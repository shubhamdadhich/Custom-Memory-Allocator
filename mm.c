/*
  Author: Daniel Kopta, using code and concepts from CSAPP, Bryant and O'Hallaron

  This allocator represents the expected strategies that students will use, 
  achieving full credit:

  - Implicit list using 8-byte headers/footers
  - Immediate free block coalescing and splitting
  - Excplicit unordered free list with first-fit
  - Doubling mmap size requests, up to a point
  - Unmap unused pages
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

// interchangeable
typedef size_t header;
typedef size_t footer;

typedef struct node{
  struct node* next;
  struct node* prev;
} free_node;

// the head of the free list
free_node* free_list = NULL;

int num_page_chunks = 0;

/* always use 16-byte alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))

/* rounds up to the nearest multiple of pagesize */
#define PAGE_ALIGN(size) (((size) + (pagesize-1)) & ~(pagesize-1))


/*-------------Macros from assignment---*/
// This assumes you have a struct or typedef called "header" and "footer"
#define OVERHEAD (sizeof(header)+sizeof(footer))

#define MIN_BLOCK_SIZE (OVERHEAD + ALIGNMENT)

// ensure that the sentinel's payload is 16-byte aligned
#define PAGE_PAD 8

// Overhead in a new empty page chunk
//                        pad     sentinel       terminator
#define PAGE_OVERHEAD (PAGE_PAD + OVERHEAD + sizeof(footer))

// Given a payload pointer, get the header or footer pointer
#define HDRP(bp) ((char *)(bp) - sizeof(header))
#define FTRP(bp) ((char *)(bp)+GET_SIZE(HDRP(bp))-OVERHEAD)

// Given a payload pointer, get the next or previous payload pointer
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE((char *)(bp)-OVERHEAD))

// ******These macros assume you are using a size_t for headers and footers ******
// Given a pointer to a header, get or set its value
#define GET(p)      (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val))

// Combine a size and alloc bit
#define PACK(size, alloc) ((size) | (alloc))

// Given a header pointer, get the alloc or size 
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_SIZE(p)  (GET(p) & ~0xF)

#define MAX_PAGE_PER_MAP 32
  
void* extend (size_t size);
void* find_free_block(size_t reqsize);
void allocate(void* bp, size_t size);
void* coalesce(void* ptr);
void add_free(void* bp);
void del_free(void* bp);
void try_unmap(void* bp);
void print_page(void* page);
void print_heap(void* start, int N);

int map_multiplier = 1;
int pagesize = 0;
void* recent_page;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
  map_multiplier = 1;
  free_list = NULL;
  num_page_chunks = 0;
  pagesize = mem_pagesize();
  
  return 0;
}

/* 
 * mm_malloc - Allocate a block by using bytes from current_avail,
 *     grabbing a new page if necessary.
 */
void *mm_malloc(size_t size)
{
  //printf("malloc %zu\n", size);
  int newsize = ALIGN(size + OVERHEAD);
  void *p;


  p = find_free_block(newsize);
  if (p == NULL) {
    p = extend(newsize);
    if (p == NULL)
      return NULL;
    // guaranteed to work if the above extend worked
    p = find_free_block(newsize);
  }

  // for debugging
  //print_heap(recent_page, 30);
  
  return p;
}

/*
 * mm_free
 */
void mm_free(void *ptr)
{  
  size_t cursize = GET_SIZE(HDRP(ptr));
  PUT(HDRP(ptr), PACK(cursize, 0));
  PUT(FTRP(ptr), PACK(cursize, 0));
  
  // coalesce will handle updates to the explicit free list  
  void* leftmost = coalesce(ptr);

  // check if we can unmap, but don't unmap the last one
  if(num_page_chunks > 1)
    try_unmap(leftmost);

  // for debugging
  //print_heap(recent_page, 30);
}

void try_unmap(void* bp)
{
  // check if it's a full page chunk surrounded by sentinel and terminator
  void* prev = PREV_BLKP(bp);
  void* next = NEXT_BLKP(bp);
  // can't use GET_SIZE macro on 8-byte block for the terminator
  if(GET_SIZE(HDRP(prev)) == OVERHEAD && GET(HDRP(next)) == 0x9)
  {
    // full page chunk size
    size_t chunk_size = GET_SIZE(HDRP(bp)) + PAGE_OVERHEAD;
    // address of page chunk
    void* base = (char*)prev - (sizeof(header) + PAGE_PAD);
    del_free(bp);
    mem_unmap(base, chunk_size);
    num_page_chunks--;
  }  
}

void* coalesce(void* ptr)
{
  void* lbp = PREV_BLKP(ptr);
  void* rbp = NEXT_BLKP(ptr);

  int lfree = !GET_ALLOC(HDRP(lbp));
  int rfree = !GET_ALLOC(HDRP(rbp));

  size_t cursize = GET_SIZE(HDRP(ptr));
  size_t lsize = GET_SIZE(HDRP(lbp));
  size_t rsize = GET_SIZE(HDRP(rbp));
  
  // no free neighbors
  if(!lfree && !rfree)
  {
    add_free(ptr);
    return ptr;
  }

  // left neighbor free
  if(lfree && !rfree)
  {
    PUT(HDRP(lbp), PACK(lsize + cursize, 0));
    PUT(FTRP(lbp), PACK(lsize + cursize, 0));
    return lbp;
  }

  // right neighbor free
  if(!lfree && rfree)
  {
    PUT(HDRP(ptr), PACK(cursize + rsize, 0));
    PUT(FTRP(ptr), PACK(cursize + rsize, 0));
    del_free(rbp);
    add_free(ptr);
    return ptr;
  }

  // both free
  if(lfree && rfree)
  {
    PUT(HDRP(lbp), PACK(lsize + cursize + rsize, 0));
    PUT(FTRP(lbp), PACK(lsize + cursize + rsize, 0));
    del_free(rbp);
    return lbp;
  }
  return NULL;
}

// add a free node to the explicit free list
void add_free(void* ptr)
{
  // init new node
  free_node* node = (free_node*)ptr;  
  node->prev = NULL;
  node->next = NULL;
  
  if(free_list == NULL)
  {
    free_list = node;
    return;
  }

  node->next = free_list;
  free_list->prev = node;
  free_list = node;
}

// delete a free node from the explicit free list
void del_free(void* ptr)
{
  free_node* node = (free_node*)ptr;

  if(node->prev != NULL)
    node->prev->next = node->next;

  if(node->next != NULL)
    node->next->prev = node->prev;

  if(node == free_list)
    free_list = free_list->next;
}


/*
  Find a free bock big enough for the requested allocation and allocate it
  or return null if no blocks big enough
 */
void* find_free_block(size_t reqsize)
{
  free_node* n = free_list;

  while(n != NULL)
  {
    if(GET_SIZE(HDRP(n)) >= reqsize)
    {
      allocate(n, reqsize);      
      return n;
    }
    n = n->next;    
  }
  return NULL; 
}


/*
  Entry point for allocating a block, using other helpers 
  to split and update the free list
 */
void allocate(void* bp, size_t size)
{
  size_t cursize = GET_SIZE(HDRP(bp));
  size_t remainder = cursize - size;
  // split?
  if(remainder >= MIN_BLOCK_SIZE)
  {
    // reduce size of current block
    PUT(HDRP(bp), size);
    PUT(FTRP(bp), size);

    // new unallocated block
    void* next = NEXT_BLKP(bp);
    PUT(HDRP(next), PACK(remainder, 0));
    PUT(FTRP(next), PACK(remainder, 0));
    add_free(next);
  }

  // allocate old block
  cursize = GET_SIZE(HDRP(bp));
  PUT(HDRP(bp), PACK(cursize, 1));
  PUT(FTRP(bp), PACK(cursize, 1));
  del_free(bp);
}

/*
  Takes in full block size, including overhead
  already determined by malloc
 */
void* extend (size_t size)
{  
  // The smallest mapping needed for the new allocation
  int reqsize = PAGE_ALIGN(size + PAGE_OVERHEAD);

  // Try our usual doubling size
  int newsize = map_multiplier * pagesize;

  // Take the bigger of the two
  if(newsize < reqsize)
    newsize = reqsize;

  // Double the multiplier, to an extent
  if(map_multiplier < MAX_PAGE_PER_MAP)
    map_multiplier *= 2;

  void* newmap = mem_map(newsize);
  if(newmap == NULL)
    return NULL;

  // for debugging only
  recent_page = newmap;

  num_page_chunks++;

  char* sentinel = (char*)newmap + PAGE_PAD;
  char* terminator = (char*)newmap + newsize - sizeof(header);
  char* bp = sentinel + OVERHEAD + sizeof(header);
  
  // place the sentinel
  PUT(sentinel, PACK(OVERHEAD, 1));
  PUT(sentinel + sizeof(header), PACK(OVERHEAD, 1));

  // place the terminator
  PUT(terminator, PACK(sizeof(header), 1));

  int block_size = newsize - PAGE_OVERHEAD;
  // place the unallocated block using the rest of the page
  PUT(HDRP(bp), PACK(block_size, 0));
  PUT(FTRP(bp), PACK(block_size, 0));
  add_free(bp);

  //print_page(newmap);
  
  // return a pointer to the new payload
  return (void*)bp;
}


// prints the blocks in the implicit list in the page chunk
void print_page(void* page)
{
  char* p = page;

  printf("page %p\n", p);

  // payload of sentinel
  p += OVERHEAD;
  
  printf("\tsentinel\n");
  printf("\t\theader: (0x%zx)  size: %zu  alloc: %zu\n", GET(HDRP(p)), GET_SIZE(HDRP(p)), GET_ALLOC(HDRP(p)));
  printf("\t\tfooter: (0x%zx)  size: %zu  alloc: %zu\n", GET(FTRP(p)), GET_SIZE(FTRP(p)), GET_ALLOC(FTRP(p)));

  p = NEXT_BLKP(p);
  
  printf("\tblocks\n");

  do
  {
    printf("\t\t%p\n", p);
    printf("\t\theader: (0x%zx)  size: %zu  alloc: %zu\n", GET(HDRP(p)), GET_SIZE(HDRP(p)), GET_ALLOC(HDRP(p)));
    printf("\t\tfooter: (0x%zx)  size: %zu  alloc: %zu\n", GET(FTRP(p)), GET_SIZE(FTRP(p)), GET_ALLOC(FTRP(p)));
    p = NEXT_BLKP(p);    
  }
  while(GET_SIZE(HDRP(p)) > sizeof(header));

  printf("\tterminator\n");
  printf("\t\theader: (0x%zx)  size: %zu  alloc: %zu\n", GET(HDRP(p)), GET_SIZE(HDRP(p)), GET_ALLOC(HDRP(p)));
}


void print_heap(void* start, int N)
{
  printf("printing %d words of heap\n", N);
  size_t* p = (size_t*)start;

  for(int i = 0; i < N; i++)
  {
    printf("%p\t0x%zx\n", p, *p);
    p++;
  }
}
