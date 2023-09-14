#include "mm.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"

team_t team = {
    /* Team name */
    "Number 1",
    /* First member's full name */
    "ssongwoe",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 10)
#define LISTLIMIT 12

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7) // 하위 3비트를 다 0으로 만들기
#define GET_ALLOC(p) (GET(p) & 0x1) // 됐는지 안됐는지 확인하는거

#define HDRP(bp) ((char *)(bp)-WSIZE)                        // 헤더
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 푸터

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))

#define PREP(bp) (* (char **)(bp))
#define SUCP(bp) (* (char **)(bp + WSIZE))

static char *heap_listp;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

void printarray();
void add_block_first(void *bp);
void delete_block(void *bp);


void* seg_list[LISTLIMIT];
int calc_index(int size);

int mm_init(void)
{
  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    return -1;

  for (int i = 0; i < LISTLIMIT; i ++){
      seg_list[i] = NULL;
  }
  PUT(heap_listp, 0);
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
  heap_listp += (2 * WSIZE);

  if (extend_heap(4) == NULL)       
    return -1;

  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    return -1;

  // printarray();
  return 0;
}

static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

  return coalesce(bp);
}

static void *coalesce(void *bp)
{

  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && !next_alloc)
  {
    delete_block(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  
  if (!prev_alloc && next_alloc) {
    delete_block(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  
  if (!prev_alloc && !next_alloc) 
  {
    delete_block(PREV_BLKP(bp));
    delete_block(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  add_block_first(bp);
  return bp;
}

void *mm_malloc(size_t size)
{
  size_t asize;
  size_t extendsize;
  char *bp;

  if (size == 0)
    return NULL;

  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
    asize = ALIGNMENT * ((size + (DSIZE) + (ALIGNMENT - 1)) / ALIGNMENT); // 올림

  if ((bp = find_fit(asize)) != NULL)
  {
    place(bp, asize);
    return bp;
  }

  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
    return NULL;
  }

  place(bp, asize);

  return bp;
}

void mm_free(void *ptr)
{
  size_t size = GET_SIZE(HDRP(ptr));

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  coalesce(ptr);
}

void *mm_realloc(void *bp, size_t size)
{
  size_t old_size = GET_SIZE(HDRP(bp)); // 기존 블록의 사이즈
  if (old_size-DSIZE >= size) {
    return bp;
  } 

  size_t need_size = size -(old_size - DSIZE); 
  if (!GET_ALLOC(HDRP(NEXT_BLKP(bp))) && GET_SIZE(HDRP(NEXT_BLKP(bp)))>=need_size)
  {
    delete_block(NEXT_BLKP(bp));
    size_t now_size = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(now_size, 1));
    PUT(FTRP(bp), PACK(now_size, 1));
    return bp;
  }
  else
  {
    void *oldptr = bp;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
  }
    
}

static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));

  delete_block(bp);

  if ((csize - asize) >= (2 * DSIZE))
  {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    
    add_block_first(bp);
  }
  else
  {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}

static void *find_fit(size_t asize)
{
  void *bp;
  // int index = calc_index(asize);
  int index = LISTLIMIT-1;
  bp = seg_list[index];
  while (index < LISTLIMIT) {
    bp = seg_list[index];
    for(bp ; bp != NULL; bp = SUCP(bp)){
      if(GET_SIZE(HDRP(bp)) >= asize){
        return bp;
      }
    }    
    index++;
  }

  return NULL;
}

void add_block_first(void *bp)
{
  // printf("addblock first %d\n", GET_SIZE(HDRP(bp)));
  int tmp = GET_SIZE(HDRP(bp));
  int index = calc_index(tmp);
  
  // printf("index: %d\n", index);
  void* head = seg_list[index];

  PREP(bp) = NULL; // 나한테 prev 추가
  SUCP(bp) = head;  // 나한테 next 추가
  if (head != NULL) {
    PREP(head) = bp; // 기존 첫번째 노드의 prev를 수정
  }
  seg_list[index] = bp; // 연결리스트 헤드 변경

}

void delete_block(void *bp)
{
  int index = calc_index(GET_SIZE(HDRP(bp)));
  void* head = seg_list[index];
  
  if(bp == head){
    if (SUCP(bp)!= NULL) {
      PREP(SUCP(bp)) = NULL;
    }
    seg_list[index] = SUCP(bp);
  }else{
      SUCP(PREP(bp)) = SUCP(bp);
      if (SUCP(bp)!= NULL) {
        PREP(SUCP(bp)) = PREP(bp);
      }
  }
}

int calc_index(int size){
    int i = -4;
    while (size > 0){
        size = (size >> 1);
        i++;
        if (i >= LISTLIMIT-1)
         break;
    }
    if (i < 0) 
      return 0;
    return i;
}



void printarray() {
  int idx = 0;
  while (idx < LISTLIMIT) {
    void* now = seg_list[idx]; 
    int count = 0;
    while (now != NULL) {
      count++;
      now = SUCP(now);
    }
    printf("%d 리스트 개수 : %d\n", idx, count);
    idx++;
  }
}

int ALIGN_double(size_t size)
{
    size_t searchsize = 1;
    // size_t searchsize = size;
    while (1)
    {
        if (searchsize >= size)
            return searchsize;
        searchsize *= 2;
    }
    return 0;
}

static void *coalesce(void *bp)
{
    while (1)
    { // buddy가 계속 있다면, 끝없이 coalescing
        if (내가 버디보다 뒤에있는 친구였다면..)
        {
            if (버디한테 할당할수 있으면)
            {
                remove_block(버디블럭);
                전체 블럭에 2배사이즈 할당!
                bp = 버디블럭
            }
            else
                break;
        }
        else
        {   //내가 버디보다 앞에있는친구였다면...

            if (버디한테 할당할수 있으면)
            {
                remove_block(버디블럭);
                전체블럭에 2배사이즈 할당!
            }
            else
                break;
        }
    }
    bp = (void *)bp;
    insert_block(bp, size);
    return bp;
}


int find_buddy(int v) {
  v--;
  v |= v >> 1;
  v |= v >> 2;
  v |= v >> 4;
  v |= v >> 8;
  v |= v >> 16;
  v++;
  return v;
}