/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "5team",
    /* First member's full name */
    "Kim Taeyong",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


// 기본 상수
#define WSIZE 4                // 글자, 헤더, 풋터 크기 4byte
#define DSIZE 8                // 더블(부동소수점) 글자 크기 8byte
#define CHUNKSIZE (1<<12)      // 힙 확장을 위한 기본 크기(초기의 빈 블록의 크기)

// 매크로
#define MAX(x, y)  ((x) > (y) ? (x) : (y))

// size와 할당 비트를 결합, header와 footer에 저장할 값
#define PACK(size, alloc)  ((size) | (alloc))

// p가 참조하는 워드 반환(포인터라서 직접 역참조 불가능 -> 타입 캐스팅)
#define GET(p)        (*(unsigned int *)(p))
// p에 val 저장
#define PUT(p, val)   (*(unsigned int *)(p) = (val))

// 사이즈 (~0x7: ...11111000, '&' 연산으로 뒤에 세자리 없어짐)
#define GET_SIZE(p)   (GET(p) & ~0x7)
// 할당 상태
#define GET_ALLOC(p)  (GET(p) & 0x1)

// Header 포인터
#define HDRP(bp)      ((char *)(bp) - WSIZE)
// Footer 포인터 (Header의 정보를 참조해서 가져오기 때문에, Header의 정보를 변경했다면 변경된 위치의 Footer가 반환됨에 유의)
#define FTRP(bp)      ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음 블록의 포인터
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 이전 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// 
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {     // case 1
        return bp;
    }

    else if (prev_alloc && !next_alloc) {        // case 2
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {        /// case 3
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));   // case 4
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));   // 블럭을 해제 핸들러
    PUT(FTRP(bp), PACK(size, 0));   // 풋터를 해제 핸들러
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/////////////////
static void *find_fit(size_t asize)
{
    void *bp = mem_heap_lo() + 2 * WSIZE; // 첫번째 블록(주소: 힙의 첫 부분 + 8bytes)부터 탐색 시작
    while (GET_SIZE(HDRP(bp)) > 0)
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 가용 상태이고, 사이즈가 적합하면
            return bp;                                             // 해당 블록 포인터 리턴
        bp = NEXT_BLKP(bp);                                        // 조건에 맞지 않으면 다음 블록으로 이동해서 탐색을 이어감
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
//////////////

// mm_init - initialize the malloc package.
// 힙생성하기, 패딩+프롤로그 헤더+프롤로그 풋터+에필로그 풋터를 담기위해 4워드 크기합을 구성함
// 생성 후 CHUNKSIZE만큼 추가 메모리를 요청해 힙의 크기를 확장
int mm_init(void)
{
    char *heap_listp;    // 초기 힙을 생성한다 

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)    // 4워드 크기의 힙 생성, heap_listp에 힙의 시작 주소값 할당
        return -1;
    PUT(heap_listp, 0);                            // 정렬 패딩
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));   // 프롤로그 헤더
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));   // 프롤로그 풋터
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));       // 에필로그 헤더(프로그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄)
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)      // free블록으로 빈 힙을 CHUNKSIZE bytes로 확장
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
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







