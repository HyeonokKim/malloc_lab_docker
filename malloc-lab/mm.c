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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

// Word and Double Word size
#define WSIZE 4
#define DSIZE 8

// 힙을 한 번 확장할 때 기본으로 늘릴 크기
#define CHUNKSIZE (1<<12)

// 둘 중 큰 값 반환
#define MAX(x,y) ((x)>(y)? (x):(y))

// 블록 크기와 할당 비트 합침 -> header, footer에 저장할 값
#define PACK(size, alloc) ((size) | (alloc))

// 주소 p가 가리키는 위치에서 4바이트 읽기/쓰기
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p)=(val))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// header와 footer에서 블록 크기와 할당 비트 추출
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp(블록 포인터)로부터 헤더/푸터 주소 계산
// 헤더: bp 바로 앞 1워드
// 푸터: bp + 블록크기 - 2워드 (헤더+푸터 각 1워드)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + (GET_SIZE(HDRP(bp))) - DSIZE)

// bp로부터 다음/이전 블록의 bp 계산
// 다음 블록: 현재 블록 크기만큼 앞으로
// 이전 블록: 이전 블록 푸터에서 크기 읽어 뒤로
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 힙의 시작을 가리키는 전역 포인터 (프롤로그 블록의 payload 시작)
static char *heap_listp;

/* -----------------------------------------------------------------------
 * 헬퍼 함수 선언 (아래에서 구현)
 * ----------------------------------------------------------------------- */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void  place(void *bp, size_t asize);


/*
 * mm_init - initialize the malloc package.
 */

/*
 * [mm_init 구현 로직]
 *
 * 목표: 힙의 초기 구조(프롤로그 블록 + 에필로그 헤더)를 잡고,
 *       첫 가용 블록을 만들어 둔다.
 *
 * 메모리 레이아웃 (초기화 직후):
 *   [ padding(0) | prologue hdr | prologue ftr | epilogue hdr ]
 *      4bytes        8/1             8/1              0/1
 *
 * 단계:
 *  1) mem_sbrk(4*WSIZE)로 16바이트 확보 → 실패 시 -1 반환
 *  2) heap_listp[0] = 0          : 더블워드 정렬을 위한 패딩
 *  3) heap_listp[1] = PACK(8,1)  : 프롤로그 헤더  (크기=8, 할당됨)
 *  4) heap_listp[2] = PACK(8,1)  : 프롤로그 푸터  (크기=8, 할당됨)
 *  5) heap_listp[3] = PACK(0,1)  : 에필로그 헤더  (크기=0, 할당됨)
 *  6) heap_listp을 프롤로그 푸터(=payload 시작)로 이동
 *  7) extend_heap(CHUNKSIZE/WSIZE)로 초기 가용 블록 생성
 *     → 실패 시 -1 반환, 성공 시 0 반환
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE,1)); //prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE,1)); //prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0,1));     //epilogue header

    heap_listp += (2 * WSIZE);

    // extend_heap으로 첫 free block 생성
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/* -----------------------------------------------------------------------
 * extend_heap - 힙을 words 워드만큼 늘리고 새 가용 블록 반환
 *
 * [구현 로직]
 *  1) words를 짝수로 맞춰 더블워드 정렬 보장
 *     → size = (words % 2) ? (words+1)*WSIZE : words*WSIZE
 *  2) mem_sbrk(size)로 힙 확장 → 실패 시 NULL 반환
 *  3) 새 블록의 헤더/푸터를 FREE(0)로 초기화
 *     PUT(HDRP(bp), PACK(size, 0))
 *     PUT(FTRP(bp), PACK(size, 0))
 *  4) 새 에필로그 헤더 설정
 *     PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1))
 *  5) coalesce(bp)로 이전 블록이 free면 합치고 반환
 * ----------------------------------------------------------------------- */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 더블워드 정렬을 위해 짝수 워드 단위로 반올림 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 새 가용 블록의 헤더/푸터와 에필로그 헤더 설정 */
    PUT(HDRP(bp), PACK(size, 0));           /* 가용 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));           /* 가용 블록 푸터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  /* 새 에필로그 헤더 */

    /* 이전 블록이 가용 상태면 합치기 */
    return coalesce(bp);
}

/* -----------------------------------------------------------------------
 * coalesce - 인접한 가용 블록을 합쳐 단편화 방지 (4가지 경우)
 *
 * [구현 로직]
 *  case 1: 이전 할당, 다음 할당 → 합칠 것 없음, bp 그대로 반환
 *  case 2: 이전 할당, 다음 가용 → 다음 블록과 합침
 *    - size += GET_SIZE(HDRP(NEXT_BLKP(bp)))
 *    - 현재 헤더와 다음 푸터를 새 size로 갱신
 *  case 3: 이전 가용, 다음 할당 → 이전 블록과 합침
 *    - size += GET_SIZE(HDRP(PREV_BLKP(bp)))
 *    - 이전 헤더와 현재 푸터를 새 size로 갱신
 *    - bp를 이전 블록의 bp로 이동
 *  case 4: 이전 가용, 다음 가용 → 앞뒤 모두 합침
 *    - size += 이전 + 다음 블록 크기
 *    - 이전 헤더, 다음 푸터를 새 size로 갱신
 *    - bp를 이전 블록의 bp로 이동
 *  최종적으로 합쳐진 블록의 bp 반환
 * ----------------------------------------------------------------------- */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); /* 이전 블록 할당 여부 */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); /* 다음 블록 할당 여부 */
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {           /* case 1: 양쪽 모두 할당됨 */
        return bp;

    } else if (prev_alloc && !next_alloc) {   /* case 2: 다음 블록이 가용 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

    } else if (!prev_alloc && next_alloc) {   /* case 3: 이전 블록이 가용 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

    } else {                                  /* case 4: 양쪽 모두 가용 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/* -----------------------------------------------------------------------
 * find_fit - first-fit 방식으로 asize 이상의 가용 블록 탐색
 *
 * [구현 로직]
 *  - heap_listp부터 에필로그(size==0)까지 순회
 *  - 현재 블록이 가용(alloc==0)이고 크기가 asize 이상이면 해당 bp 반환
 *  - 없으면 NULL 반환
 *
 * (성능 개선 옵션)
 *  - next-fit: 마지막으로 탐색한 위치를 기억하는 전역 포인터 사용
 *  - best-fit: 가장 작은 가용 블록을 선택하되 전체 탐색 필요
 * ----------------------------------------------------------------------- */
static void *find_fit(size_t asize)
{
    /* first-fit 탐색 */
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; /* 맞는 블록 없음 */
}

/* -----------------------------------------------------------------------
 * place - 가용 블록 bp에 asize 바이트 할당; 남은 공간이 충분하면 분할
 *
 * [구현 로직]
 *  1) 현재 블록 크기 csize = GET_SIZE(HDRP(bp))
 *  2) 분할 가능 여부 판단:
 *     남은 크기 = csize - asize
 *     최소 블록 크기 = 2*DSIZE (헤더+푸터+최소 payload)
 *     → 남은 크기 >= 2*DSIZE 이면 분할
 *  3) 분할하는 경우:
 *     - 앞부분: PACK(asize, 1)로 헤더/푸터 설정
 *     - 뒷부분(나머지 가용 블록): PACK(csize-asize, 0)으로 헤더/푸터 설정
 *  4) 분할 안 하는 경우:
 *     - 전체 블록을 PACK(csize, 1)로 헤더/푸터 설정
 * ----------------------------------------------------------------------- */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) {
        /* 분할: 요청 크기만큼 할당하고 나머지는 가용 블록으로 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        /* 분할 안 함: 블록 전체를 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

/*
 * [mm_malloc 구현 로직]
 *
 * 목표: size 바이트의 payload를 담을 수 있는 블록을 할당하고,
 *       payload 시작 주소(bp)를 반환한다.
 *
 * 단계:
 *  1) 예외 처리: size == 0 이면 NULL 반환
 *
 *  2) 실제 할당 크기(asize) 계산 (헤더+푸터+정렬 고려)
 *     - 최소 블록 크기: 2*DSIZE (헤더1 + 푸터1 + payload 최소 2워드)
 *     - size <= DSIZE  → asize = 2*DSIZE
 *     - size >  DSIZE  → asize = DSIZE * ((size + DSIZE + (DSIZE-1)) / DSIZE)
 *       (헤더/푸터 포함, 8바이트 배수로 올림)
 *
 *  3) find_fit(asize)로 가용 리스트에서 적합한 블록 탐색
 *     → 찾으면 place(bp, asize)로 배치 후 bp 반환
 *
 *  4) 가용 블록이 없으면 extend_heap으로 힙 확장
 *     - 확장 크기: MAX(asize, CHUNKSIZE)
 *     → 확장 실패 시 NULL 반환
 *     → 성공 시 place(bp, asize)로 배치 후 bp 반환
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* 조정된 블록 크기 */
    size_t extendsize;  /* 힙 부족 시 확장할 크기 */
    char  *bp;

    /* 1) 잘못된 요청 무시 */
    if (size == 0)
        return NULL;

    /* 2) 오버헤드와 정렬 요건을 반영한 블록 크기 계산 */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    /* 3) 가용 리스트에서 적합한 블록 탐색 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 4) 적합한 블록 없음 → 힙 확장 후 배치 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */

/*
 * [mm_free 구현 로직]
 *
 * 목표: ptr이 가리키는 블록을 가용 상태로 전환하고,
 *       인접 가용 블록과 합쳐 단편화를 줄인다.
 *
 * 단계:
 *  1) 현재 블록 크기 읽기: size = GET_SIZE(HDRP(ptr))
 *  2) 헤더와 푸터를 FREE(alloc=0)로 갱신
 *     PUT(HDRP(ptr), PACK(size, 0))
 *     PUT(FTRP(ptr), PACK(size, 0))
 *  3) coalesce(ptr)로 인접 가용 블록과 즉시 병합
 *     (즉시 합치기 = immediate coalescing 정책)
 */
void mm_free(void *ptr)
{
    /* 1) 현재 블록의 크기 확인 */
    size_t size = GET_SIZE(HDRP(ptr));

    /* 2) 헤더와 푸터를 가용(0)으로 표시 */
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    /* 3) 인접 가용 블록과 병합 */
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */

/*
 * [mm_realloc 구현 로직]
 *
 * 목표: ptr 블록의 크기를 size 바이트로 재조정한다.
 *
 * 예외 처리 (표준 realloc 명세):
 *  - ptr == NULL          → mm_malloc(size)와 동일
 *  - size == 0            → mm_free(ptr) 후 NULL 반환
 *
 * 기본 구현 (naive):
 *  1) mm_malloc(size)로 새 블록 할당 → 실패 시 NULL 반환
 *     (기존 블록 내용 유지 필요: ptr은 건드리지 않음)
 *  2) 복사할 크기 결정:
 *     copySize = MIN(기존 블록의 payload 크기, size)
 *     기존 크기: GET_SIZE(HDRP(ptr)) - DSIZE  (헤더+푸터 제외)
 *  3) memcpy(newptr, ptr, copySize)로 데이터 복사
 *  4) mm_free(ptr)로 기존 블록 해제
 *  5) newptr 반환
 *
 * (성능 개선 옵션 - 추후 구현 가능)
 *  - 다음 블록이 가용이고 합쳤을 때 size를 충족하면 in-place 확장
 *  - 이전 블록이 가용이면 앞으로 당겨 데이터 복사 최소화
 *  - 크기를 줄이는 경우 남은 공간이 최소 블록 이상이면 분할
 */
void *mm_realloc(void *ptr, size_t size)
{
    void  *newptr;
    size_t copySize;

    /* 예외 처리 */
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    /* 새 블록 할당 */
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    /* 복사할 크기 = MIN(기존 payload 크기, 요청 크기) */
    copySize = GET_SIZE(HDRP(ptr)) - DSIZE; /* 헤더+푸터(2*WSIZE*2=DSIZE) 제외 */
    if (size < copySize)
        copySize = size;

    /* 데이터 복사 후 기존 블록 해제 */
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}
