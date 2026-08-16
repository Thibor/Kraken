#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>
#include <math.h>

#if defined(_WIN32) || defined(_WIN64)
#include <windows.h>
#endif

/* define the mate value */
#define MATE 10000

#define WHITE 0
#define BLACK 8
#define MAX_PLY 64
#define KEY_SIZE 1024
#define U8 unsigned __int8
#define S16 signed __int16
#define S64 signed __int64
#define U64 unsigned __int64
#define FALSE 0
#define TRUE 1
#define NAME "Kraken"
#define VERSION "2026-07-30"
#define START_FEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
#define FLIP(sp) ((sp)^0x38)
#define ABSSQ(sq,blackTurn) ((blackTurn) ? FLIP(sq) : (sq))

typedef enum { EMPTY, PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB }TPieceType;
typedef enum { UPPER, LOWER, EXACT } Bound;
enum { CASTLE_WK = 0b0001, CASTLE_WQ = 0b0010, CASTLE_BK = 0b0100, CASTLE_BQ = 0b1000 };
/* define the move type, for example
   KING|CASTLE is a castle move
   PAWN|CAPTURE|EP is an enpassant move
   PAWN|PROMO|CAPTURE is a promotion with a capture */
typedef enum { CASTLE = 0x40, PROMO = 0x20, EP = 0x10, CAPTURE = 0x08 } TMoveType;
typedef enum {
	SQ_A1, SQ_B1, SQ_C1, SQ_D1, SQ_E1, SQ_F1, SQ_G1, SQ_H1,
	SQ_A2, SQ_B2, SQ_C2, SQ_D2, SQ_E2, SQ_F2, SQ_G2, SQ_H2,
	SQ_A3, SQ_B3, SQ_C3, SQ_D3, SQ_E3, SQ_F3, SQ_G3, SQ_H3,
	SQ_A4, SQ_B4, SQ_C4, SQ_D4, SQ_E4, SQ_F4, SQ_G4, SQ_H4,
	SQ_A5, SQ_B5, SQ_C5, SQ_D5, SQ_E5, SQ_F5, SQ_G5, SQ_H5,
	SQ_A6, SQ_B6, SQ_C6, SQ_D6, SQ_E6, SQ_F6, SQ_G6, SQ_H6,
	SQ_A7, SQ_B7, SQ_C7, SQ_D7, SQ_E7, SQ_F7, SQ_G7, SQ_H7,
	SQ_A8, SQ_B8, SQ_C8, SQ_D8, SQ_E8, SQ_F8, SQ_G8, SQ_H8,
	SQ_NONE,
	SQ_NB = 64
}Square;

typedef struct {
	U8 post;
	U8 stop;
	U8 depthLimit;
	U64 timeStart;
	U64 timeLimit;
	U64 nodes;
	U64 nodesLimit;
}SearchInfo;

/* move structure */
typedef union
{
	struct {
		U8 from;
		U8 to;
		U8 promo;
		U8 flag;
	};
	unsigned int Move;
}TMove;

/*
Board structure definition

PM,P0,P1,P2 are the 4 bitboards that contain the whole board
PM is the bitboard with the side to move pieces
P0,P1 and P2: with these bitboards you can obtain every type of pieces and every pieces combinations.
*/
typedef struct {
	U64 PM;
	U64 P0;
	U64 P1;
	U64 P2;
	U8 castleFlags; /* ..sl..SL  short long opponent SHORT LONG side to move */
	U8 enPassant; /* enpassant column, =8 if not set */
	U8 move50; /* 50 move rule counter */
	U8 STM; /* side to move */
} Position;

typedef struct {
	S16 score;
	TMove move;
	TMove killer1;
	TMove killer2;
} Stack;

typedef struct {
	U64 hash;
	TMove move;
	S16 score;
	U8 depth;
	U8 flag;
}TTEntry;

typedef struct {
	U64 hash;
	S16 score;
} TTEntryEval;

Position position;

U64 keys[KEY_SIZE];
Stack ss[128];
int hh[2][64][64];
TTEntry* tt;
TTEntryEval* ttEval;
int historyCount = 0;
U64 historyHash[1024];
U64 ttSize;
U64 ttMask;

int phaseVal[PT_NB] = { 0,0,1,1,2,4,0 };
int insufVal[PT_NB] = { 0,3,1,2,3,3,0 };

int mg_material[PT_NB] = { 0, 82, 337, 365, 477, 1025, 0 };
int eg_material[PT_NB] = { 0, 94, 281, 297, 512,  936, 0 };
int mx_material[PT_NB] = { 0, 94, 337, 365, 512, 1025, 0 };

int boardCastle[64] = {
	 7, 15, 15, 15,  3, 15, 15, 11,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	15, 15, 15, 15, 15, 15, 15, 15,
	13, 15, 15, 15, 12, 15, 15, 14
};
int empty_table[64];
int mg_pawn_table[64] = {
	  0,   0,   0,   0,   0,   0,  0,   0,
	 98, 134,  61,  95,  68, 126, 34, -11,
	 -6,   7,  26,  31,  65,  56, 25, -20,
	-14,  13,   6,  21,  23,  12, 17, -23,
	-27,  -2,  -5,  12,  17,   6, 10, -25,
	-26,  -4,  -4, -10,   3,   3, 33, -12,
	-35,  -1, -20, -23, -15,  24, 38, -22,
	  0,   0,   0,   0,   0,   0,  0,   0,
};

int eg_pawn_table[64] = {
	  0,   0,   0,   0,   0,   0,   0,   0,
	178, 173, 158, 134, 147, 132, 165, 187,
	 94, 100,  85,  67,  56,  53,  82,  84,
	 32,  24,  13,   5,  -2,   4,  17,  17,
	 13,   9,  -3,  -7,  -7,  -8,   3,  -1,
	  4,   7,  -6,   1,   0,  -5,  -1,  -8,
	 13,   8,   8,  10,  13,   0,   2,  -7,
	  0,   0,   0,   0,   0,   0,   0,   0,
};

int mg_knight_table[64] = {
	-167, -89, -34, -49,  61, -97, -15, -107,
	 -73, -41,  72,  36,  23,  62,   7,  -17,
	 -47,  60,  37,  65,  84, 129,  73,   44,
	  -9,  17,  19,  53,  37,  69,  18,   22,
	 -13,   4,  16,  13,  28,  19,  21,   -8,
	 -23,  -9,  12,  10,  19,  17,  25,  -16,
	 -29, -53, -12,  -3,  -1,  18, -14,  -19,
	-105, -21, -58, -33, -17, -28, -19,  -23,
};

int eg_knight_table[64] = {
	-58, -38, -13, -28, -31, -27, -63, -99,
	-25,  -8, -25,  -2,  -9, -25, -24, -52,
	-24, -20,  10,   9,  -1,  -9, -19, -41,
	-17,   3,  22,  22,  22,  11,   8, -18,
	-18,  -6,  16,  25,  16,  17,   4, -18,
	-23,  -3,  -1,  15,  10,  -3, -20, -22,
	-42, -20, -10,  -5,  -2, -20, -23, -44,
	-29, -51, -23, -15, -22, -18, -50, -64,
};

int mg_bishop_table[64] = {
	-29,   4, -82, -37, -25, -42,   7,  -8,
	-26,  16, -18, -13,  30,  59,  18, -47,
	-16,  37,  43,  40,  35,  50,  37,  -2,
	 -4,   5,  19,  50,  37,  37,   7,  -2,
	 -6,  13,  13,  26,  34,  12,  10,   4,
	  0,  15,  15,  15,  14,  27,  18,  10,
	  4,  15,  16,   0,   7,  21,  33,   1,
	-33,  -3, -14, -21, -13, -12, -39, -21,
};

int eg_bishop_table[64] = {
	-14, -21, -11,  -8, -7,  -9, -17, -24,
	 -8,  -4,   7, -12, -3, -13,  -4, -14,
	  2,  -8,   0,  -1, -2,   6,   0,   4,
	 -3,   9,  12,   9, 14,  10,   3,   2,
	 -6,   3,  13,  19,  7,  10,  -3,  -9,
	-12,  -3,   8,  10, 13,   3,  -7, -15,
	-14, -18,  -7,  -1,  4,  -9, -15, -27,
	-23,  -9, -23,  -5, -9, -16,  -5, -17,
};

int mg_rook_table[64] = {
	 32,  42,  32,  51, 63,  9,  31,  43,
	 27,  32,  58,  62, 80, 67,  26,  44,
	 -5,  19,  26,  36, 17, 45,  61,  16,
	-24, -11,   7,  26, 24, 35,  -8, -20,
	-36, -26, -12,  -1,  9, -7,   6, -23,
	-45, -25, -16, -17,  3,  0,  -5, -33,
	-44, -16, -20,  -9, -1, 11,  -6, -71,
	-19, -13,   1,  17, 16,  7, -37, -26,
};

int eg_rook_table[64] = {
	13, 10, 18, 15, 12,  12,   8,   5,
	11, 13, 13, 11, -3,   3,   8,   3,
	 7,  7,  7,  5,  4,  -3,  -5,  -3,
	 4,  3, 13,  1,  2,   1,  -1,   2,
	 3,  5,  8,  4, -5,  -6,  -8, -11,
	-4,  0, -5, -1, -7, -12,  -8, -16,
	-6, -6,  0,  2, -9,  -9, -11,  -3,
	-9,  2,  3, -1, -5, -13,   4, -20,
};

int mg_queen_table[64] = {
	-28,   0,  29,  12,  59,  44,  43,  45,
	-24, -39,  -5,   1, -16,  57,  28,  54,
	-13, -17,   7,   8,  29,  56,  47,  57,
	-27, -27, -16, -16,  -1,  17,  -2,   1,
	 -9, -26,  -9, -10,  -2,  -4,   3,  -3,
	-14,   2, -11,  -2,  -5,   2,  14,   5,
	-35,  -8,  11,   2,   8,  15,  -3,   1,
	 -1, -18,  -9,  10, -15, -25, -31, -50,
};

int eg_queen_table[64] = {
	 -9,  22,  22,  27,  27,  19,  10,  20,
	-17,  20,  32,  41,  58,  25,  30,   0,
	-20,   6,   9,  49,  47,  35,  19,   9,
	  3,  22,  24,  45,  57,  40,  57,  36,
	-18,  28,  19,  47,  31,  34,  39,  23,
	-16, -27,  15,   6,   9,  17,  10,   5,
	-22, -23, -30, -16, -16, -23, -36, -32,
	-33, -28, -22, -43,  -5, -32, -20, -41,
};

int mg_king_table[64] = {
	-65,  23,  16, -15, -56, -34,   2,  13,
	 29,  -1, -20,  -7,  -8,  -4, -38, -29,
	 -9,  24,   2, -16, -20,   6,  22, -22,
	-17, -20, -12, -27, -30, -25, -14, -36,
	-49,  -1, -27, -39, -46, -44, -33, -51,
	-14, -14, -22, -46, -44, -30, -15, -27,
	  1,   7,  -8, -64, -43, -16,   9,   8,
	-15,  36,  12, -54,   8, -28,  24,  14,
};

int eg_king_table[64] = {
	-74, -35, -18, -18, -11,  15,   4, -17,
	-12,  17,  14,  17,  17,  38,  23,  11,
	 10,  17,  23,  15,  20,  45,  44,  13,
	 -8,  22,  24,  27,  26,  33,  26,   3,
	-18,  -4,  21,  24,  27,  23,   9, -11,
	-19,  -3,  11,  21,  23,  16,   7,  -9,
	-27, -11,   4,  13,  14,   4,  -5, -17,
	-53, -34, -21, -11, -28, -14, -24, -43
};

int* mg_table[PT_NB] = {
	empty_table,
	mg_pawn_table,
	mg_knight_table,
	mg_bishop_table,
	mg_rook_table,
	mg_queen_table,
	mg_king_table
};

int* eg_table[PT_NB] = {
	empty_table,
	eg_pawn_table,
	eg_knight_table,
	eg_bishop_table,
	eg_rook_table,
	eg_queen_table,
	eg_king_table
};

int mg_pst[PT_NB][64];
int eg_pst[PT_NB][64];

/* array of bitboards that contains all the knight destination for every square */
const U64 KnightDest[64] = { 0x0000000000020400ULL,0x0000000000050800ULL,0x00000000000a1100ULL,0x0000000000142200ULL,
						   0x0000000000284400ULL,0x0000000000508800ULL,0x0000000000a01000ULL,0x0000000000402000ULL,
						   0x0000000002040004ULL,0x0000000005080008ULL,0x000000000a110011ULL,0x0000000014220022ULL,
						   0x0000000028440044ULL,0x0000000050880088ULL,0x00000000a0100010ULL,0x0000000040200020ULL,
						   0x0000000204000402ULL,0x0000000508000805ULL,0x0000000a1100110aULL,0x0000001422002214ULL,
						   0x0000002844004428ULL,0x0000005088008850ULL,0x000000a0100010a0ULL,0x0000004020002040ULL,
						   0x0000020400040200ULL,0x0000050800080500ULL,0x00000a1100110a00ULL,0x0000142200221400ULL,
						   0x0000284400442800ULL,0x0000508800885000ULL,0x0000a0100010a000ULL,0x0000402000204000ULL,
						   0x0002040004020000ULL,0x0005080008050000ULL,0x000a1100110a0000ULL,0x0014220022140000ULL,
						   0x0028440044280000ULL,0x0050880088500000ULL,0x00a0100010a00000ULL,0x0040200020400000ULL,
						   0x0204000402000000ULL,0x0508000805000000ULL,0x0a1100110a000000ULL,0x1422002214000000ULL,
						   0x2844004428000000ULL,0x5088008850000000ULL,0xa0100010a0000000ULL,0x4020002040000000ULL,
						   0x0400040200000000ULL,0x0800080500000000ULL,0x1100110a00000000ULL,0x2200221400000000ULL,
						   0x4400442800000000ULL,0x8800885000000000ULL,0x100010a000000000ULL,0x2000204000000000ULL,
						   0x0004020000000000ULL,0x0008050000000000ULL,0x00110a0000000000ULL,0x0022140000000000ULL,
						   0x0044280000000000ULL,0x0088500000000000ULL,0x0010a00000000000ULL,0x0020400000000000ULL };
/* The same for the king */
const U64 KingDest[64] = { 0x0000000000000302ULL,0x0000000000000705ULL,0x0000000000000e0aULL,0x0000000000001c14ULL,
						  0x0000000000003828ULL,0x0000000000007050ULL,0x000000000000e0a0ULL,0x000000000000c040ULL,
						  0x0000000000030203ULL,0x0000000000070507ULL,0x00000000000e0a0eULL,0x00000000001c141cULL,
						  0x0000000000382838ULL,0x0000000000705070ULL,0x0000000000e0a0e0ULL,0x0000000000c040c0ULL,
						  0x0000000003020300ULL,0x0000000007050700ULL,0x000000000e0a0e00ULL,0x000000001c141c00ULL,
						  0x0000000038283800ULL,0x0000000070507000ULL,0x00000000e0a0e000ULL,0x00000000c040c000ULL,
						  0x0000000302030000ULL,0x0000000705070000ULL,0x0000000e0a0e0000ULL,0x0000001c141c0000ULL,
						  0x0000003828380000ULL,0x0000007050700000ULL,0x000000e0a0e00000ULL,0x000000c040c00000ULL,
						  0x0000030203000000ULL,0x0000070507000000ULL,0x00000e0a0e000000ULL,0x00001c141c000000ULL,
						  0x0000382838000000ULL,0x0000705070000000ULL,0x0000e0a0e0000000ULL,0x0000c040c0000000ULL,
						  0x0003020300000000ULL,0x0007050700000000ULL,0x000e0a0e00000000ULL,0x001c141c00000000ULL,
						  0x0038283800000000ULL,0x0070507000000000ULL,0x00e0a0e000000000ULL,0x00c040c000000000ULL,
						  0x0302030000000000ULL,0x0705070000000000ULL,0x0e0a0e0000000000ULL,0x1c141c0000000000ULL,
						  0x3828380000000000ULL,0x7050700000000000ULL,0xe0a0e00000000000ULL,0xc040c00000000000ULL,
						  0x0203000000000000ULL,0x0507000000000000ULL,0x0a0e000000000000ULL,0x141c000000000000ULL,
						  0x2838000000000000ULL,0x5070000000000000ULL,0xa0e0000000000000ULL,0x40c0000000000000ULL };

/* masks for finding the pawns that can capture with an enpassant (in move generation) */
const U64 enPassant[8] = {
0x0000000200000000ULL,0x0000000500000000ULL,0x0000000A00000000ULL,0x0000001400000000ULL,
0x0000002800000000ULL,0x0000005000000000ULL,0x000000A000000000ULL,0x0000004000000000ULL
};

/* masks for finding the pawns that can capture with an enpassant (in make move) */
const U64 EnPassantM[8] = {
0x0000000002000000ULL,0x0000000005000000ULL,0x000000000A000000ULL,0x0000000014000000ULL,
0x0000000028000000ULL,0x0000000050000000ULL,0x00000000A0000000ULL,0x0000000040000000ULL
};

/*
reverse a bitboard:
A bitboard is an array of byte: Byte0,Byte1,Byte2,Byte3,Byte4,Byte5,Byte6,Byte7
after this function the bitboard will be: Byte7,Byte6,Byte5,Byte4,Byte3,Byte2,Byte1,Byte0

The board is saved always with the side to move in the low significant bits of the bitboard, so this function
is used to change the side to move
*/

SearchInfo info;

#if defined(_MSC_VER)

#define RevBB(bb) (_byteswap_uint64(bb))

unsigned long __inline MSB(unsigned __int64 value)
{
	unsigned long leading_zero = 0;

	if (_BitScanReverse64(&leading_zero, value))
	{
		return 0x3F ^ (63 - leading_zero);
	}
	else
	{
		return 0x3F ^ 64;
	}
}

unsigned long __inline LSB(unsigned __int64 value)
{
	unsigned long trailing_zero = 0;

	if (_BitScanForward64(&trailing_zero, value))
	{
		return trailing_zero;
	}
	else
	{
		return 64;
	}
}

#define PopCount(bb) (__popcnt64(bb))

#else
#define RevBB(bb) (__builtin_bswap64(bb))
/* return the index of the most significant bit of the bitboard, bb must always be !=0 */
#define MSB(bb) (0x3F ^ __builtin_clzll(bb))
/* return the index of the least significant bit of the bitboard, bb must always be !=0 */
#define LSB(bb) (__builtin_ctzll(bb))
/* return the number of bits sets of a bitboard */
#define PopCount(bb) (__builtin_popcountll(bb))
#endif


/* extract the least significant bit of the bitboard */
#define ExtractLSB(bb) ((bb)&(-(bb)))
/* reset the least significant bit of bb */
#define ClearLSB(bb) ((bb)&((bb)-1))

  /* these Macros are used to calculate the bitboard of a particular kind of piece
	 P2 P1 P0
	  0  0  0    empty
	  0  0  1    pawn
	  0  1  0    knight
	  0  1  1    bishop
	  1  0  0    rook
	  1  0  1    queen
	  1  1  0    king
  */
static inline U64 Occupation(Position* pos) { return pos->P0 | pos->P1 | pos->P2; }
static inline U64 Pawns(Position* pos) { return pos->P0 & ~pos->P1 & ~pos->P2; }
static inline U64 Knights(Position* pos) { return ~pos->P0 & pos->P1 & ~pos->P2; }
static inline U64 Bishops(Position* pos) { return pos->P0 & pos->P1; }
static inline U64 Rooks(Position* pos) { return ~pos->P0 & ~pos->P1 & pos->P2; }
static inline U64 Queens(Position* pos) { return pos->P0 & pos->P2; }
static inline U64 Kings(Position* pos) { return pos->P1 & pos->P2; }
static inline U64 GetTimeMs() { return GetTickCount64(); }
static inline int PieceType(Position* pos, int sq) { return ((pos->P2 >> (sq)) & 1) << 2 | ((pos->P1 >> (sq)) & 1) << 1 | ((pos->P0 >> (sq)) & 1); }
static inline void TTClear() { memset(tt, 0, sizeof(TTEntry) * ttSize); }
static inline void HHClear() { memset(hh, 0, sizeof(hh)); }
static inline void SSClear() { memset(ss, 0, sizeof(ss)); }

void UciCommand(Position* pos, char* str);

/*
The board is always saved with the side to move in the lower part of the bitboards to use the same generation and
make for the Black and the White side.
This needs the inversion of the 4 bitboards, roll the Castle rights and update the side to move.
*/
static void FlipPosition(Position* pos) {
	pos->PM ^= Occupation(pos);
	pos->PM = RevBB(pos->PM);
	pos->P0 = RevBB(pos->P0);
	pos->P1 = RevBB(pos->P1);
	pos->P2 = RevBB(pos->P2);
	pos->castleFlags = ((pos->castleFlags >> 2) | (pos->castleFlags << 2)) & 0xf;
	pos->STM ^= BLACK;
}

static int InputAvailable(void) {
	static int init = 0, pipe;
	static HANDLE inh;
	DWORD dw;
	if (!init) {
		init = 1;
		inh = GetStdHandle(STD_INPUT_HANDLE);
		pipe = !GetConsoleMode(inh, &dw);
		if (!pipe) {
			SetConsoleMode(inh, dw & ~(ENABLE_MOUSE_INPUT | ENABLE_WINDOW_INPUT));
			FlushConsoleInputBuffer(inh);
		}
	}
	if (pipe) {
		if (!PeekNamedPipe(inh, NULL, 0, NULL, &dw, NULL))
			return 1;
		return dw > 0;
	}
	else {
		GetNumberOfConsoleInputEvents(inh, &dw);
		return dw > 1;
	}
}

static int CheckUp(Position* pos) {
	if ((++info.nodes & 0xffff) == 0) {
		if (info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit)
			info.stop = TRUE;
		if (info.nodesLimit && info.nodes > info.nodesLimit)
			info.stop = TRUE;
		if (InputAvailable()) {
			char str[4000];
			fgets(str, sizeof(str), stdin);
			UciCommand(pos, str);
		}
	}
	return info.stop;
}

/* get the corresponding string to the given move  */
static inline void MoveToStr(char* strmove, TMove move, U8 color)
{
	const char promo[7] = "\0\0nbrq";
	strmove[0] = 'a' + ABSSQ(move.from, color) % 8;
	strmove[1] = '1' + ABSSQ(move.from, color) / 8;
	strmove[2] = 'a' + ABSSQ(move.to, color) % 8;
	strmove[3] = '1' + ABSSQ(move.to, color) / 8;
	strmove[4] = promo[move.promo];
	strmove[5] = '\0';
}

/* get the corresponding move to the given string */
static inline TMove StrToMove(Position* pos, char* strmove)
{
	TMove move;
	move.from = ABSSQ((U8)(strmove[0] - 'a' + (strmove[1] - '1') * 8), pos->STM);
	move.to = ABSSQ((U8)(strmove[2] - 'a' + (strmove[3] - '1') * 8), pos->STM);
	move.promo = EMPTY;
	if (strmove[4] == 'n') move.promo = KNIGHT;
	else if (strmove[4] == 'b') move.promo = BISHOP;
	else if (strmove[4] == 'r') move.promo = ROOK;
	else if (strmove[4] == 'q') move.promo = QUEEN;
	move.flag = PieceType(pos, move.from);
	if (move.flag == PAWN) {
		if ((1ULL << move.to) & 0xFF00000000000000ULL)
			move.flag |= PROMO;
		else if (pos->enPassant != 8 && move.to == (40 + pos->enPassant))
			move.flag = PAWN | EP | CAPTURE;
	}
	else if (move.flag == KING && (move.to - move.from == 2 || move.from - move.to == 2))
		move.flag = KING | CASTLE;
	if (PieceType(pos, move.to))
		move.flag |= CAPTURE;
	return move;
}

static U64 Rand64() {
	static U64 next = 1;
	next = next * 12345104729 + 104723;
	return next;
}

static void InitHash() {
	for (int i = 0; i < KEY_SIZE; ++i)
		keys[i] = Rand64();
}

/* return the bitboard with the rook destinations */
static inline U64 GenRook(uint64_t sq, U64 occupation)
{
	U64 piece = 1ULL << sq;
	occupation ^= piece; /* remove the selected piece from the occupation */
	U64 piecesup = (0x0101010101010101ULL << sq) & (occupation | 0xFF00000000000000ULL); /* find the pieces up */
	U64 piecesdo = (0x8080808080808080ULL >> (63 - sq)) & (occupation | 0x00000000000000FFULL); /* find the pieces down */
	U64 piecesri = (0x00000000000000FFULL << sq) & (occupation | 0x8080808080808080ULL); /* find pieces on the right */
	U64 piecesle = (0xFF00000000000000ULL >> (63 - sq)) & (occupation | 0x0101010101010101ULL); /* find pieces on the left */
	return (((0x8080808080808080ULL >> (63 - LSB(piecesup))) & (0x0101010101010101ULL << MSB(piecesdo))) |
		((0xFF00000000000000ULL >> (63 - LSB(piecesri))) & (0x00000000000000FFULL << MSB(piecesle)))) ^ piece;
	/* From every direction find the first piece and from that piece put a mask in the opposite direction.
	   Put togheter all the 4 masks and remove the moving piece */
}

/* return the bitboard with the bishops destinations */
static inline U64 GenBishop(uint64_t sq, U64 occupation)
{  /* it's the same as the rook */
	U64 piece = 1ULL << sq;
	occupation ^= piece;
	U64 piecesup = (0x8040201008040201ULL << sq) & (occupation | 0xFF80808080808080ULL);
	U64 piecesdo = (0x8040201008040201ULL >> (63 - sq)) & (occupation | 0x01010101010101FFULL);
	U64 piecesle = (0x8102040810204081ULL << sq) & (occupation | 0xFF01010101010101ULL);
	U64 piecesri = (0x8102040810204081ULL >> (63 - sq)) & (occupation | 0x80808080808080FFULL);
	return (((0x8040201008040201ULL >> (63 - LSB(piecesup))) & (0x8040201008040201ULL << MSB(piecesdo))) |
		((0x8102040810204081ULL >> (63 - LSB(piecesle))) & (0x8102040810204081ULL << MSB(piecesri)))) ^ piece;
}

/* return the bitboard with pieces of the same type */
static inline U64 BBPieces(Position* pos, TPieceType piece) {
	switch (piece) {
	case PAWN: return Pawns(pos);
	case KNIGHT: return Knights(pos);
	case BISHOP: return Bishops(pos);
	case ROOK: return Rooks(pos);
	case QUEEN: return Queens(pos);
	case KING: return Kings(pos);
	}
}

/* return the bitboard with the destinations of a piece in a square (exept for pawns) */
static inline U64 BBDestinations(TPieceType piece, uint64_t sq, U64 occupation){
	switch (piece){
	case KNIGHT: return KnightDest[sq];
	case BISHOP: return GenBishop(sq, occupation);
	case ROOK: return GenRook(sq, occupation);
	case QUEEN: return GenRook(sq, occupation) | GenBishop(sq, occupation);
	case KING: return KingDest[sq];
	}
}

/* If the king is in check this function return the pieces that are attacking the king. If there aren't it returns 0 */
static inline U64 InCheck(Position* pos)
{
	U64 kings = Kings(pos);
	U64 king = kings & pos->PM;
	U64 skKing = LSB(king);
	U64 occupation = Occupation(pos);
	U64 opposing = pos->PM ^ occupation;
	return (((KnightDest[skKing] & Knights(pos)) |
		(GenRook(skKing, occupation) & (Rooks(pos) | Queens(pos))) |
		(GenBishop(skKing, occupation) & (Bishops(pos) | Queens(pos))) |
		((((king << 9) & 0xFEFEFEFEFEFEFEFEULL) | ((king << 7) & 0x7F7F7F7F7F7F7F7FULL)) & Pawns(pos)) |
		(KingDest[skKing] & kings)) & opposing);
}

/* try the move and see if the king is in check. If so return the attacking pieces, if not return 0 */
static inline U64 Illegal(Position* pos, TMove move) {
	U64 from = 1ULL << move.from;
	U64 to = 1ULL << move.to;
	U64 occupation = Occupation(pos);
	U64 opposing = pos->PM ^ occupation;
	U64 bbKing;
	uint64_t sqKing;
	U64 newoccupation = (occupation ^ from) | to;
	U64 newopposing = opposing & ~to;
	if ((move.flag & 0x07) == KING){
		bbKing = to;
		sqKing = move.to;
	}
	else{
		bbKing = Kings(pos) & pos->PM;
		sqKing = LSB(bbKing);
		if (move.flag & EP) {
			newopposing ^= to >> 8;
			newoccupation ^= to >> 8;
		}
	}
	return (((KnightDest[sqKing] & Knights(pos)) |
		(GenRook(sqKing, newoccupation) & (Rooks(pos) | Queens(pos))) |
		(GenBishop(sqKing, newoccupation) & (Bishops(pos) | Queens(pos))) |
		((((bbKing << 9) & 0xFEFEFEFEFEFEFEFEULL) | ((bbKing << 7) & 0x7F7F7F7F7F7F7F7FULL)) & Pawns(pos)) |
		(KingDest[sqKing] & Kings(pos))) & newopposing);
}

/* Generate all pseudo-legal quiet moves */
static inline int GenerateQuiets(Position* pos, TMove* const quiets) {
	U64 occupation = Occupation(pos);
	U64 opposing = occupation ^ pos->PM;

	TMove* pquiets = quiets;
	for (TPieceType piece = KING; piece >= KNIGHT; piece--) // generate moves from king to knight
	{
		// generate moves for every piece of the same type of the side to move
		for (U64 pieces = BBPieces(pos, piece) & pos->PM; pieces; pieces = ClearLSB(pieces))
		{
			uint64_t sq = LSB(pieces);
			// for every destinations on a free square generate a move
			for (U64 destinations = ~occupation & BBDestinations(piece, sq, occupation); destinations; destinations = ClearLSB(destinations))
			{
				pquiets->flag = piece;
				pquiets->from = sq;
				pquiets->to = LSB(destinations);
				pquiets->promo = EMPTY;
				pquiets++;
			}
		}
	}

	/* one pawns push */
	U64 push1 = (((Pawns(pos) & pos->PM) << 8) & ~occupation) & 0x00FFFFFFFFFFFFFFULL;
	for (U64 pieces = push1; pieces; pieces = ClearLSB(pieces))
	{
		pquiets->flag = PAWN;
		pquiets->from = LSB(pieces) - 8;
		pquiets->to = LSB(pieces);
		pquiets->promo = EMPTY;
		pquiets++;
	}

	/* double pawns pushes */
	for (U64 push2 = (push1 << 8) & ~occupation & 0x00000000FF000000ULL; push2; push2 = ClearLSB(push2))
	{
		pquiets->flag = PAWN;
		pquiets->from = LSB(push2) - 16;
		pquiets->to = LSB(push2);
		pquiets->promo = EMPTY;
		pquiets++;
	}

	/* check if long castling is possible */
	if ((pos->castleFlags & CASTLE_WQ) && !(occupation & 0x0EULL))
	{
		U64 roo, bis;
		roo = ExtractLSB(0x1010101010101000ULL & occupation); /* column e */
		roo |= ExtractLSB(0x0808080808080800ULL & occupation); /*column d */
		roo |= ExtractLSB(0x0404040404040400ULL & occupation); /*column c */
		roo |= ExtractLSB(0x00000000000000E0ULL & occupation);  /* row 1 */
		bis = ExtractLSB(0x0000000102040800ULL & occupation); /*antidiag from e1/e8 */
		bis |= ExtractLSB(0x0000000001020400ULL & occupation); /*antidiag from d1/d8 */
		bis |= ExtractLSB(0x0000000000010200ULL & occupation); /*antidiag from c1/c8 */
		bis |= ExtractLSB(0x0000000080402000ULL & occupation); /*diag from e1/e8 */
		bis |= ExtractLSB(0x0000008040201000ULL & occupation); /*diag from d1/d8 */
		bis |= ExtractLSB(0x0000804020100800ULL & occupation); /*diag from c1/c8 */
		if (!(((roo & (Rooks(pos) | Queens(pos))) | (bis & (Bishops(pos) | Queens(pos))) | (0x00000000003E7700ULL & Knights(pos)) |
			(0x0000000000003E00ULL & Pawns(pos)) | (Kings(pos) & 0x0000000000000600ULL)) & opposing))
		{  /* check if c1/c8 d1/d8 e1/e8 are not attacked */
			pquiets->flag = KING | CASTLE;
			pquiets->from = 4;
			pquiets->to = 2;
			pquiets->promo = EMPTY;
			pquiets++;
		}
	}
	/* check if short castling is possible */
	if ((pos->castleFlags & CASTLE_WK) && !(occupation & 0x60ULL))
	{
		U64 roo, bis;
		roo = ExtractLSB(0x1010101010101000ULL & occupation); /* column e */
		roo |= ExtractLSB(0x2020202020202000ULL & occupation); /* column f */
		roo |= ExtractLSB(0x4040404040404000ULL & occupation); /* column g */
		roo |= 1ULL << MSB(0x000000000000000FULL & (occupation | 0x1ULL));/* row 1 */
		bis = ExtractLSB(0x0000000102040800ULL & occupation); /* antidiag from e1/e8 */
		bis |= ExtractLSB(0x0000010204081000ULL & occupation); /*antidiag from f1/f8 */
		bis |= ExtractLSB(0x0001020408102000ULL & occupation); /*antidiag from g1/g8 */
		bis |= ExtractLSB(0x0000000080402000ULL & occupation); /*diag from e1/e8 */
		bis |= ExtractLSB(0x0000000000804000ULL & occupation); /*diag from f1/f8 */
		bis |= 0x0000000000008000ULL; /*diag from g1/g8 */
		if (!(((roo & (Rooks(pos) | Queens(pos))) | (bis & (Bishops(pos) | Queens(pos))) | (0x0000000000F8DC00ULL & Knights(pos)) |
			(0x000000000000F800ULL & Pawns(pos)) | (Kings(pos) & 0x0000000000004000ULL)) & opposing))
		{  /* check if e1/e8 f1/f8 g1/g8 are not attacked */
			pquiets->flag = KING | CASTLE;
			pquiets->from = 4;
			pquiets->to = 6;
			pquiets->promo = EMPTY;
			pquiets++;
		}
	}
	return pquiets - quiets;
}

/* Generate all pseudo-legal capture and promotions */
static inline int GenerateCapture(Position* pos, TMove* const capture)
{
	U64 opposing, occupation;
	occupation = Occupation(pos);
	opposing = pos->PM ^ occupation;

	TMove* pcapture = capture;
	for (TPieceType piece = KING; piece >= KNIGHT; piece--) // generate moves from king to knight
	{
		// generate moves for every piece of the same type of the side to move
		for (U64 pieces = BBPieces(pos, piece) & pos->PM; pieces; pieces = ClearLSB(pieces))
		{
			uint64_t sq = LSB(pieces);
			// for every destinations on an opponent pieces generate a move
			for (U64 destinations = opposing & BBDestinations(piece, sq, occupation); destinations; destinations = ClearLSB(destinations))
			{
				pcapture->flag = piece | CAPTURE;
				pcapture->from = sq;
				pcapture->to = LSB(destinations);
				pcapture->promo = EMPTY;
				pcapture++;
			}
		}
	}

	/* Generate pawns right captures */
	U64 pieces = Pawns(pos) & pos->PM;
	for (U64 captureri = (pieces << 9) & 0x00FEFEFEFEFEFEFEULL & opposing; captureri; captureri = ClearLSB(captureri))
	{
		pcapture->flag = PAWN | CAPTURE;
		pcapture->from = LSB(captureri) - 9;
		pcapture->to = LSB(captureri);
		pcapture->promo = EMPTY;
		pcapture++;
	}
	/* Generate pawns left captures */
	for (U64 capturele = (pieces << 7) & 0x007F7F7F7F7F7F7FULL & opposing; capturele; capturele = ClearLSB(capturele))
	{
		pcapture->flag = PAWN | CAPTURE;
		pcapture->from = LSB(capturele) - 7;
		pcapture->to = LSB(capturele);
		pcapture->promo = EMPTY;
		pcapture++;
	}

	/* Generate pawns promotions */
	if (pieces & 0x00FF000000000000ULL)
	{
		/* promotions with left capture */
		for (U64 promo = (pieces << 9) & 0xFE00000000000000ULL & opposing; promo; promo = ClearLSB(promo)) {
			for (TPieceType piece = QUEEN; piece >= KNIGHT; piece--) /* generate underpromotions */
			{
				pcapture->flag = PAWN | PROMO | CAPTURE;
				pcapture->from = LSB(promo) - 9;
				pcapture->to = LSB(promo);
				pcapture->promo = piece;
				pcapture++;
			}
		}
		/* promotions with right capture */
		for (U64 promo = (pieces << 7) & 0x7F00000000000000ULL & opposing; promo; promo = ClearLSB(promo))
		{
			for (TPieceType piece = QUEEN; piece >= KNIGHT; piece--) /* generate underpromotions */
			{
				pcapture->flag = PAWN | PROMO | CAPTURE;
				pcapture->from = LSB(promo) - 7;
				pcapture->to = LSB(promo);
				pcapture->promo = piece;
				pcapture++;
			}
		}
		/* no capture promotions */
		for (U64 promo = ((pieces << 8) & ~occupation) & 0xFF00000000000000ULL; promo; promo = ClearLSB(promo))
		{
			for (TPieceType piece = QUEEN; piece >= KNIGHT; piece--) /* generate underpromotions */
			{
				pcapture->flag = PAWN | PROMO;
				pcapture->from = LSB(promo) - 8;
				pcapture->to = LSB(promo);
				pcapture->promo = piece;
				pcapture++;
			}
		}
	}

	if (pos->enPassant != 8)
	{  /* Generate EnPassant captures */
		for (U64 enpassant = pieces & enPassant[pos->enPassant]; enpassant; enpassant = ClearLSB(enpassant))
		{
			pcapture->flag = PAWN | EP | CAPTURE;
			pcapture->from = LSB(enpassant);
			pcapture->to = 40 + pos->enPassant;
			pcapture->promo = EMPTY;
			pcapture++;
		}
	}
	return pcapture - capture;
}

static int GenerateMoves(Position* pos, TMove* const moves, int onlyCaptures) {
	int count = GenerateCapture(pos, moves);
	if (!onlyCaptures)
		count += GenerateQuiets(pos, moves + count);
	return count;
}

/* Make the move */
static inline void Make(Position* pos, TMove move) {
	U64 sou = 1ULL << move.from;
	U64 des = 1ULL << move.to;
	switch (move.flag & 0x07) {
	case PAWN:
		if (move.flag & EP)
		{  /* EnPassant */
			pos->PM ^= sou | des;
			pos->P0 ^= sou | des;
			pos->P0 ^= des >> 8; /* delete the captured pawn */
			pos->enPassant = 8;
		}
		else
		{
			if (move.flag & CAPTURE)
			{  /* Delete the captured piece */
				pos->P0 &= ~des;
				pos->P1 &= ~des;
				pos->P2 &= ~des;
			}
			if (move.flag & PROMO)
			{
				pos->PM ^= sou | des;
				pos->P0 ^= sou;
				pos->P0 |= (U64)(move.promo & 1) << (move.to);
				pos->P1 |= (U64)(((move.promo) >> 1) & 1) << (move.to);
				pos->P2 |= (U64)((move.promo) >> 2) << (move.to);
				pos->enPassant = 8; /* clear enpassant */
			}
			else /* capture or push */
			{
				pos->PM ^= sou | des;
				pos->P0 ^= sou | des;
				pos->enPassant = 8; /* clear enpassant */
				if (move.to == move.from + 16 && EnPassantM[move.to & 0x07] & Pawns(pos) & (pos->PM ^ (Occupation(pos))))
					pos->enPassant = move.to & 0x07; /* save enpassant column */
			}
		}
		pos->move50 = 0;
		FlipPosition(pos);
		break;
	case KNIGHT:
	case BISHOP:
	case ROOK:
	case QUEEN:
		if (move.flag & CAPTURE)
		{
			pos->P0 &= ~des;
			pos->P1 &= ~des;
			pos->P2 &= ~des;
		}
		pos->PM ^= sou | des;
		pos->P0 ^= (move.flag & 1) ? sou | des : 0;
		pos->P1 ^= (move.flag & 2) ? sou | des : 0;
		pos->P2 ^= (move.flag & 4) ? sou | des : 0;
		pos->enPassant = 8;
		if (move.flag & CAPTURE)
			pos->move50 = 0;
		FlipPosition(pos);
		if (!(move.flag & CAPTURE))
			pos->move50++;
		else
			pos->move50 = 0;
		break;
	case KING:
		if (move.flag & CAPTURE)
		{
			pos->P0 &= ~des;
			pos->P1 &= ~des;
			pos->P2 &= ~des;
		}
		pos->PM ^= sou | des;
		pos->P1 ^= sou | des;
		pos->P2 ^= sou | des;
		pos->enPassant = 8;
		if (move.flag & CAPTURE)
			pos->move50 = 0;
		else if (move.flag & CASTLE) {
			if (move.to == SQ_G1) {
				pos->PM ^= 0x00000000000000A0ULL;
				pos->P2 ^= 0x00000000000000A0ULL;
			} /* short castling */
			else {
				pos->P2 ^= 0x0000000000000009ULL;
				pos->PM ^= 0x0000000000000009ULL;
			} /* long castling */
		}
		FlipPosition(pos);
		if (!(move.flag & CAPTURE))
			pos->move50++;
		else
			pos->move50 = 0;
		break;
	}
	pos->castleFlags &= boardCastle[move.from] & boardCastle[move.to];
}

/* Evaluate the leaf positions */
static inline int Evaluate(Position* pos) {
	int scoreMg = 0;
	int scoreEg = 0;
	int phase = 0;
	int insufficent[2] = { 0 };
	for (int side = 0; side < 2; side++){
		/* for every piece sum the static value and the pst value */
		for (TPieceType pt = PAWN; pt < PT_NB; pt++)
			for (U64 pieces = BBPieces(pos, pt) & pos->PM; pieces; pieces = ClearLSB(pieces)) {
				int sq = LSB(pieces);
				phase += phaseVal[pt];
				insufficent[side] += insufVal[pt];
				scoreMg += mg_pst[pt][sq];
				scoreEg += eg_pst[pt][sq];
			}
		FlipPosition(pos);
		scoreMg = -scoreMg;
		scoreEg = -scoreEg;
	}
	if (max(insufficent[0], insufficent[1]) < 3)
		return 0;
	if (phase > 24) phase = 24;
	return (scoreMg * phase + scoreEg * (24 - phase)) / 24;
}

static int Eval(Position* pos, U64 hash) {
	TTEntryEval* ee = &ttEval[hash & ttMask];
	if (ee->hash != hash) {
		ee->hash = hash;
		ee->score = Evaluate(pos);
	}
	return (ee->score * (100 - pos->move50)) / 100;
}

static int Permill() {
	int pm = 0;
	for (int n = 0; n < 1000; n++)
		if (tt[n].hash)
			pm++;
	return pm;
}

static U64 GetHash(Position* pos) {
	U64 hash = pos->STM;
	U64 occupation = Occupation(pos);
	U64 copy = occupation & pos->PM;
	while (copy) {
		const int sq = LSB(copy);
		copy &= copy - 1;
		hash ^= keys[PieceType(pos, sq) * 64 + sq];
	}
	copy = occupation ^ pos->PM;
	while (copy) {
		const int sq = LSB(copy);
		copy &= copy - 1;
		hash ^= keys[(PieceType(pos, sq) | 0x8) * 64 + sq];
	}
	if (pos->enPassant < 8)
		hash ^= keys[pos->enPassant];
	if (pos->castleFlags)
		hash ^= keys[8 + pos->castleFlags];
	return hash;
}

static int IsPseudolegalMove(Position* pos, const TMove move) {
	TMove moves[256];
	const int num_moves = GenerateMoves(pos, moves, 0);
	for (int i = 0; i < num_moves; ++i)
		if (moves[i].Move == move.Move)
			return 1;
	return 0;
}

static void PrintPv(Position* pos, const TMove move) {
	if (!IsPseudolegalMove(pos, move))
		return;
	if (Illegal(pos, move))
		return;
	char strmove[8];
	MoveToStr(strmove, move, pos->STM);
	printf(" %s", strmove);
	const Position npos = *pos;
	Make(&npos, move);
	const U64 hash = GetHash(&npos);
	TTEntry* ttEntry = tt + (hash & ttMask);
	if (ttEntry->hash == hash && !IsRepetition(&npos, hash)) {
		historyHash[historyCount++] = hash;
		PrintPv(&npos, ttEntry->move);
		historyCount--;
	}
}

static void PrintInfo(Position* pos, int depth, int score) {
	printf("info depth %d score ", depth);
	if (abs(score) < MATE - MAX_PLY)
		printf("cp %d", score);
	else
		printf("mate %d", (score > 0 ? (MATE - score + 1) >> 1 : -(MATE + score) >> 1));
	printf(" time %lld", GetTimeMs() - info.timeStart);
	printf(" nodes %lld", info.nodes);
	printf(" hashfull %d pv", Permill());
	PrintPv(pos, ss[0].move);
	printf("\n");
}

static int IsRepetition(Position* pos, U64 hash) {
	int limit = max(0, historyCount - pos->move50);
	for (int n = historyCount - 4; n >= limit; n -= 2)
		if (historyHash[n] == hash)
			return TRUE;
	return FALSE;
}

static void PrintBoard(Position* pos) {
	int blackTurn = pos->STM == BLACK;
	if (blackTurn)
		FlipPosition(pos);
	const char* s = "   +---+---+---+---+---+---+---+---+\n";
	const char* t = "     A   B   C   D   E   F   G   H\n";
	printf(t);
	for (int r = 7; r >= 0; r--) {
		printf(s);
		printf(" %d |", r + 1);
		for (int f = 0; f < 8; f++) {
			int sq = r * 8 + f;
			int pt = PieceType(pos, sq);
			if (pos->PM & (1ull << sq))
				printf(" %c |", " ANBRQK"[pt]);
			else
				printf(" %c |", " anbrqk"[pt]);
		}
		printf(" %d \n", r + 1);
	}
	printf(s);
	printf(t);
	U64 hash = GetHash(pos);
	S16 score = Evaluate(pos);
	char castling[5] = "KQkq";
	for (int n = 0; n < 4; n++)
		if (!(pos->castleFlags & (1 << n)))
			castling[n] = '-';
	printf("side     : %16s\n", blackTurn ? "black" : "white");
	printf("castling : %16s\n", castling);
	printf("hash     : %16llx\n", hash);
	printf("score    : %16d\n", score);
	if (blackTurn)
		FlipPosition(pos);
}

static int SearchAlpha(Position* pos, int alpha, int beta, int depth, int ply, int do_null) {
	if (CheckUp(pos))
		return 0;
	int  mateValue = MATE - ply;
	if (alpha < -mateValue)
		alpha = -mateValue;
	if (beta > mateValue - 1)
		beta = mateValue - 1;
	if (alpha >= beta)
		return alpha;
	const U64 hash = GetHash(pos);

	TTEntry* ttEntry = tt + (hash & ttMask);
	TMove tt_move = { 0 };
	int inPv = beta - alpha > 1;
	if (ttEntry->hash == hash) {
		tt_move = ttEntry->move;
		if (!inPv && ttEntry->depth >= depth) {
			if (ttEntry->flag == EXACT)return ttEntry->score;
			if (ttEntry->flag == LOWER && ttEntry->score <= alpha)return ttEntry->score;
			if (ttEntry->flag == UPPER && ttEntry->score >= beta)return ttEntry->score;
		}
	}
	else
		depth -= depth > 3;

	U64 inCheck = InCheck(pos);
	if (inCheck)
		depth = max(1, depth + 1);
	int inQuiescence = depth < 1;
	if (ply && !inQuiescence)
		if (pos->move50 >= 100 || IsRepetition(pos, hash))
			return 0;

	const int staticEval = ss[ply].score = Eval(pos, hash);
	const int improving = ply > 1 && staticEval > ss[ply - 2].score;
	if (ply >= MAX_PLY)
		return staticEval;
	if (inQuiescence && alpha < staticEval) {
		alpha = staticEval;
		if (alpha >= beta)
			return beta;
	}

	if (ply && !inQuiescence && !inCheck && !inPv) {

		// Reverse futility pruning
		if (depth < 8) {
			if (staticEval - 71 * (depth - improving) >= beta)
				return staticEval;

			//inQuiescence = staticEval + 238 * depth < alpha;
		}

		// Null move pruning
		if (depth > 2 && staticEval >= beta && staticEval >= ss[ply].score && do_null &&
			pos->PM & ~Pawns(pos) & ~Kings(pos)) {
			Position npos = *pos;
			FlipPosition(&npos);
			npos.enPassant = 0;
			if (-SearchAlpha(&npos,
				-beta,
				-alpha,
				depth - 4 - depth / 5 - min((staticEval - beta) / 196, 3),
				ply + 1,
				0) >= beta)
				return beta;
		}
	}

	historyHash[historyCount++] = hash;
	int score;
	int color = pos->STM == WHITE ? 0 : 1;
	U8 ttFlag = LOWER;
	int legalMoves = 0;
	int quietMoves = 0;
	TMove qList[256];
	S64 scoreList[256];
	TMove movesList[256];
	int movesCount = GenerateMoves(pos, movesList, inQuiescence);
	for (int j = 0; j < movesCount; ++j) {
		TMove m = movesList[j];
		const int ptSou = PieceType(pos, m.from);
		int ptDes = m.promo ? m.promo : PieceType(pos, m.to);
		if (m.Move == tt_move.Move)
			scoreList[j] = 1LL << 62;
		else if (ptDes != PT_NB)
			scoreList[j] = ((ptDes + 1) * (1LL << 54)) - ptSou;
		else if (m.Move == ss[ply].killer1.Move)
			scoreList[j] = 1LL << 50;
		else if (m.Move == ss[ply].killer2.Move)
			scoreList[j] = 1LL << 48;
		else
			scoreList[j] = hh[color][m.from][m.to];
	}
	for (int i = 0; i < movesCount; ++i) {
		int bstIdx = i;
		for (int j = i + 1; j < movesCount; ++j)
			if (scoreList[bstIdx] < scoreList[j])
				bstIdx = j;
		TMove move = movesList[bstIdx];
		scoreList[bstIdx] = scoreList[i];
		movesList[bstIdx] = movesList[i];

		//int gain = move.MoveType & (CAPTURE | PROMO);
		int gain = mx_material[PieceType(pos, move.to)];
		if(move.flag & PROMO)
			gain += mx_material[move.promo];
		if(move.flag & EP)
			gain += mx_material[PAWN];
		// Delta pruning
		if (inQuiescence && !inCheck && staticEval + 50 + gain < alpha)
			break;

		// Forward futility pruning
		if (ply > 0 && depth < 8 && !inQuiescence && !inCheck && legalMoves && staticEval + 105 * depth + gain < alpha)
			break;

		if (Illegal(pos, move))
			continue;
		Position npos = *pos;
		Make(&npos, move);

		if (!legalMoves || depth < 4)
			score = -SearchAlpha(&npos, -beta, -alpha, depth - 1, ply + 1,1);
		else {
			int r = !inPv;
			score = -SearchAlpha(&npos, -alpha - 1, -alpha, depth - 1 - r, ply + 1,1);
			if (r && score > alpha)
				score = -SearchAlpha(&npos, -alpha - 1, -alpha, depth - 1, ply + 1,1);
			if (score > alpha && score < beta)
				score = -SearchAlpha(&npos, -beta, -alpha, depth - 1, ply + 1,1);
		}
		if (info.stop)
			break;
		legalMoves++;
		if (!gain)
			qList[quietMoves++] = move;
		if (alpha < score) {
			alpha = score;
			ttFlag = EXACT;
			ss[ply].move = move; /* save the best move found at this ply */
			if (!ply && info.post)
				PrintInfo(pos, depth, score);
		}
		if (alpha >= beta) {
			ttFlag = UPPER;
			if (!(move.flag & (CAPTURE | PROMO))) {
				ss[ply].killer2 = ss[ply].killer1;
				ss[ply].killer1 = move;
			}
			int bonus = depth * depth;
			int h = hh[color][move.from][move.to];
			h += bonus - h * bonus / 1024;
			hh[color][move.from][move.to] = h;
			for (int n = 0; n < quietMoves; n++) {
				TMove m = qList[n];
				int hm = hh[color][m.from][m.to];
				hm -= bonus - hm * bonus / 1024;
				hh[color][m.from][m.to] = hm;
			}
			break;
		}
		// Late move pruning based on quiet move count
		if (!inCheck && !inPv && quietMoves > 1 + depth * depth >> !improving)break;
	}

	historyCount--;
	if (info.stop)
		return 0;
	if (!legalMoves && !inQuiescence)
		return inQuiescence ? alpha : inCheck ? ply - MATE : 0;
	ttEntry->hash = hash;
	ttEntry->move = ss[ply].move;
	ttEntry->depth = max(0, depth);
	ttEntry->score = alpha;
	ttEntry->flag = ttFlag;
	return alpha;
}

static void SearchIteratively(Position* pos) {
	TTClear();
	SSClear();
	int score = 0;
	int alpha = -MATE;
	int beta = MATE;
	for (int depth = 1; depth <= info.depthLimit; ++depth) {
		int aspH = 16, aspL = 16;
		do {
			if (depth > 4) {
				alpha = score - aspL;
				beta = score + aspH;
			}
			score = SearchAlpha(pos, alpha, beta, depth, 0,1);
			if (score <= alpha) {
				alpha -= aspL;
				aspL *= 2;
			}
			else if (score >= beta) {
				beta += aspH;
				aspH *= 2;
			}
			else
				break;
		} while (!info.stop);
		if (info.stop)
			break;
		if (info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit / 2)
			break;
	}
	if (info.post) {
		char strmove[8];
		MoveToStr(strmove, ss[0].move, pos->STM);
		printf("bestmove %s\n", strmove);
		fflush(stdout);
	}
}

/*
Load a position starting from a fen and a list of moves.
This function doesn't check the correctness of the fen and the moves sent.
*/
static void SetFen(Position* pos, const char* fen) {
	historyCount = 0;
	pos->P0 = pos->P1 = pos->P2 = pos->PM = 0;
	pos->enPassant = 8;
	pos->STM = WHITE;
	pos->move50 = 0;
	pos->castleFlags = 0;

	/* translate the fen to the relative position */
	U8 pieceside = WHITE;
	U8 piece = PAWN;
	uint64_t square = 0;
	const char* cursor;
	for (cursor = fen; *cursor != ' '; cursor++)
	{
		if (*cursor >= '1' && *cursor <= '8')
			square += *cursor - '0';
		else if (*cursor == '/')
			continue;
		else
		{
			uint64_t sq = FLIP(square);
			if (*cursor == 'p') { piece = PAWN; pieceside = BLACK; }
			else if (*cursor == 'n') { piece = KNIGHT; pieceside = BLACK; }
			else if (*cursor == 'b') { piece = BISHOP; pieceside = BLACK; }
			else if (*cursor == 'r') { piece = ROOK; pieceside = BLACK; }
			else if (*cursor == 'q') { piece = QUEEN; pieceside = BLACK; }
			else if (*cursor == 'k') { piece = KING; pieceside = BLACK; }
			else if (*cursor == 'P') { piece = PAWN; pieceside = WHITE; }
			else if (*cursor == 'N') { piece = KNIGHT; pieceside = WHITE; }
			else if (*cursor == 'B') { piece = BISHOP; pieceside = WHITE; }
			else if (*cursor == 'R') { piece = ROOK; pieceside = WHITE; }
			else if (*cursor == 'Q') { piece = QUEEN; pieceside = WHITE; }
			else if (*cursor == 'K') { piece = KING; pieceside = WHITE; }
			pos->P0 |= ((uint64_t)piece & 1) << sq;
			pos->P1 |= ((uint64_t)(piece >> 1) & 1) << sq;
			pos->P2 |= ((uint64_t)piece >> 2) << sq;
			if (pieceside == WHITE) { pos->PM |= 1ULL << sq; piece |= BLACK; }
			square++;
		}
	}
	cursor++; /* read the side to move  */
	int sideBlack = *cursor == 'b';
	cursor += 2;
	if (*cursor != '-') /* read the castle rights */
	{
		for (; *cursor != ' '; cursor++)
		{
			if (*cursor == 'K')
				pos->castleFlags |= CASTLE_WK;
			else if (*cursor == 'Q')
				pos->castleFlags |= CASTLE_WQ;
			else if (*cursor == 'k')
				pos->castleFlags |= CASTLE_BK;
			else if (*cursor == 'q')
				pos->castleFlags |= CASTLE_BQ;
		}
		cursor++;
	}
	else cursor += 2;
	if (*cursor != '-') /* read the enpassant column */
	{
		pos->enPassant = *cursor - 'a';
		cursor++;
	}
	else cursor += 2;
	char counter50moves[4];
	char* pcounter;
	for (pcounter = counter50moves; *cursor != ' '; cursor++, pcounter++) *pcounter = *cursor; /* copy the string */
	*pcounter = '\0';
	pos->move50 = atoi(counter50moves); /* convert the string counter to integer */
	if (sideBlack)
		FlipPosition(pos);
}

static inline void PerftDriver(Position* pos, int depth) {
	TMove moves[256];
	const int numMoves = GenerateMoves(pos, moves, 0);
	for (int n = 0; n < numMoves; n++) {
		TMove move = moves[n];
		if (Illegal(pos, move))
			continue;
		if (depth) {
			Position npos = *pos;
			Make(&npos, move);
			PerftDriver(&npos, depth - 1);
		}
		else
			info.nodes++;
	}
}

static int ShrinkNumber(U64 n) {
	if (n < 10000)
		return 0;
	if (n < 10000000)
		return 1;
	if (n < 10000000000)
		return 2;
	return 3;
}

static void PrintSummary(U64 time, U64 nodes) {
	U64 nps = (nodes * 1000) / max(time, 1);
	const char* units[] = { "", "k", "m", "g" };
	int sn = ShrinkNumber(nps);
	int p = pow(10, sn * 3);
	int b = pow(10, 3);
	printf("-----------------------------\n");
	printf("Time        : %llu\n", time);
	printf("Nodes       : %llu\n", nodes);
	printf("Nps         : %llu (%llu%s/s)\n", nps, nps / p, units[sn]);
	printf("-----------------------------\n");
}

static void PrintPerformanceHeader() {
	printf("-----------------------------\n");
	printf("ply      time        nodes\n");
	printf("-----------------------------\n");
}

static void ResetInfo() {
	info.timeStart = GetTimeMs();
	info.timeLimit = 0;
	info.depthLimit = MAX_PLY;
	info.nodesLimit = 0;
	info.nodes = 0;
	info.stop = FALSE;
	info.post = TRUE;
}

//performance test
static void UciPerformance(Position* pos) {
	ResetInfo();
	PrintPerformanceHeader();
	info.depthLimit = 0;
	U64 elapsed = 0;
	while (elapsed < 3000) {
		PerftDriver(pos, info.depthLimit++);
		elapsed = GetTimeMs() - info.timeStart;
		printf(" %2d. %8llu %12llu\n", info.depthLimit, elapsed, info.nodes);
	}
	PrintSummary(elapsed, info.nodes);
}

//start benchmark
static void UciBench(Position* pos) {
	ResetInfo();
	PrintPerformanceHeader();
	info.depthLimit = 0;
	info.post = FALSE;
	U64 elapsed = 0;
	while (elapsed < 3000) {
		++info.depthLimit;
		SearchIteratively(pos);
		elapsed = GetTimeMs() - info.timeStart;
		printf(" %2d. %8llu %12llu\n", info.depthLimit, elapsed, info.nodes);
	}
	PrintSummary(elapsed, info.nodes);
}

static void SetMoves(Position* pos, char* str) {
	char buffer[4000];
	strcpy(buffer, str);
	char* strmove;
	for (strmove = strtok(buffer, " "); strmove; strmove = strtok(NULL, " ")) {
		TMove move = StrToMove(pos, strmove);
		historyHash[historyCount++] = GetHash(pos);
		Make(pos, move);
		if (pos->move50 == 0)
			historyCount = 0;
	}
}

static void ParsePosition(Position* pos, char* str) {
	char* fen = strstr(str, "fen");
	char* mov = strstr(str, "moves");
	if (!fen)
		fen = START_FEN;
	else
		fen += 4;
	SetFen(pos, fen);
	if (mov)
		SetMoves(pos, mov + 6);
}

static void ParseGo(Position* pos, char* command) {
	ResetInfo();
	int wtime = 0;
	int btime = 0;
	int winc = 0;
	int binc = 0;
	int movestogo = 32;
	char* argument = NULL;
	if (argument = strstr(command, "binc"))
		binc = atoi(argument + 5);
	if (argument = strstr(command, "winc"))
		winc = atoi(argument + 5);
	if (argument = strstr(command, "wtime"))
		wtime = max(1, atoi(argument + 6));
	if (argument = strstr(command, "btime"))
		btime = max(1, atoi(argument + 6));
	if ((argument = strstr(command, "movestogo")))
		movestogo = atoi(argument + 10);
	if ((argument = strstr(command, "movetime")))
		info.timeLimit = atoi(argument + 9);
	if ((argument = strstr(command, "depth")))
		info.depthLimit = atoi(argument + 6);
	if (argument = strstr(command, "nodes"))
		info.nodesLimit = atoi(argument + 5);
	int time = pos->STM ? btime : wtime;
	int inc = pos->STM ? binc : winc;
	if (time)
		info.timeLimit = max(1, min(time / movestogo + inc, time / 2));
	SearchIteratively(pos);
}

void UciCommand(Position* pos, char* str) {
	if (!strncmp(str, "ucinewgame", 10));
	else if (!strncmp(str, "uci", 3)) {
		printf("id name %s\nuciok\n", NAME);
		fflush(stdout);
	}
	else if (!strncmp(str, "isready", 7)) {
		printf("readyok\n");
		fflush(stdout);
	}
	else if (!strncmp(str, "go", 2))ParseGo(pos, str + 2);
	else if (!strncmp(str, "position", 8))ParsePosition(pos, str + 8);
	else if (!strncmp(str, "print", 5))PrintBoard(pos);
	else if (!strncmp(str, "perft", 5))UciPerformance(pos);
	else if (!strncmp(str, "bench", 5))UciBench(pos);
	else if (!strncmp(str, "stop", 4))info.stop = TRUE;
	else if (!strncmp(str, "quit", 4))exit(0);
}

static void UciLoop(Position* pos) {
	//TestPerft();
	//UciCommand("position startpos moves d2d4 d7d5 c2c4 e7e6 b1c3 g8f6 g1f3 c7c5 c1g5 c5d4 f3d4 d5c4 e2e3 d8b6 f1c4 f8e7 e1g1 e8g8 d1c2 b8c6 d4c6 b6c6 c4d3 h7h6 g5h4 c8d7 d3b5 c6c8 b5d7 c8d7 a1d1 d7c6 e3e4 e6e5 c2e2 a8e8 c3d5 f6d5 e4d5 c6d6 h4e7 e8e7 f1e1 e5e4 d1d4 f8d8 h2h3 f7f5 a2a4 d8e8 e2c2 b7b6 c2c6 e7d7 e1c1 e8d8 c6d6 d7d6 c1d1 g8f7 b2b4 f7f6 a4a5 f6e5 d4c4");
	//UciCommand("position fen 8/3P4/1p3b1p/p7/P7/1P3NPP/4p1K1/3k4 w - - 0 1");
	//UciCommand("position startpos moves e2e4 b8c6 d2d4 e7e5 d4e5 d7d6 e5d6 f8d6 c2c3 g8f6 g2g4 c8g4 d1d3 c6e5 d3c2 e5f3 g1f3 g4f3 b2b3 f3h1 f1b5 c7c6 c1g5 c6b5 g5e3 h1e4 c2e2 e8g8 a2a3 f6d5");
	//UciCommand("position startpos moves e2e4 b8c6 d2d4 e7e5 d4e5 d7d6 e5d6 f8d6 c2c3 g8f6 g2g4 c8g4 d1d3 c6e5 d3c2 e5f3 g1f3 g4f3 b2b3 f3h1 f1b5");
	//UciCommand("print");
	//UciCommand("go movetime 1000");
	//UciCommand("go depth 1");
	char str[4000];
	while (fgets(str, sizeof(str), stdin))
		UciCommand(pos, str);
}

static void Init() {
	for (int pt = PAWN; pt <= KING; pt++) {
		for (int sq = 0; sq < 64; sq++) {
			int mg = mg_material[pt] + mg_table[pt][sq];
			int eg = eg_material[pt] + eg_table[pt][sq];
			mg_pst[pt][FLIP(sq)] = mg;
			eg_pst[pt][FLIP(sq)] = eg;
		}
	}
}

static void InitTT(U64 mb) {
	ttSize = 1;
	while (ttSize < mb * 1000 * 1000 / (sizeof(TTEntry)) + sizeof(TTEntryEval))
		ttSize <<= 1;
	ttMask = ttSize - 1;
	free(tt);
	free(ttEval);
	tt = (TTEntry*)malloc(sizeof(TTEntry) * ttSize);
	ttEval = (TTEntryEval*)malloc(sizeof(TTEntryEval) * ttSize);
	TTClear();
}

int main(const int argc, const char** argv) {
	Init();
	InitHash();
	InitTT(32);
	printf("%s %s\n", NAME, VERSION);
	SetFen(&position, START_FEN);
	UciLoop(&position);
}