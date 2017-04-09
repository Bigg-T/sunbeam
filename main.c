#include <stdio.h>
#include <stdlib.h>
#include "gc.h"

extern int our_code_starts_here(int* HEAP) asm("our_code_starts_here");
extern void error() asm("error");
extern int print(int val) asm("print");
extern int equal(int val1, int val2) asm("equal");
extern int* try_gc(int* alloc_ptr, int amount_needed, int* first_frame, int* stack_top) asm("try_gc");
extern int* HEAP_END asm("HEAP_END");
extern int* STACK_BOTTOM asm("STACK_BOTTOM");
extern int check_fun_name(int val) asm("check_fun_name");
extern int is_eight_bit_boundary(int val) asm("is_eight_bit_boundary");
extern int printStack(int val, int* esp, int* ebp, int args) asm("print_stack");

const int NUM_TAG_MASK   = 0x00000001;
const int TUPLE_TAG_MASK = 0x00000007;
const int BOOL_TRUE      = 0xFFFFFFFF;
const int BOOL_FALSE     = 0x7FFFFFFF;
const int TUPLE_TAG_MASK_OP = 0xFFFFFFF8;


const int ERR_COMP_NOT_NUM   = 1;
const int ERR_ARITH_NOT_NUM  = 2;
const int ERR_LOGIC_NOT_BOOL = 3;
const int ERR_IF_NOT_BOOL    = 4;
const int ERR_OVERFLOW       = 5;
const int ERR_GET_NOT_TUPLE  = 6;
const int ERR_GET_LOW_INDEX  = 7;
const int ERR_GET_HIGH_INDEX = 8;
const int ERR_INDEX_NOT_NUM  = 9;
const int ERR_OUT_OF_MEMORY  = 10;
const int ERR_INDEX_OUT_OF_BOUNDS = 11;
const int ERR_ARITY_MISMATCH = 12;

size_t HEAP_SIZE;
int* STACK_BOTTOM;
int* HEAP;
int* HEAP_END;
int* HEAP_NEW;
const int DEBUG = 0;

int equal(int val1, int val2) {
  if(val1 == val2) { return BOOL_TRUE; }
  else { return BOOL_FALSE; }
}

int check_fun_name(int val) {
  int is_lambda = (val & 5) == 5;
  if (is_lambda) {
    int* fn_tuple_addr = (val & TUPLE_TAG_MASK_OP);
    // printf("fn_tuple_addr[0]: %d\n", fn_tuple_addr[2]);
    return fn_tuple_addr;//fn_tuple_addr[1];
  } else {
    fprintf(stderr, "Error: invalid type for call operator, instead got %x\n", val);
    exit(val);
  }
}

int is_eight_bit_boundary(int val) {
  fprintf(stderr, "got into eight bit land %x\n", (val));
  printf("successfully got into function");
  exit(val);
}

int printStack(int val, int* esp, int* ebp, int args) {
  printf("Stack bottom: %#010x\t==>  \n", (uint)STACK_BOTTOM);
  // print(*STACK_BOTTOM);
  printf("ESP: %#010x\t==>  ", (uint)esp);
  print(*esp);
  printf("\n");
  printf("EBP: %#010x\t==>  ", (uint)ebp);
  print(*ebp);
  printf("\n");
  printf("(difference: %d)\n", esp - ebp);
  printf("Requested return val: %#010x ==> \n", val);
  printf("Requested return val addr: %#010x \n", &val);
  print(val);

  if (esp > ebp) {
    printf("Error: ESP and EBP are not properly oriented\n");
  } else {
    printf("args: %d\n", args);
    for (int* cur = esp + 1; cur < ebp + args + 2; cur++) {
      if (cur == ebp) {
        printf("EBP %#010x: %#010x\t ==>  old ebp\n", (uint)cur, *cur);
      }
      else if (cur == ebp + 1) {
        printf("    %#010x: %#010x\t ==>  saved ret\n", (uint)cur, *cur);
      }
      else {
        printf("    %#010x: %#010x\t ==>  \n", (uint)cur, *cur);
      }
    }
  }
  return val;
}

int tupleCounter = 0;
void printHelp(FILE *out, int val) {
  if((val & NUM_TAG_MASK) == 0) {
    fprintf(out, "%d", val >> 1);
  }
  else if(val == BOOL_TRUE) {
    fprintf(out, "true");
  }
  else if(val == BOOL_FALSE) {
    fprintf(out, "false");
  }
  else if ((val & TUPLE_TAG_MASK) == 5) {
    fprintf(out, "<function>");
  }
  else if ((val & TUPLE_TAG_MASK) != 0) {
    int* addr = (int*)(val - 1);
    // Check whether we've visited this tuple already
    if ((*addr & 0x80000000) != 0) {
      fprintf(out, "<cyclic tuple %d>", (int)(*addr & 0x7FFFFFFF));
      return;
    }
    // Mark this tuple: save its length locally, then mark it
    int len = addr[0];
    fprintf(out, "the addr[0] is: %d\n", addr[0]);
    *(addr) = 0x80000000 | (++tupleCounter);
    fprintf(out, "(");
    for (int i = 1; i <= len; i++) {
      if (i > 1) fprintf(out, ", ");
      printHelp(out, addr[i]);
    }
    fprintf(out, ")");
    // Unmark this tuple: restore its length
    *(addr) = len;
  }
  else {
    fprintf(out, "Unknown value: %#010x", val);
  }
}

void printHelpOld(FILE *out, int val) {
  // printf("print val at: %x\n", val);
  // int is_lambda = ((val << 29) >> 29) == 5;
  int is_lambda = (val & 0x5) == 5;
  if((val & NUM_TAG_MASK) == 0) {
    fprintf(out, "%d", val >> 1);
  }
  else if(val == BOOL_TRUE) {
    fprintf(out, "true");
  }
  else if(val == BOOL_FALSE) {
    fprintf(out, "false");
  }
  else if (((val & TUPLE_TAG_MASK) != 0) && !is_lambda) {
    int* addr = (int*)(val & ~0x7);
    fprintf(out, "(");
    int len = addr[0] >> 1;
    // fprintf(out, "[%d]", len);
    for (int i = 1; i <= len; i++) {
      if (i > 1) fprintf(out, ", ");
      printHelpOld(out, addr[i]);
    }
    fprintf(out, ")");
  }
  else if (is_lambda) {
    fprintf(out, "<function>");
  }
  else {
    fprintf(out, "Unknown value: %#010x", val);
  }
}


int print(int val) {
  // we're using printHelpOld because we're experiencing some really
  // strange behavior with the tuple case in your printHelp...
  printHelpOld(stdout, val);
  printf("\n");
  return val;
}

void error(int i) {
  switch (i) {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number\n");
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number\n");
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "Error logic expected a boolean\n");
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean\n");
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: Integer overflow\n");
    break;
  case ERR_INDEX_OUT_OF_BOUNDS:
    fprintf(stderr, "Error: index out of bounds\n");
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "Error: get expected tuple\n");
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to get\n");
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to get\n");
    break;
  case ERR_INDEX_NOT_NUM:
    fprintf(stderr, "Error: get expected number for index\n");
    break;
  case ERR_ARITY_MISMATCH:
    fprintf(stderr, "Error: arity mismatch\n");
    break;
  default:
    fprintf(stderr, "Error: Unknown error code: %d\n", i);
  }
  exit(i);
}

void print_closure(int closure_addr, int total_freevars) {
  int is_lambda = (closure_addr & 5) == 5;
  if (is_lambda) {
    int* fn_tuple_addr = (closure_addr & TUPLE_TAG_MASK_OP);
    for (int i = 0; i < total_freevars; i++) {
      printf("fn_tuple_addr[%d]: %d\n", (i + 2), fn_tuple_addr[(i + 2)]);
    }
    return; // fn_tuple_addr;//fn_tuple_addr[1];
  } else {
    fprintf(stderr, "Error: invalid type for call operator, instead got %x\n", closure_addr);
    exit(closure_addr);
  }
}

/*
  Try to reserve the desired number of bytes of memory, and free garbage if
  needed.  Fail (and exit the program) if there is insufficient memory.  Does
  not actually allocate the desired number of bytes of memory; the caller
  will do that.

  Arguments:

    int* alloc_ptr - the current top of the heap (which we store in ESI), where
                     the next allocation should occur, if possible
    int bytes_needed - the number of bytes of memory we want to allocate
                       (including padding)
    int* cur_frame - the base pointer of the topmost stack frame of our code
                     (i.e., EBP)
    int* cur_stack_top - the stack pointer of the topmost stack frame of our
                         code (i.e., ESP)

  Returns:
    The new top of the heap (i.e. the new value of ESI) after garbage collection.
    Does not actually allocate bytes_needed space.

  Side effect:
    Also updates HEAP_END to point to the new end of the heap, if it's changed
*/
int* try_gc(int* alloc_ptr, int bytes_needed, int* cur_frame, int* cur_stack_top) {
  int* new_heap = (int*)calloc(HEAP_SIZE, sizeof(int));
  int* new_heap_end = new_heap + HEAP_SIZE;
  int* old_heap = HEAP;
  int* old_heap_end = HEAP_END;
  int* new_esi = NULL;

  // Do you trust your new GC?
  int CONFIDENT = 1;

  // Abort early, if we can't allocate a new to-space
  if (new_heap == NULL) {
    fprintf(stderr, "Out of memory: could not allocate a new semispace for garbage collection");
    exit(ERR_OUT_OF_MEMORY);
  }

  // When you're confident in your collector, enable the following lines to trigger your GC

  if (CONFIDENT) {
    if (DEBUG) {
      fprintf(stdout, "Heap directly before call to gc:\n");
      naive_print_heap(HEAP, HEAP_SIZE);
      fprintf(stdout, "-------------------------\n");
      fprintf(stdout, "esi directly before call to gc: %x\n", alloc_ptr);
      fprintf(stdout, "-------------------------\n");
    }
    new_esi = gc(STACK_BOTTOM, cur_frame, cur_stack_top, HEAP, HEAP_END, new_heap);
    if (DEBUG) {
      fprintf(stdout, "Heap directly after call to gc:\n");
      naive_print_heap(HEAP, HEAP_SIZE);
      fprintf(stdout, "-------------------------\n");
      fprintf(stdout, "esi directly after call to gc: %x\n", new_esi);
      fprintf(stdout, "-------------------------\n");
    }
    HEAP_NEW = new_esi;
    HEAP = new_heap;
    HEAP_END = new_heap_end;
    free(old_heap);
    if (DEBUG) {
      fprintf(stdout, "Heap directly after free:\n");
      naive_print_heap(HEAP, HEAP_SIZE);
      fprintf(stdout, "-------------------------\n");
    }
  } else {
    // This just keeps ESI where it is, and cleans up after the unneeded allocation
    free(new_heap);
    new_heap = NULL;
    new_esi = alloc_ptr;
  }

  // Note: strict greater-than is correct here: if new_esi + (bytes_needed / 4) == HEAP_END,
  // that does not mean we're *using* the byte at HEAP_END, but rather that it would be the
  // next free byte, which is still ok and not a heap-overflow.
  if (bytes_needed / 4 > HEAP_SIZE) {
    fprintf(stdout, "Heap before error:\n");
    naive_print_heap(HEAP, HEAP_SIZE);
    fprintf(stderr, "Allocation error: needed %d words, but the heap is only %d words",
            bytes_needed / 4, HEAP_SIZE);
    exit(ERR_OUT_OF_MEMORY);
  } else if((new_esi + (bytes_needed / 4)) > HEAP_END) {
    fprintf(stdout, "Heap before error:\n");
    naive_print_heap(HEAP, HEAP_SIZE);
    fprintf(stderr, "new_esi: %x \n", new_esi);
    fprintf(stderr, "Out of memory: needed %d words, but only %d remain after collection",
            bytes_needed / 4, (HEAP_END - new_esi));
    if (new_heap != NULL) free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  }
  else {
    if (DEBUG) {
      fprintf(stdout, "Heap before returning new_esi:\n");
      naive_print_heap(HEAP, HEAP_SIZE);
      fprintf(stdout, "esi: %x\tnew_esi: %x\n", alloc_ptr, new_esi);
    }
    return new_esi;
  }
}

int main(int argc, char** argv) {
  if(argc > 1) {
    HEAP_SIZE = atoi(argv[1]);
  }
  else {
    HEAP_SIZE = 100000;
  }
  HEAP = (int*)calloc(HEAP_SIZE, sizeof (int));
  HEAP_END = HEAP + HEAP_SIZE;
  if (DEBUG) {
    fprintf(stdout, "Initial heap:\n");
    naive_print_heap(HEAP, HEAP_SIZE);
  }
  int result = our_code_starts_here(HEAP);
  if (DEBUG) {
    fprintf(stdout, "----------------\n");
    fprintf(stdout, "Final heap:\n");
    naive_print_heap(HEAP, HEAP_SIZE);
  }
  print(result);
  return 0;
}
