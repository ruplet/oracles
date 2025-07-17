/* ANSI C89/C90 Compliant Strict Aliasing Example */
#include <stdio.h>

/*
 * NOTE: For strict ANSI C89/C90, stdint.h is not part of the standard.
 * We will remove the use of intptr_t for address comparison,
 * which was auxiliary to the core UB demonstration.
 * The core UB here is accessing a float's memory through an int* and then
 * reading it back as a float, which is undefined by strict aliasing rules.
 */

int check_and_do_something() {
    int i_val;    /* Declare all variables at the beginning of the block */
    float f_val;

    /* Initialize float to 0.0f. This is the value the compiler might assume it keeps. */
    f_val = 0.0f;
    i_val = 0x79345678; /* A non-zero integer value */

    /*
     * This is the type-punning operation.
     * The C standard's strict aliasing rules state that if you write to a memory
     * location using one type (here, int via int*), and then read it back
     * using an incompatible type (here, float), the behavior is undefined.
     * The only exceptions are char* and types within a union.
     */
    *(int *)&f_val = i_val; /* UB occurs here if 'f_val' is later read as float */

    /*
     * This is the "non-trivial check" that seems to guard against something.
     * However, due to the UB in the previous line, the compiler is allowed
     * to assume that 'f_val' *still has its original value of 0.0f* when read
     * as a float, because if it changed due to the int* write, it would be UB.
     * Therefore, the compiler can effectively "prove" that this condition
     * (f_val == 0.0f) is true.
     */
    if (f_val == 0.0f) {
        printf("Float is zero. (Compiler's UB assumption in action)\n");
        return 0;
    } else {
        /* This branch might be optimized out, even at -O0,
         * because the compiler assumes it's unreachable in a valid program. */
        printf("Float is non-zero. Value of f_val: %f\n", f_val);
        return 1;
    }
}

int main() {
    int result; /* Declare variable at the beginning of the block */
    result = check_and_do_something();
    printf("Result from function: %d\n", result);
    return 0;
}