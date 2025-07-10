/* ub_branch_elimination.c */
/* This code is ANSI C89/C90 compliant */

#include <stdio.h>

/*
 * This function takes an integer pointer.
 * It's designed to expose how UB assumptions can eliminate branches.
 */
int process_pointer_and_check(int *ptr) {
    /*
     * This is the "guaranteed Undefined Behavior" point if ptr is NULL.
     * The C standard says dereferencing a null pointer is UB.
     * If ptr is NULL, the program's behavior here is undefined.
     * The compiler can assume 'ptr' is NOT NULL at this line,
     * because if it were, it'd be UB, and a valid program wouldn't do that.
     */
    *ptr = 123; /* WRITE TO POTENTIALLY NULL POINTER - UB HERE IF ptr IS NULL! */

    /*
     * This is the "non-trivial check" or "conditional branch".
     * It's meant to detect a scenario that should logically only happen
     * if 'ptr' was (or became) NULL.
     * The compiler, by assuming the previous line (*ptr = 123;) was valid,
     * can "prove" that 'ptr' must be non-NULL here.
     * Therefore, the condition 'ptr == (int*)0' can be "proved" false.
     */
    if (ptr == (int*)0) { /* Equivalent to ptr == NULL in C89/C90 */
        /*
         * This branch should *logically* be taken if the input 'ptr' was NULL.
         * However, due to UB, the compiler can optimize it out.
         */
        printf("ERROR: Pointer was NULL after dereference (branch NOT eliminated at -O0?)!\n");
        return 1; /* Indicate error detected */
    }

    /* This line will only be reached if the 'if' condition was false. */
    printf("Pointer was non-NULL. Value set to %d.\n", *ptr);
    return 0; /* Indicate no error detected */
}

int main() {
    /* Declare all variables at the beginning of the block in C89/C90 */
    int local_var;
    int *valid_ptr;
    int *null_ptr;
    int result_OOB; /* Renamed for clarity in this example context */

    local_var = 456;
    valid_ptr = &local_var;
    null_ptr = (int*)0; /* NULL in C89/C90 is implementation defined, (int*)0 is typical. */

    printf("--- Test Case 1: Valid Pointer ---\n");
    process_pointer_and_check(valid_ptr);
    printf("local_var after valid write: %d\n\n", local_var);

    printf("--- Test Case 2: Null Pointer (Invoking UB) ---\n");
    /*
     * Call with a null pointer. This is where the magic happens.
     * The program might crash immediately here, but if it doesn't,
     * the branch elimination will be evident.
     */
    process_pointer_and_check(null_ptr);
    /* Note: If the program crashes immediately, the following line won't execute. */
    /* The point is to observe if the "ERROR" message ever appears. */

    return 0;
}