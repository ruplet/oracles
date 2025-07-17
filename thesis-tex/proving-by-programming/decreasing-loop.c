#include <stddef.h>
#include <stdlib.h>
#include <errno.h>
#include <stdio.h>

/**
 * Program: countdown
 * ------------------
 * Parses a non-negative integer from the command-line argument
 * and counts down from that number to zero, printing each step.
 * 
 * Usage:
 *   ./countdown <non-negative base-10 integer>
 *
 * Behavior:
 *   - Valid input: Counts down from the number to zero, both inclusively.
 *   - Invalid input:
 *       * Missing or excessive argument -> shows usage
 *       * Contains non-digit characters -> error
 *       * Negative number (e.g., "-3") -> error
 *       * Out-of-range → prints strerror via perror()
 *
 * Example:
 *   $ ./countdown 3
 *   Steps left: 3
 *   Steps left: 2
 *   Steps left: 1
 *   Steps left: 0
 * 
 * Compilation:
 *   gcc -std=c99 decreasing-loop.c
 */

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <non-negative integer>\n", argv[0]);
        return EXIT_FAILURE;
    }

    const char *input = argv[1];

    if (input[0] == '-') {
        fprintf(stderr, "Error: negative numbers are not allowed: '%s'\n", input);
        return EXIT_FAILURE;
    }

    errno = 0;
    char *endptr = NULL;
    unsigned long counter = strtoul(input, &endptr, 10);

    if (endptr == input || *endptr != '\0') {
        fprintf(stderr, "Error: input '%s' is not a valid number.\n", input);
        return EXIT_FAILURE;
    }

    if (errno != 0) {
        perror("strtoul failed");
        return EXIT_FAILURE;
    }

    for (unsigned long i = counter; i >= 0; --i) {
        printf("Steps left: %lu\n", i);
    }

    return EXIT_SUCCESS;
}
