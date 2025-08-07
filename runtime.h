#ifndef SKJS_RUNTIME_H
#define SKJS_RUNTIME_H

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Prints a stack backtrace to stderr.
 * In release builds, prints a message indicating backtrace is not available.
 */
void SKIP_print_backtrace();

#ifdef __cplusplus
}
#endif

#endif  // SKJS_RUNTIME_H