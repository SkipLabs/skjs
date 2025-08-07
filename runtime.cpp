#include <cstdio>
#include <cstring>
#include <cerrno>

#ifndef RELEASE
#include <backtrace.h>

extern "C" {

typedef struct {
  bool full_trace;
  bool before_main;
  bool before_throw;
} backtrace_data;

static int print_callback(void* data, uintptr_t /* pc */, const char* filename,
                          int lineno, const char* function) {
  auto ctx = static_cast<backtrace_data*>(data);

//  if (ctx->full_trace || (ctx->before_main && !ctx->before_throw)) {
    fprintf(stderr, "File %s, line %d\n\t%s()\n",
            filename == NULL ? "???" : filename, lineno,
            function == NULL ? "???" : function);
/*  }

  if (function != NULL && 0 == strcmp(function, "SKIP_throw")) {
    ctx->before_throw = false;
  } else if (function != NULL && 0 == strcmp(function, "skip_main")) {
    ctx->before_main = false;
  }
*/

  return 0;
}

static void error_callback(void* /* data */, const char* msg, int errnum) {
  fprintf(stderr, "libbacktrace: %s", msg);
  if (errnum > 0) fprintf(stderr, ": %s", strerror(errnum));
  fputc('\n', stderr);
}

void SKIP_print_backtrace() {
  struct backtrace_state* state =
      backtrace_create_state(nullptr, 0, error_callback, nullptr);
  if (state == nullptr) {
    fprintf(stderr, "libbacktrace: Failed to initialize backtrace\n");
    return;
  }

  backtrace_data data{false, true, true};
  backtrace_full(state, 3, print_callback, error_callback, &data);
}

}  // extern "C"

#else  // RELEASE

extern "C" {
void SKIP_print_backtrace() {
  fprintf(stderr, "Backtrace not available in release mode\n");
}
}  // extern "C"

#endif  // RELEASE
