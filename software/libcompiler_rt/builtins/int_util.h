#ifndef INT_UTIL_H
#define INT_UTIL_H

#define compilerrt_abort() compilerrt_abort_impl(__FILE__, __LINE__, __func__)

NORETURN void compilerrt_abort_impl(const char *file, int line, const char *function);

#define COMPILE_TIME_ASSERT(expr) COMPILE_TIME_ASSERT1(expr, __COUNTER__)
#define COMPILE_TIME_ASSERT1(expr, cnt) COMPILE_TIME_ASSERT2(expr, cnt)
#define COMPILE_TIME_ASSERT2(expr, cnt) typedef char ct_assert_##cnt[(expr) ? 1 : -1] UNUSED

#endif
