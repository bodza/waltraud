#include <console.h>
#include <stdio.h>
#include <stdint.h>

#include <div64.h>
#include <progress.h>

#define FILESIZE_MAX    100000000
#define HASHES_PER_LINE    40

static int printed;
static int progress_max;
static int spin;

void show_progress(int now)
{
    char spinchr[] = "\\|/-";

    if (now < 0) {
        printf("%c\b", spinchr[spin++ % (sizeof(spinchr) - 1)]);
        return;
    }

    if (progress_max && progress_max != FILESIZE_MAX) {
        uint64_t tmp = (int64_t)now * HASHES_PER_LINE;
        do_div(tmp, progress_max);
        now = tmp;
    }

    while (printed < now) {
        if (!(printed % HASHES_PER_LINE) && printed)
            printf("\n");
        printf("#");
        printed++;
    }
}

void init_progression_bar(int max)
{
    printed = 0;
    progress_max = max;
    spin = 0;
    if (progress_max && progress_max != FILESIZE_MAX)
        printf("[%*s]\r[", HASHES_PER_LINE, "");
    else
        printf("");
}
