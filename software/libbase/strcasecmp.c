#include <string.h>
#include <ctype.h>

int strcasecmp(const char *cs, const char *ct)
{
    int result;
    for (;;) {
        if ((result = (int)toupper(*cs) - (int)toupper(*ct)) != 0 || !*cs) {
            break;
        }

        cs++;
        ct++;
    }
    return result;
}
