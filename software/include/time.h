#ifndef __TIME_H
#define __TIME_H

#ifdef __cplusplus
extern "C" {
#endif

void time_init(void);
int elapsed(int *last_event, int period);

#ifdef __cplusplus
}
#endif

#endif