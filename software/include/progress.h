#ifndef __PROGRSS_H
#define __PROGRSS_H

/* Initialize a progress bar.
 * If max > 0 a one line progress bar is printed where 'max' corresponds to 100%.
 * If max == 0 a multi line progress bar is printed.
 */
void init_progression_bar(int max);

/* Update a progress bar to a new value. If now < 0 then a spinner is printed.
 */
void show_progress(int now);

#endif
