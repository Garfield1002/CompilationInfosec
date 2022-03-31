#include <stdio.h>

struct s
{
    int x;
    int y;
};

int main()
{
    int t[10];
    t[0] = 5;

    struct s *ptr;

    struct s a = {.x = 2, .y = 3};

    ptr = &a;

    printf("%d", *ptr);

    return 0;
}
