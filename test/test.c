#include <stdio.h>

struct b
{
    int a;
};

struct c
{
    struct b B;
};

int main()
{
    struct c C;

    int a = 2;

    C.b = 5;

    C.B.a = 1;

    return 0;
}
