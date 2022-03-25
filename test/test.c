#include <stdio.h>

struct s
{
    struct z;

    int x;
    int y;
};

void f(int *z, int x, int y)
{
    *z = x + y;
}

int main()
{

    char c = 'a' + 1;

    int x = 14;
    int y = 12;
    int z = 3;
    f(&z, x, y);

    printf("%d\n", z);

    return z;
}