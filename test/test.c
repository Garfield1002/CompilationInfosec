#include <stdio.h>

struct s
{
    int x;
    int y;
};

void setX(struct s *p, int x)
{
    p->x = x;
}

int main()
{
    struct s a;
    a.x = 1;
    a.y = 2;

    setX(&a, 2);

    return a.x + a.y;
}
