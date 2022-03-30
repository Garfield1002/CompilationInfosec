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

    int a = C.B.a;

    return 0;
}