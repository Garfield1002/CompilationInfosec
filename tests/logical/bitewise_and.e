
int main()
{
    int b = (3 & 4) == 0;
    if (!b)
    {
        return 1;
    }
    b = 3 & 4 == 0;
    if (b)
    {
        return 1;
    }
    b = (5 & 4) == 4;
    if (!b)
    {
        return 1;
    }
    b = (8 & 7) == 0;
    if (!b)
    {
        return 1;
    }
    b = (16 & 6) == 0;
    if (!b)
    {
        return 1;
    }
    b = (24 & 16) == 16;
    if (!b)
    {
        return 1;
    }
    b = (32 & 16) == 0;
    if (!b)
    {
        return 1;
    }
    b = (17 && 23) == 1;
    if (!b)
    {
        return 1;
    }
    b = (17 || 23) == 1;
    if (!b)
    {
        return 1;
    }
    return 0;
}