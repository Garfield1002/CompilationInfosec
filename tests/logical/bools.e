int main()
{
    int true = 1;
    int false = 0;

    if (true || false)
    {
        print_char('1');
    }
    if (false || true)
    {
        print_char('2');
    }
    if (false || false)
    {
        print_char('3');
    }
    if (true || true)
    {
        print_char('4');
    }
    if (false && true)
    {
        print_char('5');
    }
    if (true && false)
    {
        print_char('6');
    }
    if (true && true)
    {
        print_char('7');
    }
    if (false && false)
    {
        print_char('8');
    }
    if (!true)
    {
        print_char('9');
    }
    if (!false)
    {
        print_char('0');
    }

    return 0;
}