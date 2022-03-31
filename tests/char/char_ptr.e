void f(char* p, char c){
    *p = c;
}

int main()
{
    char a = 'k';
    char b = 'o';
    char* pa = &a;
    char* pb = &b;
    f(pa, 'O');
    f(pb, 'K');
    print_char(a);
    print_char(b);
    return 0;
}