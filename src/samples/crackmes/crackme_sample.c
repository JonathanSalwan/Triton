
int check(const char *c)
{
  if (c[0] == 'x')
    return 1;
  return 0;
}

int main(int ac, const char **av)
{
  return check(av[1]);
}

