/*
**  Jonathan Salwan - 2015-01-24
** 
**  http://shell-storm.org
**  http://twitter.com/JonathanSalwan
** 
**  This program is free software: you can redistribute it and/or modify
**  it under the terms of the GNU General Public License as published by
**  the Free Software  Foundation, either  version 3 of  the License, or
**  (at your option) any later version.
*/

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

