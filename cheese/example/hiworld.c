#include <stdio.h>




int check()
{

	int a = 0;

	for (a=0; a<10; a++)
		printf("for loop %d counting\n", a);
	return 0;
}
int main()
{
	check();
	return 0;

}
