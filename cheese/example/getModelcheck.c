#include <stdio.h>



int main(int argc, char* argv[])
{
//	printf("%c %c [%c] [%x]\n", argv[1][0], argv[1][1], argv[1][0]^argv[1][1], argv[1][0]^argv[1][1]);
	char test = argv[1][0] ^ argv[1][1];

	if( 1 < test && test < 5 )
		printf("done!");
	else
		printf("nope!");
	return 0;
}
