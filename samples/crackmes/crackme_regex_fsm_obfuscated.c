/*
 * From: http://doar-e.github.io/blog/2013/08/24/regular-expressions-obfuscation-under-the-microscope
 */

#include <stdio.h>
#include <string.h>

unsigned char checkinput(char *p){
unsigned int state = 2414982228;
while(*p)
{
switch(state)
{
case 1150854703:
{
if(*p == '@')
{
state = 2763154882; ++p;
}
else if(*p == '*')
{
state = 614359938; ++p;
}
else if(*p == '=')
{
state = 2460767789; ++p;
}
else if(*p == 't')
{
state = 4029873264; ++p;
}
else if(*p == '2')
{
state = 4283929247; ++p;
}
else if(*p == 'O')
{
state = 3360254177; ++p;
}
else return 0;
break;
}
case 1190742721:
{
if(*p == 'y')
{
state = 953204336; ++p;
}
else return 0;
break;
}
case 324474391:
{
if(*p == 'f')
{
state = 4120389184; ++p;
}
else if(*p == '4')
{
state = 101229758; ++p;
}
else if(*p == 'J')
{
state = 1150854703; ++p;
}
else if(*p == 'L')
{
state = 2384119878; ++p;
}
else if(*p == '>')
{
state = 2349573380; ++p;
}
else if(*p == 'x')
{
state = 1057073555; ++p;
}
else return 0;
break;
}
case 2166033187:
{
if(*p == 'k')
{
state = 3786799564; ++p;
}
else if(*p == 'T')
{
state = 1390160888; ++p;
}
else if(*p == 'm')
{
state = 721752926; ++p;
}
else if(*p == 'S')
{
state = 614359938; ++p;
}
else return 0;
break;
}
case 3268769598:
{
if(*p >= '0' && *p <= '9')
{
return 1;
}
else if(*p == '`')
{
state = 3608599948; ++p;
}
else if(*p == '8')
{
state = 691390384; ++p;
}
else if(*p == 'a')
{
state = 2242283503; ++p;
}
else if(*p == 'M')
{
state = 3335559999; ++p;
}
else return 0;
break;
}
case 2414982228:
{
if(*p == 'H')
{
state = 2696439585; ++p;
}
else if(*p == '>')
{
state = 2349573380; ++p;
}
else if(*p == 'L')
{
state = 3335559999; ++p;
}
else if(*p == 'c')
{
state = 3786799564; ++p;
}
else if(*p == 'm')
{
state = 1057073555; ++p;
}
else ++p;
break;
}
case 3786799564:
{
if(*p == 'S')
{
return 1;
}
else if(*p == ' ')
{
state = 3410901078; ++p;
}
else if(*p == 'B')
{
state = 2056998787; ++p;
}
else if(*p == 'Y')
{
state = 4267076867; ++p;
}
else if(*p == '5')
{
state = 1611919523; ++p;
}
else if(*p == 'i')
{
state = 2241134315; ++p;
}
else return 0;
break;
}
case 2971031841:
{
if(*p == '&')
{
state = 953204336; ++p;
}
else if(*p == '.')
{
state = 1515485535; ++p;
}
else if(*p == 'v')
{
state = 4120389184; ++p;
}
else if(*p == 'R')
{
state = 3608599948; ++p;
}
else if(*p == 'n')
{
state = 4135210710; ++p;
}
else if(*p == '%')
{
state = 3410901078; ++p;
}
else if(*p == 'R')
{
state = 3942154577; ++p;
}
else return 0;
break;
}
case 1057073555:
{
if(*p >= '0' && *p <= '9')
{
state = 3268769598; ++p;
}
else if(*p == 's')
{
state = 324474391; ++p;
}
else if(*p == 'Y')
{
state = 101229758; ++p;
}
else if(*p == '+')
{
state = 101229758; ++p;
}
else return 0;
break;
}
case 2934937715:
{
if(*p == '$')
{
state = 1782541044; ++p;
}
else if(*p == 'i')
{
state = 2242283503; ++p;
}
else return 0;
break;
}
case 2011019626:
{
if(*p == '+')
{
state = 1818848268; ++p;
}
else if(*p == 'o')
{
state = 2696439585; ++p;
}
else if(*p == '~')
{
state = 1239897561; ++p;
}
else if(*p == '4')
{
state = 957033642; ++p;
}
else if(*p == 'o')
{
state = 3335559999; ++p;
}
else return 0;
break;
}
case 3752577241:
{
if(*p == '%')
{
state = 3608599948; ++p;
}
else if(*p == '5')
{
state = 2384119878; ++p;
}
else if(*p == 'E')
{
state = 2241134315; ++p;
}
else if(*p == 'A')
{
state = 4267076867; ++p;
}
else if(*p == 'g')
{
state = 607666879; ++p;
}
else if(*p == 'B')
{
state = 3268769598; ++p;
}
else if(*p == 'U')
{
state = 2056998787; ++p;
}
else if(*p == 'K')
{
state = 776990946; ++p;
}
else if(*p == '\\')
{
state = 155012291; ++p;
}
else return 0;
break;
}
case 101229758:
{
if(*p == '-')
{
state = 1239897561; ++p;
}
else if(*p == 'j')
{
state = 1746586473; ++p;
}
else if(*p == 'P')
{
state = 2696439585; ++p;
}
else if(*p == 'S')
{
state = 607666879; ++p;
}
else if(*p == '=')
{
state = 609520033; ++p;
}
else if(*p == '2')
{
state = 1782541044; ++p;
}
else if(*p == '&')
{
state = 2763154882; ++p;
}
else return 0;
break;
}
case 3181597626:
{
if(*p == 'w')
{
state = 3268769598; ++p;
}
else if(*p == 'u')
{
state = 3786799564; ++p;
}
else if(*p == '/')
{
state = 3268769598; ++p;
}
else if(*p == '%')
{
state = 776990946; ++p;
}
else if(*p == 'g')
{
state = 1384595292; ++p;
}
else if(*p == 'E')
{
state = 2414982228; ++p;
}
else if(*p == 'm')
{
state = 3752577241; ++p;
}
else if(*p == '~')
{
state = 1818848268; ++p;
}
else if(*p == '4')
{
state = 2242283503; ++p;
}
else if(*p == 'D')
{
state = 3268769598; ++p;
}
else if(*p == 'L')
{
state = 2756235254; ++p;
}
else if(*p == 'C')
{
state = 2696439585; ++p;
}
else return 0;
break;
}
case 1097742315:
{
if(*p == '#')
{
state = 2166033187; ++p;
}
else if(*p == 'I')
{
state = 1390160888; ++p;
}
else if(*p == 'U')
{
state = 3891264545; ++p;
}
else return 0;
break;
}
case 2696439585:
{
if(*p == 'i')
{
state = 101229758; ++p;
}
else if(*p == 'Q')
{
state = 3891264545; ++p;
}
else if(*p == 'm')
{
state = 2492710957; ++p;
}
else if(*p == 'P')
{
state = 4135210710; ++p;
}
else if(*p == 'y')
{
state = 1611919523; ++p;
}
else if(*p == 'w')
{
state = 2241134315; ++p;
}
else return 0;
break;
}
case 4283929247:
{
if(*p == '`')
{
state = 1818848268; ++p;
}
else if(*p == 'h')
{
state = 953204336; ++p;
}
else if(*p == '6')
{
state = 689022328; ++p;
}
else if(*p == 'x')
{
state = 1782541044; ++p;
}
else if(*p == 'z')
{
state = 3410901078; ++p;
}
else if(*p == 'y')
{
state = 3891264545; ++p;
}
else if(*p == 'F')
{
state = 3786799564; ++p;
}
else if(*p == '3')
{
state = 2696439585; ++p;
}
else if(*p == '#')
{
state = 3148306748; ++p;
}
else return 0;
break;
}
case 2756235254:
{
if(*p == 'z')
{
state = 4120389184; ++p;
}
else if(*p == 'S')
{
state = 101229758; ++p;
}
else if(*p == '4')
{
state = 3942154577; ++p;
}
else if(*p == 'M')
{
state = 1390160888; ++p;
}
else if(*p == 'g')
{
state = 2166033187; ++p;
}
else if(*p == 'H')
{
state = 3335559999; ++p;
}
else if(*p == ',')
{
state = 2166033187; ++p;
}
else if(*p == 'a')
{
state = 2414982228; ++p;
}
else return 0;
break;
}
case 614359938:
{
if(*p == '3')
{
state = 1746586473; ++p;
}
else if(*p == '4')
{
state = 2384119878; ++p;
}
else if(*p == ':')
{
state = 957033642; ++p;
}
else if(*p == 'l')
{
state = 1746586473; ++p;
}
else if(*p == 'L')
{
state = 721752926; ++p;
}
else return 0;
break;
}
case 155012291:
{
if(*p == 'W')
{
state = 607666879; ++p;
}
else if(*p == '8')
{
state = 324474391; ++p;
}
else if(*p == 'X')
{
state = 2763154882; ++p;
}
else if(*p == '\\')
{
state = 324474391; ++p;
}
else if(*p == '&')
{
state = 1097742315; ++p;
}
else if(*p == 'e')
{
state = 3891264545; ++p;
}
else if(*p == '\t')
{
state = 4135210710; ++p;
}
else return 0;
break;
}
case 1611919523:
{
if(*p == 'K')
{
state = 2384119878; ++p;
}
else if(*p == '.')
{
state = 607666879; ++p;
}
else if(*p == 'g')
{
state = 324474391; ++p;
}
else if(*p == 'H')
{
state = 155012291; ++p;
}
else if(*p == '#')
{
state = 155012291; ++p;
}
else if(*p == '^')
{
state = 957033642; ++p;
}
else if(*p == '?')
{
state = 3891264545; ++p;
}
else return 0;
break;
}
case 689022328:
{
if(*p == '+')
{
state = 3268769598; ++p;
}
else if(*p == 'H')
{
state = 1057073555; ++p;
}
else if(*p == '!')
{
state = 2756235254; ++p;
}
else if(*p == '9')
{
state = 295606295; ++p;
}
else return 0;
break;
}
case 1782541044:
{
if(*p == 'k')
{
state = 607666879; ++p;
}
else if(*p == 'H')
{
state = 2241134315; ++p;
}
else if(*p == '|')
{
state = 1239897561; ++p;
}
else if(*p == 'F')
{
state = 2934937715; ++p;
}
else if(*p == '^')
{
state = 2242283503; ++p;
}
else if(*p == '\x0b')
{
state = 2056998787; ++p;
}
else if(*p == 'x')
{
state = 2696439585; ++p;
}
else return 0;
break;
}
case 3410901078:
{
if(*p >= '0' && *p <= '9')
{
state = 1057073555; ++p;
}
else if(*p == '3')
{
state = 324474391; ++p;
}
else if(*p == 't')
{
state = 3410901078; ++p;
}
else if(*p == '8')
{
state = 721752926; ++p;
}
else if(*p == '#')
{
state = 609520033; ++p;
}
else if(*p == 'J')
{
state = 1150854703; ++p;
}
else return 0;
break;
}
case 1746586473:
{
if(*p == 'f')
{
state = 1097742315; ++p;
}
else if(*p == 'X')
{
state = 4267076867; ++p;
}
else if(*p == '"')
{
state = 4135210710; ++p;
}
else return 0;
break;
}
case 609520033:
{
if(*p == 'O')
{
state = 1611919523; ++p;
}
else if(*p == 'd')
{
state = 3891264545; ++p;
}
else if(*p == 'm')
{
state = 3608599948; ++p;
}
else if(*p == '+')
{
state = 2166033187; ++p;
}
else if(*p == ':')
{
state = 4120389184; ++p;
}
else if(*p == 'd')
{
state = 1818848268; ++p;
}
else return 0;
break;
}
case 2460767789:
{
if(*p == 'h')
{
state = 3942154577; ++p;
}
else if(*p == 'z')
{
state = 3268769598; ++p;
}
else if(*p == 'z')
{
state = 2349573380; ++p;
}
else if(*p == '(')
{
state = 691390384; ++p;
}
else if(*p == '<')
{
state = 953204336; ++p;
}
else if(*p == '1')
{
state = 1818848268; ++p;
}
else return 0;
break;
}
case 2384119878:
{
if(*p == ')')
{
state = 3410901078; ++p;
}
else if(*p == 'X')
{
state = 2414982228; ++p;
}
else if(*p == '*')
{
state = 1782541044; ++p;
}
else if(*p == '-')
{
state = 1746586473; ++p;
}
else if(*p == '0')
{
state = 3786799564; ++p;
}
else return 0;
break;
}
case 776990946:
{
if(*p == 'i')
{
state = 607666879; ++p;
}
else if(*p == 'W')
{
state = 2349573380; ++p;
}
else if(*p == 'f')
{
state = 3148306748; ++p;
}
else if(*p == 'X')
{
state = 3942154577; ++p;
}
else if(*p == 'H')
{
state = 4267076867; ++p;
}
else if(*p == 'a')
{
state = 1331020175; ++p;
}
else if(*p == ',')
{
return 1;
}
else return 0;
break;
}
case 3891264545:
{
if(*p == '`')
{
state = 3891264545; ++p;
}
else if(*p == 'c')
{
return 1;
}
else if(*p == ':')
{
state = 691390384; ++p;
}
else return 0;
break;
}
case 4029873264:
{
if(*p == 'H')
{
state = 2696439585; ++p;
}
else if(*p == 'S')
{
return 1;
}
else if(*p == 'c')
{
state = 3942154577; ++p;
}
else if(*p == '@')
{
state = 1782541044; ++p;
}
else if(*p == 'J')
{
state = 1611919523; ++p;
}
else if(*p == 'W')
{
state = 3786799564; ++p;
}
else return 0;
break;
}
case 2056998787:
{
if(*p == 'T')
{
state = 324474391; ++p;
}
else if(*p == 'W')
{
state = 1150854703; ++p;
}
else if(*p == 'B')
{
state = 1190742721; ++p;
}
else if(*p == '"')
{
state = 2696439585; ++p;
}
else if(*p == '8')
{
state = 1190742721; ++p;
}
else if(*p == 'p')
{
state = 2056998787; ++p;
}
else if(*p == '6')
{
state = 609520033; ++p;
}
else if(*p == 'v')
{
state = 1239897561; ++p;
}
else if(*p == 'd')
{
state = 2756235254; ++p;
}
else return 0;
break;
}
case 2763154882:
{
if(*p == 'O')
{
state = 3268769598; ++p;
}
else if(*p == ')')
{
state = 689022328; ++p;
}
else if(*p == '4')
{
state = 2166033187; ++p;
}
else if(*p == 'Q')
{
state = 1150854703; ++p;
}
else if(*p == 'Y')
{
state = 3786799564; ++p;
}
else if(*p == 't')
{
state = 2934937715; ++p;
}
else return 0;
break;
}
case 691390384:
{
if(*p == '_')
{
state = 1057073555; ++p;
}
else if(*p == 'C')
{
state = 3752577241; ++p;
}
else if(*p == '?')
{
state = 2241134315; ++p;
}
else return 0;
break;
}
case 721752926:
{
if(*p == ';')
{
state = 4120389184; ++p;
}
else if(*p == '\x0b')
{
state = 3752577241; ++p;
}
else if(*p == 'o')
{
state = 1150854703; ++p;
}
else if(*p == ':')
{
state = 4283929247; ++p;
}
else if(*p == 'U')
{
state = 1818848268; ++p;
}
else if(*p == '0')
{
state = 1190742721; ++p;
}
else if(*p == 'Z')
{
state = 2971031841; ++p;
}
else if(*p == '"')
{
state = 2971031841; ++p;
}
else if(*p == 'G')
{
state = 3786799564; ++p;
}
else return 0;
break;
}
case 4120389184:
{
if(*p == 'o')
{
state = 2241134315; ++p;
}
else if(*p == 'i')
{
state = 3335559999; ++p;
}
else if(*p == '\\')
{
state = 3148306748; ++p;
}
else if(*p == 'n')
{
state = 2349573380; ++p;
}
else return 0;
break;
}
case 1114525773:
{
if(*p == '9')
{
state = 2242283503; ++p;
}
else if(*p == '3')
{
state = 1782541044; ++p;
}
else if(*p == 'b')
{
state = 1818848268; ++p;
}
else if(*p == ',')
{
state = 3360254177; ++p;
}
else if(*p == 'v')
{
state = 3523682200; ++p;
}
else if(*p == 'F')
{
state = 2349573380; ++p;
}
else if(*p == ',')
{
state = 3181597626; ++p;
}
else if(*p == '\n')
{
state = 721752926; ++p;
}
else if(*p == '1')
{
state = 2242283503; ++p;
}
else if(*p == 'X')
{
state = 3942154577; ++p;
}
else return 0;
break;
}
case 607666879:
{
if(*p == '2')
{
state = 1818848268; ++p;
}
else if(*p == 'p')
{
state = 2241134315; ++p;
}
else if(*p == 'h')
{
state = 3786799564; ++p;
}
else if(*p == ')')
{
state = 2492710957; ++p;
}
else if(*p == '5')
{
state = 1331020175; ++p;
}
else if(*p == 'h')
{
return 1;
}
else return 0;
break;
}
case 1384595292:
{
if(*p == 'A')
{
state = 957033642; ++p;
}
else if(*p == '|')
{
state = 1384595292; ++p;
}
else if(*p == 'M')
{
state = 1611919523; ++p;
}
else if(*p == '\x0c')
{
state = 2763154882; ++p;
}
else if(*p == ':')
{
state = 2241134315; ++p;
}
else if(*p == 'x')
{
state = 1190742721; ++p;
}
else if(*p == 'E')
{
state = 689022328; ++p;
}
else if(*p == '`')
{
state = 4029873264; ++p;
}
else if(*p == ':')
{
state = 2384119878; ++p;
}
else if(*p == 'r')
{
state = 3268769598; ++p;
}
else if(*p == '9')
{
state = 1746586473; ++p;
}
else return 0;
break;
}
case 3942154577:
{
if(*p == '@')
{
state = 2460767789; ++p;
}
else if(*p == 'h')
{
state = 2763154882; ++p;
}
else if(*p == 'M')
{
state = 2756235254; ++p;
}
else if(*p == 'y')
{
state = 3608599948; ++p;
}
else if(*p == '3')
{
state = 1150854703; ++p;
}
else if(*p == 'P')
{
state = 1390160888; ++p;
}
else return 0;
break;
}
case 3523682200:
{
if(*p == '>')
{
state = 3360254177; ++p;
}
else if(*p == '$')
{
state = 2241134315; ++p;
}
else if(*p == ':')
{
state = 953204336; ++p;
}
else if(*p == '*')
{
state = 2971031841; ++p;
}
else if(*p == '@')
{
state = 324474391; ++p;
}
else if(*p == '[')
{
state = 776990946; ++p;
}
else return 0;
break;
}
case 295606295:
{
if(*p == '_')
{
state = 3523682200; ++p;
}
else if(*p == 's')
{
state = 4283929247; ++p;
}
else return 0;
break;
}
case 1390160888:
{
if(*p == '0')
{
state = 2696439585; ++p;
}
else if(*p == 'T')
{
state = 155012291; ++p;
}
else if(*p == '=')
{
state = 1818848268; ++p;
}
else if(*p == '2')
{
state = 1150854703; ++p;
}
else if(*p == 'n')
{
state = 2056998787; ++p;
}
else if(*p == 'j')
{
state = 1114525773; ++p;
}
else return 0;
break;
}
case 4135210710:
{
if(*p == 'A')
{
state = 721752926; ++p;
}
else if(*p == 'E')
{
state = 2971031841; ++p;
}
else if(*p == 'N')
{
state = 3891264545; ++p;
}
else if(*p == 'N')
{
state = 2971031841; ++p;
}
else if(*p == '@')
{
state = 689022328; ++p;
}
else if(*p == '=')
{
state = 609520033; ++p;
}
else if(*p == 'H')
{
state = 2696439585; ++p;
}
else return 0;
break;
}
case 3360254177:
{
if(*p == 'B')
{
state = 1746586473; ++p;
}
else if(*p == '_')
{
state = 324474391; ++p;
}
else if(*p == '\r')
{
return 1;
}
else return 0;
break;
}
case 953204336:
{
if(*p == 'r')
{
state = 3752577241; ++p;
}
else if(*p == 't')
{
state = 2166033187; ++p;
}
else if(*p == 's')
{
state = 4283929247; ++p;
}
else if(*p == 'z')
{
state = 689022328; ++p;
}
else if(*p == 'r')
{
state = 3148306748; ++p;
}
else if(*p == '5')
{
state = 2011019626; ++p;
}
else return 0;
break;
}
case 957033642:
{
if(*p == '7')
{
state = 614359938; ++p;
}
else if(*p == '\x0b')
{
state = 101229758; ++p;
}
else if(*p == 'w')
{
state = 1331020175; ++p;
}
else if(*p == '%')
{
state = 1150854703; ++p;
}
else if(*p == 'P')
{
state = 101229758; ++p;
}
else if(*p == '9')
{
state = 609520033; ++p;
}
else return 0;
break;
}
case 3148306748:
{
if(*p == 'd')
{
state = 953204336; ++p;
}
else if(*p == 'c')
{
state = 2056998787; ++p;
}
else if(*p == '>')
{
state = 1782541044; ++p;
}
else return 0;
break;
}
case 1239897561:
{
if(*p >= '0' && *p <= '9')
{
state = 3410901078; ++p;
}
else if(*p == '-')
{
state = 101229758; ++p;
}
else if(*p == '-')
{
state = 1331020175; ++p;
}
else if(*p == ' ')
{
state = 957033642; ++p;
}
else if(*p == '2')
{
state = 3942154577; ++p;
}
else if(*p == '8')
{
state = 3148306748; ++p;
}
else if(*p == 'd')
{
state = 609520033; ++p;
}
else return 0;
break;
}
case 2242283503:
{
if(*p == '+')
{
state = 2414982228; ++p;
}
else if(*p == 'e')
{
state = 3268769598; ++p;
}
else if(*p == '#')
{
state = 1818848268; ++p;
}
else if(*p == 'S')
{
state = 2763154882; ++p;
}
else if(*p == '@')
{
state = 1746586473; ++p;
}
else return 0;
break;
}
case 2492710957:
{
if(*p == 'X')
{
state = 3148306748; ++p;
}
else if(*p == 'X')
{
state = 1097742315; ++p;
}
else if(*p == 'O')
{
state = 2011019626; ++p;
}
else return 0;
break;
}
case 3608599948:
{
if(*p == '-')
{
state = 609520033; ++p;
}
else if(*p == 'a')
{
state = 3608599948; ++p;
}
else if(*p == ']')
{
state = 2056998787; ++p;
}
else if(*p == 'I')
{
state = 2384119878; ++p;
}
else return 0;
break;
}
case 3335559999:
{
if(*p == 'V')
{
state = 101229758; ++p;
}
else if(*p == 'e')
{
state = 155012291; ++p;
}
else if(*p == ',')
{
state = 3268769598; ++p;
}
else if(*p == '@')
{
state = 1097742315; ++p;
}
else if(*p == '1')
{
state = 2056998787; ++p;
}
else if(*p == 'P')
{
state = 1384595292; ++p;
}
else if(*p == '-')
{
state = 2934937715; ++p;
}
else if(*p == ')')
{
state = 1190742721; ++p;
}
else if(*p == '?')
{
state = 1239897561; ++p;
}
else return 0;
break;
}
case 1818848268:
{
if(*p == '6')
{
state = 957033642; ++p;
}
else if(*p == 'g')
{
state = 3410901078; ++p;
}
else if(*p == '\x0c')
{
state = 1746586473; ++p;
}
else if(*p == 'f')
{
state = 609520033; ++p;
}
else if(*p == '\n')
{
state = 295606295; ++p;
}
else if(*p == 'r')
{
state = 2384119878; ++p;
}
else return 0;
break;
}
case 2241134315:
{
if(*p == ':')
{
state = 3608599948; ++p;
}
else if(*p == 'S')
{
state = 3148306748; ++p;
}
else if(*p == '[')
{
state = 3335559999; ++p;
}
else if(*p == '\t')
{
state = 953204336; ++p;
}
else if(*p == 'X')
{
state = 3410901078; ++p;
}
else return 0;
break;
}
case 2349573380:
{
if(*p == '0')
{
state = 101229758; ++p;
}
else if(*p == ':')
{
state = 957033642; ++p;
}
else if(*p == 'Z')
{
state = 957033642; ++p;
}
else if(*p == ' ')
{
state = 1239897561; ++p;
}
else if(*p == 'i')
{
state = 1239897561; ++p;
}
else return 0;
break;
}
case 1331020175:
{
if(*p == 'B')
{
state = 2384119878; ++p;
}
else if(*p == '"')
{
state = 2242283503; ++p;
}
else if(*p == '#')
{
state = 3786799564; ++p;
}
else if(*p == '(')
{
state = 1057073555; ++p;
}
else if(*p == 'F')
{
state = 2242283503; ++p;
}
else if(*p == 'n')
{
state = 155012291; ++p;
}
else if(*p == 'j')
{
state = 2460767789; ++p;
}
else if(*p == '^')
{
state = 1611919523; ++p;
}
else if(*p == 'J')
{
state = 1746586473; ++p;
}
else return 0;
break;
}
case 1515485535:
{
if(*p == 'r')
{
state = 1611919523; ++p;
}
else if(*p == '.')
{
state = 1384595292; ++p;
}
else if(*p == 'M')
{
state = 2011019626; ++p;
}
else if(*p == '%')
{
state = 776990946; ++p;
}
else return 0;
break;
}
case 4267076867:
{
if(*p == '\r')
{
state = 2056998787; ++p;
}
else if(*p == ')')
{
state = 1746586473; ++p;
}
else if(*p == 'q')
{
state = 2242283503; ++p;
}
else if(*p == 'p')
{
state = 609520033; ++p;
}
else return 0;
break;
}
}
}
return 0;
}

int main(int argc, char *argv[])
{
    if(argc != 2)
    {
        printf("./fsm <string>\n");
        return 0;
    }

    if(checkinput(argv[1]))
        printf("Good boy.\n");
    else
        printf("Bad boy.\n");

    return 1;
}
