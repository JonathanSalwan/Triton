/*
 *
 * These stubs come from the glibc, uClibc, libiberty, berkeleydb  projects and aim
 * to provide standalone routines helping the dynamic symbolic exploration when
 * doing a pure emulation with Triton.
 *
 */

#include <stddef.h>
#include <limits.h>


__attribute__((STUB_ABI))
void* memccpy(void* s1, const void* s2, int c, size_t n) {
  register char *r1 = s1;
  register const char *r2 = s2;

  while (n-- && (((unsigned char)(*r1++ = *r2++)) != ((unsigned char) c)));

  return (n == (size_t) -1) ? NULL : r1;
}


__attribute__((STUB_ABI))
void* memchr(const void* s, int c, size_t n) {
  const unsigned char* r = (const unsigned char*)s;

  while (n) {
    if (*r == ((unsigned char)c)) {
    	return (void*)r;
    }
    ++r;
    --n;
  }

  return NULL;
}


__attribute__((STUB_ABI))
int memcmp(const void* s1, const void* s2, size_t n) {
  register const unsigned char* r1 = (const unsigned char*)s1;
  register const unsigned char* r2 = (const unsigned char*)s2;

  int r = 0;
  while (n-- && ((r = ((int)(*r1++)) - *r2++) == 0));

  return r;
}


__attribute__((STUB_ABI))
void* memcpy(void* s1, const void* s2, size_t n) {
  register unsigned char* r1 = s1;
  register const unsigned char* r2 = s2;

  while (n) {
    *r1++ = *r2++;
    --n;
  }

  return s1;
}


__attribute__((STUB_ABI))
void* memmem(const void* haystack, size_t haystacklen, const void* needle, size_t needlelen) {
  register const char* ph;
  register const char* pn;
  const char* plast;
  size_t n;

  if (needlelen == 0) {
    return (void*)haystack;
  }

  if (haystacklen >= needlelen) {
    ph = (const char*)haystack;
    pn = (const char*)needle;
    plast = ph + (haystacklen - needlelen);

    do {
      n = 0;
      while (ph[n] == pn[n]) {
        if (++n == needlelen) {
          return (void*) ph;
        }
      }
    } while (++ph <= plast);
  }

  return NULL;
}


__attribute__((STUB_ABI))
void* memmove(void* s1, const void* s2, size_t n) {
  register char* s = (char*)s1;
  register const char* p = (const char*)s2;

  if (p >= s) {
    while (n) {
      *s++ = *p++;
      --n;
    }
  } else {
    while (n) {
      --n;
      s[n] = p[n];
    }
  }

  return s1;
}


__attribute__((STUB_ABI))
void* mempcpy(void* s1, const void* s2, size_t n) {
  register char* r1 = s1;
  register const char* r2 = s2;

  while (n) {
    *r1++ = *r2++;
    --n;
  }

  return r1;
}


__attribute__((STUB_ABI))
void* memrchr(const void* s, int c, size_t n) {
  register const unsigned char* r;

  r = ((unsigned char*)s) + ((size_t)n);

  while (n) {
    if (*--r == ((unsigned char)c)) {
      return (void*)r;
    }
    --n;
  }

  return NULL;
}


__attribute__((STUB_ABI))
void* memset(void* s, int c, size_t n) {
  register unsigned char* p = (unsigned char*)s;

  while (n) {
    *p++ = (unsigned char)c;
    --n;
  }

  return s;
}


__attribute__((STUB_ABI))
void bcopy(const void* s2, void* s1, size_t n) {
  memmove(s1, s2, n);
}


__attribute__((STUB_ABI))
void bzero(void* s, size_t n) {
  (void)memset(s, 0, n);
}


__attribute__((STUB_ABI))
void* rawmemchr(const void* s, int c) {
  register const unsigned char* r = s;
  while (*r != ((unsigned char)c)) ++r;
  return (void*)r;
}


__attribute__((STUB_ABI))
char* stpcpy(register char* s1, const char* s2) {
  while ((*s1++ = *s2++) != 0);
  return s1 - 1;
}


__attribute__((STUB_ABI))
char* stpncpy(register char* s1, register const char* s2, size_t n) {
  char* s = s1;
  const char* p = s2;

  while (n) {
    if ((*s = *s2) != 0) s2++; /* Need to fill tail with 0s. */
    ++s;
    --n;
  }

  return s1 + (s2 - p);
}


__attribute__((STUB_ABI))
int tolower(int c) {
  int ch = c;
  if ((unsigned int)(ch - 'A') < 26u)
    ch -= 'A' - 'a';
  return ch;
}


__attribute__((STUB_ABI))
int toupper(int c) {
  int ch = c;
  if ((unsigned int)(ch - 'a') < 26u)
    ch += 'A' - 'a';
  return ch;
}


__attribute__((STUB_ABI))
int strcasecmp(register const char* s1, register const char* s2) {
  while ((*s1 == *s2) || (tolower(*s1) == tolower(*s2))) {
    if (!*s1++) {
      return 0;
    }
    ++s2;
  }
  return (((unsigned char)tolower(*s1)) < ((unsigned char)tolower(*s2))) ? -1 : 1;
}


__attribute__((STUB_ABI))
char* strcasestr(const char* s1, const char* s2) {
  register const char* s = s1;
  register const char* p = s2;

  do {
    if (!*p) {
      return (char *) s1;;
    }
    if ((*p == *s) || (tolower(*((unsigned char *)p)) == tolower(*((unsigned char *)s)))) {
      ++p;
      ++s;
    } else {
      p = s2;
      if (!*s) {
        return NULL;
      }
      s = ++s1;
    }
  } while (1);
}


__attribute__((STUB_ABI))
char* strcat(char* s1, register const char* s2)
{
  register char* s = s1;

  while (*s++);
  --s;
  while ((*s++ = *s2++) != 0);

  return s1;
}


__attribute__((STUB_ABI))
char* strchr(register const char* s, int c) {
  do {
    if (*s == ((char)c)) {
      return (char*)s;
    }
  } while (*s++);

  return NULL;
}


__attribute__((STUB_ABI))
char* strchrnul(register const char* s, int c) {
  --s;
  while (*++s && (*s != ((char)c)));
  return (char*)s;
}


__attribute__((STUB_ABI))
int strcmp(register const char* s1, register const char* s2) {
  int r;
  while (((r = ((int)(*((unsigned char*)s1))) - *((unsigned char*)s2++)) == 0) && *s1++);
  return r;
}


__attribute__((STUB_ABI))
char* strcpy(char* s1, const char* s2) {
  register char* s = s1;
  while ((*s++ = *s2++) != 0);
  return s1;
}


__attribute__((STUB_ABI))
size_t strcspn(const char* s1, const char* s2) {
  register const char* s;
  register const char* p;

  for (s=s1 ; *s ; s++) {
    for (p=s2 ; *p ; p++) {
      if (*p == *s) goto done;
    }
  }

  done:
  return s - s1;
}


__attribute__((STUB_ABI))
size_t strlen(const char* s) {
  register const char* p;
  for (p=s ; *p ; p++);
  return p - s;
}


__attribute__((STUB_ABI))
size_t strlcat(register char* dst, register const char* src, size_t n) {
  size_t len;
  char dummy[1];

  len = 0;

  while (1) {
    if (len >= n) {
      dst = dummy;
      break;
    }
    if (!*dst) {
      break;
    }
    ++dst;
    ++len;
  }

  while ((*dst = *src) != 0) {
    if (++len < n) {
      ++dst;
    }
    ++src;
  }

  return len;
}


__attribute__((STUB_ABI))
size_t strlcpy(register char* dst, register const char* src, size_t n) {
  const char* src0 = src;
  char dummy[1];

  if (!n) {
    dst = dummy;
  } else {
    --n;
  }

  while ((*dst = *src) != 0) {
    if (n) {
      --n;
      ++dst;
    }
    ++src;
  }

  return src - src0;
}


__attribute__((STUB_ABI))
int strncasecmp(register const char* s1, register const char* s2, size_t n) {
  int r = 0;
  while (n && ((s1 == s2) || !(r = ((int)(tolower(*((unsigned char*)s1)))) - tolower(*((unsigned char*)s2)))) && (--n, ++s2, *s1++));
  return r;
}


__attribute__((STUB_ABI))
char* strncat(char* s1, register const char* s2, size_t n) {
  register char *s = s1;

  while (*s++);
  --s;
  while (n && ((*s = *s2++) != 0)) {
    --n;
    ++s;
  }
  *s = 0;

  return s1;
}


__attribute__((STUB_ABI))
int strncmp(register const char* s1, register const char* s2, size_t n) {
  int r = 0;
  while (n-- && ((r = ((int)(*((unsigned char *)s1))) - *((unsigned char *)s2++)) == 0) && *s1++);
  return r;
}


__attribute__((STUB_ABI))
char* strncpy(char* s1, register const char* s2, size_t n) {
  register char* s = s1;

  while (n) {
    if ((*s = *s2) != 0) s2++; /* Need to fill tail with 0s. */
    ++s;
    --n;
  }

  return s1;
}


__attribute__((STUB_ABI))
size_t strnlen(const char* s, size_t max) {
  register const char* p = s;

  while (max && *p) {
    ++p;
    --max;
  }

  return p - s;
}


__attribute__((STUB_ABI))
char* strpbrk(const char* s1, const char* s2) {
  register const char* s;
  register const char* p;

  for (s=s1 ; *s ; s++) {
    for (p=s2 ; *p ; p++) {
      if (*p == *s) {
        return (char*)s;
      }
    }
  }
  return NULL;
}


__attribute__((STUB_ABI))
char* strrchr(register const  char* s, int c) {
  register const char* p;

  p = NULL;
  do {
    if (*s == (char)c) {
      p = s;
    }
  } while (*s++);

  return (char*)p;
}


__attribute__((STUB_ABI))
char* strsep(char** s1, const char* s2) {
  register char* s = *s1;
  register char* p;

  p = NULL;
  if (s && *s && (p = strpbrk(s, s2))) {
    *p++ = 0;
  }

  *s1 = p;
  return s;
}


__attribute__((STUB_ABI))
size_t strspn(const char* s1, const char* s2) {
  register const char* s = s1;
  register const char* p = s2;

  while (*p) {
    if (*p++ == *s) {
      ++s;
      p = s2;
    }
  }

  return s - s1;
}


__attribute__((STUB_ABI))
char* strstr(const char* s1, const char* s2) {
  register const char* s = s1;
  register const char* p = s2;

  do {
    if (!*p) {
      return (char*) s1;;
    }
    if (*p == *s) {
      ++p;
      ++s;
    } else {
      p = s2;
      if (!*s) {
        return NULL;
      }
      s = ++s1;
    }
  } while (1);
}


__attribute__((STUB_ABI))
char* strtok_r(char* s1, const char* s2, char** next_start) {
  register char* s;
  register char* p;

  if (((s = s1) != NULL) || ((s = *next_start) != NULL)) {
    if (*(s += strspn(s, s2))) {
      if ((p = strpbrk(s, s2)) != NULL) {
        *p++ = 0;
      }
    } else {
      p = s = NULL;
    }
    *next_start = p;
  }
  return s;
}


__attribute__((STUB_ABI))
char* strtok(char* s1, const char* s2) {
  static char* next_start = NULL; /* Initialized to 0 since in bss. */
  return strtok_r(s1, s2, &next_start);
}


__attribute__((STUB_ABI))
void none(void) {
  return;
}


__attribute__((STUB_ABI))
char* basename(const char* path) {
  const char* s;
  const char* p;

  p = s = path;

  while (*s) {
    if (*s++ == '/') {
      p = s;
    }
  }
  return (char *)p;
}


__attribute__((STUB_ABI))
char* dirname(char* path) {
  static const char null_or_empty_or_noslash[] = ".";
  char* s;
  char* last;
  char* first;

  last = s = path;

  if (s != NULL) {
  LOOP:
    while (*s && (*s != '/')) ++s;
    first = s;
    while (*s == '/') ++s;
    if (*s) {
      last = first;
      goto LOOP;
    }
    if (last == path) {
      if (*last != '/') {
        goto DOT;
      }
      if ((*++last == '/') && (last[1] == 0)) {
        ++last;
      }
    }
    *last = 0;
    return path;
  }
  DOT:
    return (char *)null_or_empty_or_noslash;
}


__attribute__((STUB_ABI))
int isdigit(char c) {
  return c >= '0' && c <= '9';
}


__attribute__((STUB_ABI))
int isalpha(int c) {
  return ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'));
}


__attribute__((STUB_ABI))
int isupper(int c) {
  return (c >= 'A' && c <= 'Z');
}


__attribute__((STUB_ABI))
int islower(int c) {
  return (c >= 'a' && c <= 'z');
}


__attribute__((STUB_ABI))
int isalnum(int c) {
  return (isalpha || isdigit);
}


__attribute__((STUB_ABI))
int isspace(int c) {
  return (c == '\t' || c == '\n' || c == '\v' || c == '\f' || c == '\r' || c == ' ');
}


__attribute__((STUB_ABI))
long strtol(const char* nptr, char** endptr, register int base) {
  register const char* s = nptr;
  register unsigned long acc;
  register int c;
  register unsigned long cutoff;
  register int neg = 0, any, cutlim;

  /*
   * Skip white space and pick up leading +/- sign if any.
   * If base is 0, allow 0x for hex and 0 for octal, else
   * assume decimal; if base is already 16, allow 0x.
   */
  do {
    c = *s++;
  } while (isspace(c));

  if (c == '-') {
    neg = 1;
    c = *s++;
  }
  else if (c == '+') {
    c = *s++;
  }

  if ((base == 0 || base == 16) && c == '0' && (*s == 'x' || *s == 'X')) {
    c = s[1];
    s += 2;
    base = 16;
  }

  if (base == 0) {
    base = c == '0' ? 8 : 10;
  }

  /*
   * Compute the cutoff value between legal numbers and illegal
   * numbers.  That is the largest legal value, divided by the
   * base.  An input number that is greater than this value, if
   * followed by a legal input character, is too big.  One that
   * is equal to this value may be valid or not; the limit
   * between valid and invalid numbers is then based on the last
   * digit.  For instance, if the range for longs is
   * [-2147483648..2147483647] and the input base is 10,
   * cutoff will be set to 214748364 and cutlim to either
   * 7 (neg==0) or 8 (neg==1), meaning that if we have accumulated
   * a value > 214748364, or equal but the next digit is > 7 (or 8),
   * the number is too big, and we will return a range error.
   *
   * Set any if any `digits' consumed; make it negative to indicate
   * overflow.
   */
  cutoff = neg ? -(unsigned long)LONG_MIN : LONG_MAX;
  cutlim = cutoff % (unsigned long)base;
  cutoff /= (unsigned long)base;
  for (acc = 0, any = 0;; c = *s++) {
    if (isdigit(c))
      c -= '0';
    else if (isalpha(c))
      c -= isupper(c) ? 'A' - 10 : 'a' - 10;
    else
      break;
    if (c >= base)
      break;
    if (any < 0 || acc > cutoff || (acc == cutoff && c > cutlim))
      any = -1;
    else {
      any = 1;
      acc *= base;
      acc += c;
    }
  }

  if (any < 0) {
    acc = neg ? LONG_MIN : LONG_MAX;
  }
  else if (neg) {
    acc = -acc;
  }

  if (endptr != 0)
    *endptr = (char *) (any ? s - 1 : nptr);

  return (acc);
}

__attribute__((STUB_ABI))
long long strtoll(const char* nptr, char** endptr, register int base) {
  register const char* s = nptr;
  register unsigned long long acc;
  register int c;
  register unsigned long long cutoff;
  register int neg = 0, any, cutlim;

  /*
   * Skip white space and pick up leading +/- sign if any.
   * If base is 0, allow 0x for hex and 0 for octal, else
   * assume decimal; if base is already 16, allow 0x.
   */
  do {
    c = *s++;
  } while (isspace(c));

  if (c == '-') {
    neg = 1;
    c = *s++;
  }
  else if (c == '+') {
    c = *s++;
  }

  if ((base == 0 || base == 16) && c == '0' && (*s == 'x' || *s == 'X')) {
    c = s[1];
    s += 2;
    base = 16;
  }

  if (base == 0) {
    base = c == '0' ? 8 : 10;
  }

  /*
   * Compute the cutoff value between legal numbers and illegal
   * numbers.  That is the largest legal value, divided by the
   * base.  An input number that is greater than this value, if
   * followed by a legal input character, is too big.  One that
   * is equal to this value may be valid or not; the limit
   * between valid and invalid numbers is then based on the last
   * digit.  For instance, if the range for longs is
   * [-2147483648..2147483647] and the input base is 10,
   * cutoff will be set to 214748364 and cutlim to either
   * 7 (neg==0) or 8 (neg==1), meaning that if we have accumulated
   * a value > 214748364, or equal but the next digit is > 7 (or 8),
   * the number is too big, and we will return a range error.
   *
   * Set any if any `digits' consumed; make it negative to indicate
   * overflow.
   */
  cutoff = neg ? -(unsigned long long)LLONG_MIN : LLONG_MAX;
  cutlim = cutoff % (unsigned long long)base;
  cutoff /= (unsigned long long)base;
  for (acc = 0, any = 0;; c = *s++) {
    if (isdigit(c))
      c -= '0';
    else if (isalpha(c))
      c -= isupper(c) ? 'A' - 10 : 'a' - 10;
    else
      break;
    if (c >= base)
      break;
    if (any < 0 || acc > cutoff || (acc == cutoff && c > cutlim))
      any = -1;
    else {
      any = 1;
      acc *= base;
      acc += c;
    }
  }

  if (any < 0) {
    acc = neg ? LLONG_MIN : LLONG_MAX;
  }
  else if (neg) {
    acc = -acc;
  }

  if (endptr != 0) {
    *endptr = (char *) (any ? s - 1 : nptr);
  }

  return (acc);
}


__attribute__((STUB_ABI))
unsigned long strtoul(const char* nptr, char** endptr, register int base) {
  register const char* s = nptr;
  register unsigned long acc;
  register int c;
  register unsigned long cutoff;
  register int neg = 0, any, cutlim;

  /*
   * See strtol for comments as to the logic used.
   */
  do {
    c = *s++;
  } while (isspace(c));

  if (c == '-') {
    neg = 1;
    c = *s++;
  }
  else if (c == '+') {
    c = *s++;
  }

  if ((base == 0 || base == 16) && c == '0' && (*s == 'x' || *s == 'X')) {
    c = s[1];
    s += 2;
    base = 16;
  }

  if (base == 0) {
    base = c == '0' ? 8 : 10;
  }

  cutoff = (unsigned long)ULONG_MAX / (unsigned long)base;
  cutlim = (unsigned long)ULONG_MAX % (unsigned long)base;
  for (acc = 0, any = 0;; c = *s++) {
    if (isdigit(c))
      c -= '0';
    else if (isalpha(c))
      c -= isupper(c) ? 'A' - 10 : 'a' - 10;
    else
      break;
    if (c >= base)
      break;
    if (any < 0 || acc > cutoff || (acc == cutoff && c > cutlim))
      any = -1;
    else {
      any = 1;
      acc *= base;
      acc += c;
    }
  }

  if (any < 0) {
    acc = ULONG_MAX;
  }
  else if (neg) {
    acc = -acc;
  }

  if (endptr != 0) {
    *endptr = (char *) (any ? s - 1 : nptr);
  }

  return (acc);
}


__attribute__((STUB_ABI))
unsigned long long strtoull(const char* nptr, char** endptr, register int base) {
  register const char* s = nptr;
  register unsigned long long acc;
  register int c;
  register unsigned long long cutoff;
  register int neg = 0, any, cutlim;

  /*
   * See strtol for comments as to the logic used.
   */
  do {
    c = *s++;
  } while (isspace(c));

  if (c == '-') {
    neg = 1;
    c = *s++;
  }
  else if (c == '+') {
    c = *s++;
  }

  if ((base == 0 || base == 16) && c == '0' && (*s == 'x' || *s == 'X')) {
    c = s[1];
    s += 2;
    base = 16;
  }

  if (base == 0) {
    base = c == '0' ? 8 : 10;
  }

  cutoff = (unsigned long long)ULLONG_MAX / (unsigned long long)base;
  cutlim = (unsigned long long)ULLONG_MAX % (unsigned long long)base;
  for (acc = 0, any = 0;; c = *s++) {
    if (isdigit(c))
      c -= '0';
    else if (isalpha(c))
      c -= isupper(c) ? 'A' - 10 : 'a' - 10;
    else
      break;
    if (c >= base)
      break;
    if (any < 0 || acc > cutoff || (acc == cutoff && c > cutlim))
      any = -1;
    else {
      any = 1;
      acc *= base;
      acc += c;
    }
  }

  if (any < 0) {
    acc = ULLONG_MAX;
  }
  else if (neg) {
    acc = -acc;
  }

  if (endptr != 0) {
    *endptr = (char *) (any ? s - 1 : nptr);
  }

  return (acc);
}


__attribute__((STUB_ABI))
int atoi(const char* nptr) {
  return (int)strtol(nptr, (char**)NULL, 10);
}


__attribute__((STUB_ABI))
long atol(const char* nptr) {
  return strtol(nptr, (char**)NULL, 10);
}


__attribute__((STUB_ABI))
long long atoll(const char* nptr) {
  return strtoll(nptr, (char**)NULL, 10);
}


__attribute__((STUB_ABI))
int ffs(register int valu) {
  register int bit;

  if (valu == 0)
    return 0;

  for (bit = 1; !(valu & 1); bit++)
    valu >>= 1;

  return bit;
}


__attribute__((STUB_ABI))
int abs(int i) {
  return i < 0 ? -i : i;
}


__attribute__((STUB_ABI))
long int labs (long int i) {
  return i < 0 ? -i : i;
}


__attribute__((STUB_ABI))
long long int llabs (long long int i) {
  return i < 0 ? -i : i;
}


/* Conversion table.  */
static const char conv_table[64] = {
  '.', '/', '0', '1', '2', '3', '4', '5',
  '6', '7', '8', '9', 'A', 'B', 'C', 'D',
  'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L',
  'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T',
  'U', 'V', 'W', 'X', 'Y', 'Z', 'a', 'b',
  'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j',
  'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r',
  's', 't', 'u', 'v', 'w', 'x', 'y', 'z'
};


__attribute__((STUB_ABI))
char* l64a(long int n) {
  unsigned long int m = (unsigned long int) n;
  static char result[7];
  int cnt;

  /* The standard says that only 32 bits are used.  */
  m &= 0xffffffff;

  if (m == 0ul)
    /* The value for N == 0 is defined to be the empty string. */
    return (char *) "";

  for (cnt = 0; m > 0ul; ++cnt) {
    result[cnt] = conv_table[m & 0x3f];
    m >>= 6;
  }
  result[cnt] = '\0';

  return result;
}


#define TABLE_BASE 0x2e
#define TABLE_SIZE 0x4d

#define XX ((char)0x40)

static const char a64l_table[TABLE_SIZE] = {
  /* 0x2e */                                                           0,  1,
  /* 0x30 */   2,  3,  4,  5,  6,  7,  8,  9, 10, 11, XX, XX, XX, XX, XX, XX,
  /* 0x40 */  XX, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  /* 0x50 */  27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, XX, XX, XX, XX, XX,
  /* 0x60 */  XX, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52,
  /* 0x70 */  53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63
};


__attribute__((STUB_ABI))
long int a64l(const char* string) {
  const char* ptr = string;
  unsigned long int result = 0ul;
  const char* end = ptr + 6;
  int shift = 0;

  do {
    unsigned index;
    unsigned value;

    index = *ptr - TABLE_BASE;
    if ((unsigned int) index >= TABLE_SIZE)
      break;
    value = (int) a64l_table[index];
    if (value == (int) XX)
      break;
    ++ptr;
    result |= value << shift;
    shift += 6;
  }
  while (ptr != end);

  return (long int) result;
}

#undef TABLE_BASE
#undef TABLE_SIZE
#undef XX
