/*
 *
 * These stubs come from the glibc, uClibc, libiberty, berkeleydb, arith64 projects
 * and aim to provide standalone routines helping the dynamic symbolic exploration
 * when doing a pure emulation with Triton.
 *
 */

#include <stddef.h>
#include <limits.h>
#include <stdbool.h>


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

/* A very basic malloc and free implementation */

#define ALLOC_SIZE 0x10000
#define USED 1
#define FREE !USED

struct s_alloc_header
{
  bool flag;      /* used=1 or free=0 */
  unsigned size;  /* alloc size */
};

/* yeah, it will be in .rodata but it's simpler when dumping the stub with IDA */
const char alloc_area[ALLOC_SIZE] = {0x00};

__attribute__((STUB_ABI))
void* malloc(size_t size) {
  void* ptr = 0;
  struct s_alloc_header* header = (struct s_alloc_header*)alloc_area;

  while (true) {
    /* Check if we are out of alloc area */
    if ((void*)header - (void*)alloc_area >= ALLOC_SIZE) {
      break;
    }

    /* If a chunk is used, continue to find a free one */
    if (header->flag == USED) {
      header += header->size;
      continue;
    }

    if (header->flag == FREE) {
      /* If a chunk is free and the size fits, return this chunk */
      if (header->size && size <= header->size) {
        header->flag = USED;
        ptr = (void*)header + sizeof(struct s_alloc_header);
        break;
      }
      /* If the chunk is free but the size does not fits, continue to find a new one */
      else if (header->size && size > header->size) {
        header += header->size;
        continue;
      }
      /* If the chunk is free and never initialized, used this chunk and define a size */
      else if (header->size == 0) {
        ptr = (void*)header + sizeof(struct s_alloc_header);
        if ((ptr - (void*)alloc_area) + size >= ALLOC_SIZE) {
          /* No enough memory */
          return 0;
        }
        header->flag = USED;
        header->size = size;
        break;
      }
      else {
        /* something wrong */
        return 0;
      }
    }
  }
  return ptr;
}

__attribute__((STUB_ABI))
void free(void* ptr) {
  struct s_alloc_header* header = ptr - sizeof(struct s_alloc_header);
  header->flag = FREE;
}

#undef ALLOC_SIZE
#undef FREE
#undef USED

#define arith64_u64 unsigned long long int
#define arith64_s64 signed long long int
#define arith64_u32 unsigned int
#define arith64_s32 int

typedef union {
  arith64_u64 u64;
  arith64_s64 s64;
  struct {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    arith64_u32 hi; arith64_u32 lo;
#else
    arith64_u32 lo; arith64_u32 hi;
#endif
  } u32;
  struct {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    arith64_s32 hi; arith64_s32 lo;
#else
    arith64_s32 lo; arith64_s32 hi;
#endif
  } s32;
} arith64_word;

// extract hi and lo 32-bit words from 64-bit value
#define arith64_hi(n) (arith64_word){.u64=n}.u32.hi
#define arith64_lo(n) (arith64_word){.u64=n}.u32.lo

// Negate a if b is negative, via invert and increment.
#define arith64_neg(a, b) (((a) ^ ((((arith64_s64)(b)) >= 0) - 1)) + (((arith64_s64)(b)) < 0))
#define arith64_abs(a) arith64_neg(a, a)

// Return the absolute value of a.
// Note LLINT_MIN cannot be negated.
__attribute__((STUB_ABI))
arith64_s64 __absvdi2(arith64_s64 a) {
  return arith64_abs(a);
}

// Return the result of shifting a left by b bits.
__attribute__((STUB_ABI))
arith64_s64 __ashldi3(arith64_s64 a, int b) {
  arith64_word w = {.s64 = a};

  b &= 63;

  if (b >= 32) {
    w.u32.hi = w.u32.lo << (b - 32);
    w.u32.lo = 0;
  }
  else if (b) {
    w.u32.hi = (w.u32.lo >> (32 - b)) | (w.u32.hi << b);
    w.u32.lo <<= b;
  }
  return w.s64;
}

// Return the result of arithmetically shifting a right by b bits.
__attribute__((STUB_ABI))
arith64_s64 __ashrdi3(arith64_s64 a, int b) {
  arith64_word w = {.s64 = a};

  b &= 63;

  if (b >= 32) {
    w.s32.lo = w.s32.hi >> (b - 32);
    w.s32.hi >>= 31; // 0xFFFFFFFF or 0
  }
  else if (b) {
    w.u32.lo = (w.u32.hi << (32 - b)) | (w.u32.lo >> b);
    w.s32.hi >>= b;
  }
  return w.s64;
}

// These functions return the number of leading 0-bits in a, starting at the
// most significant bit position. If a is zero, the result is undefined.
__attribute__((STUB_ABI))
int __clzsi2(arith64_u32 a) {
  int b, n = 0;
  b = !(a & 0xffff0000) << 4; n += b; a <<= b;
  b = !(a & 0xff000000) << 3; n += b; a <<= b;
  b = !(a & 0xf0000000) << 2; n += b; a <<= b;
  b = !(a & 0xc0000000) << 1; n += b; a <<= b;
  return n + !(a & 0x80000000);
}

__attribute__((STUB_ABI))
int __clzdi2(arith64_u64 a) {
  int b, n = 0;
  b = !(a & 0xffffffff00000000ULL) << 5; n += b; a <<= b;
  b = !(a & 0xffff000000000000ULL) << 4; n += b; a <<= b;
  b = !(a & 0xff00000000000000ULL) << 3; n += b; a <<= b;
  b = !(a & 0xf000000000000000ULL) << 2; n += b; a <<= b;
  b = !(a & 0xc000000000000000ULL) << 1; n += b; a <<= b;
  return n + !(a & 0x8000000000000000ULL);
}

// These functions return the number of trailing 0-bits in a, starting at the
// least significant bit position. If a is zero, the result is undefined.
__attribute__((STUB_ABI))
int __ctzsi2(arith64_u32 a) {
  int b, n = 0;
  b = !(a & 0x0000ffff) << 4; n += b; a >>= b;
  b = !(a & 0x000000ff) << 3; n += b; a >>= b;
  b = !(a & 0x0000000f) << 2; n += b; a >>= b;
  b = !(a & 0x00000003) << 1; n += b; a >>= b;
  return n + !(a & 0x00000001);
}

__attribute__((STUB_ABI))
int __ctzdi2(arith64_u64 a) {
  int b, n = 0;
  b = !(a & 0x00000000ffffffffULL) << 5; n += b; a >>= b;
  b = !(a & 0x000000000000ffffULL) << 4; n += b; a >>= b;
  b = !(a & 0x00000000000000ffULL) << 3; n += b; a >>= b;
  b = !(a & 0x000000000000000fULL) << 2; n += b; a >>= b;
  b = !(a & 0x0000000000000003ULL) << 1; n += b; a >>= b;
  return n + !(a & 0x0000000000000001ULL);
}

// Calculate both the quotient and remainder of the unsigned division of a and
// b. The return value is the quotient, and the remainder is placed in variable
// pointed to by c (if it's not NULL).
__attribute__((STUB_ABI))
arith64_u64 __divmoddi4(arith64_u64 a, arith64_u64 b, arith64_u64 *c) {
  if (b > a) {                                // divisor > numerator?
    if (c) *c = a;                            // remainder = numerator
    return 0;                                 // quotient = 0
  }
  if (!arith64_hi(b)) {                       // divisor is 32-bit
    if (b == 0) {                             // divide by 0
      volatile char x = 0; x = 1 / x;         // force an exception
    }
    if (b == 1) {                             // divide by 1
      if (c) *c = 0;                          // remainder = 0
      return a;                               // quotient = numerator
    }
    if (!arith64_hi(a)) {                     // numerator is also 32-bit
      if (c)                                  // use generic 32-bit operators
        *c = arith64_lo(a) % arith64_lo(b);
      return arith64_lo(a) / arith64_lo(b);
    }
  }

  // let's do long division
  char bits = __clzdi2(b) - __clzdi2(a) + 1;    // number of bits to iterate (a and b are non-zero)
  arith64_u64 rem = a >> bits;                  // init remainder
  a <<= 64 - bits;                              // shift numerator to the high bit
  arith64_u64 wrap = 0;                         // start with wrap = 0
  while (bits-- > 0) {                          // for each bit
    rem = (rem << 1) | (a >> 63);               // shift numerator MSB to remainder LSB
    a = (a << 1) | (wrap & 1);                  // shift out the numerator, shift in wrap
    wrap = ((arith64_s64)(b - rem - 1) >> 63);  // wrap = (b > rem) ? 0 : 0xffffffffffffffff (via sign extension)
    rem -= b & wrap;                            // if (wrap) rem -= b
  }
  if (c) *c = rem;                              // maybe set remainder
  return (a << 1) | (wrap & 1);                 // return the quotient
}

// Return the quotient of the signed division of a and b.
__attribute__((STUB_ABI))
arith64_s64 __divdi3(arith64_s64 a, arith64_s64 b) {
  arith64_u64 q = __divmoddi4(arith64_abs(a), arith64_abs(b), (void *)0);
  return arith64_neg(q, a^b); // negate q if a and b signs are different
}

// Return the index of the least significant 1-bit in a, or the value zero if a
// is zero. The least significant bit is index one.
__attribute__((STUB_ABI))
int __ffsdi2(arith64_u64 a) {
  return a ? __ctzdi2(a) + 1 : 0;
}

// Return the result of logically shifting a right by b bits.
__attribute__((STUB_ABI))
arith64_u64 __lshrdi3(arith64_u64 a, int b) {
  arith64_word w = {.u64 = a};

  b &= 63;

  if (b >= 32) {
    w.u32.lo = w.u32.hi >> (b - 32);
    w.u32.hi = 0;
  }
  else if (b) {
    w.u32.lo = (w.u32.hi << (32 - b)) | (w.u32.lo >> b);
    w.u32.hi >>= b;
  }
  return w.u64;
}

// Return the remainder of the signed division of a and b.
__attribute__((STUB_ABI))
arith64_s64 __moddi3(arith64_s64 a, arith64_s64 b) {
  arith64_u64 r;
  __divmoddi4(arith64_abs(a), arith64_abs(b), &r);
  return arith64_neg(r, a); // negate remainder if numerator is negative
}

// Return the number of bits set in a.
__attribute__((STUB_ABI))
int __popcountsi2(arith64_u32 a)
{
    // collect sums into two low bytes
    a = a - ((a >> 1) & 0x55555555);
    a = ((a >> 2) & 0x33333333) + (a & 0x33333333);
    a = (a + (a >> 4)) & 0x0F0F0F0F;
    a = (a + (a >> 16));
    // add the bytes, return bottom 6 bits
    return (a + (a >> 8)) & 63;
}

// Return the number of bits set in a.
__attribute__((STUB_ABI))
int __popcountdi2(arith64_u64 a) {
  // collect sums into two low bytes
  a = a - ((a >> 1) & 0x5555555555555555ULL);
  a = ((a >> 2) & 0x3333333333333333ULL) + (a & 0x3333333333333333ULL);
  a = (a + (a >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
  a = (a + (a >> 32));
  a = (a + (a >> 16));
  // add the bytes, return bottom 7 bits
  return (a + (a >> 8)) & 127;
}

// Return the quotient of the unsigned division of a and b.
__attribute__((STUB_ABI))
arith64_u64 __udivdi3(arith64_u64 a, arith64_u64 b) {
  return __divmoddi4(a, b, (void *)0);
}

// Return the remainder of the unsigned division of a and b.
__attribute__((STUB_ABI))
arith64_u64 __umoddi3(arith64_u64 a, arith64_u64 b) {
  arith64_u64 r;
  __divmoddi4(a, b, &r);
  return r;
}

#undef arith64_u64
#undef arith64_s64
#undef arith64_u32
#undef arith64_s32
#undef arith64_hi
#undef arith64_lo
#undef arith64_neg
#undef arith64_abs
