/*
 *
 * These stubs come from the uClibc project and aim to provide standalone
 * routines helping the dynamic symbolic exploration when doing a pure
 * emulation with Triton.
 *
 * $ gcc -shared -fPIC -o triton-stubs.so triton-stubs.c
 *
 */

#include <stddef.h>
#include <stdlib.h>


void* memccpy(void* s1, const void* s2, int c, size_t n) {
  register char *r1 = s1;
  register const char *r2 = s2;

  while (n-- && (((unsigned char)(*r1++ = *r2++)) != ((unsigned char) c)));

  return (n == (size_t) -1) ? NULL : r1;
}


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


int memcmp(const void* s1, const void* s2, size_t n) {
  register const unsigned char* r1 = (const unsigned char*)s1;
  register const unsigned char* r2 = (const unsigned char*)s2;

  int r = 0;
  while (n-- && ((r = ((int)(*r1++)) - *r2++) == 0));

  return r;
}


void* memcpy(void* s1, const void* s2, size_t n) {
  register unsigned char* r1 = s1;
  register const unsigned char* r2 = s2;

  while (n) {
    *r1++ = *r2++;
    --n;
  }

  return s1;
}


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


void* mempcpy(void* s1, const void* s2, size_t n) {
  register char* r1 = s1;
  register const char* r2 = s2;

  while (n) {
    *r1++ = *r2++;
    --n;
  }

  return r1;
}


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


void* memset(void* s, int c, size_t n) {
  register unsigned char* p = (unsigned char*)s;

  while (n) {
    *p++ = (unsigned char)c;
    --n;
  }

  return s;
}


void bcopy(const void* s2, void* s1, size_t n) {
  memmove(s1, s2, n);
}


void bzero(void* s, size_t n) {
  (void)memset(s, 0, n);
}


void* rawmemchr(const void* s, int c) {
  register const unsigned char* r = s;
  while (*r != ((unsigned char)c)) ++r;
  return (void*)r;
}


char* stpcpy(register char* s1, const char* s2) {
  while ((*s1++ = *s2++) != 0);
  return s1 - 1;
}


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


int tolower(int c) {
  int ch = c;
  if ((unsigned int)(ch - 'A') < 26u)
    ch -= 'A' - 'a';
  return ch;
}


int toupper(int c) {
  int ch = c;
  if ((unsigned int)(ch - 'a') < 26u)
    ch += 'A' - 'a';
  return ch;
}


int strcasecmp(register const char* s1, register const char* s2) {
  while ((*s1 == *s2) || (tolower(*s1) == tolower(*s2))) {
    if (!*s1++) {
      return 0;
    }
    ++s2;
  }
  return (((unsigned char)tolower(*s1)) < ((unsigned char)tolower(*s2))) ? -1 : 1;
}


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


char* strcat(char* s1, register const char* s2)
{
  register char* s = s1;

  while (*s++);
  --s;
  while ((*s++ = *s2++) != 0);

  return s1;
}


char* strchr(register const char* s, int c) {
  do {
    if (*s == ((char)c)) {
      return (char*)s;
    }
  } while (*s++);

  return NULL;
}


char* strchrnul(register const char* s, int c) {
  --s;
  while (*++s && (*s != ((char)c)));
  return (char*)s;
}


int strcmp(register const char* s1, register const char* s2) {
  int r;
  while (((r = ((int)(*((unsigned char*)s1))) - *((unsigned char*)s2++)) == 0) && *s1++);
  return r;
}


char* strcpy(char* s1, const char* s2) {
  register char* s = s1;
  while ((*s++ = *s2++) != 0);
  return s1;
}


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


size_t strlen(const char* s) {
  register const char* p;
  for (p=s ; *p ; p++);
  return p - s;
}


char* strdup(register const char* s1) {
  register char* s;
  register size_t l = (strlen(s1) + 1) * sizeof(char);

  if ((s = malloc(l)) != NULL) {
    memcpy(s, s1, l);
  }

  return s;
}


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


int strncasecmp(register const char* s1, register const char* s2, size_t n) {
  int r = 0;
  while (n && ((s1 == s2) || !(r = ((int)(tolower(*((unsigned char*)s1)))) - tolower(*((unsigned char*)s2)))) && (--n, ++s2, *s1++));
  return r;
}


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


int strncmp(register const char* s1, register const char* s2, size_t n) {
  int r = 0;
  while (n-- && ((r = ((int)(*((unsigned char *)s1))) - *((unsigned char *)s2++)) == 0) && *s1++);
  return r;
}


char* strncpy(char* s1, register const char* s2, size_t n) {
  register char* s = s1;

  while (n) {
    if ((*s = *s2) != 0) s2++; /* Need to fill tail with 0s. */
    ++s;
    --n;
  }

  return s1;
}


size_t strnlen(const char* s, size_t max) {
  register const char* p = s;

  while (max && *p) {
    ++p;
    --max;
  }

  return p - s;
}


char* strndup(register const char* s1, size_t n) {
  register char* s;

  n = strnlen(s1,n); /* Avoid problems if s1 not nul-terminated. */

  if ((s = malloc(n + 1)) != NULL) {
    memcpy(s, s1, n);
    s[n] = 0;
  }

  return s;
}


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


char* strtok(char* s1, const char* s2) {
  static char* next_start = NULL; /* Initialized to 0 since in bss. */
  return strtok_r(s1, s2, &next_start);
}
