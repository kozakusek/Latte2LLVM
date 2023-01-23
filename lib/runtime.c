#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void printInt(int x) {
    if (printf("%d\n", x) < 0) {
        perror("printInt: ");
        exit(1);
    }
    fflush(stdout);
}

void printString(char* s) {
    if (printf("%s\n", s) < 0) {
        perror("printString: ");
        exit(1);
    }
    fflush(stdout);
}

int readInt() {
    int x;
    if (scanf("%d\n", &x) < 0) {
        perror("readInt: ");
        exit(1);
    }
    return x;
}

char* readString() {
    char *c = NULL;
    size_t dump;
    size_t s = getline(&c, &dump, stdin);
    if (s == -1) {
        free(c);
        perror("readString: ");
    }
    c[s - 1] = '\0';
    return c;
}

void error() {
    fprintf(stderr, "runtime error\n");
    exit(1);
}

char* concatStrings(char* s1,  char* s2) {
    size_t s1l = strlen(s1);
    size_t s2l = strlen(s2);
    char* s = calloc(sizeof(char), s1l + s2l + 1);
    if (s == NULL) {
        perror("concatStrings: ");
        exit(1);
    }
    strcat(s, s1);
    strcat(s, s2);
    return s;
}

int compareStrings(char* s1,  char* s2) {
    return strcmp(s1, s2) == 0;
}

char* __calloc__(int size) {
    return (char*) calloc(1, size);
}