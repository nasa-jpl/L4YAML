/*
 * tryparse_c — Minimal C tryparse for yaml-test-suite integration.
 *
 * Reads a YAML file, parses it via the C API (l4yaml_parse), and
 * exits 0 on success, 1 on parse error.  Mirrors the Lean tryparse
 * binary exactly so the suiterunner can swap backends.
 *
 * Usage: tryparse_c <file.yaml> [preset]
 *   preset: unlimited (default) | default | strict | permissive | safe_tags
 */
#include "l4yaml.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint8_t parse_preset(const char *name) {
    if (strcmp(name, "default") == 0)    return L4YAML_LIMITS_DEFAULT;
    if (strcmp(name, "strict") == 0)     return L4YAML_LIMITS_STRICT;
    if (strcmp(name, "permissive") == 0) return L4YAML_LIMITS_PERMISSIVE;
    if (strcmp(name, "unlimited") == 0)  return L4YAML_LIMITS_UNLIMITED;
    if (strcmp(name, "safe_tags") == 0)  return L4YAML_LIMITS_SAFE_TAGS;
    return 255; /* invalid */
}

int main(int argc, char *argv[]) {
    if (argc < 2 || argc > 3) {
        fprintf(stderr, "Usage: tryparse_c <file.yaml> [preset]\n");
        return 2;
    }

    uint8_t preset = L4YAML_LIMITS_UNLIMITED;
    if (argc == 3) {
        preset = parse_preset(argv[2]);
        if (preset == 255) {
            fprintf(stderr, "Unknown preset '%s'; choose from: unlimited, default, strict, permissive, safe_tags\n", argv[2]);
            return 2;
        }
    }

    /* Read the file */
    FILE *f = fopen(argv[1], "rb");
    if (!f) {
        fprintf(stderr, "Cannot open %s\n", argv[1]);
        return 2;
    }
    fseek(f, 0, SEEK_END);
    long len = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = malloc((size_t)len + 1);
    if (!buf) {
        fclose(f);
        fprintf(stderr, "Out of memory\n");
        return 2;
    }
    size_t nread = fread(buf, 1, (size_t)len, f);
    fclose(f);
    buf[nread] = '\0';

    /* Initialize and parse with the selected preset. */
    l4yaml_initialize();
    l4yaml_result_t result = l4yaml_parse(buf, nread, preset);
    int ok = l4yaml_result_is_ok(result);

    if (!ok) {
        const char *msg = l4yaml_result_error_message(result);
        if (msg) fprintf(stderr, "%s\n", msg);
    }

    l4yaml_free(result);
    free(buf);
    l4yaml_finalize();

    return ok ? 0 : 1;
}
