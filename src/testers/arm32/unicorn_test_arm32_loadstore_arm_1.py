#!/usr/bin/env python
## -*- coding: utf-8 -*-

from __future__          import print_function
from triton              import *
from unicorn             import *
from unicorn.arm_const   import *

import pprint
import random
import sys

ADDR  = 0x100000
STACK = 0x200000
HEAP  = 0x300000
SIZE  = 5 * 1024 * 1024

CODE  = [
    # MISC ------------------------------------------------------------------- #
    (b"\x18\x50\xb1\xe8", "ldm r1!, {r3, r4, ip, lr}"),

    (b"\x04\xe0\x9f\xe5", "ldr lr, [pc, #4]"),

    (b"\x03\x00\x91\xe7", "ldr r0, [r1, r3]"),
    (b"\x03\x00\x11\xe7", "ldr r0, [r1, -r3]"),

    (b"\x03\x00\x91\xe6", "ldr r0, [r1], r3"),
    (b"\x03\x00\x11\xe6", "ldr r0, [r1], -r3"),

    (b"\x03\x01\x11\xe6", "ldr r0, [r1], -r3, lsl #2"),

    (b"\x03\x01\x91\xe7", "ldr r0, [r1, r3, lsl #2]"),

    (b"\x03\x01\x11\xe7", "ldr r0, [r1, -r3, lsl #2]"),
    (b"\x03\x01\x31\xe7", "ldr r0, [r1, -r3, lsl #2]!"),

    (b"\x04\x00\x11\xe4", "ldr r0, [r1], #-4"),

    (b"\x03\x00\xd1\xe7", "ldrb r0, [r1, r3]"),
    (b"\x03\x00\x51\xe7", "ldrb r0, [r1, -r3]"),
    (b"\x03\x00\xd1\xe6", "ldrb r0, [r1], r3"),
    (b"\x03\x00\x51\xe6", "ldrb r0, [r1], -r3"),
    (b"\x03\x01\x51\xe6", "ldrb r0, [r1], -r3, lsl #2"),
    (b"\x03\x01\x51\xe7", "ldrb r0, [r1, -r3, lsl #2]"),
    (b"\x03\x01\x71\xe7", "ldrb r0, [r1, -r3, lsl #2]!"),
    (b"\x04\x00\x51\xe4", "ldrb r0, [r1], #-4"),
    # (b"\x64\x00\x51\xe7", "ldrb r0, [r1, -r4, rrx]"), # FIXME: UC throws "Invalid memory read (UC_ERR_READ_UNMAPPED)" for some runs.


    (b"\x08\x00\xa1\xe8", "stm r1!, {r3}"),
    (b"\x18\x50\xa1\xe8", "stm r1!, {r3, r4, ip, lr}"),

    (b"\xf0\x00\xa1\xe8", "stmia r1!, {r4, r5, r6, r7}"),

    (b"\xf0\x00\x81\xe9", "stmib r1, {r4, r5, r6, r7}"),
    (b"\xf0\x00\xa1\xe9", "stmib r1!, {r4, r5, r6, r7}"),

    (b"\x03\x00\x8d\xe9", "stmib sp, {r0, r1}"),

    (b"\x04\xb0\x0d\xe5", "str fp, [sp, #-4]"),
    (b"\x04\xb0\x2d\xe5", "str fp, [sp, #-4]!"),
    (b"\x04\xb0\x0d\xe4", "str fp, [sp], #-4"),

    (b"\x00\x00\xc1\xe5", "strb r0, [r1]"),
    (b"\x03\x10\xc1\xe7", "strb r1, [r1, r3]"),
    (b"\x04\x10\x41\xe5", "strb r1, [r1, #-4]"),

    (b"\xf4\x00\xcd\xe1", "strd r0, r1, [sp, #4]"),
    (b"\xf4\x00\x4d\xe1", "strd r0, r1, [sp, #-4]"),
    (b"\xf3\x00\x8d\xe1", "strd r0, r1, [sp, r3]"),
    (b"\xf3\x00\x0d\xe1", "strd r0, r1, [sp, -r3]"),
    (b"\xf3\x00\x8d\xe0", "strd r0, r1, [sp], r3"),
    (b"\xf3\x00\x0d\xe0", "strd r0, r1, [sp], -r3"),
    (b"\xf4\x00\xcd\xe0", "strd r0, r1, [sp], #0x4"),
    (b"\xf4\x00\x4d\xe0", "strd r0, r1, [sp], #-0x4"),

    (b"\xb4\x00\x41\x00", "strheq r0, [r1], #-4"),
    (b"\xb3\x00\x01\x00", "strheq r0, [r1], -r3"),

    # LDR - Offset addressing -----------------------------------------------  #
    (b"\x00\x00\x91\xe5", "ldr r0, [r1]"),
    (b"\x00\x00\x91\x05", "ldreq r0, [r1]"),
    (b"\x00\x00\x91\x15", "ldrne r0, [r1]"),
    (b"\x00\x00\x91\x25", "ldrcs r0, [r1]"),
    (b"\x00\x00\x91\x35", "ldrcc r0, [r1]"),
    (b"\x00\x00\x91\x45", "ldrmi r0, [r1]"),
    (b"\x00\x00\x91\x55", "ldrpl r0, [r1]"),
    (b"\x00\x00\x91\x65", "ldrvs r0, [r1]"),
    (b"\x00\x00\x91\x75", "ldrvc r0, [r1]"),
    (b"\x00\x00\x91\x85", "ldrhi r0, [r1]"),
    (b"\x00\x00\x91\x95", "ldrls r0, [r1]"),
    (b"\x00\x00\x91\xa5", "ldrge r0, [r1]"),
    (b"\x00\x00\x91\xb5", "ldrlt r0, [r1]"),
    (b"\x00\x00\x91\xc5", "ldrgt r0, [r1]"),
    (b"\x00\x00\x91\xd5", "ldrle r0, [r1]"),
    (b"\x00\x00\x91\xe5", "ldral r0, [r1]"),

    (b"\x04\x00\x91\xe5", "ldr r0, [r1, #0x4]"),
    (b"\x04\x00\x91\x05", "ldreq r0, [r1, #0x4]"),
    (b"\x04\x00\x91\x15", "ldrne r0, [r1, #0x4]"),
    (b"\x04\x00\x91\x25", "ldrcs r0, [r1, #0x4]"),
    (b"\x04\x00\x91\x35", "ldrcc r0, [r1, #0x4]"),
    (b"\x04\x00\x91\x45", "ldrmi r0, [r1, #0x4]"),
    (b"\x04\x00\x91\x55", "ldrpl r0, [r1, #0x4]"),
    (b"\x04\x00\x91\x65", "ldrvs r0, [r1, #0x4]"),
    (b"\x04\x00\x91\x75", "ldrvc r0, [r1, #0x4]"),
    (b"\x04\x00\x91\x85", "ldrhi r0, [r1, #0x4]"),
    (b"\x04\x00\x91\x95", "ldrls r0, [r1, #0x4]"),
    (b"\x04\x00\x91\xa5", "ldrge r0, [r1, #0x4]"),
    (b"\x04\x00\x91\xb5", "ldrlt r0, [r1, #0x4]"),
    (b"\x04\x00\x91\xc5", "ldrgt r0, [r1, #0x4]"),
    (b"\x04\x00\x91\xd5", "ldrle r0, [r1, #0x4]"),
    (b"\x04\x00\x91\xe5", "ldral r0, [r1, #0x4]"),

    (b"\x04\x00\x11\xe5", "ldr r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\x05", "ldreq r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\x15", "ldrne r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\x25", "ldrcs r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\x35", "ldrcc r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\x45", "ldrmi r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\x55", "ldrpl r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\x65", "ldrvs r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\x75", "ldrvc r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\x85", "ldrhi r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\x95", "ldrls r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\xa5", "ldrge r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\xb5", "ldrlt r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\xc5", "ldrgt r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\xd5", "ldrle r0, [r1, #-0x4]"),
    (b"\x04\x00\x11\xe5", "ldral r0, [r1, #-0x4]"),

    # LDR - Pre-indexed addressing ------------------------------------------- #
    (b"\x00\x00\xb1\xe5", "ldr r0, [r1]!"),
    (b"\x00\x00\xb1\x05", "ldreq r0, [r1]!"),
    (b"\x00\x00\xb1\x15", "ldrne r0, [r1]!"),
    (b"\x00\x00\xb1\x25", "ldrcs r0, [r1]!"),
    (b"\x00\x00\xb1\x35", "ldrcc r0, [r1]!"),
    (b"\x00\x00\xb1\x45", "ldrmi r0, [r1]!"),
    (b"\x00\x00\xb1\x55", "ldrpl r0, [r1]!"),
    (b"\x00\x00\xb1\x65", "ldrvs r0, [r1]!"),
    (b"\x00\x00\xb1\x75", "ldrvc r0, [r1]!"),
    (b"\x00\x00\xb1\x85", "ldrhi r0, [r1]!"),
    (b"\x00\x00\xb1\x95", "ldrls r0, [r1]!"),
    (b"\x00\x00\xb1\xa5", "ldrge r0, [r1]!"),
    (b"\x00\x00\xb1\xb5", "ldrlt r0, [r1]!"),
    (b"\x00\x00\xb1\xc5", "ldrgt r0, [r1]!"),
    (b"\x00\x00\xb1\xd5", "ldrle r0, [r1]!"),
    (b"\x00\x00\xb1\xe5", "ldral r0, [r1]!"),

    (b"\x04\x00\xb1\xe5", "ldr r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\x05", "ldreq r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\x15", "ldrne r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\x25", "ldrcs r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\x35", "ldrcc r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\x45", "ldrmi r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\x55", "ldrpl r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\x65", "ldrvs r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\x75", "ldrvc r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\x85", "ldrhi r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\x95", "ldrls r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\xa5", "ldrge r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\xb5", "ldrlt r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\xc5", "ldrgt r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\xd5", "ldrle r0, [r1, #0x4]!"),
    (b"\x04\x00\xb1\xe5", "ldral r0, [r1, #0x4]!"),

    (b"\x04\x00\x31\xe5", "ldr r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\x05", "ldreq r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\x15", "ldrne r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\x25", "ldrcs r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\x35", "ldrcc r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\x45", "ldrmi r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\x55", "ldrpl r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\x65", "ldrvs r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\x75", "ldrvc r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\x85", "ldrhi r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\x95", "ldrls r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\xa5", "ldrge r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\xb5", "ldrlt r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\xc5", "ldrgt r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\xd5", "ldrle r0, [r1, #-0x4]!"),
    (b"\x04\x00\x31\xe5", "ldral r0, [r1, #-0x4]!"),

    # LDR - Post-indexed addressing ------------------------------------------ #
    (b"\x04\x00\x91\xe4", "ldr r0, [r1], #0x4"),
    (b"\x04\x00\x91\x04", "ldreq r0, [r1], #0x4"),
    (b"\x04\x00\x91\x14", "ldrne r0, [r1], #0x4"),
    (b"\x04\x00\x91\x24", "ldrcs r0, [r1], #0x4"),
    (b"\x04\x00\x91\x34", "ldrcc r0, [r1], #0x4"),
    (b"\x04\x00\x91\x44", "ldrmi r0, [r1], #0x4"),
    (b"\x04\x00\x91\x54", "ldrpl r0, [r1], #0x4"),
    (b"\x04\x00\x91\x64", "ldrvs r0, [r1], #0x4"),
    (b"\x04\x00\x91\x74", "ldrvc r0, [r1], #0x4"),
    (b"\x04\x00\x91\x84", "ldrhi r0, [r1], #0x4"),
    (b"\x04\x00\x91\x94", "ldrls r0, [r1], #0x4"),
    (b"\x04\x00\x91\xa4", "ldrge r0, [r1], #0x4"),
    (b"\x04\x00\x91\xb4", "ldrlt r0, [r1], #0x4"),
    (b"\x04\x00\x91\xc4", "ldrgt r0, [r1], #0x4"),
    (b"\x04\x00\x91\xd4", "ldrle r0, [r1], #0x4"),
    (b"\x04\x00\x91\xe4", "ldral r0, [r1], #0x4"),

    (b"\x04\x00\x11\xe4", "ldr r0, [r1], #-0x4"),
    (b"\x04\x00\x11\x04", "ldreq r0, [r1], #-0x4"),
    (b"\x04\x00\x11\x14", "ldrne r0, [r1], #-0x4"),
    (b"\x04\x00\x11\x24", "ldrcs r0, [r1], #-0x4"),
    (b"\x04\x00\x11\x34", "ldrcc r0, [r1], #-0x4"),
    (b"\x04\x00\x11\x44", "ldrmi r0, [r1], #-0x4"),
    (b"\x04\x00\x11\x54", "ldrpl r0, [r1], #-0x4"),
    (b"\x04\x00\x11\x64", "ldrvs r0, [r1], #-0x4"),
    (b"\x04\x00\x11\x74", "ldrvc r0, [r1], #-0x4"),
    (b"\x04\x00\x11\x84", "ldrhi r0, [r1], #-0x4"),
    (b"\x04\x00\x11\x94", "ldrls r0, [r1], #-0x4"),
    (b"\x04\x00\x11\xa4", "ldrge r0, [r1], #-0x4"),
    (b"\x04\x00\x11\xb4", "ldrlt r0, [r1], #-0x4"),
    (b"\x04\x00\x11\xc4", "ldrgt r0, [r1], #-0x4"),
    (b"\x04\x00\x11\xd4", "ldrle r0, [r1], #-0x4"),
    (b"\x04\x00\x11\xe4", "ldral r0, [r1], #-0x4"),

    # LDR with SP as operand ------------------------------------------------- #
    (b"\x00\xd0\x91\xe5", "ldr sp, [r1]"),
    (b"\x00\xd0\x91\x05", "ldreq sp, [r1]"),
    (b"\x00\xd0\x91\x15", "ldrne sp, [r1]"),
    (b"\x00\xd0\x91\x25", "ldrcs sp, [r1]"),
    (b"\x00\xd0\x91\x35", "ldrcc sp, [r1]"),
    (b"\x00\xd0\x91\x45", "ldrmi sp, [r1]"),
    (b"\x00\xd0\x91\x55", "ldrpl sp, [r1]"),
    (b"\x00\xd0\x91\x65", "ldrvs sp, [r1]"),
    (b"\x00\xd0\x91\x75", "ldrvc sp, [r1]"),
    (b"\x00\xd0\x91\x85", "ldrhi sp, [r1]"),
    (b"\x00\xd0\x91\x95", "ldrls sp, [r1]"),
    (b"\x00\xd0\x91\xa5", "ldrge sp, [r1]"),
    (b"\x00\xd0\x91\xb5", "ldrlt sp, [r1]"),
    (b"\x00\xd0\x91\xc5", "ldrgt sp, [r1]"),
    (b"\x00\xd0\x91\xd5", "ldrle sp, [r1]"),
    (b"\x00\xd0\x91\xe5", "ldral sp, [r1]"),

    (b"\x00\x00\x9d\xe5", "ldr r0, [sp]"),
    (b"\x00\x00\x9d\x05", "ldreq r0, [sp]"),
    (b"\x00\x00\x9d\x15", "ldrne r0, [sp]"),
    (b"\x00\x00\x9d\x25", "ldrcs r0, [sp]"),
    (b"\x00\x00\x9d\x35", "ldrcc r0, [sp]"),
    (b"\x00\x00\x9d\x45", "ldrmi r0, [sp]"),
    (b"\x00\x00\x9d\x55", "ldrpl r0, [sp]"),
    (b"\x00\x00\x9d\x65", "ldrvs r0, [sp]"),
    (b"\x00\x00\x9d\x75", "ldrvc r0, [sp]"),
    (b"\x00\x00\x9d\x85", "ldrhi r0, [sp]"),
    (b"\x00\x00\x9d\x95", "ldrls r0, [sp]"),
    (b"\x00\x00\x9d\xa5", "ldrge r0, [sp]"),
    (b"\x00\x00\x9d\xb5", "ldrlt r0, [sp]"),
    (b"\x00\x00\x9d\xc5", "ldrgt r0, [sp]"),
    (b"\x00\x00\x9d\xd5", "ldrle r0, [sp]"),
    (b"\x00\x00\x9d\xe5", "ldral r0, [sp]"),

    # LDRB - Offset addressing ----------------------------------------------  #
    (b"\x00\x00\xd1\xe5", "ldrb r0, [r1]"),
    (b"\x00\x00\xd1\x05", "ldrbeq r0, [r1]"),
    (b"\x00\x00\xd1\x15", "ldrbne r0, [r1]"),
    (b"\x00\x00\xd1\x25", "ldrbcs r0, [r1]"),
    (b"\x00\x00\xd1\x35", "ldrbcc r0, [r1]"),
    (b"\x00\x00\xd1\x45", "ldrbmi r0, [r1]"),
    (b"\x00\x00\xd1\x55", "ldrbpl r0, [r1]"),
    (b"\x00\x00\xd1\x65", "ldrbvs r0, [r1]"),
    (b"\x00\x00\xd1\x75", "ldrbvc r0, [r1]"),
    (b"\x00\x00\xd1\x85", "ldrbhi r0, [r1]"),
    (b"\x00\x00\xd1\x95", "ldrbls r0, [r1]"),
    (b"\x00\x00\xd1\xa5", "ldrbge r0, [r1]"),
    (b"\x00\x00\xd1\xb5", "ldrblt r0, [r1]"),
    (b"\x00\x00\xd1\xc5", "ldrbgt r0, [r1]"),
    (b"\x00\x00\xd1\xd5", "ldrble r0, [r1]"),
    (b"\x00\x00\xd1\xe5", "ldrbal r0, [r1]"),

    (b"\x04\x00\xd1\xe5", "ldrb r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\x05", "ldrbeq r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\x15", "ldrbne r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\x25", "ldrbcs r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\x35", "ldrbcc r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\x45", "ldrbmi r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\x55", "ldrbpl r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\x65", "ldrbvs r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\x75", "ldrbvc r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\x85", "ldrbhi r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\x95", "ldrbls r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\xa5", "ldrbge r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\xb5", "ldrblt r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\xc5", "ldrbgt r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\xd5", "ldrble r0, [r1, #0x4]"),
    (b"\x04\x00\xd1\xe5", "ldrbal r0, [r1, #0x4]"),

    (b"\x04\x00\x51\xe5", "ldrb r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\x05", "ldrbeq r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\x15", "ldrbne r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\x25", "ldrbcs r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\x35", "ldrbcc r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\x45", "ldrbmi r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\x55", "ldrbpl r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\x65", "ldrbvs r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\x75", "ldrbvc r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\x85", "ldrbhi r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\x95", "ldrbls r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\xa5", "ldrbge r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\xb5", "ldrblt r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\xc5", "ldrbgt r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\xd5", "ldrble r0, [r1, #-0x4]"),
    (b"\x04\x00\x51\xe5", "ldrbal r0, [r1, #-0x4]"),

    # LDRB - Pre-indexed addressing ------------------------------------------ #
    (b"\x00\x00\xf1\xe5", "ldrb r0, [r1]!"),
    (b"\x00\x00\xf1\x05", "ldrbeq r0, [r1]!"),
    (b"\x00\x00\xf1\x15", "ldrbne r0, [r1]!"),
    (b"\x00\x00\xf1\x25", "ldrbcs r0, [r1]!"),
    (b"\x00\x00\xf1\x35", "ldrbcc r0, [r1]!"),
    (b"\x00\x00\xf1\x45", "ldrbmi r0, [r1]!"),
    (b"\x00\x00\xf1\x55", "ldrbpl r0, [r1]!"),
    (b"\x00\x00\xf1\x65", "ldrbvs r0, [r1]!"),
    (b"\x00\x00\xf1\x75", "ldrbvc r0, [r1]!"),
    (b"\x00\x00\xf1\x85", "ldrbhi r0, [r1]!"),
    (b"\x00\x00\xf1\x95", "ldrbls r0, [r1]!"),
    (b"\x00\x00\xf1\xa5", "ldrbge r0, [r1]!"),
    (b"\x00\x00\xf1\xb5", "ldrblt r0, [r1]!"),
    (b"\x00\x00\xf1\xc5", "ldrbgt r0, [r1]!"),
    (b"\x00\x00\xf1\xd5", "ldrble r0, [r1]!"),
    (b"\x00\x00\xf1\xe5", "ldrbal r0, [r1]!"),

    (b"\x04\x00\xf1\xe5", "ldrb r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\x05", "ldrbeq r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\x15", "ldrbne r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\x25", "ldrbcs r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\x35", "ldrbcc r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\x45", "ldrbmi r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\x55", "ldrbpl r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\x65", "ldrbvs r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\x75", "ldrbvc r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\x85", "ldrbhi r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\x95", "ldrbls r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\xa5", "ldrbge r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\xb5", "ldrblt r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\xc5", "ldrbgt r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\xd5", "ldrble r0, [r1, #0x4]!"),
    (b"\x04\x00\xf1\xe5", "ldrbal r0, [r1, #0x4]!"),

    (b"\x04\x00\x71\xe5", "ldrb r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\x05", "ldrbeq r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\x15", "ldrbne r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\x25", "ldrbcs r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\x35", "ldrbcc r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\x45", "ldrbmi r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\x55", "ldrbpl r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\x65", "ldrbvs r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\x75", "ldrbvc r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\x85", "ldrbhi r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\x95", "ldrbls r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\xa5", "ldrbge r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\xb5", "ldrblt r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\xc5", "ldrbgt r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\xd5", "ldrble r0, [r1, #-0x4]!"),
    (b"\x04\x00\x71\xe5", "ldrbal r0, [r1, #-0x4]!"),

    # LDRB - Post-indexed addressing ------------------------------------------ #
    (b"\x04\x00\xd1\xe4", "ldrb r0, [r1], #0x4"),
    (b"\x04\x00\xd1\x04", "ldrbeq r0, [r1], #0x4"),
    (b"\x04\x00\xd1\x14", "ldrbne r0, [r1], #0x4"),
    (b"\x04\x00\xd1\x24", "ldrbcs r0, [r1], #0x4"),
    (b"\x04\x00\xd1\x34", "ldrbcc r0, [r1], #0x4"),
    (b"\x04\x00\xd1\x44", "ldrbmi r0, [r1], #0x4"),
    (b"\x04\x00\xd1\x54", "ldrbpl r0, [r1], #0x4"),
    (b"\x04\x00\xd1\x64", "ldrbvs r0, [r1], #0x4"),
    (b"\x04\x00\xd1\x74", "ldrbvc r0, [r1], #0x4"),
    (b"\x04\x00\xd1\x84", "ldrbhi r0, [r1], #0x4"),
    (b"\x04\x00\xd1\x94", "ldrbls r0, [r1], #0x4"),
    (b"\x04\x00\xd1\xa4", "ldrbge r0, [r1], #0x4"),
    (b"\x04\x00\xd1\xb4", "ldrblt r0, [r1], #0x4"),
    (b"\x04\x00\xd1\xc4", "ldrbgt r0, [r1], #0x4"),
    (b"\x04\x00\xd1\xd4", "ldrble r0, [r1], #0x4"),
    (b"\x04\x00\xd1\xe4", "ldrbal r0, [r1], #0x4"),

    (b"\x04\x00\x51\xe4", "ldrb r0, [r1], #-0x4"),
    (b"\x04\x00\x51\x04", "ldrbeq r0, [r1], #-0x4"),
    (b"\x04\x00\x51\x14", "ldrbne r0, [r1], #-0x4"),
    (b"\x04\x00\x51\x24", "ldrbcs r0, [r1], #-0x4"),
    (b"\x04\x00\x51\x34", "ldrbcc r0, [r1], #-0x4"),
    (b"\x04\x00\x51\x44", "ldrbmi r0, [r1], #-0x4"),
    (b"\x04\x00\x51\x54", "ldrbpl r0, [r1], #-0x4"),
    (b"\x04\x00\x51\x64", "ldrbvs r0, [r1], #-0x4"),
    (b"\x04\x00\x51\x74", "ldrbvc r0, [r1], #-0x4"),
    (b"\x04\x00\x51\x84", "ldrbhi r0, [r1], #-0x4"),
    (b"\x04\x00\x51\x94", "ldrbls r0, [r1], #-0x4"),
    (b"\x04\x00\x51\xa4", "ldrbge r0, [r1], #-0x4"),
    (b"\x04\x00\x51\xb4", "ldrblt r0, [r1], #-0x4"),
    (b"\x04\x00\x51\xc4", "ldrbgt r0, [r1], #-0x4"),
    (b"\x04\x00\x51\xd4", "ldrble r0, [r1], #-0x4"),
    (b"\x04\x00\x51\xe4", "ldrbal r0, [r1], #-0x4"),

    # STR - Offset addressing ------------------------------------------------ #
    (b"\x00\x00\x81\xe5", "str r0, [r1]"),
    (b"\x00\x00\x81\x05", "streq r0, [r1]"),
    (b"\x00\x00\x81\x15", "strne r0, [r1]"),
    (b"\x00\x00\x81\x25", "strcs r0, [r1]"),
    (b"\x00\x00\x81\x35", "strcc r0, [r1]"),
    (b"\x00\x00\x81\x45", "strmi r0, [r1]"),
    (b"\x00\x00\x81\x55", "strpl r0, [r1]"),
    (b"\x00\x00\x81\x65", "strvs r0, [r1]"),
    (b"\x00\x00\x81\x75", "strvc r0, [r1]"),
    (b"\x00\x00\x81\x85", "strhi r0, [r1]"),
    (b"\x00\x00\x81\x95", "strls r0, [r1]"),
    (b"\x00\x00\x81\xa5", "strge r0, [r1]"),
    (b"\x00\x00\x81\xb5", "strlt r0, [r1]"),
    (b"\x00\x00\x81\xc5", "strgt r0, [r1]"),
    (b"\x00\x00\x81\xd5", "strle r0, [r1]"),
    (b"\x00\x00\x81\xe5", "stral r0, [r1]"),

    (b"\x04\x00\x81\xe5", "str r0, [r1, #0x4]"),
    (b"\x04\x00\x81\x05", "streq r0, [r1, #0x4]"),
    (b"\x04\x00\x81\x15", "strne r0, [r1, #0x4]"),
    (b"\x04\x00\x81\x25", "strcs r0, [r1, #0x4]"),
    (b"\x04\x00\x81\x35", "strcc r0, [r1, #0x4]"),
    (b"\x04\x00\x81\x45", "strmi r0, [r1, #0x4]"),
    (b"\x04\x00\x81\x55", "strpl r0, [r1, #0x4]"),
    (b"\x04\x00\x81\x65", "strvs r0, [r1, #0x4]"),
    (b"\x04\x00\x81\x75", "strvc r0, [r1, #0x4]"),
    (b"\x04\x00\x81\x85", "strhi r0, [r1, #0x4]"),
    (b"\x04\x00\x81\x95", "strls r0, [r1, #0x4]"),
    (b"\x04\x00\x81\xa5", "strge r0, [r1, #0x4]"),
    (b"\x04\x00\x81\xb5", "strlt r0, [r1, #0x4]"),
    (b"\x04\x00\x81\xc5", "strgt r0, [r1, #0x4]"),
    (b"\x04\x00\x81\xd5", "strle r0, [r1, #0x4]"),
    (b"\x04\x00\x81\xe5", "stral r0, [r1, #0x4]"),

    (b"\x04\x00\x01\xe5", "str r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\x05", "streq r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\x15", "strne r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\x25", "strcs r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\x35", "strcc r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\x45", "strmi r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\x55", "strpl r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\x65", "strvs r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\x75", "strvc r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\x85", "strhi r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\x95", "strls r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\xa5", "strge r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\xb5", "strlt r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\xc5", "strgt r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\xd5", "strle r0, [r1, #-0x4]"),
    (b"\x04\x00\x01\xe5", "stral r0, [r1, #-0x4]"),

    # STR - Pre-indexed addressing ------------------------------------------- #
    (b"\x00\x00\xa1\xe5", "str r0, [r1]!"),
    (b"\x00\x00\xa1\x05", "streq r0, [r1]!"),
    (b"\x00\x00\xa1\x15", "strne r0, [r1]!"),
    (b"\x00\x00\xa1\x25", "strcs r0, [r1]!"),
    (b"\x00\x00\xa1\x35", "strcc r0, [r1]!"),
    (b"\x00\x00\xa1\x45", "strmi r0, [r1]!"),
    (b"\x00\x00\xa1\x55", "strpl r0, [r1]!"),
    (b"\x00\x00\xa1\x65", "strvs r0, [r1]!"),
    (b"\x00\x00\xa1\x75", "strvc r0, [r1]!"),
    (b"\x00\x00\xa1\x85", "strhi r0, [r1]!"),
    (b"\x00\x00\xa1\x95", "strls r0, [r1]!"),
    (b"\x00\x00\xa1\xa5", "strge r0, [r1]!"),
    (b"\x00\x00\xa1\xb5", "strlt r0, [r1]!"),
    (b"\x00\x00\xa1\xc5", "strgt r0, [r1]!"),
    (b"\x00\x00\xa1\xd5", "strle r0, [r1]!"),
    (b"\x00\x00\xa1\xe5", "stral r0, [r1]!"),

    (b"\x04\x00\xa1\xe5", "str r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\x05", "streq r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\x15", "strne r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\x25", "strcs r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\x35", "strcc r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\x45", "strmi r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\x55", "strpl r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\x65", "strvs r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\x75", "strvc r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\x85", "strhi r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\x95", "strls r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\xa5", "strge r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\xb5", "strlt r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\xc5", "strgt r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\xd5", "strle r0, [r1, #0x4]!"),
    (b"\x04\x00\xa1\xe5", "stral r0, [r1, #0x4]!"),

    (b"\x04\x00\x21\xe5", "str r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\x05", "streq r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\x15", "strne r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\x25", "strcs r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\x35", "strcc r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\x45", "strmi r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\x55", "strpl r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\x65", "strvs r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\x75", "strvc r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\x85", "strhi r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\x95", "strls r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\xa5", "strge r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\xb5", "strlt r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\xc5", "strgt r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\xd5", "strle r0, [r1, #-0x4]!"),
    (b"\x04\x00\x21\xe5", "stral r0, [r1, #-0x4]!"),

    # STR - Post-indexed addressing ------------------------------------------ #
    (b"\x04\x00\x81\xe4", "str r0, [r1], #0x4"),
    (b"\x04\x00\x81\x04", "streq r0, [r1], #0x4"),
    (b"\x04\x00\x81\x14", "strne r0, [r1], #0x4"),
    (b"\x04\x00\x81\x24", "strcs r0, [r1], #0x4"),
    (b"\x04\x00\x81\x34", "strcc r0, [r1], #0x4"),
    (b"\x04\x00\x81\x44", "strmi r0, [r1], #0x4"),
    (b"\x04\x00\x81\x54", "strpl r0, [r1], #0x4"),
    (b"\x04\x00\x81\x64", "strvs r0, [r1], #0x4"),
    (b"\x04\x00\x81\x74", "strvc r0, [r1], #0x4"),
    (b"\x04\x00\x81\x84", "strhi r0, [r1], #0x4"),
    (b"\x04\x00\x81\x94", "strls r0, [r1], #0x4"),
    (b"\x04\x00\x81\xa4", "strge r0, [r1], #0x4"),
    (b"\x04\x00\x81\xb4", "strlt r0, [r1], #0x4"),
    (b"\x04\x00\x81\xc4", "strgt r0, [r1], #0x4"),
    (b"\x04\x00\x81\xd4", "strle r0, [r1], #0x4"),
    (b"\x04\x00\x81\xe4", "stral r0, [r1], #0x4"),

    (b"\x04\x00\x01\xe4", "str r0, [r1], #-0x4"),
    (b"\x04\x00\x01\x04", "streq r0, [r1], #-0x4"),
    (b"\x04\x00\x01\x14", "strne r0, [r1], #-0x4"),
    (b"\x04\x00\x01\x24", "strcs r0, [r1], #-0x4"),
    (b"\x04\x00\x01\x34", "strcc r0, [r1], #-0x4"),
    (b"\x04\x00\x01\x44", "strmi r0, [r1], #-0x4"),
    (b"\x04\x00\x01\x54", "strpl r0, [r1], #-0x4"),
    (b"\x04\x00\x01\x64", "strvs r0, [r1], #-0x4"),
    (b"\x04\x00\x01\x74", "strvc r0, [r1], #-0x4"),
    (b"\x04\x00\x01\x84", "strhi r0, [r1], #-0x4"),
    (b"\x04\x00\x01\x94", "strls r0, [r1], #-0x4"),
    (b"\x04\x00\x01\xa4", "strge r0, [r1], #-0x4"),
    (b"\x04\x00\x01\xb4", "strlt r0, [r1], #-0x4"),
    (b"\x04\x00\x01\xc4", "strgt r0, [r1], #-0x4"),
    (b"\x04\x00\x01\xd4", "strle r0, [r1], #-0x4"),
    (b"\x04\x00\x01\xe4", "stral r0, [r1], #-0x4"),

    # STR with SP as operand ------------------------------------------------- #
    (b"\x00\xd0\x81\xe5", "str sp, [r1]"),
    (b"\x00\xd0\x81\x05", "streq sp, [r1]"),
    (b"\x00\xd0\x81\x15", "strne sp, [r1]"),
    (b"\x00\xd0\x81\x25", "strcs sp, [r1]"),
    (b"\x00\xd0\x81\x35", "strcc sp, [r1]"),
    (b"\x00\xd0\x81\x45", "strmi sp, [r1]"),
    (b"\x00\xd0\x81\x55", "strpl sp, [r1]"),
    (b"\x00\xd0\x81\x65", "strvs sp, [r1]"),
    (b"\x00\xd0\x81\x75", "strvc sp, [r1]"),
    (b"\x00\xd0\x81\x85", "strhi sp, [r1]"),
    (b"\x00\xd0\x81\x95", "strls sp, [r1]"),
    (b"\x00\xd0\x81\xa5", "strge sp, [r1]"),
    (b"\x00\xd0\x81\xb5", "strlt sp, [r1]"),
    (b"\x00\xd0\x81\xc5", "strgt sp, [r1]"),
    (b"\x00\xd0\x81\xd5", "strle sp, [r1]"),
    (b"\x00\xd0\x81\xe5", "stral sp, [r1]"),

    (b"\x00\x00\x8d\xe5", "str r0, [sp]"),
    (b"\x00\x00\x8d\x05", "streq r0, [sp]"),
    (b"\x00\x00\x8d\x15", "strne r0, [sp]"),
    (b"\x00\x00\x8d\x25", "strcs r0, [sp]"),
    (b"\x00\x00\x8d\x35", "strcc r0, [sp]"),
    (b"\x00\x00\x8d\x45", "strmi r0, [sp]"),
    (b"\x00\x00\x8d\x55", "strpl r0, [sp]"),
    (b"\x00\x00\x8d\x65", "strvs r0, [sp]"),
    (b"\x00\x00\x8d\x75", "strvc r0, [sp]"),
    (b"\x00\x00\x8d\x85", "strhi r0, [sp]"),
    (b"\x00\x00\x8d\x95", "strls r0, [sp]"),
    (b"\x00\x00\x8d\xa5", "strge r0, [sp]"),
    (b"\x00\x00\x8d\xb5", "strlt r0, [sp]"),
    (b"\x00\x00\x8d\xc5", "strgt r0, [sp]"),
    (b"\x00\x00\x8d\xd5", "strle r0, [sp]"),
    (b"\x00\x00\x8d\xe5", "stral r0, [sp]"),

    # STRB - Offset addressing ----------------------------------------------- #
    (b"\x00\x00\xc1\xe5", "strb r0, [r1]"),
    (b"\x00\x00\xc1\x05", "strbeq r0, [r1]"),
    (b"\x00\x00\xc1\x15", "strbne r0, [r1]"),
    (b"\x00\x00\xc1\x25", "strbcs r0, [r1]"),
    (b"\x00\x00\xc1\x35", "strbcc r0, [r1]"),
    (b"\x00\x00\xc1\x45", "strbmi r0, [r1]"),
    (b"\x00\x00\xc1\x55", "strbpl r0, [r1]"),
    (b"\x00\x00\xc1\x65", "strbvs r0, [r1]"),
    (b"\x00\x00\xc1\x75", "strbvc r0, [r1]"),
    (b"\x00\x00\xc1\x85", "strbhi r0, [r1]"),
    (b"\x00\x00\xc1\x95", "strbls r0, [r1]"),
    (b"\x00\x00\xc1\xa5", "strbge r0, [r1]"),
    (b"\x00\x00\xc1\xb5", "strblt r0, [r1]"),
    (b"\x00\x00\xc1\xc5", "strbgt r0, [r1]"),
    (b"\x00\x00\xc1\xd5", "strble r0, [r1]"),
    (b"\x00\x00\xc1\xe5", "strbal r0, [r1]"),

    (b"\x04\x00\xc1\xe5", "strb r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\x05", "strbeq r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\x15", "strbne r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\x25", "strbcs r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\x35", "strbcc r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\x45", "strbmi r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\x55", "strbpl r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\x65", "strbvs r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\x75", "strbvc r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\x85", "strbhi r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\x95", "strbls r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\xa5", "strbge r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\xb5", "strblt r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\xc5", "strbgt r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\xd5", "strble r0, [r1, #0x4]"),
    (b"\x04\x00\xc1\xe5", "strbal r0, [r1, #0x4]"),

    (b"\x04\x00\x41\xe5", "strb r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\x05", "strbeq r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\x15", "strbne r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\x25", "strbcs r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\x35", "strbcc r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\x45", "strbmi r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\x55", "strbpl r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\x65", "strbvs r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\x75", "strbvc r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\x85", "strbhi r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\x95", "strbls r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\xa5", "strbge r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\xb5", "strblt r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\xc5", "strbgt r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\xd5", "strble r0, [r1, #-0x4]"),
    (b"\x04\x00\x41\xe5", "strbal r0, [r1, #-0x4]"),

    # STRB - Pre-indexed addressing ------------------------------------------ #
    (b"\x00\x00\xe1\xe5", "strb r0, [r1]!"),
    (b"\x00\x00\xe1\x05", "strbeq r0, [r1]!"),
    (b"\x00\x00\xe1\x15", "strbne r0, [r1]!"),
    (b"\x00\x00\xe1\x25", "strbcs r0, [r1]!"),
    (b"\x00\x00\xe1\x35", "strbcc r0, [r1]!"),
    (b"\x00\x00\xe1\x45", "strbmi r0, [r1]!"),
    (b"\x00\x00\xe1\x55", "strbpl r0, [r1]!"),
    (b"\x00\x00\xe1\x65", "strbvs r0, [r1]!"),
    (b"\x00\x00\xe1\x75", "strbvc r0, [r1]!"),
    (b"\x00\x00\xe1\x85", "strbhi r0, [r1]!"),
    (b"\x00\x00\xe1\x95", "strbls r0, [r1]!"),
    (b"\x00\x00\xe1\xa5", "strbge r0, [r1]!"),
    (b"\x00\x00\xe1\xb5", "strblt r0, [r1]!"),
    (b"\x00\x00\xe1\xc5", "strbgt r0, [r1]!"),
    (b"\x00\x00\xe1\xd5", "strble r0, [r1]!"),
    (b"\x00\x00\xe1\xe5", "strbal r0, [r1]!"),

    (b"\x04\x00\xe1\xe5", "strb r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\x05", "strbeq r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\x15", "strbne r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\x25", "strbcs r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\x35", "strbcc r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\x45", "strbmi r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\x55", "strbpl r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\x65", "strbvs r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\x75", "strbvc r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\x85", "strbhi r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\x95", "strbls r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\xa5", "strbge r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\xb5", "strblt r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\xc5", "strbgt r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\xd5", "strble r0, [r1, #0x4]!"),
    (b"\x04\x00\xe1\xe5", "strbal r0, [r1, #0x4]!"),

    (b"\x04\x00\x61\xe5", "strb r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\x05", "strbeq r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\x15", "strbne r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\x25", "strbcs r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\x35", "strbcc r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\x45", "strbmi r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\x55", "strbpl r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\x65", "strbvs r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\x75", "strbvc r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\x85", "strbhi r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\x95", "strbls r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\xa5", "strbge r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\xb5", "strblt r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\xc5", "strbgt r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\xd5", "strble r0, [r1, #-0x4]!"),
    (b"\x04\x00\x61\xe5", "strbal r0, [r1, #-0x4]!"),

    # STRB - Post-indexed addressing ----------------------------------------- #
    (b"\x04\x00\xc1\xe4", "strb r0, [r1], #0x4"),
    (b"\x04\x00\xc1\x04", "strbeq r0, [r1], #0x4"),
    (b"\x04\x00\xc1\x14", "strbne r0, [r1], #0x4"),
    (b"\x04\x00\xc1\x24", "strbcs r0, [r1], #0x4"),
    (b"\x04\x00\xc1\x34", "strbcc r0, [r1], #0x4"),
    (b"\x04\x00\xc1\x44", "strbmi r0, [r1], #0x4"),
    (b"\x04\x00\xc1\x54", "strbpl r0, [r1], #0x4"),
    (b"\x04\x00\xc1\x64", "strbvs r0, [r1], #0x4"),
    (b"\x04\x00\xc1\x74", "strbvc r0, [r1], #0x4"),
    (b"\x04\x00\xc1\x84", "strbhi r0, [r1], #0x4"),
    (b"\x04\x00\xc1\x94", "strbls r0, [r1], #0x4"),
    (b"\x04\x00\xc1\xa4", "strbge r0, [r1], #0x4"),
    (b"\x04\x00\xc1\xb4", "strblt r0, [r1], #0x4"),
    (b"\x04\x00\xc1\xc4", "strbgt r0, [r1], #0x4"),
    (b"\x04\x00\xc1\xd4", "strble r0, [r1], #0x4"),
    (b"\x04\x00\xc1\xe4", "strbal r0, [r1], #0x4"),

    (b"\x04\x00\x41\xe4", "strb r0, [r1], #-0x4"),
    (b"\x04\x00\x41\x04", "strbeq r0, [r1], #-0x4"),
    (b"\x04\x00\x41\x14", "strbne r0, [r1], #-0x4"),
    (b"\x04\x00\x41\x24", "strbcs r0, [r1], #-0x4"),
    (b"\x04\x00\x41\x34", "strbcc r0, [r1], #-0x4"),
    (b"\x04\x00\x41\x44", "strbmi r0, [r1], #-0x4"),
    (b"\x04\x00\x41\x54", "strbpl r0, [r1], #-0x4"),
    (b"\x04\x00\x41\x64", "strbvs r0, [r1], #-0x4"),
    (b"\x04\x00\x41\x74", "strbvc r0, [r1], #-0x4"),
    (b"\x04\x00\x41\x84", "strbhi r0, [r1], #-0x4"),
    (b"\x04\x00\x41\x94", "strbls r0, [r1], #-0x4"),
    (b"\x04\x00\x41\xa4", "strbge r0, [r1], #-0x4"),
    (b"\x04\x00\x41\xb4", "strblt r0, [r1], #-0x4"),
    (b"\x04\x00\x41\xc4", "strbgt r0, [r1], #-0x4"),
    (b"\x04\x00\x41\xd4", "strble r0, [r1], #-0x4"),
    (b"\x04\x00\x41\xe4", "strbal r0, [r1], #-0x4"),

    # TODO: Test with PC as source register.
]


def emu_with_unicorn(opcode, istate):
    # Initialize emulator in arm32 mode.
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM)

    # Map memory for this emulation.
    mu.mem_map(ADDR, SIZE)

    # Write machine code to be emulated to memory.
    index = 0
    for op, _ in CODE:
        mu.mem_write(ADDR+index, op)
        index += len(op)

    # Retrieve APSR register value.
    apsr = mu.reg_read(UC_ARM_REG_APSR)
    nzcv = istate['n'] << 31 | istate['z'] << 30 | istate['c'] << 29 | istate['v'] << 28

    mu.mem_write(STACK,                bytes(istate['stack']))
    mu.mem_write(HEAP,                 bytes(istate['heap']))
    mu.reg_write(UC_ARM_REG_R0,        istate['r0'])
    mu.reg_write(UC_ARM_REG_R1,        istate['r1'])
    mu.reg_write(UC_ARM_REG_R2,        istate['r2'])
    mu.reg_write(UC_ARM_REG_R3,        istate['r3'])
    mu.reg_write(UC_ARM_REG_R4,        istate['r4'])
    mu.reg_write(UC_ARM_REG_R5,        istate['r5'])
    mu.reg_write(UC_ARM_REG_R6,        istate['r6'])
    mu.reg_write(UC_ARM_REG_R7,        istate['r7'])
    mu.reg_write(UC_ARM_REG_R8,        istate['r8'])
    mu.reg_write(UC_ARM_REG_R9,        istate['r9'])
    mu.reg_write(UC_ARM_REG_R10,       istate['r10'])
    mu.reg_write(UC_ARM_REG_R11,       istate['r11'])
    mu.reg_write(UC_ARM_REG_R12,       istate['r12'])
    mu.reg_write(UC_ARM_REG_SP,        istate['sp'])
    mu.reg_write(UC_ARM_REG_R14,       istate['r14'])
    mu.reg_write(UC_ARM_REG_PC,        istate['pc'])
    mu.reg_write(UC_ARM_REG_APSR,      apsr & 0x0fffffff | nzcv)

    # Emulate opcode.
    # NOTE: The +4 and count=1 is a trick so UC updates PC.
    mu.emu_start(istate['pc'], istate['pc'] + len(opcode) + 4, count=1)

    ostate = {
        "stack": bytearray(mu.mem_read(STACK, 0x100)),
        "heap":  bytearray(mu.mem_read(HEAP, 0x100)),
        "r0":    mu.reg_read(UC_ARM_REG_R0),
        "r1":    mu.reg_read(UC_ARM_REG_R1),
        "r2":    mu.reg_read(UC_ARM_REG_R2),
        "r3":    mu.reg_read(UC_ARM_REG_R3),
        "r4":    mu.reg_read(UC_ARM_REG_R4),
        "r5":    mu.reg_read(UC_ARM_REG_R5),
        "r6":    mu.reg_read(UC_ARM_REG_R6),
        "r7":    mu.reg_read(UC_ARM_REG_R7),
        "r8":    mu.reg_read(UC_ARM_REG_R8),
        "r9":    mu.reg_read(UC_ARM_REG_R9),
        "r10":   mu.reg_read(UC_ARM_REG_R10),
        "r11":   mu.reg_read(UC_ARM_REG_R11),
        "r12":   mu.reg_read(UC_ARM_REG_R12),
        "sp":    mu.reg_read(UC_ARM_REG_SP),
        "r14":   mu.reg_read(UC_ARM_REG_R14),
        "pc":    mu.reg_read(UC_ARM_REG_PC),
        "n":   ((mu.reg_read(UC_ARM_REG_APSR) >> 31) & 1),
        "z":   ((mu.reg_read(UC_ARM_REG_APSR) >> 30) & 1),
        "c":   ((mu.reg_read(UC_ARM_REG_APSR) >> 29) & 1),
        "v":   ((mu.reg_read(UC_ARM_REG_APSR) >> 28) & 1),
    }
    return ostate


def emu_with_triton(opcode, istate):
    ctx = TritonContext()
    ctx.setArchitecture(ARCH.ARM32)

    inst = Instruction(opcode)
    inst.setAddress(istate['pc'])

    # Write machine code to be emulated to memory.
    index = 0
    for op, _ in CODE:
        ctx.setConcreteMemoryAreaValue(ADDR+index, op)
        index += len(op)

    ctx.setConcreteMemoryAreaValue(STACK,           bytes(istate['stack']))
    ctx.setConcreteMemoryAreaValue(HEAP,            bytes(istate['heap']))
    ctx.setConcreteRegisterValue(ctx.registers.r0,  istate['r0'])
    ctx.setConcreteRegisterValue(ctx.registers.r1,  istate['r1'])
    ctx.setConcreteRegisterValue(ctx.registers.r2,  istate['r2'])
    ctx.setConcreteRegisterValue(ctx.registers.r3,  istate['r3'])
    ctx.setConcreteRegisterValue(ctx.registers.r4,  istate['r4'])
    ctx.setConcreteRegisterValue(ctx.registers.r5,  istate['r5'])
    ctx.setConcreteRegisterValue(ctx.registers.r6,  istate['r6'])
    ctx.setConcreteRegisterValue(ctx.registers.r7,  istate['r7'])
    ctx.setConcreteRegisterValue(ctx.registers.r8,  istate['r8'])
    ctx.setConcreteRegisterValue(ctx.registers.r9,  istate['r9'])
    ctx.setConcreteRegisterValue(ctx.registers.r10, istate['r10'])
    ctx.setConcreteRegisterValue(ctx.registers.r11, istate['r11'])
    ctx.setConcreteRegisterValue(ctx.registers.r12, istate['r12'])
    ctx.setConcreteRegisterValue(ctx.registers.sp,  istate['sp'])
    ctx.setConcreteRegisterValue(ctx.registers.r14, istate['r14'])
    ctx.setConcreteRegisterValue(ctx.registers.pc,  istate['pc'])
    ctx.setConcreteRegisterValue(ctx.registers.n,   istate['n'])
    ctx.setConcreteRegisterValue(ctx.registers.z,   istate['z'])
    ctx.setConcreteRegisterValue(ctx.registers.c,   istate['c'])
    ctx.setConcreteRegisterValue(ctx.registers.v,   istate['v'])

    ctx.processing(inst)

    # print()
    # print(inst)
    # for x in inst.getSymbolicExpressions():
    #    print(x)
    # print()

    ostate = {
        "stack": bytearray(ctx.getConcreteMemoryAreaValue(STACK, 0x100)),
        "heap":  bytearray(ctx.getConcreteMemoryAreaValue(HEAP, 0x100)),
        "r0":    ctx.getSymbolicRegisterValue(ctx.registers.r0),
        "r1":    ctx.getSymbolicRegisterValue(ctx.registers.r1),
        "r2":    ctx.getSymbolicRegisterValue(ctx.registers.r2),
        "r3":    ctx.getSymbolicRegisterValue(ctx.registers.r3),
        "r4":    ctx.getSymbolicRegisterValue(ctx.registers.r4),
        "r5":    ctx.getSymbolicRegisterValue(ctx.registers.r5),
        "r6":    ctx.getSymbolicRegisterValue(ctx.registers.r6),
        "r7":    ctx.getSymbolicRegisterValue(ctx.registers.r7),
        "r8":    ctx.getSymbolicRegisterValue(ctx.registers.r8),
        "r9":    ctx.getSymbolicRegisterValue(ctx.registers.r9),
        "r10":   ctx.getSymbolicRegisterValue(ctx.registers.r10),
        "r11":   ctx.getSymbolicRegisterValue(ctx.registers.r11),
        "r12":   ctx.getSymbolicRegisterValue(ctx.registers.r12),
        "sp":    ctx.getSymbolicRegisterValue(ctx.registers.sp),
        "r14":   ctx.getSymbolicRegisterValue(ctx.registers.r14),
        "pc":    ctx.getSymbolicRegisterValue(ctx.registers.pc),
        "n":     ctx.getSymbolicRegisterValue(ctx.registers.n),
        "z":     ctx.getSymbolicRegisterValue(ctx.registers.z),
        "c":     ctx.getSymbolicRegisterValue(ctx.registers.c),
        "v":     ctx.getSymbolicRegisterValue(ctx.registers.v),
    }
    return ostate


def diff_state(state1, state2):
    for k, v in list(state1.items()):
        if (k == 'heap' or k == 'stack') and v != state2[k]:
            print('\t%s: (UC) != (TT)' %(k))
        elif not (k == 'heap' or k == 'stack') and v != state2[k]:
            print('\t%s: %#x (UC) != %#x (TT)' %(k, v, state2[k]))
    return


def print_state(istate, uc_ostate, tt_ostate):
    for k in sorted(istate.keys()):
        if k in ['stack', 'heap']:
            continue

        diff = "!=" if uc_ostate[k] != tt_ostate[k] else "=="

        print("{:>3s}: {:08x} | {:08x} {} {:08x}".format(k, istate[k], uc_ostate[k], diff, tt_ostate[k]))


def diff_heap(istate, uc_ostate, tt_ostate):
    print("IN|UC|TT")
    for a, b, c in zip(istate['heap'], uc_ostate['heap'], tt_ostate['heap']):
        if a != b or a != c:
            print("{:02x}|{:02x}|{:02x}".format(a, b, c), sep=" ")


def diff_stack(istate, uc_ostate, tt_ostate):
    print("IN|UC|TT")
    sp = istate["sp"]
    for a, b, c in zip(istate['stack'], uc_ostate['stack'], tt_ostate['stack']):
        if a != b or a != c:
            print("{:x}: {:02x}|{:02x}|{:02x}".format(sp, a, b, c), sep=" ")
        sp += 1


if __name__ == '__main__':
    # Initial state.
    state = {
        "stack": bytearray([255 - i for i in range(256)]),
        "heap":  bytearray([i for i in range(256)]),
        "r0":    0xdeadbeef,
        "r1":    HEAP + 10 * 4,
        "r2":    random.randint(0x0, 0xffffffff),
        "r3":    4,
        "r4":    4 << 1,                                    # NOTE: For testing: "ldrb r0, [r1, -r4, rrx]".
        "r5":    random.randint(0x0, 0xffffffff),
        "r6":    random.randint(0x0, 0xffffffff),
        "r7":    random.randint(0x0, 0xffffffff),
        "r8":    random.randint(0x0, 0xffffffff),
        "r9":    random.randint(0x0, 0xffffffff),
        "r10":   random.randint(0x0, 0xffffffff),
        "r11":   random.randint(0x0, 0xffffffff),
        "r12":   random.randint(0x0, 0xffffffff),
        "sp":    STACK,
        "r14":   random.randint(0x0, 0xffffffff),
        "pc":    ADDR,
        "n":     random.randint(0x0, 0x1),
        "z":     random.randint(0x0, 0x1),
        "c":     random.randint(0x0, 0x1),
        "v":     random.randint(0x0, 0x1),
    }

    # NOTE: This tests each instruction separately. Therefore, it keeps track of
    # PC and resets the initial state after testing each instruction.
    pc = ADDR
    for opcode, disassembly in CODE:
        try:
            state['pc'] = pc
            uc_state = emu_with_unicorn(opcode, state)
            tt_state = emu_with_triton(opcode, state)
            pc += len(opcode)
        except Exception as e:
            print('[KO] %s' %(disassembly))
            print('\t%s' %(e))
            sys.exit(-1)

        for a, b in zip(uc_state['heap'], tt_state['heap']):
            if a != b:
                print('[KO] %s (heap differs!)' %(disassembly))
                diff_heap(state, uc_state, tt_state)
                print_state(state, uc_state, tt_state)
                sys.exit(-1)

        for a, b in zip(uc_state['stack'], tt_state['stack']):
            if a != b:
                print('[KO] %s (stack differs!)' %(disassembly))
                diff_stack(state, uc_state, tt_state)
                print_state(state, uc_state, tt_state)
                sys.exit(-1)

        if uc_state != tt_state:
            print('[KO] %s' %(disassembly))
            diff_state(uc_state, tt_state)
            print_state(state, uc_state, tt_state)
            sys.exit(-1)

        print('[OK] %s' %(disassembly))

    sys.exit(0)
