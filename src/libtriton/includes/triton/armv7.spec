#pragma warning(disable:4067)

#if not (defined REG_SPEC || defined REG_SPEC_NO_CAPSTONE)
#error REG_SPEC have to be specified before including specs
#endif

/* REG_SPEC(UPPER_NAME, LOWER_NAME, ARMV7AR_UPPER, ARMV7AR_LOWER, ARMV7AR_PARENT, ARMV7M_UPPER, ARMV7M_LOWER, ARMV7M_PARENT, ARMV7M_AVAIL) */

/* GPR 32-bits. */

REG_SPEC(R0, r0, ARMV7, DWORD_SIZE_BIT-1, 0, R0, DWORD_SIZE_BIT-1, 0, R0, true)                             //!< r0
REG_SPEC(R1, r1, ARMV7, DWORD_SIZE_BIT-1, 0, R1, DWORD_SIZE_BIT-1, 0, R1, true)                             //!< r1
REG_SPEC(R2, r2, ARMV7, DWORD_SIZE_BIT-1, 0, R2, DWORD_SIZE_BIT-1, 0, R2, true)                             //!< r2
REG_SPEC(R3, r3, ARMV7, DWORD_SIZE_BIT-1, 0, R3, DWORD_SIZE_BIT-1, 0, R3, true)                             //!< r3
REG_SPEC(R4, r4, ARMV7, DWORD_SIZE_BIT-1, 0, R4, DWORD_SIZE_BIT-1, 0, R4, true)                             //!< r4
REG_SPEC(R5, r5, ARMV7, DWORD_SIZE_BIT-1, 0, R5, DWORD_SIZE_BIT-1, 0, R5, true)                             //!< r5
REG_SPEC(R6, r6, ARMV7, DWORD_SIZE_BIT-1, 0, R6, DWORD_SIZE_BIT-1, 0, R6, true)                             //!< r6
REG_SPEC(R7, r7, ARMV7, DWORD_SIZE_BIT-1, 0, R7, DWORD_SIZE_BIT-1, 0, R7, true)                             //!< r7
REG_SPEC(R8, r8, ARMV7, DWORD_SIZE_BIT-1, 0, R8, DWORD_SIZE_BIT-1, 0, R8, true)                             //!< r8
REG_SPEC(R9, r9, ARMV7, DWORD_SIZE_BIT-1, 0, R9, DWORD_SIZE_BIT-1, 0, R9, true)                             //!< r9
REG_SPEC(R10, r10, ARMV7, DWORD_SIZE_BIT-1, 0, R10, DWORD_SIZE_BIT-1, 0, R10, true)                         //!< r10
REG_SPEC(R11, r11, ARMV7, DWORD_SIZE_BIT-1, 0, R11, DWORD_SIZE_BIT-1, 0, R11, true)                         //!< r11
REG_SPEC(R12, r12, ARMV7, DWORD_SIZE_BIT-1, 0, R12, DWORD_SIZE_BIT-1, 0, R12, true)                         //!< r12
REG_SPEC(LR, lr, ARMV7, DWORD_SIZE_BIT-1, 0, LR, DWORD_SIZE_BIT-1, 0, LR, true)                             //!< lr
REG_SPEC(SP, sp, ARMV7, DWORD_SIZE_BIT-1, 0, SP, DWORD_SIZE_BIT-1, 0, SP, true)                             //!< sp
REG_SPEC(PC, pc, ARMV7, DWORD_SIZE_BIT-1, 0, PC, DWORD_SIZE_BIT-1, 0, PC, false)                            //!< pc
REG_SPEC(CSPR, cspr, ARMV7, DWORD_SIZE_BIT-1, 0, CSPR, DWORD_SIZE_BIT-1, 0, CSPR, false)                    //!< cpsr
REG_SPEC(R15, r15, ARMV7, DWORD_SIZE_BIT-1, 0, R15, DWORD_SIZE_BIT-1, 0, R15, true)                         //!< r15
REG_SPEC(XPSR, xpsr, ARMV7, DWORD_SIZE_BIT-1, 0, XPSR, DWORD_SIZE_BIT-1, 0, XPSR, true)                     //!< xpsr

#undef REG_SPEC
#undef REG_SPEC_NO_CAPSTONE

#pragma warning(default:4067)
