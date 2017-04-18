//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/x86Specifications.hpp>



/*! \page py_OPCODE_page OPCODE
    \brief [**python api**] All information about the OPCODE python namespace.

\tableofcontents

\section OPCODE_py_description Description
<hr>

According to the CPU architecture, the OPCODE namespace contains all kinds of opcodes.

\section OPCODE_py_api Python API - Items of the OPCODE namespace
<hr>

\subsection OPCODE_x86_py_api x86 and x86_64

- **OPCODE.INVALID**<br>
- **OPCODE.AAA**<br>
- **OPCODE.AAD**<br>
- **OPCODE.AAM**<br>
- **OPCODE.AAS**<br>
- **OPCODE.FABS**<br>
- **OPCODE.ADC**<br>
- **OPCODE.ADCX**<br>
- **OPCODE.ADD**<br>
- **OPCODE.ADDPD**<br>
- **OPCODE.ADDPS**<br>
- **OPCODE.ADDSD**<br>
- **OPCODE.ADDSS**<br>
- **OPCODE.ADDSUBPD**<br>
- **OPCODE.ADDSUBPS**<br>
- **OPCODE.FADD**<br>
- **OPCODE.FIADD**<br>
- **OPCODE.FADDP**<br>
- **OPCODE.ADOX**<br>
- **OPCODE.AESDECLAST**<br>
- **OPCODE.AESDEC**<br>
- **OPCODE.AESENCLAST**<br>
- **OPCODE.AESENC**<br>
- **OPCODE.AESIMC**<br>
- **OPCODE.AESKEYGENASSIST**<br>
- **OPCODE.AND**<br>
- **OPCODE.ANDN**<br>
- **OPCODE.ANDNPD**<br>
- **OPCODE.ANDNPS**<br>
- **OPCODE.ANDPD**<br>
- **OPCODE.ANDPS**<br>
- **OPCODE.ARPL**<br>
- **OPCODE.BEXTR**<br>
- **OPCODE.BLCFILL**<br>
- **OPCODE.BLCI**<br>
- **OPCODE.BLCIC**<br>
- **OPCODE.BLCMSK**<br>
- **OPCODE.BLCS**<br>
- **OPCODE.BLENDPD**<br>
- **OPCODE.BLENDPS**<br>
- **OPCODE.BLENDVPD**<br>
- **OPCODE.BLENDVPS**<br>
- **OPCODE.BLSFILL**<br>
- **OPCODE.BLSI**<br>
- **OPCODE.BLSIC**<br>
- **OPCODE.BLSMSK**<br>
- **OPCODE.BLSR**<br>
- **OPCODE.BOUND**<br>
- **OPCODE.BSF**<br>
- **OPCODE.BSR**<br>
- **OPCODE.BSWAP**<br>
- **OPCODE.BT**<br>
- **OPCODE.BTC**<br>
- **OPCODE.BTR**<br>
- **OPCODE.BTS**<br>
- **OPCODE.BZHI**<br>
- **OPCODE.CALL**<br>
- **OPCODE.CBW**<br>
- **OPCODE.CDQ**<br>
- **OPCODE.CDQE**<br>
- **OPCODE.FCHS**<br>
- **OPCODE.CLAC**<br>
- **OPCODE.CLC**<br>
- **OPCODE.CLD**<br>
- **OPCODE.CLFLUSH**<br>
- **OPCODE.CLGI**<br>
- **OPCODE.CLI**<br>
- **OPCODE.CLTS**<br>
- **OPCODE.CMC**<br>
- **OPCODE.CMOVA**<br>
- **OPCODE.CMOVAE**<br>
- **OPCODE.CMOVB**<br>
- **OPCODE.CMOVBE**<br>
- **OPCODE.FCMOVBE**<br>
- **OPCODE.FCMOVB**<br>
- **OPCODE.CMOVE**<br>
- **OPCODE.FCMOVE**<br>
- **OPCODE.CMOVG**<br>
- **OPCODE.CMOVGE**<br>
- **OPCODE.CMOVL**<br>
- **OPCODE.CMOVLE**<br>
- **OPCODE.FCMOVNBE**<br>
- **OPCODE.FCMOVNB**<br>
- **OPCODE.CMOVNE**<br>
- **OPCODE.FCMOVNE**<br>
- **OPCODE.CMOVNO**<br>
- **OPCODE.CMOVNP**<br>
- **OPCODE.FCMOVNU**<br>
- **OPCODE.CMOVNS**<br>
- **OPCODE.CMOVO**<br>
- **OPCODE.CMOVP**<br>
- **OPCODE.FCMOVU**<br>
- **OPCODE.CMOVS**<br>
- **OPCODE.CMP**<br>
- **OPCODE.CMPPD**<br>
- **OPCODE.CMPPS**<br>
- **OPCODE.CMPSB**<br>
- **OPCODE.CMPSD**<br>
- **OPCODE.CMPSQ**<br>
- **OPCODE.CMPSS**<br>
- **OPCODE.CMPSW**<br>
- **OPCODE.CMPXCHG16B**<br>
- **OPCODE.CMPXCHG**<br>
- **OPCODE.CMPXCHG8B**<br>
- **OPCODE.COMISD**<br>
- **OPCODE.COMISS**<br>
- **OPCODE.FCOMP**<br>
- **OPCODE.FCOMPI**<br>
- **OPCODE.FCOMI**<br>
- **OPCODE.FCOM**<br>
- **OPCODE.FCOS**<br>
- **OPCODE.CPUID**<br>
- **OPCODE.CQO**<br>
- **OPCODE.CRC32**<br>
- **OPCODE.CVTDQ2PD**<br>
- **OPCODE.CVTDQ2PS**<br>
- **OPCODE.CVTPD2DQ**<br>
- **OPCODE.CVTPD2PS**<br>
- **OPCODE.CVTPS2DQ**<br>
- **OPCODE.CVTPS2PD**<br>
- **OPCODE.CVTSD2SI**<br>
- **OPCODE.CVTSD2SS**<br>
- **OPCODE.CVTSI2SD**<br>
- **OPCODE.CVTSI2SS**<br>
- **OPCODE.CVTSS2SD**<br>
- **OPCODE.CVTSS2SI**<br>
- **OPCODE.CVTTPD2DQ**<br>
- **OPCODE.CVTTPS2DQ**<br>
- **OPCODE.CVTTSD2SI**<br>
- **OPCODE.CVTTSS2SI**<br>
- **OPCODE.CWD**<br>
- **OPCODE.CWDE**<br>
- **OPCODE.DAA**<br>
- **OPCODE.DAS**<br>
- **OPCODE.DATA16**<br>
- **OPCODE.DEC**<br>
- **OPCODE.DIV**<br>
- **OPCODE.DIVPD**<br>
- **OPCODE.DIVPS**<br>
- **OPCODE.FDIVR**<br>
- **OPCODE.FIDIVR**<br>
- **OPCODE.FDIVRP**<br>
- **OPCODE.DIVSD**<br>
- **OPCODE.DIVSS**<br>
- **OPCODE.FDIV**<br>
- **OPCODE.FIDIV**<br>
- **OPCODE.FDIVP**<br>
- **OPCODE.DPPD**<br>
- **OPCODE.DPPS**<br>
- **OPCODE.RET**<br>
- **OPCODE.ENCLS**<br>
- **OPCODE.ENCLU**<br>
- **OPCODE.ENTER**<br>
- **OPCODE.EXTRACTPS**<br>
- **OPCODE.EXTRQ**<br>
- **OPCODE.F2XM1**<br>
- **OPCODE.LCALL**<br>
- **OPCODE.LJMP**<br>
- **OPCODE.FBLD**<br>
- **OPCODE.FBSTP**<br>
- **OPCODE.FCOMPP**<br>
- **OPCODE.FDECSTP**<br>
- **OPCODE.FEMMS**<br>
- **OPCODE.FFREE**<br>
- **OPCODE.FICOM**<br>
- **OPCODE.FICOMP**<br>
- **OPCODE.FINCSTP**<br>
- **OPCODE.FLDCW**<br>
- **OPCODE.FLDENV**<br>
- **OPCODE.FLDL2E**<br>
- **OPCODE.FLDL2T**<br>
- **OPCODE.FLDLG2**<br>
- **OPCODE.FLDLN2**<br>
- **OPCODE.FLDPI**<br>
- **OPCODE.FNCLEX**<br>
- **OPCODE.FNINIT**<br>
- **OPCODE.FNOP**<br>
- **OPCODE.FNSTCW**<br>
- **OPCODE.FNSTSW**<br>
- **OPCODE.FPATAN**<br>
- **OPCODE.FPREM**<br>
- **OPCODE.FPREM1**<br>
- **OPCODE.FPTAN**<br>
- **OPCODE.FRNDINT**<br>
- **OPCODE.FRSTOR**<br>
- **OPCODE.FNSAVE**<br>
- **OPCODE.FSCALE**<br>
- **OPCODE.FSETPM**<br>
- **OPCODE.FSINCOS**<br>
- **OPCODE.FNSTENV**<br>
- **OPCODE.FXAM**<br>
- **OPCODE.FXRSTOR**<br>
- **OPCODE.FXRSTOR64**<br>
- **OPCODE.FXSAVE**<br>
- **OPCODE.FXSAVE64**<br>
- **OPCODE.FXTRACT**<br>
- **OPCODE.FYL2X**<br>
- **OPCODE.FYL2XP1**<br>
- **OPCODE.MOVAPD**<br>
- **OPCODE.MOVAPS**<br>
- **OPCODE.ORPD**<br>
- **OPCODE.ORPS**<br>
- **OPCODE.VMOVAPD**<br>
- **OPCODE.VMOVAPS**<br>
- **OPCODE.XORPD**<br>
- **OPCODE.XORPS**<br>
- **OPCODE.GETSEC**<br>
- **OPCODE.HADDPD**<br>
- **OPCODE.HADDPS**<br>
- **OPCODE.HLT**<br>
- **OPCODE.HSUBPD**<br>
- **OPCODE.HSUBPS**<br>
- **OPCODE.IDIV**<br>
- **OPCODE.FILD**<br>
- **OPCODE.IMUL**<br>
- **OPCODE.IN**<br>
- **OPCODE.INC**<br>
- **OPCODE.INSB**<br>
- **OPCODE.INSERTPS**<br>
- **OPCODE.INSERTQ**<br>
- **OPCODE.INSD**<br>
- **OPCODE.INSW**<br>
- **OPCODE.INT**<br>
- **OPCODE.INT1**<br>
- **OPCODE.INT3**<br>
- **OPCODE.INTO**<br>
- **OPCODE.INVD**<br>
- **OPCODE.INVEPT**<br>
- **OPCODE.INVLPG**<br>
- **OPCODE.INVLPGA**<br>
- **OPCODE.INVPCID**<br>
- **OPCODE.INVVPID**<br>
- **OPCODE.IRET**<br>
- **OPCODE.IRETD**<br>
- **OPCODE.IRETQ**<br>
- **OPCODE.FISTTP**<br>
- **OPCODE.FIST**<br>
- **OPCODE.FISTP**<br>
- **OPCODE.UCOMISD**<br>
- **OPCODE.UCOMISS**<br>
- **OPCODE.VCMP**<br>
- **OPCODE.VCOMISD**<br>
- **OPCODE.VCOMISS**<br>
- **OPCODE.VCVTSD2SS**<br>
- **OPCODE.VCVTSI2SD**<br>
- **OPCODE.VCVTSI2SS**<br>
- **OPCODE.VCVTSS2SD**<br>
- **OPCODE.VCVTTSD2SI**<br>
- **OPCODE.VCVTTSD2USI**<br>
- **OPCODE.VCVTTSS2SI**<br>
- **OPCODE.VCVTTSS2USI**<br>
- **OPCODE.VCVTUSI2SD**<br>
- **OPCODE.VCVTUSI2SS**<br>
- **OPCODE.VUCOMISD**<br>
- **OPCODE.VUCOMISS**<br>
- **OPCODE.JAE**<br>
- **OPCODE.JA**<br>
- **OPCODE.JBE**<br>
- **OPCODE.JB**<br>
- **OPCODE.JCXZ**<br>
- **OPCODE.JECXZ**<br>
- **OPCODE.JE**<br>
- **OPCODE.JGE**<br>
- **OPCODE.JG**<br>
- **OPCODE.JLE**<br>
- **OPCODE.JL**<br>
- **OPCODE.JMP**<br>
- **OPCODE.JNE**<br>
- **OPCODE.JNO**<br>
- **OPCODE.JNP**<br>
- **OPCODE.JNS**<br>
- **OPCODE.JO**<br>
- **OPCODE.JP**<br>
- **OPCODE.JRCXZ**<br>
- **OPCODE.JS**<br>
- **OPCODE.KANDB**<br>
- **OPCODE.KANDD**<br>
- **OPCODE.KANDNB**<br>
- **OPCODE.KANDND**<br>
- **OPCODE.KANDNQ**<br>
- **OPCODE.KANDNW**<br>
- **OPCODE.KANDQ**<br>
- **OPCODE.KANDW**<br>
- **OPCODE.KMOVB**<br>
- **OPCODE.KMOVD**<br>
- **OPCODE.KMOVQ**<br>
- **OPCODE.KMOVW**<br>
- **OPCODE.KNOTB**<br>
- **OPCODE.KNOTD**<br>
- **OPCODE.KNOTQ**<br>
- **OPCODE.KNOTW**<br>
- **OPCODE.KORB**<br>
- **OPCODE.KORD**<br>
- **OPCODE.KORQ**<br>
- **OPCODE.KORTESTW**<br>
- **OPCODE.KORW**<br>
- **OPCODE.KSHIFTLW**<br>
- **OPCODE.KSHIFTRW**<br>
- **OPCODE.KUNPCKBW**<br>
- **OPCODE.KXNORB**<br>
- **OPCODE.KXNORD**<br>
- **OPCODE.KXNORQ**<br>
- **OPCODE.KXNORW**<br>
- **OPCODE.KXORB**<br>
- **OPCODE.KXORD**<br>
- **OPCODE.KXORQ**<br>
- **OPCODE.KXORW**<br>
- **OPCODE.LAHF**<br>
- **OPCODE.LAR**<br>
- **OPCODE.LDDQU**<br>
- **OPCODE.LDMXCSR**<br>
- **OPCODE.LDS**<br>
- **OPCODE.FLDZ**<br>
- **OPCODE.FLD1**<br>
- **OPCODE.FLD**<br>
- **OPCODE.LEA**<br>
- **OPCODE.LEAVE**<br>
- **OPCODE.LES**<br>
- **OPCODE.LFENCE**<br>
- **OPCODE.LFS**<br>
- **OPCODE.LGDT**<br>
- **OPCODE.LGS**<br>
- **OPCODE.LIDT**<br>
- **OPCODE.LLDT**<br>
- **OPCODE.LMSW**<br>
- **OPCODE.OR**<br>
- **OPCODE.SUB**<br>
- **OPCODE.XOR**<br>
- **OPCODE.LODSB**<br>
- **OPCODE.LODSD**<br>
- **OPCODE.LODSQ**<br>
- **OPCODE.LODSW**<br>
- **OPCODE.LOOP**<br>
- **OPCODE.LOOPE**<br>
- **OPCODE.LOOPNE**<br>
- **OPCODE.RETF**<br>
- **OPCODE.RETFQ**<br>
- **OPCODE.LSL**<br>
- **OPCODE.LSS**<br>
- **OPCODE.LTR**<br>
- **OPCODE.XADD**<br>
- **OPCODE.LZCNT**<br>
- **OPCODE.MASKMOVDQU**<br>
- **OPCODE.MAXPD**<br>
- **OPCODE.MAXPS**<br>
- **OPCODE.MAXSD**<br>
- **OPCODE.MAXSS**<br>
- **OPCODE.MFENCE**<br>
- **OPCODE.MINPD**<br>
- **OPCODE.MINPS**<br>
- **OPCODE.MINSD**<br>
- **OPCODE.MINSS**<br>
- **OPCODE.CVTPD2PI**<br>
- **OPCODE.CVTPI2PD**<br>
- **OPCODE.CVTPI2PS**<br>
- **OPCODE.CVTPS2PI**<br>
- **OPCODE.CVTTPD2PI**<br>
- **OPCODE.CVTTPS2PI**<br>
- **OPCODE.EMMS**<br>
- **OPCODE.MASKMOVQ**<br>
- **OPCODE.MOVD**<br>
- **OPCODE.MOVDQ2Q**<br>
- **OPCODE.MOVNTQ**<br>
- **OPCODE.MOVQ2DQ**<br>
- **OPCODE.MOVQ**<br>
- **OPCODE.PABSB**<br>
- **OPCODE.PABSD**<br>
- **OPCODE.PABSW**<br>
- **OPCODE.PACKSSDW**<br>
- **OPCODE.PACKSSWB**<br>
- **OPCODE.PACKUSWB**<br>
- **OPCODE.PADDB**<br>
- **OPCODE.PADDD**<br>
- **OPCODE.PADDQ**<br>
- **OPCODE.PADDSB**<br>
- **OPCODE.PADDSW**<br>
- **OPCODE.PADDUSB**<br>
- **OPCODE.PADDUSW**<br>
- **OPCODE.PADDW**<br>
- **OPCODE.PALIGNR**<br>
- **OPCODE.PANDN**<br>
- **OPCODE.PAND**<br>
- **OPCODE.PAVGB**<br>
- **OPCODE.PAVGW**<br>
- **OPCODE.PCMPEQB**<br>
- **OPCODE.PCMPEQD**<br>
- **OPCODE.PCMPEQW**<br>
- **OPCODE.PCMPGTB**<br>
- **OPCODE.PCMPGTD**<br>
- **OPCODE.PCMPGTW**<br>
- **OPCODE.PEXTRW**<br>
- **OPCODE.PHADDSW**<br>
- **OPCODE.PHADDW**<br>
- **OPCODE.PHADDD**<br>
- **OPCODE.PHSUBD**<br>
- **OPCODE.PHSUBSW**<br>
- **OPCODE.PHSUBW**<br>
- **OPCODE.PINSRW**<br>
- **OPCODE.PMADDUBSW**<br>
- **OPCODE.PMADDWD**<br>
- **OPCODE.PMAXSW**<br>
- **OPCODE.PMAXUB**<br>
- **OPCODE.PMINSW**<br>
- **OPCODE.PMINUB**<br>
- **OPCODE.PMOVMSKB**<br>
- **OPCODE.PMULHRSW**<br>
- **OPCODE.PMULHUW**<br>
- **OPCODE.PMULHW**<br>
- **OPCODE.PMULLW**<br>
- **OPCODE.PMULUDQ**<br>
- **OPCODE.POR**<br>
- **OPCODE.PSADBW**<br>
- **OPCODE.PSHUFB**<br>
- **OPCODE.PSHUFW**<br>
- **OPCODE.PSIGNB**<br>
- **OPCODE.PSIGND**<br>
- **OPCODE.PSIGNW**<br>
- **OPCODE.PSLLD**<br>
- **OPCODE.PSLLQ**<br>
- **OPCODE.PSLLW**<br>
- **OPCODE.PSRAD**<br>
- **OPCODE.PSRAW**<br>
- **OPCODE.PSRLD**<br>
- **OPCODE.PSRLQ**<br>
- **OPCODE.PSRLW**<br>
- **OPCODE.PSUBB**<br>
- **OPCODE.PSUBD**<br>
- **OPCODE.PSUBQ**<br>
- **OPCODE.PSUBSB**<br>
- **OPCODE.PSUBSW**<br>
- **OPCODE.PSUBUSB**<br>
- **OPCODE.PSUBUSW**<br>
- **OPCODE.PSUBW**<br>
- **OPCODE.PUNPCKHBW**<br>
- **OPCODE.PUNPCKHDQ**<br>
- **OPCODE.PUNPCKHWD**<br>
- **OPCODE.PUNPCKLBW**<br>
- **OPCODE.PUNPCKLDQ**<br>
- **OPCODE.PUNPCKLWD**<br>
- **OPCODE.PXOR**<br>
- **OPCODE.MONITOR**<br>
- **OPCODE.MONTMUL**<br>
- **OPCODE.MOV**<br>
- **OPCODE.MOVABS**<br>
- **OPCODE.MOVBE**<br>
- **OPCODE.MOVDDUP**<br>
- **OPCODE.MOVDQA**<br>
- **OPCODE.MOVDQU**<br>
- **OPCODE.MOVHLPS**<br>
- **OPCODE.MOVHPD**<br>
- **OPCODE.MOVHPS**<br>
- **OPCODE.MOVLHPS**<br>
- **OPCODE.MOVLPD**<br>
- **OPCODE.MOVLPS**<br>
- **OPCODE.MOVMSKPD**<br>
- **OPCODE.MOVMSKPS**<br>
- **OPCODE.MOVNTDQA**<br>
- **OPCODE.MOVNTDQ**<br>
- **OPCODE.MOVNTI**<br>
- **OPCODE.MOVNTPD**<br>
- **OPCODE.MOVNTPS**<br>
- **OPCODE.MOVNTSD**<br>
- **OPCODE.MOVNTSS**<br>
- **OPCODE.MOVSB**<br>
- **OPCODE.MOVSD**<br>
- **OPCODE.MOVSHDUP**<br>
- **OPCODE.MOVSLDUP**<br>
- **OPCODE.MOVSQ**<br>
- **OPCODE.MOVSS**<br>
- **OPCODE.MOVSW**<br>
- **OPCODE.MOVSX**<br>
- **OPCODE.MOVSXD**<br>
- **OPCODE.MOVUPD**<br>
- **OPCODE.MOVUPS**<br>
- **OPCODE.MOVZX**<br>
- **OPCODE.MPSADBW**<br>
- **OPCODE.MUL**<br>
- **OPCODE.MULPD**<br>
- **OPCODE.MULPS**<br>
- **OPCODE.MULSD**<br>
- **OPCODE.MULSS**<br>
- **OPCODE.MULX**<br>
- **OPCODE.FMUL**<br>
- **OPCODE.FIMUL**<br>
- **OPCODE.FMULP**<br>
- **OPCODE.MWAIT**<br>
- **OPCODE.NEG**<br>
- **OPCODE.NOP**<br>
- **OPCODE.NOT**<br>
- **OPCODE.OUT**<br>
- **OPCODE.OUTSB**<br>
- **OPCODE.OUTSD**<br>
- **OPCODE.OUTSW**<br>
- **OPCODE.PACKUSDW**<br>
- **OPCODE.PAUSE**<br>
- **OPCODE.PAVGUSB**<br>
- **OPCODE.PBLENDVB**<br>
- **OPCODE.PBLENDW**<br>
- **OPCODE.PCLMULQDQ**<br>
- **OPCODE.PCMPEQQ**<br>
- **OPCODE.PCMPESTRI**<br>
- **OPCODE.PCMPESTRM**<br>
- **OPCODE.PCMPGTQ**<br>
- **OPCODE.PCMPISTRI**<br>
- **OPCODE.PCMPISTRM**<br>
- **OPCODE.PDEP**<br>
- **OPCODE.PEXT**<br>
- **OPCODE.PEXTRB**<br>
- **OPCODE.PEXTRD**<br>
- **OPCODE.PEXTRQ**<br>
- **OPCODE.PF2ID**<br>
- **OPCODE.PF2IW**<br>
- **OPCODE.PFACC**<br>
- **OPCODE.PFADD**<br>
- **OPCODE.PFCMPEQ**<br>
- **OPCODE.PFCMPGE**<br>
- **OPCODE.PFCMPGT**<br>
- **OPCODE.PFMAX**<br>
- **OPCODE.PFMIN**<br>
- **OPCODE.PFMUL**<br>
- **OPCODE.PFNACC**<br>
- **OPCODE.PFPNACC**<br>
- **OPCODE.PFRCPIT1**<br>
- **OPCODE.PFRCPIT2**<br>
- **OPCODE.PFRCP**<br>
- **OPCODE.PFRSQIT1**<br>
- **OPCODE.PFRSQRT**<br>
- **OPCODE.PFSUBR**<br>
- **OPCODE.PFSUB**<br>
- **OPCODE.PHMINPOSUW**<br>
- **OPCODE.PI2FD**<br>
- **OPCODE.PI2FW**<br>
- **OPCODE.PINSRB**<br>
- **OPCODE.PINSRD**<br>
- **OPCODE.PINSRQ**<br>
- **OPCODE.PMAXSB**<br>
- **OPCODE.PMAXSD**<br>
- **OPCODE.PMAXUD**<br>
- **OPCODE.PMAXUW**<br>
- **OPCODE.PMINSB**<br>
- **OPCODE.PMINSD**<br>
- **OPCODE.PMINUD**<br>
- **OPCODE.PMINUW**<br>
- **OPCODE.PMOVSXBD**<br>
- **OPCODE.PMOVSXBQ**<br>
- **OPCODE.PMOVSXBW**<br>
- **OPCODE.PMOVSXDQ**<br>
- **OPCODE.PMOVSXWD**<br>
- **OPCODE.PMOVSXWQ**<br>
- **OPCODE.PMOVZXBD**<br>
- **OPCODE.PMOVZXBQ**<br>
- **OPCODE.PMOVZXBW**<br>
- **OPCODE.PMOVZXDQ**<br>
- **OPCODE.PMOVZXWD**<br>
- **OPCODE.PMOVZXWQ**<br>
- **OPCODE.PMULDQ**<br>
- **OPCODE.PMULHRW**<br>
- **OPCODE.PMULLD**<br>
- **OPCODE.POP**<br>
- **OPCODE.POPAW**<br>
- **OPCODE.POPAL**<br>
- **OPCODE.POPCNT**<br>
- **OPCODE.POPF**<br>
- **OPCODE.POPFD**<br>
- **OPCODE.POPFQ**<br>
- **OPCODE.PREFETCH**<br>
- **OPCODE.PREFETCHNTA**<br>
- **OPCODE.PREFETCHT0**<br>
- **OPCODE.PREFETCHT1**<br>
- **OPCODE.PREFETCHT2**<br>
- **OPCODE.PREFETCHW**<br>
- **OPCODE.PSHUFD**<br>
- **OPCODE.PSHUFHW**<br>
- **OPCODE.PSHUFLW**<br>
- **OPCODE.PSLLDQ**<br>
- **OPCODE.PSRLDQ**<br>
- **OPCODE.PSWAPD**<br>
- **OPCODE.PTEST**<br>
- **OPCODE.PUNPCKHQDQ**<br>
- **OPCODE.PUNPCKLQDQ**<br>
- **OPCODE.PUSH**<br>
- **OPCODE.PUSHAW**<br>
- **OPCODE.PUSHAL**<br>
- **OPCODE.PUSHF**<br>
- **OPCODE.PUSHFD**<br>
- **OPCODE.PUSHFQ**<br>
- **OPCODE.RCL**<br>
- **OPCODE.RCPPS**<br>
- **OPCODE.RCPSS**<br>
- **OPCODE.RCR**<br>
- **OPCODE.RDFSBASE**<br>
- **OPCODE.RDGSBASE**<br>
- **OPCODE.RDMSR**<br>
- **OPCODE.RDPMC**<br>
- **OPCODE.RDRAND**<br>
- **OPCODE.RDSEED**<br>
- **OPCODE.RDTSC**<br>
- **OPCODE.RDTSCP**<br>
- **OPCODE.ROL**<br>
- **OPCODE.ROR**<br>
- **OPCODE.RORX**<br>
- **OPCODE.ROUNDPD**<br>
- **OPCODE.ROUNDPS**<br>
- **OPCODE.ROUNDSD**<br>
- **OPCODE.ROUNDSS**<br>
- **OPCODE.RSM**<br>
- **OPCODE.RSQRTPS**<br>
- **OPCODE.RSQRTSS**<br>
- **OPCODE.SAHF**<br>
- **OPCODE.SAL**<br>
- **OPCODE.SALC**<br>
- **OPCODE.SAR**<br>
- **OPCODE.SARX**<br>
- **OPCODE.SBB**<br>
- **OPCODE.SCASB**<br>
- **OPCODE.SCASD**<br>
- **OPCODE.SCASQ**<br>
- **OPCODE.SCASW**<br>
- **OPCODE.SETAE**<br>
- **OPCODE.SETA**<br>
- **OPCODE.SETBE**<br>
- **OPCODE.SETB**<br>
- **OPCODE.SETE**<br>
- **OPCODE.SETGE**<br>
- **OPCODE.SETG**<br>
- **OPCODE.SETLE**<br>
- **OPCODE.SETL**<br>
- **OPCODE.SETNE**<br>
- **OPCODE.SETNO**<br>
- **OPCODE.SETNP**<br>
- **OPCODE.SETNS**<br>
- **OPCODE.SETO**<br>
- **OPCODE.SETP**<br>
- **OPCODE.SETS**<br>
- **OPCODE.SFENCE**<br>
- **OPCODE.SGDT**<br>
- **OPCODE.SHA1MSG1**<br>
- **OPCODE.SHA1MSG2**<br>
- **OPCODE.SHA1NEXTE**<br>
- **OPCODE.SHA1RNDS4**<br>
- **OPCODE.SHA256MSG1**<br>
- **OPCODE.SHA256MSG2**<br>
- **OPCODE.SHA256RNDS2**<br>
- **OPCODE.SHL**<br>
- **OPCODE.SHLD**<br>
- **OPCODE.SHLX**<br>
- **OPCODE.SHR**<br>
- **OPCODE.SHRD**<br>
- **OPCODE.SHRX**<br>
- **OPCODE.SHUFPD**<br>
- **OPCODE.SHUFPS**<br>
- **OPCODE.SIDT**<br>
- **OPCODE.FSIN**<br>
- **OPCODE.SKINIT**<br>
- **OPCODE.SLDT**<br>
- **OPCODE.SMSW**<br>
- **OPCODE.SQRTPD**<br>
- **OPCODE.SQRTPS**<br>
- **OPCODE.SQRTSD**<br>
- **OPCODE.SQRTSS**<br>
- **OPCODE.FSQRT**<br>
- **OPCODE.STAC**<br>
- **OPCODE.STC**<br>
- **OPCODE.STD**<br>
- **OPCODE.STGI**<br>
- **OPCODE.STI**<br>
- **OPCODE.STMXCSR**<br>
- **OPCODE.STOSB**<br>
- **OPCODE.STOSD**<br>
- **OPCODE.STOSQ**<br>
- **OPCODE.STOSW**<br>
- **OPCODE.STR**<br>
- **OPCODE.FST**<br>
- **OPCODE.FSTP**<br>
- **OPCODE.FSTPNCE**<br>
- **OPCODE.SUBPD**<br>
- **OPCODE.SUBPS**<br>
- **OPCODE.FSUBR**<br>
- **OPCODE.FISUBR**<br>
- **OPCODE.FSUBRP**<br>
- **OPCODE.SUBSD**<br>
- **OPCODE.SUBSS**<br>
- **OPCODE.FSUB**<br>
- **OPCODE.FISUB**<br>
- **OPCODE.FSUBP**<br>
- **OPCODE.SWAPGS**<br>
- **OPCODE.SYSCALL**<br>
- **OPCODE.SYSENTER**<br>
- **OPCODE.SYSEXIT**<br>
- **OPCODE.SYSRET**<br>
- **OPCODE.T1MSKC**<br>
- **OPCODE.TEST**<br>
- **OPCODE.UD2**<br>
- **OPCODE.FTST**<br>
- **OPCODE.TZCNT**<br>
- **OPCODE.TZMSK**<br>
- **OPCODE.FUCOMPI**<br>
- **OPCODE.FUCOMI**<br>
- **OPCODE.FUCOMPP**<br>
- **OPCODE.FUCOMP**<br>
- **OPCODE.FUCOM**<br>
- **OPCODE.UD2B**<br>
- **OPCODE.UNPCKHPD**<br>
- **OPCODE.UNPCKHPS**<br>
- **OPCODE.UNPCKLPD**<br>
- **OPCODE.UNPCKLPS**<br>
- **OPCODE.VADDPD**<br>
- **OPCODE.VADDPS**<br>
- **OPCODE.VADDSD**<br>
- **OPCODE.VADDSS**<br>
- **OPCODE.VADDSUBPD**<br>
- **OPCODE.VADDSUBPS**<br>
- **OPCODE.VAESDECLAST**<br>
- **OPCODE.VAESDEC**<br>
- **OPCODE.VAESENCLAST**<br>
- **OPCODE.VAESENC**<br>
- **OPCODE.VAESIMC**<br>
- **OPCODE.VAESKEYGENASSIST**<br>
- **OPCODE.VALIGND**<br>
- **OPCODE.VALIGNQ**<br>
- **OPCODE.VANDNPD**<br>
- **OPCODE.VANDNPS**<br>
- **OPCODE.VANDPD**<br>
- **OPCODE.VANDPS**<br>
- **OPCODE.VBLENDMPD**<br>
- **OPCODE.VBLENDMPS**<br>
- **OPCODE.VBLENDPD**<br>
- **OPCODE.VBLENDPS**<br>
- **OPCODE.VBLENDVPD**<br>
- **OPCODE.VBLENDVPS**<br>
- **OPCODE.VBROADCASTF128**<br>
- **OPCODE.VBROADCASTI128**<br>
- **OPCODE.VBROADCASTI32X4**<br>
- **OPCODE.VBROADCASTI64X4**<br>
- **OPCODE.VBROADCASTSD**<br>
- **OPCODE.VBROADCASTSS**<br>
- **OPCODE.VCMPPD**<br>
- **OPCODE.VCMPPS**<br>
- **OPCODE.VCMPSD**<br>
- **OPCODE.VCMPSS**<br>
- **OPCODE.VCVTDQ2PD**<br>
- **OPCODE.VCVTDQ2PS**<br>
- **OPCODE.VCVTPD2DQX**<br>
- **OPCODE.VCVTPD2DQ**<br>
- **OPCODE.VCVTPD2PSX**<br>
- **OPCODE.VCVTPD2PS**<br>
- **OPCODE.VCVTPD2UDQ**<br>
- **OPCODE.VCVTPH2PS**<br>
- **OPCODE.VCVTPS2DQ**<br>
- **OPCODE.VCVTPS2PD**<br>
- **OPCODE.VCVTPS2PH**<br>
- **OPCODE.VCVTPS2UDQ**<br>
- **OPCODE.VCVTSD2SI**<br>
- **OPCODE.VCVTSD2USI**<br>
- **OPCODE.VCVTSS2SI**<br>
- **OPCODE.VCVTSS2USI**<br>
- **OPCODE.VCVTTPD2DQX**<br>
- **OPCODE.VCVTTPD2DQ**<br>
- **OPCODE.VCVTTPD2UDQ**<br>
- **OPCODE.VCVTTPS2DQ**<br>
- **OPCODE.VCVTTPS2UDQ**<br>
- **OPCODE.VCVTUDQ2PD**<br>
- **OPCODE.VCVTUDQ2PS**<br>
- **OPCODE.VDIVPD**<br>
- **OPCODE.VDIVPS**<br>
- **OPCODE.VDIVSD**<br>
- **OPCODE.VDIVSS**<br>
- **OPCODE.VDPPD**<br>
- **OPCODE.VDPPS**<br>
- **OPCODE.VERR**<br>
- **OPCODE.VERW**<br>
- **OPCODE.VEXTRACTF128**<br>
- **OPCODE.VEXTRACTF32X4**<br>
- **OPCODE.VEXTRACTF64X4**<br>
- **OPCODE.VEXTRACTI128**<br>
- **OPCODE.VEXTRACTI32X4**<br>
- **OPCODE.VEXTRACTI64X4**<br>
- **OPCODE.VEXTRACTPS**<br>
- **OPCODE.VFMADD132PD**<br>
- **OPCODE.VFMADD132PS**<br>
- **OPCODE.VFMADD213PD**<br>
- **OPCODE.VFMADD213PS**<br>
- **OPCODE.VFMADDPD**<br>
- **OPCODE.VFMADD231PD**<br>
- **OPCODE.VFMADDPS**<br>
- **OPCODE.VFMADD231PS**<br>
- **OPCODE.VFMADDSD**<br>
- **OPCODE.VFMADD213SD**<br>
- **OPCODE.VFMADD132SD**<br>
- **OPCODE.VFMADD231SD**<br>
- **OPCODE.VFMADDSS**<br>
- **OPCODE.VFMADD213SS**<br>
- **OPCODE.VFMADD132SS**<br>
- **OPCODE.VFMADD231SS**<br>
- **OPCODE.VFMADDSUB132PD**<br>
- **OPCODE.VFMADDSUB132PS**<br>
- **OPCODE.VFMADDSUB213PD**<br>
- **OPCODE.VFMADDSUB213PS**<br>
- **OPCODE.VFMADDSUBPD**<br>
- **OPCODE.VFMADDSUB231PD**<br>
- **OPCODE.VFMADDSUBPS**<br>
- **OPCODE.VFMADDSUB231PS**<br>
- **OPCODE.VFMSUB132PD**<br>
- **OPCODE.VFMSUB132PS**<br>
- **OPCODE.VFMSUB213PD**<br>
- **OPCODE.VFMSUB213PS**<br>
- **OPCODE.VFMSUBADD132PD**<br>
- **OPCODE.VFMSUBADD132PS**<br>
- **OPCODE.VFMSUBADD213PD**<br>
- **OPCODE.VFMSUBADD213PS**<br>
- **OPCODE.VFMSUBADDPD**<br>
- **OPCODE.VFMSUBADD231PD**<br>
- **OPCODE.VFMSUBADDPS**<br>
- **OPCODE.VFMSUBADD231PS**<br>
- **OPCODE.VFMSUBPD**<br>
- **OPCODE.VFMSUB231PD**<br>
- **OPCODE.VFMSUBPS**<br>
- **OPCODE.VFMSUB231PS**<br>
- **OPCODE.VFMSUBSD**<br>
- **OPCODE.VFMSUB213SD**<br>
- **OPCODE.VFMSUB132SD**<br>
- **OPCODE.VFMSUB231SD**<br>
- **OPCODE.VFMSUBSS**<br>
- **OPCODE.VFMSUB213SS**<br>
- **OPCODE.VFMSUB132SS**<br>
- **OPCODE.VFMSUB231SS**<br>
- **OPCODE.VFNMADD132PD**<br>
- **OPCODE.VFNMADD132PS**<br>
- **OPCODE.VFNMADD213PD**<br>
- **OPCODE.VFNMADD213PS**<br>
- **OPCODE.VFNMADDPD**<br>
- **OPCODE.VFNMADD231PD**<br>
- **OPCODE.VFNMADDPS**<br>
- **OPCODE.VFNMADD231PS**<br>
- **OPCODE.VFNMADDSD**<br>
- **OPCODE.VFNMADD213SD**<br>
- **OPCODE.VFNMADD132SD**<br>
- **OPCODE.VFNMADD231SD**<br>
- **OPCODE.VFNMADDSS**<br>
- **OPCODE.VFNMADD213SS**<br>
- **OPCODE.VFNMADD132SS**<br>
- **OPCODE.VFNMADD231SS**<br>
- **OPCODE.VFNMSUB132PD**<br>
- **OPCODE.VFNMSUB132PS**<br>
- **OPCODE.VFNMSUB213PD**<br>
- **OPCODE.VFNMSUB213PS**<br>
- **OPCODE.VFNMSUBPD**<br>
- **OPCODE.VFNMSUB231PD**<br>
- **OPCODE.VFNMSUBPS**<br>
- **OPCODE.VFNMSUB231PS**<br>
- **OPCODE.VFNMSUBSD**<br>
- **OPCODE.VFNMSUB213SD**<br>
- **OPCODE.VFNMSUB132SD**<br>
- **OPCODE.VFNMSUB231SD**<br>
- **OPCODE.VFNMSUBSS**<br>
- **OPCODE.VFNMSUB213SS**<br>
- **OPCODE.VFNMSUB132SS**<br>
- **OPCODE.VFNMSUB231SS**<br>
- **OPCODE.VFRCZPD**<br>
- **OPCODE.VFRCZPS**<br>
- **OPCODE.VFRCZSD**<br>
- **OPCODE.VFRCZSS**<br>
- **OPCODE.VORPD**<br>
- **OPCODE.VORPS**<br>
- **OPCODE.VXORPD**<br>
- **OPCODE.VXORPS**<br>
- **OPCODE.VGATHERDPD**<br>
- **OPCODE.VGATHERDPS**<br>
- **OPCODE.VGATHERPF0DPD**<br>
- **OPCODE.VGATHERPF0DPS**<br>
- **OPCODE.VGATHERPF0QPD**<br>
- **OPCODE.VGATHERPF0QPS**<br>
- **OPCODE.VGATHERPF1DPD**<br>
- **OPCODE.VGATHERPF1DPS**<br>
- **OPCODE.VGATHERPF1QPD**<br>
- **OPCODE.VGATHERPF1QPS**<br>
- **OPCODE.VGATHERQPD**<br>
- **OPCODE.VGATHERQPS**<br>
- **OPCODE.VHADDPD**<br>
- **OPCODE.VHADDPS**<br>
- **OPCODE.VHSUBPD**<br>
- **OPCODE.VHSUBPS**<br>
- **OPCODE.VINSERTF128**<br>
- **OPCODE.VINSERTF32X4**<br>
- **OPCODE.VINSERTF64X4**<br>
- **OPCODE.VINSERTI128**<br>
- **OPCODE.VINSERTI32X4**<br>
- **OPCODE.VINSERTI64X4**<br>
- **OPCODE.VINSERTPS**<br>
- **OPCODE.VLDDQU**<br>
- **OPCODE.VLDMXCSR**<br>
- **OPCODE.VMASKMOVDQU**<br>
- **OPCODE.VMASKMOVPD**<br>
- **OPCODE.VMASKMOVPS**<br>
- **OPCODE.VMAXPD**<br>
- **OPCODE.VMAXPS**<br>
- **OPCODE.VMAXSD**<br>
- **OPCODE.VMAXSS**<br>
- **OPCODE.VMCALL**<br>
- **OPCODE.VMCLEAR**<br>
- **OPCODE.VMFUNC**<br>
- **OPCODE.VMINPD**<br>
- **OPCODE.VMINPS**<br>
- **OPCODE.VMINSD**<br>
- **OPCODE.VMINSS**<br>
- **OPCODE.VMLAUNCH**<br>
- **OPCODE.VMLOAD**<br>
- **OPCODE.VMMCALL**<br>
- **OPCODE.VMOVQ**<br>
- **OPCODE.VMOVDDUP**<br>
- **OPCODE.VMOVD**<br>
- **OPCODE.VMOVDQA32**<br>
- **OPCODE.VMOVDQA64**<br>
- **OPCODE.VMOVDQA**<br>
- **OPCODE.VMOVDQU16**<br>
- **OPCODE.VMOVDQU32**<br>
- **OPCODE.VMOVDQU64**<br>
- **OPCODE.VMOVDQU8**<br>
- **OPCODE.VMOVDQU**<br>
- **OPCODE.VMOVHLPS**<br>
- **OPCODE.VMOVHPD**<br>
- **OPCODE.VMOVHPS**<br>
- **OPCODE.VMOVLHPS**<br>
- **OPCODE.VMOVLPD**<br>
- **OPCODE.VMOVLPS**<br>
- **OPCODE.VMOVMSKPD**<br>
- **OPCODE.VMOVMSKPS**<br>
- **OPCODE.VMOVNTDQA**<br>
- **OPCODE.VMOVNTDQ**<br>
- **OPCODE.VMOVNTPD**<br>
- **OPCODE.VMOVNTPS**<br>
- **OPCODE.VMOVSD**<br>
- **OPCODE.VMOVSHDUP**<br>
- **OPCODE.VMOVSLDUP**<br>
- **OPCODE.VMOVSS**<br>
- **OPCODE.VMOVUPD**<br>
- **OPCODE.VMOVUPS**<br>
- **OPCODE.VMPSADBW**<br>
- **OPCODE.VMPTRLD**<br>
- **OPCODE.VMPTRST**<br>
- **OPCODE.VMREAD**<br>
- **OPCODE.VMRESUME**<br>
- **OPCODE.VMRUN**<br>
- **OPCODE.VMSAVE**<br>
- **OPCODE.VMULPD**<br>
- **OPCODE.VMULPS**<br>
- **OPCODE.VMULSD**<br>
- **OPCODE.VMULSS**<br>
- **OPCODE.VMWRITE**<br>
- **OPCODE.VMXOFF**<br>
- **OPCODE.VMXON**<br>
- **OPCODE.VPABSB**<br>
- **OPCODE.VPABSD**<br>
- **OPCODE.VPABSQ**<br>
- **OPCODE.VPABSW**<br>
- **OPCODE.VPACKSSDW**<br>
- **OPCODE.VPACKSSWB**<br>
- **OPCODE.VPACKUSDW**<br>
- **OPCODE.VPACKUSWB**<br>
- **OPCODE.VPADDB**<br>
- **OPCODE.VPADDD**<br>
- **OPCODE.VPADDQ**<br>
- **OPCODE.VPADDSB**<br>
- **OPCODE.VPADDSW**<br>
- **OPCODE.VPADDUSB**<br>
- **OPCODE.VPADDUSW**<br>
- **OPCODE.VPADDW**<br>
- **OPCODE.VPALIGNR**<br>
- **OPCODE.VPANDD**<br>
- **OPCODE.VPANDND**<br>
- **OPCODE.VPANDNQ**<br>
- **OPCODE.VPANDN**<br>
- **OPCODE.VPANDQ**<br>
- **OPCODE.VPAND**<br>
- **OPCODE.VPAVGB**<br>
- **OPCODE.VPAVGW**<br>
- **OPCODE.VPBLENDD**<br>
- **OPCODE.VPBLENDMD**<br>
- **OPCODE.VPBLENDMQ**<br>
- **OPCODE.VPBLENDVB**<br>
- **OPCODE.VPBLENDW**<br>
- **OPCODE.VPBROADCASTB**<br>
- **OPCODE.VPBROADCASTD**<br>
- **OPCODE.VPBROADCASTMB2Q**<br>
- **OPCODE.VPBROADCASTMW2D**<br>
- **OPCODE.VPBROADCASTQ**<br>
- **OPCODE.VPBROADCASTW**<br>
- **OPCODE.VPCLMULQDQ**<br>
- **OPCODE.VPCMOV**<br>
- **OPCODE.VPCMP**<br>
- **OPCODE.VPCMPD**<br>
- **OPCODE.VPCMPEQB**<br>
- **OPCODE.VPCMPEQD**<br>
- **OPCODE.VPCMPEQQ**<br>
- **OPCODE.VPCMPEQW**<br>
- **OPCODE.VPCMPESTRI**<br>
- **OPCODE.VPCMPESTRM**<br>
- **OPCODE.VPCMPGTB**<br>
- **OPCODE.VPCMPGTD**<br>
- **OPCODE.VPCMPGTQ**<br>
- **OPCODE.VPCMPGTW**<br>
- **OPCODE.VPCMPISTRI**<br>
- **OPCODE.VPCMPISTRM**<br>
- **OPCODE.VPCMPQ**<br>
- **OPCODE.VPCMPUD**<br>
- **OPCODE.VPCMPUQ**<br>
- **OPCODE.VPCOMB**<br>
- **OPCODE.VPCOMD**<br>
- **OPCODE.VPCOMQ**<br>
- **OPCODE.VPCOMUB**<br>
- **OPCODE.VPCOMUD**<br>
- **OPCODE.VPCOMUQ**<br>
- **OPCODE.VPCOMUW**<br>
- **OPCODE.VPCOMW**<br>
- **OPCODE.VPCONFLICTD**<br>
- **OPCODE.VPCONFLICTQ**<br>
- **OPCODE.VPERM2F128**<br>
- **OPCODE.VPERM2I128**<br>
- **OPCODE.VPERMD**<br>
- **OPCODE.VPERMI2D**<br>
- **OPCODE.VPERMI2PD**<br>
- **OPCODE.VPERMI2PS**<br>
- **OPCODE.VPERMI2Q**<br>
- **OPCODE.VPERMIL2PD**<br>
- **OPCODE.VPERMIL2PS**<br>
- **OPCODE.VPERMILPD**<br>
- **OPCODE.VPERMILPS**<br>
- **OPCODE.VPERMPD**<br>
- **OPCODE.VPERMPS**<br>
- **OPCODE.VPERMQ**<br>
- **OPCODE.VPERMT2D**<br>
- **OPCODE.VPERMT2PD**<br>
- **OPCODE.VPERMT2PS**<br>
- **OPCODE.VPERMT2Q**<br>
- **OPCODE.VPEXTRB**<br>
- **OPCODE.VPEXTRD**<br>
- **OPCODE.VPEXTRQ**<br>
- **OPCODE.VPEXTRW**<br>
- **OPCODE.VPGATHERDD**<br>
- **OPCODE.VPGATHERDQ**<br>
- **OPCODE.VPGATHERQD**<br>
- **OPCODE.VPGATHERQQ**<br>
- **OPCODE.VPHADDBD**<br>
- **OPCODE.VPHADDBQ**<br>
- **OPCODE.VPHADDBW**<br>
- **OPCODE.VPHADDDQ**<br>
- **OPCODE.VPHADDD**<br>
- **OPCODE.VPHADDSW**<br>
- **OPCODE.VPHADDUBD**<br>
- **OPCODE.VPHADDUBQ**<br>
- **OPCODE.VPHADDUBW**<br>
- **OPCODE.VPHADDUDQ**<br>
- **OPCODE.VPHADDUWD**<br>
- **OPCODE.VPHADDUWQ**<br>
- **OPCODE.VPHADDWD**<br>
- **OPCODE.VPHADDWQ**<br>
- **OPCODE.VPHADDW**<br>
- **OPCODE.VPHMINPOSUW**<br>
- **OPCODE.VPHSUBBW**<br>
- **OPCODE.VPHSUBDQ**<br>
- **OPCODE.VPHSUBD**<br>
- **OPCODE.VPHSUBSW**<br>
- **OPCODE.VPHSUBWD**<br>
- **OPCODE.VPHSUBW**<br>
- **OPCODE.VPINSRB**<br>
- **OPCODE.VPINSRD**<br>
- **OPCODE.VPINSRQ**<br>
- **OPCODE.VPINSRW**<br>
- **OPCODE.VPLZCNTD**<br>
- **OPCODE.VPLZCNTQ**<br>
- **OPCODE.VPMACSDD**<br>
- **OPCODE.VPMACSDQH**<br>
- **OPCODE.VPMACSDQL**<br>
- **OPCODE.VPMACSSDD**<br>
- **OPCODE.VPMACSSDQH**<br>
- **OPCODE.VPMACSSDQL**<br>
- **OPCODE.VPMACSSWD**<br>
- **OPCODE.VPMACSSWW**<br>
- **OPCODE.VPMACSWD**<br>
- **OPCODE.VPMACSWW**<br>
- **OPCODE.VPMADCSSWD**<br>
- **OPCODE.VPMADCSWD**<br>
- **OPCODE.VPMADDUBSW**<br>
- **OPCODE.VPMADDWD**<br>
- **OPCODE.VPMASKMOVD**<br>
- **OPCODE.VPMASKMOVQ**<br>
- **OPCODE.VPMAXSB**<br>
- **OPCODE.VPMAXSD**<br>
- **OPCODE.VPMAXSQ**<br>
- **OPCODE.VPMAXSW**<br>
- **OPCODE.VPMAXUB**<br>
- **OPCODE.VPMAXUD**<br>
- **OPCODE.VPMAXUQ**<br>
- **OPCODE.VPMAXUW**<br>
- **OPCODE.VPMINSB**<br>
- **OPCODE.VPMINSD**<br>
- **OPCODE.VPMINSQ**<br>
- **OPCODE.VPMINSW**<br>
- **OPCODE.VPMINUB**<br>
- **OPCODE.VPMINUD**<br>
- **OPCODE.VPMINUQ**<br>
- **OPCODE.VPMINUW**<br>
- **OPCODE.VPMOVDB**<br>
- **OPCODE.VPMOVDW**<br>
- **OPCODE.VPMOVMSKB**<br>
- **OPCODE.VPMOVQB**<br>
- **OPCODE.VPMOVQD**<br>
- **OPCODE.VPMOVQW**<br>
- **OPCODE.VPMOVSDB**<br>
- **OPCODE.VPMOVSDW**<br>
- **OPCODE.VPMOVSQB**<br>
- **OPCODE.VPMOVSQD**<br>
- **OPCODE.VPMOVSQW**<br>
- **OPCODE.VPMOVSXBD**<br>
- **OPCODE.VPMOVSXBQ**<br>
- **OPCODE.VPMOVSXBW**<br>
- **OPCODE.VPMOVSXDQ**<br>
- **OPCODE.VPMOVSXWD**<br>
- **OPCODE.VPMOVSXWQ**<br>
- **OPCODE.VPMOVUSDB**<br>
- **OPCODE.VPMOVUSDW**<br>
- **OPCODE.VPMOVUSQB**<br>
- **OPCODE.VPMOVUSQD**<br>
- **OPCODE.VPMOVUSQW**<br>
- **OPCODE.VPMOVZXBD**<br>
- **OPCODE.VPMOVZXBQ**<br>
- **OPCODE.VPMOVZXBW**<br>
- **OPCODE.VPMOVZXDQ**<br>
- **OPCODE.VPMOVZXWD**<br>
- **OPCODE.VPMOVZXWQ**<br>
- **OPCODE.VPMULDQ**<br>
- **OPCODE.VPMULHRSW**<br>
- **OPCODE.VPMULHUW**<br>
- **OPCODE.VPMULHW**<br>
- **OPCODE.VPMULLD**<br>
- **OPCODE.VPMULLW**<br>
- **OPCODE.VPMULUDQ**<br>
- **OPCODE.VPORD**<br>
- **OPCODE.VPORQ**<br>
- **OPCODE.VPOR**<br>
- **OPCODE.VPPERM**<br>
- **OPCODE.VPROTB**<br>
- **OPCODE.VPROTD**<br>
- **OPCODE.VPROTQ**<br>
- **OPCODE.VPROTW**<br>
- **OPCODE.VPSADBW**<br>
- **OPCODE.VPSCATTERDD**<br>
- **OPCODE.VPSCATTERDQ**<br>
- **OPCODE.VPSCATTERQD**<br>
- **OPCODE.VPSCATTERQQ**<br>
- **OPCODE.VPSHAB**<br>
- **OPCODE.VPSHAD**<br>
- **OPCODE.VPSHAQ**<br>
- **OPCODE.VPSHAW**<br>
- **OPCODE.VPSHLB**<br>
- **OPCODE.VPSHLD**<br>
- **OPCODE.VPSHLQ**<br>
- **OPCODE.VPSHLW**<br>
- **OPCODE.VPSHUFB**<br>
- **OPCODE.VPSHUFD**<br>
- **OPCODE.VPSHUFHW**<br>
- **OPCODE.VPSHUFLW**<br>
- **OPCODE.VPSIGNB**<br>
- **OPCODE.VPSIGND**<br>
- **OPCODE.VPSIGNW**<br>
- **OPCODE.VPSLLDQ**<br>
- **OPCODE.VPSLLD**<br>
- **OPCODE.VPSLLQ**<br>
- **OPCODE.VPSLLVD**<br>
- **OPCODE.VPSLLVQ**<br>
- **OPCODE.VPSLLW**<br>
- **OPCODE.VPSRAD**<br>
- **OPCODE.VPSRAQ**<br>
- **OPCODE.VPSRAVD**<br>
- **OPCODE.VPSRAVQ**<br>
- **OPCODE.VPSRAW**<br>
- **OPCODE.VPSRLDQ**<br>
- **OPCODE.VPSRLD**<br>
- **OPCODE.VPSRLQ**<br>
- **OPCODE.VPSRLVD**<br>
- **OPCODE.VPSRLVQ**<br>
- **OPCODE.VPSRLW**<br>
- **OPCODE.VPSUBB**<br>
- **OPCODE.VPSUBD**<br>
- **OPCODE.VPSUBQ**<br>
- **OPCODE.VPSUBSB**<br>
- **OPCODE.VPSUBSW**<br>
- **OPCODE.VPSUBUSB**<br>
- **OPCODE.VPSUBUSW**<br>
- **OPCODE.VPSUBW**<br>
- **OPCODE.VPTESTMD**<br>
- **OPCODE.VPTESTMQ**<br>
- **OPCODE.VPTESTNMD**<br>
- **OPCODE.VPTESTNMQ**<br>
- **OPCODE.VPTEST**<br>
- **OPCODE.VPUNPCKHBW**<br>
- **OPCODE.VPUNPCKHDQ**<br>
- **OPCODE.VPUNPCKHQDQ**<br>
- **OPCODE.VPUNPCKHWD**<br>
- **OPCODE.VPUNPCKLBW**<br>
- **OPCODE.VPUNPCKLDQ**<br>
- **OPCODE.VPUNPCKLQDQ**<br>
- **OPCODE.VPUNPCKLWD**<br>
- **OPCODE.VPXORD**<br>
- **OPCODE.VPXORQ**<br>
- **OPCODE.VPXOR**<br>
- **OPCODE.VRCP14PD**<br>
- **OPCODE.VRCP14PS**<br>
- **OPCODE.VRCP14SD**<br>
- **OPCODE.VRCP14SS**<br>
- **OPCODE.VRCP28PD**<br>
- **OPCODE.VRCP28PS**<br>
- **OPCODE.VRCP28SD**<br>
- **OPCODE.VRCP28SS**<br>
- **OPCODE.VRCPPS**<br>
- **OPCODE.VRCPSS**<br>
- **OPCODE.VRNDSCALEPD**<br>
- **OPCODE.VRNDSCALEPS**<br>
- **OPCODE.VRNDSCALESD**<br>
- **OPCODE.VRNDSCALESS**<br>
- **OPCODE.VROUNDPD**<br>
- **OPCODE.VROUNDPS**<br>
- **OPCODE.VROUNDSD**<br>
- **OPCODE.VROUNDSS**<br>
- **OPCODE.VRSQRT14PD**<br>
- **OPCODE.VRSQRT14PS**<br>
- **OPCODE.VRSQRT14SD**<br>
- **OPCODE.VRSQRT14SS**<br>
- **OPCODE.VRSQRT28PD**<br>
- **OPCODE.VRSQRT28PS**<br>
- **OPCODE.VRSQRT28SD**<br>
- **OPCODE.VRSQRT28SS**<br>
- **OPCODE.VRSQRTPS**<br>
- **OPCODE.VRSQRTSS**<br>
- **OPCODE.VSCATTERDPD**<br>
- **OPCODE.VSCATTERDPS**<br>
- **OPCODE.VSCATTERPF0DPD**<br>
- **OPCODE.VSCATTERPF0DPS**<br>
- **OPCODE.VSCATTERPF0QPD**<br>
- **OPCODE.VSCATTERPF0QPS**<br>
- **OPCODE.VSCATTERPF1DPD**<br>
- **OPCODE.VSCATTERPF1DPS**<br>
- **OPCODE.VSCATTERPF1QPD**<br>
- **OPCODE.VSCATTERPF1QPS**<br>
- **OPCODE.VSCATTERQPD**<br>
- **OPCODE.VSCATTERQPS**<br>
- **OPCODE.VSHUFPD**<br>
- **OPCODE.VSHUFPS**<br>
- **OPCODE.VSQRTPD**<br>
- **OPCODE.VSQRTPS**<br>
- **OPCODE.VSQRTSD**<br>
- **OPCODE.VSQRTSS**<br>
- **OPCODE.VSTMXCSR**<br>
- **OPCODE.VSUBPD**<br>
- **OPCODE.VSUBPS**<br>
- **OPCODE.VSUBSD**<br>
- **OPCODE.VSUBSS**<br>
- **OPCODE.VTESTPD**<br>
- **OPCODE.VTESTPS**<br>
- **OPCODE.VUNPCKHPD**<br>
- **OPCODE.VUNPCKHPS**<br>
- **OPCODE.VUNPCKLPD**<br>
- **OPCODE.VUNPCKLPS**<br>
- **OPCODE.VZEROALL**<br>
- **OPCODE.VZEROUPPER**<br>
- **OPCODE.WAIT**<br>
- **OPCODE.WBINVD**<br>
- **OPCODE.WRFSBASE**<br>
- **OPCODE.WRGSBASE**<br>
- **OPCODE.WRMSR**<br>
- **OPCODE.XABORT**<br>
- **OPCODE.XACQUIRE**<br>
- **OPCODE.XBEGIN**<br>
- **OPCODE.XCHG**<br>
- **OPCODE.FXCH**<br>
- **OPCODE.XCRYPTCBC**<br>
- **OPCODE.XCRYPTCFB**<br>
- **OPCODE.XCRYPTCTR**<br>
- **OPCODE.XCRYPTECB**<br>
- **OPCODE.XCRYPTOFB**<br>
- **OPCODE.XEND**<br>
- **OPCODE.XGETBV**<br>
- **OPCODE.XLATB**<br>
- **OPCODE.XRELEASE**<br>
- **OPCODE.XRSTOR**<br>
- **OPCODE.XRSTOR64**<br>
- **OPCODE.XSAVE**<br>
- **OPCODE.XSAVE64**<br>
- **OPCODE.XSAVEOPT**<br>
- **OPCODE.XSAVEOPT64**<br>
- **OPCODE.XSETBV**<br>
- **OPCODE.XSHA1**<br>
- **OPCODE.XSHA256**<br>
- **OPCODE.XSTORE**<br>
- **OPCODE.XTEST**<br>

*/


namespace triton {
  namespace bindings {
    namespace python {

      void initX86OpcodesNamespace(PyObject* opcodesDict) {
        PyDict_Clear(opcodesDict);

        PyDict_SetItemString(opcodesDict, "INVALID", PyLong_FromUint32(triton::arch::x86::ID_INST_INVALID));
        PyDict_SetItemString(opcodesDict, "AAA", PyLong_FromUint32(triton::arch::x86::ID_INS_AAA));
        PyDict_SetItemString(opcodesDict, "AAD", PyLong_FromUint32(triton::arch::x86::ID_INS_AAD));
        PyDict_SetItemString(opcodesDict, "AAM", PyLong_FromUint32(triton::arch::x86::ID_INS_AAM));
        PyDict_SetItemString(opcodesDict, "AAS", PyLong_FromUint32(triton::arch::x86::ID_INS_AAS));
        PyDict_SetItemString(opcodesDict, "FABS", PyLong_FromUint32(triton::arch::x86::ID_INS_FABS));
        PyDict_SetItemString(opcodesDict, "ADC", PyLong_FromUint32(triton::arch::x86::ID_INS_ADC));
        PyDict_SetItemString(opcodesDict, "ADCX", PyLong_FromUint32(triton::arch::x86::ID_INS_ADCX));
        PyDict_SetItemString(opcodesDict, "ADD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADD));
        PyDict_SetItemString(opcodesDict, "ADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDPD));
        PyDict_SetItemString(opcodesDict, "ADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDPS));
        PyDict_SetItemString(opcodesDict, "ADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSD));
        PyDict_SetItemString(opcodesDict, "ADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSS));
        PyDict_SetItemString(opcodesDict, "ADDSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSUBPD));
        PyDict_SetItemString(opcodesDict, "ADDSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSUBPS));
        PyDict_SetItemString(opcodesDict, "FADD", PyLong_FromUint32(triton::arch::x86::ID_INS_FADD));
        PyDict_SetItemString(opcodesDict, "FIADD", PyLong_FromUint32(triton::arch::x86::ID_INS_FIADD));
        PyDict_SetItemString(opcodesDict, "FADDP", PyLong_FromUint32(triton::arch::x86::ID_INS_FADDP));
        PyDict_SetItemString(opcodesDict, "ADOX", PyLong_FromUint32(triton::arch::x86::ID_INS_ADOX));
        PyDict_SetItemString(opcodesDict, "AESDECLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_AESDECLAST));
        PyDict_SetItemString(opcodesDict, "AESDEC", PyLong_FromUint32(triton::arch::x86::ID_INS_AESDEC));
        PyDict_SetItemString(opcodesDict, "AESENCLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_AESENCLAST));
        PyDict_SetItemString(opcodesDict, "AESENC", PyLong_FromUint32(triton::arch::x86::ID_INS_AESENC));
        PyDict_SetItemString(opcodesDict, "AESIMC", PyLong_FromUint32(triton::arch::x86::ID_INS_AESIMC));
        PyDict_SetItemString(opcodesDict, "AESKEYGENASSIST", PyLong_FromUint32(triton::arch::x86::ID_INS_AESKEYGENASSIST));
        PyDict_SetItemString(opcodesDict, "AND", PyLong_FromUint32(triton::arch::x86::ID_INS_AND));
        PyDict_SetItemString(opcodesDict, "ANDN", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDN));
        PyDict_SetItemString(opcodesDict, "ANDNPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDNPD));
        PyDict_SetItemString(opcodesDict, "ANDNPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDNPS));
        PyDict_SetItemString(opcodesDict, "ANDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDPD));
        PyDict_SetItemString(opcodesDict, "ANDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDPS));
        PyDict_SetItemString(opcodesDict, "ARPL", PyLong_FromUint32(triton::arch::x86::ID_INS_ARPL));
        PyDict_SetItemString(opcodesDict, "BEXTR", PyLong_FromUint32(triton::arch::x86::ID_INS_BEXTR));
        PyDict_SetItemString(opcodesDict, "BLCFILL", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCFILL));
        PyDict_SetItemString(opcodesDict, "BLCI", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCI));
        PyDict_SetItemString(opcodesDict, "BLCIC", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCIC));
        PyDict_SetItemString(opcodesDict, "BLCMSK", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCMSK));
        PyDict_SetItemString(opcodesDict, "BLCS", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCS));
        PyDict_SetItemString(opcodesDict, "BLENDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDPD));
        PyDict_SetItemString(opcodesDict, "BLENDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDPS));
        PyDict_SetItemString(opcodesDict, "BLENDVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDVPD));
        PyDict_SetItemString(opcodesDict, "BLENDVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDVPS));
        PyDict_SetItemString(opcodesDict, "BLSFILL", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSFILL));
        PyDict_SetItemString(opcodesDict, "BLSI", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSI));
        PyDict_SetItemString(opcodesDict, "BLSIC", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSIC));
        PyDict_SetItemString(opcodesDict, "BLSMSK", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSMSK));
        PyDict_SetItemString(opcodesDict, "BLSR", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSR));
        PyDict_SetItemString(opcodesDict, "BOUND", PyLong_FromUint32(triton::arch::x86::ID_INS_BOUND));
        PyDict_SetItemString(opcodesDict, "BSF", PyLong_FromUint32(triton::arch::x86::ID_INS_BSF));
        PyDict_SetItemString(opcodesDict, "BSR", PyLong_FromUint32(triton::arch::x86::ID_INS_BSR));
        PyDict_SetItemString(opcodesDict, "BSWAP", PyLong_FromUint32(triton::arch::x86::ID_INS_BSWAP));
        PyDict_SetItemString(opcodesDict, "BT", PyLong_FromUint32(triton::arch::x86::ID_INS_BT));
        PyDict_SetItemString(opcodesDict, "BTC", PyLong_FromUint32(triton::arch::x86::ID_INS_BTC));
        PyDict_SetItemString(opcodesDict, "BTR", PyLong_FromUint32(triton::arch::x86::ID_INS_BTR));
        PyDict_SetItemString(opcodesDict, "BTS", PyLong_FromUint32(triton::arch::x86::ID_INS_BTS));
        PyDict_SetItemString(opcodesDict, "BZHI", PyLong_FromUint32(triton::arch::x86::ID_INS_BZHI));
        PyDict_SetItemString(opcodesDict, "CALL", PyLong_FromUint32(triton::arch::x86::ID_INS_CALL));
        PyDict_SetItemString(opcodesDict, "CBW", PyLong_FromUint32(triton::arch::x86::ID_INS_CBW));
        PyDict_SetItemString(opcodesDict, "CDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CDQ));
        PyDict_SetItemString(opcodesDict, "CDQE", PyLong_FromUint32(triton::arch::x86::ID_INS_CDQE));
        PyDict_SetItemString(opcodesDict, "FCHS", PyLong_FromUint32(triton::arch::x86::ID_INS_FCHS));
        PyDict_SetItemString(opcodesDict, "CLAC", PyLong_FromUint32(triton::arch::x86::ID_INS_CLAC));
        PyDict_SetItemString(opcodesDict, "CLC", PyLong_FromUint32(triton::arch::x86::ID_INS_CLC));
        PyDict_SetItemString(opcodesDict, "CLD", PyLong_FromUint32(triton::arch::x86::ID_INS_CLD));
        PyDict_SetItemString(opcodesDict, "CLFLUSH", PyLong_FromUint32(triton::arch::x86::ID_INS_CLFLUSH));
        PyDict_SetItemString(opcodesDict, "CLGI", PyLong_FromUint32(triton::arch::x86::ID_INS_CLGI));
        PyDict_SetItemString(opcodesDict, "CLI", PyLong_FromUint32(triton::arch::x86::ID_INS_CLI));
        PyDict_SetItemString(opcodesDict, "CLTS", PyLong_FromUint32(triton::arch::x86::ID_INS_CLTS));
        PyDict_SetItemString(opcodesDict, "CMC", PyLong_FromUint32(triton::arch::x86::ID_INS_CMC));
        PyDict_SetItemString(opcodesDict, "CMOVA", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVA));
        PyDict_SetItemString(opcodesDict, "CMOVAE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVAE));
        PyDict_SetItemString(opcodesDict, "CMOVB", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVB));
        PyDict_SetItemString(opcodesDict, "CMOVBE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVBE));
        PyDict_SetItemString(opcodesDict, "FCMOVBE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVBE));
        PyDict_SetItemString(opcodesDict, "FCMOVB", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVB));
        PyDict_SetItemString(opcodesDict, "CMOVE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVE));
        PyDict_SetItemString(opcodesDict, "FCMOVE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVE));
        PyDict_SetItemString(opcodesDict, "CMOVG", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVG));
        PyDict_SetItemString(opcodesDict, "CMOVGE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVGE));
        PyDict_SetItemString(opcodesDict, "CMOVL", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVL));
        PyDict_SetItemString(opcodesDict, "CMOVLE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVLE));
        PyDict_SetItemString(opcodesDict, "FCMOVNBE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNBE));
        PyDict_SetItemString(opcodesDict, "FCMOVNB", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNB));
        PyDict_SetItemString(opcodesDict, "CMOVNE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNE));
        PyDict_SetItemString(opcodesDict, "FCMOVNE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNE));
        PyDict_SetItemString(opcodesDict, "CMOVNO", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNO));
        PyDict_SetItemString(opcodesDict, "CMOVNP", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNP));
        PyDict_SetItemString(opcodesDict, "FCMOVNU", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNU));
        PyDict_SetItemString(opcodesDict, "CMOVNS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNS));
        PyDict_SetItemString(opcodesDict, "CMOVO", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVO));
        PyDict_SetItemString(opcodesDict, "CMOVP", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVP));
        PyDict_SetItemString(opcodesDict, "FCMOVU", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVU));
        PyDict_SetItemString(opcodesDict, "CMOVS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVS));
        PyDict_SetItemString(opcodesDict, "CMP", PyLong_FromUint32(triton::arch::x86::ID_INS_CMP));
        PyDict_SetItemString(opcodesDict, "CMPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPPD));
        PyDict_SetItemString(opcodesDict, "CMPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPPS));
        PyDict_SetItemString(opcodesDict, "CMPSB", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSB));
        PyDict_SetItemString(opcodesDict, "CMPSD", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSD));
        PyDict_SetItemString(opcodesDict, "CMPSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSQ));
        PyDict_SetItemString(opcodesDict, "CMPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSS));
        PyDict_SetItemString(opcodesDict, "CMPSW", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSW));
        PyDict_SetItemString(opcodesDict, "CMPXCHG16B", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPXCHG16B));
        PyDict_SetItemString(opcodesDict, "CMPXCHG", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPXCHG));
        PyDict_SetItemString(opcodesDict, "CMPXCHG8B", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPXCHG8B));
        PyDict_SetItemString(opcodesDict, "COMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_COMISD));
        PyDict_SetItemString(opcodesDict, "COMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_COMISS));
        PyDict_SetItemString(opcodesDict, "FCOMP", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMP));
        PyDict_SetItemString(opcodesDict, "FCOMPI", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMPI));
        PyDict_SetItemString(opcodesDict, "FCOMI", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMI));
        PyDict_SetItemString(opcodesDict, "FCOM", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOM));
        PyDict_SetItemString(opcodesDict, "FCOS", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOS));
        PyDict_SetItemString(opcodesDict, "CPUID", PyLong_FromUint32(triton::arch::x86::ID_INS_CPUID));
        PyDict_SetItemString(opcodesDict, "CQO", PyLong_FromUint32(triton::arch::x86::ID_INS_CQO));
        PyDict_SetItemString(opcodesDict, "CRC32", PyLong_FromUint32(triton::arch::x86::ID_INS_CRC32));
        PyDict_SetItemString(opcodesDict, "CVTDQ2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTDQ2PD));
        PyDict_SetItemString(opcodesDict, "CVTDQ2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTDQ2PS));
        PyDict_SetItemString(opcodesDict, "CVTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPD2DQ));
        PyDict_SetItemString(opcodesDict, "CVTPD2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPD2PS));
        PyDict_SetItemString(opcodesDict, "CVTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPS2DQ));
        PyDict_SetItemString(opcodesDict, "CVTPS2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPS2PD));
        PyDict_SetItemString(opcodesDict, "CVTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSD2SI));
        PyDict_SetItemString(opcodesDict, "CVTSD2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSD2SS));
        PyDict_SetItemString(opcodesDict, "CVTSI2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSI2SD));
        PyDict_SetItemString(opcodesDict, "CVTSI2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSI2SS));
        PyDict_SetItemString(opcodesDict, "CVTSS2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSS2SD));
        PyDict_SetItemString(opcodesDict, "CVTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSS2SI));
        PyDict_SetItemString(opcodesDict, "CVTTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPD2DQ));
        PyDict_SetItemString(opcodesDict, "CVTTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPS2DQ));
        PyDict_SetItemString(opcodesDict, "CVTTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTSD2SI));
        PyDict_SetItemString(opcodesDict, "CVTTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTSS2SI));
        PyDict_SetItemString(opcodesDict, "CWD", PyLong_FromUint32(triton::arch::x86::ID_INS_CWD));
        PyDict_SetItemString(opcodesDict, "CWDE", PyLong_FromUint32(triton::arch::x86::ID_INS_CWDE));
        PyDict_SetItemString(opcodesDict, "DAA", PyLong_FromUint32(triton::arch::x86::ID_INS_DAA));
        PyDict_SetItemString(opcodesDict, "DAS", PyLong_FromUint32(triton::arch::x86::ID_INS_DAS));
        PyDict_SetItemString(opcodesDict, "DATA16", PyLong_FromUint32(triton::arch::x86::ID_INS_DATA16));
        PyDict_SetItemString(opcodesDict, "DEC", PyLong_FromUint32(triton::arch::x86::ID_INS_DEC));
        PyDict_SetItemString(opcodesDict, "DIV", PyLong_FromUint32(triton::arch::x86::ID_INS_DIV));
        PyDict_SetItemString(opcodesDict, "DIVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVPD));
        PyDict_SetItemString(opcodesDict, "DIVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVPS));
        PyDict_SetItemString(opcodesDict, "FDIVR", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIVR));
        PyDict_SetItemString(opcodesDict, "FIDIVR", PyLong_FromUint32(triton::arch::x86::ID_INS_FIDIVR));
        PyDict_SetItemString(opcodesDict, "FDIVRP", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIVRP));
        PyDict_SetItemString(opcodesDict, "DIVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVSD));
        PyDict_SetItemString(opcodesDict, "DIVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVSS));
        PyDict_SetItemString(opcodesDict, "FDIV", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIV));
        PyDict_SetItemString(opcodesDict, "FIDIV", PyLong_FromUint32(triton::arch::x86::ID_INS_FIDIV));
        PyDict_SetItemString(opcodesDict, "FDIVP", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIVP));
        PyDict_SetItemString(opcodesDict, "DPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_DPPD));
        PyDict_SetItemString(opcodesDict, "DPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_DPPS));
        PyDict_SetItemString(opcodesDict, "RET", PyLong_FromUint32(triton::arch::x86::ID_INS_RET));
        PyDict_SetItemString(opcodesDict, "ENCLS", PyLong_FromUint32(triton::arch::x86::ID_INS_ENCLS));
        PyDict_SetItemString(opcodesDict, "ENCLU", PyLong_FromUint32(triton::arch::x86::ID_INS_ENCLU));
        PyDict_SetItemString(opcodesDict, "ENTER", PyLong_FromUint32(triton::arch::x86::ID_INS_ENTER));
        PyDict_SetItemString(opcodesDict, "EXTRACTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_EXTRACTPS));
        PyDict_SetItemString(opcodesDict, "EXTRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_EXTRQ));
        PyDict_SetItemString(opcodesDict, "F2XM1", PyLong_FromUint32(triton::arch::x86::ID_INS_F2XM1));
        PyDict_SetItemString(opcodesDict, "LCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_LCALL));
        PyDict_SetItemString(opcodesDict, "LJMP", PyLong_FromUint32(triton::arch::x86::ID_INS_LJMP));
        PyDict_SetItemString(opcodesDict, "FBLD", PyLong_FromUint32(triton::arch::x86::ID_INS_FBLD));
        PyDict_SetItemString(opcodesDict, "FBSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FBSTP));
        PyDict_SetItemString(opcodesDict, "FCOMPP", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMPP));
        PyDict_SetItemString(opcodesDict, "FDECSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FDECSTP));
        PyDict_SetItemString(opcodesDict, "FEMMS", PyLong_FromUint32(triton::arch::x86::ID_INS_FEMMS));
        PyDict_SetItemString(opcodesDict, "FFREE", PyLong_FromUint32(triton::arch::x86::ID_INS_FFREE));
        PyDict_SetItemString(opcodesDict, "FICOM", PyLong_FromUint32(triton::arch::x86::ID_INS_FICOM));
        PyDict_SetItemString(opcodesDict, "FICOMP", PyLong_FromUint32(triton::arch::x86::ID_INS_FICOMP));
        PyDict_SetItemString(opcodesDict, "FINCSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FINCSTP));
        PyDict_SetItemString(opcodesDict, "FLDCW", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDCW));
        PyDict_SetItemString(opcodesDict, "FLDENV", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDENV));
        PyDict_SetItemString(opcodesDict, "FLDL2E", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDL2E));
        PyDict_SetItemString(opcodesDict, "FLDL2T", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDL2T));
        PyDict_SetItemString(opcodesDict, "FLDLG2", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDLG2));
        PyDict_SetItemString(opcodesDict, "FLDLN2", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDLN2));
        PyDict_SetItemString(opcodesDict, "FLDPI", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDPI));
        PyDict_SetItemString(opcodesDict, "FNCLEX", PyLong_FromUint32(triton::arch::x86::ID_INS_FNCLEX));
        PyDict_SetItemString(opcodesDict, "FNINIT", PyLong_FromUint32(triton::arch::x86::ID_INS_FNINIT));
        PyDict_SetItemString(opcodesDict, "FNOP", PyLong_FromUint32(triton::arch::x86::ID_INS_FNOP));
        PyDict_SetItemString(opcodesDict, "FNSTCW", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSTCW));
        PyDict_SetItemString(opcodesDict, "FNSTSW", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSTSW));
        PyDict_SetItemString(opcodesDict, "FPATAN", PyLong_FromUint32(triton::arch::x86::ID_INS_FPATAN));
        PyDict_SetItemString(opcodesDict, "FPREM", PyLong_FromUint32(triton::arch::x86::ID_INS_FPREM));
        PyDict_SetItemString(opcodesDict, "FPREM1", PyLong_FromUint32(triton::arch::x86::ID_INS_FPREM1));
        PyDict_SetItemString(opcodesDict, "FPTAN", PyLong_FromUint32(triton::arch::x86::ID_INS_FPTAN));
        PyDict_SetItemString(opcodesDict, "FRNDINT", PyLong_FromUint32(triton::arch::x86::ID_INS_FRNDINT));
        PyDict_SetItemString(opcodesDict, "FRSTOR", PyLong_FromUint32(triton::arch::x86::ID_INS_FRSTOR));
        PyDict_SetItemString(opcodesDict, "FNSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSAVE));
        PyDict_SetItemString(opcodesDict, "FSCALE", PyLong_FromUint32(triton::arch::x86::ID_INS_FSCALE));
        PyDict_SetItemString(opcodesDict, "FSETPM", PyLong_FromUint32(triton::arch::x86::ID_INS_FSETPM));
        PyDict_SetItemString(opcodesDict, "FSINCOS", PyLong_FromUint32(triton::arch::x86::ID_INS_FSINCOS));
        PyDict_SetItemString(opcodesDict, "FNSTENV", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSTENV));
        PyDict_SetItemString(opcodesDict, "FXAM", PyLong_FromUint32(triton::arch::x86::ID_INS_FXAM));
        PyDict_SetItemString(opcodesDict, "FXRSTOR", PyLong_FromUint32(triton::arch::x86::ID_INS_FXRSTOR));
        PyDict_SetItemString(opcodesDict, "FXRSTOR64", PyLong_FromUint32(triton::arch::x86::ID_INS_FXRSTOR64));
        PyDict_SetItemString(opcodesDict, "FXSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_FXSAVE));
        PyDict_SetItemString(opcodesDict, "FXSAVE64", PyLong_FromUint32(triton::arch::x86::ID_INS_FXSAVE64));
        PyDict_SetItemString(opcodesDict, "FXTRACT", PyLong_FromUint32(triton::arch::x86::ID_INS_FXTRACT));
        PyDict_SetItemString(opcodesDict, "FYL2X", PyLong_FromUint32(triton::arch::x86::ID_INS_FYL2X));
        PyDict_SetItemString(opcodesDict, "FYL2XP1", PyLong_FromUint32(triton::arch::x86::ID_INS_FYL2XP1));
        PyDict_SetItemString(opcodesDict, "MOVAPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVAPD));
        PyDict_SetItemString(opcodesDict, "MOVAPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVAPS));
        PyDict_SetItemString(opcodesDict, "ORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ORPD));
        PyDict_SetItemString(opcodesDict, "ORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ORPS));
        PyDict_SetItemString(opcodesDict, "VMOVAPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVAPD));
        PyDict_SetItemString(opcodesDict, "VMOVAPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVAPS));
        PyDict_SetItemString(opcodesDict, "XORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_XORPD));
        PyDict_SetItemString(opcodesDict, "XORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_XORPS));
        PyDict_SetItemString(opcodesDict, "GETSEC", PyLong_FromUint32(triton::arch::x86::ID_INS_GETSEC));
        PyDict_SetItemString(opcodesDict, "HADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_HADDPD));
        PyDict_SetItemString(opcodesDict, "HADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_HADDPS));
        PyDict_SetItemString(opcodesDict, "HLT", PyLong_FromUint32(triton::arch::x86::ID_INS_HLT));
        PyDict_SetItemString(opcodesDict, "HSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_HSUBPD));
        PyDict_SetItemString(opcodesDict, "HSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_HSUBPS));
        PyDict_SetItemString(opcodesDict, "IDIV", PyLong_FromUint32(triton::arch::x86::ID_INS_IDIV));
        PyDict_SetItemString(opcodesDict, "FILD", PyLong_FromUint32(triton::arch::x86::ID_INS_FILD));
        PyDict_SetItemString(opcodesDict, "IMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_IMUL));
        PyDict_SetItemString(opcodesDict, "IN", PyLong_FromUint32(triton::arch::x86::ID_INS_IN));
        PyDict_SetItemString(opcodesDict, "INC", PyLong_FromUint32(triton::arch::x86::ID_INS_INC));
        PyDict_SetItemString(opcodesDict, "INSB", PyLong_FromUint32(triton::arch::x86::ID_INS_INSB));
        PyDict_SetItemString(opcodesDict, "INSERTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_INSERTPS));
        PyDict_SetItemString(opcodesDict, "INSERTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_INSERTQ));
        PyDict_SetItemString(opcodesDict, "INSD", PyLong_FromUint32(triton::arch::x86::ID_INS_INSD));
        PyDict_SetItemString(opcodesDict, "INSW", PyLong_FromUint32(triton::arch::x86::ID_INS_INSW));
        PyDict_SetItemString(opcodesDict, "INT", PyLong_FromUint32(triton::arch::x86::ID_INS_INT));
        PyDict_SetItemString(opcodesDict, "INT1", PyLong_FromUint32(triton::arch::x86::ID_INS_INT1));
        PyDict_SetItemString(opcodesDict, "INT3", PyLong_FromUint32(triton::arch::x86::ID_INS_INT3));
        PyDict_SetItemString(opcodesDict, "INTO", PyLong_FromUint32(triton::arch::x86::ID_INS_INTO));
        PyDict_SetItemString(opcodesDict, "INVD", PyLong_FromUint32(triton::arch::x86::ID_INS_INVD));
        PyDict_SetItemString(opcodesDict, "INVEPT", PyLong_FromUint32(triton::arch::x86::ID_INS_INVEPT));
        PyDict_SetItemString(opcodesDict, "INVLPG", PyLong_FromUint32(triton::arch::x86::ID_INS_INVLPG));
        PyDict_SetItemString(opcodesDict, "INVLPGA", PyLong_FromUint32(triton::arch::x86::ID_INS_INVLPGA));
        PyDict_SetItemString(opcodesDict, "INVPCID", PyLong_FromUint32(triton::arch::x86::ID_INS_INVPCID));
        PyDict_SetItemString(opcodesDict, "INVVPID", PyLong_FromUint32(triton::arch::x86::ID_INS_INVVPID));
        PyDict_SetItemString(opcodesDict, "IRET", PyLong_FromUint32(triton::arch::x86::ID_INS_IRET));
        PyDict_SetItemString(opcodesDict, "IRETD", PyLong_FromUint32(triton::arch::x86::ID_INS_IRETD));
        PyDict_SetItemString(opcodesDict, "IRETQ", PyLong_FromUint32(triton::arch::x86::ID_INS_IRETQ));
        PyDict_SetItemString(opcodesDict, "FISTTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FISTTP));
        PyDict_SetItemString(opcodesDict, "FIST", PyLong_FromUint32(triton::arch::x86::ID_INS_FIST));
        PyDict_SetItemString(opcodesDict, "FISTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FISTP));
        PyDict_SetItemString(opcodesDict, "UCOMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_UCOMISD));
        PyDict_SetItemString(opcodesDict, "UCOMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_UCOMISS));
        PyDict_SetItemString(opcodesDict, "VCMP", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMP));
        PyDict_SetItemString(opcodesDict, "VCOMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCOMISD));
        PyDict_SetItemString(opcodesDict, "VCOMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCOMISS));
        PyDict_SetItemString(opcodesDict, "VCVTSD2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSD2SS));
        PyDict_SetItemString(opcodesDict, "VCVTSI2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSI2SD));
        PyDict_SetItemString(opcodesDict, "VCVTSI2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSI2SS));
        PyDict_SetItemString(opcodesDict, "VCVTSS2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSS2SD));
        PyDict_SetItemString(opcodesDict, "VCVTTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSD2SI));
        PyDict_SetItemString(opcodesDict, "VCVTTSD2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSD2USI));
        PyDict_SetItemString(opcodesDict, "VCVTTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSS2SI));
        PyDict_SetItemString(opcodesDict, "VCVTTSS2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSS2USI));
        PyDict_SetItemString(opcodesDict, "VCVTUSI2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUSI2SD));
        PyDict_SetItemString(opcodesDict, "VCVTUSI2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUSI2SS));
        PyDict_SetItemString(opcodesDict, "VUCOMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_VUCOMISD));
        PyDict_SetItemString(opcodesDict, "VUCOMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_VUCOMISS));
        PyDict_SetItemString(opcodesDict, "JAE", PyLong_FromUint32(triton::arch::x86::ID_INS_JAE));
        PyDict_SetItemString(opcodesDict, "JA", PyLong_FromUint32(triton::arch::x86::ID_INS_JA));
        PyDict_SetItemString(opcodesDict, "JBE", PyLong_FromUint32(triton::arch::x86::ID_INS_JBE));
        PyDict_SetItemString(opcodesDict, "JB", PyLong_FromUint32(triton::arch::x86::ID_INS_JB));
        PyDict_SetItemString(opcodesDict, "JCXZ", PyLong_FromUint32(triton::arch::x86::ID_INS_JCXZ));
        PyDict_SetItemString(opcodesDict, "JECXZ", PyLong_FromUint32(triton::arch::x86::ID_INS_JECXZ));
        PyDict_SetItemString(opcodesDict, "JE", PyLong_FromUint32(triton::arch::x86::ID_INS_JE));
        PyDict_SetItemString(opcodesDict, "JGE", PyLong_FromUint32(triton::arch::x86::ID_INS_JGE));
        PyDict_SetItemString(opcodesDict, "JG", PyLong_FromUint32(triton::arch::x86::ID_INS_JG));
        PyDict_SetItemString(opcodesDict, "JLE", PyLong_FromUint32(triton::arch::x86::ID_INS_JLE));
        PyDict_SetItemString(opcodesDict, "JL", PyLong_FromUint32(triton::arch::x86::ID_INS_JL));
        PyDict_SetItemString(opcodesDict, "JMP", PyLong_FromUint32(triton::arch::x86::ID_INS_JMP));
        PyDict_SetItemString(opcodesDict, "JNE", PyLong_FromUint32(triton::arch::x86::ID_INS_JNE));
        PyDict_SetItemString(opcodesDict, "JNO", PyLong_FromUint32(triton::arch::x86::ID_INS_JNO));
        PyDict_SetItemString(opcodesDict, "JNP", PyLong_FromUint32(triton::arch::x86::ID_INS_JNP));
        PyDict_SetItemString(opcodesDict, "JNS", PyLong_FromUint32(triton::arch::x86::ID_INS_JNS));
        PyDict_SetItemString(opcodesDict, "JO", PyLong_FromUint32(triton::arch::x86::ID_INS_JO));
        PyDict_SetItemString(opcodesDict, "JP", PyLong_FromUint32(triton::arch::x86::ID_INS_JP));
        PyDict_SetItemString(opcodesDict, "JRCXZ", PyLong_FromUint32(triton::arch::x86::ID_INS_JRCXZ));
        PyDict_SetItemString(opcodesDict, "JS", PyLong_FromUint32(triton::arch::x86::ID_INS_JS));
        PyDict_SetItemString(opcodesDict, "KANDB", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDB));
        PyDict_SetItemString(opcodesDict, "KANDD", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDD));
        PyDict_SetItemString(opcodesDict, "KANDNB", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDNB));
        PyDict_SetItemString(opcodesDict, "KANDND", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDND));
        PyDict_SetItemString(opcodesDict, "KANDNQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDNQ));
        PyDict_SetItemString(opcodesDict, "KANDNW", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDNW));
        PyDict_SetItemString(opcodesDict, "KANDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDQ));
        PyDict_SetItemString(opcodesDict, "KANDW", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDW));
        PyDict_SetItemString(opcodesDict, "KMOVB", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVB));
        PyDict_SetItemString(opcodesDict, "KMOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVD));
        PyDict_SetItemString(opcodesDict, "KMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVQ));
        PyDict_SetItemString(opcodesDict, "KMOVW", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVW));
        PyDict_SetItemString(opcodesDict, "KNOTB", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTB));
        PyDict_SetItemString(opcodesDict, "KNOTD", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTD));
        PyDict_SetItemString(opcodesDict, "KNOTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTQ));
        PyDict_SetItemString(opcodesDict, "KNOTW", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTW));
        PyDict_SetItemString(opcodesDict, "KORB", PyLong_FromUint32(triton::arch::x86::ID_INS_KORB));
        PyDict_SetItemString(opcodesDict, "KORD", PyLong_FromUint32(triton::arch::x86::ID_INS_KORD));
        PyDict_SetItemString(opcodesDict, "KORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KORQ));
        PyDict_SetItemString(opcodesDict, "KORTESTW", PyLong_FromUint32(triton::arch::x86::ID_INS_KORTESTW));
        PyDict_SetItemString(opcodesDict, "KORW", PyLong_FromUint32(triton::arch::x86::ID_INS_KORW));
        PyDict_SetItemString(opcodesDict, "KSHIFTLW", PyLong_FromUint32(triton::arch::x86::ID_INS_KSHIFTLW));
        PyDict_SetItemString(opcodesDict, "KSHIFTRW", PyLong_FromUint32(triton::arch::x86::ID_INS_KSHIFTRW));
        PyDict_SetItemString(opcodesDict, "KUNPCKBW", PyLong_FromUint32(triton::arch::x86::ID_INS_KUNPCKBW));
        PyDict_SetItemString(opcodesDict, "KXNORB", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORB));
        PyDict_SetItemString(opcodesDict, "KXNORD", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORD));
        PyDict_SetItemString(opcodesDict, "KXNORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORQ));
        PyDict_SetItemString(opcodesDict, "KXNORW", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORW));
        PyDict_SetItemString(opcodesDict, "KXORB", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORB));
        PyDict_SetItemString(opcodesDict, "KXORD", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORD));
        PyDict_SetItemString(opcodesDict, "KXORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORQ));
        PyDict_SetItemString(opcodesDict, "KXORW", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORW));
        PyDict_SetItemString(opcodesDict, "LAHF", PyLong_FromUint32(triton::arch::x86::ID_INS_LAHF));
        PyDict_SetItemString(opcodesDict, "LAR", PyLong_FromUint32(triton::arch::x86::ID_INS_LAR));
        PyDict_SetItemString(opcodesDict, "LDDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_LDDQU));
        PyDict_SetItemString(opcodesDict, "LDMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_LDMXCSR));
        PyDict_SetItemString(opcodesDict, "LDS", PyLong_FromUint32(triton::arch::x86::ID_INS_LDS));
        PyDict_SetItemString(opcodesDict, "FLDZ", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDZ));
        PyDict_SetItemString(opcodesDict, "FLD1", PyLong_FromUint32(triton::arch::x86::ID_INS_FLD1));
        PyDict_SetItemString(opcodesDict, "FLD", PyLong_FromUint32(triton::arch::x86::ID_INS_FLD));
        PyDict_SetItemString(opcodesDict, "LEA", PyLong_FromUint32(triton::arch::x86::ID_INS_LEA));
        PyDict_SetItemString(opcodesDict, "LEAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_LEAVE));
        PyDict_SetItemString(opcodesDict, "LES", PyLong_FromUint32(triton::arch::x86::ID_INS_LES));
        PyDict_SetItemString(opcodesDict, "LFENCE", PyLong_FromUint32(triton::arch::x86::ID_INS_LFENCE));
        PyDict_SetItemString(opcodesDict, "LFS", PyLong_FromUint32(triton::arch::x86::ID_INS_LFS));
        PyDict_SetItemString(opcodesDict, "LGDT", PyLong_FromUint32(triton::arch::x86::ID_INS_LGDT));
        PyDict_SetItemString(opcodesDict, "LGS", PyLong_FromUint32(triton::arch::x86::ID_INS_LGS));
        PyDict_SetItemString(opcodesDict, "LIDT", PyLong_FromUint32(triton::arch::x86::ID_INS_LIDT));
        PyDict_SetItemString(opcodesDict, "LLDT", PyLong_FromUint32(triton::arch::x86::ID_INS_LLDT));
        PyDict_SetItemString(opcodesDict, "LMSW", PyLong_FromUint32(triton::arch::x86::ID_INS_LMSW));
        PyDict_SetItemString(opcodesDict, "OR", PyLong_FromUint32(triton::arch::x86::ID_INS_OR));
        PyDict_SetItemString(opcodesDict, "SUB", PyLong_FromUint32(triton::arch::x86::ID_INS_SUB));
        PyDict_SetItemString(opcodesDict, "XOR", PyLong_FromUint32(triton::arch::x86::ID_INS_XOR));
        PyDict_SetItemString(opcodesDict, "LODSB", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSB));
        PyDict_SetItemString(opcodesDict, "LODSD", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSD));
        PyDict_SetItemString(opcodesDict, "LODSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSQ));
        PyDict_SetItemString(opcodesDict, "LODSW", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSW));
        PyDict_SetItemString(opcodesDict, "LOOP", PyLong_FromUint32(triton::arch::x86::ID_INS_LOOP));
        PyDict_SetItemString(opcodesDict, "LOOPE", PyLong_FromUint32(triton::arch::x86::ID_INS_LOOPE));
        PyDict_SetItemString(opcodesDict, "LOOPNE", PyLong_FromUint32(triton::arch::x86::ID_INS_LOOPNE));
        PyDict_SetItemString(opcodesDict, "RETF", PyLong_FromUint32(triton::arch::x86::ID_INS_RETF));
        PyDict_SetItemString(opcodesDict, "RETFQ", PyLong_FromUint32(triton::arch::x86::ID_INS_RETFQ));
        PyDict_SetItemString(opcodesDict, "LSL", PyLong_FromUint32(triton::arch::x86::ID_INS_LSL));
        PyDict_SetItemString(opcodesDict, "LSS", PyLong_FromUint32(triton::arch::x86::ID_INS_LSS));
        PyDict_SetItemString(opcodesDict, "LTR", PyLong_FromUint32(triton::arch::x86::ID_INS_LTR));
        PyDict_SetItemString(opcodesDict, "XADD", PyLong_FromUint32(triton::arch::x86::ID_INS_XADD));
        PyDict_SetItemString(opcodesDict, "LZCNT", PyLong_FromUint32(triton::arch::x86::ID_INS_LZCNT));
        PyDict_SetItemString(opcodesDict, "MASKMOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_MASKMOVDQU));
        PyDict_SetItemString(opcodesDict, "MAXPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXPD));
        PyDict_SetItemString(opcodesDict, "MAXPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXPS));
        PyDict_SetItemString(opcodesDict, "MAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXSD));
        PyDict_SetItemString(opcodesDict, "MAXSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXSS));
        PyDict_SetItemString(opcodesDict, "MFENCE", PyLong_FromUint32(triton::arch::x86::ID_INS_MFENCE));
        PyDict_SetItemString(opcodesDict, "MINPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MINPD));
        PyDict_SetItemString(opcodesDict, "MINPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MINPS));
        PyDict_SetItemString(opcodesDict, "MINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MINSD));
        PyDict_SetItemString(opcodesDict, "MINSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MINSS));
        PyDict_SetItemString(opcodesDict, "CVTPD2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPD2PI));
        PyDict_SetItemString(opcodesDict, "CVTPI2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPI2PD));
        PyDict_SetItemString(opcodesDict, "CVTPI2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPI2PS));
        PyDict_SetItemString(opcodesDict, "CVTPS2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPS2PI));
        PyDict_SetItemString(opcodesDict, "CVTTPD2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPD2PI));
        PyDict_SetItemString(opcodesDict, "CVTTPS2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPS2PI));
        PyDict_SetItemString(opcodesDict, "EMMS", PyLong_FromUint32(triton::arch::x86::ID_INS_EMMS));
        PyDict_SetItemString(opcodesDict, "MASKMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MASKMOVQ));
        PyDict_SetItemString(opcodesDict, "MOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVD));
        PyDict_SetItemString(opcodesDict, "MOVDQ2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDQ2Q));
        PyDict_SetItemString(opcodesDict, "MOVNTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTQ));
        PyDict_SetItemString(opcodesDict, "MOVQ2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVQ2DQ));
        PyDict_SetItemString(opcodesDict, "MOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVQ));
        PyDict_SetItemString(opcodesDict, "PABSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PABSB));
        PyDict_SetItemString(opcodesDict, "PABSD", PyLong_FromUint32(triton::arch::x86::ID_INS_PABSD));
        PyDict_SetItemString(opcodesDict, "PABSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PABSW));
        PyDict_SetItemString(opcodesDict, "PACKSSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKSSDW));
        PyDict_SetItemString(opcodesDict, "PACKSSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKSSWB));
        PyDict_SetItemString(opcodesDict, "PACKUSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKUSWB));
        PyDict_SetItemString(opcodesDict, "PADDB", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDB));
        PyDict_SetItemString(opcodesDict, "PADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDD));
        PyDict_SetItemString(opcodesDict, "PADDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDQ));
        PyDict_SetItemString(opcodesDict, "PADDSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDSB));
        PyDict_SetItemString(opcodesDict, "PADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDSW));
        PyDict_SetItemString(opcodesDict, "PADDUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDUSB));
        PyDict_SetItemString(opcodesDict, "PADDUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDUSW));
        PyDict_SetItemString(opcodesDict, "PADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDW));
        PyDict_SetItemString(opcodesDict, "PALIGNR", PyLong_FromUint32(triton::arch::x86::ID_INS_PALIGNR));
        PyDict_SetItemString(opcodesDict, "PANDN", PyLong_FromUint32(triton::arch::x86::ID_INS_PANDN));
        PyDict_SetItemString(opcodesDict, "PAND", PyLong_FromUint32(triton::arch::x86::ID_INS_PAND));
        PyDict_SetItemString(opcodesDict, "PAVGB", PyLong_FromUint32(triton::arch::x86::ID_INS_PAVGB));
        PyDict_SetItemString(opcodesDict, "PAVGW", PyLong_FromUint32(triton::arch::x86::ID_INS_PAVGW));
        PyDict_SetItemString(opcodesDict, "PCMPEQB", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQB));
        PyDict_SetItemString(opcodesDict, "PCMPEQD", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQD));
        PyDict_SetItemString(opcodesDict, "PCMPEQW", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQW));
        PyDict_SetItemString(opcodesDict, "PCMPGTB", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTB));
        PyDict_SetItemString(opcodesDict, "PCMPGTD", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTD));
        PyDict_SetItemString(opcodesDict, "PCMPGTW", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTW));
        PyDict_SetItemString(opcodesDict, "PEXTRW", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRW));
        PyDict_SetItemString(opcodesDict, "PHADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHADDSW));
        PyDict_SetItemString(opcodesDict, "PHADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHADDW));
        PyDict_SetItemString(opcodesDict, "PHADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_PHADDD));
        PyDict_SetItemString(opcodesDict, "PHSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PHSUBD));
        PyDict_SetItemString(opcodesDict, "PHSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHSUBSW));
        PyDict_SetItemString(opcodesDict, "PHSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHSUBW));
        PyDict_SetItemString(opcodesDict, "PINSRW", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRW));
        PyDict_SetItemString(opcodesDict, "PMADDUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMADDUBSW));
        PyDict_SetItemString(opcodesDict, "PMADDWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMADDWD));
        PyDict_SetItemString(opcodesDict, "PMAXSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXSW));
        PyDict_SetItemString(opcodesDict, "PMAXUB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXUB));
        PyDict_SetItemString(opcodesDict, "PMINSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINSW));
        PyDict_SetItemString(opcodesDict, "PMINUB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINUB));
        PyDict_SetItemString(opcodesDict, "PMOVMSKB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVMSKB));
        PyDict_SetItemString(opcodesDict, "PMULHRSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHRSW));
        PyDict_SetItemString(opcodesDict, "PMULHUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHUW));
        PyDict_SetItemString(opcodesDict, "PMULHW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHW));
        PyDict_SetItemString(opcodesDict, "PMULLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULLW));
        PyDict_SetItemString(opcodesDict, "PMULUDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULUDQ));
        PyDict_SetItemString(opcodesDict, "POR", PyLong_FromUint32(triton::arch::x86::ID_INS_POR));
        PyDict_SetItemString(opcodesDict, "PSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSADBW));
        PyDict_SetItemString(opcodesDict, "PSHUFB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFB));
        PyDict_SetItemString(opcodesDict, "PSHUFW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFW));
        PyDict_SetItemString(opcodesDict, "PSIGNB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSIGNB));
        PyDict_SetItemString(opcodesDict, "PSIGND", PyLong_FromUint32(triton::arch::x86::ID_INS_PSIGND));
        PyDict_SetItemString(opcodesDict, "PSIGNW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSIGNW));
        PyDict_SetItemString(opcodesDict, "PSLLD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLD));
        PyDict_SetItemString(opcodesDict, "PSLLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLQ));
        PyDict_SetItemString(opcodesDict, "PSLLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLW));
        PyDict_SetItemString(opcodesDict, "PSRAD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRAD));
        PyDict_SetItemString(opcodesDict, "PSRAW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRAW));
        PyDict_SetItemString(opcodesDict, "PSRLD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLD));
        PyDict_SetItemString(opcodesDict, "PSRLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLQ));
        PyDict_SetItemString(opcodesDict, "PSRLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLW));
        PyDict_SetItemString(opcodesDict, "PSUBB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBB));
        PyDict_SetItemString(opcodesDict, "PSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBD));
        PyDict_SetItemString(opcodesDict, "PSUBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBQ));
        PyDict_SetItemString(opcodesDict, "PSUBSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBSB));
        PyDict_SetItemString(opcodesDict, "PSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBSW));
        PyDict_SetItemString(opcodesDict, "PSUBUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBUSB));
        PyDict_SetItemString(opcodesDict, "PSUBUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBUSW));
        PyDict_SetItemString(opcodesDict, "PSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBW));
        PyDict_SetItemString(opcodesDict, "PUNPCKHBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHBW));
        PyDict_SetItemString(opcodesDict, "PUNPCKHDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHDQ));
        PyDict_SetItemString(opcodesDict, "PUNPCKHWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHWD));
        PyDict_SetItemString(opcodesDict, "PUNPCKLBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLBW));
        PyDict_SetItemString(opcodesDict, "PUNPCKLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLDQ));
        PyDict_SetItemString(opcodesDict, "PUNPCKLWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLWD));
        PyDict_SetItemString(opcodesDict, "PXOR", PyLong_FromUint32(triton::arch::x86::ID_INS_PXOR));
        PyDict_SetItemString(opcodesDict, "MONITOR", PyLong_FromUint32(triton::arch::x86::ID_INS_MONITOR));
        PyDict_SetItemString(opcodesDict, "MONTMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_MONTMUL));
        PyDict_SetItemString(opcodesDict, "MOV", PyLong_FromUint32(triton::arch::x86::ID_INS_MOV));
        PyDict_SetItemString(opcodesDict, "MOVABS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVABS));
        PyDict_SetItemString(opcodesDict, "MOVBE", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVBE));
        PyDict_SetItemString(opcodesDict, "MOVDDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDDUP));
        PyDict_SetItemString(opcodesDict, "MOVDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDQA));
        PyDict_SetItemString(opcodesDict, "MOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDQU));
        PyDict_SetItemString(opcodesDict, "MOVHLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVHLPS));
        PyDict_SetItemString(opcodesDict, "MOVHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVHPD));
        PyDict_SetItemString(opcodesDict, "MOVHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVHPS));
        PyDict_SetItemString(opcodesDict, "MOVLHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVLHPS));
        PyDict_SetItemString(opcodesDict, "MOVLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVLPD));
        PyDict_SetItemString(opcodesDict, "MOVLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVLPS));
        PyDict_SetItemString(opcodesDict, "MOVMSKPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVMSKPD));
        PyDict_SetItemString(opcodesDict, "MOVMSKPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVMSKPS));
        PyDict_SetItemString(opcodesDict, "MOVNTDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTDQA));
        PyDict_SetItemString(opcodesDict, "MOVNTDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTDQ));
        PyDict_SetItemString(opcodesDict, "MOVNTI", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTI));
        PyDict_SetItemString(opcodesDict, "MOVNTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTPD));
        PyDict_SetItemString(opcodesDict, "MOVNTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTPS));
        PyDict_SetItemString(opcodesDict, "MOVNTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTSD));
        PyDict_SetItemString(opcodesDict, "MOVNTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTSS));
        PyDict_SetItemString(opcodesDict, "MOVSB", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSB));
        PyDict_SetItemString(opcodesDict, "MOVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSD));
        PyDict_SetItemString(opcodesDict, "MOVSHDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSHDUP));
        PyDict_SetItemString(opcodesDict, "MOVSLDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSLDUP));
        PyDict_SetItemString(opcodesDict, "MOVSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSQ));
        PyDict_SetItemString(opcodesDict, "MOVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSS));
        PyDict_SetItemString(opcodesDict, "MOVSW", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSW));
        PyDict_SetItemString(opcodesDict, "MOVSX", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSX));
        PyDict_SetItemString(opcodesDict, "MOVSXD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSXD));
        PyDict_SetItemString(opcodesDict, "MOVUPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVUPD));
        PyDict_SetItemString(opcodesDict, "MOVUPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVUPS));
        PyDict_SetItemString(opcodesDict, "MOVZX", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVZX));
        PyDict_SetItemString(opcodesDict, "MPSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_MPSADBW));
        PyDict_SetItemString(opcodesDict, "MUL", PyLong_FromUint32(triton::arch::x86::ID_INS_MUL));
        PyDict_SetItemString(opcodesDict, "MULPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MULPD));
        PyDict_SetItemString(opcodesDict, "MULPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MULPS));
        PyDict_SetItemString(opcodesDict, "MULSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MULSD));
        PyDict_SetItemString(opcodesDict, "MULSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MULSS));
        PyDict_SetItemString(opcodesDict, "MULX", PyLong_FromUint32(triton::arch::x86::ID_INS_MULX));
        PyDict_SetItemString(opcodesDict, "FMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_FMUL));
        PyDict_SetItemString(opcodesDict, "FIMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_FIMUL));
        PyDict_SetItemString(opcodesDict, "FMULP", PyLong_FromUint32(triton::arch::x86::ID_INS_FMULP));
        PyDict_SetItemString(opcodesDict, "MWAIT", PyLong_FromUint32(triton::arch::x86::ID_INS_MWAIT));
        PyDict_SetItemString(opcodesDict, "NEG", PyLong_FromUint32(triton::arch::x86::ID_INS_NEG));
        PyDict_SetItemString(opcodesDict, "NOP", PyLong_FromUint32(triton::arch::x86::ID_INS_NOP));
        PyDict_SetItemString(opcodesDict, "NOT", PyLong_FromUint32(triton::arch::x86::ID_INS_NOT));
        PyDict_SetItemString(opcodesDict, "OUT", PyLong_FromUint32(triton::arch::x86::ID_INS_OUT));
        PyDict_SetItemString(opcodesDict, "OUTSB", PyLong_FromUint32(triton::arch::x86::ID_INS_OUTSB));
        PyDict_SetItemString(opcodesDict, "OUTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_OUTSD));
        PyDict_SetItemString(opcodesDict, "OUTSW", PyLong_FromUint32(triton::arch::x86::ID_INS_OUTSW));
        PyDict_SetItemString(opcodesDict, "PACKUSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKUSDW));
        PyDict_SetItemString(opcodesDict, "PAUSE", PyLong_FromUint32(triton::arch::x86::ID_INS_PAUSE));
        PyDict_SetItemString(opcodesDict, "PAVGUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PAVGUSB));
        PyDict_SetItemString(opcodesDict, "PBLENDVB", PyLong_FromUint32(triton::arch::x86::ID_INS_PBLENDVB));
        PyDict_SetItemString(opcodesDict, "PBLENDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PBLENDW));
        PyDict_SetItemString(opcodesDict, "PCLMULQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PCLMULQDQ));
        PyDict_SetItemString(opcodesDict, "PCMPEQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQQ));
        PyDict_SetItemString(opcodesDict, "PCMPESTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPESTRI));
        PyDict_SetItemString(opcodesDict, "PCMPESTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPESTRM));
        PyDict_SetItemString(opcodesDict, "PCMPGTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTQ));
        PyDict_SetItemString(opcodesDict, "PCMPISTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPISTRI));
        PyDict_SetItemString(opcodesDict, "PCMPISTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPISTRM));
        PyDict_SetItemString(opcodesDict, "PDEP", PyLong_FromUint32(triton::arch::x86::ID_INS_PDEP));
        PyDict_SetItemString(opcodesDict, "PEXT", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXT));
        PyDict_SetItemString(opcodesDict, "PEXTRB", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRB));
        PyDict_SetItemString(opcodesDict, "PEXTRD", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRD));
        PyDict_SetItemString(opcodesDict, "PEXTRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRQ));
        PyDict_SetItemString(opcodesDict, "PF2ID", PyLong_FromUint32(triton::arch::x86::ID_INS_PF2ID));
        PyDict_SetItemString(opcodesDict, "PF2IW", PyLong_FromUint32(triton::arch::x86::ID_INS_PF2IW));
        PyDict_SetItemString(opcodesDict, "PFACC", PyLong_FromUint32(triton::arch::x86::ID_INS_PFACC));
        PyDict_SetItemString(opcodesDict, "PFADD", PyLong_FromUint32(triton::arch::x86::ID_INS_PFADD));
        PyDict_SetItemString(opcodesDict, "PFCMPEQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PFCMPEQ));
        PyDict_SetItemString(opcodesDict, "PFCMPGE", PyLong_FromUint32(triton::arch::x86::ID_INS_PFCMPGE));
        PyDict_SetItemString(opcodesDict, "PFCMPGT", PyLong_FromUint32(triton::arch::x86::ID_INS_PFCMPGT));
        PyDict_SetItemString(opcodesDict, "PFMAX", PyLong_FromUint32(triton::arch::x86::ID_INS_PFMAX));
        PyDict_SetItemString(opcodesDict, "PFMIN", PyLong_FromUint32(triton::arch::x86::ID_INS_PFMIN));
        PyDict_SetItemString(opcodesDict, "PFMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_PFMUL));
        PyDict_SetItemString(opcodesDict, "PFNACC", PyLong_FromUint32(triton::arch::x86::ID_INS_PFNACC));
        PyDict_SetItemString(opcodesDict, "PFPNACC", PyLong_FromUint32(triton::arch::x86::ID_INS_PFPNACC));
        PyDict_SetItemString(opcodesDict, "PFRCPIT1", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRCPIT1));
        PyDict_SetItemString(opcodesDict, "PFRCPIT2", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRCPIT2));
        PyDict_SetItemString(opcodesDict, "PFRCP", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRCP));
        PyDict_SetItemString(opcodesDict, "PFRSQIT1", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRSQIT1));
        PyDict_SetItemString(opcodesDict, "PFRSQRT", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRSQRT));
        PyDict_SetItemString(opcodesDict, "PFSUBR", PyLong_FromUint32(triton::arch::x86::ID_INS_PFSUBR));
        PyDict_SetItemString(opcodesDict, "PFSUB", PyLong_FromUint32(triton::arch::x86::ID_INS_PFSUB));
        PyDict_SetItemString(opcodesDict, "PHMINPOSUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHMINPOSUW));
        PyDict_SetItemString(opcodesDict, "PI2FD", PyLong_FromUint32(triton::arch::x86::ID_INS_PI2FD));
        PyDict_SetItemString(opcodesDict, "PI2FW", PyLong_FromUint32(triton::arch::x86::ID_INS_PI2FW));
        PyDict_SetItemString(opcodesDict, "PINSRB", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRB));
        PyDict_SetItemString(opcodesDict, "PINSRD", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRD));
        PyDict_SetItemString(opcodesDict, "PINSRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRQ));
        PyDict_SetItemString(opcodesDict, "PMAXSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXSB));
        PyDict_SetItemString(opcodesDict, "PMAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXSD));
        PyDict_SetItemString(opcodesDict, "PMAXUD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXUD));
        PyDict_SetItemString(opcodesDict, "PMAXUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXUW));
        PyDict_SetItemString(opcodesDict, "PMINSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINSB));
        PyDict_SetItemString(opcodesDict, "PMINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINSD));
        PyDict_SetItemString(opcodesDict, "PMINUD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINUD));
        PyDict_SetItemString(opcodesDict, "PMINUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINUW));
        PyDict_SetItemString(opcodesDict, "PMOVSXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXBD));
        PyDict_SetItemString(opcodesDict, "PMOVSXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXBQ));
        PyDict_SetItemString(opcodesDict, "PMOVSXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXBW));
        PyDict_SetItemString(opcodesDict, "PMOVSXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXDQ));
        PyDict_SetItemString(opcodesDict, "PMOVSXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXWD));
        PyDict_SetItemString(opcodesDict, "PMOVSXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXWQ));
        PyDict_SetItemString(opcodesDict, "PMOVZXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXBD));
        PyDict_SetItemString(opcodesDict, "PMOVZXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXBQ));
        PyDict_SetItemString(opcodesDict, "PMOVZXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXBW));
        PyDict_SetItemString(opcodesDict, "PMOVZXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXDQ));
        PyDict_SetItemString(opcodesDict, "PMOVZXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXWD));
        PyDict_SetItemString(opcodesDict, "PMOVZXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXWQ));
        PyDict_SetItemString(opcodesDict, "PMULDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULDQ));
        PyDict_SetItemString(opcodesDict, "PMULHRW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHRW));
        PyDict_SetItemString(opcodesDict, "PMULLD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULLD));
        PyDict_SetItemString(opcodesDict, "POP", PyLong_FromUint32(triton::arch::x86::ID_INS_POP));
        PyDict_SetItemString(opcodesDict, "POPAW", PyLong_FromUint32(triton::arch::x86::ID_INS_POPAW));
        PyDict_SetItemString(opcodesDict, "POPAL", PyLong_FromUint32(triton::arch::x86::ID_INS_POPAL));
        PyDict_SetItemString(opcodesDict, "POPCNT", PyLong_FromUint32(triton::arch::x86::ID_INS_POPCNT));
        PyDict_SetItemString(opcodesDict, "POPF", PyLong_FromUint32(triton::arch::x86::ID_INS_POPF));
        PyDict_SetItemString(opcodesDict, "POPFD", PyLong_FromUint32(triton::arch::x86::ID_INS_POPFD));
        PyDict_SetItemString(opcodesDict, "POPFQ", PyLong_FromUint32(triton::arch::x86::ID_INS_POPFQ));
        PyDict_SetItemString(opcodesDict, "PREFETCH", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCH));
        PyDict_SetItemString(opcodesDict, "PREFETCHNTA", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHNTA));
        PyDict_SetItemString(opcodesDict, "PREFETCHT0", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHT0));
        PyDict_SetItemString(opcodesDict, "PREFETCHT1", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHT1));
        PyDict_SetItemString(opcodesDict, "PREFETCHT2", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHT2));
        PyDict_SetItemString(opcodesDict, "PREFETCHW", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHW));
        PyDict_SetItemString(opcodesDict, "PSHUFD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFD));
        PyDict_SetItemString(opcodesDict, "PSHUFHW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFHW));
        PyDict_SetItemString(opcodesDict, "PSHUFLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFLW));
        PyDict_SetItemString(opcodesDict, "PSLLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLDQ));
        PyDict_SetItemString(opcodesDict, "PSRLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLDQ));
        PyDict_SetItemString(opcodesDict, "PSWAPD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSWAPD));
        PyDict_SetItemString(opcodesDict, "PTEST", PyLong_FromUint32(triton::arch::x86::ID_INS_PTEST));
        PyDict_SetItemString(opcodesDict, "PUNPCKHQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHQDQ));
        PyDict_SetItemString(opcodesDict, "PUNPCKLQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLQDQ));
        PyDict_SetItemString(opcodesDict, "PUSH", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSH));
        PyDict_SetItemString(opcodesDict, "PUSHAW", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHAW));
        PyDict_SetItemString(opcodesDict, "PUSHAL", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHAL));
        PyDict_SetItemString(opcodesDict, "PUSHF", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHF));
        PyDict_SetItemString(opcodesDict, "PUSHFD", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHFD));
        PyDict_SetItemString(opcodesDict, "PUSHFQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHFQ));
        PyDict_SetItemString(opcodesDict, "RCL", PyLong_FromUint32(triton::arch::x86::ID_INS_RCL));
        PyDict_SetItemString(opcodesDict, "RCPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_RCPPS));
        PyDict_SetItemString(opcodesDict, "RCPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_RCPSS));
        PyDict_SetItemString(opcodesDict, "RCR", PyLong_FromUint32(triton::arch::x86::ID_INS_RCR));
        PyDict_SetItemString(opcodesDict, "RDFSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_RDFSBASE));
        PyDict_SetItemString(opcodesDict, "RDGSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_RDGSBASE));
        PyDict_SetItemString(opcodesDict, "RDMSR", PyLong_FromUint32(triton::arch::x86::ID_INS_RDMSR));
        PyDict_SetItemString(opcodesDict, "RDPMC", PyLong_FromUint32(triton::arch::x86::ID_INS_RDPMC));
        PyDict_SetItemString(opcodesDict, "RDRAND", PyLong_FromUint32(triton::arch::x86::ID_INS_RDRAND));
        PyDict_SetItemString(opcodesDict, "RDSEED", PyLong_FromUint32(triton::arch::x86::ID_INS_RDSEED));
        PyDict_SetItemString(opcodesDict, "RDTSC", PyLong_FromUint32(triton::arch::x86::ID_INS_RDTSC));
        PyDict_SetItemString(opcodesDict, "RDTSCP", PyLong_FromUint32(triton::arch::x86::ID_INS_RDTSCP));
        PyDict_SetItemString(opcodesDict, "ROL", PyLong_FromUint32(triton::arch::x86::ID_INS_ROL));
        PyDict_SetItemString(opcodesDict, "ROR", PyLong_FromUint32(triton::arch::x86::ID_INS_ROR));
        PyDict_SetItemString(opcodesDict, "RORX", PyLong_FromUint32(triton::arch::x86::ID_INS_RORX));
        PyDict_SetItemString(opcodesDict, "ROUNDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDPD));
        PyDict_SetItemString(opcodesDict, "ROUNDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDPS));
        PyDict_SetItemString(opcodesDict, "ROUNDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDSD));
        PyDict_SetItemString(opcodesDict, "ROUNDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDSS));
        PyDict_SetItemString(opcodesDict, "RSM", PyLong_FromUint32(triton::arch::x86::ID_INS_RSM));
        PyDict_SetItemString(opcodesDict, "RSQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_RSQRTPS));
        PyDict_SetItemString(opcodesDict, "RSQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_RSQRTSS));
        PyDict_SetItemString(opcodesDict, "SAHF", PyLong_FromUint32(triton::arch::x86::ID_INS_SAHF));
        PyDict_SetItemString(opcodesDict, "SAL", PyLong_FromUint32(triton::arch::x86::ID_INS_SAL));
        PyDict_SetItemString(opcodesDict, "SALC", PyLong_FromUint32(triton::arch::x86::ID_INS_SALC));
        PyDict_SetItemString(opcodesDict, "SAR", PyLong_FromUint32(triton::arch::x86::ID_INS_SAR));
        PyDict_SetItemString(opcodesDict, "SARX", PyLong_FromUint32(triton::arch::x86::ID_INS_SARX));
        PyDict_SetItemString(opcodesDict, "SBB", PyLong_FromUint32(triton::arch::x86::ID_INS_SBB));
        PyDict_SetItemString(opcodesDict, "SCASB", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASB));
        PyDict_SetItemString(opcodesDict, "SCASD", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASD));
        PyDict_SetItemString(opcodesDict, "SCASQ", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASQ));
        PyDict_SetItemString(opcodesDict, "SCASW", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASW));
        PyDict_SetItemString(opcodesDict, "SETAE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETAE));
        PyDict_SetItemString(opcodesDict, "SETA", PyLong_FromUint32(triton::arch::x86::ID_INS_SETA));
        PyDict_SetItemString(opcodesDict, "SETBE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETBE));
        PyDict_SetItemString(opcodesDict, "SETB", PyLong_FromUint32(triton::arch::x86::ID_INS_SETB));
        PyDict_SetItemString(opcodesDict, "SETE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETE));
        PyDict_SetItemString(opcodesDict, "SETGE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETGE));
        PyDict_SetItemString(opcodesDict, "SETG", PyLong_FromUint32(triton::arch::x86::ID_INS_SETG));
        PyDict_SetItemString(opcodesDict, "SETLE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETLE));
        PyDict_SetItemString(opcodesDict, "SETL", PyLong_FromUint32(triton::arch::x86::ID_INS_SETL));
        PyDict_SetItemString(opcodesDict, "SETNE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNE));
        PyDict_SetItemString(opcodesDict, "SETNO", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNO));
        PyDict_SetItemString(opcodesDict, "SETNP", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNP));
        PyDict_SetItemString(opcodesDict, "SETNS", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNS));
        PyDict_SetItemString(opcodesDict, "SETO", PyLong_FromUint32(triton::arch::x86::ID_INS_SETO));
        PyDict_SetItemString(opcodesDict, "SETP", PyLong_FromUint32(triton::arch::x86::ID_INS_SETP));
        PyDict_SetItemString(opcodesDict, "SETS", PyLong_FromUint32(triton::arch::x86::ID_INS_SETS));
        PyDict_SetItemString(opcodesDict, "SFENCE", PyLong_FromUint32(triton::arch::x86::ID_INS_SFENCE));
        PyDict_SetItemString(opcodesDict, "SGDT", PyLong_FromUint32(triton::arch::x86::ID_INS_SGDT));
        PyDict_SetItemString(opcodesDict, "SHA1MSG1", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1MSG1));
        PyDict_SetItemString(opcodesDict, "SHA1MSG2", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1MSG2));
        PyDict_SetItemString(opcodesDict, "SHA1NEXTE", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1NEXTE));
        PyDict_SetItemString(opcodesDict, "SHA1RNDS4", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1RNDS4));
        PyDict_SetItemString(opcodesDict, "SHA256MSG1", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA256MSG1));
        PyDict_SetItemString(opcodesDict, "SHA256MSG2", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA256MSG2));
        PyDict_SetItemString(opcodesDict, "SHA256RNDS2", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA256RNDS2));
        PyDict_SetItemString(opcodesDict, "SHL", PyLong_FromUint32(triton::arch::x86::ID_INS_SHL));
        PyDict_SetItemString(opcodesDict, "SHLD", PyLong_FromUint32(triton::arch::x86::ID_INS_SHLD));
        PyDict_SetItemString(opcodesDict, "SHLX", PyLong_FromUint32(triton::arch::x86::ID_INS_SHLX));
        PyDict_SetItemString(opcodesDict, "SHR", PyLong_FromUint32(triton::arch::x86::ID_INS_SHR));
        PyDict_SetItemString(opcodesDict, "SHRD", PyLong_FromUint32(triton::arch::x86::ID_INS_SHRD));
        PyDict_SetItemString(opcodesDict, "SHRX", PyLong_FromUint32(triton::arch::x86::ID_INS_SHRX));
        PyDict_SetItemString(opcodesDict, "SHUFPD", PyLong_FromUint32(triton::arch::x86::ID_INS_SHUFPD));
        PyDict_SetItemString(opcodesDict, "SHUFPS", PyLong_FromUint32(triton::arch::x86::ID_INS_SHUFPS));
        PyDict_SetItemString(opcodesDict, "SIDT", PyLong_FromUint32(triton::arch::x86::ID_INS_SIDT));
        PyDict_SetItemString(opcodesDict, "FSIN", PyLong_FromUint32(triton::arch::x86::ID_INS_FSIN));
        PyDict_SetItemString(opcodesDict, "SKINIT", PyLong_FromUint32(triton::arch::x86::ID_INS_SKINIT));
        PyDict_SetItemString(opcodesDict, "SLDT", PyLong_FromUint32(triton::arch::x86::ID_INS_SLDT));
        PyDict_SetItemString(opcodesDict, "SMSW", PyLong_FromUint32(triton::arch::x86::ID_INS_SMSW));
        PyDict_SetItemString(opcodesDict, "SQRTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTPD));
        PyDict_SetItemString(opcodesDict, "SQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTPS));
        PyDict_SetItemString(opcodesDict, "SQRTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTSD));
        PyDict_SetItemString(opcodesDict, "SQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTSS));
        PyDict_SetItemString(opcodesDict, "FSQRT", PyLong_FromUint32(triton::arch::x86::ID_INS_FSQRT));
        PyDict_SetItemString(opcodesDict, "STAC", PyLong_FromUint32(triton::arch::x86::ID_INS_STAC));
        PyDict_SetItemString(opcodesDict, "STC", PyLong_FromUint32(triton::arch::x86::ID_INS_STC));
        PyDict_SetItemString(opcodesDict, "STD", PyLong_FromUint32(triton::arch::x86::ID_INS_STD));
        PyDict_SetItemString(opcodesDict, "STGI", PyLong_FromUint32(triton::arch::x86::ID_INS_STGI));
        PyDict_SetItemString(opcodesDict, "STI", PyLong_FromUint32(triton::arch::x86::ID_INS_STI));
        PyDict_SetItemString(opcodesDict, "STMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_STMXCSR));
        PyDict_SetItemString(opcodesDict, "STOSB", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSB));
        PyDict_SetItemString(opcodesDict, "STOSD", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSD));
        PyDict_SetItemString(opcodesDict, "STOSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSQ));
        PyDict_SetItemString(opcodesDict, "STOSW", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSW));
        PyDict_SetItemString(opcodesDict, "STR", PyLong_FromUint32(triton::arch::x86::ID_INS_STR));
        PyDict_SetItemString(opcodesDict, "FST", PyLong_FromUint32(triton::arch::x86::ID_INS_FST));
        PyDict_SetItemString(opcodesDict, "FSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FSTP));
        PyDict_SetItemString(opcodesDict, "FSTPNCE", PyLong_FromUint32(triton::arch::x86::ID_INS_FSTPNCE));
        PyDict_SetItemString(opcodesDict, "SUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBPD));
        PyDict_SetItemString(opcodesDict, "SUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBPS));
        PyDict_SetItemString(opcodesDict, "FSUBR", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUBR));
        PyDict_SetItemString(opcodesDict, "FISUBR", PyLong_FromUint32(triton::arch::x86::ID_INS_FISUBR));
        PyDict_SetItemString(opcodesDict, "FSUBRP", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUBRP));
        PyDict_SetItemString(opcodesDict, "SUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBSD));
        PyDict_SetItemString(opcodesDict, "SUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBSS));
        PyDict_SetItemString(opcodesDict, "FSUB", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUB));
        PyDict_SetItemString(opcodesDict, "FISUB", PyLong_FromUint32(triton::arch::x86::ID_INS_FISUB));
        PyDict_SetItemString(opcodesDict, "FSUBP", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUBP));
        PyDict_SetItemString(opcodesDict, "SWAPGS", PyLong_FromUint32(triton::arch::x86::ID_INS_SWAPGS));
        PyDict_SetItemString(opcodesDict, "SYSCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSCALL));
        PyDict_SetItemString(opcodesDict, "SYSENTER", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSENTER));
        PyDict_SetItemString(opcodesDict, "SYSEXIT", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSEXIT));
        PyDict_SetItemString(opcodesDict, "SYSRET", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSRET));
        PyDict_SetItemString(opcodesDict, "T1MSKC", PyLong_FromUint32(triton::arch::x86::ID_INS_T1MSKC));
        PyDict_SetItemString(opcodesDict, "TEST", PyLong_FromUint32(triton::arch::x86::ID_INS_TEST));
        PyDict_SetItemString(opcodesDict, "UD2", PyLong_FromUint32(triton::arch::x86::ID_INS_UD2));
        PyDict_SetItemString(opcodesDict, "FTST", PyLong_FromUint32(triton::arch::x86::ID_INS_FTST));
        PyDict_SetItemString(opcodesDict, "TZCNT", PyLong_FromUint32(triton::arch::x86::ID_INS_TZCNT));
        PyDict_SetItemString(opcodesDict, "TZMSK", PyLong_FromUint32(triton::arch::x86::ID_INS_TZMSK));
        PyDict_SetItemString(opcodesDict, "FUCOMPI", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMPI));
        PyDict_SetItemString(opcodesDict, "FUCOMI", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMI));
        PyDict_SetItemString(opcodesDict, "FUCOMPP", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMPP));
        PyDict_SetItemString(opcodesDict, "FUCOMP", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMP));
        PyDict_SetItemString(opcodesDict, "FUCOM", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOM));
        PyDict_SetItemString(opcodesDict, "UD2B", PyLong_FromUint32(triton::arch::x86::ID_INS_UD2B));
        PyDict_SetItemString(opcodesDict, "UNPCKHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKHPD));
        PyDict_SetItemString(opcodesDict, "UNPCKHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKHPS));
        PyDict_SetItemString(opcodesDict, "UNPCKLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKLPD));
        PyDict_SetItemString(opcodesDict, "UNPCKLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKLPS));
        PyDict_SetItemString(opcodesDict, "VADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDPD));
        PyDict_SetItemString(opcodesDict, "VADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDPS));
        PyDict_SetItemString(opcodesDict, "VADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSD));
        PyDict_SetItemString(opcodesDict, "VADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSS));
        PyDict_SetItemString(opcodesDict, "VADDSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSUBPD));
        PyDict_SetItemString(opcodesDict, "VADDSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSUBPS));
        PyDict_SetItemString(opcodesDict, "VAESDECLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESDECLAST));
        PyDict_SetItemString(opcodesDict, "VAESDEC", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESDEC));
        PyDict_SetItemString(opcodesDict, "VAESENCLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESENCLAST));
        PyDict_SetItemString(opcodesDict, "VAESENC", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESENC));
        PyDict_SetItemString(opcodesDict, "VAESIMC", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESIMC));
        PyDict_SetItemString(opcodesDict, "VAESKEYGENASSIST", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESKEYGENASSIST));
        PyDict_SetItemString(opcodesDict, "VALIGND", PyLong_FromUint32(triton::arch::x86::ID_INS_VALIGND));
        PyDict_SetItemString(opcodesDict, "VALIGNQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VALIGNQ));
        PyDict_SetItemString(opcodesDict, "VANDNPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDNPD));
        PyDict_SetItemString(opcodesDict, "VANDNPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDNPS));
        PyDict_SetItemString(opcodesDict, "VANDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDPD));
        PyDict_SetItemString(opcodesDict, "VANDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDPS));
        PyDict_SetItemString(opcodesDict, "VBLENDMPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDMPD));
        PyDict_SetItemString(opcodesDict, "VBLENDMPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDMPS));
        PyDict_SetItemString(opcodesDict, "VBLENDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDPD));
        PyDict_SetItemString(opcodesDict, "VBLENDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDPS));
        PyDict_SetItemString(opcodesDict, "VBLENDVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDVPD));
        PyDict_SetItemString(opcodesDict, "VBLENDVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDVPS));
        PyDict_SetItemString(opcodesDict, "VBROADCASTF128", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTF128));
        PyDict_SetItemString(opcodesDict, "VBROADCASTI128", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTI128));
        PyDict_SetItemString(opcodesDict, "VBROADCASTI32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTI32X4));
        PyDict_SetItemString(opcodesDict, "VBROADCASTI64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTI64X4));
        PyDict_SetItemString(opcodesDict, "VBROADCASTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTSD));
        PyDict_SetItemString(opcodesDict, "VBROADCASTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTSS));
        PyDict_SetItemString(opcodesDict, "VCMPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPPD));
        PyDict_SetItemString(opcodesDict, "VCMPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPPS));
        PyDict_SetItemString(opcodesDict, "VCMPSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPSD));
        PyDict_SetItemString(opcodesDict, "VCMPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPSS));
        PyDict_SetItemString(opcodesDict, "VCVTDQ2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTDQ2PD));
        PyDict_SetItemString(opcodesDict, "VCVTDQ2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTDQ2PS));
        PyDict_SetItemString(opcodesDict, "VCVTPD2DQX", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2DQX));
        PyDict_SetItemString(opcodesDict, "VCVTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2DQ));
        PyDict_SetItemString(opcodesDict, "VCVTPD2PSX", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2PSX));
        PyDict_SetItemString(opcodesDict, "VCVTPD2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2PS));
        PyDict_SetItemString(opcodesDict, "VCVTPD2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2UDQ));
        PyDict_SetItemString(opcodesDict, "VCVTPH2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPH2PS));
        PyDict_SetItemString(opcodesDict, "VCVTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2DQ));
        PyDict_SetItemString(opcodesDict, "VCVTPS2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2PD));
        PyDict_SetItemString(opcodesDict, "VCVTPS2PH", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2PH));
        PyDict_SetItemString(opcodesDict, "VCVTPS2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2UDQ));
        PyDict_SetItemString(opcodesDict, "VCVTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSD2SI));
        PyDict_SetItemString(opcodesDict, "VCVTSD2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSD2USI));
        PyDict_SetItemString(opcodesDict, "VCVTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSS2SI));
        PyDict_SetItemString(opcodesDict, "VCVTSS2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSS2USI));
        PyDict_SetItemString(opcodesDict, "VCVTTPD2DQX", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPD2DQX));
        PyDict_SetItemString(opcodesDict, "VCVTTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPD2DQ));
        PyDict_SetItemString(opcodesDict, "VCVTTPD2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPD2UDQ));
        PyDict_SetItemString(opcodesDict, "VCVTTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPS2DQ));
        PyDict_SetItemString(opcodesDict, "VCVTTPS2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPS2UDQ));
        PyDict_SetItemString(opcodesDict, "VCVTUDQ2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUDQ2PD));
        PyDict_SetItemString(opcodesDict, "VCVTUDQ2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUDQ2PS));
        PyDict_SetItemString(opcodesDict, "VDIVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVPD));
        PyDict_SetItemString(opcodesDict, "VDIVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVPS));
        PyDict_SetItemString(opcodesDict, "VDIVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVSD));
        PyDict_SetItemString(opcodesDict, "VDIVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVSS));
        PyDict_SetItemString(opcodesDict, "VDPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VDPPD));
        PyDict_SetItemString(opcodesDict, "VDPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VDPPS));
        PyDict_SetItemString(opcodesDict, "VERR", PyLong_FromUint32(triton::arch::x86::ID_INS_VERR));
        PyDict_SetItemString(opcodesDict, "VERW", PyLong_FromUint32(triton::arch::x86::ID_INS_VERW));
        PyDict_SetItemString(opcodesDict, "VEXTRACTF128", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTF128));
        PyDict_SetItemString(opcodesDict, "VEXTRACTF32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTF32X4));
        PyDict_SetItemString(opcodesDict, "VEXTRACTF64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTF64X4));
        PyDict_SetItemString(opcodesDict, "VEXTRACTI128", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTI128));
        PyDict_SetItemString(opcodesDict, "VEXTRACTI32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTI32X4));
        PyDict_SetItemString(opcodesDict, "VEXTRACTI64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTI64X4));
        PyDict_SetItemString(opcodesDict, "VEXTRACTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTPS));
        PyDict_SetItemString(opcodesDict, "VFMADD132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132PD));
        PyDict_SetItemString(opcodesDict, "VFMADD132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132PS));
        PyDict_SetItemString(opcodesDict, "VFMADD213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213PD));
        PyDict_SetItemString(opcodesDict, "VFMADD213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213PS));
        PyDict_SetItemString(opcodesDict, "VFMADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDPD));
        PyDict_SetItemString(opcodesDict, "VFMADD231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231PD));
        PyDict_SetItemString(opcodesDict, "VFMADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDPS));
        PyDict_SetItemString(opcodesDict, "VFMADD231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231PS));
        PyDict_SetItemString(opcodesDict, "VFMADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSD));
        PyDict_SetItemString(opcodesDict, "VFMADD213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213SD));
        PyDict_SetItemString(opcodesDict, "VFMADD132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132SD));
        PyDict_SetItemString(opcodesDict, "VFMADD231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231SD));
        PyDict_SetItemString(opcodesDict, "VFMADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSS));
        PyDict_SetItemString(opcodesDict, "VFMADD213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213SS));
        PyDict_SetItemString(opcodesDict, "VFMADD132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132SS));
        PyDict_SetItemString(opcodesDict, "VFMADD231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231SS));
        PyDict_SetItemString(opcodesDict, "VFMADDSUB132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB132PD));
        PyDict_SetItemString(opcodesDict, "VFMADDSUB132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB132PS));
        PyDict_SetItemString(opcodesDict, "VFMADDSUB213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB213PD));
        PyDict_SetItemString(opcodesDict, "VFMADDSUB213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB213PS));
        PyDict_SetItemString(opcodesDict, "VFMADDSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUBPD));
        PyDict_SetItemString(opcodesDict, "VFMADDSUB231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB231PD));
        PyDict_SetItemString(opcodesDict, "VFMADDSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUBPS));
        PyDict_SetItemString(opcodesDict, "VFMADDSUB231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB231PS));
        PyDict_SetItemString(opcodesDict, "VFMSUB132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132PD));
        PyDict_SetItemString(opcodesDict, "VFMSUB132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132PS));
        PyDict_SetItemString(opcodesDict, "VFMSUB213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213PD));
        PyDict_SetItemString(opcodesDict, "VFMSUB213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213PS));
        PyDict_SetItemString(opcodesDict, "VFMSUBADD132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD132PD));
        PyDict_SetItemString(opcodesDict, "VFMSUBADD132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD132PS));
        PyDict_SetItemString(opcodesDict, "VFMSUBADD213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD213PD));
        PyDict_SetItemString(opcodesDict, "VFMSUBADD213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD213PS));
        PyDict_SetItemString(opcodesDict, "VFMSUBADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADDPD));
        PyDict_SetItemString(opcodesDict, "VFMSUBADD231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD231PD));
        PyDict_SetItemString(opcodesDict, "VFMSUBADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADDPS));
        PyDict_SetItemString(opcodesDict, "VFMSUBADD231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD231PS));
        PyDict_SetItemString(opcodesDict, "VFMSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBPD));
        PyDict_SetItemString(opcodesDict, "VFMSUB231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231PD));
        PyDict_SetItemString(opcodesDict, "VFMSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBPS));
        PyDict_SetItemString(opcodesDict, "VFMSUB231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231PS));
        PyDict_SetItemString(opcodesDict, "VFMSUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBSD));
        PyDict_SetItemString(opcodesDict, "VFMSUB213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213SD));
        PyDict_SetItemString(opcodesDict, "VFMSUB132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132SD));
        PyDict_SetItemString(opcodesDict, "VFMSUB231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231SD));
        PyDict_SetItemString(opcodesDict, "VFMSUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBSS));
        PyDict_SetItemString(opcodesDict, "VFMSUB213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213SS));
        PyDict_SetItemString(opcodesDict, "VFMSUB132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132SS));
        PyDict_SetItemString(opcodesDict, "VFMSUB231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231SS));
        PyDict_SetItemString(opcodesDict, "VFNMADD132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132PD));
        PyDict_SetItemString(opcodesDict, "VFNMADD132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132PS));
        PyDict_SetItemString(opcodesDict, "VFNMADD213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213PD));
        PyDict_SetItemString(opcodesDict, "VFNMADD213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213PS));
        PyDict_SetItemString(opcodesDict, "VFNMADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDPD));
        PyDict_SetItemString(opcodesDict, "VFNMADD231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231PD));
        PyDict_SetItemString(opcodesDict, "VFNMADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDPS));
        PyDict_SetItemString(opcodesDict, "VFNMADD231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231PS));
        PyDict_SetItemString(opcodesDict, "VFNMADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDSD));
        PyDict_SetItemString(opcodesDict, "VFNMADD213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213SD));
        PyDict_SetItemString(opcodesDict, "VFNMADD132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132SD));
        PyDict_SetItemString(opcodesDict, "VFNMADD231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231SD));
        PyDict_SetItemString(opcodesDict, "VFNMADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDSS));
        PyDict_SetItemString(opcodesDict, "VFNMADD213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213SS));
        PyDict_SetItemString(opcodesDict, "VFNMADD132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132SS));
        PyDict_SetItemString(opcodesDict, "VFNMADD231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231SS));
        PyDict_SetItemString(opcodesDict, "VFNMSUB132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132PD));
        PyDict_SetItemString(opcodesDict, "VFNMSUB132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132PS));
        PyDict_SetItemString(opcodesDict, "VFNMSUB213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213PD));
        PyDict_SetItemString(opcodesDict, "VFNMSUB213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213PS));
        PyDict_SetItemString(opcodesDict, "VFNMSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBPD));
        PyDict_SetItemString(opcodesDict, "VFNMSUB231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231PD));
        PyDict_SetItemString(opcodesDict, "VFNMSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBPS));
        PyDict_SetItemString(opcodesDict, "VFNMSUB231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231PS));
        PyDict_SetItemString(opcodesDict, "VFNMSUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBSD));
        PyDict_SetItemString(opcodesDict, "VFNMSUB213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213SD));
        PyDict_SetItemString(opcodesDict, "VFNMSUB132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132SD));
        PyDict_SetItemString(opcodesDict, "VFNMSUB231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231SD));
        PyDict_SetItemString(opcodesDict, "VFNMSUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBSS));
        PyDict_SetItemString(opcodesDict, "VFNMSUB213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213SS));
        PyDict_SetItemString(opcodesDict, "VFNMSUB132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132SS));
        PyDict_SetItemString(opcodesDict, "VFNMSUB231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231SS));
        PyDict_SetItemString(opcodesDict, "VFRCZPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZPD));
        PyDict_SetItemString(opcodesDict, "VFRCZPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZPS));
        PyDict_SetItemString(opcodesDict, "VFRCZSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZSD));
        PyDict_SetItemString(opcodesDict, "VFRCZSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZSS));
        PyDict_SetItemString(opcodesDict, "VORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VORPD));
        PyDict_SetItemString(opcodesDict, "VORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VORPS));
        PyDict_SetItemString(opcodesDict, "VXORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VXORPD));
        PyDict_SetItemString(opcodesDict, "VXORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VXORPS));
        PyDict_SetItemString(opcodesDict, "VGATHERDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERDPD));
        PyDict_SetItemString(opcodesDict, "VGATHERDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERDPS));
        PyDict_SetItemString(opcodesDict, "VGATHERPF0DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0DPD));
        PyDict_SetItemString(opcodesDict, "VGATHERPF0DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0DPS));
        PyDict_SetItemString(opcodesDict, "VGATHERPF0QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0QPD));
        PyDict_SetItemString(opcodesDict, "VGATHERPF0QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0QPS));
        PyDict_SetItemString(opcodesDict, "VGATHERPF1DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1DPD));
        PyDict_SetItemString(opcodesDict, "VGATHERPF1DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1DPS));
        PyDict_SetItemString(opcodesDict, "VGATHERPF1QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1QPD));
        PyDict_SetItemString(opcodesDict, "VGATHERPF1QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1QPS));
        PyDict_SetItemString(opcodesDict, "VGATHERQPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERQPD));
        PyDict_SetItemString(opcodesDict, "VGATHERQPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERQPS));
        PyDict_SetItemString(opcodesDict, "VHADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VHADDPD));
        PyDict_SetItemString(opcodesDict, "VHADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VHADDPS));
        PyDict_SetItemString(opcodesDict, "VHSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VHSUBPD));
        PyDict_SetItemString(opcodesDict, "VHSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VHSUBPS));
        PyDict_SetItemString(opcodesDict, "VINSERTF128", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTF128));
        PyDict_SetItemString(opcodesDict, "VINSERTF32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTF32X4));
        PyDict_SetItemString(opcodesDict, "VINSERTF64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTF64X4));
        PyDict_SetItemString(opcodesDict, "VINSERTI128", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTI128));
        PyDict_SetItemString(opcodesDict, "VINSERTI32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTI32X4));
        PyDict_SetItemString(opcodesDict, "VINSERTI64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTI64X4));
        PyDict_SetItemString(opcodesDict, "VINSERTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTPS));
        PyDict_SetItemString(opcodesDict, "VLDDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_VLDDQU));
        PyDict_SetItemString(opcodesDict, "VLDMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_VLDMXCSR));
        PyDict_SetItemString(opcodesDict, "VMASKMOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_VMASKMOVDQU));
        PyDict_SetItemString(opcodesDict, "VMASKMOVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMASKMOVPD));
        PyDict_SetItemString(opcodesDict, "VMASKMOVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMASKMOVPS));
        PyDict_SetItemString(opcodesDict, "VMAXPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXPD));
        PyDict_SetItemString(opcodesDict, "VMAXPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXPS));
        PyDict_SetItemString(opcodesDict, "VMAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXSD));
        PyDict_SetItemString(opcodesDict, "VMAXSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXSS));
        PyDict_SetItemString(opcodesDict, "VMCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_VMCALL));
        PyDict_SetItemString(opcodesDict, "VMCLEAR", PyLong_FromUint32(triton::arch::x86::ID_INS_VMCLEAR));
        PyDict_SetItemString(opcodesDict, "VMFUNC", PyLong_FromUint32(triton::arch::x86::ID_INS_VMFUNC));
        PyDict_SetItemString(opcodesDict, "VMINPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINPD));
        PyDict_SetItemString(opcodesDict, "VMINPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINPS));
        PyDict_SetItemString(opcodesDict, "VMINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINSD));
        PyDict_SetItemString(opcodesDict, "VMINSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINSS));
        PyDict_SetItemString(opcodesDict, "VMLAUNCH", PyLong_FromUint32(triton::arch::x86::ID_INS_VMLAUNCH));
        PyDict_SetItemString(opcodesDict, "VMLOAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMLOAD));
        PyDict_SetItemString(opcodesDict, "VMMCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_VMMCALL));
        PyDict_SetItemString(opcodesDict, "VMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVQ));
        PyDict_SetItemString(opcodesDict, "VMOVDDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDDUP));
        PyDict_SetItemString(opcodesDict, "VMOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVD));
        PyDict_SetItemString(opcodesDict, "VMOVDQA32", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQA32));
        PyDict_SetItemString(opcodesDict, "VMOVDQA64", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQA64));
        PyDict_SetItemString(opcodesDict, "VMOVDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQA));
        PyDict_SetItemString(opcodesDict, "VMOVDQU16", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU16));
        PyDict_SetItemString(opcodesDict, "VMOVDQU32", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU32));
        PyDict_SetItemString(opcodesDict, "VMOVDQU64", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU64));
        PyDict_SetItemString(opcodesDict, "VMOVDQU8", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU8));
        PyDict_SetItemString(opcodesDict, "VMOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU));
        PyDict_SetItemString(opcodesDict, "VMOVHLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVHLPS));
        PyDict_SetItemString(opcodesDict, "VMOVHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVHPD));
        PyDict_SetItemString(opcodesDict, "VMOVHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVHPS));
        PyDict_SetItemString(opcodesDict, "VMOVLHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVLHPS));
        PyDict_SetItemString(opcodesDict, "VMOVLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVLPD));
        PyDict_SetItemString(opcodesDict, "VMOVLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVLPS));
        PyDict_SetItemString(opcodesDict, "VMOVMSKPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVMSKPD));
        PyDict_SetItemString(opcodesDict, "VMOVMSKPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVMSKPS));
        PyDict_SetItemString(opcodesDict, "VMOVNTDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTDQA));
        PyDict_SetItemString(opcodesDict, "VMOVNTDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTDQ));
        PyDict_SetItemString(opcodesDict, "VMOVNTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTPD));
        PyDict_SetItemString(opcodesDict, "VMOVNTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTPS));
        PyDict_SetItemString(opcodesDict, "VMOVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSD));
        PyDict_SetItemString(opcodesDict, "VMOVSHDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSHDUP));
        PyDict_SetItemString(opcodesDict, "VMOVSLDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSLDUP));
        PyDict_SetItemString(opcodesDict, "VMOVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSS));
        PyDict_SetItemString(opcodesDict, "VMOVUPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVUPD));
        PyDict_SetItemString(opcodesDict, "VMOVUPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVUPS));
        PyDict_SetItemString(opcodesDict, "VMPSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VMPSADBW));
        PyDict_SetItemString(opcodesDict, "VMPTRLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMPTRLD));
        PyDict_SetItemString(opcodesDict, "VMPTRST", PyLong_FromUint32(triton::arch::x86::ID_INS_VMPTRST));
        PyDict_SetItemString(opcodesDict, "VMREAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMREAD));
        PyDict_SetItemString(opcodesDict, "VMRESUME", PyLong_FromUint32(triton::arch::x86::ID_INS_VMRESUME));
        PyDict_SetItemString(opcodesDict, "VMRUN", PyLong_FromUint32(triton::arch::x86::ID_INS_VMRUN));
        PyDict_SetItemString(opcodesDict, "VMSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_VMSAVE));
        PyDict_SetItemString(opcodesDict, "VMULPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULPD));
        PyDict_SetItemString(opcodesDict, "VMULPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULPS));
        PyDict_SetItemString(opcodesDict, "VMULSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULSD));
        PyDict_SetItemString(opcodesDict, "VMULSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULSS));
        PyDict_SetItemString(opcodesDict, "VMWRITE", PyLong_FromUint32(triton::arch::x86::ID_INS_VMWRITE));
        PyDict_SetItemString(opcodesDict, "VMXOFF", PyLong_FromUint32(triton::arch::x86::ID_INS_VMXOFF));
        PyDict_SetItemString(opcodesDict, "VMXON", PyLong_FromUint32(triton::arch::x86::ID_INS_VMXON));
        PyDict_SetItemString(opcodesDict, "VPABSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSB));
        PyDict_SetItemString(opcodesDict, "VPABSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSD));
        PyDict_SetItemString(opcodesDict, "VPABSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSQ));
        PyDict_SetItemString(opcodesDict, "VPABSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSW));
        PyDict_SetItemString(opcodesDict, "VPACKSSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKSSDW));
        PyDict_SetItemString(opcodesDict, "VPACKSSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKSSWB));
        PyDict_SetItemString(opcodesDict, "VPACKUSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKUSDW));
        PyDict_SetItemString(opcodesDict, "VPACKUSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKUSWB));
        PyDict_SetItemString(opcodesDict, "VPADDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDB));
        PyDict_SetItemString(opcodesDict, "VPADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDD));
        PyDict_SetItemString(opcodesDict, "VPADDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDQ));
        PyDict_SetItemString(opcodesDict, "VPADDSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDSB));
        PyDict_SetItemString(opcodesDict, "VPADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDSW));
        PyDict_SetItemString(opcodesDict, "VPADDUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDUSB));
        PyDict_SetItemString(opcodesDict, "VPADDUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDUSW));
        PyDict_SetItemString(opcodesDict, "VPADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDW));
        PyDict_SetItemString(opcodesDict, "VPALIGNR", PyLong_FromUint32(triton::arch::x86::ID_INS_VPALIGNR));
        PyDict_SetItemString(opcodesDict, "VPANDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDD));
        PyDict_SetItemString(opcodesDict, "VPANDND", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDND));
        PyDict_SetItemString(opcodesDict, "VPANDNQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDNQ));
        PyDict_SetItemString(opcodesDict, "VPANDN", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDN));
        PyDict_SetItemString(opcodesDict, "VPANDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDQ));
        PyDict_SetItemString(opcodesDict, "VPAND", PyLong_FromUint32(triton::arch::x86::ID_INS_VPAND));
        PyDict_SetItemString(opcodesDict, "VPAVGB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPAVGB));
        PyDict_SetItemString(opcodesDict, "VPAVGW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPAVGW));
        PyDict_SetItemString(opcodesDict, "VPBLENDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDD));
        PyDict_SetItemString(opcodesDict, "VPBLENDMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDMD));
        PyDict_SetItemString(opcodesDict, "VPBLENDMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDMQ));
        PyDict_SetItemString(opcodesDict, "VPBLENDVB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDVB));
        PyDict_SetItemString(opcodesDict, "VPBLENDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDW));
        PyDict_SetItemString(opcodesDict, "VPBROADCASTB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTB));
        PyDict_SetItemString(opcodesDict, "VPBROADCASTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTD));
        PyDict_SetItemString(opcodesDict, "VPBROADCASTMB2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTMB2Q));
        PyDict_SetItemString(opcodesDict, "VPBROADCASTMW2D", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTMW2D));
        PyDict_SetItemString(opcodesDict, "VPBROADCASTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTQ));
        PyDict_SetItemString(opcodesDict, "VPBROADCASTW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTW));
        PyDict_SetItemString(opcodesDict, "VPCLMULQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCLMULQDQ));
        PyDict_SetItemString(opcodesDict, "VPCMOV", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMOV));
        PyDict_SetItemString(opcodesDict, "VPCMP", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMP));
        PyDict_SetItemString(opcodesDict, "VPCMPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPD));
        PyDict_SetItemString(opcodesDict, "VPCMPEQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQB));
        PyDict_SetItemString(opcodesDict, "VPCMPEQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQD));
        PyDict_SetItemString(opcodesDict, "VPCMPEQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQQ));
        PyDict_SetItemString(opcodesDict, "VPCMPEQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQW));
        PyDict_SetItemString(opcodesDict, "VPCMPESTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPESTRI));
        PyDict_SetItemString(opcodesDict, "VPCMPESTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPESTRM));
        PyDict_SetItemString(opcodesDict, "VPCMPGTB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTB));
        PyDict_SetItemString(opcodesDict, "VPCMPGTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTD));
        PyDict_SetItemString(opcodesDict, "VPCMPGTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTQ));
        PyDict_SetItemString(opcodesDict, "VPCMPGTW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTW));
        PyDict_SetItemString(opcodesDict, "VPCMPISTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPISTRI));
        PyDict_SetItemString(opcodesDict, "VPCMPISTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPISTRM));
        PyDict_SetItemString(opcodesDict, "VPCMPQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPQ));
        PyDict_SetItemString(opcodesDict, "VPCMPUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPUD));
        PyDict_SetItemString(opcodesDict, "VPCMPUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPUQ));
        PyDict_SetItemString(opcodesDict, "VPCOMB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMB));
        PyDict_SetItemString(opcodesDict, "VPCOMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMD));
        PyDict_SetItemString(opcodesDict, "VPCOMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMQ));
        PyDict_SetItemString(opcodesDict, "VPCOMUB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUB));
        PyDict_SetItemString(opcodesDict, "VPCOMUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUD));
        PyDict_SetItemString(opcodesDict, "VPCOMUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUQ));
        PyDict_SetItemString(opcodesDict, "VPCOMUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUW));
        PyDict_SetItemString(opcodesDict, "VPCOMW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMW));
        PyDict_SetItemString(opcodesDict, "VPCONFLICTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCONFLICTD));
        PyDict_SetItemString(opcodesDict, "VPCONFLICTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCONFLICTQ));
        PyDict_SetItemString(opcodesDict, "VPERM2F128", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERM2F128));
        PyDict_SetItemString(opcodesDict, "VPERM2I128", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERM2I128));
        PyDict_SetItemString(opcodesDict, "VPERMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMD));
        PyDict_SetItemString(opcodesDict, "VPERMI2D", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2D));
        PyDict_SetItemString(opcodesDict, "VPERMI2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2PD));
        PyDict_SetItemString(opcodesDict, "VPERMI2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2PS));
        PyDict_SetItemString(opcodesDict, "VPERMI2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2Q));
        PyDict_SetItemString(opcodesDict, "VPERMIL2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMIL2PD));
        PyDict_SetItemString(opcodesDict, "VPERMIL2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMIL2PS));
        PyDict_SetItemString(opcodesDict, "VPERMILPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMILPD));
        PyDict_SetItemString(opcodesDict, "VPERMILPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMILPS));
        PyDict_SetItemString(opcodesDict, "VPERMPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMPD));
        PyDict_SetItemString(opcodesDict, "VPERMPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMPS));
        PyDict_SetItemString(opcodesDict, "VPERMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMQ));
        PyDict_SetItemString(opcodesDict, "VPERMT2D", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2D));
        PyDict_SetItemString(opcodesDict, "VPERMT2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2PD));
        PyDict_SetItemString(opcodesDict, "VPERMT2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2PS));
        PyDict_SetItemString(opcodesDict, "VPERMT2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2Q));
        PyDict_SetItemString(opcodesDict, "VPEXTRB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRB));
        PyDict_SetItemString(opcodesDict, "VPEXTRD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRD));
        PyDict_SetItemString(opcodesDict, "VPEXTRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRQ));
        PyDict_SetItemString(opcodesDict, "VPEXTRW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRW));
        PyDict_SetItemString(opcodesDict, "VPGATHERDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERDD));
        PyDict_SetItemString(opcodesDict, "VPGATHERDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERDQ));
        PyDict_SetItemString(opcodesDict, "VPGATHERQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERQD));
        PyDict_SetItemString(opcodesDict, "VPGATHERQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERQQ));
        PyDict_SetItemString(opcodesDict, "VPHADDBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDBD));
        PyDict_SetItemString(opcodesDict, "VPHADDBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDBQ));
        PyDict_SetItemString(opcodesDict, "VPHADDBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDBW));
        PyDict_SetItemString(opcodesDict, "VPHADDDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDDQ));
        PyDict_SetItemString(opcodesDict, "VPHADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDD));
        PyDict_SetItemString(opcodesDict, "VPHADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDSW));
        PyDict_SetItemString(opcodesDict, "VPHADDUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUBD));
        PyDict_SetItemString(opcodesDict, "VPHADDUBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUBQ));
        PyDict_SetItemString(opcodesDict, "VPHADDUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUBW));
        PyDict_SetItemString(opcodesDict, "VPHADDUDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUDQ));
        PyDict_SetItemString(opcodesDict, "VPHADDUWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUWD));
        PyDict_SetItemString(opcodesDict, "VPHADDUWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUWQ));
        PyDict_SetItemString(opcodesDict, "VPHADDWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDWD));
        PyDict_SetItemString(opcodesDict, "VPHADDWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDWQ));
        PyDict_SetItemString(opcodesDict, "VPHADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDW));
        PyDict_SetItemString(opcodesDict, "VPHMINPOSUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHMINPOSUW));
        PyDict_SetItemString(opcodesDict, "VPHSUBBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBBW));
        PyDict_SetItemString(opcodesDict, "VPHSUBDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBDQ));
        PyDict_SetItemString(opcodesDict, "VPHSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBD));
        PyDict_SetItemString(opcodesDict, "VPHSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBSW));
        PyDict_SetItemString(opcodesDict, "VPHSUBWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBWD));
        PyDict_SetItemString(opcodesDict, "VPHSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBW));
        PyDict_SetItemString(opcodesDict, "VPINSRB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRB));
        PyDict_SetItemString(opcodesDict, "VPINSRD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRD));
        PyDict_SetItemString(opcodesDict, "VPINSRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRQ));
        PyDict_SetItemString(opcodesDict, "VPINSRW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRW));
        PyDict_SetItemString(opcodesDict, "VPLZCNTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPLZCNTD));
        PyDict_SetItemString(opcodesDict, "VPLZCNTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPLZCNTQ));
        PyDict_SetItemString(opcodesDict, "VPMACSDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSDD));
        PyDict_SetItemString(opcodesDict, "VPMACSDQH", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSDQH));
        PyDict_SetItemString(opcodesDict, "VPMACSDQL", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSDQL));
        PyDict_SetItemString(opcodesDict, "VPMACSSDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSDD));
        PyDict_SetItemString(opcodesDict, "VPMACSSDQH", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSDQH));
        PyDict_SetItemString(opcodesDict, "VPMACSSDQL", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSDQL));
        PyDict_SetItemString(opcodesDict, "VPMACSSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSWD));
        PyDict_SetItemString(opcodesDict, "VPMACSSWW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSWW));
        PyDict_SetItemString(opcodesDict, "VPMACSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSWD));
        PyDict_SetItemString(opcodesDict, "VPMACSWW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSWW));
        PyDict_SetItemString(opcodesDict, "VPMADCSSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADCSSWD));
        PyDict_SetItemString(opcodesDict, "VPMADCSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADCSWD));
        PyDict_SetItemString(opcodesDict, "VPMADDUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADDUBSW));
        PyDict_SetItemString(opcodesDict, "VPMADDWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADDWD));
        PyDict_SetItemString(opcodesDict, "VPMASKMOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMASKMOVD));
        PyDict_SetItemString(opcodesDict, "VPMASKMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMASKMOVQ));
        PyDict_SetItemString(opcodesDict, "VPMAXSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSB));
        PyDict_SetItemString(opcodesDict, "VPMAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSD));
        PyDict_SetItemString(opcodesDict, "VPMAXSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSQ));
        PyDict_SetItemString(opcodesDict, "VPMAXSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSW));
        PyDict_SetItemString(opcodesDict, "VPMAXUB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUB));
        PyDict_SetItemString(opcodesDict, "VPMAXUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUD));
        PyDict_SetItemString(opcodesDict, "VPMAXUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUQ));
        PyDict_SetItemString(opcodesDict, "VPMAXUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUW));
        PyDict_SetItemString(opcodesDict, "VPMINSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSB));
        PyDict_SetItemString(opcodesDict, "VPMINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSD));
        PyDict_SetItemString(opcodesDict, "VPMINSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSQ));
        PyDict_SetItemString(opcodesDict, "VPMINSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSW));
        PyDict_SetItemString(opcodesDict, "VPMINUB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUB));
        PyDict_SetItemString(opcodesDict, "VPMINUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUD));
        PyDict_SetItemString(opcodesDict, "VPMINUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUQ));
        PyDict_SetItemString(opcodesDict, "VPMINUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUW));
        PyDict_SetItemString(opcodesDict, "VPMOVDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVDB));
        PyDict_SetItemString(opcodesDict, "VPMOVDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVDW));
        PyDict_SetItemString(opcodesDict, "VPMOVMSKB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVMSKB));
        PyDict_SetItemString(opcodesDict, "VPMOVQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVQB));
        PyDict_SetItemString(opcodesDict, "VPMOVQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVQD));
        PyDict_SetItemString(opcodesDict, "VPMOVQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVQW));
        PyDict_SetItemString(opcodesDict, "VPMOVSDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSDB));
        PyDict_SetItemString(opcodesDict, "VPMOVSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSDW));
        PyDict_SetItemString(opcodesDict, "VPMOVSQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSQB));
        PyDict_SetItemString(opcodesDict, "VPMOVSQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSQD));
        PyDict_SetItemString(opcodesDict, "VPMOVSQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSQW));
        PyDict_SetItemString(opcodesDict, "VPMOVSXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXBD));
        PyDict_SetItemString(opcodesDict, "VPMOVSXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXBQ));
        PyDict_SetItemString(opcodesDict, "VPMOVSXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXBW));
        PyDict_SetItemString(opcodesDict, "VPMOVSXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXDQ));
        PyDict_SetItemString(opcodesDict, "VPMOVSXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXWD));
        PyDict_SetItemString(opcodesDict, "VPMOVSXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXWQ));
        PyDict_SetItemString(opcodesDict, "VPMOVUSDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSDB));
        PyDict_SetItemString(opcodesDict, "VPMOVUSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSDW));
        PyDict_SetItemString(opcodesDict, "VPMOVUSQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSQB));
        PyDict_SetItemString(opcodesDict, "VPMOVUSQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSQD));
        PyDict_SetItemString(opcodesDict, "VPMOVUSQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSQW));
        PyDict_SetItemString(opcodesDict, "VPMOVZXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXBD));
        PyDict_SetItemString(opcodesDict, "VPMOVZXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXBQ));
        PyDict_SetItemString(opcodesDict, "VPMOVZXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXBW));
        PyDict_SetItemString(opcodesDict, "VPMOVZXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXDQ));
        PyDict_SetItemString(opcodesDict, "VPMOVZXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXWD));
        PyDict_SetItemString(opcodesDict, "VPMOVZXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXWQ));
        PyDict_SetItemString(opcodesDict, "VPMULDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULDQ));
        PyDict_SetItemString(opcodesDict, "VPMULHRSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULHRSW));
        PyDict_SetItemString(opcodesDict, "VPMULHUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULHUW));
        PyDict_SetItemString(opcodesDict, "VPMULHW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULHW));
        PyDict_SetItemString(opcodesDict, "VPMULLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULLD));
        PyDict_SetItemString(opcodesDict, "VPMULLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULLW));
        PyDict_SetItemString(opcodesDict, "VPMULUDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULUDQ));
        PyDict_SetItemString(opcodesDict, "VPORD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPORD));
        PyDict_SetItemString(opcodesDict, "VPORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPORQ));
        PyDict_SetItemString(opcodesDict, "VPOR", PyLong_FromUint32(triton::arch::x86::ID_INS_VPOR));
        PyDict_SetItemString(opcodesDict, "VPPERM", PyLong_FromUint32(triton::arch::x86::ID_INS_VPPERM));
        PyDict_SetItemString(opcodesDict, "VPROTB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTB));
        PyDict_SetItemString(opcodesDict, "VPROTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTD));
        PyDict_SetItemString(opcodesDict, "VPROTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTQ));
        PyDict_SetItemString(opcodesDict, "VPROTW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTW));
        PyDict_SetItemString(opcodesDict, "VPSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSADBW));
        PyDict_SetItemString(opcodesDict, "VPSCATTERDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERDD));
        PyDict_SetItemString(opcodesDict, "VPSCATTERDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERDQ));
        PyDict_SetItemString(opcodesDict, "VPSCATTERQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERQD));
        PyDict_SetItemString(opcodesDict, "VPSCATTERQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERQQ));
        PyDict_SetItemString(opcodesDict, "VPSHAB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAB));
        PyDict_SetItemString(opcodesDict, "VPSHAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAD));
        PyDict_SetItemString(opcodesDict, "VPSHAQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAQ));
        PyDict_SetItemString(opcodesDict, "VPSHAW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAW));
        PyDict_SetItemString(opcodesDict, "VPSHLB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLB));
        PyDict_SetItemString(opcodesDict, "VPSHLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLD));
        PyDict_SetItemString(opcodesDict, "VPSHLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLQ));
        PyDict_SetItemString(opcodesDict, "VPSHLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLW));
        PyDict_SetItemString(opcodesDict, "VPSHUFB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFB));
        PyDict_SetItemString(opcodesDict, "VPSHUFD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFD));
        PyDict_SetItemString(opcodesDict, "VPSHUFHW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFHW));
        PyDict_SetItemString(opcodesDict, "VPSHUFLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFLW));
        PyDict_SetItemString(opcodesDict, "VPSIGNB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSIGNB));
        PyDict_SetItemString(opcodesDict, "VPSIGND", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSIGND));
        PyDict_SetItemString(opcodesDict, "VPSIGNW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSIGNW));
        PyDict_SetItemString(opcodesDict, "VPSLLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLDQ));
        PyDict_SetItemString(opcodesDict, "VPSLLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLD));
        PyDict_SetItemString(opcodesDict, "VPSLLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLQ));
        PyDict_SetItemString(opcodesDict, "VPSLLVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLVD));
        PyDict_SetItemString(opcodesDict, "VPSLLVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLVQ));
        PyDict_SetItemString(opcodesDict, "VPSLLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLW));
        PyDict_SetItemString(opcodesDict, "VPSRAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAD));
        PyDict_SetItemString(opcodesDict, "VPSRAQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAQ));
        PyDict_SetItemString(opcodesDict, "VPSRAVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAVD));
        PyDict_SetItemString(opcodesDict, "VPSRAVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAVQ));
        PyDict_SetItemString(opcodesDict, "VPSRAW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAW));
        PyDict_SetItemString(opcodesDict, "VPSRLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLDQ));
        PyDict_SetItemString(opcodesDict, "VPSRLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLD));
        PyDict_SetItemString(opcodesDict, "VPSRLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLQ));
        PyDict_SetItemString(opcodesDict, "VPSRLVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLVD));
        PyDict_SetItemString(opcodesDict, "VPSRLVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLVQ));
        PyDict_SetItemString(opcodesDict, "VPSRLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLW));
        PyDict_SetItemString(opcodesDict, "VPSUBB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBB));
        PyDict_SetItemString(opcodesDict, "VPSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBD));
        PyDict_SetItemString(opcodesDict, "VPSUBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBQ));
        PyDict_SetItemString(opcodesDict, "VPSUBSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBSB));
        PyDict_SetItemString(opcodesDict, "VPSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBSW));
        PyDict_SetItemString(opcodesDict, "VPSUBUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBUSB));
        PyDict_SetItemString(opcodesDict, "VPSUBUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBUSW));
        PyDict_SetItemString(opcodesDict, "VPSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBW));
        PyDict_SetItemString(opcodesDict, "VPTESTMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTMD));
        PyDict_SetItemString(opcodesDict, "VPTESTMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTMQ));
        PyDict_SetItemString(opcodesDict, "VPTESTNMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTNMD));
        PyDict_SetItemString(opcodesDict, "VPTESTNMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTNMQ));
        PyDict_SetItemString(opcodesDict, "VPTEST", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTEST));
        PyDict_SetItemString(opcodesDict, "VPUNPCKHBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHBW));
        PyDict_SetItemString(opcodesDict, "VPUNPCKHDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHDQ));
        PyDict_SetItemString(opcodesDict, "VPUNPCKHQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHQDQ));
        PyDict_SetItemString(opcodesDict, "VPUNPCKHWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHWD));
        PyDict_SetItemString(opcodesDict, "VPUNPCKLBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLBW));
        PyDict_SetItemString(opcodesDict, "VPUNPCKLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLDQ));
        PyDict_SetItemString(opcodesDict, "VPUNPCKLQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLQDQ));
        PyDict_SetItemString(opcodesDict, "VPUNPCKLWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLWD));
        PyDict_SetItemString(opcodesDict, "VPXORD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPXORD));
        PyDict_SetItemString(opcodesDict, "VPXORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPXORQ));
        PyDict_SetItemString(opcodesDict, "VPXOR", PyLong_FromUint32(triton::arch::x86::ID_INS_VPXOR));
        PyDict_SetItemString(opcodesDict, "VRCP14PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14PD));
        PyDict_SetItemString(opcodesDict, "VRCP14PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14PS));
        PyDict_SetItemString(opcodesDict, "VRCP14SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14SD));
        PyDict_SetItemString(opcodesDict, "VRCP14SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14SS));
        PyDict_SetItemString(opcodesDict, "VRCP28PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28PD));
        PyDict_SetItemString(opcodesDict, "VRCP28PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28PS));
        PyDict_SetItemString(opcodesDict, "VRCP28SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28SD));
        PyDict_SetItemString(opcodesDict, "VRCP28SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28SS));
        PyDict_SetItemString(opcodesDict, "VRCPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCPPS));
        PyDict_SetItemString(opcodesDict, "VRCPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCPSS));
        PyDict_SetItemString(opcodesDict, "VRNDSCALEPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALEPD));
        PyDict_SetItemString(opcodesDict, "VRNDSCALEPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALEPS));
        PyDict_SetItemString(opcodesDict, "VRNDSCALESD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALESD));
        PyDict_SetItemString(opcodesDict, "VRNDSCALESS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALESS));
        PyDict_SetItemString(opcodesDict, "VROUNDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDPD));
        PyDict_SetItemString(opcodesDict, "VROUNDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDPS));
        PyDict_SetItemString(opcodesDict, "VROUNDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDSD));
        PyDict_SetItemString(opcodesDict, "VROUNDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDSS));
        PyDict_SetItemString(opcodesDict, "VRSQRT14PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14PD));
        PyDict_SetItemString(opcodesDict, "VRSQRT14PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14PS));
        PyDict_SetItemString(opcodesDict, "VRSQRT14SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14SD));
        PyDict_SetItemString(opcodesDict, "VRSQRT14SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14SS));
        PyDict_SetItemString(opcodesDict, "VRSQRT28PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28PD));
        PyDict_SetItemString(opcodesDict, "VRSQRT28PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28PS));
        PyDict_SetItemString(opcodesDict, "VRSQRT28SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28SD));
        PyDict_SetItemString(opcodesDict, "VRSQRT28SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28SS));
        PyDict_SetItemString(opcodesDict, "VRSQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRTPS));
        PyDict_SetItemString(opcodesDict, "VRSQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRTSS));
        PyDict_SetItemString(opcodesDict, "VSCATTERDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERDPD));
        PyDict_SetItemString(opcodesDict, "VSCATTERDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERDPS));
        PyDict_SetItemString(opcodesDict, "VSCATTERPF0DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0DPD));
        PyDict_SetItemString(opcodesDict, "VSCATTERPF0DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0DPS));
        PyDict_SetItemString(opcodesDict, "VSCATTERPF0QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0QPD));
        PyDict_SetItemString(opcodesDict, "VSCATTERPF0QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0QPS));
        PyDict_SetItemString(opcodesDict, "VSCATTERPF1DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1DPD));
        PyDict_SetItemString(opcodesDict, "VSCATTERPF1DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1DPS));
        PyDict_SetItemString(opcodesDict, "VSCATTERPF1QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1QPD));
        PyDict_SetItemString(opcodesDict, "VSCATTERPF1QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1QPS));
        PyDict_SetItemString(opcodesDict, "VSCATTERQPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERQPD));
        PyDict_SetItemString(opcodesDict, "VSCATTERQPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERQPS));
        PyDict_SetItemString(opcodesDict, "VSHUFPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSHUFPD));
        PyDict_SetItemString(opcodesDict, "VSHUFPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSHUFPS));
        PyDict_SetItemString(opcodesDict, "VSQRTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTPD));
        PyDict_SetItemString(opcodesDict, "VSQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTPS));
        PyDict_SetItemString(opcodesDict, "VSQRTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTSD));
        PyDict_SetItemString(opcodesDict, "VSQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTSS));
        PyDict_SetItemString(opcodesDict, "VSTMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_VSTMXCSR));
        PyDict_SetItemString(opcodesDict, "VSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBPD));
        PyDict_SetItemString(opcodesDict, "VSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBPS));
        PyDict_SetItemString(opcodesDict, "VSUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBSD));
        PyDict_SetItemString(opcodesDict, "VSUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBSS));
        PyDict_SetItemString(opcodesDict, "VTESTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VTESTPD));
        PyDict_SetItemString(opcodesDict, "VTESTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VTESTPS));
        PyDict_SetItemString(opcodesDict, "VUNPCKHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKHPD));
        PyDict_SetItemString(opcodesDict, "VUNPCKHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKHPS));
        PyDict_SetItemString(opcodesDict, "VUNPCKLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKLPD));
        PyDict_SetItemString(opcodesDict, "VUNPCKLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKLPS));
        PyDict_SetItemString(opcodesDict, "VZEROALL", PyLong_FromUint32(triton::arch::x86::ID_INS_VZEROALL));
        PyDict_SetItemString(opcodesDict, "VZEROUPPER", PyLong_FromUint32(triton::arch::x86::ID_INS_VZEROUPPER));
        PyDict_SetItemString(opcodesDict, "WAIT", PyLong_FromUint32(triton::arch::x86::ID_INS_WAIT));
        PyDict_SetItemString(opcodesDict, "WBINVD", PyLong_FromUint32(triton::arch::x86::ID_INS_WBINVD));
        PyDict_SetItemString(opcodesDict, "WRFSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_WRFSBASE));
        PyDict_SetItemString(opcodesDict, "WRGSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_WRGSBASE));
        PyDict_SetItemString(opcodesDict, "WRMSR", PyLong_FromUint32(triton::arch::x86::ID_INS_WRMSR));
        PyDict_SetItemString(opcodesDict, "XABORT", PyLong_FromUint32(triton::arch::x86::ID_INS_XABORT));
        PyDict_SetItemString(opcodesDict, "XACQUIRE", PyLong_FromUint32(triton::arch::x86::ID_INS_XACQUIRE));
        PyDict_SetItemString(opcodesDict, "XBEGIN", PyLong_FromUint32(triton::arch::x86::ID_INS_XBEGIN));
        PyDict_SetItemString(opcodesDict, "XCHG", PyLong_FromUint32(triton::arch::x86::ID_INS_XCHG));
        PyDict_SetItemString(opcodesDict, "FXCH", PyLong_FromUint32(triton::arch::x86::ID_INS_FXCH));
        PyDict_SetItemString(opcodesDict, "XCRYPTCBC", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTCBC));
        PyDict_SetItemString(opcodesDict, "XCRYPTCFB", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTCFB));
        PyDict_SetItemString(opcodesDict, "XCRYPTCTR", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTCTR));
        PyDict_SetItemString(opcodesDict, "XCRYPTECB", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTECB));
        PyDict_SetItemString(opcodesDict, "XCRYPTOFB", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTOFB));
        PyDict_SetItemString(opcodesDict, "XEND", PyLong_FromUint32(triton::arch::x86::ID_INS_XEND));
        PyDict_SetItemString(opcodesDict, "XGETBV", PyLong_FromUint32(triton::arch::x86::ID_INS_XGETBV));
        PyDict_SetItemString(opcodesDict, "XLATB", PyLong_FromUint32(triton::arch::x86::ID_INS_XLATB));
        PyDict_SetItemString(opcodesDict, "XRELEASE", PyLong_FromUint32(triton::arch::x86::ID_INS_XRELEASE));
        PyDict_SetItemString(opcodesDict, "XRSTOR", PyLong_FromUint32(triton::arch::x86::ID_INS_XRSTOR));
        PyDict_SetItemString(opcodesDict, "XRSTOR64", PyLong_FromUint32(triton::arch::x86::ID_INS_XRSTOR64));
        PyDict_SetItemString(opcodesDict, "XSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVE));
        PyDict_SetItemString(opcodesDict, "XSAVE64", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVE64));
        PyDict_SetItemString(opcodesDict, "XSAVEOPT", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVEOPT));
        PyDict_SetItemString(opcodesDict, "XSAVEOPT64", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVEOPT64));
        PyDict_SetItemString(opcodesDict, "XSETBV", PyLong_FromUint32(triton::arch::x86::ID_INS_XSETBV));
        PyDict_SetItemString(opcodesDict, "XSHA1", PyLong_FromUint32(triton::arch::x86::ID_INS_XSHA1));
        PyDict_SetItemString(opcodesDict, "XSHA256", PyLong_FromUint32(triton::arch::x86::ID_INS_XSHA256));
        PyDict_SetItemString(opcodesDict, "XSTORE", PyLong_FromUint32(triton::arch::x86::ID_INS_XSTORE));
        PyDict_SetItemString(opcodesDict, "XTEST", PyLong_FromUint32(triton::arch::x86::ID_INS_XTEST));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
