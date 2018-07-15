//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/pythonXFunctions.hpp>
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

#ifdef IS_PY3
      NAMESPACE_TYPE(OPCODE, OpcodeNamespace)

      PyObject *initX86OpcodesNamespace() {
        PyType_Ready(&OpcodeNamespace_Type);
        PyObject *opcodesDict = OpcodeNamespace_Type.tp_dict;
#else
      void initX86OpcodesNamespace(PyObject* opcodesDict) {
        PyDict_Clear(opcodesDict);
#endif

        xPyDict_SetItemString(opcodesDict, "INVALID", PyLong_FromUint32(triton::arch::x86::ID_INST_INVALID));
        xPyDict_SetItemString(opcodesDict, "AAA", PyLong_FromUint32(triton::arch::x86::ID_INS_AAA));
        xPyDict_SetItemString(opcodesDict, "AAD", PyLong_FromUint32(triton::arch::x86::ID_INS_AAD));
        xPyDict_SetItemString(opcodesDict, "AAM", PyLong_FromUint32(triton::arch::x86::ID_INS_AAM));
        xPyDict_SetItemString(opcodesDict, "AAS", PyLong_FromUint32(triton::arch::x86::ID_INS_AAS));
        xPyDict_SetItemString(opcodesDict, "FABS", PyLong_FromUint32(triton::arch::x86::ID_INS_FABS));
        xPyDict_SetItemString(opcodesDict, "ADC", PyLong_FromUint32(triton::arch::x86::ID_INS_ADC));
        xPyDict_SetItemString(opcodesDict, "ADCX", PyLong_FromUint32(triton::arch::x86::ID_INS_ADCX));
        xPyDict_SetItemString(opcodesDict, "ADD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADD));
        xPyDict_SetItemString(opcodesDict, "ADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDPD));
        xPyDict_SetItemString(opcodesDict, "ADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDPS));
        xPyDict_SetItemString(opcodesDict, "ADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSD));
        xPyDict_SetItemString(opcodesDict, "ADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSS));
        xPyDict_SetItemString(opcodesDict, "ADDSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSUBPD));
        xPyDict_SetItemString(opcodesDict, "ADDSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSUBPS));
        xPyDict_SetItemString(opcodesDict, "FADD", PyLong_FromUint32(triton::arch::x86::ID_INS_FADD));
        xPyDict_SetItemString(opcodesDict, "FIADD", PyLong_FromUint32(triton::arch::x86::ID_INS_FIADD));
        xPyDict_SetItemString(opcodesDict, "FADDP", PyLong_FromUint32(triton::arch::x86::ID_INS_FADDP));
        xPyDict_SetItemString(opcodesDict, "ADOX", PyLong_FromUint32(triton::arch::x86::ID_INS_ADOX));
        xPyDict_SetItemString(opcodesDict, "AESDECLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_AESDECLAST));
        xPyDict_SetItemString(opcodesDict, "AESDEC", PyLong_FromUint32(triton::arch::x86::ID_INS_AESDEC));
        xPyDict_SetItemString(opcodesDict, "AESENCLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_AESENCLAST));
        xPyDict_SetItemString(opcodesDict, "AESENC", PyLong_FromUint32(triton::arch::x86::ID_INS_AESENC));
        xPyDict_SetItemString(opcodesDict, "AESIMC", PyLong_FromUint32(triton::arch::x86::ID_INS_AESIMC));
        xPyDict_SetItemString(opcodesDict, "AESKEYGENASSIST", PyLong_FromUint32(triton::arch::x86::ID_INS_AESKEYGENASSIST));
        xPyDict_SetItemString(opcodesDict, "AND", PyLong_FromUint32(triton::arch::x86::ID_INS_AND));
        xPyDict_SetItemString(opcodesDict, "ANDN", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDN));
        xPyDict_SetItemString(opcodesDict, "ANDNPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDNPD));
        xPyDict_SetItemString(opcodesDict, "ANDNPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDNPS));
        xPyDict_SetItemString(opcodesDict, "ANDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDPD));
        xPyDict_SetItemString(opcodesDict, "ANDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDPS));
        xPyDict_SetItemString(opcodesDict, "ARPL", PyLong_FromUint32(triton::arch::x86::ID_INS_ARPL));
        xPyDict_SetItemString(opcodesDict, "BEXTR", PyLong_FromUint32(triton::arch::x86::ID_INS_BEXTR));
        xPyDict_SetItemString(opcodesDict, "BLCFILL", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCFILL));
        xPyDict_SetItemString(opcodesDict, "BLCI", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCI));
        xPyDict_SetItemString(opcodesDict, "BLCIC", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCIC));
        xPyDict_SetItemString(opcodesDict, "BLCMSK", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCMSK));
        xPyDict_SetItemString(opcodesDict, "BLCS", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCS));
        xPyDict_SetItemString(opcodesDict, "BLENDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDPD));
        xPyDict_SetItemString(opcodesDict, "BLENDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDPS));
        xPyDict_SetItemString(opcodesDict, "BLENDVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDVPD));
        xPyDict_SetItemString(opcodesDict, "BLENDVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDVPS));
        xPyDict_SetItemString(opcodesDict, "BLSFILL", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSFILL));
        xPyDict_SetItemString(opcodesDict, "BLSI", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSI));
        xPyDict_SetItemString(opcodesDict, "BLSIC", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSIC));
        xPyDict_SetItemString(opcodesDict, "BLSMSK", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSMSK));
        xPyDict_SetItemString(opcodesDict, "BLSR", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSR));
        xPyDict_SetItemString(opcodesDict, "BOUND", PyLong_FromUint32(triton::arch::x86::ID_INS_BOUND));
        xPyDict_SetItemString(opcodesDict, "BSF", PyLong_FromUint32(triton::arch::x86::ID_INS_BSF));
        xPyDict_SetItemString(opcodesDict, "BSR", PyLong_FromUint32(triton::arch::x86::ID_INS_BSR));
        xPyDict_SetItemString(opcodesDict, "BSWAP", PyLong_FromUint32(triton::arch::x86::ID_INS_BSWAP));
        xPyDict_SetItemString(opcodesDict, "BT", PyLong_FromUint32(triton::arch::x86::ID_INS_BT));
        xPyDict_SetItemString(opcodesDict, "BTC", PyLong_FromUint32(triton::arch::x86::ID_INS_BTC));
        xPyDict_SetItemString(opcodesDict, "BTR", PyLong_FromUint32(triton::arch::x86::ID_INS_BTR));
        xPyDict_SetItemString(opcodesDict, "BTS", PyLong_FromUint32(triton::arch::x86::ID_INS_BTS));
        xPyDict_SetItemString(opcodesDict, "BZHI", PyLong_FromUint32(triton::arch::x86::ID_INS_BZHI));
        xPyDict_SetItemString(opcodesDict, "CALL", PyLong_FromUint32(triton::arch::x86::ID_INS_CALL));
        xPyDict_SetItemString(opcodesDict, "CBW", PyLong_FromUint32(triton::arch::x86::ID_INS_CBW));
        xPyDict_SetItemString(opcodesDict, "CDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CDQ));
        xPyDict_SetItemString(opcodesDict, "CDQE", PyLong_FromUint32(triton::arch::x86::ID_INS_CDQE));
        xPyDict_SetItemString(opcodesDict, "FCHS", PyLong_FromUint32(triton::arch::x86::ID_INS_FCHS));
        xPyDict_SetItemString(opcodesDict, "CLAC", PyLong_FromUint32(triton::arch::x86::ID_INS_CLAC));
        xPyDict_SetItemString(opcodesDict, "CLC", PyLong_FromUint32(triton::arch::x86::ID_INS_CLC));
        xPyDict_SetItemString(opcodesDict, "CLD", PyLong_FromUint32(triton::arch::x86::ID_INS_CLD));
        xPyDict_SetItemString(opcodesDict, "CLFLUSH", PyLong_FromUint32(triton::arch::x86::ID_INS_CLFLUSH));
        xPyDict_SetItemString(opcodesDict, "CLGI", PyLong_FromUint32(triton::arch::x86::ID_INS_CLGI));
        xPyDict_SetItemString(opcodesDict, "CLI", PyLong_FromUint32(triton::arch::x86::ID_INS_CLI));
        xPyDict_SetItemString(opcodesDict, "CLTS", PyLong_FromUint32(triton::arch::x86::ID_INS_CLTS));
        xPyDict_SetItemString(opcodesDict, "CMC", PyLong_FromUint32(triton::arch::x86::ID_INS_CMC));
        xPyDict_SetItemString(opcodesDict, "CMOVA", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVA));
        xPyDict_SetItemString(opcodesDict, "CMOVAE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVAE));
        xPyDict_SetItemString(opcodesDict, "CMOVB", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVB));
        xPyDict_SetItemString(opcodesDict, "CMOVBE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVBE));
        xPyDict_SetItemString(opcodesDict, "FCMOVBE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVBE));
        xPyDict_SetItemString(opcodesDict, "FCMOVB", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVB));
        xPyDict_SetItemString(opcodesDict, "CMOVE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVE));
        xPyDict_SetItemString(opcodesDict, "FCMOVE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVE));
        xPyDict_SetItemString(opcodesDict, "CMOVG", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVG));
        xPyDict_SetItemString(opcodesDict, "CMOVGE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVGE));
        xPyDict_SetItemString(opcodesDict, "CMOVL", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVL));
        xPyDict_SetItemString(opcodesDict, "CMOVLE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVLE));
        xPyDict_SetItemString(opcodesDict, "FCMOVNBE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNBE));
        xPyDict_SetItemString(opcodesDict, "FCMOVNB", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNB));
        xPyDict_SetItemString(opcodesDict, "CMOVNE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNE));
        xPyDict_SetItemString(opcodesDict, "FCMOVNE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNE));
        xPyDict_SetItemString(opcodesDict, "CMOVNO", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNO));
        xPyDict_SetItemString(opcodesDict, "CMOVNP", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNP));
        xPyDict_SetItemString(opcodesDict, "FCMOVNU", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNU));
        xPyDict_SetItemString(opcodesDict, "CMOVNS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNS));
        xPyDict_SetItemString(opcodesDict, "CMOVO", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVO));
        xPyDict_SetItemString(opcodesDict, "CMOVP", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVP));
        xPyDict_SetItemString(opcodesDict, "FCMOVU", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVU));
        xPyDict_SetItemString(opcodesDict, "CMOVS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVS));
        xPyDict_SetItemString(opcodesDict, "CMP", PyLong_FromUint32(triton::arch::x86::ID_INS_CMP));
        xPyDict_SetItemString(opcodesDict, "CMPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPPD));
        xPyDict_SetItemString(opcodesDict, "CMPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPPS));
        xPyDict_SetItemString(opcodesDict, "CMPSB", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSB));
        xPyDict_SetItemString(opcodesDict, "CMPSD", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSD));
        xPyDict_SetItemString(opcodesDict, "CMPSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSQ));
        xPyDict_SetItemString(opcodesDict, "CMPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSS));
        xPyDict_SetItemString(opcodesDict, "CMPSW", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSW));
        xPyDict_SetItemString(opcodesDict, "CMPXCHG16B", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPXCHG16B));
        xPyDict_SetItemString(opcodesDict, "CMPXCHG", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPXCHG));
        xPyDict_SetItemString(opcodesDict, "CMPXCHG8B", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPXCHG8B));
        xPyDict_SetItemString(opcodesDict, "COMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_COMISD));
        xPyDict_SetItemString(opcodesDict, "COMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_COMISS));
        xPyDict_SetItemString(opcodesDict, "FCOMP", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMP));
        xPyDict_SetItemString(opcodesDict, "FCOMPI", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMPI));
        xPyDict_SetItemString(opcodesDict, "FCOMI", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMI));
        xPyDict_SetItemString(opcodesDict, "FCOM", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOM));
        xPyDict_SetItemString(opcodesDict, "FCOS", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOS));
        xPyDict_SetItemString(opcodesDict, "CPUID", PyLong_FromUint32(triton::arch::x86::ID_INS_CPUID));
        xPyDict_SetItemString(opcodesDict, "CQO", PyLong_FromUint32(triton::arch::x86::ID_INS_CQO));
        xPyDict_SetItemString(opcodesDict, "CRC32", PyLong_FromUint32(triton::arch::x86::ID_INS_CRC32));
        xPyDict_SetItemString(opcodesDict, "CVTDQ2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTDQ2PD));
        xPyDict_SetItemString(opcodesDict, "CVTDQ2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTDQ2PS));
        xPyDict_SetItemString(opcodesDict, "CVTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPD2DQ));
        xPyDict_SetItemString(opcodesDict, "CVTPD2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPD2PS));
        xPyDict_SetItemString(opcodesDict, "CVTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPS2DQ));
        xPyDict_SetItemString(opcodesDict, "CVTPS2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPS2PD));
        xPyDict_SetItemString(opcodesDict, "CVTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSD2SI));
        xPyDict_SetItemString(opcodesDict, "CVTSD2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSD2SS));
        xPyDict_SetItemString(opcodesDict, "CVTSI2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSI2SD));
        xPyDict_SetItemString(opcodesDict, "CVTSI2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSI2SS));
        xPyDict_SetItemString(opcodesDict, "CVTSS2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSS2SD));
        xPyDict_SetItemString(opcodesDict, "CVTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSS2SI));
        xPyDict_SetItemString(opcodesDict, "CVTTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPD2DQ));
        xPyDict_SetItemString(opcodesDict, "CVTTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPS2DQ));
        xPyDict_SetItemString(opcodesDict, "CVTTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTSD2SI));
        xPyDict_SetItemString(opcodesDict, "CVTTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTSS2SI));
        xPyDict_SetItemString(opcodesDict, "CWD", PyLong_FromUint32(triton::arch::x86::ID_INS_CWD));
        xPyDict_SetItemString(opcodesDict, "CWDE", PyLong_FromUint32(triton::arch::x86::ID_INS_CWDE));
        xPyDict_SetItemString(opcodesDict, "DAA", PyLong_FromUint32(triton::arch::x86::ID_INS_DAA));
        xPyDict_SetItemString(opcodesDict, "DAS", PyLong_FromUint32(triton::arch::x86::ID_INS_DAS));
        xPyDict_SetItemString(opcodesDict, "DATA16", PyLong_FromUint32(triton::arch::x86::ID_INS_DATA16));
        xPyDict_SetItemString(opcodesDict, "DEC", PyLong_FromUint32(triton::arch::x86::ID_INS_DEC));
        xPyDict_SetItemString(opcodesDict, "DIV", PyLong_FromUint32(triton::arch::x86::ID_INS_DIV));
        xPyDict_SetItemString(opcodesDict, "DIVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVPD));
        xPyDict_SetItemString(opcodesDict, "DIVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVPS));
        xPyDict_SetItemString(opcodesDict, "FDIVR", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIVR));
        xPyDict_SetItemString(opcodesDict, "FIDIVR", PyLong_FromUint32(triton::arch::x86::ID_INS_FIDIVR));
        xPyDict_SetItemString(opcodesDict, "FDIVRP", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIVRP));
        xPyDict_SetItemString(opcodesDict, "DIVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVSD));
        xPyDict_SetItemString(opcodesDict, "DIVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVSS));
        xPyDict_SetItemString(opcodesDict, "FDIV", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIV));
        xPyDict_SetItemString(opcodesDict, "FIDIV", PyLong_FromUint32(triton::arch::x86::ID_INS_FIDIV));
        xPyDict_SetItemString(opcodesDict, "FDIVP", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIVP));
        xPyDict_SetItemString(opcodesDict, "DPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_DPPD));
        xPyDict_SetItemString(opcodesDict, "DPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_DPPS));
        xPyDict_SetItemString(opcodesDict, "RET", PyLong_FromUint32(triton::arch::x86::ID_INS_RET));
        xPyDict_SetItemString(opcodesDict, "ENCLS", PyLong_FromUint32(triton::arch::x86::ID_INS_ENCLS));
        xPyDict_SetItemString(opcodesDict, "ENCLU", PyLong_FromUint32(triton::arch::x86::ID_INS_ENCLU));
        xPyDict_SetItemString(opcodesDict, "ENTER", PyLong_FromUint32(triton::arch::x86::ID_INS_ENTER));
        xPyDict_SetItemString(opcodesDict, "EXTRACTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_EXTRACTPS));
        xPyDict_SetItemString(opcodesDict, "EXTRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_EXTRQ));
        xPyDict_SetItemString(opcodesDict, "F2XM1", PyLong_FromUint32(triton::arch::x86::ID_INS_F2XM1));
        xPyDict_SetItemString(opcodesDict, "LCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_LCALL));
        xPyDict_SetItemString(opcodesDict, "LJMP", PyLong_FromUint32(triton::arch::x86::ID_INS_LJMP));
        xPyDict_SetItemString(opcodesDict, "FBLD", PyLong_FromUint32(triton::arch::x86::ID_INS_FBLD));
        xPyDict_SetItemString(opcodesDict, "FBSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FBSTP));
        xPyDict_SetItemString(opcodesDict, "FCOMPP", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMPP));
        xPyDict_SetItemString(opcodesDict, "FDECSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FDECSTP));
        xPyDict_SetItemString(opcodesDict, "FEMMS", PyLong_FromUint32(triton::arch::x86::ID_INS_FEMMS));
        xPyDict_SetItemString(opcodesDict, "FFREE", PyLong_FromUint32(triton::arch::x86::ID_INS_FFREE));
        xPyDict_SetItemString(opcodesDict, "FICOM", PyLong_FromUint32(triton::arch::x86::ID_INS_FICOM));
        xPyDict_SetItemString(opcodesDict, "FICOMP", PyLong_FromUint32(triton::arch::x86::ID_INS_FICOMP));
        xPyDict_SetItemString(opcodesDict, "FINCSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FINCSTP));
        xPyDict_SetItemString(opcodesDict, "FLDCW", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDCW));
        xPyDict_SetItemString(opcodesDict, "FLDENV", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDENV));
        xPyDict_SetItemString(opcodesDict, "FLDL2E", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDL2E));
        xPyDict_SetItemString(opcodesDict, "FLDL2T", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDL2T));
        xPyDict_SetItemString(opcodesDict, "FLDLG2", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDLG2));
        xPyDict_SetItemString(opcodesDict, "FLDLN2", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDLN2));
        xPyDict_SetItemString(opcodesDict, "FLDPI", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDPI));
        xPyDict_SetItemString(opcodesDict, "FNCLEX", PyLong_FromUint32(triton::arch::x86::ID_INS_FNCLEX));
        xPyDict_SetItemString(opcodesDict, "FNINIT", PyLong_FromUint32(triton::arch::x86::ID_INS_FNINIT));
        xPyDict_SetItemString(opcodesDict, "FNOP", PyLong_FromUint32(triton::arch::x86::ID_INS_FNOP));
        xPyDict_SetItemString(opcodesDict, "FNSTCW", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSTCW));
        xPyDict_SetItemString(opcodesDict, "FNSTSW", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSTSW));
        xPyDict_SetItemString(opcodesDict, "FPATAN", PyLong_FromUint32(triton::arch::x86::ID_INS_FPATAN));
        xPyDict_SetItemString(opcodesDict, "FPREM", PyLong_FromUint32(triton::arch::x86::ID_INS_FPREM));
        xPyDict_SetItemString(opcodesDict, "FPREM1", PyLong_FromUint32(triton::arch::x86::ID_INS_FPREM1));
        xPyDict_SetItemString(opcodesDict, "FPTAN", PyLong_FromUint32(triton::arch::x86::ID_INS_FPTAN));
        xPyDict_SetItemString(opcodesDict, "FRNDINT", PyLong_FromUint32(triton::arch::x86::ID_INS_FRNDINT));
        xPyDict_SetItemString(opcodesDict, "FRSTOR", PyLong_FromUint32(triton::arch::x86::ID_INS_FRSTOR));
        xPyDict_SetItemString(opcodesDict, "FNSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSAVE));
        xPyDict_SetItemString(opcodesDict, "FSCALE", PyLong_FromUint32(triton::arch::x86::ID_INS_FSCALE));
        xPyDict_SetItemString(opcodesDict, "FSETPM", PyLong_FromUint32(triton::arch::x86::ID_INS_FSETPM));
        xPyDict_SetItemString(opcodesDict, "FSINCOS", PyLong_FromUint32(triton::arch::x86::ID_INS_FSINCOS));
        xPyDict_SetItemString(opcodesDict, "FNSTENV", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSTENV));
        xPyDict_SetItemString(opcodesDict, "FXAM", PyLong_FromUint32(triton::arch::x86::ID_INS_FXAM));
        xPyDict_SetItemString(opcodesDict, "FXRSTOR", PyLong_FromUint32(triton::arch::x86::ID_INS_FXRSTOR));
        xPyDict_SetItemString(opcodesDict, "FXRSTOR64", PyLong_FromUint32(triton::arch::x86::ID_INS_FXRSTOR64));
        xPyDict_SetItemString(opcodesDict, "FXSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_FXSAVE));
        xPyDict_SetItemString(opcodesDict, "FXSAVE64", PyLong_FromUint32(triton::arch::x86::ID_INS_FXSAVE64));
        xPyDict_SetItemString(opcodesDict, "FXTRACT", PyLong_FromUint32(triton::arch::x86::ID_INS_FXTRACT));
        xPyDict_SetItemString(opcodesDict, "FYL2X", PyLong_FromUint32(triton::arch::x86::ID_INS_FYL2X));
        xPyDict_SetItemString(opcodesDict, "FYL2XP1", PyLong_FromUint32(triton::arch::x86::ID_INS_FYL2XP1));
        xPyDict_SetItemString(opcodesDict, "MOVAPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVAPD));
        xPyDict_SetItemString(opcodesDict, "MOVAPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVAPS));
        xPyDict_SetItemString(opcodesDict, "ORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ORPD));
        xPyDict_SetItemString(opcodesDict, "ORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ORPS));
        xPyDict_SetItemString(opcodesDict, "VMOVAPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVAPD));
        xPyDict_SetItemString(opcodesDict, "VMOVAPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVAPS));
        xPyDict_SetItemString(opcodesDict, "XORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_XORPD));
        xPyDict_SetItemString(opcodesDict, "XORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_XORPS));
        xPyDict_SetItemString(opcodesDict, "GETSEC", PyLong_FromUint32(triton::arch::x86::ID_INS_GETSEC));
        xPyDict_SetItemString(opcodesDict, "HADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_HADDPD));
        xPyDict_SetItemString(opcodesDict, "HADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_HADDPS));
        xPyDict_SetItemString(opcodesDict, "HLT", PyLong_FromUint32(triton::arch::x86::ID_INS_HLT));
        xPyDict_SetItemString(opcodesDict, "HSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_HSUBPD));
        xPyDict_SetItemString(opcodesDict, "HSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_HSUBPS));
        xPyDict_SetItemString(opcodesDict, "IDIV", PyLong_FromUint32(triton::arch::x86::ID_INS_IDIV));
        xPyDict_SetItemString(opcodesDict, "FILD", PyLong_FromUint32(triton::arch::x86::ID_INS_FILD));
        xPyDict_SetItemString(opcodesDict, "IMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_IMUL));
        xPyDict_SetItemString(opcodesDict, "IN", PyLong_FromUint32(triton::arch::x86::ID_INS_IN));
        xPyDict_SetItemString(opcodesDict, "INC", PyLong_FromUint32(triton::arch::x86::ID_INS_INC));
        xPyDict_SetItemString(opcodesDict, "INSB", PyLong_FromUint32(triton::arch::x86::ID_INS_INSB));
        xPyDict_SetItemString(opcodesDict, "INSERTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_INSERTPS));
        xPyDict_SetItemString(opcodesDict, "INSERTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_INSERTQ));
        xPyDict_SetItemString(opcodesDict, "INSD", PyLong_FromUint32(triton::arch::x86::ID_INS_INSD));
        xPyDict_SetItemString(opcodesDict, "INSW", PyLong_FromUint32(triton::arch::x86::ID_INS_INSW));
        xPyDict_SetItemString(opcodesDict, "INT", PyLong_FromUint32(triton::arch::x86::ID_INS_INT));
        xPyDict_SetItemString(opcodesDict, "INT1", PyLong_FromUint32(triton::arch::x86::ID_INS_INT1));
        xPyDict_SetItemString(opcodesDict, "INT3", PyLong_FromUint32(triton::arch::x86::ID_INS_INT3));
        xPyDict_SetItemString(opcodesDict, "INTO", PyLong_FromUint32(triton::arch::x86::ID_INS_INTO));
        xPyDict_SetItemString(opcodesDict, "INVD", PyLong_FromUint32(triton::arch::x86::ID_INS_INVD));
        xPyDict_SetItemString(opcodesDict, "INVEPT", PyLong_FromUint32(triton::arch::x86::ID_INS_INVEPT));
        xPyDict_SetItemString(opcodesDict, "INVLPG", PyLong_FromUint32(triton::arch::x86::ID_INS_INVLPG));
        xPyDict_SetItemString(opcodesDict, "INVLPGA", PyLong_FromUint32(triton::arch::x86::ID_INS_INVLPGA));
        xPyDict_SetItemString(opcodesDict, "INVPCID", PyLong_FromUint32(triton::arch::x86::ID_INS_INVPCID));
        xPyDict_SetItemString(opcodesDict, "INVVPID", PyLong_FromUint32(triton::arch::x86::ID_INS_INVVPID));
        xPyDict_SetItemString(opcodesDict, "IRET", PyLong_FromUint32(triton::arch::x86::ID_INS_IRET));
        xPyDict_SetItemString(opcodesDict, "IRETD", PyLong_FromUint32(triton::arch::x86::ID_INS_IRETD));
        xPyDict_SetItemString(opcodesDict, "IRETQ", PyLong_FromUint32(triton::arch::x86::ID_INS_IRETQ));
        xPyDict_SetItemString(opcodesDict, "FISTTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FISTTP));
        xPyDict_SetItemString(opcodesDict, "FIST", PyLong_FromUint32(triton::arch::x86::ID_INS_FIST));
        xPyDict_SetItemString(opcodesDict, "FISTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FISTP));
        xPyDict_SetItemString(opcodesDict, "UCOMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_UCOMISD));
        xPyDict_SetItemString(opcodesDict, "UCOMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_UCOMISS));
        xPyDict_SetItemString(opcodesDict, "VCMP", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMP));
        xPyDict_SetItemString(opcodesDict, "VCOMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCOMISD));
        xPyDict_SetItemString(opcodesDict, "VCOMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCOMISS));
        xPyDict_SetItemString(opcodesDict, "VCVTSD2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSD2SS));
        xPyDict_SetItemString(opcodesDict, "VCVTSI2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSI2SD));
        xPyDict_SetItemString(opcodesDict, "VCVTSI2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSI2SS));
        xPyDict_SetItemString(opcodesDict, "VCVTSS2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSS2SD));
        xPyDict_SetItemString(opcodesDict, "VCVTTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSD2SI));
        xPyDict_SetItemString(opcodesDict, "VCVTTSD2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSD2USI));
        xPyDict_SetItemString(opcodesDict, "VCVTTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSS2SI));
        xPyDict_SetItemString(opcodesDict, "VCVTTSS2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSS2USI));
        xPyDict_SetItemString(opcodesDict, "VCVTUSI2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUSI2SD));
        xPyDict_SetItemString(opcodesDict, "VCVTUSI2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUSI2SS));
        xPyDict_SetItemString(opcodesDict, "VUCOMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_VUCOMISD));
        xPyDict_SetItemString(opcodesDict, "VUCOMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_VUCOMISS));
        xPyDict_SetItemString(opcodesDict, "JAE", PyLong_FromUint32(triton::arch::x86::ID_INS_JAE));
        xPyDict_SetItemString(opcodesDict, "JA", PyLong_FromUint32(triton::arch::x86::ID_INS_JA));
        xPyDict_SetItemString(opcodesDict, "JBE", PyLong_FromUint32(triton::arch::x86::ID_INS_JBE));
        xPyDict_SetItemString(opcodesDict, "JB", PyLong_FromUint32(triton::arch::x86::ID_INS_JB));
        xPyDict_SetItemString(opcodesDict, "JCXZ", PyLong_FromUint32(triton::arch::x86::ID_INS_JCXZ));
        xPyDict_SetItemString(opcodesDict, "JECXZ", PyLong_FromUint32(triton::arch::x86::ID_INS_JECXZ));
        xPyDict_SetItemString(opcodesDict, "JE", PyLong_FromUint32(triton::arch::x86::ID_INS_JE));
        xPyDict_SetItemString(opcodesDict, "JGE", PyLong_FromUint32(triton::arch::x86::ID_INS_JGE));
        xPyDict_SetItemString(opcodesDict, "JG", PyLong_FromUint32(triton::arch::x86::ID_INS_JG));
        xPyDict_SetItemString(opcodesDict, "JLE", PyLong_FromUint32(triton::arch::x86::ID_INS_JLE));
        xPyDict_SetItemString(opcodesDict, "JL", PyLong_FromUint32(triton::arch::x86::ID_INS_JL));
        xPyDict_SetItemString(opcodesDict, "JMP", PyLong_FromUint32(triton::arch::x86::ID_INS_JMP));
        xPyDict_SetItemString(opcodesDict, "JNE", PyLong_FromUint32(triton::arch::x86::ID_INS_JNE));
        xPyDict_SetItemString(opcodesDict, "JNO", PyLong_FromUint32(triton::arch::x86::ID_INS_JNO));
        xPyDict_SetItemString(opcodesDict, "JNP", PyLong_FromUint32(triton::arch::x86::ID_INS_JNP));
        xPyDict_SetItemString(opcodesDict, "JNS", PyLong_FromUint32(triton::arch::x86::ID_INS_JNS));
        xPyDict_SetItemString(opcodesDict, "JO", PyLong_FromUint32(triton::arch::x86::ID_INS_JO));
        xPyDict_SetItemString(opcodesDict, "JP", PyLong_FromUint32(triton::arch::x86::ID_INS_JP));
        xPyDict_SetItemString(opcodesDict, "JRCXZ", PyLong_FromUint32(triton::arch::x86::ID_INS_JRCXZ));
        xPyDict_SetItemString(opcodesDict, "JS", PyLong_FromUint32(triton::arch::x86::ID_INS_JS));
        xPyDict_SetItemString(opcodesDict, "KANDB", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDB));
        xPyDict_SetItemString(opcodesDict, "KANDD", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDD));
        xPyDict_SetItemString(opcodesDict, "KANDNB", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDNB));
        xPyDict_SetItemString(opcodesDict, "KANDND", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDND));
        xPyDict_SetItemString(opcodesDict, "KANDNQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDNQ));
        xPyDict_SetItemString(opcodesDict, "KANDNW", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDNW));
        xPyDict_SetItemString(opcodesDict, "KANDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDQ));
        xPyDict_SetItemString(opcodesDict, "KANDW", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDW));
        xPyDict_SetItemString(opcodesDict, "KMOVB", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVB));
        xPyDict_SetItemString(opcodesDict, "KMOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVD));
        xPyDict_SetItemString(opcodesDict, "KMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVQ));
        xPyDict_SetItemString(opcodesDict, "KMOVW", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVW));
        xPyDict_SetItemString(opcodesDict, "KNOTB", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTB));
        xPyDict_SetItemString(opcodesDict, "KNOTD", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTD));
        xPyDict_SetItemString(opcodesDict, "KNOTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTQ));
        xPyDict_SetItemString(opcodesDict, "KNOTW", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTW));
        xPyDict_SetItemString(opcodesDict, "KORB", PyLong_FromUint32(triton::arch::x86::ID_INS_KORB));
        xPyDict_SetItemString(opcodesDict, "KORD", PyLong_FromUint32(triton::arch::x86::ID_INS_KORD));
        xPyDict_SetItemString(opcodesDict, "KORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KORQ));
        xPyDict_SetItemString(opcodesDict, "KORTESTW", PyLong_FromUint32(triton::arch::x86::ID_INS_KORTESTW));
        xPyDict_SetItemString(opcodesDict, "KORW", PyLong_FromUint32(triton::arch::x86::ID_INS_KORW));
        xPyDict_SetItemString(opcodesDict, "KSHIFTLW", PyLong_FromUint32(triton::arch::x86::ID_INS_KSHIFTLW));
        xPyDict_SetItemString(opcodesDict, "KSHIFTRW", PyLong_FromUint32(triton::arch::x86::ID_INS_KSHIFTRW));
        xPyDict_SetItemString(opcodesDict, "KUNPCKBW", PyLong_FromUint32(triton::arch::x86::ID_INS_KUNPCKBW));
        xPyDict_SetItemString(opcodesDict, "KXNORB", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORB));
        xPyDict_SetItemString(opcodesDict, "KXNORD", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORD));
        xPyDict_SetItemString(opcodesDict, "KXNORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORQ));
        xPyDict_SetItemString(opcodesDict, "KXNORW", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORW));
        xPyDict_SetItemString(opcodesDict, "KXORB", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORB));
        xPyDict_SetItemString(opcodesDict, "KXORD", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORD));
        xPyDict_SetItemString(opcodesDict, "KXORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORQ));
        xPyDict_SetItemString(opcodesDict, "KXORW", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORW));
        xPyDict_SetItemString(opcodesDict, "LAHF", PyLong_FromUint32(triton::arch::x86::ID_INS_LAHF));
        xPyDict_SetItemString(opcodesDict, "LAR", PyLong_FromUint32(triton::arch::x86::ID_INS_LAR));
        xPyDict_SetItemString(opcodesDict, "LDDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_LDDQU));
        xPyDict_SetItemString(opcodesDict, "LDMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_LDMXCSR));
        xPyDict_SetItemString(opcodesDict, "LDS", PyLong_FromUint32(triton::arch::x86::ID_INS_LDS));
        xPyDict_SetItemString(opcodesDict, "FLDZ", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDZ));
        xPyDict_SetItemString(opcodesDict, "FLD1", PyLong_FromUint32(triton::arch::x86::ID_INS_FLD1));
        xPyDict_SetItemString(opcodesDict, "FLD", PyLong_FromUint32(triton::arch::x86::ID_INS_FLD));
        xPyDict_SetItemString(opcodesDict, "LEA", PyLong_FromUint32(triton::arch::x86::ID_INS_LEA));
        xPyDict_SetItemString(opcodesDict, "LEAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_LEAVE));
        xPyDict_SetItemString(opcodesDict, "LES", PyLong_FromUint32(triton::arch::x86::ID_INS_LES));
        xPyDict_SetItemString(opcodesDict, "LFENCE", PyLong_FromUint32(triton::arch::x86::ID_INS_LFENCE));
        xPyDict_SetItemString(opcodesDict, "LFS", PyLong_FromUint32(triton::arch::x86::ID_INS_LFS));
        xPyDict_SetItemString(opcodesDict, "LGDT", PyLong_FromUint32(triton::arch::x86::ID_INS_LGDT));
        xPyDict_SetItemString(opcodesDict, "LGS", PyLong_FromUint32(triton::arch::x86::ID_INS_LGS));
        xPyDict_SetItemString(opcodesDict, "LIDT", PyLong_FromUint32(triton::arch::x86::ID_INS_LIDT));
        xPyDict_SetItemString(opcodesDict, "LLDT", PyLong_FromUint32(triton::arch::x86::ID_INS_LLDT));
        xPyDict_SetItemString(opcodesDict, "LMSW", PyLong_FromUint32(triton::arch::x86::ID_INS_LMSW));
        xPyDict_SetItemString(opcodesDict, "OR", PyLong_FromUint32(triton::arch::x86::ID_INS_OR));
        xPyDict_SetItemString(opcodesDict, "SUB", PyLong_FromUint32(triton::arch::x86::ID_INS_SUB));
        xPyDict_SetItemString(opcodesDict, "XOR", PyLong_FromUint32(triton::arch::x86::ID_INS_XOR));
        xPyDict_SetItemString(opcodesDict, "LODSB", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSB));
        xPyDict_SetItemString(opcodesDict, "LODSD", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSD));
        xPyDict_SetItemString(opcodesDict, "LODSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSQ));
        xPyDict_SetItemString(opcodesDict, "LODSW", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSW));
        xPyDict_SetItemString(opcodesDict, "LOOP", PyLong_FromUint32(triton::arch::x86::ID_INS_LOOP));
        xPyDict_SetItemString(opcodesDict, "LOOPE", PyLong_FromUint32(triton::arch::x86::ID_INS_LOOPE));
        xPyDict_SetItemString(opcodesDict, "LOOPNE", PyLong_FromUint32(triton::arch::x86::ID_INS_LOOPNE));
        xPyDict_SetItemString(opcodesDict, "RETF", PyLong_FromUint32(triton::arch::x86::ID_INS_RETF));
        xPyDict_SetItemString(opcodesDict, "RETFQ", PyLong_FromUint32(triton::arch::x86::ID_INS_RETFQ));
        xPyDict_SetItemString(opcodesDict, "LSL", PyLong_FromUint32(triton::arch::x86::ID_INS_LSL));
        xPyDict_SetItemString(opcodesDict, "LSS", PyLong_FromUint32(triton::arch::x86::ID_INS_LSS));
        xPyDict_SetItemString(opcodesDict, "LTR", PyLong_FromUint32(triton::arch::x86::ID_INS_LTR));
        xPyDict_SetItemString(opcodesDict, "XADD", PyLong_FromUint32(triton::arch::x86::ID_INS_XADD));
        xPyDict_SetItemString(opcodesDict, "LZCNT", PyLong_FromUint32(triton::arch::x86::ID_INS_LZCNT));
        xPyDict_SetItemString(opcodesDict, "MASKMOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_MASKMOVDQU));
        xPyDict_SetItemString(opcodesDict, "MAXPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXPD));
        xPyDict_SetItemString(opcodesDict, "MAXPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXPS));
        xPyDict_SetItemString(opcodesDict, "MAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXSD));
        xPyDict_SetItemString(opcodesDict, "MAXSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXSS));
        xPyDict_SetItemString(opcodesDict, "MFENCE", PyLong_FromUint32(triton::arch::x86::ID_INS_MFENCE));
        xPyDict_SetItemString(opcodesDict, "MINPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MINPD));
        xPyDict_SetItemString(opcodesDict, "MINPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MINPS));
        xPyDict_SetItemString(opcodesDict, "MINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MINSD));
        xPyDict_SetItemString(opcodesDict, "MINSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MINSS));
        xPyDict_SetItemString(opcodesDict, "CVTPD2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPD2PI));
        xPyDict_SetItemString(opcodesDict, "CVTPI2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPI2PD));
        xPyDict_SetItemString(opcodesDict, "CVTPI2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPI2PS));
        xPyDict_SetItemString(opcodesDict, "CVTPS2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPS2PI));
        xPyDict_SetItemString(opcodesDict, "CVTTPD2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPD2PI));
        xPyDict_SetItemString(opcodesDict, "CVTTPS2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPS2PI));
        xPyDict_SetItemString(opcodesDict, "EMMS", PyLong_FromUint32(triton::arch::x86::ID_INS_EMMS));
        xPyDict_SetItemString(opcodesDict, "MASKMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MASKMOVQ));
        xPyDict_SetItemString(opcodesDict, "MOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVD));
        xPyDict_SetItemString(opcodesDict, "MOVDQ2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDQ2Q));
        xPyDict_SetItemString(opcodesDict, "MOVNTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTQ));
        xPyDict_SetItemString(opcodesDict, "MOVQ2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVQ2DQ));
        xPyDict_SetItemString(opcodesDict, "MOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVQ));
        xPyDict_SetItemString(opcodesDict, "PABSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PABSB));
        xPyDict_SetItemString(opcodesDict, "PABSD", PyLong_FromUint32(triton::arch::x86::ID_INS_PABSD));
        xPyDict_SetItemString(opcodesDict, "PABSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PABSW));
        xPyDict_SetItemString(opcodesDict, "PACKSSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKSSDW));
        xPyDict_SetItemString(opcodesDict, "PACKSSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKSSWB));
        xPyDict_SetItemString(opcodesDict, "PACKUSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKUSWB));
        xPyDict_SetItemString(opcodesDict, "PADDB", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDB));
        xPyDict_SetItemString(opcodesDict, "PADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDD));
        xPyDict_SetItemString(opcodesDict, "PADDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDQ));
        xPyDict_SetItemString(opcodesDict, "PADDSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDSB));
        xPyDict_SetItemString(opcodesDict, "PADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDSW));
        xPyDict_SetItemString(opcodesDict, "PADDUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDUSB));
        xPyDict_SetItemString(opcodesDict, "PADDUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDUSW));
        xPyDict_SetItemString(opcodesDict, "PADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDW));
        xPyDict_SetItemString(opcodesDict, "PALIGNR", PyLong_FromUint32(triton::arch::x86::ID_INS_PALIGNR));
        xPyDict_SetItemString(opcodesDict, "PANDN", PyLong_FromUint32(triton::arch::x86::ID_INS_PANDN));
        xPyDict_SetItemString(opcodesDict, "PAND", PyLong_FromUint32(triton::arch::x86::ID_INS_PAND));
        xPyDict_SetItemString(opcodesDict, "PAVGB", PyLong_FromUint32(triton::arch::x86::ID_INS_PAVGB));
        xPyDict_SetItemString(opcodesDict, "PAVGW", PyLong_FromUint32(triton::arch::x86::ID_INS_PAVGW));
        xPyDict_SetItemString(opcodesDict, "PCMPEQB", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQB));
        xPyDict_SetItemString(opcodesDict, "PCMPEQD", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQD));
        xPyDict_SetItemString(opcodesDict, "PCMPEQW", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQW));
        xPyDict_SetItemString(opcodesDict, "PCMPGTB", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTB));
        xPyDict_SetItemString(opcodesDict, "PCMPGTD", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTD));
        xPyDict_SetItemString(opcodesDict, "PCMPGTW", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTW));
        xPyDict_SetItemString(opcodesDict, "PEXTRW", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRW));
        xPyDict_SetItemString(opcodesDict, "PHADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHADDSW));
        xPyDict_SetItemString(opcodesDict, "PHADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHADDW));
        xPyDict_SetItemString(opcodesDict, "PHADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_PHADDD));
        xPyDict_SetItemString(opcodesDict, "PHSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PHSUBD));
        xPyDict_SetItemString(opcodesDict, "PHSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHSUBSW));
        xPyDict_SetItemString(opcodesDict, "PHSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHSUBW));
        xPyDict_SetItemString(opcodesDict, "PINSRW", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRW));
        xPyDict_SetItemString(opcodesDict, "PMADDUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMADDUBSW));
        xPyDict_SetItemString(opcodesDict, "PMADDWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMADDWD));
        xPyDict_SetItemString(opcodesDict, "PMAXSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXSW));
        xPyDict_SetItemString(opcodesDict, "PMAXUB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXUB));
        xPyDict_SetItemString(opcodesDict, "PMINSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINSW));
        xPyDict_SetItemString(opcodesDict, "PMINUB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINUB));
        xPyDict_SetItemString(opcodesDict, "PMOVMSKB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVMSKB));
        xPyDict_SetItemString(opcodesDict, "PMULHRSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHRSW));
        xPyDict_SetItemString(opcodesDict, "PMULHUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHUW));
        xPyDict_SetItemString(opcodesDict, "PMULHW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHW));
        xPyDict_SetItemString(opcodesDict, "PMULLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULLW));
        xPyDict_SetItemString(opcodesDict, "PMULUDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULUDQ));
        xPyDict_SetItemString(opcodesDict, "POR", PyLong_FromUint32(triton::arch::x86::ID_INS_POR));
        xPyDict_SetItemString(opcodesDict, "PSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSADBW));
        xPyDict_SetItemString(opcodesDict, "PSHUFB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFB));
        xPyDict_SetItemString(opcodesDict, "PSHUFW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFW));
        xPyDict_SetItemString(opcodesDict, "PSIGNB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSIGNB));
        xPyDict_SetItemString(opcodesDict, "PSIGND", PyLong_FromUint32(triton::arch::x86::ID_INS_PSIGND));
        xPyDict_SetItemString(opcodesDict, "PSIGNW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSIGNW));
        xPyDict_SetItemString(opcodesDict, "PSLLD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLD));
        xPyDict_SetItemString(opcodesDict, "PSLLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLQ));
        xPyDict_SetItemString(opcodesDict, "PSLLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLW));
        xPyDict_SetItemString(opcodesDict, "PSRAD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRAD));
        xPyDict_SetItemString(opcodesDict, "PSRAW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRAW));
        xPyDict_SetItemString(opcodesDict, "PSRLD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLD));
        xPyDict_SetItemString(opcodesDict, "PSRLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLQ));
        xPyDict_SetItemString(opcodesDict, "PSRLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLW));
        xPyDict_SetItemString(opcodesDict, "PSUBB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBB));
        xPyDict_SetItemString(opcodesDict, "PSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBD));
        xPyDict_SetItemString(opcodesDict, "PSUBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBQ));
        xPyDict_SetItemString(opcodesDict, "PSUBSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBSB));
        xPyDict_SetItemString(opcodesDict, "PSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBSW));
        xPyDict_SetItemString(opcodesDict, "PSUBUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBUSB));
        xPyDict_SetItemString(opcodesDict, "PSUBUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBUSW));
        xPyDict_SetItemString(opcodesDict, "PSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBW));
        xPyDict_SetItemString(opcodesDict, "PUNPCKHBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHBW));
        xPyDict_SetItemString(opcodesDict, "PUNPCKHDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHDQ));
        xPyDict_SetItemString(opcodesDict, "PUNPCKHWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHWD));
        xPyDict_SetItemString(opcodesDict, "PUNPCKLBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLBW));
        xPyDict_SetItemString(opcodesDict, "PUNPCKLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLDQ));
        xPyDict_SetItemString(opcodesDict, "PUNPCKLWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLWD));
        xPyDict_SetItemString(opcodesDict, "PXOR", PyLong_FromUint32(triton::arch::x86::ID_INS_PXOR));
        xPyDict_SetItemString(opcodesDict, "MONITOR", PyLong_FromUint32(triton::arch::x86::ID_INS_MONITOR));
        xPyDict_SetItemString(opcodesDict, "MONTMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_MONTMUL));
        xPyDict_SetItemString(opcodesDict, "MOV", PyLong_FromUint32(triton::arch::x86::ID_INS_MOV));
        xPyDict_SetItemString(opcodesDict, "MOVABS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVABS));
        xPyDict_SetItemString(opcodesDict, "MOVBE", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVBE));
        xPyDict_SetItemString(opcodesDict, "MOVDDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDDUP));
        xPyDict_SetItemString(opcodesDict, "MOVDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDQA));
        xPyDict_SetItemString(opcodesDict, "MOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDQU));
        xPyDict_SetItemString(opcodesDict, "MOVHLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVHLPS));
        xPyDict_SetItemString(opcodesDict, "MOVHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVHPD));
        xPyDict_SetItemString(opcodesDict, "MOVHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVHPS));
        xPyDict_SetItemString(opcodesDict, "MOVLHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVLHPS));
        xPyDict_SetItemString(opcodesDict, "MOVLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVLPD));
        xPyDict_SetItemString(opcodesDict, "MOVLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVLPS));
        xPyDict_SetItemString(opcodesDict, "MOVMSKPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVMSKPD));
        xPyDict_SetItemString(opcodesDict, "MOVMSKPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVMSKPS));
        xPyDict_SetItemString(opcodesDict, "MOVNTDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTDQA));
        xPyDict_SetItemString(opcodesDict, "MOVNTDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTDQ));
        xPyDict_SetItemString(opcodesDict, "MOVNTI", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTI));
        xPyDict_SetItemString(opcodesDict, "MOVNTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTPD));
        xPyDict_SetItemString(opcodesDict, "MOVNTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTPS));
        xPyDict_SetItemString(opcodesDict, "MOVNTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTSD));
        xPyDict_SetItemString(opcodesDict, "MOVNTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTSS));
        xPyDict_SetItemString(opcodesDict, "MOVSB", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSB));
        xPyDict_SetItemString(opcodesDict, "MOVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSD));
        xPyDict_SetItemString(opcodesDict, "MOVSHDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSHDUP));
        xPyDict_SetItemString(opcodesDict, "MOVSLDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSLDUP));
        xPyDict_SetItemString(opcodesDict, "MOVSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSQ));
        xPyDict_SetItemString(opcodesDict, "MOVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSS));
        xPyDict_SetItemString(opcodesDict, "MOVSW", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSW));
        xPyDict_SetItemString(opcodesDict, "MOVSX", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSX));
        xPyDict_SetItemString(opcodesDict, "MOVSXD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSXD));
        xPyDict_SetItemString(opcodesDict, "MOVUPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVUPD));
        xPyDict_SetItemString(opcodesDict, "MOVUPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVUPS));
        xPyDict_SetItemString(opcodesDict, "MOVZX", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVZX));
        xPyDict_SetItemString(opcodesDict, "MPSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_MPSADBW));
        xPyDict_SetItemString(opcodesDict, "MUL", PyLong_FromUint32(triton::arch::x86::ID_INS_MUL));
        xPyDict_SetItemString(opcodesDict, "MULPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MULPD));
        xPyDict_SetItemString(opcodesDict, "MULPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MULPS));
        xPyDict_SetItemString(opcodesDict, "MULSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MULSD));
        xPyDict_SetItemString(opcodesDict, "MULSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MULSS));
        xPyDict_SetItemString(opcodesDict, "MULX", PyLong_FromUint32(triton::arch::x86::ID_INS_MULX));
        xPyDict_SetItemString(opcodesDict, "FMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_FMUL));
        xPyDict_SetItemString(opcodesDict, "FIMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_FIMUL));
        xPyDict_SetItemString(opcodesDict, "FMULP", PyLong_FromUint32(triton::arch::x86::ID_INS_FMULP));
        xPyDict_SetItemString(opcodesDict, "MWAIT", PyLong_FromUint32(triton::arch::x86::ID_INS_MWAIT));
        xPyDict_SetItemString(opcodesDict, "NEG", PyLong_FromUint32(triton::arch::x86::ID_INS_NEG));
        xPyDict_SetItemString(opcodesDict, "NOP", PyLong_FromUint32(triton::arch::x86::ID_INS_NOP));
        xPyDict_SetItemString(opcodesDict, "NOT", PyLong_FromUint32(triton::arch::x86::ID_INS_NOT));
        xPyDict_SetItemString(opcodesDict, "OUT", PyLong_FromUint32(triton::arch::x86::ID_INS_OUT));
        xPyDict_SetItemString(opcodesDict, "OUTSB", PyLong_FromUint32(triton::arch::x86::ID_INS_OUTSB));
        xPyDict_SetItemString(opcodesDict, "OUTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_OUTSD));
        xPyDict_SetItemString(opcodesDict, "OUTSW", PyLong_FromUint32(triton::arch::x86::ID_INS_OUTSW));
        xPyDict_SetItemString(opcodesDict, "PACKUSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKUSDW));
        xPyDict_SetItemString(opcodesDict, "PAUSE", PyLong_FromUint32(triton::arch::x86::ID_INS_PAUSE));
        xPyDict_SetItemString(opcodesDict, "PAVGUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PAVGUSB));
        xPyDict_SetItemString(opcodesDict, "PBLENDVB", PyLong_FromUint32(triton::arch::x86::ID_INS_PBLENDVB));
        xPyDict_SetItemString(opcodesDict, "PBLENDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PBLENDW));
        xPyDict_SetItemString(opcodesDict, "PCLMULQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PCLMULQDQ));
        xPyDict_SetItemString(opcodesDict, "PCMPEQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQQ));
        xPyDict_SetItemString(opcodesDict, "PCMPESTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPESTRI));
        xPyDict_SetItemString(opcodesDict, "PCMPESTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPESTRM));
        xPyDict_SetItemString(opcodesDict, "PCMPGTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTQ));
        xPyDict_SetItemString(opcodesDict, "PCMPISTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPISTRI));
        xPyDict_SetItemString(opcodesDict, "PCMPISTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPISTRM));
        xPyDict_SetItemString(opcodesDict, "PDEP", PyLong_FromUint32(triton::arch::x86::ID_INS_PDEP));
        xPyDict_SetItemString(opcodesDict, "PEXT", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXT));
        xPyDict_SetItemString(opcodesDict, "PEXTRB", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRB));
        xPyDict_SetItemString(opcodesDict, "PEXTRD", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRD));
        xPyDict_SetItemString(opcodesDict, "PEXTRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRQ));
        xPyDict_SetItemString(opcodesDict, "PF2ID", PyLong_FromUint32(triton::arch::x86::ID_INS_PF2ID));
        xPyDict_SetItemString(opcodesDict, "PF2IW", PyLong_FromUint32(triton::arch::x86::ID_INS_PF2IW));
        xPyDict_SetItemString(opcodesDict, "PFACC", PyLong_FromUint32(triton::arch::x86::ID_INS_PFACC));
        xPyDict_SetItemString(opcodesDict, "PFADD", PyLong_FromUint32(triton::arch::x86::ID_INS_PFADD));
        xPyDict_SetItemString(opcodesDict, "PFCMPEQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PFCMPEQ));
        xPyDict_SetItemString(opcodesDict, "PFCMPGE", PyLong_FromUint32(triton::arch::x86::ID_INS_PFCMPGE));
        xPyDict_SetItemString(opcodesDict, "PFCMPGT", PyLong_FromUint32(triton::arch::x86::ID_INS_PFCMPGT));
        xPyDict_SetItemString(opcodesDict, "PFMAX", PyLong_FromUint32(triton::arch::x86::ID_INS_PFMAX));
        xPyDict_SetItemString(opcodesDict, "PFMIN", PyLong_FromUint32(triton::arch::x86::ID_INS_PFMIN));
        xPyDict_SetItemString(opcodesDict, "PFMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_PFMUL));
        xPyDict_SetItemString(opcodesDict, "PFNACC", PyLong_FromUint32(triton::arch::x86::ID_INS_PFNACC));
        xPyDict_SetItemString(opcodesDict, "PFPNACC", PyLong_FromUint32(triton::arch::x86::ID_INS_PFPNACC));
        xPyDict_SetItemString(opcodesDict, "PFRCPIT1", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRCPIT1));
        xPyDict_SetItemString(opcodesDict, "PFRCPIT2", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRCPIT2));
        xPyDict_SetItemString(opcodesDict, "PFRCP", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRCP));
        xPyDict_SetItemString(opcodesDict, "PFRSQIT1", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRSQIT1));
        xPyDict_SetItemString(opcodesDict, "PFRSQRT", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRSQRT));
        xPyDict_SetItemString(opcodesDict, "PFSUBR", PyLong_FromUint32(triton::arch::x86::ID_INS_PFSUBR));
        xPyDict_SetItemString(opcodesDict, "PFSUB", PyLong_FromUint32(triton::arch::x86::ID_INS_PFSUB));
        xPyDict_SetItemString(opcodesDict, "PHMINPOSUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHMINPOSUW));
        xPyDict_SetItemString(opcodesDict, "PI2FD", PyLong_FromUint32(triton::arch::x86::ID_INS_PI2FD));
        xPyDict_SetItemString(opcodesDict, "PI2FW", PyLong_FromUint32(triton::arch::x86::ID_INS_PI2FW));
        xPyDict_SetItemString(opcodesDict, "PINSRB", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRB));
        xPyDict_SetItemString(opcodesDict, "PINSRD", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRD));
        xPyDict_SetItemString(opcodesDict, "PINSRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRQ));
        xPyDict_SetItemString(opcodesDict, "PMAXSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXSB));
        xPyDict_SetItemString(opcodesDict, "PMAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXSD));
        xPyDict_SetItemString(opcodesDict, "PMAXUD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXUD));
        xPyDict_SetItemString(opcodesDict, "PMAXUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXUW));
        xPyDict_SetItemString(opcodesDict, "PMINSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINSB));
        xPyDict_SetItemString(opcodesDict, "PMINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINSD));
        xPyDict_SetItemString(opcodesDict, "PMINUD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINUD));
        xPyDict_SetItemString(opcodesDict, "PMINUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINUW));
        xPyDict_SetItemString(opcodesDict, "PMOVSXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXBD));
        xPyDict_SetItemString(opcodesDict, "PMOVSXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXBQ));
        xPyDict_SetItemString(opcodesDict, "PMOVSXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXBW));
        xPyDict_SetItemString(opcodesDict, "PMOVSXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXDQ));
        xPyDict_SetItemString(opcodesDict, "PMOVSXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXWD));
        xPyDict_SetItemString(opcodesDict, "PMOVSXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXWQ));
        xPyDict_SetItemString(opcodesDict, "PMOVZXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXBD));
        xPyDict_SetItemString(opcodesDict, "PMOVZXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXBQ));
        xPyDict_SetItemString(opcodesDict, "PMOVZXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXBW));
        xPyDict_SetItemString(opcodesDict, "PMOVZXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXDQ));
        xPyDict_SetItemString(opcodesDict, "PMOVZXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXWD));
        xPyDict_SetItemString(opcodesDict, "PMOVZXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXWQ));
        xPyDict_SetItemString(opcodesDict, "PMULDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULDQ));
        xPyDict_SetItemString(opcodesDict, "PMULHRW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHRW));
        xPyDict_SetItemString(opcodesDict, "PMULLD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULLD));
        xPyDict_SetItemString(opcodesDict, "POP", PyLong_FromUint32(triton::arch::x86::ID_INS_POP));
        xPyDict_SetItemString(opcodesDict, "POPAW", PyLong_FromUint32(triton::arch::x86::ID_INS_POPAW));
        xPyDict_SetItemString(opcodesDict, "POPAL", PyLong_FromUint32(triton::arch::x86::ID_INS_POPAL));
        xPyDict_SetItemString(opcodesDict, "POPCNT", PyLong_FromUint32(triton::arch::x86::ID_INS_POPCNT));
        xPyDict_SetItemString(opcodesDict, "POPF", PyLong_FromUint32(triton::arch::x86::ID_INS_POPF));
        xPyDict_SetItemString(opcodesDict, "POPFD", PyLong_FromUint32(triton::arch::x86::ID_INS_POPFD));
        xPyDict_SetItemString(opcodesDict, "POPFQ", PyLong_FromUint32(triton::arch::x86::ID_INS_POPFQ));
        xPyDict_SetItemString(opcodesDict, "PREFETCH", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCH));
        xPyDict_SetItemString(opcodesDict, "PREFETCHNTA", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHNTA));
        xPyDict_SetItemString(opcodesDict, "PREFETCHT0", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHT0));
        xPyDict_SetItemString(opcodesDict, "PREFETCHT1", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHT1));
        xPyDict_SetItemString(opcodesDict, "PREFETCHT2", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHT2));
        xPyDict_SetItemString(opcodesDict, "PREFETCHW", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHW));
        xPyDict_SetItemString(opcodesDict, "PSHUFD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFD));
        xPyDict_SetItemString(opcodesDict, "PSHUFHW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFHW));
        xPyDict_SetItemString(opcodesDict, "PSHUFLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFLW));
        xPyDict_SetItemString(opcodesDict, "PSLLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLDQ));
        xPyDict_SetItemString(opcodesDict, "PSRLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLDQ));
        xPyDict_SetItemString(opcodesDict, "PSWAPD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSWAPD));
        xPyDict_SetItemString(opcodesDict, "PTEST", PyLong_FromUint32(triton::arch::x86::ID_INS_PTEST));
        xPyDict_SetItemString(opcodesDict, "PUNPCKHQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHQDQ));
        xPyDict_SetItemString(opcodesDict, "PUNPCKLQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLQDQ));
        xPyDict_SetItemString(opcodesDict, "PUSH", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSH));
        xPyDict_SetItemString(opcodesDict, "PUSHAW", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHAW));
        xPyDict_SetItemString(opcodesDict, "PUSHAL", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHAL));
        xPyDict_SetItemString(opcodesDict, "PUSHF", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHF));
        xPyDict_SetItemString(opcodesDict, "PUSHFD", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHFD));
        xPyDict_SetItemString(opcodesDict, "PUSHFQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHFQ));
        xPyDict_SetItemString(opcodesDict, "RCL", PyLong_FromUint32(triton::arch::x86::ID_INS_RCL));
        xPyDict_SetItemString(opcodesDict, "RCPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_RCPPS));
        xPyDict_SetItemString(opcodesDict, "RCPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_RCPSS));
        xPyDict_SetItemString(opcodesDict, "RCR", PyLong_FromUint32(triton::arch::x86::ID_INS_RCR));
        xPyDict_SetItemString(opcodesDict, "RDFSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_RDFSBASE));
        xPyDict_SetItemString(opcodesDict, "RDGSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_RDGSBASE));
        xPyDict_SetItemString(opcodesDict, "RDMSR", PyLong_FromUint32(triton::arch::x86::ID_INS_RDMSR));
        xPyDict_SetItemString(opcodesDict, "RDPMC", PyLong_FromUint32(triton::arch::x86::ID_INS_RDPMC));
        xPyDict_SetItemString(opcodesDict, "RDRAND", PyLong_FromUint32(triton::arch::x86::ID_INS_RDRAND));
        xPyDict_SetItemString(opcodesDict, "RDSEED", PyLong_FromUint32(triton::arch::x86::ID_INS_RDSEED));
        xPyDict_SetItemString(opcodesDict, "RDTSC", PyLong_FromUint32(triton::arch::x86::ID_INS_RDTSC));
        xPyDict_SetItemString(opcodesDict, "RDTSCP", PyLong_FromUint32(triton::arch::x86::ID_INS_RDTSCP));
        xPyDict_SetItemString(opcodesDict, "ROL", PyLong_FromUint32(triton::arch::x86::ID_INS_ROL));
        xPyDict_SetItemString(opcodesDict, "ROR", PyLong_FromUint32(triton::arch::x86::ID_INS_ROR));
        xPyDict_SetItemString(opcodesDict, "RORX", PyLong_FromUint32(triton::arch::x86::ID_INS_RORX));
        xPyDict_SetItemString(opcodesDict, "ROUNDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDPD));
        xPyDict_SetItemString(opcodesDict, "ROUNDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDPS));
        xPyDict_SetItemString(opcodesDict, "ROUNDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDSD));
        xPyDict_SetItemString(opcodesDict, "ROUNDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDSS));
        xPyDict_SetItemString(opcodesDict, "RSM", PyLong_FromUint32(triton::arch::x86::ID_INS_RSM));
        xPyDict_SetItemString(opcodesDict, "RSQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_RSQRTPS));
        xPyDict_SetItemString(opcodesDict, "RSQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_RSQRTSS));
        xPyDict_SetItemString(opcodesDict, "SAHF", PyLong_FromUint32(triton::arch::x86::ID_INS_SAHF));
        xPyDict_SetItemString(opcodesDict, "SAL", PyLong_FromUint32(triton::arch::x86::ID_INS_SAL));
        xPyDict_SetItemString(opcodesDict, "SALC", PyLong_FromUint32(triton::arch::x86::ID_INS_SALC));
        xPyDict_SetItemString(opcodesDict, "SAR", PyLong_FromUint32(triton::arch::x86::ID_INS_SAR));
        xPyDict_SetItemString(opcodesDict, "SARX", PyLong_FromUint32(triton::arch::x86::ID_INS_SARX));
        xPyDict_SetItemString(opcodesDict, "SBB", PyLong_FromUint32(triton::arch::x86::ID_INS_SBB));
        xPyDict_SetItemString(opcodesDict, "SCASB", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASB));
        xPyDict_SetItemString(opcodesDict, "SCASD", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASD));
        xPyDict_SetItemString(opcodesDict, "SCASQ", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASQ));
        xPyDict_SetItemString(opcodesDict, "SCASW", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASW));
        xPyDict_SetItemString(opcodesDict, "SETAE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETAE));
        xPyDict_SetItemString(opcodesDict, "SETA", PyLong_FromUint32(triton::arch::x86::ID_INS_SETA));
        xPyDict_SetItemString(opcodesDict, "SETBE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETBE));
        xPyDict_SetItemString(opcodesDict, "SETB", PyLong_FromUint32(triton::arch::x86::ID_INS_SETB));
        xPyDict_SetItemString(opcodesDict, "SETE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETE));
        xPyDict_SetItemString(opcodesDict, "SETGE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETGE));
        xPyDict_SetItemString(opcodesDict, "SETG", PyLong_FromUint32(triton::arch::x86::ID_INS_SETG));
        xPyDict_SetItemString(opcodesDict, "SETLE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETLE));
        xPyDict_SetItemString(opcodesDict, "SETL", PyLong_FromUint32(triton::arch::x86::ID_INS_SETL));
        xPyDict_SetItemString(opcodesDict, "SETNE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNE));
        xPyDict_SetItemString(opcodesDict, "SETNO", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNO));
        xPyDict_SetItemString(opcodesDict, "SETNP", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNP));
        xPyDict_SetItemString(opcodesDict, "SETNS", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNS));
        xPyDict_SetItemString(opcodesDict, "SETO", PyLong_FromUint32(triton::arch::x86::ID_INS_SETO));
        xPyDict_SetItemString(opcodesDict, "SETP", PyLong_FromUint32(triton::arch::x86::ID_INS_SETP));
        xPyDict_SetItemString(opcodesDict, "SETS", PyLong_FromUint32(triton::arch::x86::ID_INS_SETS));
        xPyDict_SetItemString(opcodesDict, "SFENCE", PyLong_FromUint32(triton::arch::x86::ID_INS_SFENCE));
        xPyDict_SetItemString(opcodesDict, "SGDT", PyLong_FromUint32(triton::arch::x86::ID_INS_SGDT));
        xPyDict_SetItemString(opcodesDict, "SHA1MSG1", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1MSG1));
        xPyDict_SetItemString(opcodesDict, "SHA1MSG2", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1MSG2));
        xPyDict_SetItemString(opcodesDict, "SHA1NEXTE", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1NEXTE));
        xPyDict_SetItemString(opcodesDict, "SHA1RNDS4", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1RNDS4));
        xPyDict_SetItemString(opcodesDict, "SHA256MSG1", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA256MSG1));
        xPyDict_SetItemString(opcodesDict, "SHA256MSG2", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA256MSG2));
        xPyDict_SetItemString(opcodesDict, "SHA256RNDS2", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA256RNDS2));
        xPyDict_SetItemString(opcodesDict, "SHL", PyLong_FromUint32(triton::arch::x86::ID_INS_SHL));
        xPyDict_SetItemString(opcodesDict, "SHLD", PyLong_FromUint32(triton::arch::x86::ID_INS_SHLD));
        xPyDict_SetItemString(opcodesDict, "SHLX", PyLong_FromUint32(triton::arch::x86::ID_INS_SHLX));
        xPyDict_SetItemString(opcodesDict, "SHR", PyLong_FromUint32(triton::arch::x86::ID_INS_SHR));
        xPyDict_SetItemString(opcodesDict, "SHRD", PyLong_FromUint32(triton::arch::x86::ID_INS_SHRD));
        xPyDict_SetItemString(opcodesDict, "SHRX", PyLong_FromUint32(triton::arch::x86::ID_INS_SHRX));
        xPyDict_SetItemString(opcodesDict, "SHUFPD", PyLong_FromUint32(triton::arch::x86::ID_INS_SHUFPD));
        xPyDict_SetItemString(opcodesDict, "SHUFPS", PyLong_FromUint32(triton::arch::x86::ID_INS_SHUFPS));
        xPyDict_SetItemString(opcodesDict, "SIDT", PyLong_FromUint32(triton::arch::x86::ID_INS_SIDT));
        xPyDict_SetItemString(opcodesDict, "FSIN", PyLong_FromUint32(triton::arch::x86::ID_INS_FSIN));
        xPyDict_SetItemString(opcodesDict, "SKINIT", PyLong_FromUint32(triton::arch::x86::ID_INS_SKINIT));
        xPyDict_SetItemString(opcodesDict, "SLDT", PyLong_FromUint32(triton::arch::x86::ID_INS_SLDT));
        xPyDict_SetItemString(opcodesDict, "SMSW", PyLong_FromUint32(triton::arch::x86::ID_INS_SMSW));
        xPyDict_SetItemString(opcodesDict, "SQRTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTPD));
        xPyDict_SetItemString(opcodesDict, "SQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTPS));
        xPyDict_SetItemString(opcodesDict, "SQRTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTSD));
        xPyDict_SetItemString(opcodesDict, "SQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTSS));
        xPyDict_SetItemString(opcodesDict, "FSQRT", PyLong_FromUint32(triton::arch::x86::ID_INS_FSQRT));
        xPyDict_SetItemString(opcodesDict, "STAC", PyLong_FromUint32(triton::arch::x86::ID_INS_STAC));
        xPyDict_SetItemString(opcodesDict, "STC", PyLong_FromUint32(triton::arch::x86::ID_INS_STC));
        xPyDict_SetItemString(opcodesDict, "STD", PyLong_FromUint32(triton::arch::x86::ID_INS_STD));
        xPyDict_SetItemString(opcodesDict, "STGI", PyLong_FromUint32(triton::arch::x86::ID_INS_STGI));
        xPyDict_SetItemString(opcodesDict, "STI", PyLong_FromUint32(triton::arch::x86::ID_INS_STI));
        xPyDict_SetItemString(opcodesDict, "STMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_STMXCSR));
        xPyDict_SetItemString(opcodesDict, "STOSB", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSB));
        xPyDict_SetItemString(opcodesDict, "STOSD", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSD));
        xPyDict_SetItemString(opcodesDict, "STOSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSQ));
        xPyDict_SetItemString(opcodesDict, "STOSW", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSW));
        xPyDict_SetItemString(opcodesDict, "STR", PyLong_FromUint32(triton::arch::x86::ID_INS_STR));
        xPyDict_SetItemString(opcodesDict, "FST", PyLong_FromUint32(triton::arch::x86::ID_INS_FST));
        xPyDict_SetItemString(opcodesDict, "FSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FSTP));
        xPyDict_SetItemString(opcodesDict, "FSTPNCE", PyLong_FromUint32(triton::arch::x86::ID_INS_FSTPNCE));
        xPyDict_SetItemString(opcodesDict, "SUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBPD));
        xPyDict_SetItemString(opcodesDict, "SUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBPS));
        xPyDict_SetItemString(opcodesDict, "FSUBR", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUBR));
        xPyDict_SetItemString(opcodesDict, "FISUBR", PyLong_FromUint32(triton::arch::x86::ID_INS_FISUBR));
        xPyDict_SetItemString(opcodesDict, "FSUBRP", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUBRP));
        xPyDict_SetItemString(opcodesDict, "SUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBSD));
        xPyDict_SetItemString(opcodesDict, "SUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBSS));
        xPyDict_SetItemString(opcodesDict, "FSUB", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUB));
        xPyDict_SetItemString(opcodesDict, "FISUB", PyLong_FromUint32(triton::arch::x86::ID_INS_FISUB));
        xPyDict_SetItemString(opcodesDict, "FSUBP", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUBP));
        xPyDict_SetItemString(opcodesDict, "SWAPGS", PyLong_FromUint32(triton::arch::x86::ID_INS_SWAPGS));
        xPyDict_SetItemString(opcodesDict, "SYSCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSCALL));
        xPyDict_SetItemString(opcodesDict, "SYSENTER", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSENTER));
        xPyDict_SetItemString(opcodesDict, "SYSEXIT", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSEXIT));
        xPyDict_SetItemString(opcodesDict, "SYSRET", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSRET));
        xPyDict_SetItemString(opcodesDict, "T1MSKC", PyLong_FromUint32(triton::arch::x86::ID_INS_T1MSKC));
        xPyDict_SetItemString(opcodesDict, "TEST", PyLong_FromUint32(triton::arch::x86::ID_INS_TEST));
        xPyDict_SetItemString(opcodesDict, "UD2", PyLong_FromUint32(triton::arch::x86::ID_INS_UD2));
        xPyDict_SetItemString(opcodesDict, "FTST", PyLong_FromUint32(triton::arch::x86::ID_INS_FTST));
        xPyDict_SetItemString(opcodesDict, "TZCNT", PyLong_FromUint32(triton::arch::x86::ID_INS_TZCNT));
        xPyDict_SetItemString(opcodesDict, "TZMSK", PyLong_FromUint32(triton::arch::x86::ID_INS_TZMSK));
        xPyDict_SetItemString(opcodesDict, "FUCOMPI", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMPI));
        xPyDict_SetItemString(opcodesDict, "FUCOMI", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMI));
        xPyDict_SetItemString(opcodesDict, "FUCOMPP", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMPP));
        xPyDict_SetItemString(opcodesDict, "FUCOMP", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMP));
        xPyDict_SetItemString(opcodesDict, "FUCOM", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOM));
        xPyDict_SetItemString(opcodesDict, "UD2B", PyLong_FromUint32(triton::arch::x86::ID_INS_UD2B));
        xPyDict_SetItemString(opcodesDict, "UNPCKHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKHPD));
        xPyDict_SetItemString(opcodesDict, "UNPCKHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKHPS));
        xPyDict_SetItemString(opcodesDict, "UNPCKLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKLPD));
        xPyDict_SetItemString(opcodesDict, "UNPCKLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKLPS));
        xPyDict_SetItemString(opcodesDict, "VADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDPD));
        xPyDict_SetItemString(opcodesDict, "VADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDPS));
        xPyDict_SetItemString(opcodesDict, "VADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSD));
        xPyDict_SetItemString(opcodesDict, "VADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSS));
        xPyDict_SetItemString(opcodesDict, "VADDSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSUBPD));
        xPyDict_SetItemString(opcodesDict, "VADDSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSUBPS));
        xPyDict_SetItemString(opcodesDict, "VAESDECLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESDECLAST));
        xPyDict_SetItemString(opcodesDict, "VAESDEC", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESDEC));
        xPyDict_SetItemString(opcodesDict, "VAESENCLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESENCLAST));
        xPyDict_SetItemString(opcodesDict, "VAESENC", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESENC));
        xPyDict_SetItemString(opcodesDict, "VAESIMC", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESIMC));
        xPyDict_SetItemString(opcodesDict, "VAESKEYGENASSIST", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESKEYGENASSIST));
        xPyDict_SetItemString(opcodesDict, "VALIGND", PyLong_FromUint32(triton::arch::x86::ID_INS_VALIGND));
        xPyDict_SetItemString(opcodesDict, "VALIGNQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VALIGNQ));
        xPyDict_SetItemString(opcodesDict, "VANDNPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDNPD));
        xPyDict_SetItemString(opcodesDict, "VANDNPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDNPS));
        xPyDict_SetItemString(opcodesDict, "VANDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDPD));
        xPyDict_SetItemString(opcodesDict, "VANDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDPS));
        xPyDict_SetItemString(opcodesDict, "VBLENDMPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDMPD));
        xPyDict_SetItemString(opcodesDict, "VBLENDMPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDMPS));
        xPyDict_SetItemString(opcodesDict, "VBLENDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDPD));
        xPyDict_SetItemString(opcodesDict, "VBLENDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDPS));
        xPyDict_SetItemString(opcodesDict, "VBLENDVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDVPD));
        xPyDict_SetItemString(opcodesDict, "VBLENDVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDVPS));
        xPyDict_SetItemString(opcodesDict, "VBROADCASTF128", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTF128));
        xPyDict_SetItemString(opcodesDict, "VBROADCASTI128", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTI128));
        xPyDict_SetItemString(opcodesDict, "VBROADCASTI32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTI32X4));
        xPyDict_SetItemString(opcodesDict, "VBROADCASTI64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTI64X4));
        xPyDict_SetItemString(opcodesDict, "VBROADCASTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTSD));
        xPyDict_SetItemString(opcodesDict, "VBROADCASTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTSS));
        xPyDict_SetItemString(opcodesDict, "VCMPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPPD));
        xPyDict_SetItemString(opcodesDict, "VCMPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPPS));
        xPyDict_SetItemString(opcodesDict, "VCMPSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPSD));
        xPyDict_SetItemString(opcodesDict, "VCMPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPSS));
        xPyDict_SetItemString(opcodesDict, "VCVTDQ2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTDQ2PD));
        xPyDict_SetItemString(opcodesDict, "VCVTDQ2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTDQ2PS));
        xPyDict_SetItemString(opcodesDict, "VCVTPD2DQX", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2DQX));
        xPyDict_SetItemString(opcodesDict, "VCVTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2DQ));
        xPyDict_SetItemString(opcodesDict, "VCVTPD2PSX", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2PSX));
        xPyDict_SetItemString(opcodesDict, "VCVTPD2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2PS));
        xPyDict_SetItemString(opcodesDict, "VCVTPD2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2UDQ));
        xPyDict_SetItemString(opcodesDict, "VCVTPH2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPH2PS));
        xPyDict_SetItemString(opcodesDict, "VCVTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2DQ));
        xPyDict_SetItemString(opcodesDict, "VCVTPS2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2PD));
        xPyDict_SetItemString(opcodesDict, "VCVTPS2PH", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2PH));
        xPyDict_SetItemString(opcodesDict, "VCVTPS2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2UDQ));
        xPyDict_SetItemString(opcodesDict, "VCVTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSD2SI));
        xPyDict_SetItemString(opcodesDict, "VCVTSD2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSD2USI));
        xPyDict_SetItemString(opcodesDict, "VCVTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSS2SI));
        xPyDict_SetItemString(opcodesDict, "VCVTSS2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSS2USI));
        xPyDict_SetItemString(opcodesDict, "VCVTTPD2DQX", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPD2DQX));
        xPyDict_SetItemString(opcodesDict, "VCVTTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPD2DQ));
        xPyDict_SetItemString(opcodesDict, "VCVTTPD2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPD2UDQ));
        xPyDict_SetItemString(opcodesDict, "VCVTTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPS2DQ));
        xPyDict_SetItemString(opcodesDict, "VCVTTPS2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPS2UDQ));
        xPyDict_SetItemString(opcodesDict, "VCVTUDQ2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUDQ2PD));
        xPyDict_SetItemString(opcodesDict, "VCVTUDQ2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUDQ2PS));
        xPyDict_SetItemString(opcodesDict, "VDIVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVPD));
        xPyDict_SetItemString(opcodesDict, "VDIVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVPS));
        xPyDict_SetItemString(opcodesDict, "VDIVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVSD));
        xPyDict_SetItemString(opcodesDict, "VDIVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVSS));
        xPyDict_SetItemString(opcodesDict, "VDPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VDPPD));
        xPyDict_SetItemString(opcodesDict, "VDPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VDPPS));
        xPyDict_SetItemString(opcodesDict, "VERR", PyLong_FromUint32(triton::arch::x86::ID_INS_VERR));
        xPyDict_SetItemString(opcodesDict, "VERW", PyLong_FromUint32(triton::arch::x86::ID_INS_VERW));
        xPyDict_SetItemString(opcodesDict, "VEXTRACTF128", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTF128));
        xPyDict_SetItemString(opcodesDict, "VEXTRACTF32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTF32X4));
        xPyDict_SetItemString(opcodesDict, "VEXTRACTF64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTF64X4));
        xPyDict_SetItemString(opcodesDict, "VEXTRACTI128", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTI128));
        xPyDict_SetItemString(opcodesDict, "VEXTRACTI32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTI32X4));
        xPyDict_SetItemString(opcodesDict, "VEXTRACTI64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTI64X4));
        xPyDict_SetItemString(opcodesDict, "VEXTRACTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTPS));
        xPyDict_SetItemString(opcodesDict, "VFMADD132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132PD));
        xPyDict_SetItemString(opcodesDict, "VFMADD132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132PS));
        xPyDict_SetItemString(opcodesDict, "VFMADD213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213PD));
        xPyDict_SetItemString(opcodesDict, "VFMADD213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213PS));
        xPyDict_SetItemString(opcodesDict, "VFMADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDPD));
        xPyDict_SetItemString(opcodesDict, "VFMADD231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231PD));
        xPyDict_SetItemString(opcodesDict, "VFMADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDPS));
        xPyDict_SetItemString(opcodesDict, "VFMADD231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231PS));
        xPyDict_SetItemString(opcodesDict, "VFMADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSD));
        xPyDict_SetItemString(opcodesDict, "VFMADD213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213SD));
        xPyDict_SetItemString(opcodesDict, "VFMADD132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132SD));
        xPyDict_SetItemString(opcodesDict, "VFMADD231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231SD));
        xPyDict_SetItemString(opcodesDict, "VFMADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSS));
        xPyDict_SetItemString(opcodesDict, "VFMADD213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213SS));
        xPyDict_SetItemString(opcodesDict, "VFMADD132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132SS));
        xPyDict_SetItemString(opcodesDict, "VFMADD231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231SS));
        xPyDict_SetItemString(opcodesDict, "VFMADDSUB132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB132PD));
        xPyDict_SetItemString(opcodesDict, "VFMADDSUB132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB132PS));
        xPyDict_SetItemString(opcodesDict, "VFMADDSUB213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB213PD));
        xPyDict_SetItemString(opcodesDict, "VFMADDSUB213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB213PS));
        xPyDict_SetItemString(opcodesDict, "VFMADDSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUBPD));
        xPyDict_SetItemString(opcodesDict, "VFMADDSUB231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB231PD));
        xPyDict_SetItemString(opcodesDict, "VFMADDSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUBPS));
        xPyDict_SetItemString(opcodesDict, "VFMADDSUB231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB231PS));
        xPyDict_SetItemString(opcodesDict, "VFMSUB132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132PD));
        xPyDict_SetItemString(opcodesDict, "VFMSUB132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132PS));
        xPyDict_SetItemString(opcodesDict, "VFMSUB213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213PD));
        xPyDict_SetItemString(opcodesDict, "VFMSUB213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213PS));
        xPyDict_SetItemString(opcodesDict, "VFMSUBADD132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD132PD));
        xPyDict_SetItemString(opcodesDict, "VFMSUBADD132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD132PS));
        xPyDict_SetItemString(opcodesDict, "VFMSUBADD213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD213PD));
        xPyDict_SetItemString(opcodesDict, "VFMSUBADD213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD213PS));
        xPyDict_SetItemString(opcodesDict, "VFMSUBADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADDPD));
        xPyDict_SetItemString(opcodesDict, "VFMSUBADD231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD231PD));
        xPyDict_SetItemString(opcodesDict, "VFMSUBADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADDPS));
        xPyDict_SetItemString(opcodesDict, "VFMSUBADD231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD231PS));
        xPyDict_SetItemString(opcodesDict, "VFMSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBPD));
        xPyDict_SetItemString(opcodesDict, "VFMSUB231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231PD));
        xPyDict_SetItemString(opcodesDict, "VFMSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBPS));
        xPyDict_SetItemString(opcodesDict, "VFMSUB231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231PS));
        xPyDict_SetItemString(opcodesDict, "VFMSUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBSD));
        xPyDict_SetItemString(opcodesDict, "VFMSUB213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213SD));
        xPyDict_SetItemString(opcodesDict, "VFMSUB132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132SD));
        xPyDict_SetItemString(opcodesDict, "VFMSUB231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231SD));
        xPyDict_SetItemString(opcodesDict, "VFMSUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBSS));
        xPyDict_SetItemString(opcodesDict, "VFMSUB213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213SS));
        xPyDict_SetItemString(opcodesDict, "VFMSUB132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132SS));
        xPyDict_SetItemString(opcodesDict, "VFMSUB231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231SS));
        xPyDict_SetItemString(opcodesDict, "VFNMADD132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132PD));
        xPyDict_SetItemString(opcodesDict, "VFNMADD132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132PS));
        xPyDict_SetItemString(opcodesDict, "VFNMADD213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213PD));
        xPyDict_SetItemString(opcodesDict, "VFNMADD213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213PS));
        xPyDict_SetItemString(opcodesDict, "VFNMADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDPD));
        xPyDict_SetItemString(opcodesDict, "VFNMADD231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231PD));
        xPyDict_SetItemString(opcodesDict, "VFNMADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDPS));
        xPyDict_SetItemString(opcodesDict, "VFNMADD231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231PS));
        xPyDict_SetItemString(opcodesDict, "VFNMADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDSD));
        xPyDict_SetItemString(opcodesDict, "VFNMADD213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213SD));
        xPyDict_SetItemString(opcodesDict, "VFNMADD132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132SD));
        xPyDict_SetItemString(opcodesDict, "VFNMADD231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231SD));
        xPyDict_SetItemString(opcodesDict, "VFNMADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDSS));
        xPyDict_SetItemString(opcodesDict, "VFNMADD213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213SS));
        xPyDict_SetItemString(opcodesDict, "VFNMADD132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132SS));
        xPyDict_SetItemString(opcodesDict, "VFNMADD231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231SS));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132PD));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132PS));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213PD));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213PS));
        xPyDict_SetItemString(opcodesDict, "VFNMSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBPD));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231PD));
        xPyDict_SetItemString(opcodesDict, "VFNMSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBPS));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231PS));
        xPyDict_SetItemString(opcodesDict, "VFNMSUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBSD));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213SD));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132SD));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231SD));
        xPyDict_SetItemString(opcodesDict, "VFNMSUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBSS));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213SS));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132SS));
        xPyDict_SetItemString(opcodesDict, "VFNMSUB231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231SS));
        xPyDict_SetItemString(opcodesDict, "VFRCZPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZPD));
        xPyDict_SetItemString(opcodesDict, "VFRCZPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZPS));
        xPyDict_SetItemString(opcodesDict, "VFRCZSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZSD));
        xPyDict_SetItemString(opcodesDict, "VFRCZSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZSS));
        xPyDict_SetItemString(opcodesDict, "VORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VORPD));
        xPyDict_SetItemString(opcodesDict, "VORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VORPS));
        xPyDict_SetItemString(opcodesDict, "VXORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VXORPD));
        xPyDict_SetItemString(opcodesDict, "VXORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VXORPS));
        xPyDict_SetItemString(opcodesDict, "VGATHERDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERDPD));
        xPyDict_SetItemString(opcodesDict, "VGATHERDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERDPS));
        xPyDict_SetItemString(opcodesDict, "VGATHERPF0DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0DPD));
        xPyDict_SetItemString(opcodesDict, "VGATHERPF0DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0DPS));
        xPyDict_SetItemString(opcodesDict, "VGATHERPF0QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0QPD));
        xPyDict_SetItemString(opcodesDict, "VGATHERPF0QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0QPS));
        xPyDict_SetItemString(opcodesDict, "VGATHERPF1DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1DPD));
        xPyDict_SetItemString(opcodesDict, "VGATHERPF1DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1DPS));
        xPyDict_SetItemString(opcodesDict, "VGATHERPF1QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1QPD));
        xPyDict_SetItemString(opcodesDict, "VGATHERPF1QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1QPS));
        xPyDict_SetItemString(opcodesDict, "VGATHERQPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERQPD));
        xPyDict_SetItemString(opcodesDict, "VGATHERQPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERQPS));
        xPyDict_SetItemString(opcodesDict, "VHADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VHADDPD));
        xPyDict_SetItemString(opcodesDict, "VHADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VHADDPS));
        xPyDict_SetItemString(opcodesDict, "VHSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VHSUBPD));
        xPyDict_SetItemString(opcodesDict, "VHSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VHSUBPS));
        xPyDict_SetItemString(opcodesDict, "VINSERTF128", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTF128));
        xPyDict_SetItemString(opcodesDict, "VINSERTF32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTF32X4));
        xPyDict_SetItemString(opcodesDict, "VINSERTF64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTF64X4));
        xPyDict_SetItemString(opcodesDict, "VINSERTI128", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTI128));
        xPyDict_SetItemString(opcodesDict, "VINSERTI32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTI32X4));
        xPyDict_SetItemString(opcodesDict, "VINSERTI64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTI64X4));
        xPyDict_SetItemString(opcodesDict, "VINSERTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTPS));
        xPyDict_SetItemString(opcodesDict, "VLDDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_VLDDQU));
        xPyDict_SetItemString(opcodesDict, "VLDMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_VLDMXCSR));
        xPyDict_SetItemString(opcodesDict, "VMASKMOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_VMASKMOVDQU));
        xPyDict_SetItemString(opcodesDict, "VMASKMOVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMASKMOVPD));
        xPyDict_SetItemString(opcodesDict, "VMASKMOVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMASKMOVPS));
        xPyDict_SetItemString(opcodesDict, "VMAXPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXPD));
        xPyDict_SetItemString(opcodesDict, "VMAXPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXPS));
        xPyDict_SetItemString(opcodesDict, "VMAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXSD));
        xPyDict_SetItemString(opcodesDict, "VMAXSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXSS));
        xPyDict_SetItemString(opcodesDict, "VMCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_VMCALL));
        xPyDict_SetItemString(opcodesDict, "VMCLEAR", PyLong_FromUint32(triton::arch::x86::ID_INS_VMCLEAR));
        xPyDict_SetItemString(opcodesDict, "VMFUNC", PyLong_FromUint32(triton::arch::x86::ID_INS_VMFUNC));
        xPyDict_SetItemString(opcodesDict, "VMINPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINPD));
        xPyDict_SetItemString(opcodesDict, "VMINPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINPS));
        xPyDict_SetItemString(opcodesDict, "VMINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINSD));
        xPyDict_SetItemString(opcodesDict, "VMINSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINSS));
        xPyDict_SetItemString(opcodesDict, "VMLAUNCH", PyLong_FromUint32(triton::arch::x86::ID_INS_VMLAUNCH));
        xPyDict_SetItemString(opcodesDict, "VMLOAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMLOAD));
        xPyDict_SetItemString(opcodesDict, "VMMCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_VMMCALL));
        xPyDict_SetItemString(opcodesDict, "VMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVQ));
        xPyDict_SetItemString(opcodesDict, "VMOVDDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDDUP));
        xPyDict_SetItemString(opcodesDict, "VMOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVD));
        xPyDict_SetItemString(opcodesDict, "VMOVDQA32", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQA32));
        xPyDict_SetItemString(opcodesDict, "VMOVDQA64", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQA64));
        xPyDict_SetItemString(opcodesDict, "VMOVDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQA));
        xPyDict_SetItemString(opcodesDict, "VMOVDQU16", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU16));
        xPyDict_SetItemString(opcodesDict, "VMOVDQU32", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU32));
        xPyDict_SetItemString(opcodesDict, "VMOVDQU64", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU64));
        xPyDict_SetItemString(opcodesDict, "VMOVDQU8", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU8));
        xPyDict_SetItemString(opcodesDict, "VMOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU));
        xPyDict_SetItemString(opcodesDict, "VMOVHLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVHLPS));
        xPyDict_SetItemString(opcodesDict, "VMOVHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVHPD));
        xPyDict_SetItemString(opcodesDict, "VMOVHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVHPS));
        xPyDict_SetItemString(opcodesDict, "VMOVLHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVLHPS));
        xPyDict_SetItemString(opcodesDict, "VMOVLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVLPD));
        xPyDict_SetItemString(opcodesDict, "VMOVLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVLPS));
        xPyDict_SetItemString(opcodesDict, "VMOVMSKPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVMSKPD));
        xPyDict_SetItemString(opcodesDict, "VMOVMSKPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVMSKPS));
        xPyDict_SetItemString(opcodesDict, "VMOVNTDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTDQA));
        xPyDict_SetItemString(opcodesDict, "VMOVNTDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTDQ));
        xPyDict_SetItemString(opcodesDict, "VMOVNTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTPD));
        xPyDict_SetItemString(opcodesDict, "VMOVNTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTPS));
        xPyDict_SetItemString(opcodesDict, "VMOVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSD));
        xPyDict_SetItemString(opcodesDict, "VMOVSHDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSHDUP));
        xPyDict_SetItemString(opcodesDict, "VMOVSLDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSLDUP));
        xPyDict_SetItemString(opcodesDict, "VMOVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSS));
        xPyDict_SetItemString(opcodesDict, "VMOVUPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVUPD));
        xPyDict_SetItemString(opcodesDict, "VMOVUPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVUPS));
        xPyDict_SetItemString(opcodesDict, "VMPSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VMPSADBW));
        xPyDict_SetItemString(opcodesDict, "VMPTRLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMPTRLD));
        xPyDict_SetItemString(opcodesDict, "VMPTRST", PyLong_FromUint32(triton::arch::x86::ID_INS_VMPTRST));
        xPyDict_SetItemString(opcodesDict, "VMREAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMREAD));
        xPyDict_SetItemString(opcodesDict, "VMRESUME", PyLong_FromUint32(triton::arch::x86::ID_INS_VMRESUME));
        xPyDict_SetItemString(opcodesDict, "VMRUN", PyLong_FromUint32(triton::arch::x86::ID_INS_VMRUN));
        xPyDict_SetItemString(opcodesDict, "VMSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_VMSAVE));
        xPyDict_SetItemString(opcodesDict, "VMULPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULPD));
        xPyDict_SetItemString(opcodesDict, "VMULPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULPS));
        xPyDict_SetItemString(opcodesDict, "VMULSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULSD));
        xPyDict_SetItemString(opcodesDict, "VMULSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULSS));
        xPyDict_SetItemString(opcodesDict, "VMWRITE", PyLong_FromUint32(triton::arch::x86::ID_INS_VMWRITE));
        xPyDict_SetItemString(opcodesDict, "VMXOFF", PyLong_FromUint32(triton::arch::x86::ID_INS_VMXOFF));
        xPyDict_SetItemString(opcodesDict, "VMXON", PyLong_FromUint32(triton::arch::x86::ID_INS_VMXON));
        xPyDict_SetItemString(opcodesDict, "VPABSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSB));
        xPyDict_SetItemString(opcodesDict, "VPABSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSD));
        xPyDict_SetItemString(opcodesDict, "VPABSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSQ));
        xPyDict_SetItemString(opcodesDict, "VPABSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSW));
        xPyDict_SetItemString(opcodesDict, "VPACKSSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKSSDW));
        xPyDict_SetItemString(opcodesDict, "VPACKSSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKSSWB));
        xPyDict_SetItemString(opcodesDict, "VPACKUSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKUSDW));
        xPyDict_SetItemString(opcodesDict, "VPACKUSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKUSWB));
        xPyDict_SetItemString(opcodesDict, "VPADDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDB));
        xPyDict_SetItemString(opcodesDict, "VPADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDD));
        xPyDict_SetItemString(opcodesDict, "VPADDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDQ));
        xPyDict_SetItemString(opcodesDict, "VPADDSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDSB));
        xPyDict_SetItemString(opcodesDict, "VPADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDSW));
        xPyDict_SetItemString(opcodesDict, "VPADDUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDUSB));
        xPyDict_SetItemString(opcodesDict, "VPADDUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDUSW));
        xPyDict_SetItemString(opcodesDict, "VPADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDW));
        xPyDict_SetItemString(opcodesDict, "VPALIGNR", PyLong_FromUint32(triton::arch::x86::ID_INS_VPALIGNR));
        xPyDict_SetItemString(opcodesDict, "VPANDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDD));
        xPyDict_SetItemString(opcodesDict, "VPANDND", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDND));
        xPyDict_SetItemString(opcodesDict, "VPANDNQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDNQ));
        xPyDict_SetItemString(opcodesDict, "VPANDN", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDN));
        xPyDict_SetItemString(opcodesDict, "VPANDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDQ));
        xPyDict_SetItemString(opcodesDict, "VPAND", PyLong_FromUint32(triton::arch::x86::ID_INS_VPAND));
        xPyDict_SetItemString(opcodesDict, "VPAVGB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPAVGB));
        xPyDict_SetItemString(opcodesDict, "VPAVGW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPAVGW));
        xPyDict_SetItemString(opcodesDict, "VPBLENDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDD));
        xPyDict_SetItemString(opcodesDict, "VPBLENDMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDMD));
        xPyDict_SetItemString(opcodesDict, "VPBLENDMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDMQ));
        xPyDict_SetItemString(opcodesDict, "VPBLENDVB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDVB));
        xPyDict_SetItemString(opcodesDict, "VPBLENDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDW));
        xPyDict_SetItemString(opcodesDict, "VPBROADCASTB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTB));
        xPyDict_SetItemString(opcodesDict, "VPBROADCASTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTD));
        xPyDict_SetItemString(opcodesDict, "VPBROADCASTMB2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTMB2Q));
        xPyDict_SetItemString(opcodesDict, "VPBROADCASTMW2D", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTMW2D));
        xPyDict_SetItemString(opcodesDict, "VPBROADCASTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTQ));
        xPyDict_SetItemString(opcodesDict, "VPBROADCASTW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTW));
        xPyDict_SetItemString(opcodesDict, "VPCLMULQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCLMULQDQ));
        xPyDict_SetItemString(opcodesDict, "VPCMOV", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMOV));
        xPyDict_SetItemString(opcodesDict, "VPCMP", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMP));
        xPyDict_SetItemString(opcodesDict, "VPCMPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPD));
        xPyDict_SetItemString(opcodesDict, "VPCMPEQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQB));
        xPyDict_SetItemString(opcodesDict, "VPCMPEQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQD));
        xPyDict_SetItemString(opcodesDict, "VPCMPEQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQQ));
        xPyDict_SetItemString(opcodesDict, "VPCMPEQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQW));
        xPyDict_SetItemString(opcodesDict, "VPCMPESTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPESTRI));
        xPyDict_SetItemString(opcodesDict, "VPCMPESTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPESTRM));
        xPyDict_SetItemString(opcodesDict, "VPCMPGTB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTB));
        xPyDict_SetItemString(opcodesDict, "VPCMPGTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTD));
        xPyDict_SetItemString(opcodesDict, "VPCMPGTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTQ));
        xPyDict_SetItemString(opcodesDict, "VPCMPGTW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTW));
        xPyDict_SetItemString(opcodesDict, "VPCMPISTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPISTRI));
        xPyDict_SetItemString(opcodesDict, "VPCMPISTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPISTRM));
        xPyDict_SetItemString(opcodesDict, "VPCMPQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPQ));
        xPyDict_SetItemString(opcodesDict, "VPCMPUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPUD));
        xPyDict_SetItemString(opcodesDict, "VPCMPUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPUQ));
        xPyDict_SetItemString(opcodesDict, "VPCOMB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMB));
        xPyDict_SetItemString(opcodesDict, "VPCOMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMD));
        xPyDict_SetItemString(opcodesDict, "VPCOMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMQ));
        xPyDict_SetItemString(opcodesDict, "VPCOMUB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUB));
        xPyDict_SetItemString(opcodesDict, "VPCOMUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUD));
        xPyDict_SetItemString(opcodesDict, "VPCOMUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUQ));
        xPyDict_SetItemString(opcodesDict, "VPCOMUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUW));
        xPyDict_SetItemString(opcodesDict, "VPCOMW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMW));
        xPyDict_SetItemString(opcodesDict, "VPCONFLICTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCONFLICTD));
        xPyDict_SetItemString(opcodesDict, "VPCONFLICTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCONFLICTQ));
        xPyDict_SetItemString(opcodesDict, "VPERM2F128", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERM2F128));
        xPyDict_SetItemString(opcodesDict, "VPERM2I128", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERM2I128));
        xPyDict_SetItemString(opcodesDict, "VPERMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMD));
        xPyDict_SetItemString(opcodesDict, "VPERMI2D", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2D));
        xPyDict_SetItemString(opcodesDict, "VPERMI2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2PD));
        xPyDict_SetItemString(opcodesDict, "VPERMI2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2PS));
        xPyDict_SetItemString(opcodesDict, "VPERMI2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2Q));
        xPyDict_SetItemString(opcodesDict, "VPERMIL2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMIL2PD));
        xPyDict_SetItemString(opcodesDict, "VPERMIL2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMIL2PS));
        xPyDict_SetItemString(opcodesDict, "VPERMILPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMILPD));
        xPyDict_SetItemString(opcodesDict, "VPERMILPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMILPS));
        xPyDict_SetItemString(opcodesDict, "VPERMPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMPD));
        xPyDict_SetItemString(opcodesDict, "VPERMPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMPS));
        xPyDict_SetItemString(opcodesDict, "VPERMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMQ));
        xPyDict_SetItemString(opcodesDict, "VPERMT2D", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2D));
        xPyDict_SetItemString(opcodesDict, "VPERMT2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2PD));
        xPyDict_SetItemString(opcodesDict, "VPERMT2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2PS));
        xPyDict_SetItemString(opcodesDict, "VPERMT2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2Q));
        xPyDict_SetItemString(opcodesDict, "VPEXTRB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRB));
        xPyDict_SetItemString(opcodesDict, "VPEXTRD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRD));
        xPyDict_SetItemString(opcodesDict, "VPEXTRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRQ));
        xPyDict_SetItemString(opcodesDict, "VPEXTRW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRW));
        xPyDict_SetItemString(opcodesDict, "VPGATHERDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERDD));
        xPyDict_SetItemString(opcodesDict, "VPGATHERDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERDQ));
        xPyDict_SetItemString(opcodesDict, "VPGATHERQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERQD));
        xPyDict_SetItemString(opcodesDict, "VPGATHERQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERQQ));
        xPyDict_SetItemString(opcodesDict, "VPHADDBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDBD));
        xPyDict_SetItemString(opcodesDict, "VPHADDBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDBQ));
        xPyDict_SetItemString(opcodesDict, "VPHADDBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDBW));
        xPyDict_SetItemString(opcodesDict, "VPHADDDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDDQ));
        xPyDict_SetItemString(opcodesDict, "VPHADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDD));
        xPyDict_SetItemString(opcodesDict, "VPHADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDSW));
        xPyDict_SetItemString(opcodesDict, "VPHADDUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUBD));
        xPyDict_SetItemString(opcodesDict, "VPHADDUBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUBQ));
        xPyDict_SetItemString(opcodesDict, "VPHADDUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUBW));
        xPyDict_SetItemString(opcodesDict, "VPHADDUDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUDQ));
        xPyDict_SetItemString(opcodesDict, "VPHADDUWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUWD));
        xPyDict_SetItemString(opcodesDict, "VPHADDUWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUWQ));
        xPyDict_SetItemString(opcodesDict, "VPHADDWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDWD));
        xPyDict_SetItemString(opcodesDict, "VPHADDWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDWQ));
        xPyDict_SetItemString(opcodesDict, "VPHADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDW));
        xPyDict_SetItemString(opcodesDict, "VPHMINPOSUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHMINPOSUW));
        xPyDict_SetItemString(opcodesDict, "VPHSUBBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBBW));
        xPyDict_SetItemString(opcodesDict, "VPHSUBDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBDQ));
        xPyDict_SetItemString(opcodesDict, "VPHSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBD));
        xPyDict_SetItemString(opcodesDict, "VPHSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBSW));
        xPyDict_SetItemString(opcodesDict, "VPHSUBWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBWD));
        xPyDict_SetItemString(opcodesDict, "VPHSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBW));
        xPyDict_SetItemString(opcodesDict, "VPINSRB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRB));
        xPyDict_SetItemString(opcodesDict, "VPINSRD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRD));
        xPyDict_SetItemString(opcodesDict, "VPINSRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRQ));
        xPyDict_SetItemString(opcodesDict, "VPINSRW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRW));
        xPyDict_SetItemString(opcodesDict, "VPLZCNTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPLZCNTD));
        xPyDict_SetItemString(opcodesDict, "VPLZCNTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPLZCNTQ));
        xPyDict_SetItemString(opcodesDict, "VPMACSDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSDD));
        xPyDict_SetItemString(opcodesDict, "VPMACSDQH", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSDQH));
        xPyDict_SetItemString(opcodesDict, "VPMACSDQL", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSDQL));
        xPyDict_SetItemString(opcodesDict, "VPMACSSDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSDD));
        xPyDict_SetItemString(opcodesDict, "VPMACSSDQH", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSDQH));
        xPyDict_SetItemString(opcodesDict, "VPMACSSDQL", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSDQL));
        xPyDict_SetItemString(opcodesDict, "VPMACSSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSWD));
        xPyDict_SetItemString(opcodesDict, "VPMACSSWW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSWW));
        xPyDict_SetItemString(opcodesDict, "VPMACSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSWD));
        xPyDict_SetItemString(opcodesDict, "VPMACSWW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSWW));
        xPyDict_SetItemString(opcodesDict, "VPMADCSSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADCSSWD));
        xPyDict_SetItemString(opcodesDict, "VPMADCSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADCSWD));
        xPyDict_SetItemString(opcodesDict, "VPMADDUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADDUBSW));
        xPyDict_SetItemString(opcodesDict, "VPMADDWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADDWD));
        xPyDict_SetItemString(opcodesDict, "VPMASKMOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMASKMOVD));
        xPyDict_SetItemString(opcodesDict, "VPMASKMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMASKMOVQ));
        xPyDict_SetItemString(opcodesDict, "VPMAXSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSB));
        xPyDict_SetItemString(opcodesDict, "VPMAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSD));
        xPyDict_SetItemString(opcodesDict, "VPMAXSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSQ));
        xPyDict_SetItemString(opcodesDict, "VPMAXSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSW));
        xPyDict_SetItemString(opcodesDict, "VPMAXUB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUB));
        xPyDict_SetItemString(opcodesDict, "VPMAXUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUD));
        xPyDict_SetItemString(opcodesDict, "VPMAXUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUQ));
        xPyDict_SetItemString(opcodesDict, "VPMAXUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUW));
        xPyDict_SetItemString(opcodesDict, "VPMINSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSB));
        xPyDict_SetItemString(opcodesDict, "VPMINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSD));
        xPyDict_SetItemString(opcodesDict, "VPMINSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSQ));
        xPyDict_SetItemString(opcodesDict, "VPMINSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSW));
        xPyDict_SetItemString(opcodesDict, "VPMINUB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUB));
        xPyDict_SetItemString(opcodesDict, "VPMINUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUD));
        xPyDict_SetItemString(opcodesDict, "VPMINUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUQ));
        xPyDict_SetItemString(opcodesDict, "VPMINUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUW));
        xPyDict_SetItemString(opcodesDict, "VPMOVDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVDB));
        xPyDict_SetItemString(opcodesDict, "VPMOVDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVDW));
        xPyDict_SetItemString(opcodesDict, "VPMOVMSKB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVMSKB));
        xPyDict_SetItemString(opcodesDict, "VPMOVQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVQB));
        xPyDict_SetItemString(opcodesDict, "VPMOVQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVQD));
        xPyDict_SetItemString(opcodesDict, "VPMOVQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVQW));
        xPyDict_SetItemString(opcodesDict, "VPMOVSDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSDB));
        xPyDict_SetItemString(opcodesDict, "VPMOVSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSDW));
        xPyDict_SetItemString(opcodesDict, "VPMOVSQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSQB));
        xPyDict_SetItemString(opcodesDict, "VPMOVSQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSQD));
        xPyDict_SetItemString(opcodesDict, "VPMOVSQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSQW));
        xPyDict_SetItemString(opcodesDict, "VPMOVSXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXBD));
        xPyDict_SetItemString(opcodesDict, "VPMOVSXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXBQ));
        xPyDict_SetItemString(opcodesDict, "VPMOVSXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXBW));
        xPyDict_SetItemString(opcodesDict, "VPMOVSXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXDQ));
        xPyDict_SetItemString(opcodesDict, "VPMOVSXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXWD));
        xPyDict_SetItemString(opcodesDict, "VPMOVSXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXWQ));
        xPyDict_SetItemString(opcodesDict, "VPMOVUSDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSDB));
        xPyDict_SetItemString(opcodesDict, "VPMOVUSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSDW));
        xPyDict_SetItemString(opcodesDict, "VPMOVUSQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSQB));
        xPyDict_SetItemString(opcodesDict, "VPMOVUSQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSQD));
        xPyDict_SetItemString(opcodesDict, "VPMOVUSQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSQW));
        xPyDict_SetItemString(opcodesDict, "VPMOVZXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXBD));
        xPyDict_SetItemString(opcodesDict, "VPMOVZXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXBQ));
        xPyDict_SetItemString(opcodesDict, "VPMOVZXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXBW));
        xPyDict_SetItemString(opcodesDict, "VPMOVZXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXDQ));
        xPyDict_SetItemString(opcodesDict, "VPMOVZXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXWD));
        xPyDict_SetItemString(opcodesDict, "VPMOVZXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXWQ));
        xPyDict_SetItemString(opcodesDict, "VPMULDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULDQ));
        xPyDict_SetItemString(opcodesDict, "VPMULHRSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULHRSW));
        xPyDict_SetItemString(opcodesDict, "VPMULHUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULHUW));
        xPyDict_SetItemString(opcodesDict, "VPMULHW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULHW));
        xPyDict_SetItemString(opcodesDict, "VPMULLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULLD));
        xPyDict_SetItemString(opcodesDict, "VPMULLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULLW));
        xPyDict_SetItemString(opcodesDict, "VPMULUDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULUDQ));
        xPyDict_SetItemString(opcodesDict, "VPORD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPORD));
        xPyDict_SetItemString(opcodesDict, "VPORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPORQ));
        xPyDict_SetItemString(opcodesDict, "VPOR", PyLong_FromUint32(triton::arch::x86::ID_INS_VPOR));
        xPyDict_SetItemString(opcodesDict, "VPPERM", PyLong_FromUint32(triton::arch::x86::ID_INS_VPPERM));
        xPyDict_SetItemString(opcodesDict, "VPROTB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTB));
        xPyDict_SetItemString(opcodesDict, "VPROTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTD));
        xPyDict_SetItemString(opcodesDict, "VPROTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTQ));
        xPyDict_SetItemString(opcodesDict, "VPROTW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTW));
        xPyDict_SetItemString(opcodesDict, "VPSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSADBW));
        xPyDict_SetItemString(opcodesDict, "VPSCATTERDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERDD));
        xPyDict_SetItemString(opcodesDict, "VPSCATTERDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERDQ));
        xPyDict_SetItemString(opcodesDict, "VPSCATTERQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERQD));
        xPyDict_SetItemString(opcodesDict, "VPSCATTERQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERQQ));
        xPyDict_SetItemString(opcodesDict, "VPSHAB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAB));
        xPyDict_SetItemString(opcodesDict, "VPSHAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAD));
        xPyDict_SetItemString(opcodesDict, "VPSHAQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAQ));
        xPyDict_SetItemString(opcodesDict, "VPSHAW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAW));
        xPyDict_SetItemString(opcodesDict, "VPSHLB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLB));
        xPyDict_SetItemString(opcodesDict, "VPSHLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLD));
        xPyDict_SetItemString(opcodesDict, "VPSHLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLQ));
        xPyDict_SetItemString(opcodesDict, "VPSHLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLW));
        xPyDict_SetItemString(opcodesDict, "VPSHUFB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFB));
        xPyDict_SetItemString(opcodesDict, "VPSHUFD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFD));
        xPyDict_SetItemString(opcodesDict, "VPSHUFHW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFHW));
        xPyDict_SetItemString(opcodesDict, "VPSHUFLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFLW));
        xPyDict_SetItemString(opcodesDict, "VPSIGNB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSIGNB));
        xPyDict_SetItemString(opcodesDict, "VPSIGND", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSIGND));
        xPyDict_SetItemString(opcodesDict, "VPSIGNW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSIGNW));
        xPyDict_SetItemString(opcodesDict, "VPSLLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLDQ));
        xPyDict_SetItemString(opcodesDict, "VPSLLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLD));
        xPyDict_SetItemString(opcodesDict, "VPSLLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLQ));
        xPyDict_SetItemString(opcodesDict, "VPSLLVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLVD));
        xPyDict_SetItemString(opcodesDict, "VPSLLVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLVQ));
        xPyDict_SetItemString(opcodesDict, "VPSLLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLW));
        xPyDict_SetItemString(opcodesDict, "VPSRAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAD));
        xPyDict_SetItemString(opcodesDict, "VPSRAQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAQ));
        xPyDict_SetItemString(opcodesDict, "VPSRAVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAVD));
        xPyDict_SetItemString(opcodesDict, "VPSRAVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAVQ));
        xPyDict_SetItemString(opcodesDict, "VPSRAW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAW));
        xPyDict_SetItemString(opcodesDict, "VPSRLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLDQ));
        xPyDict_SetItemString(opcodesDict, "VPSRLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLD));
        xPyDict_SetItemString(opcodesDict, "VPSRLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLQ));
        xPyDict_SetItemString(opcodesDict, "VPSRLVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLVD));
        xPyDict_SetItemString(opcodesDict, "VPSRLVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLVQ));
        xPyDict_SetItemString(opcodesDict, "VPSRLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLW));
        xPyDict_SetItemString(opcodesDict, "VPSUBB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBB));
        xPyDict_SetItemString(opcodesDict, "VPSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBD));
        xPyDict_SetItemString(opcodesDict, "VPSUBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBQ));
        xPyDict_SetItemString(opcodesDict, "VPSUBSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBSB));
        xPyDict_SetItemString(opcodesDict, "VPSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBSW));
        xPyDict_SetItemString(opcodesDict, "VPSUBUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBUSB));
        xPyDict_SetItemString(opcodesDict, "VPSUBUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBUSW));
        xPyDict_SetItemString(opcodesDict, "VPSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBW));
        xPyDict_SetItemString(opcodesDict, "VPTESTMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTMD));
        xPyDict_SetItemString(opcodesDict, "VPTESTMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTMQ));
        xPyDict_SetItemString(opcodesDict, "VPTESTNMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTNMD));
        xPyDict_SetItemString(opcodesDict, "VPTESTNMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTNMQ));
        xPyDict_SetItemString(opcodesDict, "VPTEST", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTEST));
        xPyDict_SetItemString(opcodesDict, "VPUNPCKHBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHBW));
        xPyDict_SetItemString(opcodesDict, "VPUNPCKHDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHDQ));
        xPyDict_SetItemString(opcodesDict, "VPUNPCKHQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHQDQ));
        xPyDict_SetItemString(opcodesDict, "VPUNPCKHWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHWD));
        xPyDict_SetItemString(opcodesDict, "VPUNPCKLBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLBW));
        xPyDict_SetItemString(opcodesDict, "VPUNPCKLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLDQ));
        xPyDict_SetItemString(opcodesDict, "VPUNPCKLQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLQDQ));
        xPyDict_SetItemString(opcodesDict, "VPUNPCKLWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLWD));
        xPyDict_SetItemString(opcodesDict, "VPXORD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPXORD));
        xPyDict_SetItemString(opcodesDict, "VPXORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPXORQ));
        xPyDict_SetItemString(opcodesDict, "VPXOR", PyLong_FromUint32(triton::arch::x86::ID_INS_VPXOR));
        xPyDict_SetItemString(opcodesDict, "VRCP14PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14PD));
        xPyDict_SetItemString(opcodesDict, "VRCP14PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14PS));
        xPyDict_SetItemString(opcodesDict, "VRCP14SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14SD));
        xPyDict_SetItemString(opcodesDict, "VRCP14SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14SS));
        xPyDict_SetItemString(opcodesDict, "VRCP28PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28PD));
        xPyDict_SetItemString(opcodesDict, "VRCP28PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28PS));
        xPyDict_SetItemString(opcodesDict, "VRCP28SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28SD));
        xPyDict_SetItemString(opcodesDict, "VRCP28SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28SS));
        xPyDict_SetItemString(opcodesDict, "VRCPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCPPS));
        xPyDict_SetItemString(opcodesDict, "VRCPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCPSS));
        xPyDict_SetItemString(opcodesDict, "VRNDSCALEPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALEPD));
        xPyDict_SetItemString(opcodesDict, "VRNDSCALEPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALEPS));
        xPyDict_SetItemString(opcodesDict, "VRNDSCALESD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALESD));
        xPyDict_SetItemString(opcodesDict, "VRNDSCALESS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALESS));
        xPyDict_SetItemString(opcodesDict, "VROUNDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDPD));
        xPyDict_SetItemString(opcodesDict, "VROUNDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDPS));
        xPyDict_SetItemString(opcodesDict, "VROUNDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDSD));
        xPyDict_SetItemString(opcodesDict, "VROUNDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDSS));
        xPyDict_SetItemString(opcodesDict, "VRSQRT14PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14PD));
        xPyDict_SetItemString(opcodesDict, "VRSQRT14PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14PS));
        xPyDict_SetItemString(opcodesDict, "VRSQRT14SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14SD));
        xPyDict_SetItemString(opcodesDict, "VRSQRT14SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14SS));
        xPyDict_SetItemString(opcodesDict, "VRSQRT28PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28PD));
        xPyDict_SetItemString(opcodesDict, "VRSQRT28PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28PS));
        xPyDict_SetItemString(opcodesDict, "VRSQRT28SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28SD));
        xPyDict_SetItemString(opcodesDict, "VRSQRT28SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28SS));
        xPyDict_SetItemString(opcodesDict, "VRSQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRTPS));
        xPyDict_SetItemString(opcodesDict, "VRSQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRTSS));
        xPyDict_SetItemString(opcodesDict, "VSCATTERDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERDPD));
        xPyDict_SetItemString(opcodesDict, "VSCATTERDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERDPS));
        xPyDict_SetItemString(opcodesDict, "VSCATTERPF0DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0DPD));
        xPyDict_SetItemString(opcodesDict, "VSCATTERPF0DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0DPS));
        xPyDict_SetItemString(opcodesDict, "VSCATTERPF0QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0QPD));
        xPyDict_SetItemString(opcodesDict, "VSCATTERPF0QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0QPS));
        xPyDict_SetItemString(opcodesDict, "VSCATTERPF1DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1DPD));
        xPyDict_SetItemString(opcodesDict, "VSCATTERPF1DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1DPS));
        xPyDict_SetItemString(opcodesDict, "VSCATTERPF1QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1QPD));
        xPyDict_SetItemString(opcodesDict, "VSCATTERPF1QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1QPS));
        xPyDict_SetItemString(opcodesDict, "VSCATTERQPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERQPD));
        xPyDict_SetItemString(opcodesDict, "VSCATTERQPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERQPS));
        xPyDict_SetItemString(opcodesDict, "VSHUFPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSHUFPD));
        xPyDict_SetItemString(opcodesDict, "VSHUFPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSHUFPS));
        xPyDict_SetItemString(opcodesDict, "VSQRTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTPD));
        xPyDict_SetItemString(opcodesDict, "VSQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTPS));
        xPyDict_SetItemString(opcodesDict, "VSQRTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTSD));
        xPyDict_SetItemString(opcodesDict, "VSQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTSS));
        xPyDict_SetItemString(opcodesDict, "VSTMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_VSTMXCSR));
        xPyDict_SetItemString(opcodesDict, "VSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBPD));
        xPyDict_SetItemString(opcodesDict, "VSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBPS));
        xPyDict_SetItemString(opcodesDict, "VSUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBSD));
        xPyDict_SetItemString(opcodesDict, "VSUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBSS));
        xPyDict_SetItemString(opcodesDict, "VTESTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VTESTPD));
        xPyDict_SetItemString(opcodesDict, "VTESTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VTESTPS));
        xPyDict_SetItemString(opcodesDict, "VUNPCKHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKHPD));
        xPyDict_SetItemString(opcodesDict, "VUNPCKHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKHPS));
        xPyDict_SetItemString(opcodesDict, "VUNPCKLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKLPD));
        xPyDict_SetItemString(opcodesDict, "VUNPCKLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKLPS));
        xPyDict_SetItemString(opcodesDict, "VZEROALL", PyLong_FromUint32(triton::arch::x86::ID_INS_VZEROALL));
        xPyDict_SetItemString(opcodesDict, "VZEROUPPER", PyLong_FromUint32(triton::arch::x86::ID_INS_VZEROUPPER));
        xPyDict_SetItemString(opcodesDict, "WAIT", PyLong_FromUint32(triton::arch::x86::ID_INS_WAIT));
        xPyDict_SetItemString(opcodesDict, "WBINVD", PyLong_FromUint32(triton::arch::x86::ID_INS_WBINVD));
        xPyDict_SetItemString(opcodesDict, "WRFSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_WRFSBASE));
        xPyDict_SetItemString(opcodesDict, "WRGSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_WRGSBASE));
        xPyDict_SetItemString(opcodesDict, "WRMSR", PyLong_FromUint32(triton::arch::x86::ID_INS_WRMSR));
        xPyDict_SetItemString(opcodesDict, "XABORT", PyLong_FromUint32(triton::arch::x86::ID_INS_XABORT));
        xPyDict_SetItemString(opcodesDict, "XACQUIRE", PyLong_FromUint32(triton::arch::x86::ID_INS_XACQUIRE));
        xPyDict_SetItemString(opcodesDict, "XBEGIN", PyLong_FromUint32(triton::arch::x86::ID_INS_XBEGIN));
        xPyDict_SetItemString(opcodesDict, "XCHG", PyLong_FromUint32(triton::arch::x86::ID_INS_XCHG));
        xPyDict_SetItemString(opcodesDict, "FXCH", PyLong_FromUint32(triton::arch::x86::ID_INS_FXCH));
        xPyDict_SetItemString(opcodesDict, "XCRYPTCBC", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTCBC));
        xPyDict_SetItemString(opcodesDict, "XCRYPTCFB", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTCFB));
        xPyDict_SetItemString(opcodesDict, "XCRYPTCTR", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTCTR));
        xPyDict_SetItemString(opcodesDict, "XCRYPTECB", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTECB));
        xPyDict_SetItemString(opcodesDict, "XCRYPTOFB", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTOFB));
        xPyDict_SetItemString(opcodesDict, "XEND", PyLong_FromUint32(triton::arch::x86::ID_INS_XEND));
        xPyDict_SetItemString(opcodesDict, "XGETBV", PyLong_FromUint32(triton::arch::x86::ID_INS_XGETBV));
        xPyDict_SetItemString(opcodesDict, "XLATB", PyLong_FromUint32(triton::arch::x86::ID_INS_XLATB));
        xPyDict_SetItemString(opcodesDict, "XRELEASE", PyLong_FromUint32(triton::arch::x86::ID_INS_XRELEASE));
        xPyDict_SetItemString(opcodesDict, "XRSTOR", PyLong_FromUint32(triton::arch::x86::ID_INS_XRSTOR));
        xPyDict_SetItemString(opcodesDict, "XRSTOR64", PyLong_FromUint32(triton::arch::x86::ID_INS_XRSTOR64));
        xPyDict_SetItemString(opcodesDict, "XSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVE));
        xPyDict_SetItemString(opcodesDict, "XSAVE64", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVE64));
        xPyDict_SetItemString(opcodesDict, "XSAVEOPT", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVEOPT));
        xPyDict_SetItemString(opcodesDict, "XSAVEOPT64", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVEOPT64));
        xPyDict_SetItemString(opcodesDict, "XSETBV", PyLong_FromUint32(triton::arch::x86::ID_INS_XSETBV));
        xPyDict_SetItemString(opcodesDict, "XSHA1", PyLong_FromUint32(triton::arch::x86::ID_INS_XSHA1));
        xPyDict_SetItemString(opcodesDict, "XSHA256", PyLong_FromUint32(triton::arch::x86::ID_INS_XSHA256));
        xPyDict_SetItemString(opcodesDict, "XSTORE", PyLong_FromUint32(triton::arch::x86::ID_INS_XSTORE));
        xPyDict_SetItemString(opcodesDict, "XTEST", PyLong_FromUint32(triton::arch::x86::ID_INS_XTEST));
#ifdef IS_PY3
        return _PyObject_New(&OpcodeNamespace_Type);
#endif
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
