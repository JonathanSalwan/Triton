//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <triton/pythonBindings.hpp>
#include <triton/pythonUtils.hpp>
#include <triton/api.hpp>
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

      void initX86OpcodesNamespace(void) {
        if (!triton::bindings::python::initialized)
          return;

        PyDict_Clear(triton::bindings::python::opcodesDict);

        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INVALID", PyLong_FromUint32(triton::arch::x86::ID_INST_INVALID));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AAA", PyLong_FromUint32(triton::arch::x86::ID_INS_AAA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AAD", PyLong_FromUint32(triton::arch::x86::ID_INS_AAD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AAM", PyLong_FromUint32(triton::arch::x86::ID_INS_AAM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AAS", PyLong_FromUint32(triton::arch::x86::ID_INS_AAS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FABS", PyLong_FromUint32(triton::arch::x86::ID_INS_FABS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ADC", PyLong_FromUint32(triton::arch::x86::ID_INS_ADC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ADCX", PyLong_FromUint32(triton::arch::x86::ID_INS_ADCX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ADD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ADDSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSUBPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ADDSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ADDSUBPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FADD", PyLong_FromUint32(triton::arch::x86::ID_INS_FADD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FIADD", PyLong_FromUint32(triton::arch::x86::ID_INS_FIADD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FADDP", PyLong_FromUint32(triton::arch::x86::ID_INS_FADDP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ADOX", PyLong_FromUint32(triton::arch::x86::ID_INS_ADOX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AESDECLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_AESDECLAST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AESDEC", PyLong_FromUint32(triton::arch::x86::ID_INS_AESDEC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AESENCLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_AESENCLAST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AESENC", PyLong_FromUint32(triton::arch::x86::ID_INS_AESENC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AESIMC", PyLong_FromUint32(triton::arch::x86::ID_INS_AESIMC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AESKEYGENASSIST", PyLong_FromUint32(triton::arch::x86::ID_INS_AESKEYGENASSIST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "AND", PyLong_FromUint32(triton::arch::x86::ID_INS_AND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ANDN", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDN));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ANDNPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDNPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ANDNPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDNPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ANDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ANDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ANDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ARPL", PyLong_FromUint32(triton::arch::x86::ID_INS_ARPL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BEXTR", PyLong_FromUint32(triton::arch::x86::ID_INS_BEXTR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLCFILL", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCFILL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLCI", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLCIC", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCIC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLCMSK", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCMSK));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLCS", PyLong_FromUint32(triton::arch::x86::ID_INS_BLCS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLENDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLENDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLENDVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDVPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLENDVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_BLENDVPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLSFILL", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSFILL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLSI", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLSIC", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSIC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLSMSK", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSMSK));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BLSR", PyLong_FromUint32(triton::arch::x86::ID_INS_BLSR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BOUND", PyLong_FromUint32(triton::arch::x86::ID_INS_BOUND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BSF", PyLong_FromUint32(triton::arch::x86::ID_INS_BSF));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BSR", PyLong_FromUint32(triton::arch::x86::ID_INS_BSR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BSWAP", PyLong_FromUint32(triton::arch::x86::ID_INS_BSWAP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BT", PyLong_FromUint32(triton::arch::x86::ID_INS_BT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BTC", PyLong_FromUint32(triton::arch::x86::ID_INS_BTC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BTR", PyLong_FromUint32(triton::arch::x86::ID_INS_BTR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BTS", PyLong_FromUint32(triton::arch::x86::ID_INS_BTS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "BZHI", PyLong_FromUint32(triton::arch::x86::ID_INS_BZHI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CALL", PyLong_FromUint32(triton::arch::x86::ID_INS_CALL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CBW", PyLong_FromUint32(triton::arch::x86::ID_INS_CBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CDQE", PyLong_FromUint32(triton::arch::x86::ID_INS_CDQE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCHS", PyLong_FromUint32(triton::arch::x86::ID_INS_FCHS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CLAC", PyLong_FromUint32(triton::arch::x86::ID_INS_CLAC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CLC", PyLong_FromUint32(triton::arch::x86::ID_INS_CLC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CLD", PyLong_FromUint32(triton::arch::x86::ID_INS_CLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CLFLUSH", PyLong_FromUint32(triton::arch::x86::ID_INS_CLFLUSH));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CLGI", PyLong_FromUint32(triton::arch::x86::ID_INS_CLGI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CLI", PyLong_FromUint32(triton::arch::x86::ID_INS_CLI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CLTS", PyLong_FromUint32(triton::arch::x86::ID_INS_CLTS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMC", PyLong_FromUint32(triton::arch::x86::ID_INS_CMC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVA", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVAE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVAE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVB", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVBE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVBE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCMOVBE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVBE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCMOVB", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCMOVE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVG", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVG));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVGE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVGE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVL", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVLE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVLE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCMOVNBE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNBE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCMOVNB", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVNE", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCMOVNE", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVNO", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNO));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVNP", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCMOVNU", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVNU));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVNS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVNS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVO", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVO));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVP", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCMOVU", PyLong_FromUint32(triton::arch::x86::ID_INS_FCMOVU));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMOVS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMOVS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMP", PyLong_FromUint32(triton::arch::x86::ID_INS_CMP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMPSB", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMPSD", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMPSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMPSW", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMPXCHG16B", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPXCHG16B));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMPXCHG", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPXCHG));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CMPXCHG8B", PyLong_FromUint32(triton::arch::x86::ID_INS_CMPXCHG8B));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "COMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_COMISD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "COMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_COMISS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCOMP", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCOMPI", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMPI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCOMI", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCOM", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCOS", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CPUID", PyLong_FromUint32(triton::arch::x86::ID_INS_CPUID));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CQO", PyLong_FromUint32(triton::arch::x86::ID_INS_CQO));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CRC32", PyLong_FromUint32(triton::arch::x86::ID_INS_CRC32));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTDQ2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTDQ2PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTDQ2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTDQ2PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPD2DQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTPD2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPD2PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPS2DQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTPS2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPS2PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSD2SI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTSD2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSD2SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTSI2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSI2SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTSI2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSI2SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTSS2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSS2SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTSS2SI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPD2DQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPS2DQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTSD2SI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTSS2SI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CWD", PyLong_FromUint32(triton::arch::x86::ID_INS_CWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CWDE", PyLong_FromUint32(triton::arch::x86::ID_INS_CWDE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DAA", PyLong_FromUint32(triton::arch::x86::ID_INS_DAA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DAS", PyLong_FromUint32(triton::arch::x86::ID_INS_DAS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DATA16", PyLong_FromUint32(triton::arch::x86::ID_INS_DATA16));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DEC", PyLong_FromUint32(triton::arch::x86::ID_INS_DEC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DIV", PyLong_FromUint32(triton::arch::x86::ID_INS_DIV));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DIVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DIVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FDIVR", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIVR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FIDIVR", PyLong_FromUint32(triton::arch::x86::ID_INS_FIDIVR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FDIVRP", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIVRP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DIVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DIVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_DIVSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FDIV", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIV));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FIDIV", PyLong_FromUint32(triton::arch::x86::ID_INS_FIDIV));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FDIVP", PyLong_FromUint32(triton::arch::x86::ID_INS_FDIVP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_DPPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "DPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_DPPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RET", PyLong_FromUint32(triton::arch::x86::ID_INS_RET));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ENCLS", PyLong_FromUint32(triton::arch::x86::ID_INS_ENCLS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ENCLU", PyLong_FromUint32(triton::arch::x86::ID_INS_ENCLU));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ENTER", PyLong_FromUint32(triton::arch::x86::ID_INS_ENTER));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "EXTRACTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_EXTRACTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "EXTRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_EXTRQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "F2XM1", PyLong_FromUint32(triton::arch::x86::ID_INS_F2XM1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_LCALL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LJMP", PyLong_FromUint32(triton::arch::x86::ID_INS_LJMP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FBLD", PyLong_FromUint32(triton::arch::x86::ID_INS_FBLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FBSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FBSTP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FCOMPP", PyLong_FromUint32(triton::arch::x86::ID_INS_FCOMPP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FDECSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FDECSTP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FEMMS", PyLong_FromUint32(triton::arch::x86::ID_INS_FEMMS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FFREE", PyLong_FromUint32(triton::arch::x86::ID_INS_FFREE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FICOM", PyLong_FromUint32(triton::arch::x86::ID_INS_FICOM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FICOMP", PyLong_FromUint32(triton::arch::x86::ID_INS_FICOMP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FINCSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FINCSTP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FLDCW", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDCW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FLDENV", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDENV));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FLDL2E", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDL2E));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FLDL2T", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDL2T));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FLDLG2", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDLG2));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FLDLN2", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDLN2));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FLDPI", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDPI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FNCLEX", PyLong_FromUint32(triton::arch::x86::ID_INS_FNCLEX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FNINIT", PyLong_FromUint32(triton::arch::x86::ID_INS_FNINIT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FNOP", PyLong_FromUint32(triton::arch::x86::ID_INS_FNOP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FNSTCW", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSTCW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FNSTSW", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSTSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FPATAN", PyLong_FromUint32(triton::arch::x86::ID_INS_FPATAN));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FPREM", PyLong_FromUint32(triton::arch::x86::ID_INS_FPREM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FPREM1", PyLong_FromUint32(triton::arch::x86::ID_INS_FPREM1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FPTAN", PyLong_FromUint32(triton::arch::x86::ID_INS_FPTAN));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FRNDINT", PyLong_FromUint32(triton::arch::x86::ID_INS_FRNDINT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FRSTOR", PyLong_FromUint32(triton::arch::x86::ID_INS_FRSTOR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FNSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSAVE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSCALE", PyLong_FromUint32(triton::arch::x86::ID_INS_FSCALE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSETPM", PyLong_FromUint32(triton::arch::x86::ID_INS_FSETPM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSINCOS", PyLong_FromUint32(triton::arch::x86::ID_INS_FSINCOS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FNSTENV", PyLong_FromUint32(triton::arch::x86::ID_INS_FNSTENV));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FXAM", PyLong_FromUint32(triton::arch::x86::ID_INS_FXAM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FXRSTOR", PyLong_FromUint32(triton::arch::x86::ID_INS_FXRSTOR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FXRSTOR64", PyLong_FromUint32(triton::arch::x86::ID_INS_FXRSTOR64));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FXSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_FXSAVE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FXSAVE64", PyLong_FromUint32(triton::arch::x86::ID_INS_FXSAVE64));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FXTRACT", PyLong_FromUint32(triton::arch::x86::ID_INS_FXTRACT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FYL2X", PyLong_FromUint32(triton::arch::x86::ID_INS_FYL2X));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FYL2XP1", PyLong_FromUint32(triton::arch::x86::ID_INS_FYL2XP1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVAPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVAPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVAPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVAPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ORPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ORPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVAPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVAPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVAPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVAPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_XORPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_XORPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "GETSEC", PyLong_FromUint32(triton::arch::x86::ID_INS_GETSEC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "HADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_HADDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "HADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_HADDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "HLT", PyLong_FromUint32(triton::arch::x86::ID_INS_HLT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "HSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_HSUBPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "HSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_HSUBPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "IDIV", PyLong_FromUint32(triton::arch::x86::ID_INS_IDIV));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FILD", PyLong_FromUint32(triton::arch::x86::ID_INS_FILD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "IMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_IMUL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "IN", PyLong_FromUint32(triton::arch::x86::ID_INS_IN));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INC", PyLong_FromUint32(triton::arch::x86::ID_INS_INC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INSB", PyLong_FromUint32(triton::arch::x86::ID_INS_INSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INSERTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_INSERTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INSERTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_INSERTQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INSD", PyLong_FromUint32(triton::arch::x86::ID_INS_INSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INSW", PyLong_FromUint32(triton::arch::x86::ID_INS_INSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INT", PyLong_FromUint32(triton::arch::x86::ID_INS_INT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INT1", PyLong_FromUint32(triton::arch::x86::ID_INS_INT1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INT3", PyLong_FromUint32(triton::arch::x86::ID_INS_INT3));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INTO", PyLong_FromUint32(triton::arch::x86::ID_INS_INTO));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INVD", PyLong_FromUint32(triton::arch::x86::ID_INS_INVD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INVEPT", PyLong_FromUint32(triton::arch::x86::ID_INS_INVEPT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INVLPG", PyLong_FromUint32(triton::arch::x86::ID_INS_INVLPG));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INVLPGA", PyLong_FromUint32(triton::arch::x86::ID_INS_INVLPGA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INVPCID", PyLong_FromUint32(triton::arch::x86::ID_INS_INVPCID));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "INVVPID", PyLong_FromUint32(triton::arch::x86::ID_INS_INVVPID));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "IRET", PyLong_FromUint32(triton::arch::x86::ID_INS_IRET));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "IRETD", PyLong_FromUint32(triton::arch::x86::ID_INS_IRETD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "IRETQ", PyLong_FromUint32(triton::arch::x86::ID_INS_IRETQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FISTTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FISTTP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FIST", PyLong_FromUint32(triton::arch::x86::ID_INS_FIST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FISTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FISTP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "UCOMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_UCOMISD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "UCOMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_UCOMISS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCMP", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCOMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCOMISD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCOMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCOMISS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTSD2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSD2SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTSI2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSI2SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTSI2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSI2SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTSS2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSS2SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSD2SI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTTSD2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSD2USI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSS2SI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTTSS2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTSS2USI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTUSI2SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUSI2SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTUSI2SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUSI2SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VUCOMISD", PyLong_FromUint32(triton::arch::x86::ID_INS_VUCOMISD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VUCOMISS", PyLong_FromUint32(triton::arch::x86::ID_INS_VUCOMISS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JAE", PyLong_FromUint32(triton::arch::x86::ID_INS_JAE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JA", PyLong_FromUint32(triton::arch::x86::ID_INS_JA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JBE", PyLong_FromUint32(triton::arch::x86::ID_INS_JBE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JB", PyLong_FromUint32(triton::arch::x86::ID_INS_JB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JCXZ", PyLong_FromUint32(triton::arch::x86::ID_INS_JCXZ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JECXZ", PyLong_FromUint32(triton::arch::x86::ID_INS_JECXZ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JE", PyLong_FromUint32(triton::arch::x86::ID_INS_JE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JGE", PyLong_FromUint32(triton::arch::x86::ID_INS_JGE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JG", PyLong_FromUint32(triton::arch::x86::ID_INS_JG));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JLE", PyLong_FromUint32(triton::arch::x86::ID_INS_JLE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JL", PyLong_FromUint32(triton::arch::x86::ID_INS_JL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JMP", PyLong_FromUint32(triton::arch::x86::ID_INS_JMP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JNE", PyLong_FromUint32(triton::arch::x86::ID_INS_JNE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JNO", PyLong_FromUint32(triton::arch::x86::ID_INS_JNO));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JNP", PyLong_FromUint32(triton::arch::x86::ID_INS_JNP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JNS", PyLong_FromUint32(triton::arch::x86::ID_INS_JNS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JO", PyLong_FromUint32(triton::arch::x86::ID_INS_JO));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JP", PyLong_FromUint32(triton::arch::x86::ID_INS_JP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JRCXZ", PyLong_FromUint32(triton::arch::x86::ID_INS_JRCXZ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "JS", PyLong_FromUint32(triton::arch::x86::ID_INS_JS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KANDB", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KANDD", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KANDNB", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDNB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KANDND", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KANDNQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDNQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KANDNW", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDNW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KANDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KANDW", PyLong_FromUint32(triton::arch::x86::ID_INS_KANDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KMOVB", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KMOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KMOVW", PyLong_FromUint32(triton::arch::x86::ID_INS_KMOVW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KNOTB", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KNOTD", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KNOTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KNOTW", PyLong_FromUint32(triton::arch::x86::ID_INS_KNOTW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KORB", PyLong_FromUint32(triton::arch::x86::ID_INS_KORB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KORD", PyLong_FromUint32(triton::arch::x86::ID_INS_KORD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KORQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KORTESTW", PyLong_FromUint32(triton::arch::x86::ID_INS_KORTESTW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KORW", PyLong_FromUint32(triton::arch::x86::ID_INS_KORW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KSHIFTLW", PyLong_FromUint32(triton::arch::x86::ID_INS_KSHIFTLW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KSHIFTRW", PyLong_FromUint32(triton::arch::x86::ID_INS_KSHIFTRW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KUNPCKBW", PyLong_FromUint32(triton::arch::x86::ID_INS_KUNPCKBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KXNORB", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KXNORD", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KXNORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KXNORW", PyLong_FromUint32(triton::arch::x86::ID_INS_KXNORW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KXORB", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KXORD", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KXORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "KXORW", PyLong_FromUint32(triton::arch::x86::ID_INS_KXORW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LAHF", PyLong_FromUint32(triton::arch::x86::ID_INS_LAHF));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LAR", PyLong_FromUint32(triton::arch::x86::ID_INS_LAR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LDDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_LDDQU));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LDMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_LDMXCSR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LDS", PyLong_FromUint32(triton::arch::x86::ID_INS_LDS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FLDZ", PyLong_FromUint32(triton::arch::x86::ID_INS_FLDZ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FLD1", PyLong_FromUint32(triton::arch::x86::ID_INS_FLD1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FLD", PyLong_FromUint32(triton::arch::x86::ID_INS_FLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LEA", PyLong_FromUint32(triton::arch::x86::ID_INS_LEA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LEAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_LEAVE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LES", PyLong_FromUint32(triton::arch::x86::ID_INS_LES));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LFENCE", PyLong_FromUint32(triton::arch::x86::ID_INS_LFENCE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LFS", PyLong_FromUint32(triton::arch::x86::ID_INS_LFS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LGDT", PyLong_FromUint32(triton::arch::x86::ID_INS_LGDT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LGS", PyLong_FromUint32(triton::arch::x86::ID_INS_LGS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LIDT", PyLong_FromUint32(triton::arch::x86::ID_INS_LIDT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LLDT", PyLong_FromUint32(triton::arch::x86::ID_INS_LLDT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LMSW", PyLong_FromUint32(triton::arch::x86::ID_INS_LMSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "OR", PyLong_FromUint32(triton::arch::x86::ID_INS_OR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SUB", PyLong_FromUint32(triton::arch::x86::ID_INS_SUB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XOR", PyLong_FromUint32(triton::arch::x86::ID_INS_XOR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LODSB", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LODSD", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LODSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LODSW", PyLong_FromUint32(triton::arch::x86::ID_INS_LODSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LOOP", PyLong_FromUint32(triton::arch::x86::ID_INS_LOOP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LOOPE", PyLong_FromUint32(triton::arch::x86::ID_INS_LOOPE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LOOPNE", PyLong_FromUint32(triton::arch::x86::ID_INS_LOOPNE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RETF", PyLong_FromUint32(triton::arch::x86::ID_INS_RETF));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RETFQ", PyLong_FromUint32(triton::arch::x86::ID_INS_RETFQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LSL", PyLong_FromUint32(triton::arch::x86::ID_INS_LSL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LSS", PyLong_FromUint32(triton::arch::x86::ID_INS_LSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LTR", PyLong_FromUint32(triton::arch::x86::ID_INS_LTR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XADD", PyLong_FromUint32(triton::arch::x86::ID_INS_XADD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "LZCNT", PyLong_FromUint32(triton::arch::x86::ID_INS_LZCNT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MASKMOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_MASKMOVDQU));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MAXPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MAXPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MAXSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MAXSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MFENCE", PyLong_FromUint32(triton::arch::x86::ID_INS_MFENCE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MINPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MINPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MINPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MINPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MINSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MINSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MINSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTPD2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPD2PI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTPI2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPI2PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTPI2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPI2PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTPS2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTPS2PI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTTPD2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPD2PI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "CVTTPS2PI", PyLong_FromUint32(triton::arch::x86::ID_INS_CVTTPS2PI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "EMMS", PyLong_FromUint32(triton::arch::x86::ID_INS_EMMS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MASKMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MASKMOVQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVDQ2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDQ2Q));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVNTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVQ2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVQ2DQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PABSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PABSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PABSD", PyLong_FromUint32(triton::arch::x86::ID_INS_PABSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PABSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PABSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PACKSSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKSSDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PACKSSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKSSWB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PACKUSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKUSWB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PADDB", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PADDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PADDSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PADDUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDUSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PADDUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDUSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PADDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PALIGNR", PyLong_FromUint32(triton::arch::x86::ID_INS_PALIGNR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PANDN", PyLong_FromUint32(triton::arch::x86::ID_INS_PANDN));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PAND", PyLong_FromUint32(triton::arch::x86::ID_INS_PAND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PAVGB", PyLong_FromUint32(triton::arch::x86::ID_INS_PAVGB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PAVGW", PyLong_FromUint32(triton::arch::x86::ID_INS_PAVGW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPEQB", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPEQD", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPEQW", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPGTB", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPGTD", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPGTW", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PEXTRW", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PHADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHADDSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PHADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHADDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PHADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_PHADDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PHSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PHSUBD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PHSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHSUBSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PHSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHSUBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PINSRW", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMADDUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMADDUBSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMADDWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMADDWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMAXSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMAXUB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXUB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMINSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMINUB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINUB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVMSKB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVMSKB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMULHRSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHRSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMULHUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHUW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMULHW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMULLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULLW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMULUDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULUDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "POR", PyLong_FromUint32(triton::arch::x86::ID_INS_POR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSADBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSHUFB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSHUFW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSIGNB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSIGNB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSIGND", PyLong_FromUint32(triton::arch::x86::ID_INS_PSIGND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSIGNW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSIGNW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSLLD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSLLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSLLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSRAD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRAD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSRAW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRAW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSRLD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSRLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSRLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSUBB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSUBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSUBSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSUBUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBUSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSUBUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBUSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSUBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUNPCKHBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUNPCKHDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUNPCKHWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUNPCKLBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUNPCKLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUNPCKLWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PXOR", PyLong_FromUint32(triton::arch::x86::ID_INS_PXOR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MONITOR", PyLong_FromUint32(triton::arch::x86::ID_INS_MONITOR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MONTMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_MONTMUL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOV", PyLong_FromUint32(triton::arch::x86::ID_INS_MOV));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVABS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVABS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVBE", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVBE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVDDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDDUP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDQA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVDQU));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVHLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVHLPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVHPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVHPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVLHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVLHPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVLPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVLPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVMSKPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVMSKPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVMSKPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVMSKPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVNTDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTDQA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVNTDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVNTI", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVNTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVNTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVNTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVNTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVNTSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVSB", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVSHDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSHDUP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVSLDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSLDUP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVSW", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVSX", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVSXD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVSXD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVUPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVUPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVUPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVUPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MOVZX", PyLong_FromUint32(triton::arch::x86::ID_INS_MOVZX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MPSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_MPSADBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MUL", PyLong_FromUint32(triton::arch::x86::ID_INS_MUL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MULPD", PyLong_FromUint32(triton::arch::x86::ID_INS_MULPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MULPS", PyLong_FromUint32(triton::arch::x86::ID_INS_MULPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MULSD", PyLong_FromUint32(triton::arch::x86::ID_INS_MULSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MULSS", PyLong_FromUint32(triton::arch::x86::ID_INS_MULSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MULX", PyLong_FromUint32(triton::arch::x86::ID_INS_MULX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_FMUL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FIMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_FIMUL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FMULP", PyLong_FromUint32(triton::arch::x86::ID_INS_FMULP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "MWAIT", PyLong_FromUint32(triton::arch::x86::ID_INS_MWAIT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "NEG", PyLong_FromUint32(triton::arch::x86::ID_INS_NEG));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "NOP", PyLong_FromUint32(triton::arch::x86::ID_INS_NOP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "NOT", PyLong_FromUint32(triton::arch::x86::ID_INS_NOT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "OUT", PyLong_FromUint32(triton::arch::x86::ID_INS_OUT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "OUTSB", PyLong_FromUint32(triton::arch::x86::ID_INS_OUTSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "OUTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_OUTSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "OUTSW", PyLong_FromUint32(triton::arch::x86::ID_INS_OUTSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PACKUSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PACKUSDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PAUSE", PyLong_FromUint32(triton::arch::x86::ID_INS_PAUSE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PAVGUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PAVGUSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PBLENDVB", PyLong_FromUint32(triton::arch::x86::ID_INS_PBLENDVB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PBLENDW", PyLong_FromUint32(triton::arch::x86::ID_INS_PBLENDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCLMULQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PCLMULQDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPEQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPEQQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPESTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPESTRI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPESTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPESTRM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPGTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPGTQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPISTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPISTRI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PCMPISTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_PCMPISTRM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PDEP", PyLong_FromUint32(triton::arch::x86::ID_INS_PDEP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PEXT", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PEXTRB", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PEXTRD", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PEXTRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PEXTRQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PF2ID", PyLong_FromUint32(triton::arch::x86::ID_INS_PF2ID));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PF2IW", PyLong_FromUint32(triton::arch::x86::ID_INS_PF2IW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFACC", PyLong_FromUint32(triton::arch::x86::ID_INS_PFACC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFADD", PyLong_FromUint32(triton::arch::x86::ID_INS_PFADD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFCMPEQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PFCMPEQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFCMPGE", PyLong_FromUint32(triton::arch::x86::ID_INS_PFCMPGE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFCMPGT", PyLong_FromUint32(triton::arch::x86::ID_INS_PFCMPGT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFMAX", PyLong_FromUint32(triton::arch::x86::ID_INS_PFMAX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFMIN", PyLong_FromUint32(triton::arch::x86::ID_INS_PFMIN));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFMUL", PyLong_FromUint32(triton::arch::x86::ID_INS_PFMUL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFNACC", PyLong_FromUint32(triton::arch::x86::ID_INS_PFNACC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFPNACC", PyLong_FromUint32(triton::arch::x86::ID_INS_PFPNACC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFRCPIT1", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRCPIT1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFRCPIT2", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRCPIT2));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFRCP", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRCP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFRSQIT1", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRSQIT1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFRSQRT", PyLong_FromUint32(triton::arch::x86::ID_INS_PFRSQRT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFSUBR", PyLong_FromUint32(triton::arch::x86::ID_INS_PFSUBR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PFSUB", PyLong_FromUint32(triton::arch::x86::ID_INS_PFSUB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PHMINPOSUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PHMINPOSUW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PI2FD", PyLong_FromUint32(triton::arch::x86::ID_INS_PI2FD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PI2FW", PyLong_FromUint32(triton::arch::x86::ID_INS_PI2FW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PINSRB", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PINSRD", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PINSRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PINSRQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMAXSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMAXUD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXUD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMAXUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMAXUW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMINSB", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMINUD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINUD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMINUW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMINUW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVSXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXBD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVSXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXBQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVSXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVSXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVSXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVSXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVSXWQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVZXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXBD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVZXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXBQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVZXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVZXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVZXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMOVZXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMOVZXWQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMULDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMULHRW", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULHRW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PMULLD", PyLong_FromUint32(triton::arch::x86::ID_INS_PMULLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "POP", PyLong_FromUint32(triton::arch::x86::ID_INS_POP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "POPAW", PyLong_FromUint32(triton::arch::x86::ID_INS_POPAW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "POPAL", PyLong_FromUint32(triton::arch::x86::ID_INS_POPAL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "POPCNT", PyLong_FromUint32(triton::arch::x86::ID_INS_POPCNT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "POPF", PyLong_FromUint32(triton::arch::x86::ID_INS_POPF));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "POPFD", PyLong_FromUint32(triton::arch::x86::ID_INS_POPFD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "POPFQ", PyLong_FromUint32(triton::arch::x86::ID_INS_POPFQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PREFETCH", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCH));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PREFETCHNTA", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHNTA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PREFETCHT0", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHT0));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PREFETCHT1", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHT1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PREFETCHT2", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHT2));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PREFETCHW", PyLong_FromUint32(triton::arch::x86::ID_INS_PREFETCHW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSHUFD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSHUFHW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFHW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSHUFLW", PyLong_FromUint32(triton::arch::x86::ID_INS_PSHUFLW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSLLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSLLDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSRLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PSRLDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PSWAPD", PyLong_FromUint32(triton::arch::x86::ID_INS_PSWAPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PTEST", PyLong_FromUint32(triton::arch::x86::ID_INS_PTEST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUNPCKHQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKHQDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUNPCKLQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUNPCKLQDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUSH", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSH));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUSHAW", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHAW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUSHAL", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHAL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUSHF", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHF));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUSHFD", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHFD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "PUSHFQ", PyLong_FromUint32(triton::arch::x86::ID_INS_PUSHFQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RCL", PyLong_FromUint32(triton::arch::x86::ID_INS_RCL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RCPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_RCPPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RCPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_RCPSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RCR", PyLong_FromUint32(triton::arch::x86::ID_INS_RCR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RDFSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_RDFSBASE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RDGSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_RDGSBASE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RDMSR", PyLong_FromUint32(triton::arch::x86::ID_INS_RDMSR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RDPMC", PyLong_FromUint32(triton::arch::x86::ID_INS_RDPMC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RDRAND", PyLong_FromUint32(triton::arch::x86::ID_INS_RDRAND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RDSEED", PyLong_FromUint32(triton::arch::x86::ID_INS_RDSEED));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RDTSC", PyLong_FromUint32(triton::arch::x86::ID_INS_RDTSC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RDTSCP", PyLong_FromUint32(triton::arch::x86::ID_INS_RDTSCP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ROL", PyLong_FromUint32(triton::arch::x86::ID_INS_ROL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ROR", PyLong_FromUint32(triton::arch::x86::ID_INS_ROR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RORX", PyLong_FromUint32(triton::arch::x86::ID_INS_RORX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ROUNDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ROUNDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ROUNDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "ROUNDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_ROUNDSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RSM", PyLong_FromUint32(triton::arch::x86::ID_INS_RSM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RSQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_RSQRTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "RSQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_RSQRTSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SAHF", PyLong_FromUint32(triton::arch::x86::ID_INS_SAHF));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SAL", PyLong_FromUint32(triton::arch::x86::ID_INS_SAL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SALC", PyLong_FromUint32(triton::arch::x86::ID_INS_SALC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SAR", PyLong_FromUint32(triton::arch::x86::ID_INS_SAR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SARX", PyLong_FromUint32(triton::arch::x86::ID_INS_SARX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SBB", PyLong_FromUint32(triton::arch::x86::ID_INS_SBB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SCASB", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SCASD", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SCASQ", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SCASW", PyLong_FromUint32(triton::arch::x86::ID_INS_SCASW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETAE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETAE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETA", PyLong_FromUint32(triton::arch::x86::ID_INS_SETA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETBE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETBE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETB", PyLong_FromUint32(triton::arch::x86::ID_INS_SETB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETGE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETGE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETG", PyLong_FromUint32(triton::arch::x86::ID_INS_SETG));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETLE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETLE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETL", PyLong_FromUint32(triton::arch::x86::ID_INS_SETL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETNE", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETNO", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNO));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETNP", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETNS", PyLong_FromUint32(triton::arch::x86::ID_INS_SETNS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETO", PyLong_FromUint32(triton::arch::x86::ID_INS_SETO));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETP", PyLong_FromUint32(triton::arch::x86::ID_INS_SETP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SETS", PyLong_FromUint32(triton::arch::x86::ID_INS_SETS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SFENCE", PyLong_FromUint32(triton::arch::x86::ID_INS_SFENCE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SGDT", PyLong_FromUint32(triton::arch::x86::ID_INS_SGDT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHA1MSG1", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1MSG1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHA1MSG2", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1MSG2));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHA1NEXTE", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1NEXTE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHA1RNDS4", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA1RNDS4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHA256MSG1", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA256MSG1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHA256MSG2", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA256MSG2));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHA256RNDS2", PyLong_FromUint32(triton::arch::x86::ID_INS_SHA256RNDS2));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHL", PyLong_FromUint32(triton::arch::x86::ID_INS_SHL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHLD", PyLong_FromUint32(triton::arch::x86::ID_INS_SHLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHLX", PyLong_FromUint32(triton::arch::x86::ID_INS_SHLX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHR", PyLong_FromUint32(triton::arch::x86::ID_INS_SHR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHRD", PyLong_FromUint32(triton::arch::x86::ID_INS_SHRD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHRX", PyLong_FromUint32(triton::arch::x86::ID_INS_SHRX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHUFPD", PyLong_FromUint32(triton::arch::x86::ID_INS_SHUFPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SHUFPS", PyLong_FromUint32(triton::arch::x86::ID_INS_SHUFPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SIDT", PyLong_FromUint32(triton::arch::x86::ID_INS_SIDT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSIN", PyLong_FromUint32(triton::arch::x86::ID_INS_FSIN));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SKINIT", PyLong_FromUint32(triton::arch::x86::ID_INS_SKINIT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SLDT", PyLong_FromUint32(triton::arch::x86::ID_INS_SLDT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SMSW", PyLong_FromUint32(triton::arch::x86::ID_INS_SMSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SQRTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SQRTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_SQRTSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSQRT", PyLong_FromUint32(triton::arch::x86::ID_INS_FSQRT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STAC", PyLong_FromUint32(triton::arch::x86::ID_INS_STAC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STC", PyLong_FromUint32(triton::arch::x86::ID_INS_STC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STD", PyLong_FromUint32(triton::arch::x86::ID_INS_STD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STGI", PyLong_FromUint32(triton::arch::x86::ID_INS_STGI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STI", PyLong_FromUint32(triton::arch::x86::ID_INS_STI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_STMXCSR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STOSB", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STOSD", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STOSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STOSW", PyLong_FromUint32(triton::arch::x86::ID_INS_STOSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "STR", PyLong_FromUint32(triton::arch::x86::ID_INS_STR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FST", PyLong_FromUint32(triton::arch::x86::ID_INS_FST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSTP", PyLong_FromUint32(triton::arch::x86::ID_INS_FSTP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSTPNCE", PyLong_FromUint32(triton::arch::x86::ID_INS_FSTPNCE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSUBR", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUBR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FISUBR", PyLong_FromUint32(triton::arch::x86::ID_INS_FISUBR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSUBRP", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUBRP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_SUBSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSUB", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FISUB", PyLong_FromUint32(triton::arch::x86::ID_INS_FISUB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FSUBP", PyLong_FromUint32(triton::arch::x86::ID_INS_FSUBP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SWAPGS", PyLong_FromUint32(triton::arch::x86::ID_INS_SWAPGS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SYSCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSCALL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SYSENTER", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSENTER));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SYSEXIT", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSEXIT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "SYSRET", PyLong_FromUint32(triton::arch::x86::ID_INS_SYSRET));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "T1MSKC", PyLong_FromUint32(triton::arch::x86::ID_INS_T1MSKC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "TEST", PyLong_FromUint32(triton::arch::x86::ID_INS_TEST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "UD2", PyLong_FromUint32(triton::arch::x86::ID_INS_UD2));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FTST", PyLong_FromUint32(triton::arch::x86::ID_INS_FTST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "TZCNT", PyLong_FromUint32(triton::arch::x86::ID_INS_TZCNT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "TZMSK", PyLong_FromUint32(triton::arch::x86::ID_INS_TZMSK));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FUCOMPI", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMPI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FUCOMI", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FUCOMPP", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMPP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FUCOMP", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOMP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FUCOM", PyLong_FromUint32(triton::arch::x86::ID_INS_FUCOM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "UD2B", PyLong_FromUint32(triton::arch::x86::ID_INS_UD2B));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "UNPCKHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKHPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "UNPCKHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKHPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "UNPCKLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKLPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "UNPCKLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_UNPCKLPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VADDSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSUBPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VADDSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VADDSUBPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VAESDECLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESDECLAST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VAESDEC", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESDEC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VAESENCLAST", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESENCLAST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VAESENC", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESENC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VAESIMC", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESIMC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VAESKEYGENASSIST", PyLong_FromUint32(triton::arch::x86::ID_INS_VAESKEYGENASSIST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VALIGND", PyLong_FromUint32(triton::arch::x86::ID_INS_VALIGND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VALIGNQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VALIGNQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VANDNPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDNPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VANDNPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDNPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VANDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VANDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VANDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBLENDMPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDMPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBLENDMPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDMPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBLENDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBLENDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBLENDVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDVPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBLENDVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBLENDVPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBROADCASTF128", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTF128));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBROADCASTI128", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTI128));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBROADCASTI32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTI32X4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBROADCASTI64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTI64X4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBROADCASTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VBROADCASTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VBROADCASTSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCMPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCMPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCMPSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCMPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCMPSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTDQ2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTDQ2PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTDQ2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTDQ2PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTPD2DQX", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2DQX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2DQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTPD2PSX", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2PSX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTPD2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTPD2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPD2UDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTPH2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPH2PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2DQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTPS2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTPS2PH", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2PH));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTPS2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTPS2UDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTSD2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSD2SI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTSD2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSD2USI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTSS2SI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSS2SI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTSS2USI", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTSS2USI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTTPD2DQX", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPD2DQX));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTTPD2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPD2DQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTTPD2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPD2UDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTTPS2DQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPS2DQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTTPS2UDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTTPS2UDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTUDQ2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUDQ2PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VCVTUDQ2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VCVTUDQ2PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VDIVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VDIVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VDIVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VDIVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VDIVSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VDPPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VDPPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VDPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VDPPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VERR", PyLong_FromUint32(triton::arch::x86::ID_INS_VERR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VERW", PyLong_FromUint32(triton::arch::x86::ID_INS_VERW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VEXTRACTF128", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTF128));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VEXTRACTF32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTF32X4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VEXTRACTF64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTF64X4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VEXTRACTI128", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTI128));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VEXTRACTI32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTI32X4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VEXTRACTI64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTI64X4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VEXTRACTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VEXTRACTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD213SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD132SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADD231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADD231SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDSUB132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB132PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDSUB132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB132PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDSUB213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB213PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDSUB213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB213PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUBPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDSUB231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB231PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUBPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMADDSUB231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMADDSUB231PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBADD132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD132PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBADD132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD132PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBADD213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD213PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBADD213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD213PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBADD231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD231PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBADD231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBADD231PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUBSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB213SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB132SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFMSUB231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFMSUB231SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADDSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD213SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD132SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMADD231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMADD231SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB132PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB132PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB213PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB213PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB231PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB231PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB213SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB132SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB231SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUBSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB213SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB213SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB132SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB132SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFNMSUB231SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFNMSUB231SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFRCZPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFRCZPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFRCZSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VFRCZSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VFRCZSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VORPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VORPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VXORPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VXORPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VXORPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VXORPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERPF0DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0DPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERPF0DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0DPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERPF0QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0QPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERPF0QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF0QPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERPF1DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1DPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERPF1DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1DPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERPF1QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1QPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERPF1QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERPF1QPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERQPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERQPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VGATHERQPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VGATHERQPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VHADDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VHADDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VHADDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VHADDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VHSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VHSUBPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VHSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VHSUBPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VINSERTF128", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTF128));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VINSERTF32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTF32X4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VINSERTF64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTF64X4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VINSERTI128", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTI128));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VINSERTI32X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTI32X4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VINSERTI64X4", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTI64X4));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VINSERTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VINSERTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VLDDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_VLDDQU));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VLDMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_VLDMXCSR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMASKMOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_VMASKMOVDQU));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMASKMOVPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMASKMOVPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMASKMOVPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMASKMOVPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMAXPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMAXPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMAXSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMAXSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_VMCALL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMCLEAR", PyLong_FromUint32(triton::arch::x86::ID_INS_VMCLEAR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMFUNC", PyLong_FromUint32(triton::arch::x86::ID_INS_VMFUNC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMINPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMINPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMINSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMINSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMLAUNCH", PyLong_FromUint32(triton::arch::x86::ID_INS_VMLAUNCH));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMLOAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMLOAD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMMCALL", PyLong_FromUint32(triton::arch::x86::ID_INS_VMMCALL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVDDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDDUP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVDQA32", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQA32));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVDQA64", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQA64));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVDQU16", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU16));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVDQU32", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU32));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVDQU64", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU64));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVDQU8", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU8));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVDQU", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVDQU));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVHLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVHLPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVHPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVHPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVLHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVLHPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVLPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVLPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVMSKPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVMSKPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVMSKPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVMSKPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVNTDQA", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTDQA));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVNTDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVNTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVNTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVNTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVSHDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSHDUP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVSLDUP", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSLDUP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVUPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVUPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMOVUPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMOVUPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMPSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VMPSADBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMPTRLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMPTRLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMPTRST", PyLong_FromUint32(triton::arch::x86::ID_INS_VMPTRST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMREAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMREAD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMRESUME", PyLong_FromUint32(triton::arch::x86::ID_INS_VMRESUME));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMRUN", PyLong_FromUint32(triton::arch::x86::ID_INS_VMRUN));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_VMSAVE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMULPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMULPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMULSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMULSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VMULSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMWRITE", PyLong_FromUint32(triton::arch::x86::ID_INS_VMWRITE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMXOFF", PyLong_FromUint32(triton::arch::x86::ID_INS_VMXOFF));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VMXON", PyLong_FromUint32(triton::arch::x86::ID_INS_VMXON));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPABSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPABSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPABSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPABSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPABSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPACKSSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKSSDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPACKSSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKSSWB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPACKUSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKUSDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPACKUSWB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPACKUSWB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPADDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPADDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPADDSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPADDUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDUSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPADDUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDUSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPADDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPALIGNR", PyLong_FromUint32(triton::arch::x86::ID_INS_VPALIGNR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPANDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPANDND", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPANDNQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDNQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPANDN", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDN));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPANDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPANDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPAND", PyLong_FromUint32(triton::arch::x86::ID_INS_VPAND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPAVGB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPAVGB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPAVGW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPAVGW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBLENDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBLENDMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDMD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBLENDMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDMQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBLENDVB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDVB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBLENDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBLENDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBROADCASTB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBROADCASTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBROADCASTMB2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTMB2Q));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBROADCASTMW2D", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTMW2D));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBROADCASTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPBROADCASTW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPBROADCASTW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCLMULQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCLMULQDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMOV", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMOV));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMP", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMP));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPEQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPEQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPEQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPEQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPEQW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPESTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPESTRI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPESTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPESTRM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPGTB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPGTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPGTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPGTW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPGTW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPISTRI", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPISTRI));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPISTRM", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPISTRM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPUD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCMPUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCMPUQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCOMB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCOMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCOMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCOMUB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCOMUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCOMUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCOMUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMUW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCOMW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCOMW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCONFLICTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCONFLICTD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPCONFLICTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPCONFLICTQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERM2F128", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERM2F128));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERM2I128", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERM2I128));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMI2D", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2D));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMI2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMI2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMI2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMI2Q));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMIL2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMIL2PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMIL2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMIL2PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMILPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMILPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMILPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMILPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMT2D", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2D));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMT2PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMT2PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPERMT2Q", PyLong_FromUint32(triton::arch::x86::ID_INS_VPERMT2Q));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPEXTRB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPEXTRD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPEXTRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPEXTRW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPEXTRW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPGATHERDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPGATHERDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPGATHERQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERQD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPGATHERQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPGATHERQQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDBD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDBQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUBD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDUBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUBQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDUDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDUWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDUWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDUWQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDWQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHADDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHADDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHMINPOSUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHMINPOSUW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHSUBBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHSUBDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHSUBWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPHSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPHSUBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPINSRB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPINSRD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPINSRQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPINSRW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPINSRW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPLZCNTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPLZCNTD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPLZCNTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPLZCNTQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMACSDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMACSDQH", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSDQH));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMACSDQL", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSDQL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMACSSDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMACSSDQH", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSDQH));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMACSSDQL", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSDQL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMACSSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMACSSWW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSSWW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMACSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMACSWW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMACSWW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMADCSSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADCSSWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMADCSWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADCSWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMADDUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADDUBSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMADDWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMADDWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMASKMOVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMASKMOVD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMASKMOVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMASKMOVQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMAXSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMAXSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMAXSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMAXSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMAXUB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMAXUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMAXUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMAXUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMAXUW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMINSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMINSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMINSQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMINSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMINUB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMINUD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMINUQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMINUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMINUW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVDB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVMSKB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVMSKB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVQB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVQD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVQW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSDB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSQB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSQD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSQW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXBD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXBQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVSXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVSXWQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVUSDB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSDB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVUSDW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSDW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVUSQB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSQB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVUSQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSQD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVUSQW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVUSQW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVZXBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXBD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVZXBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXBQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVZXBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVZXDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVZXWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMOVZXWQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMOVZXWQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMULDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMULHRSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULHRSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMULHUW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULHUW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMULHW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULHW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMULLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMULLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULLW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPMULUDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPMULUDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPORD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPORD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPORQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPOR", PyLong_FromUint32(triton::arch::x86::ID_INS_VPOR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPPERM", PyLong_FromUint32(triton::arch::x86::ID_INS_VPPERM));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPROTB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPROTD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPROTQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPROTW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPROTW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSADBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSADBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSCATTERDD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERDD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSCATTERDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSCATTERQD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERQD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSCATTERQQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSCATTERQQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHAB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHAQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHAW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHAW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHLB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHLW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHUFB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHUFD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHUFHW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFHW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSHUFLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSHUFLW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSIGNB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSIGNB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSIGND", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSIGND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSIGNW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSIGNW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSLLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSLLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSLLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSLLVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLVD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSLLVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLVQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSLLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSLLW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRAD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRAQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRAVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAVD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRAVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAVQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRAW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRAW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRLD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRLQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRLVD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLVD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRLVQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLVQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSRLW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSRLW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSUBB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSUBD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSUBQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSUBSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSUBSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSUBUSB", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBUSB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSUBUSW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBUSW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPSUBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPSUBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPTESTMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTMD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPTESTMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTMQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPTESTNMD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTNMD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPTESTNMQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTESTNMQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPTEST", PyLong_FromUint32(triton::arch::x86::ID_INS_VPTEST));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPUNPCKHBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPUNPCKHDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPUNPCKHQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHQDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPUNPCKHWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKHWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPUNPCKLBW", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLBW));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPUNPCKLDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPUNPCKLQDQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLQDQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPUNPCKLWD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPUNPCKLWD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPXORD", PyLong_FromUint32(triton::arch::x86::ID_INS_VPXORD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPXORQ", PyLong_FromUint32(triton::arch::x86::ID_INS_VPXORQ));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VPXOR", PyLong_FromUint32(triton::arch::x86::ID_INS_VPXOR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRCP14PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRCP14PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRCP14SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRCP14SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP14SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRCP28PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRCP28PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRCP28SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRCP28SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCP28SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRCPPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCPPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRCPSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRCPSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRNDSCALEPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALEPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRNDSCALEPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALEPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRNDSCALESD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALESD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRNDSCALESS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRNDSCALESS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VROUNDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VROUNDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VROUNDSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VROUNDSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VROUNDSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRSQRT14PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRSQRT14PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRSQRT14SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRSQRT14SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT14SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRSQRT28PD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28PD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRSQRT28PS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28PS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRSQRT28SD", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28SD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRSQRT28SS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRT28SS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRSQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VRSQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VRSQRTSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERDPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERDPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERDPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERDPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERPF0DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0DPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERPF0DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0DPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERPF0QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0QPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERPF0QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF0QPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERPF1DPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1DPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERPF1DPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1DPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERPF1QPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1QPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERPF1QPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERPF1QPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERQPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERQPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSCATTERQPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSCATTERQPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSHUFPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSHUFPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSHUFPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSHUFPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSQRTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSQRTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSQRTSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSQRTSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSQRTSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSTMXCSR", PyLong_FromUint32(triton::arch::x86::ID_INS_VSTMXCSR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSUBPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSUBPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSUBSD", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBSD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VSUBSS", PyLong_FromUint32(triton::arch::x86::ID_INS_VSUBSS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VTESTPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VTESTPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VTESTPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VTESTPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VUNPCKHPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKHPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VUNPCKHPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKHPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VUNPCKLPD", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKLPD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VUNPCKLPS", PyLong_FromUint32(triton::arch::x86::ID_INS_VUNPCKLPS));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VZEROALL", PyLong_FromUint32(triton::arch::x86::ID_INS_VZEROALL));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "VZEROUPPER", PyLong_FromUint32(triton::arch::x86::ID_INS_VZEROUPPER));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "WAIT", PyLong_FromUint32(triton::arch::x86::ID_INS_WAIT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "WBINVD", PyLong_FromUint32(triton::arch::x86::ID_INS_WBINVD));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "WRFSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_WRFSBASE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "WRGSBASE", PyLong_FromUint32(triton::arch::x86::ID_INS_WRGSBASE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "WRMSR", PyLong_FromUint32(triton::arch::x86::ID_INS_WRMSR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XABORT", PyLong_FromUint32(triton::arch::x86::ID_INS_XABORT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XACQUIRE", PyLong_FromUint32(triton::arch::x86::ID_INS_XACQUIRE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XBEGIN", PyLong_FromUint32(triton::arch::x86::ID_INS_XBEGIN));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XCHG", PyLong_FromUint32(triton::arch::x86::ID_INS_XCHG));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "FXCH", PyLong_FromUint32(triton::arch::x86::ID_INS_FXCH));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XCRYPTCBC", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTCBC));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XCRYPTCFB", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTCFB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XCRYPTCTR", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTCTR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XCRYPTECB", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTECB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XCRYPTOFB", PyLong_FromUint32(triton::arch::x86::ID_INS_XCRYPTOFB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XEND", PyLong_FromUint32(triton::arch::x86::ID_INS_XEND));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XGETBV", PyLong_FromUint32(triton::arch::x86::ID_INS_XGETBV));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XLATB", PyLong_FromUint32(triton::arch::x86::ID_INS_XLATB));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XRELEASE", PyLong_FromUint32(triton::arch::x86::ID_INS_XRELEASE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XRSTOR", PyLong_FromUint32(triton::arch::x86::ID_INS_XRSTOR));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XRSTOR64", PyLong_FromUint32(triton::arch::x86::ID_INS_XRSTOR64));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XSAVE", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XSAVE64", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVE64));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XSAVEOPT", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVEOPT));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XSAVEOPT64", PyLong_FromUint32(triton::arch::x86::ID_INS_XSAVEOPT64));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XSETBV", PyLong_FromUint32(triton::arch::x86::ID_INS_XSETBV));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XSHA1", PyLong_FromUint32(triton::arch::x86::ID_INS_XSHA1));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XSHA256", PyLong_FromUint32(triton::arch::x86::ID_INS_XSHA256));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XSTORE", PyLong_FromUint32(triton::arch::x86::ID_INS_XSTORE));
        PyDict_SetItemString(triton::bindings::python::opcodesDict, "XTEST", PyLong_FromUint32(triton::arch::x86::ID_INS_XTEST));
      }

    }; /* python namespace */
  }; /* bindings namespace */
}; /* triton namespace */
