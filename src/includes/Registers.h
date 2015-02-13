#ifndef  __REGISTERS_H__
#define  __REGISTERS_H__

enum regID_t
{
  /* Register ID used in the Taint and Symbolic Engines */
  ID_RAX,
  ID_RBX,
  ID_RCX,
  ID_RDX,
  ID_RDI,
  ID_RSI,
  ID_RBP,
  ID_RSP,
  ID_R8 ,
  ID_R9 ,
  ID_R10,
  ID_R11,
  ID_R12,
  ID_R13,
  ID_R14,
  ID_R15,

  /* Flags ID used in the Taint and Symbolic Engines */
  ID_CF,
  ID_PF,
  ID_AF,
  ID_ZF,
  ID_SF,
  ID_TF,
  ID_IF,
  ID_DF,
  ID_OF,
};

#endif //__REGISTERS_H__
