var MIPS = (function(MIPS) {
  function MIPS.disasm(instr) {
    function rs(x)     { return (x&0x3E00000)>>>21; }
    function rt(x)     { return (x&0x1F0000)>>>16; }
    function rd(x)     { return (x&0xF800)>>>11; }
    function imm(x)    { return (x&0xFFFF); }
    function h(x)      { return (x&0x7C0)>>>6; }
    function target(x) { return (x&0x3FFFFFF); }
    function opcode(x) { return (x&0xFC000000)>>>26; }
    function funct(x)  { return (x&0x3F); }
    switch(opcode(instr)) {
      case opARITH:
        switch(funct(instr)) {
          case opADD:     return "add $" + rd(instr) + ", $" + rs(instr) + ", $" + rt(instr);
          case opADDU:    return "addu $" + rd(instr) + ", $" + rs(instr) + ", $" + rt(instr);
          case opAND:     return "and $" + rd(instr) + ", $" + rs(instr) + ", $" + rt(instr);
          case opDIV:     return "div $" + rs(intsr) + ", $" + rt(instr);
          case opDIVU:    return "divu $" + rs(intsr) + ", $" + rt(instr);
          case opJR:      return "jr $" + rs(instr);
          case opMFHI:    return "mfhi $" + rd(instr);
          case opMFLO:    return "mflo $" + rd(instr);
          case opMULT:    return "mult $" + rs(instr) + ", $" + rt(instr);
          case opMULTU:   return "multu $" + rs(instr) + ", $" + rt(instr);
          case opNOOP:
		        if(instr === 0)
			        return "noop";
		        else
			        return "sll $" + rd(instr) + ", $" + rt(instr) + ", " + h(instr);
		        break;
          case opRET:     return "ret $" + rs(instr);
          case opPUTC:    return "putc $" + rs(instr);
          case opSLLV:    return "sslv $" + rd(instr) + ", $" + rt(instr) + ", $" + rs(instr);
          case opSLT:     return "slt $" + rd(instr) + ", $" + rs(instr) + ", $" + rt(instr);
          case opSLTU:    return "sltu $" + rd(instr) + ", $" + rs(instr) + ", $" + rt(instr);
          case opSRA:     return "sra $" + rd(instr) + ", $" + rt(instr) + ", " + h(instr);
          case opSRL:     return "srl $" + rd(instr) + ", $" + rt(instr) + ", " + h(instr);
          case opSRLV:    return "srlv $" + rd(instr) + ", $" + rs(instr) + ", $" + rt(instr);
          case opSUB:     return "sub $" + rd(instr) + ", $" + rs(instr) + ", $" + rt(instr);
          case opSUBU:    return "subu $" + rd(instr) + ", $" + rs(instr) + ", $" + rt(instr);
          case opSYSCALL: return "syscall";
          case opXOR:     return "xor $" + rd(instr) + ", $" + rs(instr) + ", $" + rt(instr);
          default:        return "???";
        }
        break;
      case opBRANCH:
        switch(rt(instr)) {
          case opBGEZ:   return "bgez $" + rs(instr) + ", 0x" + imm(instr).toString(16);
          case opBGEZAL: return "bgezal $" + rs(instr) + ", 0x" + imm(instr).toString(16);
          case opBLTZ:   return "bltz $" + rs(instr) + ", 0x" + imm(instr).toString(16);
          case opBLTZAL: return "bltzal $" + rs(instr) + ", 0x" + imm(instr).toString(16);
          default:       return "???";
        }
        break;
      case opADDI:   return "addi $" + rd(instr) + ", $" + rs(instr) + ", 0x" + imm(instr).toString(16);
      case opANDI:   return "andi $" + rd(instr) + ", $" + rs(instr) + ", 0x" + imm(instr).toString(16);
      case opBEQ:    return "beq $" + rs(instr) + ", $" + rt(instr) + ", 0x" + imm(instr).toString(16);
      case opBGTZ:   return "bgtz $" + rs(instr) + ", 0x" + imm(instr).toString(16);
      case opBLEZ:   return "blez $" + rs(instr) + ", 0x" + imm(instr).toString(16);
      case opBNE:    return "bne $" + rs(instr) + ", $" + rt(instr) + ", 0x" + imm(instr).toString(16);
      case opCALL:   return "call 0x" + target(instr).toString(16);
      case opJ:      return "j 0x" + target(instr).toString(16);
      case opJAL:    return "jal 0x" + target(instr).toString(16);
      case opLB:     return "lb $" + rt(instr) + ", 0x" + imm(instr).toString(16) + "($" + rs(instr) + ")";
      case opLUI:    return "lui $" + rt(instr) + ", 0x" + imm(instr).toString(16);
      case opLW:     return "lw $" + rt(instr) + ", 0x" + imm(instr).toString(16) + "($" + rs(instr) + ")";
      case opORI:    return "ori $" + rd(instr) + ", $" + rs(instr) + ", 0x" + imm(instr).toString(16);
      case opSB:     return "sb $" + rt(instr) + ", 0x" + imm(instr).toString(16) + "($" + rs(instr) + ")";
      case opSLTI:   return "slti $" + rd(instr) + ", $" + rs(instr) + ", 0x" + imm(instr).toString(16);
      case opSLTIU:  return "sltiu $" + rd(instr) + ", $" + rs(instr) + ", 0x" + imm(instr).toString(16);
      case opSW:     return "sw $" + rt(instr) + ", 0x" + imm(instr).toString(16) + "($" + rs(instr) + ")";
      case opXORI:   return "xori $" + rd(instr) + ", $" + rs(instr) + ", 0x" + imm(instr).toString(16);
      default:       return "???";
    }
  }
}(MIPS || {}));
