var MIPS = (function(MIPS) {
  var opARITH  = 0x00,
      opBRANCH = 0x01,
      opADDI   = 0x08,
      opADDIU  = 0x09,
      opANDI   = 0x0C,
      opBEQ    = 0x04,
      opBGTZ   = 0x07,
      opBLEZ   = 0x06,
      opBNE    = 0x05,
      opJ      = 0x02,
      opJAL    = 0x03,
      opLB     = 0x20,
      opLUI    = 0x0F,
      opLW     = 0x23,
      opOR     = 0x25,
      opORI    = 0x0D,
      opSB     = 0x28,
      opSLTI   = 0x0A,
      opSLTIU  = 0x0B,
      opSW     = 0x2B,
      opXORI   = 0x0E;
  var opBGEZ   = 0x01
      opBGEZAL = 0x11,
      opBLTZ   = 0x00,
      opBLTZAL = 0x10;
  var opADD     = 0x20,
      opADDU    = 0x21,
      opAND     = 0x24,
      opDIV     = 0x1A,
      opDIVU    = 0x1B,
      opJR      = 0x08,
      opMFHI    = 0x10,
      opMFLO    = 0x12,
      opMULT    = 0x18,
      opMULTU   = 0x19,
      opNOOP    = 0x00,
      opSLL     = 0x00,
      opSLLV    = 0x04,
      opSLT     = 0x2A,
      opSLTU    = 0x2B,
      opSRA     = 0x03,
      opSRL     = 0x02,
      opSRLV    = 0x06,
      opSUB     = 0x22,
      opSUBU    = 0x13,
      opSYSCALL = 0x0C,
      opXOR     = 0x26;
  var opPUTC    = 0x01, // custom opcodes
      opRET     = 0x05,
      opCALL    = 0x12;
  var regSP = 29,
      regFP = 30,
      regLR = 31;
}(MIPS || {}));

// TODO: this is bad, do it better.
$.getScript('lib/mips/vm.js');
$.getScript('lib/mips/asm.js');
$.getScript('lib/mips/disasm.js');
