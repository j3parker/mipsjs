function MIPS(ramsize) {
  var MIPS = new Object();
  var vm;

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

  MIPS.assemble = function(asm) {
    function formatstrlen(x) { for(var i = 0; i < x.length; x++) { var ans = 0; if(i==='\\') continue; ans++; } return ans; }
    function formatstr(x) {
      var ans = '';
      var esc = false;
      for(var i = 0; i < x.length; i++) {
        if(esc) {
          switch(x[i]) {
            case 'n': ans += '\n'; esc = false; break;
            default: throw { msg: "unknown escape sequence \\" + x[i] };
          }
        } else {
          if(x[i] == '\\') { esc = true; }
          else { ans += x[i]; }
        }
      }
      if(esc) throw { msg: "unterminated escape sequence in string" };
      return ans;
    }
    function zeropadL(x, n) {
      n -= x.length;
      while(n-- > 0) { x = '0' + x; }
      return x;
    }
    function zeropadR(x,n) {
      n -= x.length;
      while(n-- > 0) { x += '0'; }
      return x;
    }
    function strtowords(x) {
      var i=0, j = 0;
      var ans = new Array();
      var word = '';
      for(i = 0; i < x.length; i+=1) {
        word += zeropadL(x.charCodeAt(i).toString(16), 2);
        if(++j == 4) {
          ans.push(+('0x' + word));
          j = 0;
          word = '';
        }
      }
      ans.push(+('0x' + zeropadR(word, 8)));
      return ans;
    }

    var s = asm.replace(/:/g,":\n").split("\n").map(
      function(x) { return x.replace(/ *; .*$/, ""); }
    ).filter(
      function(x) {
        return (null === /^[ \t]*$/.exec(x));
      }
    );

    var type0R = 0
        type1R = 1,
        type2R = 2,
        type3R = 3,
        type1I = 4,
        type2I = 5,
        typeB = 6,
        typeP = 7,
        typeL = 8,
        typeW = 9,
        typeS = 10;
    var rxs =
      [
        // 0R
        /^[ \t]*([a-z]+)$/,
        // 1R
        /^[ \t]*([a-z]+)[ \t]* \$([0-9]+)$/,
        // 2R
        /^[ \t]*([a-z]+)[ \t]* \$([0-9]+)[ \t]*,[ \t]*\$([0-9]+)$/,
        // 3R
        /^[ \t]*([a-z]+)[ \t]* \$([0-9]+)[ \t]*,[ \t]*\$([0-9]+)[ \t]*,[ \t]*\$([0-9]+)$/,
        // 1I
        /^[ \t]*([a-z]+)[ \t]* (-?[_a-zA-Z0-9]+)$/,
        // 2I
        /^[ \t]*([a-z]+)[ \t]* \$([0-9]+)[ \t]*[ \t]*,[ \t]*(-?[_a-zA-Z0-9]+)$/,
        // Branch
        /^[ \t]*([a-z]+)[ \t]* \$([0-9]+)[ \t]*,[ \t]*\$([0-9]+)[ \t]*,[ \t]*(-?[_a-zA-Z0-9]+)$/,
        // Load/store
        /^[ \t]*([a-z]+)[ \t]* \$([0-9]+)[ \t]*,[ \t]*(-?[_a-zA-Z0-9]+)[ \t]*\([ \t]*\$([0-9]+)[ \t]*\)$/,
        // Label
        /^[ \t]*([a-zA-Z]+[_a-zA-Z0-9]*):$/,
        // .word macro
        /^[ \t]*(\.word)[ \t]* (-?[_a-zA-Z0-9]+)[ \t]*$/,
        // .string macro
        /^[ \t]*(\.string)[ \t]* "([^"]*)"$/,
      ];

    var asm_matches = s.map(function(x) { return rxs.map(function(y) { return y.exec(x); }); }).map(
      function(v) {
        for(var i=0; i<v.length; i++) {
          if(v[i] !== null) {
            var foo = [];
            foo.push(i);
            foo.push.apply(foo, v[i].slice(1, v.length-1));
            return foo;
          }
        }
        return null; });

    var labels = new Array();
    var pc = 0;
    for(var idx=0;idx<asm_matches.length;idx++) {
      line = asm_matches[idx];
      if(line === null) {
        throw "Malformed instruction or garbage in input at instruction " + idx + ".";
      }

      if(line[0] === typeL) {
        if(labels[line[1]] !== undefined) {
          throw "Label '" + line[1] + "' twice defined.";
        }
        labels[line[1]] = pc;
      } else if(line[0] === typeS) {
        pc += 4*Math.ceil((1 + formatstrlen(line[2]))/4);
      } else {
        pc += 4;
      }
    }
    /*for(idx in labels) {
      console.log(idx + ":" + labels[idx]);
    }*/

    function assert_type(i, t) {
      if(i[0] !== t) {
        throw "Malformed instruction. Expected type " + t + ", but got " + i[0] + ".";
      }
    }

    function rs(x) { return (x<<21)&0x03E00000; }
    function rt(x) { return (x<<16)&0x001F0000; }
    function rd(x) { return (x<<11)&0x0000F800; }

    function asm_r(fun) {
      switch(arguments.length) {
        case 1: return ((fun)&0x3F);
        case 2: return ((fun)&0x3F) | rd(arguments[1]);
        case 3: return ((fun)&0x3F) | rd(arguments[1]) | rs(arguments[2]);
        case 4: return ((fun)&0x3F) | rd(arguments[1]) | rs(arguments[2]) | rt(arguments[3]);
      }
    }

    function asm_rs(fun, shamt) {
      switch(arguments.length) {
        case 2: return ((shamt<<6)&0x7C0) | ((fun)&0x3F);
        case 3: return ((shamt<<6)&0x7C0) | ((fun)&0x3F) | rd(arguments[2]);
        case 4: return ((shamt<<6)&0x7C0) | ((fun)&0x3F) | rd(arguments[2]) | rs(arguments[3]);
        case 5: return ((shamt<<6)&0x7C0) | ((fun)&0x3F) | rd(arguments[2]) | rs(arguments[3]) | rt(arguments[4]);
      }
    }

    function asm_i(op, im) {
      switch(arguments.length) {
        case 3: return ((op<<26)&0xFC000000) | (im&0x0000FFFF) | rs(arguments[2]);
        case 4: return ((op<<26)&0xFC000000) | (im&0x0000FFFF) | rs(arguments[2]) | rt(arguments[3]);
      }
    }

    function asm_j(op, im) {
      return ((op<<26)&0xFC000000) | (im&0x03FFFFFF);
    }

    function dai(im) {
       if(!isNaN(im)) {
         return im;
       } else {
         if(labels[im] === undefined) {
           throw "Label undefined: " + im + ".";
         }
         return labels[im];
       }
    }

    function dri(im, pc) {
      if(!isNaN(im)) {
        return im;
      } else {
        return (dai(im) - pc)/4 - 1;
      }
    }

    var output = new Array();
    cpc = 0;
    for(var idx=0;idx<asm_matches.length;idx++) {
      inst = asm_matches[idx];
      if(inst[0] === typeL) {
        continue;
      }

      switch(inst[1]) {

        // R type:
        case "add":
          assert_type(inst, type3R);
          output.push(asm_r(opADD, +inst[2], +inst[3], +inst[4]));
          break;
        case "addu":
          assert_type(inst, type3R);
          output.push(asm_r(opADDU, +inst[2], +inst[3], +inst[4]));
          break;
        case "and":
          assert_type(inst, type3R);
          output.push(asm_r(opAND, +inst[2], +inst[3], +inst[4]));
          break;
        case "break":
          assert_type(inst, type0R);
          output.push(asm_r(opBREAK));
          break;
        case "div":
          assert_type(inst, type2R);
          output.push(asm_r(opDIV, 0, +inst[2], +inst[3]));
          break;
        case "divu":
          assert_type(inst, type2R);
          output.push(asm_r(opDIVU, 0, +inst[2], +inst[3]));
          break;
        case "jalr":
          assert_type(inst, type2R);
          output.push(asm_r(opJALR, 0, +inst[2], +inst[3]));
          break;
        case "jr":
          assert_type(inst, type1R);
          output.push(asm_r(opJR, 0, +inst[2]));
          break;
        case "mfhi":
          assert_type(inst, type1R);
          output.push(asm_r(opMFHI, +inst[2]));
          break;
        case "mflo":
          assert_type(inst, type1R);
          output.push(asm_r(opMFLO, +inst[2]));
          break;
        case "mthi":
          assert_type(inst, type1R);
          output.push(asm_r(opMTHI, 0, +inst[2]));
          break;
        case "mtlo":
          assert_type(inst, type1R);
          output.push(asm_r(opMTLO, 0, +inst[2]));
          break;
        case "mult":
          assert_type(inst, type2R);
          output.push(asm_r(opMULT, 0, +inst[2], +inst[3]));
          break;
        case "multu":
          assert_type(inst, type2R);
          output.push(asm_r(opMULTU, 0, +inst[2], +inst[3]));
          break;
        case "noop":
          assert_type(inst, type0R);
          output.push(asm_r(opNOOP));
          break;
        case "nor":
          assert_type(inst, type3R);
          output.push(asm_r(opNOR, +inst[2], +inst[3], +inst[4]));
          break;
        case "or":
          assert_type(inst, type3R);
          output.push(asm_r(opOR, +inst[2], +inst[3], +inst[4]));
          break;
        case "putc":
          assert_type(inst, type1R);
          output.push(asm_r(opPUTC, 0, +inst[2]));
          break;
        case "ret":
          assert_type(inst, type1R);
          output.push(asm_r(opRET, 0, +inst[2]));
          break;
        case "sll":
          assert_type(inst, typeB);
          output.push(asm_rs(opSLL, +inst[4], +inst[2], 0, +inst[3]));
          break;
        case "sllv":
          assert_type(inst, type3R);
          output.push(asm_r(opSLLV, +inst[2], +inst[4], +inst[3]));
          break;
        case "slt":
          assert_type(inst, type3R);
          output.push(asm_r(opSLT, +inst[2], +inst[3], +inst[4]));
          break;
        case "sltu":
          assert_type(inst, type3R);
          output.push(asm_r(opSLTU, +inst[2], +inst[3], +inst[4]));
          break;
        case "sra":
          assert_type(inst, typeB);
          output.push(asm_rs(opSRA, +inst[4], +inst[2], 0, +inst[3]));
          break;
        case "srav":
          assert_type(inst, type3R);
          output.push(asm_r(opSRAV, +inst[2], +inst[4], +inst[3]));
          break;
        case "srl":
          assert_type(inst, typeB);
          output.push(asm_rs(opSRL, +inst[4], +inst[2], 0, +inst[3]));
          break;
        case "srlv":
          assert_type(inst, type3R);
          output.push(asm_r(opSRLV, +inst[2], +inst[4], +inst[3]));
          break;
        case "sub":
          assert_type(inst, type3R);
          output.push(asm_r(opSUB, +inst[2], +inst[3], +inst[4]));
          break;
        case "subu":
          assert_type(inst, type3R);
          output.push(asm_r(opSUBU, +inst[2], +inst[3], +inst[4]));
          break;
        case "syscall":
          assert_type(inst, type0R);
          output.push(asm_r(opSYSCALL));
          break;
        case "xor":
          assert_type(inst, type3R);
          output.push(asm_r(opXOR, +inst[2], +inst[3], +inst[4]));
          break;

        // I type:
        case "addi":
          assert_type(inst, typeB);
          output.push(asm_i(opADDI, dai(inst[4]), +inst[3], +inst[2]));
          break;
        case "addiu":
          assert_type(inst, typeB);
          output.push(asm_i(opADDIU, dai(inst[4]), +inst[3], +inst[2]));
          break;
        case "andi":
          assert_type(inst, typeB);
          output.push(asm_i(opANDI, dai(inst[4]), +inst[3], +inst[2]));
          break;
        case "beq":
          assert_type(inst, typeB);
          output.push(asm_i(opBEQ, dri(inst[4], cpc), +inst[2], +inst[3]));
          break;
        case "bgez":
          assert_type(inst, type2I);
          output.push(asm_i(opBGEZ, dri(inst[3], cpc), +inst[2], opBGEZ));
          break;
        case "bgezal":
          assert_type(inst, type2I);
          output.push(asm_i(opBGEZAL, dri(inst[3], cpc), +inst[2], opBGEZ));
          break;
        case "bgtz":
          assert_type(inst, type2I);
          output.push(asm_i(opBGTZ, dri(inst[3], cpc), +inst[2]));
          break;
        case "blez":
          assert_type(inst, type2I);
          output.push(asm_i(opBLEZ, dri(inst[3], cpc), +inst[2]));
          break;
        case "bltz":
          assert_type(inst, type2I);
          output.push(asm_i(opBLTZ, dri(inst[3], cpc), +inst[2]));
          break;
        case "bltzal":
          assert_type(inst, type2I);
          output.push(asm_i(opBLTZAL, dri(inst[3], cpc), +inst[2]));
          break;
        case "bne":
          assert_type(inst, typeB);
          output.push(asm_i(opBNE, dri(inst[4], cpc), +inst[2], +inst[3]));
          break;
        case "lb":
          assert_type(inst, typeP);
          output.push(asm_i(opLB, dai(inst[3]), +inst[4], +inst[2]));
          break;
        case "lbu":
          assert_type(inst, typeP);
          output.push(asm_i(opLBU, dai(inst[3]), +inst[4], +inst[2]));
          break;
        case "lh":
          assert_type(inst, typeP);
          output.push(asm_i(opLH, dai(inst[3]), +inst[4], +inst[2]));
          break;
        case "lhu":
          assert_type(inst, typeP);
          output.push(asm_i(opLHU, dai(inst[3]), +inst[4], +inst[2]));
          break;
        case "lui":
          assert_type(inst, type2I);
          output.push(asm_i(opLUI, dai(inst[3]), 0, +inst[2]));
          break;
        case "lw":
          assert_type(inst, typeP);
          output.push(asm_i(opLW, dai(inst[3]), +inst[4], +inst[2]));
          break;
        case "lwc1":
          assert_type(inst, typeP);
          output.push(asm_i(opLWC1, dai(inst[3]), +inst[4], +inst[2]));
          break;
        case "ori":
          assert_type(inst, typeB);
          output.push(asm_i(opORI, dai(inst[4]), +inst[3], +inst[2]));
          break;
        case "sb":
          assert_type(inst, typeP);
          output.push(asm_i(opSB, dai(inst[3]), +inst[4], +inst[2]));
          break;
        case "slti":
          assert_type(inst, typeB);
          output.push(asm_i(opSLTI, dai(inst[4]), +inst[3], +inst[2]));
          break;
        case "sltiu":
          assert_type(inst, typeB);
          output.push(asm_i(opSLTIU, dai(inst[4]), +inst[3], +inst[2]));
          break;
        case "sh":
          assert_type(inst, typeP);
          output.push(asm_i(opSH, dai(inst[3]), +inst[4], +inst[2]));
          break;
        case "sw":
          assert_type(inst, typeP);
          output.push(asm_i(opSW, dai(inst[3]), +inst[4], +inst[2]));
          break;
        case "swc1":
          assert_type(inst, typeP);
          output.push(asm_i(opSWC1, dai(inst[3]), +inst[4], +inst[2]));
          break;
        case "xori":
          assert_type(inst, typeB);
          output.push(asm_i(opXORI, dai(inst[4]), +inst[3], +inst[2]));
          break;

        // J type:
        case "call":
          assert_type(inst, type1I);
          output.push(asm_j(opCALL, dai(inst[2])));
          break;
        case "j":
          assert_type(inst, type1I);
          output.push(asm_j(opJ, dai(inst[2])));
          break;
        case "jal":
          assert_type(inst, type1I);
          output.push(asm_j(opJAL, dai(inst[2])));
          break;

        // W type
        case ".word":
          assert_type(inst, typeW);
          output.push(+inst[2]);
          break;
        case ".string":
          assert_type(inst, typeS);
          var ans = strtowords(formatstr(inst[2]));
          // why did concat not work? TODO
          for(var iii = 0; iii < ans.length;iii++) output.push(ans[iii]);
          break;
        default:
          throw "Unknown opcode: " + inst[1] + ".";
      }

      cpc += 4;
    }
    return output;
  }

  var RAM_CODE    = 0x01,
      RAM_STACK   = 0x02,
      RAM_HEAP    = 0x04,
      RAM_UNALLOC = 0x08,
      RAM_UNINIT  = 0x10,

      VM_DEVICE_START     = 0xFFFF0000,
      VM_CONSOLE_CHAR_OUT = 0xFFFF0000;

  MIPS.program_ram = function(loc, op) {
    vm.RAM[loc] = op;
    vm.RAMState[loc] = RAM_CODE;
  }

  MIPS.run = function(n) {
    var dirty = { ram: new Array(), reg: [] },
        oldpc = vm.pc,
        data,
        loc,
        write_mem,
        instr, offset,
        i, rsx, rtx, rdx, op, immx;
    function tc32_to_untyped(tc32) { return ((tc32 + 0x8000000) & 0xFFFFFFF) - 0x8000000; }
    function tc16_to_untyped(tc16) { return ((tc16 + 0x8000) & 0xFFFF) - 0x8000; }
    //function rs(x)     { return (x&0x3E00000)>>>21; }
    //function rt(x)     { return (x&0x1F0000)>>>16; }
    //function rd(x)     { return (x&0xF800)>>>11; }
    //function imm(x)    { return tc16_to_untyped(x&0xFFFF); }
    function h(x)      { return (x&0x7C0)>>>6; }
    function target(x) { return (x&0x3FFFFFF); }
    //function opcode(x) { return (x&0xFC000000)>>>26; }
    function funct(x)  { return (x&0x3F); }
    for(i = 0; i < n; i += 1) {
      if(vm.config.faultOnPCEscape && !(vm.RAMState[vm.pc] & RAM_CODE)) {
        throw {
                PC: vm.pc,
                message: "PC at non-code location.",
                fatal: true
        };
      }
      if(vm.config.faultOnUnallocR && (vm.RAMState[vm.pc] & RAM_UNALLOC)) {
        throw {
                PC: vm.pc,
                message: "Attempted to load instruction from unallocated memory.",
                fatal: true
        };
      }
      if(vm.pc >= vm.RAM.length) {
        throw {
                PC: vm.pc,
                message: "Attmpted to load code from non-existant memory at location " + loc.toString(16) + ".",
                fatal: true
        };
      }
      write_mem = false;

      instr = vm.RAM[vm.pc];
      rsx = (instr&0x3E00000)>>>21;
      rtx = (instr&0x1F0000)>>>16;
      rdx = (instr&0xF800)>>>11;
      op = (instr&0xFC000000)>>>26;
      immx = tc16_to_untyped(instr&0xFFFF);
      vm.pc += 1;
      switch(op) {
        case opARITH:
          switch(funct(instr)) {
            case opADD:
            case opADDU: vm.regs[rdx] = vm.regs[rsx] + vm.regs[rtx]; break;
            case opAND: vm.regs[rdx] = vm.regs[rsx] & vm.regs[rtx]; break;
            case opDIV:
            case opDIVU:
              vm.lo = Math.floor(vm.regs[rsx] / vm.regs[rtx]) & 0xFFFFFFFF;
              vm.hi = Math.floor(vm.regs[rsx] % vm.regs[rtx]) & 0xFFFFFFFF;
              break;
            case opJR: vm.pc = vm.regs[rsx] - 1; break;
            case opMFHI: vm.regs[rdx] = vm.hi; break;
            case opMFLO: vm.regs[rdx] = vm.lo; break;
            case opMULT:
              /* more disgusting */
              vm.hi = Math.floor((tc32_to_untyped(vm.regs[rsx]) * tc32_to_untyped(vm.regs[rtx]))
                        / 0x100000000) & 0xFFFFFFFF;
              vm.lo = (tc32_to_untyped(vm.regs[rsx]) * tc32_to_untyped(vm.regs[rtx])) & 0xFFFFFFFF;
              break;
            case opMULTU:
              /* disgusting */
              vm.hi = Math.floor((vm.regs[rsx] * vm.regs[rtx]) / 0x100000000) & 0xFFFFFFFF;
              vm.lo = (vm.regs[rsx] * vm.regs[rtx]) & 0xFFFFFFFF;
              break;
            case opOR: vm.regs[rdx] = vm.regs[rsx] | vm.regs[rtx]; break;
            case opPUTC:
              loc = VM_CONSOLE_CHAR_OUT;
              data = vm.regs[rsx];
              write_mem = true;
              break;
            case opRET:
              vm.pc = vm.regs[regLR] - 1;
              var oldfp = vm.regs[regFP];
              var retval = vm.regs[rsx];
              for(var i = 6; i < 32; i++) {
                if(vm.RAMState[oldfp - i + 5] !== RAM_STACK) {
                  throw {
                    message: "Bad stack pointer on ret.",
                    fatal: true
                  };
                }
                vm.regs[32 - i + 5] = vm.RAM[oldfp - i + 5];
                vm.RAMState[oldfp - i + 5] = RAM_UNALLOC;
                dirty.ram.push(oldfp - i + 5);
              }
              vm.regs[1] = retval;
              break;
            case opSLL: vm.regs[rdx] = vm.regs[rtx] << h(instr); break;
            case opSLLV: vm.regs[rdx] = vm.regs[rtx] << vm.regs[rsx]; break;
            case opSLT:
              vm.regs[rdx] =
                tc32_to_untyped(vm.regs[rsx]) < tc32_to_untyped(vm.regs[rtx]);
              break;
            case opSLTU: vm.regs[rdx] = vm.regs[rsx] < vm.regs[rtx]; break;
            case opSRA: vm.regs[rdx] = vm.regs[rtx] >> h(instr); break;
            case opSRL: vm.regs[rdx] = vm.regs[rtx] >>> h(instr); break;
            case opSRLV: vm.regs[rdx] = vm.regs[rtx] >>> vm.regs[rsx]; break;
            case opSUB:
              vm.regs[rdx] =
                tc32_to_untyped(vm.regs[rsx]) - tc32_to_untyped(vm.regs[rtx]);
              break;
            case opSUBU: vm.regs[rdx] = vm.regs[rsx] - vm.regs[rtx]; break;
            case opSYSCALL:
              /* assume exception handler at 0x80 */
              vm.pc = 0x80/4 - 1;
              break;
            case opXOR: vm.regs[rdx] = vm.regs[rsx] ^ vm.regs[rtx]; break;
            default:
              throw {
                PC: vm.pc,
                op: instr,
                message: "Invalid function code for arithmetic operation.",
                fatal: true
              };
          }
          break;
        case opBRANCH:
          switch(rtx) {
            case opBGEZ: if(tc32_to_untyped(vm.regs[rsx]) >= 0) { vm.pc += immx; } break;
            case opBGEZAL: if(tc32_to_untyped(vm.regs[rsx]) >= 0) { vm.regs[31] = vm.pc; vm.pc += immx; } break;
            case opBLTZ: if(tc32_to_untyped(vm.regs[rsx]) < 0) { vm.pc += immx; } break;
            case opBLTZAL: if(tc32_to_untyped(vm.regs[rsx]) < 0) { vm.regs[31] = vm.pc; vm.pc += immx; } break;
            default: throw {
                       PC: vm.pc,
                       message: "Invalid branch-like opcode.",
                       fatal: true
                     };
          }
          break;
        case opADDI:
          /* eww */
          vm.regs[rtx] =
            tc32_to_untyped(vm.regs[rsx]) + tc32_to_untyped(immx);
          break;
        case opADDIU: vm.regs[rtx] = vm.regs[rsx] + immx; break;
        case opANDI: vm.regs[rtx] = vm.regs[rsx] & immx; break;
        case opCALL:
          var newLR = vm.pc + 1;
          vm.pc = (vm.pc & 0xF0000000) | target(instr)/4;
          for(var i = 6; i < 32; i++) {
            var loc = vm.regs[regSP] + i - 6;
            if(vm.RAMState[loc] !== RAM_UNALLOC) {
              throw {
                message: "On call, invalid stack pointer.",
                fatal: true
              };
            }
            vm.RAM[loc] = vm.regs[i];
            vm.RAMState[loc] = RAM_STACK;
            dirty.ram.push(loc);
          }
          vm.regs[regSP] += 26;
          vm.regs[regFP] = vm.regs[regSP];
          vm.regs[regLR] = newLR;
          break;
        case opBEQ: if(vm.regs[rsx] === vm.regs[rtx]) { vm.pc += immx; } break;
        case opBGTZ: if(tc32_to_untyped(vm.regs[rsx]) > 0) { vm.pc += immx; } break;
        case opBLEZ: if(tc32_to_untyped(vm.regs[rsx]) < 0) { vm.pc += immx; } break;
        case opBNE: if(vm.regs[rsx] !== vm.regs[rtx]) { vm.pc += immx; } break;
        case opJ: vm.pc = (vm.pc & 0xF0000000) | target(instr)/4; break;
        case opJAL:
          vm.regs[regLR] = vm.pc + 1;
          vm.pc = (vm.pc & 0xF0000000) | target(instr)/4;
          break;
        case opLB:
          loc = vm.regs[rsx] + immx;
          var wloc = Math.floor(loc/4);
          vm.regs[rtx] = (vm.RAM[wloc] & (0xFF<<(8*(3-loc%4))))>>((3-loc%4)*8);
          // TODO: err, this is possibly backwards, also check out .string
          break;
        case opLUI: vm.regs[rtx] = immx << 16; break;
        case opLW:
          loc = vm.regs[rsx] + immx;
          if(loc%4 !== 0) {
            throw {
              PC: vm.pc,
              message: "Unaligned word read.",
              fatal: true
            };
          }
          if(loc/4 >= vm.RAM.length) {
            throw {
              PC: vm.pc,
              message: "Attmpted to read from non-existant memory at location " + loc.toString(16) + ".",
              fatal: true
            };
          }
          vm.regs[rtx] = vm.RAM[loc/4];
          break;
        case opORI:
        case opSB:
        case opSLTI:
        case opSLTIU:
        case opSW:
          offset = immx;
          if(offset%4 !== 0) {
            throw {
              PC: vm.pc,
              message: "Unaligned word store.",
              fatal: true
            };
          }
          loc = vm.regs[rsx] + offset/4;
          data = vm.regs[rtx];
          write_mem = true;
          break;
        case opXORI: break;
        default:
          throw {
            PC: vm.pc,
            message: "Invalid opcode: " + opcode(instr).toString(16) + ".",
            fatal: true
          };
      }
      dirty.ram.push(oldpc);
      dirty.ram.push(vm.pc);
      if(write_mem) {
        if(loc >= VM_DEVICE_START) {
          handle_io(loc, data);
        } else if(loc >= vm.RAM.length) {
          throw {
            PC: vm.pc,
            message: "Attmpted to write to non-existant memory at location " + loc.toString(16) + ".",
            fatal: true
          };
        } else if(vm.RAMState[loc] & RAM_UNALLOC && vm.config.faultOnUnallocW) {
          throw {
            PC: vm.pc,
            message: "Attempted write to unallocated memory",
            fatal: true
          };
        } else if(vm.RAMState[loc] & RAM_CODE && vm.config.faultOnCodeW) {
          throw {
            PC: vm.pc,
            message: "Attempted write to protected code location.",
            fatal: true
          };
        } else {
          if((vm.RAMState[loc] & RAM_UNALLOC) && vm.config.heapAllocOnUnallocW) { vm.RAMState[loc] = RAM_HEAP; }
          vm.RAM[loc] = data;
          dirty.ram.push(loc);
        }
      }
      vm.regs[0] = 0;
      dirty.reg = [rsx, rtx, rdx];
    }
    return dirty;
  }

  function handle_io(loc, data) {
    switch(loc) {
      case VM_CONSOLE_CHAR_OUT:
        if(typeof vm.console === "undefined") {
          throw {
            PC: vm.pc,
            message: "No console attached.",
            fatal: true,
          };
        }
        vm.console.putc(String.fromCharCode(data));
        break;
      case VM_CONSOLE_CHAR_IN :
        if(typeof vm.console === "undefined") {
          throw {
            PC: vm.pc,
            message: "No console attached.",
            fatal: true,
          };
        }
        vm.console.getc();
        break;
      default:
        throw {
          PC: vm.pc,
          message: "Attempted write to incorrect device register.",
          fatal: true,
        };
    }
  }

  var i = 0;
  vm = { regs: new Uint32Array(32),
         pc: 0,
         hi: 0,
         lo: 0,
         RAM: new Uint32Array(ramsize),
         RAMState: new Uint8Array(ramsize),
         config: {
           faultOnCodeW:        true,
           faultOnCodeR:        true,
           faultOnUnallocR:     true,
           faultOnUnallocW:     false,
           faultOnUninitR:      true,
           faultOnPCEscape:     true,
           heapAllocOnUnallocW: true
         }
       };
  for(i = 0; i < ramsize; i += 1) {
    vm.RAMState[i] = RAM_UNALLOC;
  }
  return MIPS;
}
