var MIPS = (function(MIPS) {
  function asmtomips(asm) {
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
}(MIPS || {}));
