var MIPS = (function(MIPS) {
  "use strict";
  var RAM_CODE    = 0x01,
      RAM_STACK   = 0x02,
      RAM_HEAP    = 0x04,
      RAM_UNALLOC = 0x08,
      RAM_UNINIT  = 0x10,

      VM_DEVICE_START     = 0xFFFF0000,
      VM_CONSOLE_CHAR_OUT = 0xFFFF0000;

  function MIPS.make_vm(ramsize) {
    var i = 0,
        vm = {
          regs: new Uint32Array(32),
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
    return vm;
  }

  function MIPS.program_ram(vm, loc, op) {
    vm.RAM[loc] = op;
    vm.RAMState[loc] = RAM_CODE;
  }

  function MIPS.run(vm, n) {
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
}(MIPS || {}));
