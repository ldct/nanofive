import TinyFive.Machine
import TinyFive.SieveMemory
import LucyMemory
import GrumpyBinary.Program
import GrumpyBinary.Attr

/-! Instruction fetch and machine arithmetic for the recompiled grumpygordon image.

`instrAt` is the decoded instruction at every code address below `codeEnd = 1236`; `fetch`
checks it against the loaded words by `decide`. The rest are rewrite rules that evaluate an
instruction on registers holding natural numbers (`bv n`) or integers (`iv z`), each with the
range conditions under which the machine operation agrees with the arithmetic one. -/
namespace TinyFive.GrumpyBinary
open SieveMemory

/-- The loaded image, code and initial heap cursor. -/
def image : Array (BitVec 8) := (load 64 prog 1248 []).mem

/-- The end of the code; the 8-byte heap cursor is at 1240. -/
abbrev codeEnd : Nat := 1236

def instrAt : Nat → Instr
  | 0 => .lui 2 0x00400#20
  | 4 => .jal 1 0x000068#21
  | 8 => .opImm .add 17 0 0x001#12
  | 12 => .ecall
  | 16 => .opImm .add 10 0 0x00a#12
  | 20 => .opImm .add 17 0 0x00b#12
  | 24 => .ecall
  | 28 => .opImm .add 17 0 0x00a#12
  | 32 => .ecall
  | 36 => .op .add 12 10 12
  | 40 => .opImm .add 15 10 0x000#12
  | 44 => .branch .bne 15 12 0x0008#13
  | 48 => .jalr 0 1 0x000#12
  | 52 => .opImm .add 15 15 0x001#12
  | 56 => .store .byte 11 15 0xfff#12
  | 60 => .jal 0 0x1ffff0#21
  | 64 => .opImm .add 15 10 0x001#12
  | 68 => .opImm .srl 15 15 0x001#12
  | 72 => .opImm .add 14 10 0x000#12
  | 76 => .branch .bltu 15 14 0x000c#13
  | 80 => .opImmWord .add 10 14 0x000#12
  | 84 => .jalr 0 1 0x000#12
  | 88 => .op .divu 13 10 15
  | 92 => .opImm .add 14 15 0x000#12
  | 96 => .op .add 13 13 15
  | 100 => .opImm .srl 15 13 0x001#12
  | 104 => .jal 0 0x1fffe4#21
  | 108 => .opImm .add 15 0 0x001#12
  | 112 => .branch .bge 15 10 0x0428#13
  | 116 => .opImm .add 2 2 0xf90#12
  | 120 => .store .dword 19 2 0x048#12
  | 124 => .store .dword 1 2 0x068#12
  | 128 => .opImm .add 19 10 0x000#12
  | 132 => .store .dword 8 2 0x060#12
  | 136 => .store .dword 9 2 0x058#12
  | 140 => .store .dword 18 2 0x050#12
  | 144 => .store .dword 20 2 0x040#12
  | 148 => .store .dword 21 2 0x038#12
  | 152 => .store .dword 22 2 0x030#12
  | 156 => .store .dword 23 2 0x028#12
  | 160 => .store .dword 24 2 0x020#12
  | 164 => .store .dword 25 2 0x018#12
  | 168 => .opImm .add 15 0 0x002#12
  | 172 => .opImm .add 10 0 0x001#12
  | 176 => .branch .beq 19 15 0x012c#13
  | 180 => .opImm .add 15 19 0x001#12
  | 184 => .opImm .srl 15 15 0x001#12
  | 188 => .opImm .add 22 19 0x000#12
  | 192 => .branch .bltu 15 22 0x0150#13
  | 196 => .opImm .add 15 0 0x002#12
  | 200 => .opImmWord .add 23 22 0x001#12
  | 204 => .opWord .div 9 23 15
  | 208 => .opImm .add 10 2 0x000#12
  | 212 => .opImmWord .add 18 22 0x000#12
  | 216 => .opImm .add 11 9 0x000#12
  | 220 => .auipc 1 0x00000#20
  | 224 => .jalr 1 1 0x3c4#12
  | 228 => .load .dword true 20 2 0x000#12
  | 232 => .opImm .add 15 0 0x001#12
  | 236 => .opImmWord .add 13 15 0x000#12
  | 240 => .branch .blt 13 9 0x0134#13
  | 244 => .opImm .add 11 9 0x000#12
  | 248 => .opImm .add 10 2 0x008#12
  | 252 => .auipc 1 0x00000#20
  | 256 => .jalr 1 1 0x3a4#12
  | 260 => .load .dword true 21 2 0x008#12
  | 264 => .opImm .add 15 0 0x000#12
  | 268 => .opImmWord .add 14 15 0x000#12
  | 272 => .branch .blt 14 9 0x0128#13
  | 276 => .auipc 25 0x00000#20
  | 280 => .opImm .add 25 25 0x3c4#12
  | 284 => .load .dword true 8 25 0x000#12
  | 288 => .opImm .sll 24 9 0x003#12
  | 292 => .opImm .add 12 24 0x000#12
  | 296 => .opImm .add 8 8 0x007#12
  | 300 => .opImm .and 8 8 0xff8#12
  | 304 => .opImm .add 11 0 0x000#12
  | 308 => .opImm .add 10 8 0x000#12
  | 312 => .auipc 1 0x00000#20
  | 316 => .jalr 1 1 0xeec#12
  | 320 => .opImm .add 14 0 0x000#12
  | 324 => .opImm .add 12 0 0x002#12
  | 328 => .opImmWord .add 15 14 0x000#12
  | 332 => .branch .blt 15 9 0x0108#13
  | 336 => .op .add 24 8 24
  | 340 => .op .add 15 24 23
  | 344 => .opImm .add 12 23 0x000#12
  | 348 => .opImm .add 11 0 0x000#12
  | 352 => .opImm .add 10 24 0x000#12
  | 356 => .store .dword 15 25 0x000#12
  | 360 => .opImmWord .add 22 22 0xfff#12
  | 364 => .auipc 1 0x00000#20
  | 368 => .jalr 1 1 0xeb8#12
  | 372 => .opImmWord .sra 22 22 0x001#12
  | 376 => .opImm .add 12 0 0x003#12
  | 380 => .opImm .add 14 0 0x000#12
  | 384 => .opImm .add 10 0 0x001#12
  | 388 => .opImmWord .add 13 12 0x000#12
  | 392 => .branch .bge 18 13 0x00f4#13
  | 396 => .opImmWord .add 15 14 0xfff#12
  | 400 => .opImmWord .sll 15 15 0x001#12
  | 404 => .opImmWord .add 13 9 0xfff#12
  | 408 => .opWord .add 15 15 9
  | 412 => .op .mul 15 15 13
  | 416 => .opImm .add 13 0 0x002#12
  | 420 => .op .div 15 15 13
  | 424 => .load .dword true 13 8 0x000#12
  | 428 => .op .add 15 15 13
  | 432 => .opImm .add 13 0 0x000#12
  | 436 => .opImm .add 13 13 0x001#12
  | 440 => .store .dword 15 8 0x000#12
  | 444 => .opImmWord .add 12 13 0x000#12
  | 448 => .branch .blt 12 9 0x022c#13
  | 452 => .opImm .add 16 14 0x000#12
  | 456 => .opImm .add 12 0 0x001#12
  | 460 => .opImmWord .add 17 12 0x000#12
  | 464 => .branch .blt 17 9 0x0230#13
  | 468 => .load .dword true 10 8 0x000#12
  | 472 => .opImm .add 10 10 0x001#12
  | 476 => .load .dword true 1 2 0x068#12
  | 480 => .load .dword true 8 2 0x060#12
  | 484 => .load .dword true 9 2 0x058#12
  | 488 => .load .dword true 18 2 0x050#12
  | 492 => .load .dword true 19 2 0x048#12
  | 496 => .load .dword true 20 2 0x040#12
  | 500 => .load .dword true 21 2 0x038#12
  | 504 => .load .dword true 22 2 0x030#12
  | 508 => .load .dword true 23 2 0x028#12
  | 512 => .load .dword true 24 2 0x020#12
  | 516 => .load .dword true 25 2 0x018#12
  | 520 => .opImm .add 2 2 0x070#12
  | 524 => .jalr 0 1 0x000#12
  | 528 => .op .divu 14 19 15
  | 532 => .opImm .add 22 15 0x000#12
  | 536 => .op .add 14 14 15
  | 540 => .opImm .srl 15 14 0x001#12
  | 544 => .jal 0 0x1ffea0#21
  | 548 => .opImm .sll 14 15 0x002#12
  | 552 => .op .add 14 20 14
  | 556 => .store .word 13 14 0x000#12
  | 560 => .opImm .add 15 15 0x001#12
  | 564 => .jal 0 0x1ffeb8#21
  | 568 => .opImm .sll 14 15 0x002#12
  | 572 => .opImmWord .sll 13 15 0x001#12
  | 576 => .op .add 14 21 14
  | 580 => .opImmWord .add 13 13 0x001#12
  | 584 => .store .word 13 14 0x000#12
  | 588 => .opImm .add 15 15 0x001#12
  | 592 => .jal 0 0x1ffebc#21
  | 596 => .opImm .sll 15 14 0x001#12
  | 600 => .opImm .add 15 15 0x001#12
  | 604 => .op .div 15 19 15
  | 608 => .opImm .sll 13 14 0x003#12
  | 612 => .op .add 13 13 8
  | 616 => .opImm .add 14 14 0x001#12
  | 620 => .opImm .add 15 15 0xfff#12
  | 624 => .op .div 15 15 12
  | 628 => .store .dword 15 13 0x000#12
  | 632 => .jal 0 0x1ffed0#21
  | 636 => .op .add 11 24 12
  | 640 => .load .byte false 15 11 0x000#12
  | 644 => .branch .bne 15 0 0x0054#13
  | 648 => .opWord .mul 15 13 13
  | 652 => .op .mul 16 15 15
  | 656 => .branch .blt 19 16 0x1efc#13
  | 660 => .store .byte 10 11 0x000#12
  | 664 => .opImmWord .sll 11 12 0x001#12
  | 668 => .opImmWord .add 16 15 0x000#12
  | 672 => .branch .bge 18 16 0x0040#13
  | 676 => .opImm .add 17 0 0x000#12
  | 680 => .opImm .add 16 0 0x000#12
  | 684 => .opImmWord .add 15 17 0x000#12
  | 688 => .branch .blt 15 9 0x0040#13
  | 692 => .opWord .div 15 18 13
  | 696 => .opImm .add 17 22 0x000#12
  | 700 => .opImmWord .add 15 15 0xfff#12
  | 704 => .opImm .or 15 15 0x001#12
  | 708 => .opImmWord .add 28 15 0x000#12
  | 712 => .opWord .mul 15 15 13
  | 716 => .branch .bge 28 13 0x00b8#13
  | 720 => .opImmWord .add 14 14 0x001#12
  | 724 => .opImm .add 9 16 0x000#12
  | 728 => .opImm .add 12 12 0x002#12
  | 732 => .jal 0 0x1ffea8#21
  | 736 => .op .add 16 24 15
  | 740 => .store .byte 10 16 0x000#12
  | 744 => .op .add 15 15 11
  | 748 => .jal 0 0x1fffb0#21
  | 752 => .opImm .sll 15 17 0x002#12
  | 756 => .op .add 15 21 15
  | 760 => .load .word true 6 15 0x000#12
  | 764 => .op .add 15 24 6
  | 768 => .load .byte false 15 15 0x000#12
  | 772 => .branch .bne 15 0 0x005c#13
  | 776 => .op .mul 15 6 12
  | 780 => .opImm .sll 28 17 0x003#12
  | 784 => .op .add 28 28 8
  | 788 => .load .dword true 28 28 0x000#12
  | 792 => .branch .blt 18 15 0x0050#13
  | 796 => .opImm .sra 15 15 0x001#12
  | 800 => .opImm .sll 15 15 0x002#12
  | 804 => .op .add 15 20 15
  | 808 => .load .word true 15 15 0x000#12
  | 812 => .opWord .sub 15 15 14
  | 816 => .opImm .sll 15 15 0x003#12
  | 820 => .op .add 15 8 15
  | 824 => .load .dword true 30 15 0x000#12
  | 828 => .opImm .sll 29 16 0x003#12
  | 832 => .op .sub 28 28 30
  | 836 => .opImm .sll 15 16 0x002#12
  | 840 => .op .add 29 8 29
  | 844 => .op .add 28 28 14
  | 848 => .store .dword 28 29 0x000#12
  | 852 => .op .add 15 21 15
  | 856 => .opImmWord .add 16 16 0x001#12
  | 860 => .store .word 6 15 0x000#12
  | 864 => .opImm .add 17 17 0x001#12
  | 868 => .jal 0 0x1fff48#21
  | 872 => .op .div 15 19 15
  | 876 => .opImmWord .add 15 15 0xfff#12
  | 880 => .opImmWord .sra 15 15 0x001#12
  | 884 => .opImm .sll 15 15 0x002#12
  | 888 => .op .add 15 20 15
  | 892 => .load .word true 30 15 0x000#12
  | 896 => .jal 0 0x1fffbc#21
  | 900 => .opImm .sra 6 28 0x001#12
  | 904 => .opImm .sll 6 6 0x002#12
  | 908 => .op .add 6 20 6
  | 912 => .load .word true 30 6 0x000#12
  | 916 => .opImmWord .sra 5 15 0x001#12
  | 920 => .opImm .sra 7 15 0x001#12
  | 924 => .opWord .sub 30 30 14
  | 928 => .opImm .add 6 17 0x000#12
  | 932 => .opImmWord .add 29 6 0x000#12
  | 936 => .branch .bge 29 7 0x0028#13
  | 940 => .opImmWord .add 29 5 0xfff#12
  | 944 => .opImm .add 6 0 0x000#12
  | 948 => .branch .blt 17 29 0x000c#13
  | 952 => .opImmWord .add 6 17 0x001#12
  | 956 => .opWord .sub 6 5 6
  | 960 => .opWord .add 17 6 17
  | 964 => .opImmWord .add 28 28 0xffe#12
  | 968 => .opWord .sub 15 15 11
  | 972 => .jal 0 0x1fff00#21
  | 976 => .opImm .sll 29 6 0x002#12
  | 980 => .op .add 29 20 29
  | 984 => .load .word true 31 29 0x000#12
  | 988 => .opImm .add 6 6 0xfff#12
  | 992 => .opWord .sub 31 31 30
  | 996 => .store .word 31 29 0x000#12
  | 1000 => .jal 0 0x1fffbc#21
  | 1004 => .opImm .sll 12 13 0x003#12
  | 1008 => .op .add 12 12 8
  | 1012 => .load .dword true 12 12 0x000#12
  | 1016 => .op .sub 15 15 12
  | 1020 => .jal 0 0x1ffdb8#21
  | 1024 => .opImm .sll 15 12 0x002#12
  | 1028 => .op .add 15 21 15
  | 1032 => .load .word true 15 15 0x000#12
  | 1036 => .op .div 6 19 15
  | 1040 => .op .div 15 6 15
  | 1044 => .opImmWord .add 15 15 0xfff#12
  | 1048 => .opImmWord .sra 15 15 0x001#12
  | 1052 => .opImm .sll 15 15 0x002#12
  | 1056 => .op .add 15 20 15
  | 1060 => .load .word true 13 15 0x000#12
  | 1064 => .opWord .sub 28 13 14
  | 1068 => .opImm .add 13 28 0x000#12
  | 1072 => .branch .bge 17 28 0x1da4#13
  | 1076 => .opImm .add 12 12 0x001#12
  | 1080 => .opImm .add 10 12 0x000#12
  | 1084 => .opImm .add 11 0 0x000#12
  | 1088 => .opImmWord .add 15 10 0x000#12
  | 1092 => .branch .bge 28 15 0x0024#13
  | 1096 => .opWord .sub 13 13 17
  | 1100 => .op .mul 13 13 16
  | 1104 => .load .dword true 15 8 0x000#12
  | 1108 => .opImm .add 16 16 0x001#12
  | 1112 => .op .sub 11 11 13
  | 1116 => .op .add 15 15 11
  | 1120 => .store .dword 15 8 0x000#12
  | 1124 => .jal 0 0x1ffd68#21
  | 1128 => .opImm .sll 15 10 0x002#12
  | 1132 => .op .add 15 21 15
  | 1136 => .load .word true 15 15 0x000#12
  | 1140 => .opImm .add 10 10 0x001#12
  | 1144 => .op .div 15 6 15
  | 1148 => .opImmWord .add 15 15 0xfff#12
  | 1152 => .opImmWord .sra 15 15 0x001#12
  | 1156 => .opImm .sll 15 15 0x002#12
  | 1160 => .op .add 15 20 15
  | 1164 => .load .word true 15 15 0x000#12
  | 1168 => .op .add 11 11 15
  | 1172 => .jal 0 0x1fffac#21
  | 1176 => .opImm .add 10 0 0x000#12
  | 1180 => .jalr 0 1 0x000#12
  | 1184 => .auipc 14 0x00000#20
  | 1188 => .opImm .add 14 14 0x038#12
  | 1192 => .load .dword true 15 14 0x000#12
  | 1196 => .opImm .sll 12 11 0x002#12
  | 1200 => .opImm .add 11 0 0x000#12
  | 1204 => .opImm .add 15 15 0x007#12
  | 1208 => .opImm .and 15 15 0xff8#12
  | 1212 => .store .dword 15 10 0x000#12
  | 1216 => .op .add 13 15 12
  | 1220 => .opImm .add 10 15 0x000#12
  | 1224 => .store .dword 13 14 0x000#12
  | 1228 => .auipc 6 0x00000#20
  | 1232 => .jalr 0 6 0xb58#12
  | _ => .ecall

/-! One rewrite rule per address, for symbolic execution. -/

@[gfetch] theorem instrAt_0 : instrAt 0 = .lui 2 0x00400#20 := rfl
@[gfetch] theorem instrAt_4 : instrAt 4 = .jal 1 0x000068#21 := rfl
@[gfetch] theorem instrAt_8 : instrAt 8 = .opImm .add 17 0 0x001#12 := rfl
@[gfetch] theorem instrAt_12 : instrAt 12 = .ecall := rfl
@[gfetch] theorem instrAt_16 : instrAt 16 = .opImm .add 10 0 0x00a#12 := rfl
@[gfetch] theorem instrAt_20 : instrAt 20 = .opImm .add 17 0 0x00b#12 := rfl
@[gfetch] theorem instrAt_24 : instrAt 24 = .ecall := rfl
@[gfetch] theorem instrAt_28 : instrAt 28 = .opImm .add 17 0 0x00a#12 := rfl
@[gfetch] theorem instrAt_32 : instrAt 32 = .ecall := rfl
@[gfetch] theorem instrAt_36 : instrAt 36 = .op .add 12 10 12 := rfl
@[gfetch] theorem instrAt_40 : instrAt 40 = .opImm .add 15 10 0x000#12 := rfl
@[gfetch] theorem instrAt_44 : instrAt 44 = .branch .bne 15 12 0x0008#13 := rfl
@[gfetch] theorem instrAt_48 : instrAt 48 = .jalr 0 1 0x000#12 := rfl
@[gfetch] theorem instrAt_52 : instrAt 52 = .opImm .add 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_56 : instrAt 56 = .store .byte 11 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_60 : instrAt 60 = .jal 0 0x1ffff0#21 := rfl
@[gfetch] theorem instrAt_64 : instrAt 64 = .opImm .add 15 10 0x001#12 := rfl
@[gfetch] theorem instrAt_68 : instrAt 68 = .opImm .srl 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_72 : instrAt 72 = .opImm .add 14 10 0x000#12 := rfl
@[gfetch] theorem instrAt_76 : instrAt 76 = .branch .bltu 15 14 0x000c#13 := rfl
@[gfetch] theorem instrAt_80 : instrAt 80 = .opImmWord .add 10 14 0x000#12 := rfl
@[gfetch] theorem instrAt_84 : instrAt 84 = .jalr 0 1 0x000#12 := rfl
@[gfetch] theorem instrAt_88 : instrAt 88 = .op .divu 13 10 15 := rfl
@[gfetch] theorem instrAt_92 : instrAt 92 = .opImm .add 14 15 0x000#12 := rfl
@[gfetch] theorem instrAt_96 : instrAt 96 = .op .add 13 13 15 := rfl
@[gfetch] theorem instrAt_100 : instrAt 100 = .opImm .srl 15 13 0x001#12 := rfl
@[gfetch] theorem instrAt_104 : instrAt 104 = .jal 0 0x1fffe4#21 := rfl
@[gfetch] theorem instrAt_108 : instrAt 108 = .opImm .add 15 0 0x001#12 := rfl
@[gfetch] theorem instrAt_112 : instrAt 112 = .branch .bge 15 10 0x0428#13 := rfl
@[gfetch] theorem instrAt_116 : instrAt 116 = .opImm .add 2 2 0xf90#12 := rfl
@[gfetch] theorem instrAt_120 : instrAt 120 = .store .dword 19 2 0x048#12 := rfl
@[gfetch] theorem instrAt_124 : instrAt 124 = .store .dword 1 2 0x068#12 := rfl
@[gfetch] theorem instrAt_128 : instrAt 128 = .opImm .add 19 10 0x000#12 := rfl
@[gfetch] theorem instrAt_132 : instrAt 132 = .store .dword 8 2 0x060#12 := rfl
@[gfetch] theorem instrAt_136 : instrAt 136 = .store .dword 9 2 0x058#12 := rfl
@[gfetch] theorem instrAt_140 : instrAt 140 = .store .dword 18 2 0x050#12 := rfl
@[gfetch] theorem instrAt_144 : instrAt 144 = .store .dword 20 2 0x040#12 := rfl
@[gfetch] theorem instrAt_148 : instrAt 148 = .store .dword 21 2 0x038#12 := rfl
@[gfetch] theorem instrAt_152 : instrAt 152 = .store .dword 22 2 0x030#12 := rfl
@[gfetch] theorem instrAt_156 : instrAt 156 = .store .dword 23 2 0x028#12 := rfl
@[gfetch] theorem instrAt_160 : instrAt 160 = .store .dword 24 2 0x020#12 := rfl
@[gfetch] theorem instrAt_164 : instrAt 164 = .store .dword 25 2 0x018#12 := rfl
@[gfetch] theorem instrAt_168 : instrAt 168 = .opImm .add 15 0 0x002#12 := rfl
@[gfetch] theorem instrAt_172 : instrAt 172 = .opImm .add 10 0 0x001#12 := rfl
@[gfetch] theorem instrAt_176 : instrAt 176 = .branch .beq 19 15 0x012c#13 := rfl
@[gfetch] theorem instrAt_180 : instrAt 180 = .opImm .add 15 19 0x001#12 := rfl
@[gfetch] theorem instrAt_184 : instrAt 184 = .opImm .srl 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_188 : instrAt 188 = .opImm .add 22 19 0x000#12 := rfl
@[gfetch] theorem instrAt_192 : instrAt 192 = .branch .bltu 15 22 0x0150#13 := rfl
@[gfetch] theorem instrAt_196 : instrAt 196 = .opImm .add 15 0 0x002#12 := rfl
@[gfetch] theorem instrAt_200 : instrAt 200 = .opImmWord .add 23 22 0x001#12 := rfl
@[gfetch] theorem instrAt_204 : instrAt 204 = .opWord .div 9 23 15 := rfl
@[gfetch] theorem instrAt_208 : instrAt 208 = .opImm .add 10 2 0x000#12 := rfl
@[gfetch] theorem instrAt_212 : instrAt 212 = .opImmWord .add 18 22 0x000#12 := rfl
@[gfetch] theorem instrAt_216 : instrAt 216 = .opImm .add 11 9 0x000#12 := rfl
@[gfetch] theorem instrAt_220 : instrAt 220 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_224 : instrAt 224 = .jalr 1 1 0x3c4#12 := rfl
@[gfetch] theorem instrAt_228 : instrAt 228 = .load .dword true 20 2 0x000#12 := rfl
@[gfetch] theorem instrAt_232 : instrAt 232 = .opImm .add 15 0 0x001#12 := rfl
@[gfetch] theorem instrAt_236 : instrAt 236 = .opImmWord .add 13 15 0x000#12 := rfl
@[gfetch] theorem instrAt_240 : instrAt 240 = .branch .blt 13 9 0x0134#13 := rfl
@[gfetch] theorem instrAt_244 : instrAt 244 = .opImm .add 11 9 0x000#12 := rfl
@[gfetch] theorem instrAt_248 : instrAt 248 = .opImm .add 10 2 0x008#12 := rfl
@[gfetch] theorem instrAt_252 : instrAt 252 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_256 : instrAt 256 = .jalr 1 1 0x3a4#12 := rfl
@[gfetch] theorem instrAt_260 : instrAt 260 = .load .dword true 21 2 0x008#12 := rfl
@[gfetch] theorem instrAt_264 : instrAt 264 = .opImm .add 15 0 0x000#12 := rfl
@[gfetch] theorem instrAt_268 : instrAt 268 = .opImmWord .add 14 15 0x000#12 := rfl
@[gfetch] theorem instrAt_272 : instrAt 272 = .branch .blt 14 9 0x0128#13 := rfl
@[gfetch] theorem instrAt_276 : instrAt 276 = .auipc 25 0x00000#20 := rfl
@[gfetch] theorem instrAt_280 : instrAt 280 = .opImm .add 25 25 0x3c4#12 := rfl
@[gfetch] theorem instrAt_284 : instrAt 284 = .load .dword true 8 25 0x000#12 := rfl
@[gfetch] theorem instrAt_288 : instrAt 288 = .opImm .sll 24 9 0x003#12 := rfl
@[gfetch] theorem instrAt_292 : instrAt 292 = .opImm .add 12 24 0x000#12 := rfl
@[gfetch] theorem instrAt_296 : instrAt 296 = .opImm .add 8 8 0x007#12 := rfl
@[gfetch] theorem instrAt_300 : instrAt 300 = .opImm .and 8 8 0xff8#12 := rfl
@[gfetch] theorem instrAt_304 : instrAt 304 = .opImm .add 11 0 0x000#12 := rfl
@[gfetch] theorem instrAt_308 : instrAt 308 = .opImm .add 10 8 0x000#12 := rfl
@[gfetch] theorem instrAt_312 : instrAt 312 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_316 : instrAt 316 = .jalr 1 1 0xeec#12 := rfl
@[gfetch] theorem instrAt_320 : instrAt 320 = .opImm .add 14 0 0x000#12 := rfl
@[gfetch] theorem instrAt_324 : instrAt 324 = .opImm .add 12 0 0x002#12 := rfl
@[gfetch] theorem instrAt_328 : instrAt 328 = .opImmWord .add 15 14 0x000#12 := rfl
@[gfetch] theorem instrAt_332 : instrAt 332 = .branch .blt 15 9 0x0108#13 := rfl
@[gfetch] theorem instrAt_336 : instrAt 336 = .op .add 24 8 24 := rfl
@[gfetch] theorem instrAt_340 : instrAt 340 = .op .add 15 24 23 := rfl
@[gfetch] theorem instrAt_344 : instrAt 344 = .opImm .add 12 23 0x000#12 := rfl
@[gfetch] theorem instrAt_348 : instrAt 348 = .opImm .add 11 0 0x000#12 := rfl
@[gfetch] theorem instrAt_352 : instrAt 352 = .opImm .add 10 24 0x000#12 := rfl
@[gfetch] theorem instrAt_356 : instrAt 356 = .store .dword 15 25 0x000#12 := rfl
@[gfetch] theorem instrAt_360 : instrAt 360 = .opImmWord .add 22 22 0xfff#12 := rfl
@[gfetch] theorem instrAt_364 : instrAt 364 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_368 : instrAt 368 = .jalr 1 1 0xeb8#12 := rfl
@[gfetch] theorem instrAt_372 : instrAt 372 = .opImmWord .sra 22 22 0x001#12 := rfl
@[gfetch] theorem instrAt_376 : instrAt 376 = .opImm .add 12 0 0x003#12 := rfl
@[gfetch] theorem instrAt_380 : instrAt 380 = .opImm .add 14 0 0x000#12 := rfl
@[gfetch] theorem instrAt_384 : instrAt 384 = .opImm .add 10 0 0x001#12 := rfl
@[gfetch] theorem instrAt_388 : instrAt 388 = .opImmWord .add 13 12 0x000#12 := rfl
@[gfetch] theorem instrAt_392 : instrAt 392 = .branch .bge 18 13 0x00f4#13 := rfl
@[gfetch] theorem instrAt_396 : instrAt 396 = .opImmWord .add 15 14 0xfff#12 := rfl
@[gfetch] theorem instrAt_400 : instrAt 400 = .opImmWord .sll 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_404 : instrAt 404 = .opImmWord .add 13 9 0xfff#12 := rfl
@[gfetch] theorem instrAt_408 : instrAt 408 = .opWord .add 15 15 9 := rfl
@[gfetch] theorem instrAt_412 : instrAt 412 = .op .mul 15 15 13 := rfl
@[gfetch] theorem instrAt_416 : instrAt 416 = .opImm .add 13 0 0x002#12 := rfl
@[gfetch] theorem instrAt_420 : instrAt 420 = .op .div 15 15 13 := rfl
@[gfetch] theorem instrAt_424 : instrAt 424 = .load .dword true 13 8 0x000#12 := rfl
@[gfetch] theorem instrAt_428 : instrAt 428 = .op .add 15 15 13 := rfl
@[gfetch] theorem instrAt_432 : instrAt 432 = .opImm .add 13 0 0x000#12 := rfl
@[gfetch] theorem instrAt_436 : instrAt 436 = .opImm .add 13 13 0x001#12 := rfl
@[gfetch] theorem instrAt_440 : instrAt 440 = .store .dword 15 8 0x000#12 := rfl
@[gfetch] theorem instrAt_444 : instrAt 444 = .opImmWord .add 12 13 0x000#12 := rfl
@[gfetch] theorem instrAt_448 : instrAt 448 = .branch .blt 12 9 0x022c#13 := rfl
@[gfetch] theorem instrAt_452 : instrAt 452 = .opImm .add 16 14 0x000#12 := rfl
@[gfetch] theorem instrAt_456 : instrAt 456 = .opImm .add 12 0 0x001#12 := rfl
@[gfetch] theorem instrAt_460 : instrAt 460 = .opImmWord .add 17 12 0x000#12 := rfl
@[gfetch] theorem instrAt_464 : instrAt 464 = .branch .blt 17 9 0x0230#13 := rfl
@[gfetch] theorem instrAt_468 : instrAt 468 = .load .dword true 10 8 0x000#12 := rfl
@[gfetch] theorem instrAt_472 : instrAt 472 = .opImm .add 10 10 0x001#12 := rfl
@[gfetch] theorem instrAt_476 : instrAt 476 = .load .dword true 1 2 0x068#12 := rfl
@[gfetch] theorem instrAt_480 : instrAt 480 = .load .dword true 8 2 0x060#12 := rfl
@[gfetch] theorem instrAt_484 : instrAt 484 = .load .dword true 9 2 0x058#12 := rfl
@[gfetch] theorem instrAt_488 : instrAt 488 = .load .dword true 18 2 0x050#12 := rfl
@[gfetch] theorem instrAt_492 : instrAt 492 = .load .dword true 19 2 0x048#12 := rfl
@[gfetch] theorem instrAt_496 : instrAt 496 = .load .dword true 20 2 0x040#12 := rfl
@[gfetch] theorem instrAt_500 : instrAt 500 = .load .dword true 21 2 0x038#12 := rfl
@[gfetch] theorem instrAt_504 : instrAt 504 = .load .dword true 22 2 0x030#12 := rfl
@[gfetch] theorem instrAt_508 : instrAt 508 = .load .dword true 23 2 0x028#12 := rfl
@[gfetch] theorem instrAt_512 : instrAt 512 = .load .dword true 24 2 0x020#12 := rfl
@[gfetch] theorem instrAt_516 : instrAt 516 = .load .dword true 25 2 0x018#12 := rfl
@[gfetch] theorem instrAt_520 : instrAt 520 = .opImm .add 2 2 0x070#12 := rfl
@[gfetch] theorem instrAt_524 : instrAt 524 = .jalr 0 1 0x000#12 := rfl
@[gfetch] theorem instrAt_528 : instrAt 528 = .op .divu 14 19 15 := rfl
@[gfetch] theorem instrAt_532 : instrAt 532 = .opImm .add 22 15 0x000#12 := rfl
@[gfetch] theorem instrAt_536 : instrAt 536 = .op .add 14 14 15 := rfl
@[gfetch] theorem instrAt_540 : instrAt 540 = .opImm .srl 15 14 0x001#12 := rfl
@[gfetch] theorem instrAt_544 : instrAt 544 = .jal 0 0x1ffea0#21 := rfl
@[gfetch] theorem instrAt_548 : instrAt 548 = .opImm .sll 14 15 0x002#12 := rfl
@[gfetch] theorem instrAt_552 : instrAt 552 = .op .add 14 20 14 := rfl
@[gfetch] theorem instrAt_556 : instrAt 556 = .store .word 13 14 0x000#12 := rfl
@[gfetch] theorem instrAt_560 : instrAt 560 = .opImm .add 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_564 : instrAt 564 = .jal 0 0x1ffeb8#21 := rfl
@[gfetch] theorem instrAt_568 : instrAt 568 = .opImm .sll 14 15 0x002#12 := rfl
@[gfetch] theorem instrAt_572 : instrAt 572 = .opImmWord .sll 13 15 0x001#12 := rfl
@[gfetch] theorem instrAt_576 : instrAt 576 = .op .add 14 21 14 := rfl
@[gfetch] theorem instrAt_580 : instrAt 580 = .opImmWord .add 13 13 0x001#12 := rfl
@[gfetch] theorem instrAt_584 : instrAt 584 = .store .word 13 14 0x000#12 := rfl
@[gfetch] theorem instrAt_588 : instrAt 588 = .opImm .add 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_592 : instrAt 592 = .jal 0 0x1ffebc#21 := rfl
@[gfetch] theorem instrAt_596 : instrAt 596 = .opImm .sll 15 14 0x001#12 := rfl
@[gfetch] theorem instrAt_600 : instrAt 600 = .opImm .add 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_604 : instrAt 604 = .op .div 15 19 15 := rfl
@[gfetch] theorem instrAt_608 : instrAt 608 = .opImm .sll 13 14 0x003#12 := rfl
@[gfetch] theorem instrAt_612 : instrAt 612 = .op .add 13 13 8 := rfl
@[gfetch] theorem instrAt_616 : instrAt 616 = .opImm .add 14 14 0x001#12 := rfl
@[gfetch] theorem instrAt_620 : instrAt 620 = .opImm .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_624 : instrAt 624 = .op .div 15 15 12 := rfl
@[gfetch] theorem instrAt_628 : instrAt 628 = .store .dword 15 13 0x000#12 := rfl
@[gfetch] theorem instrAt_632 : instrAt 632 = .jal 0 0x1ffed0#21 := rfl
@[gfetch] theorem instrAt_636 : instrAt 636 = .op .add 11 24 12 := rfl
@[gfetch] theorem instrAt_640 : instrAt 640 = .load .byte false 15 11 0x000#12 := rfl
@[gfetch] theorem instrAt_644 : instrAt 644 = .branch .bne 15 0 0x0054#13 := rfl
@[gfetch] theorem instrAt_648 : instrAt 648 = .opWord .mul 15 13 13 := rfl
@[gfetch] theorem instrAt_652 : instrAt 652 = .op .mul 16 15 15 := rfl
@[gfetch] theorem instrAt_656 : instrAt 656 = .branch .blt 19 16 0x1efc#13 := rfl
@[gfetch] theorem instrAt_660 : instrAt 660 = .store .byte 10 11 0x000#12 := rfl
@[gfetch] theorem instrAt_664 : instrAt 664 = .opImmWord .sll 11 12 0x001#12 := rfl
@[gfetch] theorem instrAt_668 : instrAt 668 = .opImmWord .add 16 15 0x000#12 := rfl
@[gfetch] theorem instrAt_672 : instrAt 672 = .branch .bge 18 16 0x0040#13 := rfl
@[gfetch] theorem instrAt_676 : instrAt 676 = .opImm .add 17 0 0x000#12 := rfl
@[gfetch] theorem instrAt_680 : instrAt 680 = .opImm .add 16 0 0x000#12 := rfl
@[gfetch] theorem instrAt_684 : instrAt 684 = .opImmWord .add 15 17 0x000#12 := rfl
@[gfetch] theorem instrAt_688 : instrAt 688 = .branch .blt 15 9 0x0040#13 := rfl
@[gfetch] theorem instrAt_692 : instrAt 692 = .opWord .div 15 18 13 := rfl
@[gfetch] theorem instrAt_696 : instrAt 696 = .opImm .add 17 22 0x000#12 := rfl
@[gfetch] theorem instrAt_700 : instrAt 700 = .opImmWord .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_704 : instrAt 704 = .opImm .or 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_708 : instrAt 708 = .opImmWord .add 28 15 0x000#12 := rfl
@[gfetch] theorem instrAt_712 : instrAt 712 = .opWord .mul 15 15 13 := rfl
@[gfetch] theorem instrAt_716 : instrAt 716 = .branch .bge 28 13 0x00b8#13 := rfl
@[gfetch] theorem instrAt_720 : instrAt 720 = .opImmWord .add 14 14 0x001#12 := rfl
@[gfetch] theorem instrAt_724 : instrAt 724 = .opImm .add 9 16 0x000#12 := rfl
@[gfetch] theorem instrAt_728 : instrAt 728 = .opImm .add 12 12 0x002#12 := rfl
@[gfetch] theorem instrAt_732 : instrAt 732 = .jal 0 0x1ffea8#21 := rfl
@[gfetch] theorem instrAt_736 : instrAt 736 = .op .add 16 24 15 := rfl
@[gfetch] theorem instrAt_740 : instrAt 740 = .store .byte 10 16 0x000#12 := rfl
@[gfetch] theorem instrAt_744 : instrAt 744 = .op .add 15 15 11 := rfl
@[gfetch] theorem instrAt_748 : instrAt 748 = .jal 0 0x1fffb0#21 := rfl
@[gfetch] theorem instrAt_752 : instrAt 752 = .opImm .sll 15 17 0x002#12 := rfl
@[gfetch] theorem instrAt_756 : instrAt 756 = .op .add 15 21 15 := rfl
@[gfetch] theorem instrAt_760 : instrAt 760 = .load .word true 6 15 0x000#12 := rfl
@[gfetch] theorem instrAt_764 : instrAt 764 = .op .add 15 24 6 := rfl
@[gfetch] theorem instrAt_768 : instrAt 768 = .load .byte false 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_772 : instrAt 772 = .branch .bne 15 0 0x005c#13 := rfl
@[gfetch] theorem instrAt_776 : instrAt 776 = .op .mul 15 6 12 := rfl
@[gfetch] theorem instrAt_780 : instrAt 780 = .opImm .sll 28 17 0x003#12 := rfl
@[gfetch] theorem instrAt_784 : instrAt 784 = .op .add 28 28 8 := rfl
@[gfetch] theorem instrAt_788 : instrAt 788 = .load .dword true 28 28 0x000#12 := rfl
@[gfetch] theorem instrAt_792 : instrAt 792 = .branch .blt 18 15 0x0050#13 := rfl
@[gfetch] theorem instrAt_796 : instrAt 796 = .opImm .sra 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_800 : instrAt 800 = .opImm .sll 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_804 : instrAt 804 = .op .add 15 20 15 := rfl
@[gfetch] theorem instrAt_808 : instrAt 808 = .load .word true 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_812 : instrAt 812 = .opWord .sub 15 15 14 := rfl
@[gfetch] theorem instrAt_816 : instrAt 816 = .opImm .sll 15 15 0x003#12 := rfl
@[gfetch] theorem instrAt_820 : instrAt 820 = .op .add 15 8 15 := rfl
@[gfetch] theorem instrAt_824 : instrAt 824 = .load .dword true 30 15 0x000#12 := rfl
@[gfetch] theorem instrAt_828 : instrAt 828 = .opImm .sll 29 16 0x003#12 := rfl
@[gfetch] theorem instrAt_832 : instrAt 832 = .op .sub 28 28 30 := rfl
@[gfetch] theorem instrAt_836 : instrAt 836 = .opImm .sll 15 16 0x002#12 := rfl
@[gfetch] theorem instrAt_840 : instrAt 840 = .op .add 29 8 29 := rfl
@[gfetch] theorem instrAt_844 : instrAt 844 = .op .add 28 28 14 := rfl
@[gfetch] theorem instrAt_848 : instrAt 848 = .store .dword 28 29 0x000#12 := rfl
@[gfetch] theorem instrAt_852 : instrAt 852 = .op .add 15 21 15 := rfl
@[gfetch] theorem instrAt_856 : instrAt 856 = .opImmWord .add 16 16 0x001#12 := rfl
@[gfetch] theorem instrAt_860 : instrAt 860 = .store .word 6 15 0x000#12 := rfl
@[gfetch] theorem instrAt_864 : instrAt 864 = .opImm .add 17 17 0x001#12 := rfl
@[gfetch] theorem instrAt_868 : instrAt 868 = .jal 0 0x1fff48#21 := rfl
@[gfetch] theorem instrAt_872 : instrAt 872 = .op .div 15 19 15 := rfl
@[gfetch] theorem instrAt_876 : instrAt 876 = .opImmWord .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_880 : instrAt 880 = .opImmWord .sra 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_884 : instrAt 884 = .opImm .sll 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_888 : instrAt 888 = .op .add 15 20 15 := rfl
@[gfetch] theorem instrAt_892 : instrAt 892 = .load .word true 30 15 0x000#12 := rfl
@[gfetch] theorem instrAt_896 : instrAt 896 = .jal 0 0x1fffbc#21 := rfl
@[gfetch] theorem instrAt_900 : instrAt 900 = .opImm .sra 6 28 0x001#12 := rfl
@[gfetch] theorem instrAt_904 : instrAt 904 = .opImm .sll 6 6 0x002#12 := rfl
@[gfetch] theorem instrAt_908 : instrAt 908 = .op .add 6 20 6 := rfl
@[gfetch] theorem instrAt_912 : instrAt 912 = .load .word true 30 6 0x000#12 := rfl
@[gfetch] theorem instrAt_916 : instrAt 916 = .opImmWord .sra 5 15 0x001#12 := rfl
@[gfetch] theorem instrAt_920 : instrAt 920 = .opImm .sra 7 15 0x001#12 := rfl
@[gfetch] theorem instrAt_924 : instrAt 924 = .opWord .sub 30 30 14 := rfl
@[gfetch] theorem instrAt_928 : instrAt 928 = .opImm .add 6 17 0x000#12 := rfl
@[gfetch] theorem instrAt_932 : instrAt 932 = .opImmWord .add 29 6 0x000#12 := rfl
@[gfetch] theorem instrAt_936 : instrAt 936 = .branch .bge 29 7 0x0028#13 := rfl
@[gfetch] theorem instrAt_940 : instrAt 940 = .opImmWord .add 29 5 0xfff#12 := rfl
@[gfetch] theorem instrAt_944 : instrAt 944 = .opImm .add 6 0 0x000#12 := rfl
@[gfetch] theorem instrAt_948 : instrAt 948 = .branch .blt 17 29 0x000c#13 := rfl
@[gfetch] theorem instrAt_952 : instrAt 952 = .opImmWord .add 6 17 0x001#12 := rfl
@[gfetch] theorem instrAt_956 : instrAt 956 = .opWord .sub 6 5 6 := rfl
@[gfetch] theorem instrAt_960 : instrAt 960 = .opWord .add 17 6 17 := rfl
@[gfetch] theorem instrAt_964 : instrAt 964 = .opImmWord .add 28 28 0xffe#12 := rfl
@[gfetch] theorem instrAt_968 : instrAt 968 = .opWord .sub 15 15 11 := rfl
@[gfetch] theorem instrAt_972 : instrAt 972 = .jal 0 0x1fff00#21 := rfl
@[gfetch] theorem instrAt_976 : instrAt 976 = .opImm .sll 29 6 0x002#12 := rfl
@[gfetch] theorem instrAt_980 : instrAt 980 = .op .add 29 20 29 := rfl
@[gfetch] theorem instrAt_984 : instrAt 984 = .load .word true 31 29 0x000#12 := rfl
@[gfetch] theorem instrAt_988 : instrAt 988 = .opImm .add 6 6 0xfff#12 := rfl
@[gfetch] theorem instrAt_992 : instrAt 992 = .opWord .sub 31 31 30 := rfl
@[gfetch] theorem instrAt_996 : instrAt 996 = .store .word 31 29 0x000#12 := rfl
@[gfetch] theorem instrAt_1000 : instrAt 1000 = .jal 0 0x1fffbc#21 := rfl
@[gfetch] theorem instrAt_1004 : instrAt 1004 = .opImm .sll 12 13 0x003#12 := rfl
@[gfetch] theorem instrAt_1008 : instrAt 1008 = .op .add 12 12 8 := rfl
@[gfetch] theorem instrAt_1012 : instrAt 1012 = .load .dword true 12 12 0x000#12 := rfl
@[gfetch] theorem instrAt_1016 : instrAt 1016 = .op .sub 15 15 12 := rfl
@[gfetch] theorem instrAt_1020 : instrAt 1020 = .jal 0 0x1ffdb8#21 := rfl
@[gfetch] theorem instrAt_1024 : instrAt 1024 = .opImm .sll 15 12 0x002#12 := rfl
@[gfetch] theorem instrAt_1028 : instrAt 1028 = .op .add 15 21 15 := rfl
@[gfetch] theorem instrAt_1032 : instrAt 1032 = .load .word true 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1036 : instrAt 1036 = .op .div 6 19 15 := rfl
@[gfetch] theorem instrAt_1040 : instrAt 1040 = .op .div 15 6 15 := rfl
@[gfetch] theorem instrAt_1044 : instrAt 1044 = .opImmWord .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_1048 : instrAt 1048 = .opImmWord .sra 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_1052 : instrAt 1052 = .opImm .sll 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_1056 : instrAt 1056 = .op .add 15 20 15 := rfl
@[gfetch] theorem instrAt_1060 : instrAt 1060 = .load .word true 13 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1064 : instrAt 1064 = .opWord .sub 28 13 14 := rfl
@[gfetch] theorem instrAt_1068 : instrAt 1068 = .opImm .add 13 28 0x000#12 := rfl
@[gfetch] theorem instrAt_1072 : instrAt 1072 = .branch .bge 17 28 0x1da4#13 := rfl
@[gfetch] theorem instrAt_1076 : instrAt 1076 = .opImm .add 12 12 0x001#12 := rfl
@[gfetch] theorem instrAt_1080 : instrAt 1080 = .opImm .add 10 12 0x000#12 := rfl
@[gfetch] theorem instrAt_1084 : instrAt 1084 = .opImm .add 11 0 0x000#12 := rfl
@[gfetch] theorem instrAt_1088 : instrAt 1088 = .opImmWord .add 15 10 0x000#12 := rfl
@[gfetch] theorem instrAt_1092 : instrAt 1092 = .branch .bge 28 15 0x0024#13 := rfl
@[gfetch] theorem instrAt_1096 : instrAt 1096 = .opWord .sub 13 13 17 := rfl
@[gfetch] theorem instrAt_1100 : instrAt 1100 = .op .mul 13 13 16 := rfl
@[gfetch] theorem instrAt_1104 : instrAt 1104 = .load .dword true 15 8 0x000#12 := rfl
@[gfetch] theorem instrAt_1108 : instrAt 1108 = .opImm .add 16 16 0x001#12 := rfl
@[gfetch] theorem instrAt_1112 : instrAt 1112 = .op .sub 11 11 13 := rfl
@[gfetch] theorem instrAt_1116 : instrAt 1116 = .op .add 15 15 11 := rfl
@[gfetch] theorem instrAt_1120 : instrAt 1120 = .store .dword 15 8 0x000#12 := rfl
@[gfetch] theorem instrAt_1124 : instrAt 1124 = .jal 0 0x1ffd68#21 := rfl
@[gfetch] theorem instrAt_1128 : instrAt 1128 = .opImm .sll 15 10 0x002#12 := rfl
@[gfetch] theorem instrAt_1132 : instrAt 1132 = .op .add 15 21 15 := rfl
@[gfetch] theorem instrAt_1136 : instrAt 1136 = .load .word true 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1140 : instrAt 1140 = .opImm .add 10 10 0x001#12 := rfl
@[gfetch] theorem instrAt_1144 : instrAt 1144 = .op .div 15 6 15 := rfl
@[gfetch] theorem instrAt_1148 : instrAt 1148 = .opImmWord .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_1152 : instrAt 1152 = .opImmWord .sra 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_1156 : instrAt 1156 = .opImm .sll 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_1160 : instrAt 1160 = .op .add 15 20 15 := rfl
@[gfetch] theorem instrAt_1164 : instrAt 1164 = .load .word true 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1168 : instrAt 1168 = .op .add 11 11 15 := rfl
@[gfetch] theorem instrAt_1172 : instrAt 1172 = .jal 0 0x1fffac#21 := rfl
@[gfetch] theorem instrAt_1176 : instrAt 1176 = .opImm .add 10 0 0x000#12 := rfl
@[gfetch] theorem instrAt_1180 : instrAt 1180 = .jalr 0 1 0x000#12 := rfl
@[gfetch] theorem instrAt_1184 : instrAt 1184 = .auipc 14 0x00000#20 := rfl
@[gfetch] theorem instrAt_1188 : instrAt 1188 = .opImm .add 14 14 0x038#12 := rfl
@[gfetch] theorem instrAt_1192 : instrAt 1192 = .load .dword true 15 14 0x000#12 := rfl
@[gfetch] theorem instrAt_1196 : instrAt 1196 = .opImm .sll 12 11 0x002#12 := rfl
@[gfetch] theorem instrAt_1200 : instrAt 1200 = .opImm .add 11 0 0x000#12 := rfl
@[gfetch] theorem instrAt_1204 : instrAt 1204 = .opImm .add 15 15 0x007#12 := rfl
@[gfetch] theorem instrAt_1208 : instrAt 1208 = .opImm .and 15 15 0xff8#12 := rfl
@[gfetch] theorem instrAt_1212 : instrAt 1212 = .store .dword 15 10 0x000#12 := rfl
@[gfetch] theorem instrAt_1216 : instrAt 1216 = .op .add 13 15 12 := rfl
@[gfetch] theorem instrAt_1220 : instrAt 1220 = .opImm .add 10 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1224 : instrAt 1224 = .store .dword 13 14 0x000#12 := rfl
@[gfetch] theorem instrAt_1228 : instrAt 1228 = .auipc 6 0x00000#20 := rfl
@[gfetch] theorem instrAt_1232 : instrAt 1232 = .jalr 0 6 0xb58#12 := rfl

/-! Sign extension of every immediate in the program, so that symbolic execution does not
leave it to the kernel to evaluate. -/

@[gfetch] theorem sext_u0 : BitVec.signExtend 64 (0x0#20 ++ 0#12) = 0#64 := by decide
@[gfetch] theorem sext_u1024 : BitVec.signExtend 64 (0x400#20 ++ 0#12) = 4194304#64 := by decide
@[gfetch] theorem sextw_12_0 : BitVec.signExtend 32 (0x0#12) = 0#32 := by decide
@[gfetch] theorem sextw_12_1 : BitVec.signExtend 32 (0x1#12) = 1#32 := by decide
@[gfetch] theorem sextw_12_4094 : BitVec.signExtend 32 (0xffe#12) = 4294967294#32 := by decide
@[gfetch] theorem sextw_12_4095 : BitVec.signExtend 32 (0xfff#12) = 4294967295#32 := by decide
@[gfetch] theorem sext_12_0 : BitVec.signExtend 64 (0x0#12) = 0#64 := by decide
@[gfetch] theorem sext_12_1 : BitVec.signExtend 64 (0x1#12) = 1#64 := by decide
@[gfetch] theorem sext_12_2 : BitVec.signExtend 64 (0x2#12) = 2#64 := by decide
@[gfetch] theorem sext_12_3 : BitVec.signExtend 64 (0x3#12) = 3#64 := by decide
@[gfetch] theorem sext_12_7 : BitVec.signExtend 64 (0x7#12) = 7#64 := by decide
@[gfetch] theorem sext_12_8 : BitVec.signExtend 64 (0x8#12) = 8#64 := by decide
@[gfetch] theorem sext_13_8 : BitVec.signExtend 64 (0x8#13) = 8#64 := by decide
@[gfetch] theorem sext_12_10 : BitVec.signExtend 64 (0xa#12) = 10#64 := by decide
@[gfetch] theorem sext_12_11 : BitVec.signExtend 64 (0xb#12) = 11#64 := by decide
@[gfetch] theorem sext_13_12 : BitVec.signExtend 64 (0xc#13) = 12#64 := by decide
@[gfetch] theorem sext_12_24 : BitVec.signExtend 64 (0x18#12) = 24#64 := by decide
@[gfetch] theorem sext_12_32 : BitVec.signExtend 64 (0x20#12) = 32#64 := by decide
@[gfetch] theorem sext_13_36 : BitVec.signExtend 64 (0x24#13) = 36#64 := by decide
@[gfetch] theorem sext_12_40 : BitVec.signExtend 64 (0x28#12) = 40#64 := by decide
@[gfetch] theorem sext_13_40 : BitVec.signExtend 64 (0x28#13) = 40#64 := by decide
@[gfetch] theorem sext_12_48 : BitVec.signExtend 64 (0x30#12) = 48#64 := by decide
@[gfetch] theorem sext_12_56 : BitVec.signExtend 64 (0x38#12) = 56#64 := by decide
@[gfetch] theorem sext_12_64 : BitVec.signExtend 64 (0x40#12) = 64#64 := by decide
@[gfetch] theorem sext_13_64 : BitVec.signExtend 64 (0x40#13) = 64#64 := by decide
@[gfetch] theorem sext_12_72 : BitVec.signExtend 64 (0x48#12) = 72#64 := by decide
@[gfetch] theorem sext_12_80 : BitVec.signExtend 64 (0x50#12) = 80#64 := by decide
@[gfetch] theorem sext_13_80 : BitVec.signExtend 64 (0x50#13) = 80#64 := by decide
@[gfetch] theorem sext_13_84 : BitVec.signExtend 64 (0x54#13) = 84#64 := by decide
@[gfetch] theorem sext_12_88 : BitVec.signExtend 64 (0x58#12) = 88#64 := by decide
@[gfetch] theorem sext_13_92 : BitVec.signExtend 64 (0x5c#13) = 92#64 := by decide
@[gfetch] theorem sext_12_96 : BitVec.signExtend 64 (0x60#12) = 96#64 := by decide
@[gfetch] theorem sext_12_104 : BitVec.signExtend 64 (0x68#12) = 104#64 := by decide
@[gfetch] theorem sext_21_104 : BitVec.signExtend 64 (0x68#21) = 104#64 := by decide
@[gfetch] theorem sext_12_112 : BitVec.signExtend 64 (0x70#12) = 112#64 := by decide
@[gfetch] theorem sext_13_184 : BitVec.signExtend 64 (0xb8#13) = 184#64 := by decide
@[gfetch] theorem sext_13_244 : BitVec.signExtend 64 (0xf4#13) = 244#64 := by decide
@[gfetch] theorem sext_13_264 : BitVec.signExtend 64 (0x108#13) = 264#64 := by decide
@[gfetch] theorem sext_13_296 : BitVec.signExtend 64 (0x128#13) = 296#64 := by decide
@[gfetch] theorem sext_13_300 : BitVec.signExtend 64 (0x12c#13) = 300#64 := by decide
@[gfetch] theorem sext_13_308 : BitVec.signExtend 64 (0x134#13) = 308#64 := by decide
@[gfetch] theorem sext_13_336 : BitVec.signExtend 64 (0x150#13) = 336#64 := by decide
@[gfetch] theorem sext_13_556 : BitVec.signExtend 64 (0x22c#13) = 556#64 := by decide
@[gfetch] theorem sext_13_560 : BitVec.signExtend 64 (0x230#13) = 560#64 := by decide
@[gfetch] theorem sext_12_932 : BitVec.signExtend 64 (0x3a4#12) = 932#64 := by decide
@[gfetch] theorem sext_12_964 : BitVec.signExtend 64 (0x3c4#12) = 964#64 := by decide
@[gfetch] theorem sext_13_1064 : BitVec.signExtend 64 (0x428#13) = 1064#64 := by decide
@[gfetch] theorem sext_12_2904 : BitVec.signExtend 64 (0xb58#12) = 18446744073709550424#64 := by decide
@[gfetch] theorem sext_12_3768 : BitVec.signExtend 64 (0xeb8#12) = 18446744073709551288#64 := by decide
@[gfetch] theorem sext_12_3820 : BitVec.signExtend 64 (0xeec#12) = 18446744073709551340#64 := by decide
@[gfetch] theorem sext_12_3984 : BitVec.signExtend 64 (0xf90#12) = 18446744073709551504#64 := by decide
@[gfetch] theorem sext_12_4088 : BitVec.signExtend 64 (0xff8#12) = 18446744073709551608#64 := by decide
@[gfetch] theorem sext_12_4095 : BitVec.signExtend 64 (0xfff#12) = 18446744073709551615#64 := by decide
@[gfetch] theorem sext_13_7588 : BitVec.signExtend 64 (0x1da4#13) = 18446744073709551012#64 := by decide
@[gfetch] theorem sext_13_7932 : BitVec.signExtend 64 (0x1efc#13) = 18446744073709551356#64 := by decide
@[gfetch] theorem sext_21_2096488 : BitVec.signExtend 64 (0x1ffd68#21) = 18446744073709550952#64 := by decide
@[gfetch] theorem sext_21_2096568 : BitVec.signExtend 64 (0x1ffdb8#21) = 18446744073709551032#64 := by decide
@[gfetch] theorem sext_21_2096800 : BitVec.signExtend 64 (0x1ffea0#21) = 18446744073709551264#64 := by decide
@[gfetch] theorem sext_21_2096808 : BitVec.signExtend 64 (0x1ffea8#21) = 18446744073709551272#64 := by decide
@[gfetch] theorem sext_21_2096824 : BitVec.signExtend 64 (0x1ffeb8#21) = 18446744073709551288#64 := by decide
@[gfetch] theorem sext_21_2096828 : BitVec.signExtend 64 (0x1ffebc#21) = 18446744073709551292#64 := by decide
@[gfetch] theorem sext_21_2096848 : BitVec.signExtend 64 (0x1ffed0#21) = 18446744073709551312#64 := by decide
@[gfetch] theorem sext_21_2096896 : BitVec.signExtend 64 (0x1fff00#21) = 18446744073709551360#64 := by decide
@[gfetch] theorem sext_21_2096968 : BitVec.signExtend 64 (0x1fff48#21) = 18446744073709551432#64 := by decide
@[gfetch] theorem sext_21_2097068 : BitVec.signExtend 64 (0x1fffac#21) = 18446744073709551532#64 := by decide
@[gfetch] theorem sext_21_2097072 : BitVec.signExtend 64 (0x1fffb0#21) = 18446744073709551536#64 := by decide
@[gfetch] theorem sext_21_2097084 : BitVec.signExtend 64 (0x1fffbc#21) = 18446744073709551548#64 := by decide
@[gfetch] theorem sext_21_2097124 : BitVec.signExtend 64 (0x1fffe4#21) = 18446744073709551588#64 := by decide
@[gfetch] theorem sext_21_2097136 : BitVec.signExtend 64 (0x1ffff0#21) = 18446744073709551600#64 := by decide

theorem fetch : ∀ pc, pc < codeEnd → pc % 4 = 0 →
    (readBytes image pc 4).bind (decode 64) = some (instrAt pc) := by
  decide +kernel

theorem step_at (x : Regs 64) (pc : Nat) (mem : Array (BitVec 8))
    (out : String) (st : Status) (hmem : Prefix image mem 1236)
    (h : pc < 1236) (h4 : pc % 4 = 0) :
    step ⟨x, BitVec.ofNat 64 pc, mem, [], out, st⟩ =
      exec (instrAt pc) ⟨x, BitVec.ofNat 64 pc, mem, [], out, st⟩ := by
  have hpc : (BitVec.ofNat 64 pc).toNat = pc := by
    rw [BitVec.toNat_ofNat]; omega
  apply step_of_prefix _ image 1236 hmem (by change (BitVec.ofNat 64 pc).toNat + 4 ≤ 1236; omega)
  change (readBytes image (BitVec.ofNat 64 pc).toNat 4).bind (decode 64) = _
  rw [hpc]
  exact fetch _ h h4

end TinyFive.GrumpyBinary
