import TinyFive.Machine
import TinyFive.SieveMemory
import LucyMemory
import ZjyBinary.Program
import GrumpyBinary.Attr

/-! Instruction fetch for the recompiled zjy2008 image.

`instrAt` is the decoded instruction at every code address below `codeEnd = 1480`; `fetch`
checks it against the loaded words by `decide`. The `gfetch` lemmas are shared with the
grumpygordon proof, whose arithmetic rewrite rules this proof reuses. -/
namespace TinyFive.ZjyBinary
open SieveMemory

/-- The loaded image: code, the wheel table and the initial heap cursor. -/
def image : Array (BitVec 8) := (load 64 prog 1520 []).mem

/-- The end of the code; the wheel table is at 1480 and the 8-byte heap cursor at 1512. -/
abbrev codeEnd : Nat := 1480

def instrAt : Nat → Instr
  | 0 => .lui 2 0x00400#20
  | 4 => .jal 1 0x000214#21
  | 8 => .opImm .add 17 0 0x001#12
  | 12 => .ecall
  | 16 => .opImm .add 10 0 0x00a#12
  | 20 => .opImm .add 17 0 0x00b#12
  | 24 => .ecall
  | 28 => .opImm .add 17 0 0x00a#12
  | 32 => .ecall
  | 36 => .load .dword true 15 10 0x000#12
  | 40 => .opImm .add 2 2 0xff0#12
  | 44 => .opImm .add 14 0 0x001#12
  | 48 => .load .dword true 31 15 0x000#12
  | 52 => .store .dword 8 2 0x008#12
  | 56 => .load .dword true 30 10 0x008#12
  | 60 => .op .add 15 31 11
  | 64 => .store .byte 14 15 0x000#12
  | 68 => .opWord .mul 15 11 11
  | 72 => .load .word true 12 30 0x000#12
  | 76 => .opImmWord .sll 14 11 0x001#12
  | 80 => .opImm .add 16 0 0x001#12
  | 84 => .opImmWord .add 13 15 0x000#12
  | 88 => .branch .bge 12 13 0x0068#13
  | 92 => .load .dword true 7 10 0x010#12
  | 96 => .load .dword true 28 10 0x030#12
  | 100 => .opImm .add 16 0 0x000#12
  | 104 => .opImm .add 12 0 0x000#12
  | 108 => .load .word true 14 7 0x000#12
  | 112 => .opImmWord .add 15 16 0x000#12
  | 116 => .branch .blt 15 14 0x005c#13
  | 120 => .store .word 12 7 0x000#12
  | 124 => .load .word true 15 30 0x000#12
  | 128 => .opImm .add 17 0 0xffe#12
  | 132 => .opWord .mul 17 17 11
  | 136 => .opImmWord .add 14 15 0xfff#12
  | 140 => .opImmWord .sra 14 14 0x001#12
  | 144 => .opWord .div 15 15 11
  | 148 => .opImmWord .add 15 15 0xfff#12
  | 152 => .opImm .or 15 15 0x001#12
  | 156 => .opImmWord .add 16 15 0x000#12
  | 160 => .opWord .mul 15 15 11
  | 164 => .load .word true 12 28 0x000#12
  | 168 => .branch .bge 16 11 0x00e4#13
  | 172 => .load .dword true 8 2 0x008#12
  | 176 => .opImmWord .add 12 12 0x001#12
  | 180 => .store .word 12 28 0x000#12
  | 184 => .opImm .add 2 2 0x010#12
  | 188 => .jalr 0 1 0x000#12
  | 192 => .op .add 13 31 15
  | 196 => .store .byte 16 13 0x000#12
  | 200 => .op .add 15 15 14
  | 204 => .jal 0 0x1fff88#21
  | 208 => .load .dword true 15 10 0x018#12
  | 212 => .load .dword true 29 15 0x000#12
  | 216 => .opImm .sll 15 16 0x002#12
  | 220 => .op .add 15 29 15
  | 224 => .load .word true 5 15 0x000#12
  | 228 => .op .add 15 31 5
  | 232 => .load .byte false 15 15 0x000#12
  | 236 => .branch .bne 15 0 0x0074#13
  | 240 => .load .dword true 15 10 0x020#12
  | 244 => .op .mul 14 5 11
  | 248 => .load .word true 8 28 0x000#12
  | 252 => .load .dword true 17 15 0x000#12
  | 256 => .opImm .sll 15 16 0x003#12
  | 260 => .op .add 15 17 15
  | 264 => .load .dword true 6 15 0x000#12
  | 268 => .load .dword true 15 10 0x028#12
  | 272 => .load .dword true 13 15 0x000#12
  | 276 => .load .word true 15 30 0x000#12
  | 280 => .branch .blt 15 14 0x0050#13
  | 284 => .opImm .sra 14 14 0x001#12
  | 288 => .opImm .sll 14 14 0x002#12
  | 292 => .op .add 13 13 14
  | 296 => .load .word true 15 13 0x000#12
  | 300 => .opWord .sub 15 15 8
  | 304 => .opImm .sll 15 15 0x003#12
  | 308 => .op .add 15 17 15
  | 312 => .load .dword true 14 15 0x000#12
  | 316 => .opImm .sll 13 12 0x003#12
  | 320 => .op .sub 6 6 14
  | 324 => .opImm .sll 15 12 0x002#12
  | 328 => .op .add 17 17 13
  | 332 => .op .add 6 6 8
  | 336 => .store .dword 6 17 0x000#12
  | 340 => .op .add 29 29 15
  | 344 => .opImmWord .add 12 12 0x001#12
  | 348 => .store .word 5 29 0x000#12
  | 352 => .opImm .add 16 16 0x001#12
  | 356 => .jal 0 0x1fff08#21
  | 360 => .load .dword true 15 10 0x038#12
  | 364 => .load .dword true 15 15 0x000#12
  | 368 => .op .div 15 15 14
  | 372 => .opImm .add 15 15 0xfff#12
  | 376 => .opImm .sra 15 15 0x001#12
  | 380 => .opImm .sll 15 15 0x002#12
  | 384 => .op .add 13 13 15
  | 388 => .load .word true 14 13 0x000#12
  | 392 => .jal 0 0x1fffb4#21
  | 396 => .load .dword true 13 10 0x028#12
  | 400 => .opImmWord .sra 30 15 0x001#12
  | 404 => .opImm .sra 5 15 0x001#12
  | 408 => .load .dword true 31 13 0x000#12
  | 412 => .opImm .sra 13 16 0x001#12
  | 416 => .opImm .sll 13 13 0x002#12
  | 420 => .op .add 13 31 13
  | 424 => .load .word true 6 13 0x000#12
  | 428 => .opImm .add 13 14 0x000#12
  | 432 => .opWord .sub 6 6 12
  | 436 => .opImmWord .add 12 13 0x000#12
  | 440 => .branch .bge 12 5 0x0028#13
  | 444 => .opImmWord .add 12 30 0xfff#12
  | 448 => .opImm .add 13 0 0x000#12
  | 452 => .branch .blt 14 12 0x000c#13
  | 456 => .opImmWord .add 13 14 0x001#12
  | 460 => .opWord .sub 13 30 13
  | 464 => .opWord .add 14 13 14
  | 468 => .opImmWord .add 16 16 0xffe#12
  | 472 => .opWord .add 15 15 17
  | 476 => .jal 0 0x1ffec8#21
  | 480 => .opImm .sll 12 13 0x002#12
  | 484 => .op .add 12 31 12
  | 488 => .load .word true 29 12 0x000#12
  | 492 => .opImm .add 13 13 0xfff#12
  | 496 => .opWord .sub 29 29 6
  | 500 => .store .word 29 12 0x000#12
  | 504 => .jal 0 0x1fffbc#21
  | 508 => .op .add 12 10 12
  | 512 => .opImm .add 15 10 0x000#12
  | 516 => .branch .bne 15 12 0x0008#13
  | 520 => .jalr 0 1 0x000#12
  | 524 => .opImm .add 15 15 0x001#12
  | 528 => .store .byte 11 15 0xfff#12
  | 532 => .jal 0 0x1ffff0#21
  | 536 => .opImm .add 2 2 0xf30#12
  | 540 => .store .dword 1 2 0x0c8#12
  | 544 => .store .dword 8 2 0x0c0#12
  | 548 => .store .dword 9 2 0x0b8#12
  | 552 => .store .dword 18 2 0x0b0#12
  | 556 => .store .dword 19 2 0x0a8#12
  | 560 => .store .dword 20 2 0x0a0#12
  | 564 => .store .dword 21 2 0x098#12
  | 568 => .store .dword 22 2 0x090#12
  | 572 => .store .dword 23 2 0x088#12
  | 576 => .store .dword 10 2 0x008#12
  | 580 => .opImm .add 15 0 0x006#12
  | 584 => .branch .blt 15 10 0x0050#13
  | 588 => .opImm .slt 15 10 0x002#12
  | 592 => .opImm .slt 14 10 0x003#12
  | 596 => .opImm .sltu 15 15 0x001#12
  | 600 => .opImm .sltu 14 14 0x001#12
  | 604 => .opImm .slt 10 10 0x005#12
  | 608 => .opWord .add 15 15 14
  | 612 => .opImm .sltu 10 10 0x001#12
  | 616 => .opWord .add 10 15 10
  | 620 => .load .dword true 1 2 0x0c8#12
  | 624 => .load .dword true 8 2 0x0c0#12
  | 628 => .load .dword true 9 2 0x0b8#12
  | 632 => .load .dword true 18 2 0x0b0#12
  | 636 => .load .dword true 19 2 0x0a8#12
  | 640 => .load .dword true 20 2 0x0a0#12
  | 644 => .load .dword true 21 2 0x098#12
  | 648 => .load .dword true 22 2 0x090#12
  | 652 => .load .dword true 23 2 0x088#12
  | 656 => .opImm .add 2 2 0x0d0#12
  | 660 => .jalr 0 1 0x000#12
  | 664 => .opImm .add 15 10 0x001#12
  | 668 => .opImm .srl 15 15 0x001#12
  | 672 => .opImm .add 11 10 0x000#12
  | 676 => .branch .bltu 15 11 0x01c4#13
  | 680 => .opImmWord .add 11 11 0x000#12
  | 684 => .opImm .add 15 11 0x001#12
  | 688 => .store .word 11 2 0x014#12
  | 692 => .opImm .srl 15 15 0x001#12
  | 696 => .opImm .add 19 11 0x000#12
  | 700 => .branch .bltu 15 19 0x01c0#13
  | 704 => .opImm .add 15 0 0x002#12
  | 708 => .opImmWord .add 11 11 0x001#12
  | 712 => .opWord .div 11 11 15
  | 716 => .opImm .add 20 2 0x020#12
  | 720 => .opImm .add 10 20 0x000#12
  | 724 => .store .word 0 2 0x018#12
  | 728 => .opImm .add 21 2 0x028#12
  | 732 => .auipc 18 0x00000#20
  | 736 => .opImm .add 18 18 0x30c#12
  | 740 => .store .word 11 2 0x01c#12
  | 744 => .auipc 1 0x00000#20
  | 748 => .jalr 1 1 0x2ac#12
  | 752 => .load .word true 11 2 0x01c#12
  | 756 => .opImm .add 10 21 0x000#12
  | 760 => .auipc 1 0x00000#20
  | 764 => .jalr 1 1 0x29c#12
  | 768 => .load .dword true 8 18 0x000#12
  | 772 => .load .word true 9 2 0x014#12
  | 776 => .opImm .add 11 0 0x000#12
  | 780 => .opImm .add 8 8 0x007#12
  | 784 => .opImm .and 8 8 0xff8#12
  | 788 => .opImmWord .add 9 9 0x001#12
  | 792 => .opImm .add 12 9 0x000#12
  | 796 => .opImm .add 10 8 0x000#12
  | 800 => .store .dword 8 2 0x030#12
  | 804 => .auipc 1 0x00000#20
  | 808 => .jalr 1 1 0xed8#12
  | 812 => .load .word true 12 2 0x01c#12
  | 816 => .opImm .add 9 9 0x007#12
  | 820 => .op .add 10 8 9
  | 824 => .opImm .and 10 10 0xff8#12
  | 828 => .opImm .sll 12 12 0x003#12
  | 832 => .op .add 15 10 12
  | 836 => .opImm .add 11 0 0x000#12
  | 840 => .store .dword 15 18 0x000#12
  | 844 => .store .dword 10 2 0x038#12
  | 848 => .auipc 1 0x00000#20
  | 852 => .jalr 1 1 0xeac#12
  | 856 => .load .dword true 8 2 0x020#12
  | 860 => .load .dword true 9 2 0x028#12
  | 864 => .load .dword true 18 2 0x038#12
  | 868 => .opImm .add 13 0 0x001#12
  | 872 => .opImm .add 14 0 0x000#12
  | 876 => .load .word true 15 2 0x01c#12
  | 880 => .opImmWord .add 12 14 0x000#12
  | 884 => .branch .blt 12 15 0x011c#13
  | 888 => .opImm .add 15 2 0x030#12
  | 892 => .store .dword 15 2 0x040#12
  | 896 => .opImm .add 15 2 0x014#12
  | 900 => .store .dword 15 2 0x048#12
  | 904 => .opImm .add 15 2 0x01c#12
  | 908 => .store .dword 15 2 0x050#12
  | 912 => .opImm .add 15 2 0x038#12
  | 916 => .store .dword 15 2 0x060#12
  | 920 => .load .word true 14 2 0x014#12
  | 924 => .opImm .add 15 2 0x018#12
  | 928 => .store .dword 15 2 0x070#12
  | 932 => .opImm .add 15 2 0x008#12
  | 936 => .store .dword 15 2 0x078#12
  | 940 => .store .dword 21 2 0x058#12
  | 944 => .store .dword 20 2 0x068#12
  | 948 => .opImm .add 15 0 0x008#12
  | 952 => .branch .blt 15 14 0x0114#13
  | 956 => .load .word true 13 2 0x01c#12
  | 960 => .load .word true 12 2 0x018#12
  | 964 => .opImm .add 15 13 0xfff#12
  | 968 => .opWord .add 10 13 12
  | 972 => .opWord .add 10 10 12
  | 976 => .opImmWord .add 10 10 0xffe#12
  | 980 => .op .mul 10 10 15
  | 984 => .opImm .add 15 0 0x002#12
  | 988 => .op .div 10 10 15
  | 992 => .load .dword true 15 18 0x000#12
  | 996 => .opImm .add 15 15 0x001#12
  | 1000 => .op .add 10 10 15
  | 1004 => .opImm .add 15 0 0x000#12
  | 1008 => .opImm .add 15 15 0x001#12
  | 1012 => .opImmWord .add 14 15 0x000#12
  | 1016 => .branch .blt 14 13 0x0158#13
  | 1020 => .load .dword true 28 2 0x008#12
  | 1024 => .opImm .add 6 12 0x000#12
  | 1028 => .opImm .add 11 0 0x001#12
  | 1032 => .opImmWord .add 17 11 0x000#12
  | 1036 => .branch .bge 17 13 0x1e60#13
  | 1040 => .opImm .sll 15 11 0x002#12
  | 1044 => .op .add 15 9 15
  | 1048 => .load .word true 15 15 0x000#12
  | 1052 => .op .div 29 28 15
  | 1056 => .op .div 15 29 15
  | 1060 => .opImm .add 15 15 0xfff#12
  | 1064 => .opImm .sra 15 15 0x001#12
  | 1068 => .opImm .sll 15 15 0x002#12
  | 1072 => .op .add 15 8 15
  | 1076 => .load .word true 14 15 0x000#12
  | 1080 => .opWord .sub 30 14 12
  | 1084 => .opImm .add 14 30 0x000#12
  | 1088 => .branch .bge 17 30 0x1e2c#13
  | 1092 => .opImm .add 11 11 0x001#12
  | 1096 => .opImm .add 16 11 0x000#12
  | 1100 => .opImmWord .add 15 16 0x000#12
  | 1104 => .branch .bge 30 15 0x0114#13
  | 1108 => .opWord .sub 14 14 17
  | 1112 => .op .mul 14 14 6
  | 1116 => .opImm .add 6 6 0x001#12
  | 1120 => .op .sub 10 10 14
  | 1124 => .jal 0 0x1fffa4#21
  | 1128 => .op .divu 14 10 15
  | 1132 => .opImm .add 11 15 0x000#12
  | 1136 => .op .add 14 14 15
  | 1140 => .opImm .srl 15 14 0x001#12
  | 1144 => .jal 0 0x1ffe2c#21
  | 1148 => .op .divu 14 11 15
  | 1152 => .opImm .add 19 15 0x000#12
  | 1156 => .op .add 14 14 15
  | 1160 => .opImm .srl 15 14 0x001#12
  | 1164 => .jal 0 0x1ffe30#21
  | 1168 => .opImm .sll 15 14 0x002#12
  | 1172 => .op .add 11 8 15
  | 1176 => .store .word 12 11 0x000#12
  | 1180 => .op .add 15 9 15
  | 1184 => .store .word 13 15 0x000#12
  | 1188 => .load .dword true 15 2 0x008#12
  | 1192 => .opImm .sll 12 14 0x003#12
  | 1196 => .op .add 12 18 12
  | 1200 => .op .div 15 15 13
  | 1204 => .opImm .add 14 14 0x001#12
  | 1208 => .opImm .add 13 13 0x002#12
  | 1212 => .opImm .add 15 15 0xfff#12
  | 1216 => .opImm .sra 15 15 0x001#12
  | 1220 => .store .dword 15 12 0x000#12
  | 1224 => .jal 0 0x1ffea4#21
  | 1228 => .opImm .add 22 2 0x040#12
  | 1232 => .opImm .add 11 0 0x003#12
  | 1236 => .opImm .add 10 22 0x000#12
  | 1240 => .auipc 1 0x00000#20
  | 1244 => .jalr 1 1 0xb4c#12
  | 1248 => .load .word true 14 2 0x014#12
  | 1252 => .opImm .add 15 0 0x018#12
  | 1256 => .branch .bge 15 14 0x1ed4#13
  | 1260 => .opImm .add 11 0 0x005#12
  | 1264 => .opImm .add 10 22 0x000#12
  | 1268 => .opImmWord .add 19 19 0x000#12
  | 1272 => .auipc 1 0x00000#20
  | 1276 => .jalr 1 1 0xb2c#12
  | 1280 => .opImm .add 21 0 0x000#12
  | 1284 => .opImm .add 20 0 0x007#12
  | 1288 => .auipc 23 0x00000#20
  | 1292 => .opImm .add 23 23 0x0c0#12
  | 1296 => .branch .blt 19 20 0x1eac#13
  | 1300 => .load .dword true 15 2 0x030#12
  | 1304 => .op .add 15 15 20
  | 1308 => .load .byte false 15 15 0x000#12
  | 1312 => .branch .bne 15 0 0x0014#13
  | 1316 => .opImm .add 11 20 0x000#12
  | 1320 => .opImm .add 10 22 0x000#12
  | 1324 => .auipc 1 0x00000#20
  | 1328 => .jalr 1 1 0xaf8#12
  | 1332 => .opImm .and 15 21 0x007#12
  | 1336 => .opImm .sll 15 15 0x002#12
  | 1340 => .op .add 15 23 15
  | 1344 => .load .word true 15 15 0x000#12
  | 1348 => .opImmWord .add 21 21 0x001#12
  | 1352 => .opWord .add 20 15 20
  | 1356 => .jal 0 0x1fffc4#21
  | 1360 => .opImm .sll 14 15 0x003#12
  | 1364 => .op .add 14 18 14
  | 1368 => .load .dword true 14 14 0x000#12
  | 1372 => .op .sub 10 10 14
  | 1376 => .jal 0 0x1ffe90#21
  | 1380 => .opImm .sll 15 16 0x002#12
  | 1384 => .op .add 15 9 15
  | 1388 => .load .word true 15 15 0x000#12
  | 1392 => .opImm .add 16 16 0x001#12
  | 1396 => .op .div 15 29 15
  | 1400 => .opImm .add 15 15 0xfff#12
  | 1404 => .opImm .sra 15 15 0x001#12
  | 1408 => .opImm .sll 15 15 0x002#12
  | 1412 => .op .add 15 8 15
  | 1416 => .load .word true 15 15 0x000#12
  | 1420 => .op .add 10 10 15
  | 1424 => .jal 0 0x1ffebc#21
  | 1428 => .auipc 14 0x00000#20
  | 1432 => .opImm .add 14 14 0x054#12
  | 1436 => .load .dword true 15 14 0x000#12
  | 1440 => .opImm .sll 12 11 0x002#12
  | 1444 => .opImm .add 11 0 0x000#12
  | 1448 => .opImm .add 15 15 0x007#12
  | 1452 => .opImm .and 15 15 0xff8#12
  | 1456 => .store .dword 15 10 0x000#12
  | 1460 => .op .add 13 15 12
  | 1464 => .opImm .add 10 15 0x000#12
  | 1468 => .store .dword 13 14 0x000#12
  | 1472 => .auipc 6 0x00000#20
  | 1476 => .jalr 0 6 0xc3c#12
  | _ => .ecall

/-! One rewrite rule per address, for symbolic execution. -/

@[gfetch] theorem instrAt_0 : instrAt 0 = .lui 2 0x00400#20 := rfl
@[gfetch] theorem instrAt_4 : instrAt 4 = .jal 1 0x000214#21 := rfl
@[gfetch] theorem instrAt_8 : instrAt 8 = .opImm .add 17 0 0x001#12 := rfl
@[gfetch] theorem instrAt_12 : instrAt 12 = .ecall := rfl
@[gfetch] theorem instrAt_16 : instrAt 16 = .opImm .add 10 0 0x00a#12 := rfl
@[gfetch] theorem instrAt_20 : instrAt 20 = .opImm .add 17 0 0x00b#12 := rfl
@[gfetch] theorem instrAt_24 : instrAt 24 = .ecall := rfl
@[gfetch] theorem instrAt_28 : instrAt 28 = .opImm .add 17 0 0x00a#12 := rfl
@[gfetch] theorem instrAt_32 : instrAt 32 = .ecall := rfl
@[gfetch] theorem instrAt_36 : instrAt 36 = .load .dword true 15 10 0x000#12 := rfl
@[gfetch] theorem instrAt_40 : instrAt 40 = .opImm .add 2 2 0xff0#12 := rfl
@[gfetch] theorem instrAt_44 : instrAt 44 = .opImm .add 14 0 0x001#12 := rfl
@[gfetch] theorem instrAt_48 : instrAt 48 = .load .dword true 31 15 0x000#12 := rfl
@[gfetch] theorem instrAt_52 : instrAt 52 = .store .dword 8 2 0x008#12 := rfl
@[gfetch] theorem instrAt_56 : instrAt 56 = .load .dword true 30 10 0x008#12 := rfl
@[gfetch] theorem instrAt_60 : instrAt 60 = .op .add 15 31 11 := rfl
@[gfetch] theorem instrAt_64 : instrAt 64 = .store .byte 14 15 0x000#12 := rfl
@[gfetch] theorem instrAt_68 : instrAt 68 = .opWord .mul 15 11 11 := rfl
@[gfetch] theorem instrAt_72 : instrAt 72 = .load .word true 12 30 0x000#12 := rfl
@[gfetch] theorem instrAt_76 : instrAt 76 = .opImmWord .sll 14 11 0x001#12 := rfl
@[gfetch] theorem instrAt_80 : instrAt 80 = .opImm .add 16 0 0x001#12 := rfl
@[gfetch] theorem instrAt_84 : instrAt 84 = .opImmWord .add 13 15 0x000#12 := rfl
@[gfetch] theorem instrAt_88 : instrAt 88 = .branch .bge 12 13 0x0068#13 := rfl
@[gfetch] theorem instrAt_92 : instrAt 92 = .load .dword true 7 10 0x010#12 := rfl
@[gfetch] theorem instrAt_96 : instrAt 96 = .load .dword true 28 10 0x030#12 := rfl
@[gfetch] theorem instrAt_100 : instrAt 100 = .opImm .add 16 0 0x000#12 := rfl
@[gfetch] theorem instrAt_104 : instrAt 104 = .opImm .add 12 0 0x000#12 := rfl
@[gfetch] theorem instrAt_108 : instrAt 108 = .load .word true 14 7 0x000#12 := rfl
@[gfetch] theorem instrAt_112 : instrAt 112 = .opImmWord .add 15 16 0x000#12 := rfl
@[gfetch] theorem instrAt_116 : instrAt 116 = .branch .blt 15 14 0x005c#13 := rfl
@[gfetch] theorem instrAt_120 : instrAt 120 = .store .word 12 7 0x000#12 := rfl
@[gfetch] theorem instrAt_124 : instrAt 124 = .load .word true 15 30 0x000#12 := rfl
@[gfetch] theorem instrAt_128 : instrAt 128 = .opImm .add 17 0 0xffe#12 := rfl
@[gfetch] theorem instrAt_132 : instrAt 132 = .opWord .mul 17 17 11 := rfl
@[gfetch] theorem instrAt_136 : instrAt 136 = .opImmWord .add 14 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_140 : instrAt 140 = .opImmWord .sra 14 14 0x001#12 := rfl
@[gfetch] theorem instrAt_144 : instrAt 144 = .opWord .div 15 15 11 := rfl
@[gfetch] theorem instrAt_148 : instrAt 148 = .opImmWord .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_152 : instrAt 152 = .opImm .or 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_156 : instrAt 156 = .opImmWord .add 16 15 0x000#12 := rfl
@[gfetch] theorem instrAt_160 : instrAt 160 = .opWord .mul 15 15 11 := rfl
@[gfetch] theorem instrAt_164 : instrAt 164 = .load .word true 12 28 0x000#12 := rfl
@[gfetch] theorem instrAt_168 : instrAt 168 = .branch .bge 16 11 0x00e4#13 := rfl
@[gfetch] theorem instrAt_172 : instrAt 172 = .load .dword true 8 2 0x008#12 := rfl
@[gfetch] theorem instrAt_176 : instrAt 176 = .opImmWord .add 12 12 0x001#12 := rfl
@[gfetch] theorem instrAt_180 : instrAt 180 = .store .word 12 28 0x000#12 := rfl
@[gfetch] theorem instrAt_184 : instrAt 184 = .opImm .add 2 2 0x010#12 := rfl
@[gfetch] theorem instrAt_188 : instrAt 188 = .jalr 0 1 0x000#12 := rfl
@[gfetch] theorem instrAt_192 : instrAt 192 = .op .add 13 31 15 := rfl
@[gfetch] theorem instrAt_196 : instrAt 196 = .store .byte 16 13 0x000#12 := rfl
@[gfetch] theorem instrAt_200 : instrAt 200 = .op .add 15 15 14 := rfl
@[gfetch] theorem instrAt_204 : instrAt 204 = .jal 0 0x1fff88#21 := rfl
@[gfetch] theorem instrAt_208 : instrAt 208 = .load .dword true 15 10 0x018#12 := rfl
@[gfetch] theorem instrAt_212 : instrAt 212 = .load .dword true 29 15 0x000#12 := rfl
@[gfetch] theorem instrAt_216 : instrAt 216 = .opImm .sll 15 16 0x002#12 := rfl
@[gfetch] theorem instrAt_220 : instrAt 220 = .op .add 15 29 15 := rfl
@[gfetch] theorem instrAt_224 : instrAt 224 = .load .word true 5 15 0x000#12 := rfl
@[gfetch] theorem instrAt_228 : instrAt 228 = .op .add 15 31 5 := rfl
@[gfetch] theorem instrAt_232 : instrAt 232 = .load .byte false 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_236 : instrAt 236 = .branch .bne 15 0 0x0074#13 := rfl
@[gfetch] theorem instrAt_240 : instrAt 240 = .load .dword true 15 10 0x020#12 := rfl
@[gfetch] theorem instrAt_244 : instrAt 244 = .op .mul 14 5 11 := rfl
@[gfetch] theorem instrAt_248 : instrAt 248 = .load .word true 8 28 0x000#12 := rfl
@[gfetch] theorem instrAt_252 : instrAt 252 = .load .dword true 17 15 0x000#12 := rfl
@[gfetch] theorem instrAt_256 : instrAt 256 = .opImm .sll 15 16 0x003#12 := rfl
@[gfetch] theorem instrAt_260 : instrAt 260 = .op .add 15 17 15 := rfl
@[gfetch] theorem instrAt_264 : instrAt 264 = .load .dword true 6 15 0x000#12 := rfl
@[gfetch] theorem instrAt_268 : instrAt 268 = .load .dword true 15 10 0x028#12 := rfl
@[gfetch] theorem instrAt_272 : instrAt 272 = .load .dword true 13 15 0x000#12 := rfl
@[gfetch] theorem instrAt_276 : instrAt 276 = .load .word true 15 30 0x000#12 := rfl
@[gfetch] theorem instrAt_280 : instrAt 280 = .branch .blt 15 14 0x0050#13 := rfl
@[gfetch] theorem instrAt_284 : instrAt 284 = .opImm .sra 14 14 0x001#12 := rfl
@[gfetch] theorem instrAt_288 : instrAt 288 = .opImm .sll 14 14 0x002#12 := rfl
@[gfetch] theorem instrAt_292 : instrAt 292 = .op .add 13 13 14 := rfl
@[gfetch] theorem instrAt_296 : instrAt 296 = .load .word true 15 13 0x000#12 := rfl
@[gfetch] theorem instrAt_300 : instrAt 300 = .opWord .sub 15 15 8 := rfl
@[gfetch] theorem instrAt_304 : instrAt 304 = .opImm .sll 15 15 0x003#12 := rfl
@[gfetch] theorem instrAt_308 : instrAt 308 = .op .add 15 17 15 := rfl
@[gfetch] theorem instrAt_312 : instrAt 312 = .load .dword true 14 15 0x000#12 := rfl
@[gfetch] theorem instrAt_316 : instrAt 316 = .opImm .sll 13 12 0x003#12 := rfl
@[gfetch] theorem instrAt_320 : instrAt 320 = .op .sub 6 6 14 := rfl
@[gfetch] theorem instrAt_324 : instrAt 324 = .opImm .sll 15 12 0x002#12 := rfl
@[gfetch] theorem instrAt_328 : instrAt 328 = .op .add 17 17 13 := rfl
@[gfetch] theorem instrAt_332 : instrAt 332 = .op .add 6 6 8 := rfl
@[gfetch] theorem instrAt_336 : instrAt 336 = .store .dword 6 17 0x000#12 := rfl
@[gfetch] theorem instrAt_340 : instrAt 340 = .op .add 29 29 15 := rfl
@[gfetch] theorem instrAt_344 : instrAt 344 = .opImmWord .add 12 12 0x001#12 := rfl
@[gfetch] theorem instrAt_348 : instrAt 348 = .store .word 5 29 0x000#12 := rfl
@[gfetch] theorem instrAt_352 : instrAt 352 = .opImm .add 16 16 0x001#12 := rfl
@[gfetch] theorem instrAt_356 : instrAt 356 = .jal 0 0x1fff08#21 := rfl
@[gfetch] theorem instrAt_360 : instrAt 360 = .load .dword true 15 10 0x038#12 := rfl
@[gfetch] theorem instrAt_364 : instrAt 364 = .load .dword true 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_368 : instrAt 368 = .op .div 15 15 14 := rfl
@[gfetch] theorem instrAt_372 : instrAt 372 = .opImm .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_376 : instrAt 376 = .opImm .sra 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_380 : instrAt 380 = .opImm .sll 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_384 : instrAt 384 = .op .add 13 13 15 := rfl
@[gfetch] theorem instrAt_388 : instrAt 388 = .load .word true 14 13 0x000#12 := rfl
@[gfetch] theorem instrAt_392 : instrAt 392 = .jal 0 0x1fffb4#21 := rfl
@[gfetch] theorem instrAt_396 : instrAt 396 = .load .dword true 13 10 0x028#12 := rfl
@[gfetch] theorem instrAt_400 : instrAt 400 = .opImmWord .sra 30 15 0x001#12 := rfl
@[gfetch] theorem instrAt_404 : instrAt 404 = .opImm .sra 5 15 0x001#12 := rfl
@[gfetch] theorem instrAt_408 : instrAt 408 = .load .dword true 31 13 0x000#12 := rfl
@[gfetch] theorem instrAt_412 : instrAt 412 = .opImm .sra 13 16 0x001#12 := rfl
@[gfetch] theorem instrAt_416 : instrAt 416 = .opImm .sll 13 13 0x002#12 := rfl
@[gfetch] theorem instrAt_420 : instrAt 420 = .op .add 13 31 13 := rfl
@[gfetch] theorem instrAt_424 : instrAt 424 = .load .word true 6 13 0x000#12 := rfl
@[gfetch] theorem instrAt_428 : instrAt 428 = .opImm .add 13 14 0x000#12 := rfl
@[gfetch] theorem instrAt_432 : instrAt 432 = .opWord .sub 6 6 12 := rfl
@[gfetch] theorem instrAt_436 : instrAt 436 = .opImmWord .add 12 13 0x000#12 := rfl
@[gfetch] theorem instrAt_440 : instrAt 440 = .branch .bge 12 5 0x0028#13 := rfl
@[gfetch] theorem instrAt_444 : instrAt 444 = .opImmWord .add 12 30 0xfff#12 := rfl
@[gfetch] theorem instrAt_448 : instrAt 448 = .opImm .add 13 0 0x000#12 := rfl
@[gfetch] theorem instrAt_452 : instrAt 452 = .branch .blt 14 12 0x000c#13 := rfl
@[gfetch] theorem instrAt_456 : instrAt 456 = .opImmWord .add 13 14 0x001#12 := rfl
@[gfetch] theorem instrAt_460 : instrAt 460 = .opWord .sub 13 30 13 := rfl
@[gfetch] theorem instrAt_464 : instrAt 464 = .opWord .add 14 13 14 := rfl
@[gfetch] theorem instrAt_468 : instrAt 468 = .opImmWord .add 16 16 0xffe#12 := rfl
@[gfetch] theorem instrAt_472 : instrAt 472 = .opWord .add 15 15 17 := rfl
@[gfetch] theorem instrAt_476 : instrAt 476 = .jal 0 0x1ffec8#21 := rfl
@[gfetch] theorem instrAt_480 : instrAt 480 = .opImm .sll 12 13 0x002#12 := rfl
@[gfetch] theorem instrAt_484 : instrAt 484 = .op .add 12 31 12 := rfl
@[gfetch] theorem instrAt_488 : instrAt 488 = .load .word true 29 12 0x000#12 := rfl
@[gfetch] theorem instrAt_492 : instrAt 492 = .opImm .add 13 13 0xfff#12 := rfl
@[gfetch] theorem instrAt_496 : instrAt 496 = .opWord .sub 29 29 6 := rfl
@[gfetch] theorem instrAt_500 : instrAt 500 = .store .word 29 12 0x000#12 := rfl
@[gfetch] theorem instrAt_504 : instrAt 504 = .jal 0 0x1fffbc#21 := rfl
@[gfetch] theorem instrAt_508 : instrAt 508 = .op .add 12 10 12 := rfl
@[gfetch] theorem instrAt_512 : instrAt 512 = .opImm .add 15 10 0x000#12 := rfl
@[gfetch] theorem instrAt_516 : instrAt 516 = .branch .bne 15 12 0x0008#13 := rfl
@[gfetch] theorem instrAt_520 : instrAt 520 = .jalr 0 1 0x000#12 := rfl
@[gfetch] theorem instrAt_524 : instrAt 524 = .opImm .add 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_528 : instrAt 528 = .store .byte 11 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_532 : instrAt 532 = .jal 0 0x1ffff0#21 := rfl
@[gfetch] theorem instrAt_536 : instrAt 536 = .opImm .add 2 2 0xf30#12 := rfl
@[gfetch] theorem instrAt_540 : instrAt 540 = .store .dword 1 2 0x0c8#12 := rfl
@[gfetch] theorem instrAt_544 : instrAt 544 = .store .dword 8 2 0x0c0#12 := rfl
@[gfetch] theorem instrAt_548 : instrAt 548 = .store .dword 9 2 0x0b8#12 := rfl
@[gfetch] theorem instrAt_552 : instrAt 552 = .store .dword 18 2 0x0b0#12 := rfl
@[gfetch] theorem instrAt_556 : instrAt 556 = .store .dword 19 2 0x0a8#12 := rfl
@[gfetch] theorem instrAt_560 : instrAt 560 = .store .dword 20 2 0x0a0#12 := rfl
@[gfetch] theorem instrAt_564 : instrAt 564 = .store .dword 21 2 0x098#12 := rfl
@[gfetch] theorem instrAt_568 : instrAt 568 = .store .dword 22 2 0x090#12 := rfl
@[gfetch] theorem instrAt_572 : instrAt 572 = .store .dword 23 2 0x088#12 := rfl
@[gfetch] theorem instrAt_576 : instrAt 576 = .store .dword 10 2 0x008#12 := rfl
@[gfetch] theorem instrAt_580 : instrAt 580 = .opImm .add 15 0 0x006#12 := rfl
@[gfetch] theorem instrAt_584 : instrAt 584 = .branch .blt 15 10 0x0050#13 := rfl
@[gfetch] theorem instrAt_588 : instrAt 588 = .opImm .slt 15 10 0x002#12 := rfl
@[gfetch] theorem instrAt_592 : instrAt 592 = .opImm .slt 14 10 0x003#12 := rfl
@[gfetch] theorem instrAt_596 : instrAt 596 = .opImm .sltu 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_600 : instrAt 600 = .opImm .sltu 14 14 0x001#12 := rfl
@[gfetch] theorem instrAt_604 : instrAt 604 = .opImm .slt 10 10 0x005#12 := rfl
@[gfetch] theorem instrAt_608 : instrAt 608 = .opWord .add 15 15 14 := rfl
@[gfetch] theorem instrAt_612 : instrAt 612 = .opImm .sltu 10 10 0x001#12 := rfl
@[gfetch] theorem instrAt_616 : instrAt 616 = .opWord .add 10 15 10 := rfl
@[gfetch] theorem instrAt_620 : instrAt 620 = .load .dword true 1 2 0x0c8#12 := rfl
@[gfetch] theorem instrAt_624 : instrAt 624 = .load .dword true 8 2 0x0c0#12 := rfl
@[gfetch] theorem instrAt_628 : instrAt 628 = .load .dword true 9 2 0x0b8#12 := rfl
@[gfetch] theorem instrAt_632 : instrAt 632 = .load .dword true 18 2 0x0b0#12 := rfl
@[gfetch] theorem instrAt_636 : instrAt 636 = .load .dword true 19 2 0x0a8#12 := rfl
@[gfetch] theorem instrAt_640 : instrAt 640 = .load .dword true 20 2 0x0a0#12 := rfl
@[gfetch] theorem instrAt_644 : instrAt 644 = .load .dword true 21 2 0x098#12 := rfl
@[gfetch] theorem instrAt_648 : instrAt 648 = .load .dword true 22 2 0x090#12 := rfl
@[gfetch] theorem instrAt_652 : instrAt 652 = .load .dword true 23 2 0x088#12 := rfl
@[gfetch] theorem instrAt_656 : instrAt 656 = .opImm .add 2 2 0x0d0#12 := rfl
@[gfetch] theorem instrAt_660 : instrAt 660 = .jalr 0 1 0x000#12 := rfl
@[gfetch] theorem instrAt_664 : instrAt 664 = .opImm .add 15 10 0x001#12 := rfl
@[gfetch] theorem instrAt_668 : instrAt 668 = .opImm .srl 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_672 : instrAt 672 = .opImm .add 11 10 0x000#12 := rfl
@[gfetch] theorem instrAt_676 : instrAt 676 = .branch .bltu 15 11 0x01c4#13 := rfl
@[gfetch] theorem instrAt_680 : instrAt 680 = .opImmWord .add 11 11 0x000#12 := rfl
@[gfetch] theorem instrAt_684 : instrAt 684 = .opImm .add 15 11 0x001#12 := rfl
@[gfetch] theorem instrAt_688 : instrAt 688 = .store .word 11 2 0x014#12 := rfl
@[gfetch] theorem instrAt_692 : instrAt 692 = .opImm .srl 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_696 : instrAt 696 = .opImm .add 19 11 0x000#12 := rfl
@[gfetch] theorem instrAt_700 : instrAt 700 = .branch .bltu 15 19 0x01c0#13 := rfl
@[gfetch] theorem instrAt_704 : instrAt 704 = .opImm .add 15 0 0x002#12 := rfl
@[gfetch] theorem instrAt_708 : instrAt 708 = .opImmWord .add 11 11 0x001#12 := rfl
@[gfetch] theorem instrAt_712 : instrAt 712 = .opWord .div 11 11 15 := rfl
@[gfetch] theorem instrAt_716 : instrAt 716 = .opImm .add 20 2 0x020#12 := rfl
@[gfetch] theorem instrAt_720 : instrAt 720 = .opImm .add 10 20 0x000#12 := rfl
@[gfetch] theorem instrAt_724 : instrAt 724 = .store .word 0 2 0x018#12 := rfl
@[gfetch] theorem instrAt_728 : instrAt 728 = .opImm .add 21 2 0x028#12 := rfl
@[gfetch] theorem instrAt_732 : instrAt 732 = .auipc 18 0x00000#20 := rfl
@[gfetch] theorem instrAt_736 : instrAt 736 = .opImm .add 18 18 0x30c#12 := rfl
@[gfetch] theorem instrAt_740 : instrAt 740 = .store .word 11 2 0x01c#12 := rfl
@[gfetch] theorem instrAt_744 : instrAt 744 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_748 : instrAt 748 = .jalr 1 1 0x2ac#12 := rfl
@[gfetch] theorem instrAt_752 : instrAt 752 = .load .word true 11 2 0x01c#12 := rfl
@[gfetch] theorem instrAt_756 : instrAt 756 = .opImm .add 10 21 0x000#12 := rfl
@[gfetch] theorem instrAt_760 : instrAt 760 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_764 : instrAt 764 = .jalr 1 1 0x29c#12 := rfl
@[gfetch] theorem instrAt_768 : instrAt 768 = .load .dword true 8 18 0x000#12 := rfl
@[gfetch] theorem instrAt_772 : instrAt 772 = .load .word true 9 2 0x014#12 := rfl
@[gfetch] theorem instrAt_776 : instrAt 776 = .opImm .add 11 0 0x000#12 := rfl
@[gfetch] theorem instrAt_780 : instrAt 780 = .opImm .add 8 8 0x007#12 := rfl
@[gfetch] theorem instrAt_784 : instrAt 784 = .opImm .and 8 8 0xff8#12 := rfl
@[gfetch] theorem instrAt_788 : instrAt 788 = .opImmWord .add 9 9 0x001#12 := rfl
@[gfetch] theorem instrAt_792 : instrAt 792 = .opImm .add 12 9 0x000#12 := rfl
@[gfetch] theorem instrAt_796 : instrAt 796 = .opImm .add 10 8 0x000#12 := rfl
@[gfetch] theorem instrAt_800 : instrAt 800 = .store .dword 8 2 0x030#12 := rfl
@[gfetch] theorem instrAt_804 : instrAt 804 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_808 : instrAt 808 = .jalr 1 1 0xed8#12 := rfl
@[gfetch] theorem instrAt_812 : instrAt 812 = .load .word true 12 2 0x01c#12 := rfl
@[gfetch] theorem instrAt_816 : instrAt 816 = .opImm .add 9 9 0x007#12 := rfl
@[gfetch] theorem instrAt_820 : instrAt 820 = .op .add 10 8 9 := rfl
@[gfetch] theorem instrAt_824 : instrAt 824 = .opImm .and 10 10 0xff8#12 := rfl
@[gfetch] theorem instrAt_828 : instrAt 828 = .opImm .sll 12 12 0x003#12 := rfl
@[gfetch] theorem instrAt_832 : instrAt 832 = .op .add 15 10 12 := rfl
@[gfetch] theorem instrAt_836 : instrAt 836 = .opImm .add 11 0 0x000#12 := rfl
@[gfetch] theorem instrAt_840 : instrAt 840 = .store .dword 15 18 0x000#12 := rfl
@[gfetch] theorem instrAt_844 : instrAt 844 = .store .dword 10 2 0x038#12 := rfl
@[gfetch] theorem instrAt_848 : instrAt 848 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_852 : instrAt 852 = .jalr 1 1 0xeac#12 := rfl
@[gfetch] theorem instrAt_856 : instrAt 856 = .load .dword true 8 2 0x020#12 := rfl
@[gfetch] theorem instrAt_860 : instrAt 860 = .load .dword true 9 2 0x028#12 := rfl
@[gfetch] theorem instrAt_864 : instrAt 864 = .load .dword true 18 2 0x038#12 := rfl
@[gfetch] theorem instrAt_868 : instrAt 868 = .opImm .add 13 0 0x001#12 := rfl
@[gfetch] theorem instrAt_872 : instrAt 872 = .opImm .add 14 0 0x000#12 := rfl
@[gfetch] theorem instrAt_876 : instrAt 876 = .load .word true 15 2 0x01c#12 := rfl
@[gfetch] theorem instrAt_880 : instrAt 880 = .opImmWord .add 12 14 0x000#12 := rfl
@[gfetch] theorem instrAt_884 : instrAt 884 = .branch .blt 12 15 0x011c#13 := rfl
@[gfetch] theorem instrAt_888 : instrAt 888 = .opImm .add 15 2 0x030#12 := rfl
@[gfetch] theorem instrAt_892 : instrAt 892 = .store .dword 15 2 0x040#12 := rfl
@[gfetch] theorem instrAt_896 : instrAt 896 = .opImm .add 15 2 0x014#12 := rfl
@[gfetch] theorem instrAt_900 : instrAt 900 = .store .dword 15 2 0x048#12 := rfl
@[gfetch] theorem instrAt_904 : instrAt 904 = .opImm .add 15 2 0x01c#12 := rfl
@[gfetch] theorem instrAt_908 : instrAt 908 = .store .dword 15 2 0x050#12 := rfl
@[gfetch] theorem instrAt_912 : instrAt 912 = .opImm .add 15 2 0x038#12 := rfl
@[gfetch] theorem instrAt_916 : instrAt 916 = .store .dword 15 2 0x060#12 := rfl
@[gfetch] theorem instrAt_920 : instrAt 920 = .load .word true 14 2 0x014#12 := rfl
@[gfetch] theorem instrAt_924 : instrAt 924 = .opImm .add 15 2 0x018#12 := rfl
@[gfetch] theorem instrAt_928 : instrAt 928 = .store .dword 15 2 0x070#12 := rfl
@[gfetch] theorem instrAt_932 : instrAt 932 = .opImm .add 15 2 0x008#12 := rfl
@[gfetch] theorem instrAt_936 : instrAt 936 = .store .dword 15 2 0x078#12 := rfl
@[gfetch] theorem instrAt_940 : instrAt 940 = .store .dword 21 2 0x058#12 := rfl
@[gfetch] theorem instrAt_944 : instrAt 944 = .store .dword 20 2 0x068#12 := rfl
@[gfetch] theorem instrAt_948 : instrAt 948 = .opImm .add 15 0 0x008#12 := rfl
@[gfetch] theorem instrAt_952 : instrAt 952 = .branch .blt 15 14 0x0114#13 := rfl
@[gfetch] theorem instrAt_956 : instrAt 956 = .load .word true 13 2 0x01c#12 := rfl
@[gfetch] theorem instrAt_960 : instrAt 960 = .load .word true 12 2 0x018#12 := rfl
@[gfetch] theorem instrAt_964 : instrAt 964 = .opImm .add 15 13 0xfff#12 := rfl
@[gfetch] theorem instrAt_968 : instrAt 968 = .opWord .add 10 13 12 := rfl
@[gfetch] theorem instrAt_972 : instrAt 972 = .opWord .add 10 10 12 := rfl
@[gfetch] theorem instrAt_976 : instrAt 976 = .opImmWord .add 10 10 0xffe#12 := rfl
@[gfetch] theorem instrAt_980 : instrAt 980 = .op .mul 10 10 15 := rfl
@[gfetch] theorem instrAt_984 : instrAt 984 = .opImm .add 15 0 0x002#12 := rfl
@[gfetch] theorem instrAt_988 : instrAt 988 = .op .div 10 10 15 := rfl
@[gfetch] theorem instrAt_992 : instrAt 992 = .load .dword true 15 18 0x000#12 := rfl
@[gfetch] theorem instrAt_996 : instrAt 996 = .opImm .add 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_1000 : instrAt 1000 = .op .add 10 10 15 := rfl
@[gfetch] theorem instrAt_1004 : instrAt 1004 = .opImm .add 15 0 0x000#12 := rfl
@[gfetch] theorem instrAt_1008 : instrAt 1008 = .opImm .add 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_1012 : instrAt 1012 = .opImmWord .add 14 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1016 : instrAt 1016 = .branch .blt 14 13 0x0158#13 := rfl
@[gfetch] theorem instrAt_1020 : instrAt 1020 = .load .dword true 28 2 0x008#12 := rfl
@[gfetch] theorem instrAt_1024 : instrAt 1024 = .opImm .add 6 12 0x000#12 := rfl
@[gfetch] theorem instrAt_1028 : instrAt 1028 = .opImm .add 11 0 0x001#12 := rfl
@[gfetch] theorem instrAt_1032 : instrAt 1032 = .opImmWord .add 17 11 0x000#12 := rfl
@[gfetch] theorem instrAt_1036 : instrAt 1036 = .branch .bge 17 13 0x1e60#13 := rfl
@[gfetch] theorem instrAt_1040 : instrAt 1040 = .opImm .sll 15 11 0x002#12 := rfl
@[gfetch] theorem instrAt_1044 : instrAt 1044 = .op .add 15 9 15 := rfl
@[gfetch] theorem instrAt_1048 : instrAt 1048 = .load .word true 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1052 : instrAt 1052 = .op .div 29 28 15 := rfl
@[gfetch] theorem instrAt_1056 : instrAt 1056 = .op .div 15 29 15 := rfl
@[gfetch] theorem instrAt_1060 : instrAt 1060 = .opImm .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_1064 : instrAt 1064 = .opImm .sra 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_1068 : instrAt 1068 = .opImm .sll 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_1072 : instrAt 1072 = .op .add 15 8 15 := rfl
@[gfetch] theorem instrAt_1076 : instrAt 1076 = .load .word true 14 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1080 : instrAt 1080 = .opWord .sub 30 14 12 := rfl
@[gfetch] theorem instrAt_1084 : instrAt 1084 = .opImm .add 14 30 0x000#12 := rfl
@[gfetch] theorem instrAt_1088 : instrAt 1088 = .branch .bge 17 30 0x1e2c#13 := rfl
@[gfetch] theorem instrAt_1092 : instrAt 1092 = .opImm .add 11 11 0x001#12 := rfl
@[gfetch] theorem instrAt_1096 : instrAt 1096 = .opImm .add 16 11 0x000#12 := rfl
@[gfetch] theorem instrAt_1100 : instrAt 1100 = .opImmWord .add 15 16 0x000#12 := rfl
@[gfetch] theorem instrAt_1104 : instrAt 1104 = .branch .bge 30 15 0x0114#13 := rfl
@[gfetch] theorem instrAt_1108 : instrAt 1108 = .opWord .sub 14 14 17 := rfl
@[gfetch] theorem instrAt_1112 : instrAt 1112 = .op .mul 14 14 6 := rfl
@[gfetch] theorem instrAt_1116 : instrAt 1116 = .opImm .add 6 6 0x001#12 := rfl
@[gfetch] theorem instrAt_1120 : instrAt 1120 = .op .sub 10 10 14 := rfl
@[gfetch] theorem instrAt_1124 : instrAt 1124 = .jal 0 0x1fffa4#21 := rfl
@[gfetch] theorem instrAt_1128 : instrAt 1128 = .op .divu 14 10 15 := rfl
@[gfetch] theorem instrAt_1132 : instrAt 1132 = .opImm .add 11 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1136 : instrAt 1136 = .op .add 14 14 15 := rfl
@[gfetch] theorem instrAt_1140 : instrAt 1140 = .opImm .srl 15 14 0x001#12 := rfl
@[gfetch] theorem instrAt_1144 : instrAt 1144 = .jal 0 0x1ffe2c#21 := rfl
@[gfetch] theorem instrAt_1148 : instrAt 1148 = .op .divu 14 11 15 := rfl
@[gfetch] theorem instrAt_1152 : instrAt 1152 = .opImm .add 19 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1156 : instrAt 1156 = .op .add 14 14 15 := rfl
@[gfetch] theorem instrAt_1160 : instrAt 1160 = .opImm .srl 15 14 0x001#12 := rfl
@[gfetch] theorem instrAt_1164 : instrAt 1164 = .jal 0 0x1ffe30#21 := rfl
@[gfetch] theorem instrAt_1168 : instrAt 1168 = .opImm .sll 15 14 0x002#12 := rfl
@[gfetch] theorem instrAt_1172 : instrAt 1172 = .op .add 11 8 15 := rfl
@[gfetch] theorem instrAt_1176 : instrAt 1176 = .store .word 12 11 0x000#12 := rfl
@[gfetch] theorem instrAt_1180 : instrAt 1180 = .op .add 15 9 15 := rfl
@[gfetch] theorem instrAt_1184 : instrAt 1184 = .store .word 13 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1188 : instrAt 1188 = .load .dword true 15 2 0x008#12 := rfl
@[gfetch] theorem instrAt_1192 : instrAt 1192 = .opImm .sll 12 14 0x003#12 := rfl
@[gfetch] theorem instrAt_1196 : instrAt 1196 = .op .add 12 18 12 := rfl
@[gfetch] theorem instrAt_1200 : instrAt 1200 = .op .div 15 15 13 := rfl
@[gfetch] theorem instrAt_1204 : instrAt 1204 = .opImm .add 14 14 0x001#12 := rfl
@[gfetch] theorem instrAt_1208 : instrAt 1208 = .opImm .add 13 13 0x002#12 := rfl
@[gfetch] theorem instrAt_1212 : instrAt 1212 = .opImm .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_1216 : instrAt 1216 = .opImm .sra 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_1220 : instrAt 1220 = .store .dword 15 12 0x000#12 := rfl
@[gfetch] theorem instrAt_1224 : instrAt 1224 = .jal 0 0x1ffea4#21 := rfl
@[gfetch] theorem instrAt_1228 : instrAt 1228 = .opImm .add 22 2 0x040#12 := rfl
@[gfetch] theorem instrAt_1232 : instrAt 1232 = .opImm .add 11 0 0x003#12 := rfl
@[gfetch] theorem instrAt_1236 : instrAt 1236 = .opImm .add 10 22 0x000#12 := rfl
@[gfetch] theorem instrAt_1240 : instrAt 1240 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_1244 : instrAt 1244 = .jalr 1 1 0xb4c#12 := rfl
@[gfetch] theorem instrAt_1248 : instrAt 1248 = .load .word true 14 2 0x014#12 := rfl
@[gfetch] theorem instrAt_1252 : instrAt 1252 = .opImm .add 15 0 0x018#12 := rfl
@[gfetch] theorem instrAt_1256 : instrAt 1256 = .branch .bge 15 14 0x1ed4#13 := rfl
@[gfetch] theorem instrAt_1260 : instrAt 1260 = .opImm .add 11 0 0x005#12 := rfl
@[gfetch] theorem instrAt_1264 : instrAt 1264 = .opImm .add 10 22 0x000#12 := rfl
@[gfetch] theorem instrAt_1268 : instrAt 1268 = .opImmWord .add 19 19 0x000#12 := rfl
@[gfetch] theorem instrAt_1272 : instrAt 1272 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_1276 : instrAt 1276 = .jalr 1 1 0xb2c#12 := rfl
@[gfetch] theorem instrAt_1280 : instrAt 1280 = .opImm .add 21 0 0x000#12 := rfl
@[gfetch] theorem instrAt_1284 : instrAt 1284 = .opImm .add 20 0 0x007#12 := rfl
@[gfetch] theorem instrAt_1288 : instrAt 1288 = .auipc 23 0x00000#20 := rfl
@[gfetch] theorem instrAt_1292 : instrAt 1292 = .opImm .add 23 23 0x0c0#12 := rfl
@[gfetch] theorem instrAt_1296 : instrAt 1296 = .branch .blt 19 20 0x1eac#13 := rfl
@[gfetch] theorem instrAt_1300 : instrAt 1300 = .load .dword true 15 2 0x030#12 := rfl
@[gfetch] theorem instrAt_1304 : instrAt 1304 = .op .add 15 15 20 := rfl
@[gfetch] theorem instrAt_1308 : instrAt 1308 = .load .byte false 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1312 : instrAt 1312 = .branch .bne 15 0 0x0014#13 := rfl
@[gfetch] theorem instrAt_1316 : instrAt 1316 = .opImm .add 11 20 0x000#12 := rfl
@[gfetch] theorem instrAt_1320 : instrAt 1320 = .opImm .add 10 22 0x000#12 := rfl
@[gfetch] theorem instrAt_1324 : instrAt 1324 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_1328 : instrAt 1328 = .jalr 1 1 0xaf8#12 := rfl
@[gfetch] theorem instrAt_1332 : instrAt 1332 = .opImm .and 15 21 0x007#12 := rfl
@[gfetch] theorem instrAt_1336 : instrAt 1336 = .opImm .sll 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_1340 : instrAt 1340 = .op .add 15 23 15 := rfl
@[gfetch] theorem instrAt_1344 : instrAt 1344 = .load .word true 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1348 : instrAt 1348 = .opImmWord .add 21 21 0x001#12 := rfl
@[gfetch] theorem instrAt_1352 : instrAt 1352 = .opWord .add 20 15 20 := rfl
@[gfetch] theorem instrAt_1356 : instrAt 1356 = .jal 0 0x1fffc4#21 := rfl
@[gfetch] theorem instrAt_1360 : instrAt 1360 = .opImm .sll 14 15 0x003#12 := rfl
@[gfetch] theorem instrAt_1364 : instrAt 1364 = .op .add 14 18 14 := rfl
@[gfetch] theorem instrAt_1368 : instrAt 1368 = .load .dword true 14 14 0x000#12 := rfl
@[gfetch] theorem instrAt_1372 : instrAt 1372 = .op .sub 10 10 14 := rfl
@[gfetch] theorem instrAt_1376 : instrAt 1376 = .jal 0 0x1ffe90#21 := rfl
@[gfetch] theorem instrAt_1380 : instrAt 1380 = .opImm .sll 15 16 0x002#12 := rfl
@[gfetch] theorem instrAt_1384 : instrAt 1384 = .op .add 15 9 15 := rfl
@[gfetch] theorem instrAt_1388 : instrAt 1388 = .load .word true 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1392 : instrAt 1392 = .opImm .add 16 16 0x001#12 := rfl
@[gfetch] theorem instrAt_1396 : instrAt 1396 = .op .div 15 29 15 := rfl
@[gfetch] theorem instrAt_1400 : instrAt 1400 = .opImm .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_1404 : instrAt 1404 = .opImm .sra 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_1408 : instrAt 1408 = .opImm .sll 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_1412 : instrAt 1412 = .op .add 15 8 15 := rfl
@[gfetch] theorem instrAt_1416 : instrAt 1416 = .load .word true 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1420 : instrAt 1420 = .op .add 10 10 15 := rfl
@[gfetch] theorem instrAt_1424 : instrAt 1424 = .jal 0 0x1ffebc#21 := rfl
@[gfetch] theorem instrAt_1428 : instrAt 1428 = .auipc 14 0x00000#20 := rfl
@[gfetch] theorem instrAt_1432 : instrAt 1432 = .opImm .add 14 14 0x054#12 := rfl
@[gfetch] theorem instrAt_1436 : instrAt 1436 = .load .dword true 15 14 0x000#12 := rfl
@[gfetch] theorem instrAt_1440 : instrAt 1440 = .opImm .sll 12 11 0x002#12 := rfl
@[gfetch] theorem instrAt_1444 : instrAt 1444 = .opImm .add 11 0 0x000#12 := rfl
@[gfetch] theorem instrAt_1448 : instrAt 1448 = .opImm .add 15 15 0x007#12 := rfl
@[gfetch] theorem instrAt_1452 : instrAt 1452 = .opImm .and 15 15 0xff8#12 := rfl
@[gfetch] theorem instrAt_1456 : instrAt 1456 = .store .dword 15 10 0x000#12 := rfl
@[gfetch] theorem instrAt_1460 : instrAt 1460 = .op .add 13 15 12 := rfl
@[gfetch] theorem instrAt_1464 : instrAt 1464 = .opImm .add 10 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1468 : instrAt 1468 = .store .dword 13 14 0x000#12 := rfl
@[gfetch] theorem instrAt_1472 : instrAt 1472 = .auipc 6 0x00000#20 := rfl
@[gfetch] theorem instrAt_1476 : instrAt 1476 = .jalr 0 6 0xc3c#12 := rfl

/-! Sign extensions of the immediates not already in the shared `gfetch` set. -/

@[gfetch] theorem zsext_12_120 : BitVec.signExtend 64 (0x078#12) = 120#64 := by decide
@[gfetch] theorem zsext_12_136 : BitVec.signExtend 64 (0x088#12) = 136#64 := by decide
@[gfetch] theorem zsext_12_144 : BitVec.signExtend 64 (0x090#12) = 144#64 := by decide
@[gfetch] theorem zsext_12_152 : BitVec.signExtend 64 (0x098#12) = 152#64 := by decide
@[gfetch] theorem zsext_12_16 : BitVec.signExtend 64 (0x010#12) = 16#64 := by decide
@[gfetch] theorem zsext_12_160 : BitVec.signExtend 64 (0x0a0#12) = 160#64 := by decide
@[gfetch] theorem zsext_12_168 : BitVec.signExtend 64 (0x0a8#12) = 168#64 := by decide
@[gfetch] theorem zsext_12_176 : BitVec.signExtend 64 (0x0b0#12) = 176#64 := by decide
@[gfetch] theorem zsext_12_184 : BitVec.signExtend 64 (0x0b8#12) = 184#64 := by decide
@[gfetch] theorem zsext_12_192 : BitVec.signExtend 64 (0x0c0#12) = 192#64 := by decide
@[gfetch] theorem zsext_12_20 : BitVec.signExtend 64 (0x014#12) = 20#64 := by decide
@[gfetch] theorem zsext_12_200 : BitVec.signExtend 64 (0x0c8#12) = 200#64 := by decide
@[gfetch] theorem zsext_12_208 : BitVec.signExtend 64 (0x0d0#12) = 208#64 := by decide
@[gfetch] theorem zsext_12_28 : BitVec.signExtend 64 (0x01c#12) = 28#64 := by decide
@[gfetch] theorem zsext_12_2808 : BitVec.signExtend 64 (0xaf8#12) = 18446744073709550328#64 := by decide
@[gfetch] theorem zsext_12_2860 : BitVec.signExtend 64 (0xb2c#12) = 18446744073709550380#64 := by decide
@[gfetch] theorem zsext_12_2892 : BitVec.signExtend 64 (0xb4c#12) = 18446744073709550412#64 := by decide
@[gfetch] theorem zsext_12_3132 : BitVec.signExtend 64 (0xc3c#12) = 18446744073709550652#64 := by decide
@[gfetch] theorem zsext_12_3756 : BitVec.signExtend 64 (0xeac#12) = 18446744073709551276#64 := by decide
@[gfetch] theorem zsext_12_3800 : BitVec.signExtend 64 (0xed8#12) = 18446744073709551320#64 := by decide
@[gfetch] theorem zsext_12_3888 : BitVec.signExtend 64 (0xf30#12) = 18446744073709551408#64 := by decide
@[gfetch] theorem zsext_12_4080 : BitVec.signExtend 64 (0xff0#12) = 18446744073709551600#64 := by decide
@[gfetch] theorem zsext_12_4094 : BitVec.signExtend 64 (0xffe#12) = 18446744073709551614#64 := by decide
@[gfetch] theorem zsext_12_5 : BitVec.signExtend 64 (0x005#12) = 5#64 := by decide
@[gfetch] theorem zsext_12_6 : BitVec.signExtend 64 (0x006#12) = 6#64 := by decide
@[gfetch] theorem zsext_12_668 : BitVec.signExtend 64 (0x29c#12) = 668#64 := by decide
@[gfetch] theorem zsext_12_684 : BitVec.signExtend 64 (0x2ac#12) = 684#64 := by decide
@[gfetch] theorem zsext_12_780 : BitVec.signExtend 64 (0x30c#12) = 780#64 := by decide
@[gfetch] theorem zsext_12_84 : BitVec.signExtend 64 (0x054#12) = 84#64 := by decide
@[gfetch] theorem zsext_13_104 : BitVec.signExtend 64 (0x0068#13) = 104#64 := by decide
@[gfetch] theorem zsext_13_116 : BitVec.signExtend 64 (0x0074#13) = 116#64 := by decide
@[gfetch] theorem zsext_13_20 : BitVec.signExtend 64 (0x0014#13) = 20#64 := by decide
@[gfetch] theorem zsext_13_228 : BitVec.signExtend 64 (0x00e4#13) = 228#64 := by decide
@[gfetch] theorem zsext_13_276 : BitVec.signExtend 64 (0x0114#13) = 276#64 := by decide
@[gfetch] theorem zsext_13_284 : BitVec.signExtend 64 (0x011c#13) = 284#64 := by decide
@[gfetch] theorem zsext_13_344 : BitVec.signExtend 64 (0x0158#13) = 344#64 := by decide
@[gfetch] theorem zsext_13_448 : BitVec.signExtend 64 (0x01c0#13) = 448#64 := by decide
@[gfetch] theorem zsext_13_452 : BitVec.signExtend 64 (0x01c4#13) = 452#64 := by decide
@[gfetch] theorem zsext_13_7724 : BitVec.signExtend 64 (0x1e2c#13) = 18446744073709551148#64 := by decide
@[gfetch] theorem zsext_13_7776 : BitVec.signExtend 64 (0x1e60#13) = 18446744073709551200#64 := by decide
@[gfetch] theorem zsext_13_7852 : BitVec.signExtend 64 (0x1eac#13) = 18446744073709551276#64 := by decide
@[gfetch] theorem zsext_13_7892 : BitVec.signExtend 64 (0x1ed4#13) = 18446744073709551316#64 := by decide
@[gfetch] theorem zsext_21_2096684 : BitVec.signExtend 64 (0x1ffe2c#21) = 18446744073709551148#64 := by decide
@[gfetch] theorem zsext_21_2096688 : BitVec.signExtend 64 (0x1ffe30#21) = 18446744073709551152#64 := by decide
@[gfetch] theorem zsext_21_2096784 : BitVec.signExtend 64 (0x1ffe90#21) = 18446744073709551248#64 := by decide
@[gfetch] theorem zsext_21_2096804 : BitVec.signExtend 64 (0x1ffea4#21) = 18446744073709551268#64 := by decide
@[gfetch] theorem zsext_21_2096840 : BitVec.signExtend 64 (0x1ffec8#21) = 18446744073709551304#64 := by decide
@[gfetch] theorem zsext_21_2096904 : BitVec.signExtend 64 (0x1fff08#21) = 18446744073709551368#64 := by decide
@[gfetch] theorem zsext_21_2097032 : BitVec.signExtend 64 (0x1fff88#21) = 18446744073709551496#64 := by decide
@[gfetch] theorem zsext_21_2097060 : BitVec.signExtend 64 (0x1fffa4#21) = 18446744073709551524#64 := by decide
@[gfetch] theorem zsext_21_2097076 : BitVec.signExtend 64 (0x1fffb4#21) = 18446744073709551540#64 := by decide
@[gfetch] theorem zsext_21_2097092 : BitVec.signExtend 64 (0x1fffc4#21) = 18446744073709551556#64 := by decide
@[gfetch] theorem zsext_21_532 : BitVec.signExtend 64 (0x000214#21) = 532#64 := by decide
@[gfetch] theorem zsext_u0 : BitVec.signExtend 64 (0x00000#20 ++ 0#12) = 0#64 := by decide
@[gfetch] theorem zsext_u1024 : BitVec.signExtend 64 (0x00400#20 ++ 0#12) = 4194304#64 := by decide

theorem fetch_0 : ∀ pc, pc < 400 → pc % 4 = 0 →
    (readBytes image (0 + pc) 4).bind (decode 64) = some (instrAt (0 + pc)) := by
  decide +kernel

theorem fetch_400 : ∀ pc, pc < 400 → pc % 4 = 0 →
    (readBytes image (400 + pc) 4).bind (decode 64) = some (instrAt (400 + pc)) := by
  decide +kernel

theorem fetch_800 : ∀ pc, pc < 400 → pc % 4 = 0 →
    (readBytes image (800 + pc) 4).bind (decode 64) = some (instrAt (800 + pc)) := by
  decide +kernel

theorem fetch_1200 : ∀ pc, pc < 280 → pc % 4 = 0 →
    (readBytes image (1200 + pc) 4).bind (decode 64) = some (instrAt (1200 + pc)) := by
  decide +kernel

theorem fetch (pc : Nat) (h : pc < codeEnd) (h4 : pc % 4 = 0) :
    (readBytes image pc 4).bind (decode 64) = some (instrAt pc) := by
  change pc < 1480 at h
  by_cases h400 : pc < 400
  · have := fetch_0 (pc - 0) (by omega) (by omega)
    rwa [show 0 + (pc - 0) = pc by omega] at this
  by_cases h800 : pc < 800
  · have := fetch_400 (pc - 400) (by omega) (by omega)
    rwa [show 400 + (pc - 400) = pc by omega] at this
  by_cases h1200 : pc < 1200
  · have := fetch_800 (pc - 800) (by omega) (by omega)
    rwa [show 800 + (pc - 800) = pc by omega] at this
  have := fetch_1200 (pc - 1200) (by omega) (by omega)
  rwa [show 1200 + (pc - 1200) = pc by omega] at this

theorem step_at (x : Regs 64) (pc : Nat) (mem : Array (BitVec 8))
    (out : String) (st : Status) (hmem : Prefix image mem 1480)
    (h : pc < 1480) (h4 : pc % 4 = 0) :
    step ⟨x, BitVec.ofNat 64 pc, mem, [], out, st⟩ =
      exec (instrAt pc) ⟨x, BitVec.ofNat 64 pc, mem, [], out, st⟩ := by
  have hpc : (BitVec.ofNat 64 pc).toNat = pc := by
    rw [BitVec.toNat_ofNat]; omega
  apply step_of_prefix _ image 1480 hmem (by change (BitVec.ofNat 64 pc).toNat + 4 ≤ 1480; omega)
  change (readBytes image (BitVec.ofNat 64 pc).toNat 4).bind (decode 64) = _
  rw [hpc]
  exact fetch _ h h4

end TinyFive.ZjyBinary
