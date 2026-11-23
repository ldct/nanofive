import TinyFive.Machine
import TinyFive.SieveMemory
import LucyMemory
import LphaBinary.Program
import GrumpyBinary.Attr

/-! Instruction fetch for the recompiled lpha image.

`instrAt` is the decoded instruction at every code address below `codeEnd = 1536`; `fetch`
checks it against the loaded words by `decide`. The `gfetch` lemmas are shared with the
grumpygordon proof, whose arithmetic rewrite rules this proof reuses. -/
namespace TinyFive.LphaBinary
open SieveMemory

/-- The loaded image (code only). -/
def image : Array (BitVec 8) := (load 64 prog 1536 []).mem

/-- The end of the code (the whole image). -/
abbrev codeEnd : Nat := 1536

def instrAt : Nat → Instr
  | 0 => .lui 2 0x00400#20
  | 4 => .jal 1 0x000044#21
  | 8 => .opImm .sll 10 10 0x020#12
  | 12 => .opImm .srl 10 10 0x020#12
  | 16 => .opImm .add 17 0 0x001#12
  | 20 => .ecall
  | 24 => .opImm .add 10 0 0x00a#12
  | 28 => .opImm .add 17 0 0x00b#12
  | 32 => .ecall
  | 36 => .opImm .add 17 0 0x00a#12
  | 40 => .ecall
  | 44 => .op .add 12 10 12
  | 48 => .opImm .add 15 10 0x000#12
  | 52 => .branch .bne 15 12 0x0008#13
  | 56 => .jalr 0 1 0x000#12
  | 60 => .opImm .add 15 15 0x001#12
  | 64 => .store .byte 11 15 0xfff#12
  | 68 => .jal 0 0x1ffff0#21
  | 72 => .opImm .add 15 0 0x001#12
  | 76 => .branch .bgeu 15 10 0x05ac#13
  | 80 => .opImm .add 2 2 0xb80#12
  | 84 => .lui 5 0xffcaf#20
  | 88 => .opImm .add 15 10 0x001#12
  | 92 => .store .dword 9 2 0x468#12
  | 96 => .store .dword 18 2 0x460#12
  | 100 => .store .dword 1 2 0x478#12
  | 104 => .store .dword 8 2 0x470#12
  | 108 => .store .dword 19 2 0x458#12
  | 112 => .store .dword 20 2 0x450#12
  | 116 => .store .dword 21 2 0x448#12
  | 120 => .store .dword 22 2 0x440#12
  | 124 => .store .dword 23 2 0x438#12
  | 128 => .store .dword 24 2 0x430#12
  | 132 => .store .dword 25 2 0x428#12
  | 136 => .store .dword 26 2 0x420#12
  | 140 => .store .dword 27 2 0x418#12
  | 144 => .opImm .add 18 10 0x000#12
  | 148 => .op .add 2 2 5
  | 152 => .opImm .srl 15 15 0x001#12
  | 156 => .opImm .add 9 10 0x000#12
  | 160 => .branch .bltu 15 9 0x0250#13
  | 164 => .lui 19 0x00351#20
  | 168 => .lui 10 0xffcaf#20
  | 172 => .opImm .add 10 10 0xc10#12
  | 176 => .opImm .add 15 19 0x3f0#12
  | 180 => .op .add 15 15 10
  | 184 => .opImm .add 14 2 0x020#12
  | 188 => .lui 12 0x0004d#20
  | 192 => .op .add 10 15 14
  | 196 => .opImm .add 12 12 0x344#12
  | 200 => .opImm .add 11 0 0x000#12
  | 204 => .auipc 1 0x00000#20
  | 208 => .jalr 1 1 0xf60#12
  | 212 => .lui 15 0xffcfc#20
  | 216 => .opImm .add 15 15 0xf58#12
  | 220 => .opImm .add 13 19 0x3f0#12
  | 224 => .op .add 13 13 15
  | 228 => .lui 12 0xffe31#20
  | 232 => .opImm .add 15 2 0x020#12
  | 236 => .opImm .add 12 12 0xc68#12
  | 240 => .op .add 15 13 15
  | 244 => .opImm .add 13 19 0x3f0#12
  | 248 => .op .add 13 13 12
  | 252 => .opImm .add 12 2 0x020#12
  | 256 => .op .add 12 13 12
  | 260 => .lui 13 0xffecb#20
  | 264 => .opImm .add 13 13 0x2f0#12
  | 268 => .opImm .add 11 19 0x3f0#12
  | 272 => .op .add 11 11 13
  | 276 => .opImm .add 13 2 0x020#12
  | 280 => .op .add 13 11 13
  | 284 => .lui 11 0xffd96#20
  | 288 => .opImm .add 11 11 0x5e0#12
  | 292 => .opImm .add 14 19 0x3f0#12
  | 296 => .op .add 14 14 11
  | 300 => .opImm .add 11 2 0x020#12
  | 304 => .opImm .add 8 9 0x001#12
  | 308 => .op .add 11 14 11
  | 312 => .opImm .srl 8 8 0x001#12
  | 316 => .opImm .add 17 11 0x000#12
  | 320 => .opImm .add 6 13 0x000#12
  | 324 => .opImm .add 28 12 0x000#12
  | 328 => .opImm .add 16 0 0x001#12
  | 332 => .opImm .add 10 0 0x000#12
  | 336 => .branch .bne 10 8 0x01b4#13
  | 340 => .lui 17 0x00351#20
  | 344 => .lui 7 0xffcaf#20
  | 348 => .opImm .add 16 17 0x3f0#12
  | 352 => .opImm .add 6 2 0x020#12
  | 356 => .op .add 16 16 7
  | 360 => .op .add 7 16 6
  | 364 => .lui 28 0xffd96#20
  | 368 => .opImm .add 16 17 0x3f0#12
  | 372 => .op .add 16 16 28
  | 376 => .op .add 28 16 6
  | 380 => .lui 29 0xffcfc#20
  | 384 => .opImm .add 16 17 0x3f0#12
  | 388 => .op .add 16 16 29
  | 392 => .op .add 29 16 6
  | 396 => .lui 16 0xffe31#20
  | 400 => .opImm .add 16 16 0xc68#12
  | 404 => .opImm .add 6 17 0x3f0#12
  | 408 => .op .add 6 6 16
  | 412 => .opImm .add 16 2 0x020#12
  | 416 => .op .add 16 6 16
  | 420 => .store .dword 16 2 0x008#12
  | 424 => .lui 16 0xffecb#20
  | 428 => .opImm .add 16 16 0x2f0#12
  | 432 => .opImm .add 6 17 0x3f0#12
  | 436 => .op .add 6 6 16
  | 440 => .opImm .add 16 2 0x020#12
  | 444 => .op .add 16 6 16
  | 448 => .lui 30 0xffd96#20
  | 452 => .store .dword 16 2 0x010#12
  | 456 => .opImm .add 30 30 0x5e0#12
  | 460 => .opImm .add 16 17 0x3f0#12
  | 464 => .opImm .add 15 9 0xfff#12
  | 468 => .opImm .add 6 2 0x020#12
  | 472 => .lui 10 0xffcaf#20
  | 476 => .op .add 16 16 30
  | 480 => .opImm .add 10 10 0xc10#12
  | 484 => .op .add 16 16 6
  | 488 => .opImm .srl 27 15 0x001#12
  | 492 => .lui 31 0xffcfc#20
  | 496 => .opImm .add 15 17 0x3f0#12
  | 500 => .op .add 15 15 10
  | 504 => .opImm .add 14 2 0x020#12
  | 508 => .opImm .add 31 31 0xf58#12
  | 512 => .store .dword 16 2 0x018#12
  | 516 => .opImm .add 16 17 0x3f0#12
  | 520 => .op .add 10 15 14
  | 524 => .op .add 16 16 31
  | 528 => .opImm .add 15 0 0x003#12
  | 532 => .opImm .add 14 0 0x000#12
  | 536 => .store .dword 10 2 0x000#12
  | 540 => .op .add 31 16 6
  | 544 => .op .mul 16 15 15
  | 548 => .branch .bgeu 9 16 0x0118#13
  | 552 => .lui 10 0x00351#20
  | 556 => .lui 15 0xffd96#20
  | 560 => .opImm .add 10 10 0x3f0#12
  | 564 => .op .add 10 10 15
  | 568 => .opImm .add 15 2 0x020#12
  | 572 => .op .add 15 10 15
  | 576 => .load .word true 15 15 0x5e0#12
  | 580 => .opImm .add 10 0 0x001#12
  | 584 => .opImmWord .add 15 15 0x001#12
  | 588 => .opImm .add 11 11 0x004#12
  | 592 => .branch .bltu 10 8 0x030c#13
  | 596 => .opImm .add 16 8 0xfff#12
  | 600 => .op .mul 11 16 8
  | 604 => .opImmWord .add 10 14 0xfff#12
  | 608 => .lui 6 0xffcfc#20
  | 612 => .opImm .add 17 2 0x020#12
  | 616 => .opImmWord .add 30 14 0xffe#12
  | 620 => .opWord .mul 10 10 16
  | 624 => .opImm .srl 11 11 0x001#12
  | 628 => .opImm .add 16 0 0x001#12
  | 632 => .opWord .add 10 10 11
  | 636 => .lui 11 0x00351#20
  | 640 => .opWord .add 10 10 15
  | 644 => .opImm .add 15 11 0x3f0#12
  | 648 => .op .add 15 15 6
  | 652 => .op .add 6 15 17
  | 656 => .lui 17 0xffecb#20
  | 660 => .opImm .add 17 17 0x2f0#12
  | 664 => .opImm .add 15 11 0x3f0#12
  | 668 => .op .add 15 15 17
  | 672 => .opImm .add 11 2 0x020#12
  | 676 => .op .add 17 15 11
  | 680 => .branch .bltu 16 8 0x02c4#13
  | 684 => .lui 5 0x00351#20
  | 688 => .op .add 2 2 5
  | 692 => .load .dword true 1 2 0x478#12
  | 696 => .load .dword true 8 2 0x470#12
  | 700 => .load .dword true 9 2 0x468#12
  | 704 => .load .dword true 18 2 0x460#12
  | 708 => .load .dword true 19 2 0x458#12
  | 712 => .load .dword true 20 2 0x450#12
  | 716 => .load .dword true 21 2 0x448#12
  | 720 => .load .dword true 22 2 0x440#12
  | 724 => .load .dword true 23 2 0x438#12
  | 728 => .load .dword true 24 2 0x430#12
  | 732 => .load .dword true 25 2 0x428#12
  | 736 => .load .dword true 26 2 0x420#12
  | 740 => .load .dword true 27 2 0x418#12
  | 744 => .opImm .add 2 2 0x480#12
  | 748 => .jalr 0 1 0x000#12
  | 752 => .op .divu 14 18 15
  | 756 => .opImm .add 9 15 0x000#12
  | 760 => .op .add 14 14 15
  | 764 => .opImm .srl 15 14 0x001#12
  | 768 => .jal 0 0x1ffda0#21
  | 772 => .op .divu 14 18 16
  | 776 => .store .word 10 15 0x000#12
  | 780 => .store .word 16 28 0x000#12
  | 784 => .opImm .add 10 10 0x001#12
  | 788 => .opImm .add 15 15 0x004#12
  | 792 => .opImm .add 28 28 0x004#12
  | 796 => .opImm .add 16 16 0x002#12
  | 800 => .opImm .add 6 6 0x008#12
  | 804 => .opImm .add 17 17 0x004#12
  | 808 => .store .dword 14 6 0xff8#12
  | 812 => .opImm .add 14 14 0xfff#12
  | 816 => .opImm .srl 14 14 0x001#12
  | 820 => .store .word 14 17 0xffc#12
  | 824 => .jal 0 0x1ffe18#21
  | 828 => .load .byte false 17 10 0x003#12
  | 832 => .branch .bne 17 0 0x00d0#13
  | 836 => .opImm .add 17 0 0x001#12
  | 840 => .store .byte 17 10 0x003#12
  | 844 => .opImm .sll 24 15 0x001#12
  | 848 => .opImm .add 6 0 0x001#12
  | 852 => .load .dword true 17 2 0x000#12
  | 856 => .op .add 17 17 16
  | 860 => .store .byte 6 17 0x000#12
  | 864 => .op .add 16 16 24
  | 868 => .branch .bgeu 9 16 0x1ff0#13
  | 872 => .lui 5 0x00351#20
  | 876 => .lui 22 0xffecb#20
  | 880 => .opImm .add 6 5 0x3f0#12
  | 884 => .op .add 6 6 22
  | 888 => .opImm .add 30 2 0x020#12
  | 892 => .lui 23 0xffe31#20
  | 896 => .op .add 22 6 30
  | 900 => .opImm .add 6 5 0x3f0#12
  | 904 => .op .add 6 6 23
  | 908 => .opImm .add 19 13 0x000#12
  | 912 => .opImm .add 20 11 0x000#12
  | 916 => .opImm .add 21 12 0x000#12
  | 920 => .opImm .add 17 0 0x000#12
  | 924 => .opImm .add 16 0 0x000#12
  | 928 => .op .add 23 6 30
  | 932 => .load .word true 25 21 0x000#12
  | 936 => .opImm .sll 6 25 0x020#12
  | 940 => .opImm .srl 6 6 0x020#12
  | 944 => .op .add 5 7 6
  | 948 => .load .byte false 5 5 0xc10#12
  | 952 => .branch .bne 5 0 0x00bc#13
  | 956 => .op .mul 6 15 6
  | 960 => .branch .bgeu 9 6 0x005c#13
  | 964 => .lui 5 0x00351#20
  | 968 => .lui 19 0xffecb#20
  | 972 => .opImm .add 6 5 0x3f0#12
  | 976 => .op .add 6 6 19
  | 980 => .opImm .add 30 2 0x020#12
  | 984 => .lui 20 0xffe31#20
  | 988 => .op .add 19 6 30
  | 992 => .opImm .add 6 5 0x3f0#12
  | 996 => .op .add 6 6 20
  | 1000 => .op .add 20 6 30
  | 1004 => .branch .bltu 17 8 0x009c#13
  | 1008 => .op .divu 17 9 15
  | 1012 => .opImm .add 5 27 0x000#12
  | 1016 => .opImm .add 17 17 0xfff#12
  | 1020 => .opImm .or 17 17 0x001#12
  | 1024 => .op .mul 8 15 17
  | 1028 => .branch .bgeu 17 15 0x0110#13
  | 1032 => .opImmWord .add 14 14 0x001#12
  | 1036 => .opImm .add 8 16 0x000#12
  | 1040 => .opImm .add 15 15 0x002#12
  | 1044 => .opImm .add 10 10 0x002#12
  | 1048 => .jal 0 0x1ffe08#21
  | 1052 => .opImm .srl 6 6 0x001#12
  | 1056 => .opImm .sll 6 6 0x002#12
  | 1060 => .op .add 6 29 6
  | 1064 => .load .word true 6 6 0xf58#12
  | 1068 => .load .word true 5 20 0x000#12
  | 1072 => .opImm .sll 18 16 0x002#12
  | 1076 => .opWord .sub 6 6 14
  | 1080 => .opImm .sll 30 6 0x020#12
  | 1084 => .opImm .srl 6 30 0x01e#12
  | 1088 => .op .add 6 28 6
  | 1092 => .load .word true 6 6 0x5e0#12
  | 1096 => .opWord .add 5 5 14
  | 1100 => .op .add 26 28 18
  | 1104 => .opWord .sub 5 5 6
  | 1108 => .store .word 5 26 0x5e0#12
  | 1112 => .load .dword true 5 19 0x000#12
  | 1116 => .opImm .sll 6 16 0x003#12
  | 1120 => .op .add 6 22 6
  | 1124 => .op .add 18 23 18
  | 1128 => .store .dword 5 6 0x2f0#12
  | 1132 => .store .word 25 18 0xc68#12
  | 1136 => .opImm .add 16 16 0x001#12
  | 1140 => .opImm .add 17 17 0x001#12
  | 1144 => .opImm .add 21 21 0x004#12
  | 1148 => .opImm .add 20 20 0x004#12
  | 1152 => .opImm .add 19 19 0x008#12
  | 1156 => .jal 0 0x1fff20#21
  | 1160 => .load .dword true 5 2 0x008#12
  | 1164 => .opImm .sll 6 17 0x002#12
  | 1168 => .op .add 5 5 6
  | 1172 => .load .word true 21 5 0x000#12
  | 1176 => .opImm .sll 5 21 0x020#12
  | 1180 => .opImm .srl 5 5 0x020#12
  | 1184 => .op .add 5 7 5
  | 1188 => .load .byte false 5 5 0xc10#12
  | 1192 => .branch .bne 5 0 0x0064#13
  | 1196 => .load .dword true 18 2 0x010#12
  | 1200 => .opImm .sll 5 17 0x003#12
  | 1204 => .load .dword true 30 2 0x018#12
  | 1208 => .op .add 5 18 5
  | 1212 => .load .dword true 22 5 0x000#12
  | 1216 => .op .add 6 30 6
  | 1220 => .load .word true 5 6 0x000#12
  | 1224 => .op .divu 6 22 15
  | 1228 => .opImm .sll 18 16 0x002#12
  | 1232 => .opWord .add 5 5 14
  | 1236 => .op .add 23 28 18
  | 1240 => .op .add 18 20 18
  | 1244 => .store .word 21 18 0xc68#12
  | 1248 => .opImm .add 6 6 0xfff#12
  | 1252 => .opImm .srl 6 6 0x001#12
  | 1256 => .opImm .sll 6 6 0x002#12
  | 1260 => .op .add 6 29 6
  | 1264 => .load .word true 6 6 0xf58#12
  | 1268 => .opWord .sub 5 5 6
  | 1272 => .opImm .sll 6 16 0x003#12
  | 1276 => .op .add 6 19 6
  | 1280 => .store .word 5 23 0x5e0#12
  | 1284 => .store .dword 22 6 0x2f0#12
  | 1288 => .opImm .add 16 16 0x001#12
  | 1292 => .opImm .add 17 17 0x001#12
  | 1296 => .jal 0 0x1ffedc#21
  | 1300 => .opImm .srl 6 17 0x001#12
  | 1304 => .opImm .sll 6 6 0x002#12
  | 1308 => .op .add 6 29 6
  | 1312 => .load .word true 18 6 0xf58#12
  | 1316 => .opImm .sll 6 5 0x002#12
  | 1320 => .opImm .srl 20 8 0x001#12
  | 1324 => .op .add 6 31 6
  | 1328 => .opWord .sub 18 14 18
  | 1332 => .branch .bgeu 5 20 0x0010#13
  | 1336 => .opImm .add 17 17 0xffe#12
  | 1340 => .op .sub 8 8 24
  | 1344 => .jal 0 0x1ffec4#21
  | 1348 => .load .word true 19 6 0x000#12
  | 1352 => .opImm .add 5 5 0xfff#12
  | 1356 => .opImm .add 6 6 0xffc#12
  | 1360 => .opWord .add 19 18 19
  | 1364 => .store .word 19 6 0x004#12
  | 1368 => .jal 0 0x1fffdc#21
  | 1372 => .load .word true 16 11 0x000#12
  | 1376 => .opImm .add 10 10 0x001#12
  | 1380 => .opWord .sub 15 15 16
  | 1384 => .jal 0 0x1ffce4#21
  | 1388 => .load .word false 31 12 0x004#12
  | 1392 => .load .dword true 15 13 0x008#12
  | 1396 => .op .divu 15 15 31
  | 1400 => .opImm .add 15 15 0xfff#12
  | 1404 => .opImm .srl 15 15 0x001#12
  | 1408 => .opImm .sll 15 15 0x002#12
  | 1412 => .op .add 15 6 15
  | 1416 => .load .word true 11 15 0xf58#12
  | 1420 => .opWord .sub 11 11 14
  | 1424 => .opImm .sll 11 11 0x020#12
  | 1428 => .opImm .srl 11 11 0x020#12
  | 1432 => .branch .bgeu 16 11 0x1d14#13
  | 1436 => .opImm .add 29 16 0x001#12
  | 1440 => .opImm .add 28 29 0x000#12
  | 1444 => .branch .bgeu 11 28 0x0024#13
  | 1448 => .op .sub 11 11 16
  | 1452 => .opWord .add 15 30 29
  | 1456 => .opWord .mul 15 15 11
  | 1460 => .opImm .add 12 12 0x004#12
  | 1464 => .opImm .add 13 13 0x008#12
  | 1468 => .opImm .add 16 29 0x000#12
  | 1472 => .opWord .sub 10 10 15
  | 1476 => .jal 0 0x1ffce4#21
  | 1480 => .opImm .sll 15 28 0x003#12
  | 1484 => .op .add 15 17 15
  | 1488 => .load .dword true 15 15 0x000#12
  | 1492 => .opImm .add 28 28 0x001#12
  | 1496 => .op .divu 15 15 31
  | 1500 => .opImm .add 15 15 0xfff#12
  | 1504 => .opImm .srl 15 15 0x001#12
  | 1508 => .opImm .sll 15 15 0x002#12
  | 1512 => .op .add 15 6 15
  | 1516 => .load .word true 15 15 0xf58#12
  | 1520 => .opWord .add 10 15 10
  | 1524 => .jal 0 0x1fffb0#21
  | 1528 => .opImm .add 10 0 0x000#12
  | 1532 => .jalr 0 1 0x000#12
  | _ => .ecall

/-! One rewrite rule per address, for symbolic execution. -/

@[gfetch] theorem instrAt_0 : instrAt 0 = .lui 2 0x00400#20 := rfl
@[gfetch] theorem instrAt_4 : instrAt 4 = .jal 1 0x000044#21 := rfl
@[gfetch] theorem instrAt_8 : instrAt 8 = .opImm .sll 10 10 0x020#12 := rfl
@[gfetch] theorem instrAt_12 : instrAt 12 = .opImm .srl 10 10 0x020#12 := rfl
@[gfetch] theorem instrAt_16 : instrAt 16 = .opImm .add 17 0 0x001#12 := rfl
@[gfetch] theorem instrAt_20 : instrAt 20 = .ecall := rfl
@[gfetch] theorem instrAt_24 : instrAt 24 = .opImm .add 10 0 0x00a#12 := rfl
@[gfetch] theorem instrAt_28 : instrAt 28 = .opImm .add 17 0 0x00b#12 := rfl
@[gfetch] theorem instrAt_32 : instrAt 32 = .ecall := rfl
@[gfetch] theorem instrAt_36 : instrAt 36 = .opImm .add 17 0 0x00a#12 := rfl
@[gfetch] theorem instrAt_40 : instrAt 40 = .ecall := rfl
@[gfetch] theorem instrAt_44 : instrAt 44 = .op .add 12 10 12 := rfl
@[gfetch] theorem instrAt_48 : instrAt 48 = .opImm .add 15 10 0x000#12 := rfl
@[gfetch] theorem instrAt_52 : instrAt 52 = .branch .bne 15 12 0x0008#13 := rfl
@[gfetch] theorem instrAt_56 : instrAt 56 = .jalr 0 1 0x000#12 := rfl
@[gfetch] theorem instrAt_60 : instrAt 60 = .opImm .add 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_64 : instrAt 64 = .store .byte 11 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_68 : instrAt 68 = .jal 0 0x1ffff0#21 := rfl
@[gfetch] theorem instrAt_72 : instrAt 72 = .opImm .add 15 0 0x001#12 := rfl
@[gfetch] theorem instrAt_76 : instrAt 76 = .branch .bgeu 15 10 0x05ac#13 := rfl
@[gfetch] theorem instrAt_80 : instrAt 80 = .opImm .add 2 2 0xb80#12 := rfl
@[gfetch] theorem instrAt_84 : instrAt 84 = .lui 5 0xffcaf#20 := rfl
@[gfetch] theorem instrAt_88 : instrAt 88 = .opImm .add 15 10 0x001#12 := rfl
@[gfetch] theorem instrAt_92 : instrAt 92 = .store .dword 9 2 0x468#12 := rfl
@[gfetch] theorem instrAt_96 : instrAt 96 = .store .dword 18 2 0x460#12 := rfl
@[gfetch] theorem instrAt_100 : instrAt 100 = .store .dword 1 2 0x478#12 := rfl
@[gfetch] theorem instrAt_104 : instrAt 104 = .store .dword 8 2 0x470#12 := rfl
@[gfetch] theorem instrAt_108 : instrAt 108 = .store .dword 19 2 0x458#12 := rfl
@[gfetch] theorem instrAt_112 : instrAt 112 = .store .dword 20 2 0x450#12 := rfl
@[gfetch] theorem instrAt_116 : instrAt 116 = .store .dword 21 2 0x448#12 := rfl
@[gfetch] theorem instrAt_120 : instrAt 120 = .store .dword 22 2 0x440#12 := rfl
@[gfetch] theorem instrAt_124 : instrAt 124 = .store .dword 23 2 0x438#12 := rfl
@[gfetch] theorem instrAt_128 : instrAt 128 = .store .dword 24 2 0x430#12 := rfl
@[gfetch] theorem instrAt_132 : instrAt 132 = .store .dword 25 2 0x428#12 := rfl
@[gfetch] theorem instrAt_136 : instrAt 136 = .store .dword 26 2 0x420#12 := rfl
@[gfetch] theorem instrAt_140 : instrAt 140 = .store .dword 27 2 0x418#12 := rfl
@[gfetch] theorem instrAt_144 : instrAt 144 = .opImm .add 18 10 0x000#12 := rfl
@[gfetch] theorem instrAt_148 : instrAt 148 = .op .add 2 2 5 := rfl
@[gfetch] theorem instrAt_152 : instrAt 152 = .opImm .srl 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_156 : instrAt 156 = .opImm .add 9 10 0x000#12 := rfl
@[gfetch] theorem instrAt_160 : instrAt 160 = .branch .bltu 15 9 0x0250#13 := rfl
@[gfetch] theorem instrAt_164 : instrAt 164 = .lui 19 0x00351#20 := rfl
@[gfetch] theorem instrAt_168 : instrAt 168 = .lui 10 0xffcaf#20 := rfl
@[gfetch] theorem instrAt_172 : instrAt 172 = .opImm .add 10 10 0xc10#12 := rfl
@[gfetch] theorem instrAt_176 : instrAt 176 = .opImm .add 15 19 0x3f0#12 := rfl
@[gfetch] theorem instrAt_180 : instrAt 180 = .op .add 15 15 10 := rfl
@[gfetch] theorem instrAt_184 : instrAt 184 = .opImm .add 14 2 0x020#12 := rfl
@[gfetch] theorem instrAt_188 : instrAt 188 = .lui 12 0x0004d#20 := rfl
@[gfetch] theorem instrAt_192 : instrAt 192 = .op .add 10 15 14 := rfl
@[gfetch] theorem instrAt_196 : instrAt 196 = .opImm .add 12 12 0x344#12 := rfl
@[gfetch] theorem instrAt_200 : instrAt 200 = .opImm .add 11 0 0x000#12 := rfl
@[gfetch] theorem instrAt_204 : instrAt 204 = .auipc 1 0x00000#20 := rfl
@[gfetch] theorem instrAt_208 : instrAt 208 = .jalr 1 1 0xf60#12 := rfl
@[gfetch] theorem instrAt_212 : instrAt 212 = .lui 15 0xffcfc#20 := rfl
@[gfetch] theorem instrAt_216 : instrAt 216 = .opImm .add 15 15 0xf58#12 := rfl
@[gfetch] theorem instrAt_220 : instrAt 220 = .opImm .add 13 19 0x3f0#12 := rfl
@[gfetch] theorem instrAt_224 : instrAt 224 = .op .add 13 13 15 := rfl
@[gfetch] theorem instrAt_228 : instrAt 228 = .lui 12 0xffe31#20 := rfl
@[gfetch] theorem instrAt_232 : instrAt 232 = .opImm .add 15 2 0x020#12 := rfl
@[gfetch] theorem instrAt_236 : instrAt 236 = .opImm .add 12 12 0xc68#12 := rfl
@[gfetch] theorem instrAt_240 : instrAt 240 = .op .add 15 13 15 := rfl
@[gfetch] theorem instrAt_244 : instrAt 244 = .opImm .add 13 19 0x3f0#12 := rfl
@[gfetch] theorem instrAt_248 : instrAt 248 = .op .add 13 13 12 := rfl
@[gfetch] theorem instrAt_252 : instrAt 252 = .opImm .add 12 2 0x020#12 := rfl
@[gfetch] theorem instrAt_256 : instrAt 256 = .op .add 12 13 12 := rfl
@[gfetch] theorem instrAt_260 : instrAt 260 = .lui 13 0xffecb#20 := rfl
@[gfetch] theorem instrAt_264 : instrAt 264 = .opImm .add 13 13 0x2f0#12 := rfl
@[gfetch] theorem instrAt_268 : instrAt 268 = .opImm .add 11 19 0x3f0#12 := rfl
@[gfetch] theorem instrAt_272 : instrAt 272 = .op .add 11 11 13 := rfl
@[gfetch] theorem instrAt_276 : instrAt 276 = .opImm .add 13 2 0x020#12 := rfl
@[gfetch] theorem instrAt_280 : instrAt 280 = .op .add 13 11 13 := rfl
@[gfetch] theorem instrAt_284 : instrAt 284 = .lui 11 0xffd96#20 := rfl
@[gfetch] theorem instrAt_288 : instrAt 288 = .opImm .add 11 11 0x5e0#12 := rfl
@[gfetch] theorem instrAt_292 : instrAt 292 = .opImm .add 14 19 0x3f0#12 := rfl
@[gfetch] theorem instrAt_296 : instrAt 296 = .op .add 14 14 11 := rfl
@[gfetch] theorem instrAt_300 : instrAt 300 = .opImm .add 11 2 0x020#12 := rfl
@[gfetch] theorem instrAt_304 : instrAt 304 = .opImm .add 8 9 0x001#12 := rfl
@[gfetch] theorem instrAt_308 : instrAt 308 = .op .add 11 14 11 := rfl
@[gfetch] theorem instrAt_312 : instrAt 312 = .opImm .srl 8 8 0x001#12 := rfl
@[gfetch] theorem instrAt_316 : instrAt 316 = .opImm .add 17 11 0x000#12 := rfl
@[gfetch] theorem instrAt_320 : instrAt 320 = .opImm .add 6 13 0x000#12 := rfl
@[gfetch] theorem instrAt_324 : instrAt 324 = .opImm .add 28 12 0x000#12 := rfl
@[gfetch] theorem instrAt_328 : instrAt 328 = .opImm .add 16 0 0x001#12 := rfl
@[gfetch] theorem instrAt_332 : instrAt 332 = .opImm .add 10 0 0x000#12 := rfl
@[gfetch] theorem instrAt_336 : instrAt 336 = .branch .bne 10 8 0x01b4#13 := rfl
@[gfetch] theorem instrAt_340 : instrAt 340 = .lui 17 0x00351#20 := rfl
@[gfetch] theorem instrAt_344 : instrAt 344 = .lui 7 0xffcaf#20 := rfl
@[gfetch] theorem instrAt_348 : instrAt 348 = .opImm .add 16 17 0x3f0#12 := rfl
@[gfetch] theorem instrAt_352 : instrAt 352 = .opImm .add 6 2 0x020#12 := rfl
@[gfetch] theorem instrAt_356 : instrAt 356 = .op .add 16 16 7 := rfl
@[gfetch] theorem instrAt_360 : instrAt 360 = .op .add 7 16 6 := rfl
@[gfetch] theorem instrAt_364 : instrAt 364 = .lui 28 0xffd96#20 := rfl
@[gfetch] theorem instrAt_368 : instrAt 368 = .opImm .add 16 17 0x3f0#12 := rfl
@[gfetch] theorem instrAt_372 : instrAt 372 = .op .add 16 16 28 := rfl
@[gfetch] theorem instrAt_376 : instrAt 376 = .op .add 28 16 6 := rfl
@[gfetch] theorem instrAt_380 : instrAt 380 = .lui 29 0xffcfc#20 := rfl
@[gfetch] theorem instrAt_384 : instrAt 384 = .opImm .add 16 17 0x3f0#12 := rfl
@[gfetch] theorem instrAt_388 : instrAt 388 = .op .add 16 16 29 := rfl
@[gfetch] theorem instrAt_392 : instrAt 392 = .op .add 29 16 6 := rfl
@[gfetch] theorem instrAt_396 : instrAt 396 = .lui 16 0xffe31#20 := rfl
@[gfetch] theorem instrAt_400 : instrAt 400 = .opImm .add 16 16 0xc68#12 := rfl
@[gfetch] theorem instrAt_404 : instrAt 404 = .opImm .add 6 17 0x3f0#12 := rfl
@[gfetch] theorem instrAt_408 : instrAt 408 = .op .add 6 6 16 := rfl
@[gfetch] theorem instrAt_412 : instrAt 412 = .opImm .add 16 2 0x020#12 := rfl
@[gfetch] theorem instrAt_416 : instrAt 416 = .op .add 16 6 16 := rfl
@[gfetch] theorem instrAt_420 : instrAt 420 = .store .dword 16 2 0x008#12 := rfl
@[gfetch] theorem instrAt_424 : instrAt 424 = .lui 16 0xffecb#20 := rfl
@[gfetch] theorem instrAt_428 : instrAt 428 = .opImm .add 16 16 0x2f0#12 := rfl
@[gfetch] theorem instrAt_432 : instrAt 432 = .opImm .add 6 17 0x3f0#12 := rfl
@[gfetch] theorem instrAt_436 : instrAt 436 = .op .add 6 6 16 := rfl
@[gfetch] theorem instrAt_440 : instrAt 440 = .opImm .add 16 2 0x020#12 := rfl
@[gfetch] theorem instrAt_444 : instrAt 444 = .op .add 16 6 16 := rfl
@[gfetch] theorem instrAt_448 : instrAt 448 = .lui 30 0xffd96#20 := rfl
@[gfetch] theorem instrAt_452 : instrAt 452 = .store .dword 16 2 0x010#12 := rfl
@[gfetch] theorem instrAt_456 : instrAt 456 = .opImm .add 30 30 0x5e0#12 := rfl
@[gfetch] theorem instrAt_460 : instrAt 460 = .opImm .add 16 17 0x3f0#12 := rfl
@[gfetch] theorem instrAt_464 : instrAt 464 = .opImm .add 15 9 0xfff#12 := rfl
@[gfetch] theorem instrAt_468 : instrAt 468 = .opImm .add 6 2 0x020#12 := rfl
@[gfetch] theorem instrAt_472 : instrAt 472 = .lui 10 0xffcaf#20 := rfl
@[gfetch] theorem instrAt_476 : instrAt 476 = .op .add 16 16 30 := rfl
@[gfetch] theorem instrAt_480 : instrAt 480 = .opImm .add 10 10 0xc10#12 := rfl
@[gfetch] theorem instrAt_484 : instrAt 484 = .op .add 16 16 6 := rfl
@[gfetch] theorem instrAt_488 : instrAt 488 = .opImm .srl 27 15 0x001#12 := rfl
@[gfetch] theorem instrAt_492 : instrAt 492 = .lui 31 0xffcfc#20 := rfl
@[gfetch] theorem instrAt_496 : instrAt 496 = .opImm .add 15 17 0x3f0#12 := rfl
@[gfetch] theorem instrAt_500 : instrAt 500 = .op .add 15 15 10 := rfl
@[gfetch] theorem instrAt_504 : instrAt 504 = .opImm .add 14 2 0x020#12 := rfl
@[gfetch] theorem instrAt_508 : instrAt 508 = .opImm .add 31 31 0xf58#12 := rfl
@[gfetch] theorem instrAt_512 : instrAt 512 = .store .dword 16 2 0x018#12 := rfl
@[gfetch] theorem instrAt_516 : instrAt 516 = .opImm .add 16 17 0x3f0#12 := rfl
@[gfetch] theorem instrAt_520 : instrAt 520 = .op .add 10 15 14 := rfl
@[gfetch] theorem instrAt_524 : instrAt 524 = .op .add 16 16 31 := rfl
@[gfetch] theorem instrAt_528 : instrAt 528 = .opImm .add 15 0 0x003#12 := rfl
@[gfetch] theorem instrAt_532 : instrAt 532 = .opImm .add 14 0 0x000#12 := rfl
@[gfetch] theorem instrAt_536 : instrAt 536 = .store .dword 10 2 0x000#12 := rfl
@[gfetch] theorem instrAt_540 : instrAt 540 = .op .add 31 16 6 := rfl
@[gfetch] theorem instrAt_544 : instrAt 544 = .op .mul 16 15 15 := rfl
@[gfetch] theorem instrAt_548 : instrAt 548 = .branch .bgeu 9 16 0x0118#13 := rfl
@[gfetch] theorem instrAt_552 : instrAt 552 = .lui 10 0x00351#20 := rfl
@[gfetch] theorem instrAt_556 : instrAt 556 = .lui 15 0xffd96#20 := rfl
@[gfetch] theorem instrAt_560 : instrAt 560 = .opImm .add 10 10 0x3f0#12 := rfl
@[gfetch] theorem instrAt_564 : instrAt 564 = .op .add 10 10 15 := rfl
@[gfetch] theorem instrAt_568 : instrAt 568 = .opImm .add 15 2 0x020#12 := rfl
@[gfetch] theorem instrAt_572 : instrAt 572 = .op .add 15 10 15 := rfl
@[gfetch] theorem instrAt_576 : instrAt 576 = .load .word true 15 15 0x5e0#12 := rfl
@[gfetch] theorem instrAt_580 : instrAt 580 = .opImm .add 10 0 0x001#12 := rfl
@[gfetch] theorem instrAt_584 : instrAt 584 = .opImmWord .add 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_588 : instrAt 588 = .opImm .add 11 11 0x004#12 := rfl
@[gfetch] theorem instrAt_592 : instrAt 592 = .branch .bltu 10 8 0x030c#13 := rfl
@[gfetch] theorem instrAt_596 : instrAt 596 = .opImm .add 16 8 0xfff#12 := rfl
@[gfetch] theorem instrAt_600 : instrAt 600 = .op .mul 11 16 8 := rfl
@[gfetch] theorem instrAt_604 : instrAt 604 = .opImmWord .add 10 14 0xfff#12 := rfl
@[gfetch] theorem instrAt_608 : instrAt 608 = .lui 6 0xffcfc#20 := rfl
@[gfetch] theorem instrAt_612 : instrAt 612 = .opImm .add 17 2 0x020#12 := rfl
@[gfetch] theorem instrAt_616 : instrAt 616 = .opImmWord .add 30 14 0xffe#12 := rfl
@[gfetch] theorem instrAt_620 : instrAt 620 = .opWord .mul 10 10 16 := rfl
@[gfetch] theorem instrAt_624 : instrAt 624 = .opImm .srl 11 11 0x001#12 := rfl
@[gfetch] theorem instrAt_628 : instrAt 628 = .opImm .add 16 0 0x001#12 := rfl
@[gfetch] theorem instrAt_632 : instrAt 632 = .opWord .add 10 10 11 := rfl
@[gfetch] theorem instrAt_636 : instrAt 636 = .lui 11 0x00351#20 := rfl
@[gfetch] theorem instrAt_640 : instrAt 640 = .opWord .add 10 10 15 := rfl
@[gfetch] theorem instrAt_644 : instrAt 644 = .opImm .add 15 11 0x3f0#12 := rfl
@[gfetch] theorem instrAt_648 : instrAt 648 = .op .add 15 15 6 := rfl
@[gfetch] theorem instrAt_652 : instrAt 652 = .op .add 6 15 17 := rfl
@[gfetch] theorem instrAt_656 : instrAt 656 = .lui 17 0xffecb#20 := rfl
@[gfetch] theorem instrAt_660 : instrAt 660 = .opImm .add 17 17 0x2f0#12 := rfl
@[gfetch] theorem instrAt_664 : instrAt 664 = .opImm .add 15 11 0x3f0#12 := rfl
@[gfetch] theorem instrAt_668 : instrAt 668 = .op .add 15 15 17 := rfl
@[gfetch] theorem instrAt_672 : instrAt 672 = .opImm .add 11 2 0x020#12 := rfl
@[gfetch] theorem instrAt_676 : instrAt 676 = .op .add 17 15 11 := rfl
@[gfetch] theorem instrAt_680 : instrAt 680 = .branch .bltu 16 8 0x02c4#13 := rfl
@[gfetch] theorem instrAt_684 : instrAt 684 = .lui 5 0x00351#20 := rfl
@[gfetch] theorem instrAt_688 : instrAt 688 = .op .add 2 2 5 := rfl
@[gfetch] theorem instrAt_692 : instrAt 692 = .load .dword true 1 2 0x478#12 := rfl
@[gfetch] theorem instrAt_696 : instrAt 696 = .load .dword true 8 2 0x470#12 := rfl
@[gfetch] theorem instrAt_700 : instrAt 700 = .load .dword true 9 2 0x468#12 := rfl
@[gfetch] theorem instrAt_704 : instrAt 704 = .load .dword true 18 2 0x460#12 := rfl
@[gfetch] theorem instrAt_708 : instrAt 708 = .load .dword true 19 2 0x458#12 := rfl
@[gfetch] theorem instrAt_712 : instrAt 712 = .load .dword true 20 2 0x450#12 := rfl
@[gfetch] theorem instrAt_716 : instrAt 716 = .load .dword true 21 2 0x448#12 := rfl
@[gfetch] theorem instrAt_720 : instrAt 720 = .load .dword true 22 2 0x440#12 := rfl
@[gfetch] theorem instrAt_724 : instrAt 724 = .load .dword true 23 2 0x438#12 := rfl
@[gfetch] theorem instrAt_728 : instrAt 728 = .load .dword true 24 2 0x430#12 := rfl
@[gfetch] theorem instrAt_732 : instrAt 732 = .load .dword true 25 2 0x428#12 := rfl
@[gfetch] theorem instrAt_736 : instrAt 736 = .load .dword true 26 2 0x420#12 := rfl
@[gfetch] theorem instrAt_740 : instrAt 740 = .load .dword true 27 2 0x418#12 := rfl
@[gfetch] theorem instrAt_744 : instrAt 744 = .opImm .add 2 2 0x480#12 := rfl
@[gfetch] theorem instrAt_748 : instrAt 748 = .jalr 0 1 0x000#12 := rfl
@[gfetch] theorem instrAt_752 : instrAt 752 = .op .divu 14 18 15 := rfl
@[gfetch] theorem instrAt_756 : instrAt 756 = .opImm .add 9 15 0x000#12 := rfl
@[gfetch] theorem instrAt_760 : instrAt 760 = .op .add 14 14 15 := rfl
@[gfetch] theorem instrAt_764 : instrAt 764 = .opImm .srl 15 14 0x001#12 := rfl
@[gfetch] theorem instrAt_768 : instrAt 768 = .jal 0 0x1ffda0#21 := rfl
@[gfetch] theorem instrAt_772 : instrAt 772 = .op .divu 14 18 16 := rfl
@[gfetch] theorem instrAt_776 : instrAt 776 = .store .word 10 15 0x000#12 := rfl
@[gfetch] theorem instrAt_780 : instrAt 780 = .store .word 16 28 0x000#12 := rfl
@[gfetch] theorem instrAt_784 : instrAt 784 = .opImm .add 10 10 0x001#12 := rfl
@[gfetch] theorem instrAt_788 : instrAt 788 = .opImm .add 15 15 0x004#12 := rfl
@[gfetch] theorem instrAt_792 : instrAt 792 = .opImm .add 28 28 0x004#12 := rfl
@[gfetch] theorem instrAt_796 : instrAt 796 = .opImm .add 16 16 0x002#12 := rfl
@[gfetch] theorem instrAt_800 : instrAt 800 = .opImm .add 6 6 0x008#12 := rfl
@[gfetch] theorem instrAt_804 : instrAt 804 = .opImm .add 17 17 0x004#12 := rfl
@[gfetch] theorem instrAt_808 : instrAt 808 = .store .dword 14 6 0xff8#12 := rfl
@[gfetch] theorem instrAt_812 : instrAt 812 = .opImm .add 14 14 0xfff#12 := rfl
@[gfetch] theorem instrAt_816 : instrAt 816 = .opImm .srl 14 14 0x001#12 := rfl
@[gfetch] theorem instrAt_820 : instrAt 820 = .store .word 14 17 0xffc#12 := rfl
@[gfetch] theorem instrAt_824 : instrAt 824 = .jal 0 0x1ffe18#21 := rfl
@[gfetch] theorem instrAt_828 : instrAt 828 = .load .byte false 17 10 0x003#12 := rfl
@[gfetch] theorem instrAt_832 : instrAt 832 = .branch .bne 17 0 0x00d0#13 := rfl
@[gfetch] theorem instrAt_836 : instrAt 836 = .opImm .add 17 0 0x001#12 := rfl
@[gfetch] theorem instrAt_840 : instrAt 840 = .store .byte 17 10 0x003#12 := rfl
@[gfetch] theorem instrAt_844 : instrAt 844 = .opImm .sll 24 15 0x001#12 := rfl
@[gfetch] theorem instrAt_848 : instrAt 848 = .opImm .add 6 0 0x001#12 := rfl
@[gfetch] theorem instrAt_852 : instrAt 852 = .load .dword true 17 2 0x000#12 := rfl
@[gfetch] theorem instrAt_856 : instrAt 856 = .op .add 17 17 16 := rfl
@[gfetch] theorem instrAt_860 : instrAt 860 = .store .byte 6 17 0x000#12 := rfl
@[gfetch] theorem instrAt_864 : instrAt 864 = .op .add 16 16 24 := rfl
@[gfetch] theorem instrAt_868 : instrAt 868 = .branch .bgeu 9 16 0x1ff0#13 := rfl
@[gfetch] theorem instrAt_872 : instrAt 872 = .lui 5 0x00351#20 := rfl
@[gfetch] theorem instrAt_876 : instrAt 876 = .lui 22 0xffecb#20 := rfl
@[gfetch] theorem instrAt_880 : instrAt 880 = .opImm .add 6 5 0x3f0#12 := rfl
@[gfetch] theorem instrAt_884 : instrAt 884 = .op .add 6 6 22 := rfl
@[gfetch] theorem instrAt_888 : instrAt 888 = .opImm .add 30 2 0x020#12 := rfl
@[gfetch] theorem instrAt_892 : instrAt 892 = .lui 23 0xffe31#20 := rfl
@[gfetch] theorem instrAt_896 : instrAt 896 = .op .add 22 6 30 := rfl
@[gfetch] theorem instrAt_900 : instrAt 900 = .opImm .add 6 5 0x3f0#12 := rfl
@[gfetch] theorem instrAt_904 : instrAt 904 = .op .add 6 6 23 := rfl
@[gfetch] theorem instrAt_908 : instrAt 908 = .opImm .add 19 13 0x000#12 := rfl
@[gfetch] theorem instrAt_912 : instrAt 912 = .opImm .add 20 11 0x000#12 := rfl
@[gfetch] theorem instrAt_916 : instrAt 916 = .opImm .add 21 12 0x000#12 := rfl
@[gfetch] theorem instrAt_920 : instrAt 920 = .opImm .add 17 0 0x000#12 := rfl
@[gfetch] theorem instrAt_924 : instrAt 924 = .opImm .add 16 0 0x000#12 := rfl
@[gfetch] theorem instrAt_928 : instrAt 928 = .op .add 23 6 30 := rfl
@[gfetch] theorem instrAt_932 : instrAt 932 = .load .word true 25 21 0x000#12 := rfl
@[gfetch] theorem instrAt_936 : instrAt 936 = .opImm .sll 6 25 0x020#12 := rfl
@[gfetch] theorem instrAt_940 : instrAt 940 = .opImm .srl 6 6 0x020#12 := rfl
@[gfetch] theorem instrAt_944 : instrAt 944 = .op .add 5 7 6 := rfl
@[gfetch] theorem instrAt_948 : instrAt 948 = .load .byte false 5 5 0xc10#12 := rfl
@[gfetch] theorem instrAt_952 : instrAt 952 = .branch .bne 5 0 0x00bc#13 := rfl
@[gfetch] theorem instrAt_956 : instrAt 956 = .op .mul 6 15 6 := rfl
@[gfetch] theorem instrAt_960 : instrAt 960 = .branch .bgeu 9 6 0x005c#13 := rfl
@[gfetch] theorem instrAt_964 : instrAt 964 = .lui 5 0x00351#20 := rfl
@[gfetch] theorem instrAt_968 : instrAt 968 = .lui 19 0xffecb#20 := rfl
@[gfetch] theorem instrAt_972 : instrAt 972 = .opImm .add 6 5 0x3f0#12 := rfl
@[gfetch] theorem instrAt_976 : instrAt 976 = .op .add 6 6 19 := rfl
@[gfetch] theorem instrAt_980 : instrAt 980 = .opImm .add 30 2 0x020#12 := rfl
@[gfetch] theorem instrAt_984 : instrAt 984 = .lui 20 0xffe31#20 := rfl
@[gfetch] theorem instrAt_988 : instrAt 988 = .op .add 19 6 30 := rfl
@[gfetch] theorem instrAt_992 : instrAt 992 = .opImm .add 6 5 0x3f0#12 := rfl
@[gfetch] theorem instrAt_996 : instrAt 996 = .op .add 6 6 20 := rfl
@[gfetch] theorem instrAt_1000 : instrAt 1000 = .op .add 20 6 30 := rfl
@[gfetch] theorem instrAt_1004 : instrAt 1004 = .branch .bltu 17 8 0x009c#13 := rfl
@[gfetch] theorem instrAt_1008 : instrAt 1008 = .op .divu 17 9 15 := rfl
@[gfetch] theorem instrAt_1012 : instrAt 1012 = .opImm .add 5 27 0x000#12 := rfl
@[gfetch] theorem instrAt_1016 : instrAt 1016 = .opImm .add 17 17 0xfff#12 := rfl
@[gfetch] theorem instrAt_1020 : instrAt 1020 = .opImm .or 17 17 0x001#12 := rfl
@[gfetch] theorem instrAt_1024 : instrAt 1024 = .op .mul 8 15 17 := rfl
@[gfetch] theorem instrAt_1028 : instrAt 1028 = .branch .bgeu 17 15 0x0110#13 := rfl
@[gfetch] theorem instrAt_1032 : instrAt 1032 = .opImmWord .add 14 14 0x001#12 := rfl
@[gfetch] theorem instrAt_1036 : instrAt 1036 = .opImm .add 8 16 0x000#12 := rfl
@[gfetch] theorem instrAt_1040 : instrAt 1040 = .opImm .add 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_1044 : instrAt 1044 = .opImm .add 10 10 0x002#12 := rfl
@[gfetch] theorem instrAt_1048 : instrAt 1048 = .jal 0 0x1ffe08#21 := rfl
@[gfetch] theorem instrAt_1052 : instrAt 1052 = .opImm .srl 6 6 0x001#12 := rfl
@[gfetch] theorem instrAt_1056 : instrAt 1056 = .opImm .sll 6 6 0x002#12 := rfl
@[gfetch] theorem instrAt_1060 : instrAt 1060 = .op .add 6 29 6 := rfl
@[gfetch] theorem instrAt_1064 : instrAt 1064 = .load .word true 6 6 0xf58#12 := rfl
@[gfetch] theorem instrAt_1068 : instrAt 1068 = .load .word true 5 20 0x000#12 := rfl
@[gfetch] theorem instrAt_1072 : instrAt 1072 = .opImm .sll 18 16 0x002#12 := rfl
@[gfetch] theorem instrAt_1076 : instrAt 1076 = .opWord .sub 6 6 14 := rfl
@[gfetch] theorem instrAt_1080 : instrAt 1080 = .opImm .sll 30 6 0x020#12 := rfl
@[gfetch] theorem instrAt_1084 : instrAt 1084 = .opImm .srl 6 30 0x01e#12 := rfl
@[gfetch] theorem instrAt_1088 : instrAt 1088 = .op .add 6 28 6 := rfl
@[gfetch] theorem instrAt_1092 : instrAt 1092 = .load .word true 6 6 0x5e0#12 := rfl
@[gfetch] theorem instrAt_1096 : instrAt 1096 = .opWord .add 5 5 14 := rfl
@[gfetch] theorem instrAt_1100 : instrAt 1100 = .op .add 26 28 18 := rfl
@[gfetch] theorem instrAt_1104 : instrAt 1104 = .opWord .sub 5 5 6 := rfl
@[gfetch] theorem instrAt_1108 : instrAt 1108 = .store .word 5 26 0x5e0#12 := rfl
@[gfetch] theorem instrAt_1112 : instrAt 1112 = .load .dword true 5 19 0x000#12 := rfl
@[gfetch] theorem instrAt_1116 : instrAt 1116 = .opImm .sll 6 16 0x003#12 := rfl
@[gfetch] theorem instrAt_1120 : instrAt 1120 = .op .add 6 22 6 := rfl
@[gfetch] theorem instrAt_1124 : instrAt 1124 = .op .add 18 23 18 := rfl
@[gfetch] theorem instrAt_1128 : instrAt 1128 = .store .dword 5 6 0x2f0#12 := rfl
@[gfetch] theorem instrAt_1132 : instrAt 1132 = .store .word 25 18 0xc68#12 := rfl
@[gfetch] theorem instrAt_1136 : instrAt 1136 = .opImm .add 16 16 0x001#12 := rfl
@[gfetch] theorem instrAt_1140 : instrAt 1140 = .opImm .add 17 17 0x001#12 := rfl
@[gfetch] theorem instrAt_1144 : instrAt 1144 = .opImm .add 21 21 0x004#12 := rfl
@[gfetch] theorem instrAt_1148 : instrAt 1148 = .opImm .add 20 20 0x004#12 := rfl
@[gfetch] theorem instrAt_1152 : instrAt 1152 = .opImm .add 19 19 0x008#12 := rfl
@[gfetch] theorem instrAt_1156 : instrAt 1156 = .jal 0 0x1fff20#21 := rfl
@[gfetch] theorem instrAt_1160 : instrAt 1160 = .load .dword true 5 2 0x008#12 := rfl
@[gfetch] theorem instrAt_1164 : instrAt 1164 = .opImm .sll 6 17 0x002#12 := rfl
@[gfetch] theorem instrAt_1168 : instrAt 1168 = .op .add 5 5 6 := rfl
@[gfetch] theorem instrAt_1172 : instrAt 1172 = .load .word true 21 5 0x000#12 := rfl
@[gfetch] theorem instrAt_1176 : instrAt 1176 = .opImm .sll 5 21 0x020#12 := rfl
@[gfetch] theorem instrAt_1180 : instrAt 1180 = .opImm .srl 5 5 0x020#12 := rfl
@[gfetch] theorem instrAt_1184 : instrAt 1184 = .op .add 5 7 5 := rfl
@[gfetch] theorem instrAt_1188 : instrAt 1188 = .load .byte false 5 5 0xc10#12 := rfl
@[gfetch] theorem instrAt_1192 : instrAt 1192 = .branch .bne 5 0 0x0064#13 := rfl
@[gfetch] theorem instrAt_1196 : instrAt 1196 = .load .dword true 18 2 0x010#12 := rfl
@[gfetch] theorem instrAt_1200 : instrAt 1200 = .opImm .sll 5 17 0x003#12 := rfl
@[gfetch] theorem instrAt_1204 : instrAt 1204 = .load .dword true 30 2 0x018#12 := rfl
@[gfetch] theorem instrAt_1208 : instrAt 1208 = .op .add 5 18 5 := rfl
@[gfetch] theorem instrAt_1212 : instrAt 1212 = .load .dword true 22 5 0x000#12 := rfl
@[gfetch] theorem instrAt_1216 : instrAt 1216 = .op .add 6 30 6 := rfl
@[gfetch] theorem instrAt_1220 : instrAt 1220 = .load .word true 5 6 0x000#12 := rfl
@[gfetch] theorem instrAt_1224 : instrAt 1224 = .op .divu 6 22 15 := rfl
@[gfetch] theorem instrAt_1228 : instrAt 1228 = .opImm .sll 18 16 0x002#12 := rfl
@[gfetch] theorem instrAt_1232 : instrAt 1232 = .opWord .add 5 5 14 := rfl
@[gfetch] theorem instrAt_1236 : instrAt 1236 = .op .add 23 28 18 := rfl
@[gfetch] theorem instrAt_1240 : instrAt 1240 = .op .add 18 20 18 := rfl
@[gfetch] theorem instrAt_1244 : instrAt 1244 = .store .word 21 18 0xc68#12 := rfl
@[gfetch] theorem instrAt_1248 : instrAt 1248 = .opImm .add 6 6 0xfff#12 := rfl
@[gfetch] theorem instrAt_1252 : instrAt 1252 = .opImm .srl 6 6 0x001#12 := rfl
@[gfetch] theorem instrAt_1256 : instrAt 1256 = .opImm .sll 6 6 0x002#12 := rfl
@[gfetch] theorem instrAt_1260 : instrAt 1260 = .op .add 6 29 6 := rfl
@[gfetch] theorem instrAt_1264 : instrAt 1264 = .load .word true 6 6 0xf58#12 := rfl
@[gfetch] theorem instrAt_1268 : instrAt 1268 = .opWord .sub 5 5 6 := rfl
@[gfetch] theorem instrAt_1272 : instrAt 1272 = .opImm .sll 6 16 0x003#12 := rfl
@[gfetch] theorem instrAt_1276 : instrAt 1276 = .op .add 6 19 6 := rfl
@[gfetch] theorem instrAt_1280 : instrAt 1280 = .store .word 5 23 0x5e0#12 := rfl
@[gfetch] theorem instrAt_1284 : instrAt 1284 = .store .dword 22 6 0x2f0#12 := rfl
@[gfetch] theorem instrAt_1288 : instrAt 1288 = .opImm .add 16 16 0x001#12 := rfl
@[gfetch] theorem instrAt_1292 : instrAt 1292 = .opImm .add 17 17 0x001#12 := rfl
@[gfetch] theorem instrAt_1296 : instrAt 1296 = .jal 0 0x1ffedc#21 := rfl
@[gfetch] theorem instrAt_1300 : instrAt 1300 = .opImm .srl 6 17 0x001#12 := rfl
@[gfetch] theorem instrAt_1304 : instrAt 1304 = .opImm .sll 6 6 0x002#12 := rfl
@[gfetch] theorem instrAt_1308 : instrAt 1308 = .op .add 6 29 6 := rfl
@[gfetch] theorem instrAt_1312 : instrAt 1312 = .load .word true 18 6 0xf58#12 := rfl
@[gfetch] theorem instrAt_1316 : instrAt 1316 = .opImm .sll 6 5 0x002#12 := rfl
@[gfetch] theorem instrAt_1320 : instrAt 1320 = .opImm .srl 20 8 0x001#12 := rfl
@[gfetch] theorem instrAt_1324 : instrAt 1324 = .op .add 6 31 6 := rfl
@[gfetch] theorem instrAt_1328 : instrAt 1328 = .opWord .sub 18 14 18 := rfl
@[gfetch] theorem instrAt_1332 : instrAt 1332 = .branch .bgeu 5 20 0x0010#13 := rfl
@[gfetch] theorem instrAt_1336 : instrAt 1336 = .opImm .add 17 17 0xffe#12 := rfl
@[gfetch] theorem instrAt_1340 : instrAt 1340 = .op .sub 8 8 24 := rfl
@[gfetch] theorem instrAt_1344 : instrAt 1344 = .jal 0 0x1ffec4#21 := rfl
@[gfetch] theorem instrAt_1348 : instrAt 1348 = .load .word true 19 6 0x000#12 := rfl
@[gfetch] theorem instrAt_1352 : instrAt 1352 = .opImm .add 5 5 0xfff#12 := rfl
@[gfetch] theorem instrAt_1356 : instrAt 1356 = .opImm .add 6 6 0xffc#12 := rfl
@[gfetch] theorem instrAt_1360 : instrAt 1360 = .opWord .add 19 18 19 := rfl
@[gfetch] theorem instrAt_1364 : instrAt 1364 = .store .word 19 6 0x004#12 := rfl
@[gfetch] theorem instrAt_1368 : instrAt 1368 = .jal 0 0x1fffdc#21 := rfl
@[gfetch] theorem instrAt_1372 : instrAt 1372 = .load .word true 16 11 0x000#12 := rfl
@[gfetch] theorem instrAt_1376 : instrAt 1376 = .opImm .add 10 10 0x001#12 := rfl
@[gfetch] theorem instrAt_1380 : instrAt 1380 = .opWord .sub 15 15 16 := rfl
@[gfetch] theorem instrAt_1384 : instrAt 1384 = .jal 0 0x1ffce4#21 := rfl
@[gfetch] theorem instrAt_1388 : instrAt 1388 = .load .word false 31 12 0x004#12 := rfl
@[gfetch] theorem instrAt_1392 : instrAt 1392 = .load .dword true 15 13 0x008#12 := rfl
@[gfetch] theorem instrAt_1396 : instrAt 1396 = .op .divu 15 15 31 := rfl
@[gfetch] theorem instrAt_1400 : instrAt 1400 = .opImm .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_1404 : instrAt 1404 = .opImm .srl 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_1408 : instrAt 1408 = .opImm .sll 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_1412 : instrAt 1412 = .op .add 15 6 15 := rfl
@[gfetch] theorem instrAt_1416 : instrAt 1416 = .load .word true 11 15 0xf58#12 := rfl
@[gfetch] theorem instrAt_1420 : instrAt 1420 = .opWord .sub 11 11 14 := rfl
@[gfetch] theorem instrAt_1424 : instrAt 1424 = .opImm .sll 11 11 0x020#12 := rfl
@[gfetch] theorem instrAt_1428 : instrAt 1428 = .opImm .srl 11 11 0x020#12 := rfl
@[gfetch] theorem instrAt_1432 : instrAt 1432 = .branch .bgeu 16 11 0x1d14#13 := rfl
@[gfetch] theorem instrAt_1436 : instrAt 1436 = .opImm .add 29 16 0x001#12 := rfl
@[gfetch] theorem instrAt_1440 : instrAt 1440 = .opImm .add 28 29 0x000#12 := rfl
@[gfetch] theorem instrAt_1444 : instrAt 1444 = .branch .bgeu 11 28 0x0024#13 := rfl
@[gfetch] theorem instrAt_1448 : instrAt 1448 = .op .sub 11 11 16 := rfl
@[gfetch] theorem instrAt_1452 : instrAt 1452 = .opWord .add 15 30 29 := rfl
@[gfetch] theorem instrAt_1456 : instrAt 1456 = .opWord .mul 15 15 11 := rfl
@[gfetch] theorem instrAt_1460 : instrAt 1460 = .opImm .add 12 12 0x004#12 := rfl
@[gfetch] theorem instrAt_1464 : instrAt 1464 = .opImm .add 13 13 0x008#12 := rfl
@[gfetch] theorem instrAt_1468 : instrAt 1468 = .opImm .add 16 29 0x000#12 := rfl
@[gfetch] theorem instrAt_1472 : instrAt 1472 = .opWord .sub 10 10 15 := rfl
@[gfetch] theorem instrAt_1476 : instrAt 1476 = .jal 0 0x1ffce4#21 := rfl
@[gfetch] theorem instrAt_1480 : instrAt 1480 = .opImm .sll 15 28 0x003#12 := rfl
@[gfetch] theorem instrAt_1484 : instrAt 1484 = .op .add 15 17 15 := rfl
@[gfetch] theorem instrAt_1488 : instrAt 1488 = .load .dword true 15 15 0x000#12 := rfl
@[gfetch] theorem instrAt_1492 : instrAt 1492 = .opImm .add 28 28 0x001#12 := rfl
@[gfetch] theorem instrAt_1496 : instrAt 1496 = .op .divu 15 15 31 := rfl
@[gfetch] theorem instrAt_1500 : instrAt 1500 = .opImm .add 15 15 0xfff#12 := rfl
@[gfetch] theorem instrAt_1504 : instrAt 1504 = .opImm .srl 15 15 0x001#12 := rfl
@[gfetch] theorem instrAt_1508 : instrAt 1508 = .opImm .sll 15 15 0x002#12 := rfl
@[gfetch] theorem instrAt_1512 : instrAt 1512 = .op .add 15 6 15 := rfl
@[gfetch] theorem instrAt_1516 : instrAt 1516 = .load .word true 15 15 0xf58#12 := rfl
@[gfetch] theorem instrAt_1520 : instrAt 1520 = .opWord .add 10 15 10 := rfl
@[gfetch] theorem instrAt_1524 : instrAt 1524 = .jal 0 0x1fffb0#21 := rfl
@[gfetch] theorem instrAt_1528 : instrAt 1528 = .opImm .add 10 0 0x000#12 := rfl
@[gfetch] theorem instrAt_1532 : instrAt 1532 = .jalr 0 1 0x000#12 := rfl

/-! Sign extensions of the immediates not already in the shared `gfetch` set. -/

@[gfetch] theorem lsext_12_1008 : BitVec.signExtend 64 (0x3f0#12) = 1008#64 := by decide
@[gfetch] theorem lsext_12_1048 : BitVec.signExtend 64 (0x418#12) = 1048#64 := by decide
@[gfetch] theorem lsext_12_1056 : BitVec.signExtend 64 (0x420#12) = 1056#64 := by decide
@[gfetch] theorem lsext_12_1064 : BitVec.signExtend 64 (0x428#12) = 1064#64 := by decide
@[gfetch] theorem lsext_12_1072 : BitVec.signExtend 64 (0x430#12) = 1072#64 := by decide
@[gfetch] theorem lsext_12_1080 : BitVec.signExtend 64 (0x438#12) = 1080#64 := by decide
@[gfetch] theorem lsext_12_1088 : BitVec.signExtend 64 (0x440#12) = 1088#64 := by decide
@[gfetch] theorem lsext_12_1096 : BitVec.signExtend 64 (0x448#12) = 1096#64 := by decide
@[gfetch] theorem lsext_12_1104 : BitVec.signExtend 64 (0x450#12) = 1104#64 := by decide
@[gfetch] theorem lsext_12_1112 : BitVec.signExtend 64 (0x458#12) = 1112#64 := by decide
@[gfetch] theorem lsext_12_1120 : BitVec.signExtend 64 (0x460#12) = 1120#64 := by decide
@[gfetch] theorem lsext_12_1128 : BitVec.signExtend 64 (0x468#12) = 1128#64 := by decide
@[gfetch] theorem lsext_12_1136 : BitVec.signExtend 64 (0x470#12) = 1136#64 := by decide
@[gfetch] theorem lsext_12_1144 : BitVec.signExtend 64 (0x478#12) = 1144#64 := by decide
@[gfetch] theorem lsext_12_1152 : BitVec.signExtend 64 (0x480#12) = 1152#64 := by decide
@[gfetch] theorem lsext_12_1504 : BitVec.signExtend 64 (0x5e0#12) = 1504#64 := by decide
@[gfetch] theorem lsext_12_16 : BitVec.signExtend 64 (0x010#12) = 16#64 := by decide
@[gfetch] theorem lsext_12_2944 : BitVec.signExtend 64 (0xb80#12) = 18446744073709550464#64 := by decide
@[gfetch] theorem lsext_12_30 : BitVec.signExtend 64 (0x01e#12) = 30#64 := by decide
@[gfetch] theorem lsext_12_3088 : BitVec.signExtend 64 (0xc10#12) = 18446744073709550608#64 := by decide
@[gfetch] theorem lsext_12_3176 : BitVec.signExtend 64 (0xc68#12) = 18446744073709550696#64 := by decide
@[gfetch] theorem lsext_12_3928 : BitVec.signExtend 64 (0xf58#12) = 18446744073709551448#64 := by decide
@[gfetch] theorem lsext_12_3936 : BitVec.signExtend 64 (0xf60#12) = 18446744073709551456#64 := by decide
@[gfetch] theorem lsext_12_4 : BitVec.signExtend 64 (0x004#12) = 4#64 := by decide
@[gfetch] theorem lsext_12_4092 : BitVec.signExtend 64 (0xffc#12) = 18446744073709551612#64 := by decide
@[gfetch] theorem lsext_12_4094 : BitVec.signExtend 64 (0xffe#12) = 18446744073709551614#64 := by decide
@[gfetch] theorem lsext_12_752 : BitVec.signExtend 64 (0x2f0#12) = 752#64 := by decide
@[gfetch] theorem lsext_12_836 : BitVec.signExtend 64 (0x344#12) = 836#64 := by decide
@[gfetch] theorem lsext_13_100 : BitVec.signExtend 64 (0x0064#13) = 100#64 := by decide
@[gfetch] theorem lsext_13_1452 : BitVec.signExtend 64 (0x05ac#13) = 1452#64 := by decide
@[gfetch] theorem lsext_13_156 : BitVec.signExtend 64 (0x009c#13) = 156#64 := by decide
@[gfetch] theorem lsext_13_16 : BitVec.signExtend 64 (0x0010#13) = 16#64 := by decide
@[gfetch] theorem lsext_13_188 : BitVec.signExtend 64 (0x00bc#13) = 188#64 := by decide
@[gfetch] theorem lsext_13_208 : BitVec.signExtend 64 (0x00d0#13) = 208#64 := by decide
@[gfetch] theorem lsext_13_272 : BitVec.signExtend 64 (0x0110#13) = 272#64 := by decide
@[gfetch] theorem lsext_13_280 : BitVec.signExtend 64 (0x0118#13) = 280#64 := by decide
@[gfetch] theorem lsext_13_436 : BitVec.signExtend 64 (0x01b4#13) = 436#64 := by decide
@[gfetch] theorem lsext_13_592 : BitVec.signExtend 64 (0x0250#13) = 592#64 := by decide
@[gfetch] theorem lsext_13_708 : BitVec.signExtend 64 (0x02c4#13) = 708#64 := by decide
@[gfetch] theorem lsext_13_7444 : BitVec.signExtend 64 (0x1d14#13) = 18446744073709550868#64 := by decide
@[gfetch] theorem lsext_13_780 : BitVec.signExtend 64 (0x030c#13) = 780#64 := by decide
@[gfetch] theorem lsext_13_8176 : BitVec.signExtend 64 (0x1ff0#13) = 18446744073709551600#64 := by decide
@[gfetch] theorem lsext_21_2096356 : BitVec.signExtend 64 (0x1ffce4#21) = 18446744073709550820#64 := by decide
@[gfetch] theorem lsext_21_2096544 : BitVec.signExtend 64 (0x1ffda0#21) = 18446744073709551008#64 := by decide
@[gfetch] theorem lsext_21_2096648 : BitVec.signExtend 64 (0x1ffe08#21) = 18446744073709551112#64 := by decide
@[gfetch] theorem lsext_21_2096664 : BitVec.signExtend 64 (0x1ffe18#21) = 18446744073709551128#64 := by decide
@[gfetch] theorem lsext_21_2096836 : BitVec.signExtend 64 (0x1ffec4#21) = 18446744073709551300#64 := by decide
@[gfetch] theorem lsext_21_2096860 : BitVec.signExtend 64 (0x1ffedc#21) = 18446744073709551324#64 := by decide
@[gfetch] theorem lsext_21_2096928 : BitVec.signExtend 64 (0x1fff20#21) = 18446744073709551392#64 := by decide
@[gfetch] theorem lsext_21_2097116 : BitVec.signExtend 64 (0x1fffdc#21) = 18446744073709551580#64 := by decide
@[gfetch] theorem lsext_21_68 : BitVec.signExtend 64 (0x000044#21) = 68#64 := by decide
@[gfetch] theorem lsext_u0 : BitVec.signExtend 64 (0x00000#20 ++ 0#12) = 0#64 := by decide
@[gfetch] theorem lsext_u1024 : BitVec.signExtend 64 (0x00400#20 ++ 0#12) = 4194304#64 := by decide
@[gfetch] theorem lsext_u1047727 : BitVec.signExtend 64 (0xffcaf#20 ++ 0#12) = 18446744073706074112#64 := by decide
@[gfetch] theorem lsext_u1047804 : BitVec.signExtend 64 (0xffcfc#20 ++ 0#12) = 18446744073706389504#64 := by decide
@[gfetch] theorem lsext_u1047958 : BitVec.signExtend 64 (0xffd96#20 ++ 0#12) = 18446744073707020288#64 := by decide
@[gfetch] theorem lsext_u1048113 : BitVec.signExtend 64 (0xffe31#20 ++ 0#12) = 18446744073707655168#64 := by decide
@[gfetch] theorem lsext_u1048267 : BitVec.signExtend 64 (0xffecb#20 ++ 0#12) = 18446744073708285952#64 := by decide
@[gfetch] theorem lsext_u77 : BitVec.signExtend 64 (0x0004d#20 ++ 0#12) = 315392#64 := by decide
@[gfetch] theorem lsext_u849 : BitVec.signExtend 64 (0x00351#20 ++ 0#12) = 3477504#64 := by decide

theorem fetch_0 : ∀ pc, pc < 400 → pc % 4 = 0 →
    (readBytes image (0 + pc) 4).bind (decode 64) = some (instrAt (0 + pc)) := by
  decide +kernel

theorem fetch_400 : ∀ pc, pc < 400 → pc % 4 = 0 →
    (readBytes image (400 + pc) 4).bind (decode 64) = some (instrAt (400 + pc)) := by
  decide +kernel

theorem fetch_800 : ∀ pc, pc < 400 → pc % 4 = 0 →
    (readBytes image (800 + pc) 4).bind (decode 64) = some (instrAt (800 + pc)) := by
  decide +kernel

theorem fetch_1200 : ∀ pc, pc < 336 → pc % 4 = 0 →
    (readBytes image (1200 + pc) 4).bind (decode 64) = some (instrAt (1200 + pc)) := by
  decide +kernel

theorem fetch (pc : Nat) (h : pc < codeEnd) (h4 : pc % 4 = 0) :
    (readBytes image pc 4).bind (decode 64) = some (instrAt pc) := by
  change pc < 1536 at h
  by_cases h400 : pc < 400
  · have := fetch_0 (pc - 0) (by omega) (by omega)
    rwa [show 0 + (pc - 0) = pc by omega] at this
  by_cases h800 : pc < 800
  · have := fetch_400 (pc - 400) (by omega) (by omega)
    rwa [show 400 + (pc - 400) = pc by omega] at this
  by_cases h1200 : pc < 1200
  · have := fetch_800 (pc - 800) (by omega) (by omega)
    rwa [show 800 + (pc - 800) = pc by omega] at this
  · have := fetch_1200 (pc - 1200) (by omega) (by omega)
    rwa [show 1200 + (pc - 1200) = pc by omega] at this

theorem step_at (x : Regs 64) (pc : Nat) (mem : Array (BitVec 8))
    (out : String) (st : Status) (hmem : Prefix image mem 1536)
    (h : pc < 1536) (h4 : pc % 4 = 0) :
    step ⟨x, BitVec.ofNat 64 pc, mem, [], out, st⟩ =
      exec (instrAt pc) ⟨x, BitVec.ofNat 64 pc, mem, [], out, st⟩ := by
  have hpc : (BitVec.ofNat 64 pc).toNat = pc := by
    rw [BitVec.toNat_ofNat]; omega
  apply step_of_prefix _ image 1536 hmem (by change (BitVec.ofNat 64 pc).toNat + 4 ≤ 1536; omega)
  change (readBytes image (BitVec.ofNat 64 pc).toNat 4).bind (decode 64) = _
  rw [hpc]
  exact fetch _ h h4

end TinyFive.LphaBinary
