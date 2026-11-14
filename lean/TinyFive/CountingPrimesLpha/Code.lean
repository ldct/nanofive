import TinyFive.Machine

/-!
# The machine code of `counting_primes_lpha.py`

`prog` is the image of `counting_primes_lpha.py`: 1261 words of code from address 0, then
read-only data (the table `__clz_tab` used by `__udivdi3`, and unwinding tables). `code` is what
the code words decode to, written out so that the proofs can be read against it; the comments
are the disassembly from `counting_primes_lpha.py`. `decode_prog` proves that `prog` decodes to
`code`. That `prog` is the list of the same name in `counting_primes_lpha.py` is checked by
`counting_primes_lpha_lean_test.py`.

This file is generated from `counting_primes_lpha.py`; the generator is not part of what is
trusted, since `decode_prog` checks its output.
-/

namespace TinyFive.CountingPrimesLpha

/-- The image of `counting_primes_lpha.py`, as produced by its `prog` list. -/
def prog : List (BitVec 32) := [
  0x00400137, 0x1a5000ef, 0x05d00893, 0x00000073, 0x0ff5f593, 0x00c50733, 0x00050793, 0x00060863,
  0x00178793, 0xfeb78fa3, 0xfef71ce3, 0x00008067, 0xb7010113, 0x49212023, 0x47312e23, 0x48112623,
  0x48812423, 0x48912223, 0x47412c23, 0x47512a23, 0x47612823, 0x47712623, 0x47812423, 0x47912223,
  0x47a12023, 0x45b12e23, 0xffcaf2b7, 0x00510133, 0x00058913, 0x00050993, 0x0a0580e3, 0x00198413,
  0x01343a33, 0x012a0a33, 0x01fa1793, 0x00145413, 0x001a5a13, 0x0087e433, 0x0b2a7ee3, 0x00040613,
  0x000a0693, 0x00098513, 0x00090593, 0x6d9000ef, 0x008507b3, 0x014585b3, 0x00a7b533, 0x00b50533,
  0x00040b93, 0x000a0493, 0x01f51713, 0x0017d413, 0x00155a13, 0x00876433, 0xfc9a62e3, 0x01449463,
  0xfb746ee3, 0x001b8413, 0x017437b3, 0x009787b3, 0x01f79793, 0x00145413, 0x0087e433, 0xffcaf537,
  0x00351ab7, 0xc1450513, 0x3f0a8793, 0x0004d637, 0x00a787b3, 0x06010713, 0x34460613, 0x00000593,
  0x00e78533, 0x00040a13, 0xee9ff0ef, 0x02040ee3, 0xffcfcdb7, 0xf58d8d93, 0x3f0a8793, 0x06010713,
  0x01b787b3, 0xffe31d37, 0xc68d0d13, 0x00e78db3, 0x3f0a8793, 0x01a787b3, 0xffecbb37, 0x2f0b0b13,
  0x00e78d33, 0x3f0a8793, 0x016787b3, 0xffd96cb7, 0x5e0c8c93, 0x00e78b33, 0x3f0a8793, 0x019787b3,
  0x00000693, 0x00912423, 0x00e78cb3, 0x00100a93, 0x00000c13, 0x00068493, 0x000a8613, 0x018da023,
  0x015d2023, 0x00048693, 0x00098513, 0x00090593, 0x5d5000ef, 0x00153713, 0xfff50793, 0x40e58733,
  0x01f71713, 0x0017d793, 0x002a8613, 0x00f767b3, 0x00ab2023, 0x01563733, 0x00bb2223, 0x00fca023,
  0x001c0c13, 0x004d8d93, 0x004d0d13, 0x00060a93, 0x009704b3, 0x008b0b13, 0x004c8c93, 0xf9841ee3,
  0x00812483, 0x72048c63, 0x00351837, 0xfffb8693, 0xffcaf737, 0x0016d313, 0xc1470713, 0x3f080693,
  0x00e686b3, 0x001bb793, 0x06010713, 0x00e68733, 0x40f487b3, 0x01f79613, 0x04e12223, 0x0017d793,
  0x04f12a23, 0x04412783, 0xffe31537, 0xc6850513, 0x00378b13, 0x3f080793, 0x00a787b3, 0x06010513,
  0x00a787b3, 0xffecb8b7, 0x2f088e93, 0x02f12423, 0xffcaf8b7, 0x3f080793, 0x00080513, 0x011787b3,
  0x06010813, 0x010788b3, 0xffd967b7, 0x3f050813, 0x00f80833, 0x06010793, 0x00666733, 0x00f807b3,
  0x3f050313, 0xffcfc837, 0x01030333, 0x06010813, 0x3f050f13, 0x01030833, 0xffecb337, 0x006f0f33,
  0xffcfcdb7, 0x06010313, 0xf58d8d93, 0x006f0333, 0x3f050f13, 0x06010f93, 0xffd965b7, 0x01bf0f33,
  0x5e058e13, 0x01ff0db3, 0x3f050f13, 0x3f050513, 0x01cf0f33, 0x01d50533, 0x05c12423, 0x01f50533,
  0x01ff0e33, 0x04e12823, 0x000b0a93, 0x05d12623, 0x00600c13, 0x00000d13, 0x00300613, 0x00000693,
  0x00000993, 0x00900593, 0x00000713, 0x05c12c23, 0x04a12e23, 0x000b8c93, 0x00078b13, 0x000ac503,
  0x1e050263, 0x00260713, 0x00c73633, 0x00d606b3, 0x02e685b3, 0x00070613, 0x004c0713, 0x01873533,
  0x00070c13, 0x002a8a93, 0x01a50d33, 0x02c63733, 0x00159593, 0x00e58733, 0x02c605b3, 0x00e4e663,
  0xfa971ee3, 0xfabcfce3, 0xfff98c93, 0xfffa0793, 0x00351637, 0xffd96737, 0x3f060693, 0x00e686b3,
  0x02fa0533, 0x06010713, 0x00e68733, 0x5e072703, 0x00100693, 0x00170713, 0x02fc85b3, 0x00155513,
  0x5d46fe63, 0xffd967b7, 0x5e078793, 0x3f060693, 0x00f686b3, 0x06010793, 0x00f687b3, 0x00f12423,
  0x00812683, 0x002a1613, 0x00478793, 0x00d60633, 0x0007a683, 0x00478793, 0x40d70733, 0xfef61ae3,
  0x003516b7, 0xffecb7b7, 0x2f078793, 0x3f068613, 0x00f60633, 0x06010793, 0x00f607b3, 0xffe31c37,
  0x00f12a23, 0xc6cc0c13, 0x00b50533, 0x3f068793, 0x00e50d33, 0x018787b3, 0x06010713, 0x00e78c33,
  0x01412783, 0x3f068713, 0x00100493, 0x01078b93, 0xffcfc7b7, 0x00f70733, 0x06010793, 0x00f707b3,
  0x00f12423, 0x01412783, 0xfffc8c93, 0x000d0d93, 0x00878793, 0x00f12a23, 0x000c2903, 0xff8ba503,
  0xffcba583, 0x00000693, 0x00090613, 0x2f9000ef, 0x00812703, 0xfff50793, 0x0017d793, 0x00279793,
  0x00f707b3, 0xf587aa83, 0x413a8ab3, 0x4354f063, 0x00148b13, 0x056ae663, 0x01412783, 0x003a9413,
  0x000b8d13, 0x00f40433, 0x000d2503, 0x004d2583, 0x00090613, 0x00000693, 0x2ad000ef, 0x00812703,
  0xfff50793, 0x0017d793, 0x00279793, 0x00f707b3, 0xf587a783, 0x008d0d13, 0x00fd8db3, 0xfda416e3,
  0x016c87b3, 0x409a8ab3, 0x035787b3, 0x004c0c13, 0x008b8b93, 0x40fd8db3, 0x3b4b0a63, 0x000b0493,
  0xf59ff06f, 0x00100513, 0x00aa8023, 0x02e4ee63, 0x3e970c63, 0x04412783, 0x00100e93, 0x00b78533,
  0x018587b3, 0x00b7b5b3, 0x01a70733, 0x01d50023, 0x00e58733, 0x01850533, 0x00078593, 0x00e4e663,
  0xfe9710e3, 0xfcfcfee3, 0x04812583, 0x003517b7, 0x3f078713, 0x00b70733, 0x06010593, 0x00b70433,
  0x04c12583, 0x3f078713, 0xffe31bb7, 0x3f078793, 0x00b70733, 0x017787b3, 0x06010593, 0x02812283,
  0x00b703b3, 0x00000913, 0x00000f13, 0x00b78bb3, 0x0600006f, 0x309e0063, 0x0003ae03, 0x0043ae83,
  0x0015d593, 0x00259593, 0x00b805b3, 0x2fc72823, 0x2fd72a23, 0xf585a703, 0x00042f83, 0xc6a7a423,
  0x41370733, 0x00271713, 0x00eb0733, 0x5e072703, 0x01f987b3, 0x001f0f13, 0x40e787b3, 0x5ef0a023,
  0x00190913, 0x00428293, 0x00440413, 0x00838393, 0x0002a503, 0x002f1793, 0x003f1713, 0x00a885b3,
  0xc145cf83, 0x00fb00b3, 0x00e30733, 0x00fb87b3, 0xfc0f98e3, 0x02a685b3, 0x02c53e33, 0x01c58e33,
  0x02c505b3, 0xf7c4f8e3, 0x27497a63, 0x02812583, 0x05812503, 0x00291713, 0x00391413, 0x00e50bb3,
  0x00e58933, 0x05c12703, 0x002a1793, 0x00b785b3, 0x00870433, 0x00351737, 0xffe317b7, 0x3f070713,
  0x00f70733, 0x06010793, 0x00f707b3, 0x03512623, 0x03812c23, 0x03a12e23, 0x05b12023, 0x000b8d13,
  0x00090d93, 0x000f0a13, 0x02f12223, 0x01312e23, 0x00058a93, 0x00c12a23, 0x00d12c23, 0x03912823,
  0x02912a23, 0x00040c13, 0x00080b93, 0x02612023, 0x00088913, 0x0100006f, 0x000da783, 0x00f907b3,
  0xc147cf83, 0x002a1493, 0x01412603, 0x01812683, 0x009b0433, 0x060f9c63, 0x000c2303, 0x004c2383,
  0x000d2883, 0x01c12783, 0x00030513, 0x00038593, 0x011789b3, 0x00612423, 0x00712623, 0x069000ef,
  0xfff50793, 0x0017d793, 0x02012703, 0x00279793, 0x00fb87b3, 0xf587a683, 0x003a1793, 0x00f707b3,
  0x02412703, 0x000dac83, 0x00812303, 0x00c12383, 0x40d988b3, 0x00970833, 0xc7982423, 0x5f142023,
  0x2e67a823, 0x2e77aa23, 0x001a0a13, 0x004d8d93, 0x004d0d13, 0x008c0c13, 0xf7ba90e3, 0x02c12a83,
  0x01c12983, 0x01412603, 0x01812683, 0x03012c83, 0x03412483, 0x03812c03, 0x03c12d03, 0x02012303,
  0x04012d83, 0x00090893, 0x000b8813, 0x000c8513, 0x00048593, 0x02612023, 0x01012e23, 0x01112c23,
  0x00c12a23, 0x00d12423, 0x7bc000ef, 0x00812683, 0x00153713, 0x40e58733, 0xfff50513, 0x01412603,
  0x01812883, 0x01c12803, 0x02012303, 0x00156f93, 0x00070393, 0x0ad76c63, 0x12e68c63, 0x02c70733,
  0x05012e03, 0x05412583, 0x03f68533, 0x02cfb2b3, 0x00a70733, 0x02cf8433, 0x005702b3, 0x001fd793,
  0x00279793, 0x00f807b3, 0x01f29713, 0x00145f13, 0x0012d513, 0xf587ae83, 0x01e76f33, 0x02a5ee63,
  0x08b50263, 0x002e1793, 0x41d98eb3, 0x00fd87b3, 0x0007a703, 0x001e3913, 0x412585b3, 0x01d70733,
  0x00e7a023, 0xfffe0e13, 0xffc78793, 0x00a5e663, 0xfeb510e3, 0xfdee7ee3, 0xffef8713, 0x01f73fb3,
  0x418407b3, 0xfff38393, 0x00f43533, 0x41a282b3, 0x007f83b3, 0x00078413, 0x00070f93, 0x40a282b3,
  0x00d3e663, 0xf6769ce3, 0xf6c77ae3, 0x00198993, 0xa95ff06f, 0xd0bcf2e3, 0xd9496ae3, 0x000f0a13,
  0xeedff06f, 0xf9ee70e3, 0xfb1ff06f, 0x000d8d13, 0x003512b7, 0x00510133, 0x48c12083, 0x000d0513,
  0x48812403, 0x48412483, 0x48012903, 0x47c12983, 0x47812a03, 0x47412a83, 0x47012b03, 0x46c12b83,
  0x46812c03, 0x46412c83, 0x46012d03, 0x45c12d83, 0x49010113, 0x00008067, 0x00100793, 0x00000d13,
  0xf4a7ee63, 0xfadff06f, 0xc0bcf6e3, 0xc3dff06f, 0xeccff6e3, 0x00198993, 0xa0dff06f, 0x00800793,
  0x8d77e4e3, 0x00040a13, 0xfff00c93, 0x00000993, 0xa3dff06f, 0x01491463, 0xf5346263, 0x00098b93,
  0x00090493, 0xf98ff06f, 0x8a0490e3, 0x00800793, 0x8977ece3, 0x00351737, 0xffd967b7, 0x3f070713,
  0x00f70733, 0x06010793, 0x00f707b3, 0x5e07a703, 0x00000513, 0x00100593, 0x00170713, 0x00b70733,
  0x00a70d33, 0xf2dff06f, 0xfd010113, 0x02112623, 0x00c00893, 0x00000073, 0x00900793, 0xfd050513,
  0x00a7fa63, 0x00c00893, 0x00000073, 0xfd050513, 0xfea7eae3, 0x00000793, 0x00000593, 0x00900813,
  0x01e7d613, 0x00279713, 0x00259693, 0x00f707b3, 0x00d666b3, 0x00b686b3, 0x00e7b733, 0x00d70733,
  0x00171713, 0x01f7d693, 0x00179793, 0x00f507b3, 0x00e6e733, 0x41f55593, 0x00e585b3, 0x00a7b533,
  0x00b505b3, 0x00c00893, 0x00000073, 0xfd050513, 0xfaa878e3, 0x00078513, 0xdf8ff0ef, 0xccccd5b7,
  0xccccde37, 0x00050693, 0x00000713, 0x00000813, 0x00c10313, 0x00500e93, 0xccd58593, 0xccce0e13,
  0x00900f13, 0x00e687b3, 0x00d7b633, 0x00c787b3, 0x03d7f7b3, 0x00070893, 0x00180813, 0x01030633,
  0x00068293, 0x40f687b3, 0x00f6b533, 0x40a70733, 0x03c78fb3, 0x02b70733, 0x02b7b533, 0x01f70733,
  0x02b787b3, 0x00a70733, 0x01f71513, 0x00175713, 0x0017d793, 0x00f567b3, 0x00279513, 0x00f50533,
  0x00151513, 0x40a68533, 0x03050513, 0xfea60fa3, 0x00078693, 0xf80898e3, 0xf85f66e3, 0x00060793,
  0xfff7c503, 0x00b00893, 0x00000073, 0xfff78793, 0xfef318e3, 0x00a00513, 0x00000073, 0x02c12083,
  0x00000513, 0x03010113, 0x00008067, 0x00050313, 0x00058e13, 0x00000893, 0x0005dc63, 0x00a037b3,
  0x40b00e33, 0x40fe0e33, 0x40a00333, 0xfff00893, 0x0006dc63, 0x00c037b3, 0x40d006b3, 0xfff8c893,
  0x40f686b3, 0x40c00633, 0x00060713, 0x00030813, 0x000e0793, 0x28069c63, 0x00001597, 0x85c58593,
  0x0ece7663, 0x000106b7, 0x0cd67863, 0x10063693, 0x0016b693, 0x00369693, 0x00d65533, 0x00a585b3,
  0x0005c583, 0x02000513, 0x00d586b3, 0x40d505b3, 0x00d50c63, 0x00be17b3, 0x00d356b3, 0x00b61733,
  0x00f6e7b3, 0x00b31833, 0x01075593, 0x02b7de33, 0x01071613, 0x01065613, 0x02b7f7b3, 0x000e0513,
  0x03c60333, 0x01079693, 0x01085793, 0x00d7e7b3, 0x0067fe63, 0x00f707b3, 0xfffe0513, 0x00e7e863,
  0x0067f663, 0xffee0513, 0x00e787b3, 0x406787b3, 0x02b7d333, 0x01081813, 0x01085813, 0x02b7f7b3,
  0x026606b3, 0x01079793, 0x00f86833, 0x00030793, 0x00d87c63, 0x01070833, 0xfff30793, 0x00e86663,
  0x00d87463, 0xffe30793, 0x01051513, 0x00f56533, 0x00000593, 0x0e00006f, 0x01000537, 0x01800693,
  0xf2a67ce3, 0x01000693, 0xf31ff06f, 0x00000693, 0x00060c63, 0x000107b7, 0x0cf67a63, 0x10063693,
  0x0016b693, 0x00369693, 0x00d657b3, 0x00f585b3, 0x0005c783, 0x00d787b3, 0x02000693, 0x40f685b3,
  0x0cf69063, 0x40ce07b3, 0x00100593, 0x01075313, 0x0267deb3, 0x01071613, 0x01065613, 0x01085693,
  0x0267f7b3, 0x000e8513, 0x03d60e33, 0x01079793, 0x00f6e7b3, 0x01c7fe63, 0x00f707b3, 0xfffe8513,
  0x00e7e863, 0x01c7f663, 0xffee8513, 0x00e787b3, 0x41c787b3, 0x0267de33, 0x01081813, 0x01085813,
  0x0267f7b3, 0x03c606b3, 0x01079793, 0x00f86833, 0x000e0793, 0x00d87c63, 0x01070833, 0xfffe0793,
  0x00e86663, 0x00d87463, 0xffee0793, 0x01051513, 0x00f56533, 0x00088a63, 0x00a037b3, 0x40b005b3,
  0x40f585b3, 0x40a00533, 0x00008067, 0x010007b7, 0x01800693, 0xf2f67ae3, 0x01000693, 0xf2dff06f,
  0x00b61733, 0x00fe56b3, 0x01075513, 0x00be1e33, 0x00f357b3, 0x01c7e7b3, 0x02a6de33, 0x01071613,
  0x01065613, 0x00b31833, 0x02a6f6b3, 0x03c60333, 0x01069593, 0x0107d693, 0x00b6e6b3, 0x000e0593,
  0x0066fe63, 0x00d706b3, 0xfffe0593, 0x00e6e863, 0x0066f663, 0xffee0593, 0x00e686b3, 0x406686b3,
  0x02a6d333, 0x01079793, 0x0107d793, 0x02a6f6b3, 0x02660633, 0x01069693, 0x00d7e7b3, 0x00030693,
  0x00c7fe63, 0x00f707b3, 0xfff30693, 0x00e7e863, 0x00c7f663, 0xffe30693, 0x00e787b3, 0x01059593,
  0x40c787b3, 0x00d5e5b3, 0xea5ff06f, 0x18de6663, 0x000107b7, 0x04f6f463, 0x1006b713, 0x00173713,
  0x00371713, 0x00e6d5b3, 0x00000797, 0x5ac78793, 0x00b787b3, 0x0007c783, 0x00e787b3, 0x02000713,
  0x40f705b3, 0x02f71663, 0x00100513, 0xefc6e4e3, 0x00c33533, 0x00153513, 0xeddff06f, 0x010007b7,
  0x01800713, 0xfcf6f0e3, 0x01000713, 0xfb9ff06f, 0x00f65733, 0x00b696b3, 0x00d766b3, 0x00fe5733,
  0x00be1e33, 0x00f357b3, 0x01c7e7b3, 0x0106de13, 0x03c75f33, 0x01069813, 0x01085813, 0x00b61633,
  0x03c77733, 0x03e80eb3, 0x01071513, 0x0107d713, 0x00a76733, 0x000f0513, 0x01d77e63, 0x00e68733,
  0xffff0513, 0x00d76863, 0x01d77663, 0xffef0513, 0x00d70733, 0x41d70733, 0x03c75eb3, 0x01079793,
  0x0107d793, 0x03c77733, 0x03d80833, 0x01071713, 0x00e7e7b3, 0x000e8713, 0x0107fe63, 0x00f687b3,
  0xfffe8713, 0x00d7e863, 0x0107f663, 0xffee8713, 0x00d787b3, 0x01051513, 0x00010eb7, 0x00e56533,
  0xfffe8693, 0x00d57733, 0x410787b3, 0x00d676b3, 0x01055813, 0x01065613, 0x02d70e33, 0x02d806b3,
  0x02c70733, 0x02c80833, 0x00d70633, 0x010e5713, 0x00c70733, 0x00d77463, 0x01d80833, 0x01075693,
  0x010686b3, 0x02d7e663, 0xced794e3, 0x000107b7, 0xfff78793, 0x00f77733, 0x01071713, 0x00fe7e33,
  0x00b31333, 0x01c70733, 0x00000593, 0xdae374e3, 0xfff50513, 0xcbdff06f, 0x00000593, 0x00000513,
  0xd95ff06f, 0x00050893, 0x00058313, 0x00060713, 0x00050813, 0x00058793, 0x28069263, 0x00000597,
  0x41858593, 0x0ec37663, 0x000106b7, 0x0cd67863, 0x10063693, 0x0016b693, 0x00369693, 0x00d65533,
  0x00a585b3, 0x0005c583, 0x02000513, 0x00d586b3, 0x40d505b3, 0x00d50c63, 0x00b317b3, 0x00d8d6b3,
  0x00b61733, 0x00f6e7b3, 0x00b89833, 0x01075593, 0x02b7d333, 0x01071613, 0x01065613, 0x02b7f7b3,
  0x00030513, 0x026608b3, 0x01079693, 0x01085793, 0x00d7e7b3, 0x0117fe63, 0x00f707b3, 0xfff30513,
  0x00e7e863, 0x0117f663, 0xffe30513, 0x00e787b3, 0x411787b3, 0x02b7d8b3, 0x01081813, 0x01085813,
  0x02b7f7b3, 0x031606b3, 0x01079793, 0x00f86833, 0x00088793, 0x00d87c63, 0x01070833, 0xfff88793,
  0x00e86663, 0x00d87463, 0xffe88793, 0x01051513, 0x00f56533, 0x00000593, 0x00008067, 0x01000537,
  0x01800693, 0xf2a67ce3, 0x01000693, 0xf31ff06f, 0x00000693, 0x00060c63, 0x000107b7, 0x0cf67063,
  0x10063693, 0x0016b693, 0x00369693, 0x00d657b3, 0x00f585b3, 0x0005c783, 0x00d787b3, 0x02000693,
  0x40f685b3, 0x0af69663, 0x40c307b3, 0x00100593, 0x01075893, 0x0317de33, 0x01071613, 0x01065613,
  0x01085693, 0x0317f7b3, 0x000e0513, 0x03c60333, 0x01079793, 0x00f6e7b3, 0x0067fe63, 0x00f707b3,
  0xfffe0513, 0x00e7e863, 0x0067f663, 0xffee0513, 0x00e787b3, 0x406787b3, 0x0317d333, 0x01081813,
  0x01085813, 0x0317f7b3, 0x026606b3, 0x01079793, 0x00f86833, 0x00030793, 0x00d87c63, 0x01070833,
  0xfff30793, 0x00e86663, 0x00d87463, 0xffe30793, 0x01051513, 0x00f56533, 0x00008067, 0x010007b7,
  0x01800693, 0xf4f674e3, 0x01000693, 0xf41ff06f, 0x00b61733, 0x00f356b3, 0x01075513, 0x00b31333,
  0x00f8d7b3, 0x0067e7b3, 0x02a6d333, 0x01071613, 0x01065613, 0x00b89833, 0x02a6f6b3, 0x026608b3,
  0x01069593, 0x0107d693, 0x00b6e6b3, 0x00030593, 0x0116fe63, 0x00d706b3, 0xfff30593, 0x00e6e863,
  0x0116f663, 0xffe30593, 0x00e686b3, 0x411686b3, 0x02a6d8b3, 0x01079793, 0x0107d793, 0x02a6f6b3,
  0x03160633, 0x01069693, 0x00d7e7b3, 0x00088693, 0x00c7fe63, 0x00f707b3, 0xfff88693, 0x00e7e863,
  0x00c7f663, 0xffe88693, 0x00e787b3, 0x01059593, 0x40c787b3, 0x00d5e5b3, 0xeb9ff06f, 0x18d5e663,
  0x000107b7, 0x04f6f463, 0x1006b713, 0x00173713, 0x00371713, 0x00e6d5b3, 0x00000797, 0x17c78793,
  0x00b787b3, 0x0007c783, 0x00e787b3, 0x02000713, 0x40f705b3, 0x02f71663, 0x00100513, 0xe066eee3,
  0x00c8b533, 0x00153513, 0x00008067, 0x010007b7, 0x01800713, 0xfcf6f0e3, 0x01000713, 0xfb9ff06f,
  0x00f65733, 0x00b696b3, 0x00d766b3, 0x00f35733, 0x00b31333, 0x00f8d7b3, 0x0067e7b3, 0x0106d313,
  0x02675eb3, 0x01069813, 0x01085813, 0x00b61633, 0x02677733, 0x03d80e33, 0x01071513, 0x0107d713,
  0x00a76733, 0x000e8513, 0x01c77e63, 0x00e68733, 0xfffe8513, 0x00d76863, 0x01c77663, 0xffee8513,
  0x00d70733, 0x41c70733, 0x02675e33, 0x01079793, 0x0107d793, 0x02677733, 0x03c80833, 0x01071713,
  0x00e7e7b3, 0x000e0713, 0x0107fe63, 0x00f687b3, 0xfffe0713, 0x00d7e863, 0x0107f663, 0xffee0713,
  0x00d787b3, 0x01051513, 0x00010e37, 0x00e56533, 0xfffe0693, 0x00d57733, 0x410787b3, 0x00d676b3,
  0x01055813, 0x01065613, 0x02d70333, 0x02d806b3, 0x02c70733, 0x02c80833, 0x00d70633, 0x01035713,
  0x00c70733, 0x00d77463, 0x01c80833, 0x01075693, 0x010686b3, 0x02d7e663, 0xced79ee3, 0x000107b7,
  0xfff78793, 0x00f77733, 0x01071713, 0x00f37333, 0x00b898b3, 0x00670733, 0x00000593, 0xcce8fee3,
  0xfff50513, 0xcd1ff06f, 0x00000593, 0x00000513, 0x00008067, 0x02020100, 0x03030303, 0x04040404,
  0x04040404, 0x05050505, 0x05050505, 0x05050505, 0x05050505, 0x06060606, 0x06060606, 0x06060606,
  0x06060606, 0x06060606, 0x06060606, 0x06060606, 0x06060606, 0x07070707, 0x07070707, 0x07070707,
  0x07070707, 0x07070707, 0x07070707, 0x07070707, 0x07070707, 0x07070707, 0x07070707, 0x07070707,
  0x07070707, 0x07070707, 0x07070707, 0x07070707, 0x07070707, 0x08080808, 0x08080808, 0x08080808,
  0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808,
  0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808,
  0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808,
  0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x08080808, 0x00000010, 0x00000000, 0x00527a03,
  0x01017c01, 0x00020d1b, 0x00000010, 0x00000018, 0xfffff63c, 0x00000478, 0x00000000, 0x00000010,
  0x0000002c, 0xfffffaa0, 0x00000430, 0x00000000]

/-- What the first 1261 words of `prog` decode to. -/
def code : List Instr := [
  -- _start:
  .lui 2 0x400,                      --     0: lui   sp,0x400
  .jal 1 2468,                       --     4: jal   2472 <main>
  .opImm .add 17 0 93,               --     8: li    a7,93
  .ecall,                            --    12: ecall
  -- memset:
  .opImm .and 11 11 255,             --    16: zext.ba1,a1
  .op .add 14 10 12,                 --    20: add   a4,a0,a2
  .opImm .add 15 10 0,               --    24: mv    a5,a0
  .branch .beq 12 0 16,              --    28: beqz  a2,44
  .opImm .add 15 15 1,               --    32: addi  a5,a5,1
  .store .byte 11 15 (-1),           --    36: sb    a1,-1(a5)
  .branch .bne 14 15 (-8),           --    40: bne   a4,a5,32
  .jalr 0 1 0,                       --    44: ret
  -- prime_count(unsigned long long):
  .opImm .add 2 2 (-1168),           --    48: addi  sp,sp,-1168
  .store .word 18 2 1152,            --    52: sw    s2,1152(sp)
  .store .word 19 2 1148,            --    56: sw    s3,1148(sp)
  .store .word 1 2 1164,             --    60: sw    ra,1164(sp)
  .store .word 8 2 1160,             --    64: sw    s0,1160(sp)
  .store .word 9 2 1156,             --    68: sw    s1,1156(sp)
  .store .word 20 2 1144,            --    72: sw    s4,1144(sp)
  .store .word 21 2 1140,            --    76: sw    s5,1140(sp)
  .store .word 22 2 1136,            --    80: sw    s6,1136(sp)
  .store .word 23 2 1132,            --    84: sw    s7,1132(sp)
  .store .word 24 2 1128,            --    88: sw    s8,1128(sp)
  .store .word 25 2 1124,            --    92: sw    s9,1124(sp)
  .store .word 26 2 1120,            --    96: sw    s10,1120(sp)
  .store .word 27 2 1116,            --   100: sw    s11,1116(sp)
  .lui 5 0xffcaf,                    --   104: lui   t0,0xffcaf
  .op .add 2 2 5,                    --   108: add   sp,sp,t0
  .opImm .add 18 11 0,               --   112: mv    s2,a1
  .opImm .add 19 10 0,               --   116: mv    s3,a0
  .branch .beq 11 0 2208,            --   120: beqz  a1,2328
  .opImm .add 8 19 1,                --   124: addi  s0,s3,1
  .op .sltu 20 8 19,                 --   128: sltu  s4,s0,s3
  .op .add 20 20 18,                 --   132: add   s4,s4,s2
  .opImm .sll 15 20 31,              --   136: slli  a5,s4,0x1f
  .opImm .srl 8 8 1,                 --   140: srli  s0,s0,0x1
  .opImm .srl 20 20 1,               --   144: srli  s4,s4,0x1
  .op .or 8 15 8,                    --   148: or    s0,a5,s0
  .branch .bgeu 20 18 2236,          --   152: bgeu  s4,s2,2388
  .opImm .add 12 8 0,                --   156: mv    a2,s0
  .opImm .add 13 20 0,               --   160: mv    a3,s4
  .opImm .add 10 19 0,               --   164: mv    a0,s3
  .opImm .add 11 18 0,               --   168: mv    a1,s2
  .jal 1 3800,                       --   172: jal   3972 <__udivdi3>
  .op .add 15 10 8,                  --   176: add   a5,a0,s0
  .op .add 11 11 20,                 --   180: add   a1,a1,s4
  .op .sltu 10 15 10,                --   184: sltu  a0,a5,a0
  .op .add 10 10 11,                 --   188: add   a0,a0,a1
  .opImm .add 23 8 0,                --   192: mv    s7,s0
  .opImm .add 9 20 0,                --   196: mv    s1,s4
  .opImm .sll 14 10 31,              --   200: slli  a4,a0,0x1f
  .opImm .srl 8 15 1,                --   204: srli  s0,a5,0x1
  .opImm .srl 20 10 1,               --   208: srli  s4,a0,0x1
  .op .or 8 14 8,                    --   212: or    s0,a4,s0
  .branch .bltu 20 9 (-60),          --   216: bltu  s4,s1,156
  .branch .bne 9 20 8,               --   220: bne   s1,s4,228
  .branch .bltu 8 23 (-68),          --   224: bltu  s0,s7,156
  .opImm .add 8 23 1,                --   228: addi  s0,s7,1
  .op .sltu 15 8 23,                 --   232: sltu  a5,s0,s7
  .op .add 15 15 9,                  --   236: add   a5,a5,s1
  .opImm .sll 15 15 31,              --   240: slli  a5,a5,0x1f
  .opImm .srl 8 8 1,                 --   244: srli  s0,s0,0x1
  .op .or 8 15 8,                    --   248: or    s0,a5,s0
  .lui 10 0xffcaf,                   --   252: lui   a0,0xffcaf
  .lui 21 0x351,                     --   256: lui   s5,0x351
  .opImm .add 10 10 (-1004),         --   260: addi  a0,a0,-1004
  .opImm .add 15 21 1008,            --   264: addi  a5,s5,1008
  .lui 12 0x4d,                      --   268: lui   a2,0x4d
  .op .add 15 15 10,                 --   272: add   a5,a5,a0
  .opImm .add 14 2 96,               --   276: addi  a4,sp,96
  .opImm .add 12 12 836,             --   280: addi  a2,a2,836
  .opImm .add 11 0 0,                --   284: li    a1,0
  .op .add 10 15 14,                 --   288: add   a0,a5,a4
  .opImm .add 20 8 0,                --   292: mv    s4,s0
  .jal 1 (-280),                     --   296: jal   16 <memset>
  .branch .beq 8 0 2108,             --   300: beqz  s0,2408
  .lui 27 0xffcfc,                   --   304: lui   s11,0xffcfc
  .opImm .add 27 27 (-168),          --   308: addi  s11,s11,-168
  .opImm .add 15 21 1008,            --   312: addi  a5,s5,1008
  .opImm .add 14 2 96,               --   316: addi  a4,sp,96
  .op .add 15 15 27,                 --   320: add   a5,a5,s11
  .lui 26 0xffe31,                   --   324: lui   s10,0xffe31
  .opImm .add 26 26 (-920),          --   328: addi  s10,s10,-920
  .op .add 27 15 14,                 --   332: add   s11,a5,a4
  .opImm .add 15 21 1008,            --   336: addi  a5,s5,1008
  .op .add 15 15 26,                 --   340: add   a5,a5,s10
  .lui 22 0xffecb,                   --   344: lui   s6,0xffecb
  .opImm .add 22 22 752,             --   348: addi  s6,s6,752
  .op .add 26 15 14,                 --   352: add   s10,a5,a4
  .opImm .add 15 21 1008,            --   356: addi  a5,s5,1008
  .op .add 15 15 22,                 --   360: add   a5,a5,s6
  .lui 25 0xffd96,                   --   364: lui   s9,0xffd96
  .opImm .add 25 25 1504,            --   368: addi  s9,s9,1504
  .op .add 22 15 14,                 --   372: add   s6,a5,a4
  .opImm .add 15 21 1008,            --   376: addi  a5,s5,1008
  .op .add 15 15 25,                 --   380: add   a5,a5,s9
  .opImm .add 13 0 0,                --   384: li    a3,0
  .store .word 9 2 8,                --   388: sw    s1,8(sp)
  .op .add 25 15 14,                 --   392: add   s9,a5,a4
  .opImm .add 21 0 1,                --   396: li    s5,1
  .opImm .add 24 0 0,                --   400: li    s8,0
  .opImm .add 9 13 0,                --   404: mv    s1,a3
  .opImm .add 12 21 0,               --   408: mv    a2,s5
  .store .word 24 27 0,              --   412: sw    s8,0(s11)
  .store .word 21 26 0,              --   416: sw    s5,0(s10)
  .opImm .add 13 9 0,                --   420: mv    a3,s1
  .opImm .add 10 19 0,               --   424: mv    a0,s3
  .opImm .add 11 18 0,               --   428: mv    a1,s2
  .jal 1 3540,                       --   432: jal   3972 <__udivdi3>
  .opImm .sltu 14 10 1,              --   436: seqz  a4,a0
  .opImm .add 15 10 (-1),            --   440: addi  a5,a0,-1
  .op .sub 14 11 14,                 --   444: sub   a4,a1,a4
  .opImm .sll 14 14 31,              --   448: slli  a4,a4,0x1f
  .opImm .srl 15 15 1,               --   452: srli  a5,a5,0x1
  .opImm .add 12 21 2,               --   456: addi  a2,s5,2
  .op .or 15 14 15,                  --   460: or    a5,a4,a5
  .store .word 10 22 0,              --   464: sw    a0,0(s6)
  .op .sltu 14 12 21,                --   468: sltu  a4,a2,s5
  .store .word 11 22 4,              --   472: sw    a1,4(s6)
  .store .word 15 25 0,              --   476: sw    a5,0(s9)
  .opImm .add 24 24 1,               --   480: addi  s8,s8,1
  .opImm .add 27 27 4,               --   484: addi  s11,s11,4
  .opImm .add 26 26 4,               --   488: addi  s10,s10,4
  .opImm .add 21 12 0,               --   492: mv    s5,a2
  .op .add 9 14 9,                   --   496: add   s1,a4,s1
  .opImm .add 22 22 8,               --   500: addi  s6,s6,8
  .opImm .add 25 25 4,               --   504: addi  s9,s9,4
  .branch .bne 8 24 (-100),          --   508: bne   s0,s8,408
  .load .word true 9 2 8,            --   512: lw    s1,8(sp)
  .branch .beq 9 0 1848,             --   516: beqz  s1,2364
  .lui 16 0x351,                     --   520: lui   a6,0x351
  .opImm .add 13 23 (-1),            --   524: addi  a3,s7,-1
  .lui 14 0xffcaf,                   --   528: lui   a4,0xffcaf
  .opImm .srl 6 13 1,                --   532: srli  t1,a3,0x1
  .opImm .add 14 14 (-1004),         --   536: addi  a4,a4,-1004
  .opImm .add 13 16 1008,            --   540: addi  a3,a6,1008
  .op .add 13 13 14,                 --   544: add   a3,a3,a4
  .opImm .sltu 15 23 1,              --   548: seqz  a5,s7
  .opImm .add 14 2 96,               --   552: addi  a4,sp,96
  .op .add 14 13 14,                 --   556: add   a4,a3,a4
  .op .sub 15 9 15,                  --   560: sub   a5,s1,a5
  .opImm .sll 12 15 31,              --   564: slli  a2,a5,0x1f
  .store .word 14 2 68,              --   568: sw    a4,68(sp)
  .opImm .srl 15 15 1,               --   572: srli  a5,a5,0x1
  .store .word 15 2 84,              --   576: sw    a5,84(sp)
  .load .word true 15 2 68,          --   580: lw    a5,68(sp)
  .lui 10 0xffe31,                   --   584: lui   a0,0xffe31
  .opImm .add 10 10 (-920),          --   588: addi  a0,a0,-920
  .opImm .add 22 15 3,               --   592: addi  s6,a5,3
  .opImm .add 15 16 1008,            --   596: addi  a5,a6,1008
  .op .add 15 15 10,                 --   600: add   a5,a5,a0
  .opImm .add 10 2 96,               --   604: addi  a0,sp,96
  .op .add 15 15 10,                 --   608: add   a5,a5,a0
  .lui 17 0xffecb,                   --   612: lui   a7,0xffecb
  .opImm .add 29 17 752,             --   616: addi  t4,a7,752
  .store .word 15 2 40,              --   620: sw    a5,40(sp)
  .lui 17 0xffcaf,                   --   624: lui   a7,0xffcaf
  .opImm .add 15 16 1008,            --   628: addi  a5,a6,1008
  .opImm .add 10 16 0,               --   632: mv    a0,a6
  .op .add 15 15 17,                 --   636: add   a5,a5,a7
  .opImm .add 16 2 96,               --   640: addi  a6,sp,96
  .op .add 17 15 16,                 --   644: add   a7,a5,a6
  .lui 15 0xffd96,                   --   648: lui   a5,0xffd96
  .opImm .add 16 10 1008,            --   652: addi  a6,a0,1008
  .op .add 16 16 15,                 --   656: add   a6,a6,a5
  .opImm .add 15 2 96,               --   660: addi  a5,sp,96
  .op .or 14 12 6,                   --   664: or    a4,a2,t1
  .op .add 15 16 15,                 --   668: add   a5,a6,a5
  .opImm .add 6 10 1008,             --   672: addi  t1,a0,1008
  .lui 16 0xffcfc,                   --   676: lui   a6,0xffcfc
  .op .add 6 6 16,                   --   680: add   t1,t1,a6
  .opImm .add 16 2 96,               --   684: addi  a6,sp,96
  .opImm .add 30 10 1008,            --   688: addi  t5,a0,1008
  .op .add 16 6 16,                  --   692: add   a6,t1,a6
  .lui 6 0xffecb,                    --   696: lui   t1,0xffecb
  .op .add 30 30 6,                  --   700: add   t5,t5,t1
  .lui 27 0xffcfc,                   --   704: lui   s11,0xffcfc
  .opImm .add 6 2 96,                --   708: addi  t1,sp,96
  .opImm .add 27 27 (-168),          --   712: addi  s11,s11,-168
  .op .add 6 30 6,                   --   716: add   t1,t5,t1
  .opImm .add 30 10 1008,            --   720: addi  t5,a0,1008
  .opImm .add 31 2 96,               --   724: addi  t6,sp,96
  .lui 11 0xffd96,                   --   728: lui   a1,0xffd96
  .op .add 30 30 27,                 --   732: add   t5,t5,s11
  .opImm .add 28 11 1504,            --   736: addi  t3,a1,1504
  .op .add 27 30 31,                 --   740: add   s11,t5,t6
  .opImm .add 30 10 1008,            --   744: addi  t5,a0,1008
  .opImm .add 10 10 1008,            --   748: addi  a0,a0,1008
  .op .add 30 30 28,                 --   752: add   t5,t5,t3
  .op .add 10 10 29,                 --   756: add   a0,a0,t4
  .store .word 28 2 72,              --   760: sw    t3,72(sp)
  .op .add 10 10 31,                 --   764: add   a0,a0,t6
  .op .add 28 30 31,                 --   768: add   t3,t5,t6
  .store .word 14 2 80,              --   772: sw    a4,80(sp)
  .opImm .add 21 22 0,               --   776: mv    s5,s6
  .store .word 29 2 76,              --   780: sw    t4,76(sp)
  .opImm .add 24 0 6,                --   784: li    s8,6
  .opImm .add 26 0 0,                --   788: li    s10,0
  .opImm .add 12 0 3,                --   792: li    a2,3
  .opImm .add 13 0 0,                --   796: li    a3,0
  .opImm .add 19 0 0,                --   800: li    s3,0
  .opImm .add 11 0 9,                --   804: li    a1,9
  .opImm .add 14 0 0,                --   808: li    a4,0
  .store .word 28 2 88,              --   812: sw    t3,88(sp)
  .store .word 10 2 92,              --   816: sw    a0,92(sp)
  .opImm .add 25 23 0,               --   820: mv    s9,s7
  .opImm .add 22 15 0,               --   824: mv    s6,a5
  .load .byte false 10 21 0,         --   828: lbu   a0,0(s5)
  .branch .beq 10 0 484,             --   832: beqz  a0,1316
  .opImm .add 14 12 2,               --   836: addi  a4,a2,2
  .op .sltu 12 14 12,                --   840: sltu  a2,a4,a2
  .op .add 13 12 13,                 --   844: add   a3,a2,a3
  .mulOp .mul 11 13 14,              --   848: mul   a1,a3,a4
  .opImm .add 12 14 0,               --   852: mv    a2,a4
  .opImm .add 14 24 4,               --   856: addi  a4,s8,4
  .op .sltu 10 14 24,                --   860: sltu  a0,a4,s8
  .opImm .add 24 14 0,               --   864: mv    s8,a4
  .opImm .add 21 21 2,               --   868: addi  s5,s5,2
  .op .add 26 10 26,                 --   872: add   s10,a0,s10
  .mulOp .mulhu 14 12 12,            --   876: mulhu a4,a2,a2
  .opImm .sll 11 11 1,               --   880: slli  a1,a1,0x1
  .op .add 14 11 14,                 --   884: add   a4,a1,a4
  .mulOp .mul 11 12 12,              --   888: mul   a1,a2,a2
  .branch .bltu 9 14 12,             --   892: bltu  s1,a4,904
  .branch .bne 14 9 (-68),           --   896: bne   a4,s1,828
  .branch .bgeu 25 11 (-72),         --   900: bgeu  s9,a1,828
  .opImm .add 25 19 (-1),            --   904: addi  s9,s3,-1
  .opImm .add 15 20 (-1),            --   908: addi  a5,s4,-1
  .lui 12 0x351,                     --   912: lui   a2,0x351
  .lui 14 0xffd96,                   --   916: lui   a4,0xffd96
  .opImm .add 13 12 1008,            --   920: addi  a3,a2,1008
  .op .add 13 13 14,                 --   924: add   a3,a3,a4
  .mulOp .mul 10 20 15,              --   928: mul   a0,s4,a5
  .opImm .add 14 2 96,               --   932: addi  a4,sp,96
  .op .add 14 13 14,                 --   936: add   a4,a3,a4
  .load .word true 14 14 1504,       --   940: lw    a4,1504(a4)
  .opImm .add 13 0 1,                --   944: li    a3,1
  .opImm .add 14 14 1,               --   948: addi  a4,a4,1
  .mulOp .mul 11 25 15,              --   952: mul   a1,s9,a5
  .opImm .srl 10 10 1,               --   956: srli  a0,a0,0x1
  .branch .bgeu 13 20 1500,          --   960: bgeu  a3,s4,2460
  .lui 15 0xffd96,                   --   964: lui   a5,0xffd96
  .opImm .add 15 15 1504,            --   968: addi  a5,a5,1504
  .opImm .add 13 12 1008,            --   972: addi  a3,a2,1008
  .op .add 13 13 15,                 --   976: add   a3,a3,a5
  .opImm .add 15 2 96,               --   980: addi  a5,sp,96
  .op .add 15 13 15,                 --   984: add   a5,a3,a5
  .store .word 15 2 8,               --   988: sw    a5,8(sp)
  .load .word true 13 2 8,           --   992: lw    a3,8(sp)
  .opImm .sll 12 20 2,               --   996: slli  a2,s4,0x2
  .opImm .add 15 15 4,               --  1000: addi  a5,a5,4
  .op .add 12 12 13,                 --  1004: add   a2,a2,a3
  .load .word true 13 15 0,          --  1008: lw    a3,0(a5)
  .opImm .add 15 15 4,               --  1012: addi  a5,a5,4
  .op .sub 14 14 13,                 --  1016: sub   a4,a4,a3
  .branch .bne 12 15 (-12),          --  1020: bne   a2,a5,1008
  .lui 13 0x351,                     --  1024: lui   a3,0x351
  .lui 15 0xffecb,                   --  1028: lui   a5,0xffecb
  .opImm .add 15 15 752,             --  1032: addi  a5,a5,752
  .opImm .add 12 13 1008,            --  1036: addi  a2,a3,1008
  .op .add 12 12 15,                 --  1040: add   a2,a2,a5
  .opImm .add 15 2 96,               --  1044: addi  a5,sp,96
  .op .add 15 12 15,                 --  1048: add   a5,a2,a5
  .lui 24 0xffe31,                   --  1052: lui   s8,0xffe31
  .store .word 15 2 20,              --  1056: sw    a5,20(sp)
  .opImm .add 24 24 (-916),          --  1060: addi  s8,s8,-916
  .op .add 10 10 11,                 --  1064: add   a0,a0,a1
  .opImm .add 15 13 1008,            --  1068: addi  a5,a3,1008
  .op .add 26 10 14,                 --  1072: add   s10,a0,a4
  .op .add 15 15 24,                 --  1076: add   a5,a5,s8
  .opImm .add 14 2 96,               --  1080: addi  a4,sp,96
  .op .add 24 15 14,                 --  1084: add   s8,a5,a4
  .load .word true 15 2 20,          --  1088: lw    a5,20(sp)
  .opImm .add 14 13 1008,            --  1092: addi  a4,a3,1008
  .opImm .add 9 0 1,                 --  1096: li    s1,1
  .opImm .add 23 15 16,              --  1100: addi  s7,a5,16
  .lui 15 0xffcfc,                   --  1104: lui   a5,0xffcfc
  .op .add 14 14 15,                 --  1108: add   a4,a4,a5
  .opImm .add 15 2 96,               --  1112: addi  a5,sp,96
  .op .add 15 14 15,                 --  1116: add   a5,a4,a5
  .store .word 15 2 8,               --  1120: sw    a5,8(sp)
  .load .word true 15 2 20,          --  1124: lw    a5,20(sp)
  .opImm .add 25 25 (-1),            --  1128: addi  s9,s9,-1
  .opImm .add 27 26 0,               --  1132: mv    s11,s10
  .opImm .add 15 15 8,               --  1136: addi  a5,a5,8
  .store .word 15 2 20,              --  1140: sw    a5,20(sp)
  .load .word true 18 24 0,          --  1144: lw    s2,0(s8)
  .load .word true 10 23 (-8),       --  1148: lw    a0,-8(s7)
  .load .word true 11 23 (-4),       --  1152: lw    a1,-4(s7)
  .opImm .add 13 0 0,                --  1156: li    a3,0
  .opImm .add 12 18 0,               --  1160: mv    a2,s2
  .jal 1 2808,                       --  1164: jal   3972 <__udivdi3>
  .load .word true 14 2 8,           --  1168: lw    a4,8(sp)
  .opImm .add 15 10 (-1),            --  1172: addi  a5,a0,-1
  .opImm .srl 15 15 1,               --  1176: srli  a5,a5,0x1
  .opImm .sll 15 15 2,               --  1180: slli  a5,a5,0x2
  .op .add 15 14 15,                 --  1184: add   a5,a4,a5
  .load .word true 21 15 (-168),     --  1188: lw    s5,-168(a5)
  .op .sub 21 21 19,                 --  1192: sub   s5,s5,s3
  .branch .bgeu 9 21 1056,           --  1196: bgeu  s1,s5,2252
  .opImm .add 22 9 1,                --  1200: addi  s6,s1,1
  .branch .bltu 21 22 76,            --  1204: bltu  s5,s6,1280
  .load .word true 15 2 20,          --  1208: lw    a5,20(sp)
  .opImm .sll 8 21 3,                --  1212: slli  s0,s5,0x3
  .opImm .add 26 23 0,               --  1216: mv    s10,s7
  .op .add 8 8 15,                   --  1220: add   s0,s0,a5
  .load .word true 10 26 0,          --  1224: lw    a0,0(s10)
  .load .word true 11 26 4,          --  1228: lw    a1,4(s10)
  .opImm .add 12 18 0,               --  1232: mv    a2,s2
  .opImm .add 13 0 0,                --  1236: li    a3,0
  .jal 1 2732,                       --  1240: jal   3972 <__udivdi3>
  .load .word true 14 2 8,           --  1244: lw    a4,8(sp)
  .opImm .add 15 10 (-1),            --  1248: addi  a5,a0,-1
  .opImm .srl 15 15 1,               --  1252: srli  a5,a5,0x1
  .opImm .sll 15 15 2,               --  1256: slli  a5,a5,0x2
  .op .add 15 14 15,                 --  1260: add   a5,a4,a5
  .load .word true 15 15 (-168),     --  1264: lw    a5,-168(a5)
  .opImm .add 26 26 8,               --  1268: addi  s10,s10,8
  .op .add 27 27 15,                 --  1272: add   s11,s11,a5
  .branch .bne 8 26 (-52),           --  1276: bne   s0,s10,1224
  .op .add 15 25 22,                 --  1280: add   a5,s9,s6
  .op .sub 21 21 9,                  --  1284: sub   s5,s5,s1
  .mulOp .mul 15 15 21,              --  1288: mul   a5,a5,s5
  .opImm .add 24 24 4,               --  1292: addi  s8,s8,4
  .opImm .add 23 23 8,               --  1296: addi  s7,s7,8
  .op .sub 27 27 15,                 --  1300: sub   s11,s11,a5
  .branch .beq 22 20 948,            --  1304: beq   s6,s4,2252
  .opImm .add 9 22 0,                --  1308: mv    s1,s6
  .jal 0 (-168),                     --  1312: j     1144
  .opImm .add 10 0 1,                --  1316: li    a0,1
  .store .byte 10 21 0,              --  1320: sb    a0,0(s5)
  .branch .bltu 9 14 60,             --  1324: bltu  s1,a4,1384
  .branch .beq 14 9 1016,            --  1328: beq   a4,s1,2344
  .load .word true 15 2 68,          --  1332: lw    a5,68(sp)
  .opImm .add 29 0 1,                --  1336: li    t4,1
  .op .add 10 15 11,                 --  1340: add   a0,a5,a1
  .op .add 15 11 24,                 --  1344: add   a5,a1,s8
  .op .sltu 11 15 11,                --  1348: sltu  a1,a5,a1
  .op .add 14 14 26,                 --  1352: add   a4,a4,s10
  .store .byte 29 10 0,              --  1356: sb    t4,0(a0)
  .op .add 14 11 14,                 --  1360: add   a4,a1,a4
  .op .add 10 10 24,                 --  1364: add   a0,a0,s8
  .opImm .add 11 15 0,               --  1368: mv    a1,a5
  .branch .bltu 9 14 12,             --  1372: bltu  s1,a4,1384
  .branch .bne 14 9 (-32),           --  1376: bne   a4,s1,1344
  .branch .bgeu 25 15 (-36),         --  1380: bgeu  s9,a5,1344
  .load .word true 11 2 72,          --  1384: lw    a1,72(sp)
  .lui 15 0x351,                     --  1388: lui   a5,0x351
  .opImm .add 14 15 1008,            --  1392: addi  a4,a5,1008
  .op .add 14 14 11,                 --  1396: add   a4,a4,a1
  .opImm .add 11 2 96,               --  1400: addi  a1,sp,96
  .op .add 8 14 11,                  --  1404: add   s0,a4,a1
  .load .word true 11 2 76,          --  1408: lw    a1,76(sp)
  .opImm .add 14 15 1008,            --  1412: addi  a4,a5,1008
  .lui 23 0xffe31,                   --  1416: lui   s7,0xffe31
  .opImm .add 15 15 1008,            --  1420: addi  a5,a5,1008
  .op .add 14 14 11,                 --  1424: add   a4,a4,a1
  .op .add 15 15 23,                 --  1428: add   a5,a5,s7
  .opImm .add 11 2 96,               --  1432: addi  a1,sp,96
  .load .word true 5 2 40,           --  1436: lw    t0,40(sp)
  .op .add 7 14 11,                  --  1440: add   t2,a4,a1
  .opImm .add 18 0 0,                --  1444: li    s2,0
  .opImm .add 30 0 0,                --  1448: li    t5,0
  .op .add 23 15 11,                 --  1452: add   s7,a5,a1
  .jal 0 96,                         --  1456: j     1552
  .branch .beq 28 9 768,             --  1460: beq   t3,s1,2228
  .load .word true 28 7 0,           --  1464: lw    t3,0(t2)
  .load .word true 29 7 4,           --  1468: lw    t4,4(t2)
  .opImm .srl 11 11 1,               --  1472: srli  a1,a1,0x1
  .opImm .sll 11 11 2,               --  1476: slli  a1,a1,0x2
  .op .add 11 16 11,                 --  1480: add   a1,a6,a1
  .store .word 28 14 752,            --  1484: sw    t3,752(a4)
  .store .word 29 14 756,            --  1488: sw    t4,756(a4)
  .load .word true 14 11 (-168),     --  1492: lw    a4,-168(a1)
  .load .word true 31 8 0,           --  1496: lw    t6,0(s0)
  .store .word 10 15 (-920),         --  1500: sw    a0,-920(a5)
  .op .sub 14 14 19,                 --  1504: sub   a4,a4,s3
  .opImm .sll 14 14 2,               --  1508: slli  a4,a4,0x2
  .op .add 14 22 14,                 --  1512: add   a4,s6,a4
  .load .word true 14 14 1504,       --  1516: lw    a4,1504(a4)
  .op .add 15 19 31,                 --  1520: add   a5,s3,t6
  .opImm .add 30 30 1,               --  1524: addi  t5,t5,1
  .op .sub 15 15 14,                 --  1528: sub   a5,a5,a4
  .store .word 15 1 1504,            --  1532: sw    a5,1504(ra)
  .opImm .add 18 18 1,               --  1536: addi  s2,s2,1
  .opImm .add 5 5 4,                 --  1540: addi  t0,t0,4
  .opImm .add 8 8 4,                 --  1544: addi  s0,s0,4
  .opImm .add 7 7 8,                 --  1548: addi  t2,t2,8
  .load .word true 10 5 0,           --  1552: lw    a0,0(t0)
  .opImm .sll 15 30 2,               --  1556: slli  a5,t5,0x2
  .opImm .sll 14 30 3,               --  1560: slli  a4,t5,0x3
  .op .add 11 17 10,                 --  1564: add   a1,a7,a0
  .load .byte false 31 11 (-1004),   --  1568: lbu   t6,-1004(a1)
  .op .add 1 22 15,                  --  1572: add   ra,s6,a5
  .op .add 14 6 14,                  --  1576: add   a4,t1,a4
  .op .add 15 23 15,                 --  1580: add   a5,s7,a5
  .branch .bne 31 0 (-48),           --  1584: bnez  t6,1536
  .mulOp .mul 11 13 10,              --  1588: mul   a1,a3,a0
  .mulOp .mulhu 28 10 12,            --  1592: mulhu t3,a0,a2
  .op .add 28 11 28,                 --  1596: add   t3,a1,t3
  .mulOp .mul 11 10 12,              --  1600: mul   a1,a0,a2
  .branch .bgeu 9 28 (-144),         --  1604: bgeu  s1,t3,1460
  .branch .bgeu 18 20 628,           --  1608: bgeu  s2,s4,2236
  .load .word true 11 2 40,          --  1612: lw    a1,40(sp)
  .load .word true 10 2 88,          --  1616: lw    a0,88(sp)
  .opImm .sll 14 18 2,               --  1620: slli  a4,s2,0x2
  .opImm .sll 8 18 3,                --  1624: slli  s0,s2,0x3
  .op .add 23 10 14,                 --  1628: add   s7,a0,a4
  .op .add 18 11 14,                 --  1632: add   s2,a1,a4
  .load .word true 14 2 92,          --  1636: lw    a4,92(sp)
  .opImm .sll 15 20 2,               --  1640: slli  a5,s4,0x2
  .op .add 11 15 11,                 --  1644: add   a1,a5,a1
  .op .add 8 14 8,                   --  1648: add   s0,a4,s0
  .lui 14 0x351,                     --  1652: lui   a4,0x351
  .lui 15 0xffe31,                   --  1656: lui   a5,0xffe31
  .opImm .add 14 14 1008,            --  1660: addi  a4,a4,1008
  .op .add 14 14 15,                 --  1664: add   a4,a4,a5
  .opImm .add 15 2 96,               --  1668: addi  a5,sp,96
  .op .add 15 14 15,                 --  1672: add   a5,a4,a5
  .store .word 21 2 44,              --  1676: sw    s5,44(sp)
  .store .word 24 2 56,              --  1680: sw    s8,56(sp)
  .store .word 26 2 60,              --  1684: sw    s10,60(sp)
  .store .word 27 2 64,              --  1688: sw    s11,64(sp)
  .opImm .add 26 23 0,               --  1692: mv    s10,s7
  .opImm .add 27 18 0,               --  1696: mv    s11,s2
  .opImm .add 20 30 0,               --  1700: mv    s4,t5
  .store .word 15 2 36,              --  1704: sw    a5,36(sp)
  .store .word 19 2 28,              --  1708: sw    s3,28(sp)
  .opImm .add 21 11 0,               --  1712: mv    s5,a1
  .store .word 12 2 20,              --  1716: sw    a2,20(sp)
  .store .word 13 2 24,              --  1720: sw    a3,24(sp)
  .store .word 25 2 48,              --  1724: sw    s9,48(sp)
  .store .word 9 2 52,               --  1728: sw    s1,52(sp)
  .opImm .add 24 8 0,                --  1732: mv    s8,s0
  .opImm .add 23 16 0,               --  1736: mv    s7,a6
  .store .word 6 2 32,               --  1740: sw    t1,32(sp)
  .opImm .add 18 17 0,               --  1744: mv    s2,a7
  .jal 0 16,                         --  1748: j     1764
  .load .word true 15 27 0,          --  1752: lw    a5,0(s11)
  .op .add 15 18 15,                 --  1756: add   a5,s2,a5
  .load .byte false 31 15 (-1004),   --  1760: lbu   t6,-1004(a5)
  .opImm .sll 9 20 2,                --  1764: slli  s1,s4,0x2
  .load .word true 12 2 20,          --  1768: lw    a2,20(sp)
  .load .word true 13 2 24,          --  1772: lw    a3,24(sp)
  .op .add 8 22 9,                   --  1776: add   s0,s6,s1
  .branch .bne 31 0 120,             --  1780: bnez  t6,1900
  .load .word true 6 24 0,           --  1784: lw    t1,0(s8)
  .load .word true 7 24 4,           --  1788: lw    t2,4(s8)
  .load .word true 17 26 0,          --  1792: lw    a7,0(s10)
  .load .word true 15 2 28,          --  1796: lw    a5,28(sp)
  .opImm .add 10 6 0,                --  1800: mv    a0,t1
  .opImm .add 11 7 0,                --  1804: mv    a1,t2
  .op .add 19 15 17,                 --  1808: add   s3,a5,a7
  .store .word 6 2 8,                --  1812: sw    t1,8(sp)
  .store .word 7 2 12,               --  1816: sw    t2,12(sp)
  .jal 1 2152,                       --  1820: jal   3972 <__udivdi3>
  .opImm .add 15 10 (-1),            --  1824: addi  a5,a0,-1
  .opImm .srl 15 15 1,               --  1828: srli  a5,a5,0x1
  .load .word true 14 2 32,          --  1832: lw    a4,32(sp)
  .opImm .sll 15 15 2,               --  1836: slli  a5,a5,0x2
  .op .add 15 23 15,                 --  1840: add   a5,s7,a5
  .load .word true 13 15 (-168),     --  1844: lw    a3,-168(a5)
  .opImm .sll 15 20 3,               --  1848: slli  a5,s4,0x3
  .op .add 15 14 15,                 --  1852: add   a5,a4,a5
  .load .word true 14 2 36,          --  1856: lw    a4,36(sp)
  .load .word true 25 27 0,          --  1860: lw    s9,0(s11)
  .load .word true 6 2 8,            --  1864: lw    t1,8(sp)
  .load .word true 7 2 12,           --  1868: lw    t2,12(sp)
  .op .sub 17 19 13,                 --  1872: sub   a7,s3,a3
  .op .add 16 14 9,                  --  1876: add   a6,a4,s1
  .store .word 25 16 (-920),         --  1880: sw    s9,-920(a6)
  .store .word 17 8 1504,            --  1884: sw    a7,1504(s0)
  .store .word 6 15 752,             --  1888: sw    t1,752(a5)
  .store .word 7 15 756,             --  1892: sw    t2,756(a5)
  .opImm .add 20 20 1,               --  1896: addi  s4,s4,1
  .opImm .add 27 27 4,               --  1900: addi  s11,s11,4
  .opImm .add 26 26 4,               --  1904: addi  s10,s10,4
  .opImm .add 24 24 8,               --  1908: addi  s8,s8,8
  .branch .bne 21 27 (-160),         --  1912: bne   s5,s11,1752
  .load .word true 21 2 44,          --  1916: lw    s5,44(sp)
  .load .word true 19 2 28,          --  1920: lw    s3,28(sp)
  .load .word true 12 2 20,          --  1924: lw    a2,20(sp)
  .load .word true 13 2 24,          --  1928: lw    a3,24(sp)
  .load .word true 25 2 48,          --  1932: lw    s9,48(sp)
  .load .word true 9 2 52,           --  1936: lw    s1,52(sp)
  .load .word true 24 2 56,          --  1940: lw    s8,56(sp)
  .load .word true 26 2 60,          --  1944: lw    s10,60(sp)
  .load .word true 6 2 32,           --  1948: lw    t1,32(sp)
  .load .word true 27 2 64,          --  1952: lw    s11,64(sp)
  .opImm .add 17 18 0,               --  1956: mv    a7,s2
  .opImm .add 16 23 0,               --  1960: mv    a6,s7
  .opImm .add 10 25 0,               --  1964: mv    a0,s9
  .opImm .add 11 9 0,                --  1968: mv    a1,s1
  .store .word 6 2 32,               --  1972: sw    t1,32(sp)
  .store .word 16 2 28,              --  1976: sw    a6,28(sp)
  .store .word 17 2 24,              --  1980: sw    a7,24(sp)
  .store .word 12 2 20,              --  1984: sw    a2,20(sp)
  .store .word 13 2 8,               --  1988: sw    a3,8(sp)
  .jal 1 1980,                       --  1992: jal   3972 <__udivdi3>
  .load .word true 13 2 8,           --  1996: lw    a3,8(sp)
  .opImm .sltu 14 10 1,              --  2000: seqz  a4,a0
  .op .sub 14 11 14,                 --  2004: sub   a4,a1,a4
  .opImm .add 10 10 (-1),            --  2008: addi  a0,a0,-1
  .load .word true 12 2 20,          --  2012: lw    a2,20(sp)
  .load .word true 17 2 24,          --  2016: lw    a7,24(sp)
  .load .word true 16 2 28,          --  2020: lw    a6,28(sp)
  .load .word true 6 2 32,           --  2024: lw    t1,32(sp)
  .opImm .or 31 10 1,                --  2028: ori   t6,a0,1
  .opImm .add 7 14 0,                --  2032: mv    t2,a4
  .branch .bltu 14 13 184,           --  2036: bltu  a4,a3,2220
  .branch .beq 13 14 312,            --  2040: beq   a3,a4,2352
  .mulOp .mul 14 14 12,              --  2044: mul   a4,a4,a2
  .load .word true 28 2 80,          --  2048: lw    t3,80(sp)
  .load .word true 11 2 84,          --  2052: lw    a1,84(sp)
  .mulOp .mul 10 13 31,              --  2056: mul   a0,a3,t6
  .mulOp .mulhu 5 31 12,             --  2060: mulhu t0,t6,a2
  .op .add 14 14 10,                 --  2064: add   a4,a4,a0
  .mulOp .mul 8 31 12,               --  2068: mul   s0,t6,a2
  .op .add 5 14 5,                   --  2072: add   t0,a4,t0
  .opImm .srl 15 31 1,               --  2076: srli  a5,t6,0x1
  .opImm .sll 15 15 2,               --  2080: slli  a5,a5,0x2
  .op .add 15 16 15,                 --  2084: add   a5,a6,a5
  .opImm .sll 14 5 31,               --  2088: slli  a4,t0,0x1f
  .opImm .srl 30 8 1,                --  2092: srli  t5,s0,0x1
  .opImm .srl 10 5 1,                --  2096: srli  a0,t0,0x1
  .load .word true 29 15 (-168),     --  2100: lw    t4,-168(a5)
  .op .or 30 14 30,                  --  2104: or    t5,a4,t5
  .branch .bltu 11 10 60,            --  2108: bltu  a1,a0,2168
  .branch .beq 10 11 132,            --  2112: beq   a0,a1,2244
  .opImm .sll 15 28 2,               --  2116: slli  a5,t3,0x2
  .op .sub 29 19 29,                 --  2120: sub   t4,s3,t4
  .op .add 15 27 15,                 --  2124: add   a5,s11,a5
  .load .word true 14 15 0,          --  2128: lw    a4,0(a5)
  .opImm .sltu 18 28 1,              --  2132: seqz  s2,t3
  .op .sub 11 11 18,                 --  2136: sub   a1,a1,s2
  .op .add 14 14 29,                 --  2140: add   a4,a4,t4
  .store .word 14 15 0,              --  2144: sw    a4,0(a5)
  .opImm .add 28 28 (-1),            --  2148: addi  t3,t3,-1
  .opImm .add 15 15 (-4),            --  2152: addi  a5,a5,-4
  .branch .bltu 11 10 12,            --  2156: bltu  a1,a0,2168
  .branch .bne 10 11 (-32),          --  2160: bne   a0,a1,2128
  .branch .bgeu 28 30 (-36),         --  2164: bgeu  t3,t5,2128
  .opImm .add 14 31 (-2),            --  2168: addi  a4,t6,-2
  .op .sltu 31 14 31,                --  2172: sltu  t6,a4,t6
  .op .sub 15 8 24,                  --  2176: sub   a5,s0,s8
  .opImm .add 7 7 (-1),              --  2180: addi  t2,t2,-1
  .op .sltu 10 8 15,                 --  2184: sltu  a0,s0,a5
  .op .sub 5 5 26,                   --  2188: sub   t0,t0,s10
  .op .add 7 31 7,                   --  2192: add   t2,t6,t2
  .opImm .add 8 15 0,                --  2196: mv    s0,a5
  .opImm .add 31 14 0,               --  2200: mv    t6,a4
  .op .sub 5 5 10,                   --  2204: sub   t0,t0,a0
  .branch .bltu 7 13 12,             --  2208: bltu  t2,a3,2220
  .branch .bne 13 7 (-136),          --  2212: bne   a3,t2,2076
  .branch .bgeu 14 12 (-140),        --  2216: bgeu  a4,a2,2076
  .opImm .add 19 19 1,               --  2220: addi  s3,s3,1
  .jal 0 (-1388),                    --  2224: j     836
  .branch .bgeu 25 11 (-764),        --  2228: bgeu  s9,a1,1464
  .branch .bltu 18 20 (-620),        --  2232: bltu  s2,s4,1612
  .opImm .add 20 30 0,               --  2236: mv    s4,t5
  .jal 0 (-276),                     --  2240: j     1964
  .branch .bgeu 28 30 (-128),        --  2244: bgeu  t3,t5,2116
  .jal 0 (-80),                      --  2248: j     2168
  .opImm .add 26 27 0,               --  2252: mv    s10,s11
  .lui 5 0x351,                      --  2256: lui   t0,0x351
  .op .add 2 2 5,                    --  2260: add   sp,sp,t0
  .load .word true 1 2 1164,         --  2264: lw    ra,1164(sp)
  .opImm .add 10 26 0,               --  2268: mv    a0,s10
  .load .word true 8 2 1160,         --  2272: lw    s0,1160(sp)
  .load .word true 9 2 1156,         --  2276: lw    s1,1156(sp)
  .load .word true 18 2 1152,        --  2280: lw    s2,1152(sp)
  .load .word true 19 2 1148,        --  2284: lw    s3,1148(sp)
  .load .word true 20 2 1144,        --  2288: lw    s4,1144(sp)
  .load .word true 21 2 1140,        --  2292: lw    s5,1140(sp)
  .load .word true 22 2 1136,        --  2296: lw    s6,1136(sp)
  .load .word true 23 2 1132,        --  2300: lw    s7,1132(sp)
  .load .word true 24 2 1128,        --  2304: lw    s8,1128(sp)
  .load .word true 25 2 1124,        --  2308: lw    s9,1124(sp)
  .load .word true 26 2 1120,        --  2312: lw    s10,1120(sp)
  .load .word true 27 2 1116,        --  2316: lw    s11,1116(sp)
  .opImm .add 2 2 1168,              --  2320: addi  sp,sp,1168
  .jalr 0 1 0,                       --  2324: ret
  .opImm .add 15 0 1,                --  2328: li    a5,1
  .opImm .add 26 0 0,                --  2332: li    s10,0
  .branch .bltu 15 10 (-2212),       --  2336: bltu  a5,a0,124
  .jal 0 (-84),                      --  2340: j     2256
  .branch .bgeu 25 11 (-1012),       --  2344: bgeu  s9,a1,1332
  .jal 0 (-964),                     --  2348: j     1384
  .branch .bgeu 31 12 (-308),        --  2352: bgeu  t6,a2,2044
  .opImm .add 19 19 1,               --  2356: addi  s3,s3,1
  .jal 0 (-1524),                    --  2360: j     836
  .opImm .add 15 0 8,                --  2364: li    a5,8
  .branch .bltu 15 23 (-1848),       --  2368: bltu  a5,s7,520
  .opImm .add 20 8 0,                --  2372: mv    s4,s0
  .opImm .add 25 0 (-1),             --  2376: li    s9,-1
  .opImm .add 19 0 0,                --  2380: li    s3,0
  .jal 0 (-1476),                    --  2384: j     908
  .branch .bne 18 20 8,              --  2388: bne   s2,s4,2396
  .branch .bltu 8 19 (-2236),        --  2392: bltu  s0,s3,156
  .opImm .add 23 19 0,               --  2396: mv    s7,s3
  .opImm .add 9 18 0,                --  2400: mv    s1,s2
  .jal 0 (-2152),                    --  2404: j     252
  .branch .bne 9 0 (-1888),          --  2408: bnez  s1,520
  .opImm .add 15 0 8,                --  2412: li    a5,8
  .branch .bltu 15 23 (-1896),       --  2416: bltu  a5,s7,520
  .lui 14 0x351,                     --  2420: lui   a4,0x351
  .lui 15 0xffd96,                   --  2424: lui   a5,0xffd96
  .opImm .add 14 14 1008,            --  2428: addi  a4,a4,1008
  .op .add 14 14 15,                 --  2432: add   a4,a4,a5
  .opImm .add 15 2 96,               --  2436: addi  a5,sp,96
  .op .add 15 14 15,                 --  2440: add   a5,a4,a5
  .load .word true 14 15 1504,       --  2444: lw    a4,1504(a5)
  .opImm .add 10 0 0,                --  2448: li    a0,0
  .opImm .add 11 0 1,                --  2452: li    a1,1
  .opImm .add 14 14 1,               --  2456: addi  a4,a4,1
  .op .add 14 14 11,                 --  2460: add   a4,a4,a1
  .op .add 26 14 10,                 --  2464: add   s10,a4,a0
  .jal 0 (-212),                     --  2468: j     2256
  -- main:
  .opImm .add 2 2 (-48),             --  2472: addi  sp,sp,-48
  .store .word 1 2 44,               --  2476: sw    ra,44(sp)
  .opImm .add 17 0 12,               --  2480: li    a7,12
  .ecall,                            --  2484: ecall
  .opImm .add 15 0 9,                --  2488: li    a5,9
  .opImm .add 10 10 (-48),           --  2492: addi  a0,a0,-48
  .branch .bgeu 15 10 20,            --  2496: bgeu  a5,a0,2516
  .opImm .add 17 0 12,               --  2500: li    a7,12
  .ecall,                            --  2504: ecall
  .opImm .add 10 10 (-48),           --  2508: addi  a0,a0,-48
  .branch .bltu 15 10 (-12),         --  2512: bltu  a5,a0,2500
  .opImm .add 15 0 0,                --  2516: li    a5,0
  .opImm .add 11 0 0,                --  2520: li    a1,0
  .opImm .add 16 0 9,                --  2524: li    a6,9
  .opImm .srl 12 15 30,              --  2528: srli  a2,a5,0x1e
  .opImm .sll 14 15 2,               --  2532: slli  a4,a5,0x2
  .opImm .sll 13 11 2,               --  2536: slli  a3,a1,0x2
  .op .add 15 14 15,                 --  2540: add   a5,a4,a5
  .op .or 13 12 13,                  --  2544: or    a3,a2,a3
  .op .add 13 13 11,                 --  2548: add   a3,a3,a1
  .op .sltu 14 15 14,                --  2552: sltu  a4,a5,a4
  .op .add 14 14 13,                 --  2556: add   a4,a4,a3
  .opImm .sll 14 14 1,               --  2560: slli  a4,a4,0x1
  .opImm .srl 13 15 31,              --  2564: srli  a3,a5,0x1f
  .opImm .sll 15 15 1,               --  2568: slli  a5,a5,0x1
  .op .add 15 10 15,                 --  2572: add   a5,a0,a5
  .op .or 14 13 14,                  --  2576: or    a4,a3,a4
  .opImm .sra 11 10 31,              --  2580: srai  a1,a0,0x1f
  .op .add 11 11 14,                 --  2584: add   a1,a1,a4
  .op .sltu 10 15 10,                --  2588: sltu  a0,a5,a0
  .op .add 11 10 11,                 --  2592: add   a1,a0,a1
  .opImm .add 17 0 12,               --  2596: li    a7,12
  .ecall,                            --  2600: ecall
  .opImm .add 10 10 (-48),           --  2604: addi  a0,a0,-48
  .branch .bgeu 16 10 (-80),         --  2608: bgeu  a6,a0,2528
  .opImm .add 10 15 0,               --  2612: mv    a0,a5
  .jal 1 (-2568),                    --  2616: jal   48 <prime_count(unsigned long long)>
  .lui 11 0xccccd,                   --  2620: lui   a1,0xccccd
  .lui 28 0xccccd,                   --  2624: lui   t3,0xccccd
  .opImm .add 13 10 0,               --  2628: mv    a3,a0
  .opImm .add 14 0 0,                --  2632: li    a4,0
  .opImm .add 16 0 0,                --  2636: li    a6,0
  .opImm .add 6 2 12,                --  2640: addi  t1,sp,12
  .opImm .add 29 0 5,                --  2644: li    t4,5
  .opImm .add 11 11 (-819),          --  2648: addi  a1,a1,-819
  .opImm .add 28 28 (-820),          --  2652: addi  t3,t3,-820
  .opImm .add 30 0 9,                --  2656: li    t5,9
  .op .add 15 13 14,                 --  2660: add   a5,a3,a4
  .op .sltu 12 15 13,                --  2664: sltu  a2,a5,a3
  .op .add 15 15 12,                 --  2668: add   a5,a5,a2
  .mulOp .remu 15 15 29,             --  2672: remu  a5,a5,t4
  .opImm .add 17 14 0,               --  2676: mv    a7,a4
  .opImm .add 16 16 1,               --  2680: addi  a6,a6,1
  .op .add 12 6 16,                  --  2684: add   a2,t1,a6
  .opImm .add 5 13 0,                --  2688: mv    t0,a3
  .op .sub 15 13 15,                 --  2692: sub   a5,a3,a5
  .op .sltu 10 13 15,                --  2696: sltu  a0,a3,a5
  .op .sub 14 14 10,                 --  2700: sub   a4,a4,a0
  .mulOp .mul 31 15 28,              --  2704: mul   t6,a5,t3
  .mulOp .mul 14 14 11,              --  2708: mul   a4,a4,a1
  .mulOp .mulhu 10 15 11,            --  2712: mulhu a0,a5,a1
  .op .add 14 14 31,                 --  2716: add   a4,a4,t6
  .mulOp .mul 15 15 11,              --  2720: mul   a5,a5,a1
  .op .add 14 14 10,                 --  2724: add   a4,a4,a0
  .opImm .sll 10 14 31,              --  2728: slli  a0,a4,0x1f
  .opImm .srl 14 14 1,               --  2732: srli  a4,a4,0x1
  .opImm .srl 15 15 1,               --  2736: srli  a5,a5,0x1
  .op .or 15 10 15,                  --  2740: or    a5,a0,a5
  .opImm .sll 10 15 2,               --  2744: slli  a0,a5,0x2
  .op .add 10 10 15,                 --  2748: add   a0,a0,a5
  .opImm .sll 10 10 1,               --  2752: slli  a0,a0,0x1
  .op .sub 10 13 10,                 --  2756: sub   a0,a3,a0
  .opImm .add 10 10 48,              --  2760: addi  a0,a0,48
  .store .byte 10 12 (-1),           --  2764: sb    a0,-1(a2)
  .opImm .add 13 15 0,               --  2768: mv    a3,a5
  .branch .bne 17 0 (-112),          --  2772: bnez  a7,2660
  .branch .bltu 30 5 (-116),         --  2776: bltu  t5,t0,2660
  .opImm .add 15 12 0,               --  2780: mv    a5,a2
  .load .byte false 10 15 (-1),      --  2784: lbu   a0,-1(a5)
  .opImm .add 17 0 11,               --  2788: li    a7,11
  .ecall,                            --  2792: ecall
  .opImm .add 15 15 (-1),            --  2796: addi  a5,a5,-1
  .branch .bne 6 15 (-16),           --  2800: bne   t1,a5,2784
  .opImm .add 10 0 10,               --  2804: li    a0,10
  .ecall,                            --  2808: ecall
  .load .word true 1 2 44,           --  2812: lw    ra,44(sp)
  .opImm .add 10 0 0,                --  2816: li    a0,0
  .opImm .add 2 2 48,                --  2820: addi  sp,sp,48
  .jalr 0 1 0,                       --  2824: ret
  -- __divdi3:
  .opImm .add 6 10 0,                --  2828: mv    t1,a0
  .opImm .add 28 11 0,               --  2832: mv    t3,a1
  .opImm .add 17 0 0,                --  2836: li    a7,0
  .branch .bge 11 0 24,              --  2840: bgez  a1,2864
  .op .sltu 15 0 10,                 --  2844: snez  a5,a0
  .op .sub 28 0 11,                  --  2848: neg   t3,a1
  .op .sub 28 28 15,                 --  2852: sub   t3,t3,a5
  .op .sub 6 0 10,                   --  2856: neg   t1,a0
  .opImm .add 17 0 (-1),             --  2860: li    a7,-1
  .branch .bge 13 0 24,              --  2864: bgez  a3,2888
  .op .sltu 15 0 12,                 --  2868: snez  a5,a2
  .op .sub 13 0 13,                  --  2872: neg   a3,a3
  .opImm .xor 17 17 (-1),            --  2876: not   a7,a7
  .op .sub 13 13 15,                 --  2880: sub   a3,a3,a5
  .op .sub 12 0 12,                  --  2884: neg   a2,a2
  .opImm .add 14 12 0,               --  2888: mv    a4,a2
  .opImm .add 16 6 0,                --  2892: mv    a6,t1
  .opImm .add 15 28 0,               --  2896: mv    a5,t3
  .branch .bne 13 0 664,             --  2900: bnez  a3,3564
  .auipc 11 0x1,                     --  2904: auipc a1,0x1
  .opImm .add 11 11 (-1956),         --  2908: addi  a1,a1,-1956
  .branch .bgeu 28 12 236,           --  2912: bgeu  t3,a2,3148
  .lui 13 0x10,                      --  2916: lui   a3,0x10
  .branch .bgeu 12 13 208,           --  2920: bgeu  a2,a3,3128
  .opImm .sltu 13 12 256,            --  2924: sltiu a3,a2,256
  .opImm .sltu 13 13 1,              --  2928: seqz  a3,a3
  .opImm .sll 13 13 3,               --  2932: slli  a3,a3,0x3
  .op .srl 10 12 13,                 --  2936: srl   a0,a2,a3
  .op .add 11 11 10,                 --  2940: add   a1,a1,a0
  .load .byte false 11 11 0,         --  2944: lbu   a1,0(a1)
  .opImm .add 10 0 32,               --  2948: li    a0,32
  .op .add 13 11 13,                 --  2952: add   a3,a1,a3
  .op .sub 11 10 13,                 --  2956: sub   a1,a0,a3
  .branch .beq 10 13 24,             --  2960: beq   a0,a3,2984
  .op .sll 15 28 11,                 --  2964: sll   a5,t3,a1
  .op .srl 13 6 13,                  --  2968: srl   a3,t1,a3
  .op .sll 14 12 11,                 --  2972: sll   a4,a2,a1
  .op .or 15 13 15,                  --  2976: or    a5,a3,a5
  .op .sll 16 6 11,                  --  2980: sll   a6,t1,a1
  .opImm .srl 11 14 16,              --  2984: srli  a1,a4,0x10
  .mulOp .divu 28 15 11,             --  2988: divu  t3,a5,a1
  .opImm .sll 12 14 16,              --  2992: slli  a2,a4,0x10
  .opImm .srl 12 12 16,              --  2996: srli  a2,a2,0x10
  .mulOp .remu 15 15 11,             --  3000: remu  a5,a5,a1
  .opImm .add 10 28 0,               --  3004: mv    a0,t3
  .mulOp .mul 6 12 28,               --  3008: mul   t1,a2,t3
  .opImm .sll 13 15 16,              --  3012: slli  a3,a5,0x10
  .opImm .srl 15 16 16,              --  3016: srli  a5,a6,0x10
  .op .or 15 15 13,                  --  3020: or    a5,a5,a3
  .branch .bgeu 15 6 28,             --  3024: bgeu  a5,t1,3052
  .op .add 15 14 15,                 --  3028: add   a5,a4,a5
  .opImm .add 10 28 (-1),            --  3032: addi  a0,t3,-1
  .branch .bltu 15 14 16,            --  3036: bltu  a5,a4,3052
  .branch .bgeu 15 6 12,             --  3040: bgeu  a5,t1,3052
  .opImm .add 10 28 (-2),            --  3044: addi  a0,t3,-2
  .op .add 15 15 14,                 --  3048: add   a5,a5,a4
  .op .sub 15 15 6,                  --  3052: sub   a5,a5,t1
  .mulOp .divu 6 15 11,              --  3056: divu  t1,a5,a1
  .opImm .sll 16 16 16,              --  3060: slli  a6,a6,0x10
  .opImm .srl 16 16 16,              --  3064: srli  a6,a6,0x10
  .mulOp .remu 15 15 11,             --  3068: remu  a5,a5,a1
  .mulOp .mul 13 12 6,               --  3072: mul   a3,a2,t1
  .opImm .sll 15 15 16,              --  3076: slli  a5,a5,0x10
  .op .or 16 16 15,                  --  3080: or    a6,a6,a5
  .opImm .add 15 6 0,                --  3084: mv    a5,t1
  .branch .bgeu 16 13 24,            --  3088: bgeu  a6,a3,3112
  .op .add 16 14 16,                 --  3092: add   a6,a4,a6
  .opImm .add 15 6 (-1),             --  3096: addi  a5,t1,-1
  .branch .bltu 16 14 12,            --  3100: bltu  a6,a4,3112
  .branch .bgeu 16 13 8,             --  3104: bgeu  a6,a3,3112
  .opImm .add 15 6 (-2),             --  3108: addi  a5,t1,-2
  .opImm .sll 10 10 16,              --  3112: slli  a0,a0,0x10
  .op .or 10 10 15,                  --  3116: or    a0,a0,a5
  .opImm .add 11 0 0,                --  3120: li    a1,0
  .jal 0 224,                        --  3124: j     3348
  .lui 10 0x1000,                    --  3128: lui   a0,0x1000
  .opImm .add 13 0 24,               --  3132: li    a3,24
  .branch .bgeu 12 10 (-200),        --  3136: bgeu  a2,a0,2936
  .opImm .add 13 0 16,               --  3140: li    a3,16
  .jal 0 (-208),                     --  3144: j     2936
  .opImm .add 13 0 0,                --  3148: li    a3,0
  .branch .beq 12 0 24,              --  3152: beqz  a2,3176
  .lui 15 0x10,                      --  3156: lui   a5,0x10
  .branch .bgeu 12 15 212,           --  3160: bgeu  a2,a5,3372
  .opImm .sltu 13 12 256,            --  3164: sltiu a3,a2,256
  .opImm .sltu 13 13 1,              --  3168: seqz  a3,a3
  .opImm .sll 13 13 3,               --  3172: slli  a3,a3,0x3
  .op .srl 15 12 13,                 --  3176: srl   a5,a2,a3
  .op .add 11 11 15,                 --  3180: add   a1,a1,a5
  .load .byte false 15 11 0,         --  3184: lbu   a5,0(a1)
  .op .add 15 15 13,                 --  3188: add   a5,a5,a3
  .opImm .add 13 0 32,               --  3192: li    a3,32
  .op .sub 11 13 15,                 --  3196: sub   a1,a3,a5
  .branch .bne 13 15 192,            --  3200: bne   a3,a5,3392
  .op .sub 15 28 12,                 --  3204: sub   a5,t3,a2
  .opImm .add 11 0 1,                --  3208: li    a1,1
  .opImm .srl 6 14 16,               --  3212: srli  t1,a4,0x10
  .mulOp .divu 29 15 6,              --  3216: divu  t4,a5,t1
  .opImm .sll 12 14 16,              --  3220: slli  a2,a4,0x10
  .opImm .srl 12 12 16,              --  3224: srli  a2,a2,0x10
  .opImm .srl 13 16 16,              --  3228: srli  a3,a6,0x10
  .mulOp .remu 15 15 6,              --  3232: remu  a5,a5,t1
  .opImm .add 10 29 0,               --  3236: mv    a0,t4
  .mulOp .mul 28 12 29,              --  3240: mul   t3,a2,t4
  .opImm .sll 15 15 16,              --  3244: slli  a5,a5,0x10
  .op .or 15 13 15,                  --  3248: or    a5,a3,a5
  .branch .bgeu 15 28 28,            --  3252: bgeu  a5,t3,3280
  .op .add 15 14 15,                 --  3256: add   a5,a4,a5
  .opImm .add 10 29 (-1),            --  3260: addi  a0,t4,-1
  .branch .bltu 15 14 16,            --  3264: bltu  a5,a4,3280
  .branch .bgeu 15 28 12,            --  3268: bgeu  a5,t3,3280
  .opImm .add 10 29 (-2),            --  3272: addi  a0,t4,-2
  .op .add 15 15 14,                 --  3276: add   a5,a5,a4
  .op .sub 15 15 28,                 --  3280: sub   a5,a5,t3
  .mulOp .divu 28 15 6,              --  3284: divu  t3,a5,t1
  .opImm .sll 16 16 16,              --  3288: slli  a6,a6,0x10
  .opImm .srl 16 16 16,              --  3292: srli  a6,a6,0x10
  .mulOp .remu 15 15 6,              --  3296: remu  a5,a5,t1
  .mulOp .mul 13 12 28,              --  3300: mul   a3,a2,t3
  .opImm .sll 15 15 16,              --  3304: slli  a5,a5,0x10
  .op .or 16 16 15,                  --  3308: or    a6,a6,a5
  .opImm .add 15 28 0,               --  3312: mv    a5,t3
  .branch .bgeu 16 13 24,            --  3316: bgeu  a6,a3,3340
  .op .add 16 14 16,                 --  3320: add   a6,a4,a6
  .opImm .add 15 28 (-1),            --  3324: addi  a5,t3,-1
  .branch .bltu 16 14 12,            --  3328: bltu  a6,a4,3340
  .branch .bgeu 16 13 8,             --  3332: bgeu  a6,a3,3340
  .opImm .add 15 28 (-2),            --  3336: addi  a5,t3,-2
  .opImm .sll 10 10 16,              --  3340: slli  a0,a0,0x10
  .op .or 10 10 15,                  --  3344: or    a0,a0,a5
  .branch .beq 17 0 20,              --  3348: beqz  a7,3368
  .op .sltu 15 0 10,                 --  3352: snez  a5,a0
  .op .sub 11 0 11,                  --  3356: neg   a1,a1
  .op .sub 11 11 15,                 --  3360: sub   a1,a1,a5
  .op .sub 10 0 10,                  --  3364: neg   a0,a0
  .jalr 0 1 0,                       --  3368: ret
  .lui 15 0x1000,                    --  3372: lui   a5,0x1000
  .opImm .add 13 0 24,               --  3376: li    a3,24
  .branch .bgeu 12 15 (-204),        --  3380: bgeu  a2,a5,3176
  .opImm .add 13 0 16,               --  3384: li    a3,16
  .jal 0 (-212),                     --  3388: j     3176
  .op .sll 14 12 11,                 --  3392: sll   a4,a2,a1
  .op .srl 13 28 15,                 --  3396: srl   a3,t3,a5
  .opImm .srl 10 14 16,              --  3400: srli  a0,a4,0x10
  .op .sll 28 28 11,                 --  3404: sll   t3,t3,a1
  .op .srl 15 6 15,                  --  3408: srl   a5,t1,a5
  .op .or 15 15 28,                  --  3412: or    a5,a5,t3
  .mulOp .divu 28 13 10,             --  3416: divu  t3,a3,a0
  .opImm .sll 12 14 16,              --  3420: slli  a2,a4,0x10
  .opImm .srl 12 12 16,              --  3424: srli  a2,a2,0x10
  .op .sll 16 6 11,                  --  3428: sll   a6,t1,a1
  .mulOp .remu 13 13 10,             --  3432: remu  a3,a3,a0
  .mulOp .mul 6 12 28,               --  3436: mul   t1,a2,t3
  .opImm .sll 11 13 16,              --  3440: slli  a1,a3,0x10
  .opImm .srl 13 15 16,              --  3444: srli  a3,a5,0x10
  .op .or 13 13 11,                  --  3448: or    a3,a3,a1
  .opImm .add 11 28 0,               --  3452: mv    a1,t3
  .branch .bgeu 13 6 28,             --  3456: bgeu  a3,t1,3484
  .op .add 13 14 13,                 --  3460: add   a3,a4,a3
  .opImm .add 11 28 (-1),            --  3464: addi  a1,t3,-1
  .branch .bltu 13 14 16,            --  3468: bltu  a3,a4,3484
  .branch .bgeu 13 6 12,             --  3472: bgeu  a3,t1,3484
  .opImm .add 11 28 (-2),            --  3476: addi  a1,t3,-2
  .op .add 13 13 14,                 --  3480: add   a3,a3,a4
  .op .sub 13 13 6,                  --  3484: sub   a3,a3,t1
  .mulOp .divu 6 13 10,              --  3488: divu  t1,a3,a0
  .opImm .sll 15 15 16,              --  3492: slli  a5,a5,0x10
  .opImm .srl 15 15 16,              --  3496: srli  a5,a5,0x10
  .mulOp .remu 13 13 10,             --  3500: remu  a3,a3,a0
  .mulOp .mul 12 12 6,               --  3504: mul   a2,a2,t1
  .opImm .sll 13 13 16,              --  3508: slli  a3,a3,0x10
  .op .or 15 15 13,                  --  3512: or    a5,a5,a3
  .opImm .add 13 6 0,                --  3516: mv    a3,t1
  .branch .bgeu 15 12 28,            --  3520: bgeu  a5,a2,3548
  .op .add 15 14 15,                 --  3524: add   a5,a4,a5
  .opImm .add 13 6 (-1),             --  3528: addi  a3,t1,-1
  .branch .bltu 15 14 16,            --  3532: bltu  a5,a4,3548
  .branch .bgeu 15 12 12,            --  3536: bgeu  a5,a2,3548
  .opImm .add 13 6 (-2),             --  3540: addi  a3,t1,-2
  .op .add 15 15 14,                 --  3544: add   a5,a5,a4
  .opImm .sll 11 11 16,              --  3548: slli  a1,a1,0x10
  .op .sub 15 15 12,                 --  3552: sub   a5,a5,a2
  .op .or 11 11 13,                  --  3556: or    a1,a1,a3
  .jal 0 (-348),                     --  3560: j     3212
  .branch .bltu 28 13 396,           --  3564: bltu  t3,a3,3960
  .lui 15 0x10,                      --  3568: lui   a5,0x10
  .branch .bgeu 13 15 72,            --  3572: bgeu  a3,a5,3644
  .opImm .sltu 14 13 256,            --  3576: sltiu a4,a3,256
  .opImm .sltu 14 14 1,              --  3580: seqz  a4,a4
  .opImm .sll 14 14 3,               --  3584: slli  a4,a4,0x3
  .op .srl 11 13 14,                 --  3588: srl   a1,a3,a4
  .auipc 15 0x0,                     --  3592: auipc a5,0x0
  .opImm .add 15 15 1452,            --  3596: addi  a5,a5,1452
  .op .add 15 15 11,                 --  3600: add   a5,a5,a1
  .load .byte false 15 15 0,         --  3604: lbu   a5,0(a5)
  .op .add 15 15 14,                 --  3608: add   a5,a5,a4
  .opImm .add 14 0 32,               --  3612: li    a4,32
  .op .sub 11 14 15,                 --  3616: sub   a1,a4,a5
  .branch .bne 14 15 44,             --  3620: bne   a4,a5,3664
  .opImm .add 10 0 1,                --  3624: li    a0,1
  .branch .bltu 13 28 (-280),        --  3628: bltu  a3,t3,3348
  .op .sltu 10 6 12,                 --  3632: sltu  a0,t1,a2
  .opImm .sltu 10 10 1,              --  3636: seqz  a0,a0
  .jal 0 (-292),                     --  3640: j     3348
  .lui 15 0x1000,                    --  3644: lui   a5,0x1000
  .opImm .add 14 0 24,               --  3648: li    a4,24
  .branch .bgeu 13 15 (-64),         --  3652: bgeu  a3,a5,3588
  .opImm .add 14 0 16,               --  3656: li    a4,16
  .jal 0 (-72),                      --  3660: j     3588
  .op .srl 14 12 15,                 --  3664: srl   a4,a2,a5
  .op .sll 13 13 11,                 --  3668: sll   a3,a3,a1
  .op .or 13 14 13,                  --  3672: or    a3,a4,a3
  .op .srl 14 28 15,                 --  3676: srl   a4,t3,a5
  .op .sll 28 28 11,                 --  3680: sll   t3,t3,a1
  .op .srl 15 6 15,                  --  3684: srl   a5,t1,a5
  .op .or 15 15 28,                  --  3688: or    a5,a5,t3
  .opImm .srl 28 13 16,              --  3692: srli  t3,a3,0x10
  .mulOp .divu 30 14 28,             --  3696: divu  t5,a4,t3
  .opImm .sll 16 13 16,              --  3700: slli  a6,a3,0x10
  .opImm .srl 16 16 16,              --  3704: srli  a6,a6,0x10
  .op .sll 12 12 11,                 --  3708: sll   a2,a2,a1
  .mulOp .remu 14 14 28,             --  3712: remu  a4,a4,t3
  .mulOp .mul 29 16 30,              --  3716: mul   t4,a6,t5
  .opImm .sll 10 14 16,              --  3720: slli  a0,a4,0x10
  .opImm .srl 14 15 16,              --  3724: srli  a4,a5,0x10
  .op .or 14 14 10,                  --  3728: or    a4,a4,a0
  .opImm .add 10 30 0,               --  3732: mv    a0,t5
  .branch .bgeu 14 29 28,            --  3736: bgeu  a4,t4,3764
  .op .add 14 13 14,                 --  3740: add   a4,a3,a4
  .opImm .add 10 30 (-1),            --  3744: addi  a0,t5,-1
  .branch .bltu 14 13 16,            --  3748: bltu  a4,a3,3764
  .branch .bgeu 14 29 12,            --  3752: bgeu  a4,t4,3764
  .opImm .add 10 30 (-2),            --  3756: addi  a0,t5,-2
  .op .add 14 14 13,                 --  3760: add   a4,a4,a3
  .op .sub 14 14 29,                 --  3764: sub   a4,a4,t4
  .mulOp .divu 29 14 28,             --  3768: divu  t4,a4,t3
  .opImm .sll 15 15 16,              --  3772: slli  a5,a5,0x10
  .opImm .srl 15 15 16,              --  3776: srli  a5,a5,0x10
  .mulOp .remu 14 14 28,             --  3780: remu  a4,a4,t3
  .mulOp .mul 16 16 29,              --  3784: mul   a6,a6,t4
  .opImm .sll 14 14 16,              --  3788: slli  a4,a4,0x10
  .op .or 15 15 14,                  --  3792: or    a5,a5,a4
  .opImm .add 14 29 0,               --  3796: mv    a4,t4
  .branch .bgeu 15 16 28,            --  3800: bgeu  a5,a6,3828
  .op .add 15 13 15,                 --  3804: add   a5,a3,a5
  .opImm .add 14 29 (-1),            --  3808: addi  a4,t4,-1
  .branch .bltu 15 13 16,            --  3812: bltu  a5,a3,3828
  .branch .bgeu 15 16 12,            --  3816: bgeu  a5,a6,3828
  .opImm .add 14 29 (-2),            --  3820: addi  a4,t4,-2
  .op .add 15 15 13,                 --  3824: add   a5,a5,a3
  .opImm .sll 10 10 16,              --  3828: slli  a0,a0,0x10
  .lui 29 0x10,                      --  3832: lui   t4,0x10
  .op .or 10 10 14,                  --  3836: or    a0,a0,a4
  .opImm .add 13 29 (-1),            --  3840: addi  a3,t4,-1
  .op .and 14 10 13,                 --  3844: and   a4,a0,a3
  .op .sub 15 15 16,                 --  3848: sub   a5,a5,a6
  .op .and 13 12 13,                 --  3852: and   a3,a2,a3
  .opImm .srl 16 10 16,              --  3856: srli  a6,a0,0x10
  .opImm .srl 12 12 16,              --  3860: srli  a2,a2,0x10
  .mulOp .mul 28 14 13,              --  3864: mul   t3,a4,a3
  .mulOp .mul 13 16 13,              --  3868: mul   a3,a6,a3
  .mulOp .mul 14 14 12,              --  3872: mul   a4,a4,a2
  .mulOp .mul 16 16 12,              --  3876: mul   a6,a6,a2
  .op .add 12 14 13,                 --  3880: add   a2,a4,a3
  .opImm .srl 14 28 16,              --  3884: srli  a4,t3,0x10
  .op .add 14 14 12,                 --  3888: add   a4,a4,a2
  .branch .bgeu 14 13 8,             --  3892: bgeu  a4,a3,3900
  .op .add 16 16 29,                 --  3896: add   a6,a6,t4
  .opImm .srl 13 14 16,              --  3900: srli  a3,a4,0x10
  .op .add 13 13 16,                 --  3904: add   a3,a3,a6
  .branch .bltu 15 13 44,            --  3908: bltu  a5,a3,3952
  .branch .bne 15 13 (-792),         --  3912: bne   a5,a3,3120
  .lui 15 0x10,                      --  3916: lui   a5,0x10
  .opImm .add 15 15 (-1),            --  3920: addi  a5,a5,-1
  .op .and 14 14 15,                 --  3924: and   a4,a4,a5
  .opImm .sll 14 14 16,              --  3928: slli  a4,a4,0x10
  .op .and 28 28 15,                 --  3932: and   t3,t3,a5
  .op .sll 6 6 11,                   --  3936: sll   t1,t1,a1
  .op .add 14 14 28,                 --  3940: add   a4,a4,t3
  .opImm .add 11 0 0,                --  3944: li    a1,0
  .branch .bgeu 6 14 (-600),         --  3948: bgeu  t1,a4,3348
  .opImm .add 10 10 (-1),            --  3952: addi  a0,a0,-1
  .jal 0 (-836),                     --  3956: j     3120
  .opImm .add 11 0 0,                --  3960: li    a1,0
  .opImm .add 10 0 0,                --  3964: li    a0,0
  .jal 0 (-620),                     --  3968: j     3348
  -- __udivdi3:
  .opImm .add 17 10 0,               --  3972: mv    a7,a0
  .opImm .add 6 11 0,                --  3976: mv    t1,a1
  .opImm .add 14 12 0,               --  3980: mv    a4,a2
  .opImm .add 16 10 0,               --  3984: mv    a6,a0
  .opImm .add 15 11 0,               --  3988: mv    a5,a1
  .branch .bne 13 0 644,             --  3992: bnez  a3,4636
  .auipc 11 0x0,                     --  3996: auipc a1,0x0
  .opImm .add 11 11 1048,            --  4000: addi  a1,a1,1048
  .branch .bgeu 6 12 236,            --  4004: bgeu  t1,a2,4240
  .lui 13 0x10,                      --  4008: lui   a3,0x10
  .branch .bgeu 12 13 208,           --  4012: bgeu  a2,a3,4220
  .opImm .sltu 13 12 256,            --  4016: sltiu a3,a2,256
  .opImm .sltu 13 13 1,              --  4020: seqz  a3,a3
  .opImm .sll 13 13 3,               --  4024: slli  a3,a3,0x3
  .op .srl 10 12 13,                 --  4028: srl   a0,a2,a3
  .op .add 11 11 10,                 --  4032: add   a1,a1,a0
  .load .byte false 11 11 0,         --  4036: lbu   a1,0(a1)
  .opImm .add 10 0 32,               --  4040: li    a0,32
  .op .add 13 11 13,                 --  4044: add   a3,a1,a3
  .op .sub 11 10 13,                 --  4048: sub   a1,a0,a3
  .branch .beq 10 13 24,             --  4052: beq   a0,a3,4076
  .op .sll 15 6 11,                  --  4056: sll   a5,t1,a1
  .op .srl 13 17 13,                 --  4060: srl   a3,a7,a3
  .op .sll 14 12 11,                 --  4064: sll   a4,a2,a1
  .op .or 15 13 15,                  --  4068: or    a5,a3,a5
  .op .sll 16 17 11,                 --  4072: sll   a6,a7,a1
  .opImm .srl 11 14 16,              --  4076: srli  a1,a4,0x10
  .mulOp .divu 6 15 11,              --  4080: divu  t1,a5,a1
  .opImm .sll 12 14 16,              --  4084: slli  a2,a4,0x10
  .opImm .srl 12 12 16,              --  4088: srli  a2,a2,0x10
  .mulOp .remu 15 15 11,             --  4092: remu  a5,a5,a1
  .opImm .add 10 6 0,                --  4096: mv    a0,t1
  .mulOp .mul 17 12 6,               --  4100: mul   a7,a2,t1
  .opImm .sll 13 15 16,              --  4104: slli  a3,a5,0x10
  .opImm .srl 15 16 16,              --  4108: srli  a5,a6,0x10
  .op .or 15 15 13,                  --  4112: or    a5,a5,a3
  .branch .bgeu 15 17 28,            --  4116: bgeu  a5,a7,4144
  .op .add 15 14 15,                 --  4120: add   a5,a4,a5
  .opImm .add 10 6 (-1),             --  4124: addi  a0,t1,-1
  .branch .bltu 15 14 16,            --  4128: bltu  a5,a4,4144
  .branch .bgeu 15 17 12,            --  4132: bgeu  a5,a7,4144
  .opImm .add 10 6 (-2),             --  4136: addi  a0,t1,-2
  .op .add 15 15 14,                 --  4140: add   a5,a5,a4
  .op .sub 15 15 17,                 --  4144: sub   a5,a5,a7
  .mulOp .divu 17 15 11,             --  4148: divu  a7,a5,a1
  .opImm .sll 16 16 16,              --  4152: slli  a6,a6,0x10
  .opImm .srl 16 16 16,              --  4156: srli  a6,a6,0x10
  .mulOp .remu 15 15 11,             --  4160: remu  a5,a5,a1
  .mulOp .mul 13 12 17,              --  4164: mul   a3,a2,a7
  .opImm .sll 15 15 16,              --  4168: slli  a5,a5,0x10
  .op .or 16 16 15,                  --  4172: or    a6,a6,a5
  .opImm .add 15 17 0,               --  4176: mv    a5,a7
  .branch .bgeu 16 13 24,            --  4180: bgeu  a6,a3,4204
  .op .add 16 14 16,                 --  4184: add   a6,a4,a6
  .opImm .add 15 17 (-1),            --  4188: addi  a5,a7,-1
  .branch .bltu 16 14 12,            --  4192: bltu  a6,a4,4204
  .branch .bgeu 16 13 8,             --  4196: bgeu  a6,a3,4204
  .opImm .add 15 17 (-2),            --  4200: addi  a5,a7,-2
  .opImm .sll 10 10 16,              --  4204: slli  a0,a0,0x10
  .op .or 10 10 15,                  --  4208: or    a0,a0,a5
  .opImm .add 11 0 0,                --  4212: li    a1,0
  .jalr 0 1 0,                       --  4216: ret
  .lui 10 0x1000,                    --  4220: lui   a0,0x1000
  .opImm .add 13 0 24,               --  4224: li    a3,24
  .branch .bgeu 12 10 (-200),        --  4228: bgeu  a2,a0,4028
  .opImm .add 13 0 16,               --  4232: li    a3,16
  .jal 0 (-208),                     --  4236: j     4028
  .opImm .add 13 0 0,                --  4240: li    a3,0
  .branch .beq 12 0 24,              --  4244: beqz  a2,4268
  .lui 15 0x10,                      --  4248: lui   a5,0x10
  .branch .bgeu 12 15 192,           --  4252: bgeu  a2,a5,4444
  .opImm .sltu 13 12 256,            --  4256: sltiu a3,a2,256
  .opImm .sltu 13 13 1,              --  4260: seqz  a3,a3
  .opImm .sll 13 13 3,               --  4264: slli  a3,a3,0x3
  .op .srl 15 12 13,                 --  4268: srl   a5,a2,a3
  .op .add 11 11 15,                 --  4272: add   a1,a1,a5
  .load .byte false 15 11 0,         --  4276: lbu   a5,0(a1)
  .op .add 15 15 13,                 --  4280: add   a5,a5,a3
  .opImm .add 13 0 32,               --  4284: li    a3,32
  .op .sub 11 13 15,                 --  4288: sub   a1,a3,a5
  .branch .bne 13 15 172,            --  4292: bne   a3,a5,4464
  .op .sub 15 6 12,                  --  4296: sub   a5,t1,a2
  .opImm .add 11 0 1,                --  4300: li    a1,1
  .opImm .srl 17 14 16,              --  4304: srli  a7,a4,0x10
  .mulOp .divu 28 15 17,             --  4308: divu  t3,a5,a7
  .opImm .sll 12 14 16,              --  4312: slli  a2,a4,0x10
  .opImm .srl 12 12 16,              --  4316: srli  a2,a2,0x10
  .opImm .srl 13 16 16,              --  4320: srli  a3,a6,0x10
  .mulOp .remu 15 15 17,             --  4324: remu  a5,a5,a7
  .opImm .add 10 28 0,               --  4328: mv    a0,t3
  .mulOp .mul 6 12 28,               --  4332: mul   t1,a2,t3
  .opImm .sll 15 15 16,              --  4336: slli  a5,a5,0x10
  .op .or 15 13 15,                  --  4340: or    a5,a3,a5
  .branch .bgeu 15 6 28,             --  4344: bgeu  a5,t1,4372
  .op .add 15 14 15,                 --  4348: add   a5,a4,a5
  .opImm .add 10 28 (-1),            --  4352: addi  a0,t3,-1
  .branch .bltu 15 14 16,            --  4356: bltu  a5,a4,4372
  .branch .bgeu 15 6 12,             --  4360: bgeu  a5,t1,4372
  .opImm .add 10 28 (-2),            --  4364: addi  a0,t3,-2
  .op .add 15 15 14,                 --  4368: add   a5,a5,a4
  .op .sub 15 15 6,                  --  4372: sub   a5,a5,t1
  .mulOp .divu 6 15 17,              --  4376: divu  t1,a5,a7
  .opImm .sll 16 16 16,              --  4380: slli  a6,a6,0x10
  .opImm .srl 16 16 16,              --  4384: srli  a6,a6,0x10
  .mulOp .remu 15 15 17,             --  4388: remu  a5,a5,a7
  .mulOp .mul 13 12 6,               --  4392: mul   a3,a2,t1
  .opImm .sll 15 15 16,              --  4396: slli  a5,a5,0x10
  .op .or 16 16 15,                  --  4400: or    a6,a6,a5
  .opImm .add 15 6 0,                --  4404: mv    a5,t1
  .branch .bgeu 16 13 24,            --  4408: bgeu  a6,a3,4432
  .op .add 16 14 16,                 --  4412: add   a6,a4,a6
  .opImm .add 15 6 (-1),             --  4416: addi  a5,t1,-1
  .branch .bltu 16 14 12,            --  4420: bltu  a6,a4,4432
  .branch .bgeu 16 13 8,             --  4424: bgeu  a6,a3,4432
  .opImm .add 15 6 (-2),             --  4428: addi  a5,t1,-2
  .opImm .sll 10 10 16,              --  4432: slli  a0,a0,0x10
  .op .or 10 10 15,                  --  4436: or    a0,a0,a5
  .jalr 0 1 0,                       --  4440: ret
  .lui 15 0x1000,                    --  4444: lui   a5,0x1000
  .opImm .add 13 0 24,               --  4448: li    a3,24
  .branch .bgeu 12 15 (-184),        --  4452: bgeu  a2,a5,4268
  .opImm .add 13 0 16,               --  4456: li    a3,16
  .jal 0 (-192),                     --  4460: j     4268
  .op .sll 14 12 11,                 --  4464: sll   a4,a2,a1
  .op .srl 13 6 15,                  --  4468: srl   a3,t1,a5
  .opImm .srl 10 14 16,              --  4472: srli  a0,a4,0x10
  .op .sll 6 6 11,                   --  4476: sll   t1,t1,a1
  .op .srl 15 17 15,                 --  4480: srl   a5,a7,a5
  .op .or 15 15 6,                   --  4484: or    a5,a5,t1
  .mulOp .divu 6 13 10,              --  4488: divu  t1,a3,a0
  .opImm .sll 12 14 16,              --  4492: slli  a2,a4,0x10
  .opImm .srl 12 12 16,              --  4496: srli  a2,a2,0x10
  .op .sll 16 17 11,                 --  4500: sll   a6,a7,a1
  .mulOp .remu 13 13 10,             --  4504: remu  a3,a3,a0
  .mulOp .mul 17 12 6,               --  4508: mul   a7,a2,t1
  .opImm .sll 11 13 16,              --  4512: slli  a1,a3,0x10
  .opImm .srl 13 15 16,              --  4516: srli  a3,a5,0x10
  .op .or 13 13 11,                  --  4520: or    a3,a3,a1
  .opImm .add 11 6 0,                --  4524: mv    a1,t1
  .branch .bgeu 13 17 28,            --  4528: bgeu  a3,a7,4556
  .op .add 13 14 13,                 --  4532: add   a3,a4,a3
  .opImm .add 11 6 (-1),             --  4536: addi  a1,t1,-1
  .branch .bltu 13 14 16,            --  4540: bltu  a3,a4,4556
  .branch .bgeu 13 17 12,            --  4544: bgeu  a3,a7,4556
  .opImm .add 11 6 (-2),             --  4548: addi  a1,t1,-2
  .op .add 13 13 14,                 --  4552: add   a3,a3,a4
  .op .sub 13 13 17,                 --  4556: sub   a3,a3,a7
  .mulOp .divu 17 13 10,             --  4560: divu  a7,a3,a0
  .opImm .sll 15 15 16,              --  4564: slli  a5,a5,0x10
  .opImm .srl 15 15 16,              --  4568: srli  a5,a5,0x10
  .mulOp .remu 13 13 10,             --  4572: remu  a3,a3,a0
  .mulOp .mul 12 12 17,              --  4576: mul   a2,a2,a7
  .opImm .sll 13 13 16,              --  4580: slli  a3,a3,0x10
  .op .or 15 15 13,                  --  4584: or    a5,a5,a3
  .opImm .add 13 17 0,               --  4588: mv    a3,a7
  .branch .bgeu 15 12 28,            --  4592: bgeu  a5,a2,4620
  .op .add 15 14 15,                 --  4596: add   a5,a4,a5
  .opImm .add 13 17 (-1),            --  4600: addi  a3,a7,-1
  .branch .bltu 15 14 16,            --  4604: bltu  a5,a4,4620
  .branch .bgeu 15 12 12,            --  4608: bgeu  a5,a2,4620
  .opImm .add 13 17 (-2),            --  4612: addi  a3,a7,-2
  .op .add 15 15 14,                 --  4616: add   a5,a5,a4
  .opImm .sll 11 11 16,              --  4620: slli  a1,a1,0x10
  .op .sub 15 15 12,                 --  4624: sub   a5,a5,a2
  .op .or 11 11 13,                  --  4628: or    a1,a1,a3
  .jal 0 (-328),                     --  4632: j     4304
  .branch .bltu 11 13 396,           --  4636: bltu  a1,a3,5032
  .lui 15 0x10,                      --  4640: lui   a5,0x10
  .branch .bgeu 13 15 72,            --  4644: bgeu  a3,a5,4716
  .opImm .sltu 14 13 256,            --  4648: sltiu a4,a3,256
  .opImm .sltu 14 14 1,              --  4652: seqz  a4,a4
  .opImm .sll 14 14 3,               --  4656: slli  a4,a4,0x3
  .op .srl 11 13 14,                 --  4660: srl   a1,a3,a4
  .auipc 15 0x0,                     --  4664: auipc a5,0x0
  .opImm .add 15 15 380,             --  4668: addi  a5,a5,380
  .op .add 15 15 11,                 --  4672: add   a5,a5,a1
  .load .byte false 15 15 0,         --  4676: lbu   a5,0(a5)
  .op .add 15 15 14,                 --  4680: add   a5,a5,a4
  .opImm .add 14 0 32,               --  4684: li    a4,32
  .op .sub 11 14 15,                 --  4688: sub   a1,a4,a5
  .branch .bne 14 15 44,             --  4692: bne   a4,a5,4736
  .opImm .add 10 0 1,                --  4696: li    a0,1
  .branch .bltu 13 6 (-484),         --  4700: bltu  a3,t1,4216
  .op .sltu 10 17 12,                --  4704: sltu  a0,a7,a2
  .opImm .sltu 10 10 1,              --  4708: seqz  a0,a0
  .jalr 0 1 0,                       --  4712: ret
  .lui 15 0x1000,                    --  4716: lui   a5,0x1000
  .opImm .add 14 0 24,               --  4720: li    a4,24
  .branch .bgeu 13 15 (-64),         --  4724: bgeu  a3,a5,4660
  .opImm .add 14 0 16,               --  4728: li    a4,16
  .jal 0 (-72),                      --  4732: j     4660
  .op .srl 14 12 15,                 --  4736: srl   a4,a2,a5
  .op .sll 13 13 11,                 --  4740: sll   a3,a3,a1
  .op .or 13 14 13,                  --  4744: or    a3,a4,a3
  .op .srl 14 6 15,                  --  4748: srl   a4,t1,a5
  .op .sll 6 6 11,                   --  4752: sll   t1,t1,a1
  .op .srl 15 17 15,                 --  4756: srl   a5,a7,a5
  .op .or 15 15 6,                   --  4760: or    a5,a5,t1
  .opImm .srl 6 13 16,               --  4764: srli  t1,a3,0x10
  .mulOp .divu 29 14 6,              --  4768: divu  t4,a4,t1
  .opImm .sll 16 13 16,              --  4772: slli  a6,a3,0x10
  .opImm .srl 16 16 16,              --  4776: srli  a6,a6,0x10
  .op .sll 12 12 11,                 --  4780: sll   a2,a2,a1
  .mulOp .remu 14 14 6,              --  4784: remu  a4,a4,t1
  .mulOp .mul 28 16 29,              --  4788: mul   t3,a6,t4
  .opImm .sll 10 14 16,              --  4792: slli  a0,a4,0x10
  .opImm .srl 14 15 16,              --  4796: srli  a4,a5,0x10
  .op .or 14 14 10,                  --  4800: or    a4,a4,a0
  .opImm .add 10 29 0,               --  4804: mv    a0,t4
  .branch .bgeu 14 28 28,            --  4808: bgeu  a4,t3,4836
  .op .add 14 13 14,                 --  4812: add   a4,a3,a4
  .opImm .add 10 29 (-1),            --  4816: addi  a0,t4,-1
  .branch .bltu 14 13 16,            --  4820: bltu  a4,a3,4836
  .branch .bgeu 14 28 12,            --  4824: bgeu  a4,t3,4836
  .opImm .add 10 29 (-2),            --  4828: addi  a0,t4,-2
  .op .add 14 14 13,                 --  4832: add   a4,a4,a3
  .op .sub 14 14 28,                 --  4836: sub   a4,a4,t3
  .mulOp .divu 28 14 6,              --  4840: divu  t3,a4,t1
  .opImm .sll 15 15 16,              --  4844: slli  a5,a5,0x10
  .opImm .srl 15 15 16,              --  4848: srli  a5,a5,0x10
  .mulOp .remu 14 14 6,              --  4852: remu  a4,a4,t1
  .mulOp .mul 16 16 28,              --  4856: mul   a6,a6,t3
  .opImm .sll 14 14 16,              --  4860: slli  a4,a4,0x10
  .op .or 15 15 14,                  --  4864: or    a5,a5,a4
  .opImm .add 14 28 0,               --  4868: mv    a4,t3
  .branch .bgeu 15 16 28,            --  4872: bgeu  a5,a6,4900
  .op .add 15 13 15,                 --  4876: add   a5,a3,a5
  .opImm .add 14 28 (-1),            --  4880: addi  a4,t3,-1
  .branch .bltu 15 13 16,            --  4884: bltu  a5,a3,4900
  .branch .bgeu 15 16 12,            --  4888: bgeu  a5,a6,4900
  .opImm .add 14 28 (-2),            --  4892: addi  a4,t3,-2
  .op .add 15 15 13,                 --  4896: add   a5,a5,a3
  .opImm .sll 10 10 16,              --  4900: slli  a0,a0,0x10
  .lui 28 0x10,                      --  4904: lui   t3,0x10
  .op .or 10 10 14,                  --  4908: or    a0,a0,a4
  .opImm .add 13 28 (-1),            --  4912: addi  a3,t3,-1
  .op .and 14 10 13,                 --  4916: and   a4,a0,a3
  .op .sub 15 15 16,                 --  4920: sub   a5,a5,a6
  .op .and 13 12 13,                 --  4924: and   a3,a2,a3
  .opImm .srl 16 10 16,              --  4928: srli  a6,a0,0x10
  .opImm .srl 12 12 16,              --  4932: srli  a2,a2,0x10
  .mulOp .mul 6 14 13,               --  4936: mul   t1,a4,a3
  .mulOp .mul 13 16 13,              --  4940: mul   a3,a6,a3
  .mulOp .mul 14 14 12,              --  4944: mul   a4,a4,a2
  .mulOp .mul 16 16 12,              --  4948: mul   a6,a6,a2
  .op .add 12 14 13,                 --  4952: add   a2,a4,a3
  .opImm .srl 14 6 16,               --  4956: srli  a4,t1,0x10
  .op .add 14 14 12,                 --  4960: add   a4,a4,a2
  .branch .bgeu 14 13 8,             --  4964: bgeu  a4,a3,4972
  .op .add 16 16 28,                 --  4968: add   a6,a6,t3
  .opImm .srl 13 14 16,              --  4972: srli  a3,a4,0x10
  .op .add 13 13 16,                 --  4976: add   a3,a3,a6
  .branch .bltu 15 13 44,            --  4980: bltu  a5,a3,5024
  .branch .bne 15 13 (-772),         --  4984: bne   a5,a3,4212
  .lui 15 0x10,                      --  4988: lui   a5,0x10
  .opImm .add 15 15 (-1),            --  4992: addi  a5,a5,-1
  .op .and 14 14 15,                 --  4996: and   a4,a4,a5
  .opImm .sll 14 14 16,              --  5000: slli  a4,a4,0x10
  .op .and 6 6 15,                   --  5004: and   t1,t1,a5
  .op .sll 17 17 11,                 --  5008: sll   a7,a7,a1
  .op .add 14 14 6,                  --  5012: add   a4,a4,t1
  .opImm .add 11 0 0,                --  5016: li    a1,0
  .branch .bgeu 17 14 (-804),        --  5020: bgeu  a7,a4,4216
  .opImm .add 10 10 (-1),            --  5024: addi  a0,a0,-1
  .jal 0 (-816),                     --  5028: j     4212
  .opImm .add 11 0 0,                --  5032: li    a1,0
  .opImm .add 10 0 0,                --  5036: li    a0,0
  .jalr 0 1 0]                       --  5040: ret

/-- The number of code words. -/
abbrev codeWords : Nat := 1261

theorem decode_prog : (prog.take codeWords).map (decode 32) = code.map some := by
  decide +kernel

end TinyFive.CountingPrimesLpha
