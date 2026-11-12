from machine import *

# Library Checker "Counting Primes" (https://judge.yosupo.jp/problem/counting_primes,
# N <= 1e11): fast accepted submission 346093 by zjy2008, ported to nanofive.
# Compiled to RV32IM machine code (no libc/libstdc++; I/O via ecalls, RARS
# convention, see machine.ECALL) with riscv64-unknown-elf-g++ 13.2:
#   g++ -march=rv32im -mabi=ilp32 -O2 -std=c++17 -ffreestanding -nostdlib
#       -fno-exceptions -fno-rtti -fno-tree-loop-distribute-patterns
#       -fno-threadsafe-statics -DMEM_SIZE=0x400000 ... -lgcc
# (libgcc supplies the 64-bit division routines __udivdi3 etc.)
# and laid out flat from address 0: code, then read-only data. Zeroed data
# (.bss) follows the image; the stack grows down from the top of memory.
# Startup code:
#   _start: li sp, MEM_SIZE; call main; li a7, 93; ecall   (exit(main()))
# Reads N from stdin, prints pi(N) = the number of primes <= N.
#   echo 100000000 | python3 counting_primes_zjy2008.py   ->  5761455
#
# C++ source:
#
#   // Library Checker "Counting Primes", submission 346093 by zjy2008 (15 ms):
#   // https://judge.yosupo.jp/submission/346093
#   // Same rough-number Lucy/min_25 scheme, but sieving primes 3, 5 then a mod-30 wheel.
#   // Port changes (marked //*): runtime from rt.h instead of <bits/stdc++.h>,
#   // fdiv() is an exact integer division instead of going through double
#   // (rv32im has no FPU), sqrtl -> integer sqrt, cin/cout -> ecall I/O.
#   // ---- rt.h (inlined) ----
#   // Freestanding runtime for nanofive (no libc / libstdc++): I/O through the
#   // RARS-style ecalls (a7=12 read char, a7=11 print char), a bump allocator
#   // for vector<T>, and the integer square root the submissions get from sqrtl.
#   #include <stdint.h>
#   #include <stddef.h>
#   namespace std {}
#
#   static inline int getchar_() { register int a0 asm("a0"); register int a7 asm("a7") = 12;
#     asm volatile("ecall" : "=r"(a0) : "r"(a7)); return a0; }
#   static inline void putchar_(int c) { register int a0 asm("a0") = c; register int a7 asm("a7") = 11;
#     asm volatile("ecall" :: "r"(a0), "r"(a7)); }
#
#   static uint64_t read_u64() {          // replaces scanf("%lld") / cin >>
#     int c = getchar_();
#     while (c < '0' || c > '9') c = getchar_();
#     uint64_t n = 0;
#     for (; c >= '0' && c <= '9'; c = getchar_()) n = n * 10 + (c - '0');
#     return n;
#   }
#   static void print_u64(uint64_t n) {   // replaces printf("%lld\n") / cout <<
#     char buf[20]; int i = 0;
#     do { buf[i++] = '0' + n % 10; n /= 10; } while (n);
#     while (i) putchar_(buf[--i]);
#     putchar_('\n');
#   }
#
#   extern "C" void *memset(void *d, int c, size_t n) {  // gcc emits calls to it
#     unsigned char *p = (unsigned char *)d; while (n--) *p++ = c; return d;
#   }
#
#   extern char _end[];                    // end of .bss, from the linker script
#   static char *heap = _end;
#   template <typename T> struct vector {  // just enough of std::vector: vector<T> v(n) is n zeros
#     T *d;
#     explicit vector(size_t n) : d((T *)((uintptr_t)(heap + 7) & ~(uintptr_t)7)) {
#       heap = (char *)(d + n); memset(d, 0, n * sizeof(T));
#     }
#     T &operator[](size_t i) { return d[i]; }
#   };
#
#   static uint64_t isqrt64(uint64_t n) {  // floor(sqrt(n)), what sqrtl gives for n <= 1e11
#     uint64_t x = n, y = (x + 1) / 2;
#     while (y < x) { x = y; y = (x + n / x) / 2; }
#     return x;
#   }
#   // ---- end of rt.h ----
#   #define LL long long
#   #define uint unsigned
#   #define uLL unsigned long long
#   using namespace std;
#   inline LL fdiv(const LL&x,const LL&y){
#   	return x/y;  //* static_cast<LL>(static_cast<double>(x)/static_cast<double>(y))
#   }
#   inline LL pi(LL n){
#   	if(n<7)return (2<=n)+(3<=n)+(5<=n);
#   	const int R=isqrt64(n),sqR=isqrt64(R);  //* sqrtl(n), sqrtl(R)
#   	int C=0,V=(R+1)/2;
#   	vector<int>small(V),rough(V);
#   	vector<bool>skip(R+1);
#   	vector<LL>large(V);
#   	for(int i=0;i<V;++i)small[i]=i,rough[i]=i*2+1,large[i]=(fdiv(n,i*2+1)-1)>>1;
#   	const auto calc=[&](int p){
#   		skip[p]=1;
#   		for(int i=p*p;i<=R;i+=p+p)skip[i]=1;
#   		int m=0;
#   		for(int i=0;i<V;++i)if(!skip[rough[i]]){
#   			LL d=1LL*rough[i]*p;
#   			large[m]=large[i]-(d<=R?large[small[d>>1]-C]:small[(fdiv(n,d)-1)>>1])+C;
#   			rough[m++]=rough[i];
#   		}
#   		V=m,m=(R-1)>>1;
#   		for(int i=(R/p-1)|1;i>=p;i-=2){
#   			int s=small[i>>1]-C;
#   			for(int j=(i*p)>>1;j<=m;--m)small[m]-=s;
#   		}
#   		++C;
#   	};
#   	if(9<=R){
#   		calc(3);
#   		if(25<=R){
#   			calc(5);
#   			static const int wheel[8]={4,2,4,2,4,6,2,6};
#   			for(int p=7,c=0;p<=sqR;p+=wheel[(c++)&7])if(!skip[p])calc(p);
#   		}
#   	}
#   	LL z=large[0]+1+(V+C+C-2)*(V-1LL)/2;
#   	for(int i=1;i<V;++i)z-=large[i];
#   	for(int i=1;i<V;++i){
#   		int q=rough[i];
#   		LL y=fdiv(n,q);
#   		int e=small[(fdiv(y,q)-1)>>1]-C;
#   		if(e<i+1)break;
#   		for(int j=i+1;j<=e;++j)z+=small[(fdiv(y,rough[j])-1)>>1];
#   		z-=(e-i)*(C+i-1LL);
#   	}
#   	return z;
#   }
#   signed main(){
#   	LL n=read_u64();print_u64(pi(n));  //* cin>>n,cout<<pi(n)<<'\n'
#   	return 0;
#   }

prog = [
  # _start:
  0x00400137,  #     0: lui   sp,0x400
  0x435000ef,  #     4: jal   3128 <main>
  0x05d00893,  #     8: li    a7,93
  0x00000073,  #    12: ecall
  # memset:
  0x0ff5f593,  #    16: zext.ba1,a1
  0x00c50733,  #    20: add   a4,a0,a2
  0x00050793,  #    24: mv    a5,a0
  0x00060863,  #    28: beqz  a2,44
  0x00178793,  #    32: addi  a5,a5,1
  0xfeb78fa3,  #    36: sb    a1,-1(a5)
  0xfef71ce3,  #    40: bne   a4,a5,32
  0x00008067,  #    44: ret
  # pi(long long):
  0xf8010113,  #    48: addi  sp,sp,-128
  0x06112e23,  #    52: sw    ra,124(sp)
  0x05812c23,  #    56: sw    s8,88(sp)
  0x05912a23,  #    60: sw    s9,84(sp)
  0x00b12623,  #    64: sw    a1,12(sp)
  0x00a12823,  #    68: sw    a0,16(sp)
  0x4ab05a63,  #    72: blez  a1,1276
  0x01012783,  #    76: lw    a5,16(sp)
  0x00c12703,  #    80: lw    a4,12(sp)
  0x06812c23,  #    84: sw    s0,120(sp)
  0x00178413,  #    88: addi  s0,a5,1
  0x07212823,  #    92: sw    s2,112(sp)
  0x00f43933,  #    96: sltu  s2,s0,a5
  0x00e90933,  #   100: add   s2,s2,a4
  0x01f91793,  #   104: slli  a5,s2,0x1f
  0x00145413,  #   108: srli  s0,s0,0x1
  0x06912a23,  #   112: sw    s1,116(sp)
  0x07312623,  #   116: sw    s3,108(sp)
  0x07412423,  #   120: sw    s4,104(sp)
  0x07512223,  #   124: sw    s5,100(sp)
  0x07612023,  #   128: sw    s6,96(sp)
  0x05712e23,  #   132: sw    s7,92(sp)
  0x05a12823,  #   136: sw    s10,80(sp)
  0x05b12623,  #   140: sw    s11,76(sp)
  0x00195913,  #   144: srli  s2,s2,0x1
  0x0087e433,  #   148: or    s0,a5,s0
  0x6ee97463,  #   152: bgeu  s2,a4,1920
  0x01012503,  #   156: lw    a0,16(sp)
  0x00c12583,  #   160: lw    a1,12(sp)
  0x00090693,  #   164: mv    a3,s2
  0x00040613,  #   168: mv    a2,s0
  0x160010ef,  #   172: jal   4620 <__udivdi3>
  0x008507b3,  #   176: add   a5,a0,s0
  0x012585b3,  #   180: add   a1,a1,s2
  0x00a7b533,  #   184: sltu  a0,a5,a0
  0x00b50533,  #   188: add   a0,a0,a1
  0x00040493,  #   192: mv    s1,s0
  0x00090713,  #   196: mv    a4,s2
  0x01f51693,  #   200: slli  a3,a0,0x1f
  0x0017d413,  #   204: srli  s0,a5,0x1
  0x00155913,  #   208: srli  s2,a0,0x1
  0x0086e433,  #   212: or    s0,a3,s0
  0xfce962e3,  #   216: bltu  s2,a4,156
  0x01271463,  #   220: bne   a4,s2,228
  0xfa946ee3,  #   224: bltu  s0,s1,156
  0x00148b93,  #   228: addi  s7,s1,1
  0x41f4da13,  #   232: srai  s4,s1,0x1f
  0x009bb933,  #   236: sltu  s2,s7,s1
  0x01490933,  #   240: add   s2,s2,s4
  0x01f91793,  #   244: slli  a5,s2,0x1f
  0x001bd413,  #   248: srli  s0,s7,0x1
  0x0087e433,  #   252: or    s0,a5,s0
  0x00195913,  #   256: srli  s2,s2,0x1
  0x680a0863,  #   260: beqz  s4,1940
  0x00090693,  #   264: mv    a3,s2
  0x00040613,  #   268: mv    a2,s0
  0x00048513,  #   272: mv    a0,s1
  0x000a0593,  #   276: mv    a1,s4
  0x0f4010ef,  #   280: jal   4620 <__udivdi3>
  0x008507b3,  #   284: add   a5,a0,s0
  0x012585b3,  #   288: add   a1,a1,s2
  0x00a7b533,  #   292: sltu  a0,a5,a0
  0x00b50533,  #   296: add   a0,a0,a1
  0x00040b13,  #   300: mv    s6,s0
  0x00090713,  #   304: mv    a4,s2
  0x01f51693,  #   308: slli  a3,a0,0x1f
  0x0017d413,  #   312: srli  s0,a5,0x1
  0x00155913,  #   316: srli  s2,a0,0x1
  0x0086e433,  #   320: or    s0,a3,s0
  0xfce962e3,  #   324: bltu  s2,a4,264
  0x01271463,  #   328: bne   a4,s2,336
  0xfb646ee3,  #   332: bltu  s0,s6,264
  0x03612023,  #   336: sw    s6,32(sp)
  0x00001537,  #   340: lui   a0,0x1
  0x79852983,  #   344: lw    s3,1944(a0)
  0x01fbd793,  #   348: srli  a5,s7,0x1f
  0x017787b3,  #   352: add   a5,a5,s7
  0x4017d793,  #   356: srai  a5,a5,0x1
  0x00798993,  #   360: addi  s3,s3,7
  0x00279693,  #   364: slli  a3,a5,0x2
  0xff89f993,  #   368: andi  s3,s3,-8
  0x00768913,  #   372: addi  s2,a3,7
  0x01298933,  #   376: add   s2,s3,s2
  0xff897913,  #   380: andi  s2,s2,-8
  0x5e068263,  #   384: beqz  a3,1892
  0x00d985b3,  #   388: add   a1,s3,a3
  0x00098713,  #   392: mv    a4,s3
  0x00070023,  #   396: sb    zero,0(a4)
  0x00170713,  #   400: addi  a4,a4,1
  0xfeb71ce3,  #   404: bne   a4,a1,396
  0x00d906b3,  #   408: add   a3,s2,a3
  0x00090713,  #   412: mv    a4,s2
  0x00070023,  #   416: sb    zero,0(a4)
  0x00170713,  #   420: addi  a4,a4,1
  0xfed71ce3,  #   424: bne   a4,a3,416
  0x00768693,  #   428: addi  a3,a3,7
  0xff86f413,  #   432: andi  s0,a3,-8
  0x008b8633,  #   436: add   a2,s7,s0
  0x00040713,  #   440: mv    a4,s0
  0x5a0b8863,  #   444: beqz  s7,1900
  0x00070023,  #   448: sb    zero,0(a4)
  0x00170713,  #   452: addi  a4,a4,1
  0xfec71ce3,  #   456: bne   a4,a2,448
  0x00848a93,  #   460: addi  s5,s1,8
  0x01540ab3,  #   464: add   s5,s0,s5
  0xff8afa93,  #   468: andi  s5,s5,-8
  0x00379693,  #   472: slli  a3,a5,0x3
  0x00da8633,  #   476: add   a2,s5,a3
  0x78c52c23,  #   480: sw    a2,1944(a0)
  0x000a8713,  #   484: mv    a4,s5
  0x00068863,  #   488: beqz  a3,504
  0x00070023,  #   492: sb    zero,0(a4)
  0x00170713,  #   496: addi  a4,a4,1
  0xfec71ce3,  #   500: bne   a4,a2,492
  0x00100713,  #   504: li    a4,1
  0x0b775c63,  #   508: bge   a4,s7,692
  0x41390bb3,  #   512: sub   s7,s2,s3
  0x00000c13,  #   516: li    s8,0
  0x01212c23,  #   520: sw    s2,24(sp)
  0x000b8c93,  #   524: mv    s9,s7
  0x000c0913,  #   528: mv    s2,s8
  0x01012b83,  #   532: lw    s7,16(sp)
  0x00c12c03,  #   536: lw    s8,12(sp)
  0x00812a23,  #   540: sw    s0,20(sp)
  0x00912e23,  #   544: sw    s1,28(sp)
  0x00100d13,  #   548: li    s10,1
  0x00000d93,  #   552: li    s11,0
  0x000a8413,  #   556: mv    s0,s5
  0x00078b13,  #   560: mv    s6,a5
  0x00098493,  #   564: mv    s1,s3
  0x01b4a023,  #   568: sw    s11,0(s1)
  0x009c8633,  #   572: add   a2,s9,s1
  0x01a62023,  #   576: sw    s10,0(a2)
  0x00090693,  #   580: mv    a3,s2
  0x000d0613,  #   584: mv    a2,s10
  0x000b8513,  #   588: mv    a0,s7
  0x000c0593,  #   592: mv    a1,s8
  0x341000ef,  #   596: jal   3476 <__divdi3>
  0x00153613,  #   600: seqz  a2,a0
  0x40c585b3,  #   604: sub   a1,a1,a2
  0xfff50513,  #   608: addi  a0,a0,-1
  0x01f59813,  #   612: slli  a6,a1,0x1f
  0x00155513,  #   616: srli  a0,a0,0x1
  0x002d0613,  #   620: addi  a2,s10,2
  0x01056533,  #   624: or    a0,a0,a6
  0x4015d593,  #   628: srai  a1,a1,0x1
  0x01a63833,  #   632: sltu  a6,a2,s10
  0x00a42023,  #   636: sw    a0,0(s0)
  0x00b42223,  #   640: sw    a1,4(s0)
  0x001d8d93,  #   644: addi  s11,s11,1
  0x00448493,  #   648: addi  s1,s1,4
  0x00060d13,  #   652: mv    s10,a2
  0x01280933,  #   656: add   s2,a6,s2
  0x00840413,  #   660: addi  s0,s0,8
  0xfb6dc0e3,  #   664: blt   s11,s6,568
  0x01c12483,  #   668: lw    s1,28(sp)
  0x00800713,  #   672: li    a4,8
  0x01412403,  #   676: lw    s0,20(sp)
  0x01812903,  #   680: lw    s2,24(sp)
  0x000b0793,  #   684: mv    a5,s6
  0x2a974263,  #   688: blt   a4,s1,1364
  0x00078693,  #   692: mv    a3,a5
  0x00000713,  #   696: li    a4,0
  0x000aa303,  #   700: lw    t1,0(s5)
  0xffe68693,  #   704: addi  a3,a3,-2
  0x004aae03,  #   708: lw    t3,4(s5)
  0x0017b513,  #   712: seqz  a0,a5
  0x41f7d613,  #   716: srai  a2,a5,0x1f
  0xfff78813,  #   720: addi  a6,a5,-1
  0x41f6d593,  #   724: srai  a1,a3,0x1f
  0x40a60633,  #   728: sub   a2,a2,a0
  0x00130893,  #   732: addi  a7,t1,1
  0x02d60633,  #   736: mul   a2,a2,a3
  0x0068b333,  #   740: sltu  t1,a7,t1
  0x01c30333,  #   744: add   t1,t1,t3
  0x00100513,  #   748: li    a0,1
  0x030585b3,  #   752: mul   a1,a1,a6
  0x0306be33,  #   756: mulhu t3,a3,a6
  0x00c585b3,  #   760: add   a1,a1,a2
  0x030686b3,  #   764: mul   a3,a3,a6
  0x01c585b3,  #   768: add   a1,a1,t3
  0x01f5d613,  #   772: srli  a2,a1,0x1f
  0x00d606b3,  #   776: add   a3,a2,a3
  0x00c6b633,  #   780: sltu  a2,a3,a2
  0x00b60633,  #   784: add   a2,a2,a1
  0x01f61593,  #   788: slli  a1,a2,0x1f
  0x0016d693,  #   792: srli  a3,a3,0x1
  0x00d5e6b3,  #   796: or    a3,a1,a3
  0x011688b3,  #   800: add   a7,a3,a7
  0x40165613,  #   804: srai  a2,a2,0x1
  0x00d8b6b3,  #   808: sltu  a3,a7,a3
  0x00660633,  #   812: add   a2,a2,t1
  0x00088c13,  #   816: mv    s8,a7
  0x00c68cb3,  #   820: add   s9,a3,a2
  0x18f55063,  #   824: bge   a0,a5,1208
  0x00379313,  #   828: slli  t1,a5,0x3
  0x008a8693,  #   832: addi  a3,s5,8
  0x01530333,  #   836: add   t1,t1,s5
  0x0006a603,  #   840: lw    a2,0(a3)
  0x0046a503,  #   844: lw    a0,4(a3)
  0x00868693,  #   848: addi  a3,a3,8
  0x40cc0633,  #   852: sub   a2,s8,a2
  0x00cc35b3,  #   856: sltu  a1,s8,a2
  0x40ac8cb3,  #   860: sub   s9,s9,a0
  0x00060c13,  #   864: mv    s8,a2
  0x40bc8cb3,  #   868: sub   s9,s9,a1
  0xfe6690e3,  #   872: bne   a3,t1,840
  0x00490e13,  #   876: addi  t3,s2,4
  0x41f75693,  #   880: srai  a3,a4,0x1f
  0x00f12e23,  #   884: sw    a5,28(sp)
  0x000c8793,  #   888: mv    a5,s9
  0x00070b13,  #   892: mv    s6,a4
  0x00d12a23,  #   896: sw    a3,20(sp)
  0x000e0b93,  #   900: mv    s7,t3
  0x00100493,  #   904: li    s1,1
  0x00e12c23,  #   908: sw    a4,24(sp)
  0x03c12023,  #   912: sw    t3,32(sp)
  0x00060c93,  #   916: mv    s9,a2
  0x00078c13,  #   920: mv    s8,a5
  0x000ba403,  #   924: lw    s0,0(s7)
  0x01012503,  #   928: lw    a0,16(sp)
  0x00c12583,  #   932: lw    a1,12(sp)
  0x41f45913,  #   936: srai  s2,s0,0x1f
  0x00040613,  #   940: mv    a2,s0
  0x00090693,  #   944: mv    a3,s2
  0x1e1000ef,  #   948: jal   3476 <__divdi3>
  0x00040613,  #   952: mv    a2,s0
  0x00090693,  #   956: mv    a3,s2
  0x00050a13,  #   960: mv    s4,a0
  0x00058a93,  #   964: mv    s5,a1
  0x1cd000ef,  #   968: jal   3476 <__divdi3>
  0xfff50793,  #   972: addi  a5,a0,-1
  0x0017d793,  #   976: srli  a5,a5,0x1
  0x00279793,  #   980: slli  a5,a5,0x2
  0x00f987b3,  #   984: add   a5,s3,a5
  0x0007a403,  #   988: lw    s0,0(a5)
  0x01812783,  #   992: lw    a5,24(sp)
  0x40f40433,  #   996: sub   s0,s0,a5
  0x0c84d263,  #  1000: bge   s1,s0,1196
  0x00148d13,  #  1004: addi  s10,s1,1
  0x004b8b93,  #  1008: addi  s7,s7,4
  0x05a44e63,  #  1012: blt   s0,s10,1104
  0x02012783,  #  1016: lw    a5,32(sp)
  0x00241913,  #  1020: slli  s2,s0,0x2
  0x000b8d93,  #  1024: mv    s11,s7
  0x00f90933,  #  1028: add   s2,s2,a5
  0x000da603,  #  1032: lw    a2,0(s11)
  0x000a0513,  #  1036: mv    a0,s4
  0x000a8593,  #  1040: mv    a1,s5
  0x41f65693,  #  1044: srai  a3,a2,0x1f
  0x17d000ef,  #  1048: jal   3476 <__divdi3>
  0xfff50793,  #  1052: addi  a5,a0,-1
  0x0017d793,  #  1056: srli  a5,a5,0x1
  0x00279793,  #  1060: slli  a5,a5,0x2
  0x00f987b3,  #  1064: add   a5,s3,a5
  0x0007a783,  #  1068: lw    a5,0(a5)
  0x004d8d93,  #  1072: addi  s11,s11,4
  0x00fc86b3,  #  1076: add   a3,s9,a5
  0x41f7d793,  #  1080: srai  a5,a5,0x1f
  0x0196b633,  #  1084: sltu  a2,a3,s9
  0x00fc07b3,  #  1088: add   a5,s8,a5
  0x00068c93,  #  1092: mv    s9,a3
  0x00f60c33,  #  1096: add   s8,a2,a5
  0xfbb91ee3,  #  1100: bne   s2,s11,1032
  0x01412583,  #  1104: lw    a1,20(sp)
  0x40940433,  #  1108: sub   s0,s0,s1
  0x001b0693,  #  1112: addi  a3,s6,1
  0x41f45793,  #  1116: srai  a5,s0,0x1f
  0x0166b733,  #  1120: sltu  a4,a3,s6
  0x02858633,  #  1124: mul   a2,a1,s0
  0x00b70733,  #  1128: add   a4,a4,a1
  0x00e12a23,  #  1132: sw    a4,20(sp)
  0x036787b3,  #  1136: mul   a5,a5,s6
  0x03640733,  #  1140: mul   a4,s0,s6
  0x00c787b3,  #  1144: add   a5,a5,a2
  0x03643433,  #  1148: mulhu s0,s0,s6
  0x40ec8733,  #  1152: sub   a4,s9,a4
  0x00ecb633,  #  1156: sltu  a2,s9,a4
  0x00068b13,  #  1160: mv    s6,a3
  0x00070c93,  #  1164: mv    s9,a4
  0x008787b3,  #  1168: add   a5,a5,s0
  0x40fc07b3,  #  1172: sub   a5,s8,a5
  0x40c78c33,  #  1176: sub   s8,a5,a2
  0x01c12783,  #  1180: lw    a5,28(sp)
  0x00fd0663,  #  1184: beq   s10,a5,1196
  0x000d0493,  #  1188: mv    s1,s10
  0xef5ff06f,  #  1192: j     924
  0x000c0793,  #  1196: mv    a5,s8
  0x000c8c13,  #  1200: mv    s8,s9
  0x00078c93,  #  1204: mv    s9,a5
  0x07812403,  #  1208: lw    s0,120(sp)
  0x07c12083,  #  1212: lw    ra,124(sp)
  0x07412483,  #  1216: lw    s1,116(sp)
  0x07012903,  #  1220: lw    s2,112(sp)
  0x06c12983,  #  1224: lw    s3,108(sp)
  0x06812a03,  #  1228: lw    s4,104(sp)
  0x06412a83,  #  1232: lw    s5,100(sp)
  0x06012b03,  #  1236: lw    s6,96(sp)
  0x05c12b83,  #  1240: lw    s7,92(sp)
  0x05012d03,  #  1244: lw    s10,80(sp)
  0x04c12d83,  #  1248: lw    s11,76(sp)
  0x000c0513,  #  1252: mv    a0,s8
  0x000c8593,  #  1256: mv    a1,s9
  0x05812c03,  #  1260: lw    s8,88(sp)
  0x05412c83,  #  1264: lw    s9,84(sp)
  0x08010113,  #  1268: addi  sp,sp,128
  0x00008067,  #  1272: ret
  0x00059663,  #  1276: bnez  a1,1288
  0x00600793,  #  1280: li    a5,6
  0xb4a7e4e3,  #  1284: bltu  a5,a0,76
  0x00c12703,  #  1288: lw    a4,12(sp)
  0x00100793,  #  1292: li    a5,1
  0x24e05063,  #  1296: blez  a4,1872
  0x00c12683,  #  1300: lw    a3,12(sp)
  0x00100713,  #  1304: li    a4,1
  0x20d05e63,  #  1308: blez  a3,1848
  0x00c12683,  #  1312: lw    a3,12(sp)
  0x00e787b3,  #  1316: add   a5,a5,a4
  0x00100713,  #  1320: li    a4,1
  0x1ed05a63,  #  1324: blez  a3,1824
  0x07c12083,  #  1328: lw    ra,124(sp)
  0x00e78c33,  #  1332: add   s8,a5,a4
  0x41fc5c93,  #  1336: srai  s9,s8,0x1f
  0x000c0513,  #  1340: mv    a0,s8
  0x000c8593,  #  1344: mv    a1,s9
  0x05812c03,  #  1348: lw    s8,88(sp)
  0x05412c83,  #  1352: lw    s9,84(sp)
  0x08010113,  #  1356: addi  sp,sp,128
  0x00008067,  #  1360: ret
  0x00100713,  #  1364: li    a4,1
  0x00e401a3,  #  1368: sb    a4,3(s0)
  0x00100613,  #  1372: li    a2,1
  0x00900713,  #  1376: li    a4,9
  0x008706b3,  #  1380: add   a3,a4,s0
  0x00c68023,  #  1384: sb    a2,0(a3)
  0x00670713,  #  1388: addi  a4,a4,6
  0xfee4dae3,  #  1392: bge   s1,a4,1380
  0x00090c13,  #  1396: mv    s8,s2
  0x00090d13,  #  1400: mv    s10,s2
  0x00098c93,  #  1404: mv    s9,s3
  0x00040913,  #  1408: mv    s2,s0
  0x00000b93,  #  1412: li    s7,0
  0x00000d93,  #  1416: li    s11,0
  0x000a8413,  #  1420: mv    s0,s5
  0x00078993,  #  1424: mv    s3,a5
  0x00912c23,  #  1428: sw    s1,24(sp)
  0x0700006f,  #  1432: j     1544
  0x00135e93,  #  1436: srli  t4,t1,0x1
  0x002e9e93,  #  1440: slli  t4,t4,0x2
  0x01dc8eb3,  #  1444: add   t4,s9,t4
  0x01471663,  #  1448: bne   a4,s4,1460
  0x01812783,  #  1452: lw    a5,24(sp)
  0x0a67e463,  #  1456: bltu  a5,t1,1624
  0x000ea703,  #  1460: lw    a4,0(t4)
  0x00371713,  #  1464: slli  a4,a4,0x3
  0x00ea8733,  #  1468: add   a4,s5,a4
  0x00072683,  #  1472: lw    a3,0(a4)
  0x00472583,  #  1476: lw    a1,4(a4)
  0x40de06b3,  #  1480: sub   a3,t3,a3
  0x003b9613,  #  1484: slli  a2,s7,0x3
  0x00de3e33,  #  1488: sltu  t3,t3,a3
  0x40b488b3,  #  1492: sub   a7,s1,a1
  0x00ca8633,  #  1496: add   a2,s5,a2
  0x002b9713,  #  1500: slli  a4,s7,0x2
  0x41c888b3,  #  1504: sub   a7,a7,t3
  0x00d62023,  #  1508: sw    a3,0(a2)
  0x01162223,  #  1512: sw    a7,4(a2)
  0x00ed0733,  #  1516: add   a4,s10,a4
  0x01672023,  #  1520: sw    s6,0(a4)
  0x001b8b93,  #  1524: addi  s7,s7,1
  0x001d8d93,  #  1528: addi  s11,s11,1
  0x004c0c13,  #  1532: addi  s8,s8,4
  0x00840413,  #  1536: addi  s0,s0,8
  0x073dde63,  #  1540: bge   s11,s3,1664
  0x000c2b03,  #  1544: lw    s6,0(s8)
  0x41fb5613,  #  1548: srai  a2,s6,0x1f
  0x016905b3,  #  1552: add   a1,s2,s6
  0x001b1713,  #  1556: slli  a4,s6,0x1
  0x01fb5513,  #  1560: srli  a0,s6,0x1f
  0x00161693,  #  1564: slli  a3,a2,0x1
  0x0005c583,  #  1568: lbu   a1,0(a1)
  0x01670333,  #  1572: add   t1,a4,s6
  0x00d566b3,  #  1576: or    a3,a0,a3
  0x00e33733,  #  1580: sltu  a4,t1,a4
  0x00c686b3,  #  1584: add   a3,a3,a2
  0x00d70733,  #  1588: add   a4,a4,a3
  0xfc0590e3,  #  1592: bnez  a1,1528
  0x01012503,  #  1596: lw    a0,16(sp)
  0x00c12583,  #  1600: lw    a1,12(sp)
  0x00042e03,  #  1604: lw    t3,0(s0)
  0x00442483,  #  1608: lw    s1,4(s0)
  0x00030613,  #  1612: mv    a2,t1
  0x00070693,  #  1616: mv    a3,a4
  0xf4ea54e3,  #  1620: bge   s4,a4,1436
  0x01c12a23,  #  1624: sw    t3,20(sp)
  0x738000ef,  #  1628: jal   3476 <__divdi3>
  0xfff50713,  #  1632: addi  a4,a0,-1
  0x00175713,  #  1636: srli  a4,a4,0x1
  0x00271713,  #  1640: slli  a4,a4,0x2
  0x00ec8733,  #  1644: add   a4,s9,a4
  0x00072683,  #  1648: lw    a3,0(a4)
  0x01412e03,  #  1652: lw    t3,20(sp)
  0x41f6d593,  #  1656: srai  a1,a3,0x1f
  0xf4dff06f,  #  1660: j     1480
  0x01812483,  #  1664: lw    s1,24(sp)
  0x00300593,  #  1668: li    a1,3
  0x00090413,  #  1672: mv    s0,s2
  0x02b4c5b3,  #  1676: div   a1,s1,a1
  0xfff48793,  #  1680: addi  a5,s1,-1
  0x4017d313,  #  1684: srai  t1,a5,0x1
  0x000c8993,  #  1688: mv    s3,s9
  0x000d0913,  #  1692: mv    s2,s10
  0x00030793,  #  1696: mv    a5,t1
  0xffcc8893,  #  1700: addi  a7,s9,-4
  0x00200813,  #  1704: li    a6,2
  0xfff58593,  #  1708: addi  a1,a1,-1
  0x0015e593,  #  1712: ori   a1,a1,1
  0x00159513,  #  1716: slli  a0,a1,0x1
  0x00b50533,  #  1720: add   a0,a0,a1
  0x4015d713,  #  1724: srai  a4,a1,0x1
  0x00271713,  #  1728: slli  a4,a4,0x2
  0x00e98733,  #  1732: add   a4,s3,a4
  0x40155e13,  #  1736: srai  t3,a0,0x1
  0x00072603,  #  1740: lw    a2,0(a4)
  0x03c7c663,  #  1744: blt   a5,t3,1788
  0x00279793,  #  1748: slli  a5,a5,0x2
  0x002e1693,  #  1752: slli  a3,t3,0x2
  0x013787b3,  #  1756: add   a5,a5,s3
  0x011686b3,  #  1760: add   a3,a3,a7
  0x0007a703,  #  1764: lw    a4,0(a5)
  0xffc78793,  #  1768: addi  a5,a5,-4
  0x40c70733,  #  1772: sub   a4,a4,a2
  0x00e7a223,  #  1776: sw    a4,4(a5)
  0xfef698e3,  #  1780: bne   a3,a5,1764
  0xfffe0793,  #  1784: addi  a5,t3,-1
  0xffe58593,  #  1788: addi  a1,a1,-2
  0xffa50513,  #  1792: addi  a0,a0,-6
  0xfab84ce3,  #  1796: blt   a6,a1,1724
  0x01800793,  #  1800: li    a5,24
  0x0897cc63,  #  1804: blt   a5,s1,1956
  0x002b8693,  #  1808: addi  a3,s7,2
  0x000b8793,  #  1812: mv    a5,s7
  0x00100713,  #  1816: li    a4,1
  0xba1ff06f,  #  1820: j     700
  0x00069863,  #  1824: bnez  a3,1840
  0x01012603,  #  1828: lw    a2,16(sp)
  0x00400693,  #  1832: li    a3,4
  0xe0c6e2e3,  #  1836: bltu  a3,a2,1328
  0x00000713,  #  1840: li    a4,0
  0xdfdff06f,  #  1844: j     1328
  0x00069863,  #  1848: bnez  a3,1864
  0x01012603,  #  1852: lw    a2,16(sp)
  0x00200693,  #  1856: li    a3,2
  0xdcc6eee3,  #  1860: bltu  a3,a2,1312
  0x00000713,  #  1864: li    a4,0
  0xdd5ff06f,  #  1868: j     1312
  0x00071663,  #  1872: bnez  a4,1884
  0x01012703,  #  1876: lw    a4,16(sp)
  0xdae7eee3,  #  1880: bltu  a5,a4,1300
  0x00000793,  #  1884: li    a5,0
  0xdb5ff06f,  #  1888: j     1300
  0x00090693,  #  1892: mv    a3,s2
  0xa45ff06f,  #  1896: j     428
  0x00848493,  #  1900: addi  s1,s1,8
  0x00940433,  #  1904: add   s0,s0,s1
  0xff847a93,  #  1908: andi  s5,s0,-8
  0x79552c23,  #  1912: sw    s5,1944(a0)
  0xb39ff06f,  #  1916: j     692
  0x01271663,  #  1920: bne   a4,s2,1932
  0x01012783,  #  1924: lw    a5,16(sp)
  0x90f46ae3,  #  1928: bltu  s0,a5,156
  0x01012483,  #  1932: lw    s1,16(sp)
  0x955ff06f,  #  1936: j     228
  0x012a1463,  #  1940: bne   s4,s2,1948
  0x969468e3,  #  1944: bltu  s0,s1,264
  0x02912023,  #  1948: sw    s1,32(sp)
  0x9b5ff06f,  #  1952: j     340
  0x00100793,  #  1956: li    a5,1
  0x00f402a3,  #  1960: sb    a5,5(s0)
  0x00100693,  #  1964: li    a3,1
  0x01900793,  #  1968: li    a5,25
  0x00878733,  #  1972: add   a4,a5,s0
  0x00d70023,  #  1976: sb    a3,0(a4)
  0x00a78793,  #  1980: addi  a5,a5,10
  0xfef4dae3,  #  1984: bge   s1,a5,1972
  0x47705663,  #  1988: blez  s7,3120
  0x002b9b93,  #  1992: slli  s7,s7,0x2
  0x00000793,  #  1996: li    a5,0
  0x012b8bb3,  #  2000: add   s7,s7,s2
  0x00090d93,  #  2004: mv    s11,s2
  0x00098c93,  #  2008: mv    s9,s3
  0x00090d13,  #  2012: mv    s10,s2
  0x000a8c13,  #  2016: mv    s8,s5
  0x00040993,  #  2020: mv    s3,s0
  0x00612c23,  #  2024: sw    t1,24(sp)
  0x00078913,  #  2028: mv    s2,a5
  0x00912a23,  #  2032: sw    s1,20(sp)
  0x000dab03,  #  2036: lw    s6,0(s11)
  0x41fb5613,  #  2040: srai  a2,s6,0x1f
  0x016985b3,  #  2044: add   a1,s3,s6
  0x002b1713,  #  2048: slli  a4,s6,0x2
  0x01eb5513,  #  2052: srli  a0,s6,0x1e
  0x00261693,  #  2056: slli  a3,a2,0x2
  0x0005c583,  #  2060: lbu   a1,0(a1)
  0x01670333,  #  2064: add   t1,a4,s6
  0x00d566b3,  #  2068: or    a3,a0,a3
  0x00e33733,  #  2072: sltu  a4,t1,a4
  0x00c686b3,  #  2076: add   a3,a3,a2
  0x00d70733,  #  2080: add   a4,a4,a3
  0x08059663,  #  2084: bnez  a1,2224
  0x01012503,  #  2088: lw    a0,16(sp)
  0x00c12583,  #  2092: lw    a1,12(sp)
  0x000c2483,  #  2096: lw    s1,0(s8)
  0x004c2403,  #  2100: lw    s0,4(s8)
  0x00030613,  #  2104: mv    a2,t1
  0x00070693,  #  2108: mv    a3,a4
  0x2eea4a63,  #  2112: blt   s4,a4,2868
  0x00135e93,  #  2116: srli  t4,t1,0x1
  0x002e9e93,  #  2120: slli  t4,t4,0x2
  0x01dc8eb3,  #  2124: add   t4,s9,t4
  0x01471663,  #  2128: bne   a4,s4,2140
  0x01412783,  #  2132: lw    a5,20(sp)
  0x2c67ee63,  #  2136: bltu  a5,t1,2868
  0x000ea683,  #  2140: lw    a3,0(t4)
  0xfff68693,  #  2144: addi  a3,a3,-1
  0x00369693,  #  2148: slli  a3,a3,0x3
  0x00da86b3,  #  2152: add   a3,s5,a3
  0x0006a703,  #  2156: lw    a4,0(a3)
  0x0046a683,  #  2160: lw    a3,4(a3)
  0x40e48733,  #  2164: sub   a4,s1,a4
  0x00170513,  #  2168: addi  a0,a4,1
  0x00e4be33,  #  2172: sltu  t3,s1,a4
  0x40d40633,  #  2176: sub   a2,s0,a3
  0x00391593,  #  2180: slli  a1,s2,0x3
  0x41c60633,  #  2184: sub   a2,a2,t3
  0x00e53733,  #  2188: sltu  a4,a0,a4
  0x00ba85b3,  #  2192: add   a1,s5,a1
  0x00c70733,  #  2196: add   a4,a4,a2
  0x00291693,  #  2200: slli  a3,s2,0x2
  0x00e5a223,  #  2204: sw    a4,4(a1)
  0x00a5a023,  #  2208: sw    a0,0(a1)
  0x00dd0733,  #  2212: add   a4,s10,a3
  0x01672023,  #  2216: sw    s6,0(a4)
  0x00190913,  #  2220: addi  s2,s2,1
  0x004d8d93,  #  2224: addi  s11,s11,4
  0x008c0c13,  #  2228: addi  s8,s8,8
  0xf3bb9ee3,  #  2232: bne   s7,s11,2036
  0x01812303,  #  2236: lw    t1,24(sp)
  0x01412483,  #  2240: lw    s1,20(sp)
  0x00098413,  #  2244: mv    s0,s3
  0x00090793,  #  2248: mv    a5,s2
  0x000c8993,  #  2252: mv    s3,s9
  0x000d0913,  #  2256: mv    s2,s10
  0x00500513,  #  2260: li    a0,5
  0x02a4c533,  #  2264: div   a0,s1,a0
  0x00030713,  #  2268: mv    a4,t1
  0xffc98e13,  #  2272: addi  t3,s3,-4
  0x00400893,  #  2276: li    a7,4
  0xfff50513,  #  2280: addi  a0,a0,-1
  0x00156513,  #  2284: ori   a0,a0,1
  0x00251813,  #  2288: slli  a6,a0,0x2
  0x00a80833,  #  2292: add   a6,a6,a0
  0x40155693,  #  2296: srai  a3,a0,0x1
  0x00269693,  #  2300: slli  a3,a3,0x2
  0x00d986b3,  #  2304: add   a3,s3,a3
  0x0006a583,  #  2308: lw    a1,0(a3)
  0x40185e93,  #  2312: srai  t4,a6,0x1
  0xfff58593,  #  2316: addi  a1,a1,-1
  0x03d74663,  #  2320: blt   a4,t4,2364
  0x00271713,  #  2324: slli  a4,a4,0x2
  0x002e9613,  #  2328: slli  a2,t4,0x2
  0x01370733,  #  2332: add   a4,a4,s3
  0x01c60633,  #  2336: add   a2,a2,t3
  0x00072683,  #  2340: lw    a3,0(a4)
  0xffc70713,  #  2344: addi  a4,a4,-4
  0x40b686b3,  #  2348: sub   a3,a3,a1
  0x00d72223,  #  2352: sw    a3,4(a4)
  0xfee618e3,  #  2356: bne   a2,a4,2340
  0xfffe8713,  #  2360: addi  a4,t4,-1
  0xffe50513,  #  2364: addi  a0,a0,-2
  0xff680813,  #  2368: addi  a6,a6,-10
  0xfaa8cae3,  #  2372: blt   a7,a0,2296
  0x02012683,  #  2376: lw    a3,32(sp)
  0x00600713,  #  2380: li    a4,6
  0x2cd75a63,  #  2384: bge   a4,a3,3108
  0x00001bb7,  #  2388: lui   s7,0x1
  0xffc98b13,  #  2392: addi  s6,s3,-4
  0x00200713,  #  2396: li    a4,2
  0x00000d13,  #  2400: li    s10,0
  0x63cb8693,  #  2404: addi  a3,s7,1596
  0x02612e23,  #  2408: sw    t1,60(sp)
  0x00090c13,  #  2412: mv    s8,s2
  0x000a0313,  #  2416: mv    t1,s4
  0x000d0913,  #  2420: mv    s2,s10
  0x000a8a13,  #  2424: mv    s4,s5
  0x00078d13,  #  2428: mv    s10,a5
  0x00400f93,  #  2432: li    t6,4
  0x000b0793,  #  2436: mv    a5,s6
  0x00700d93,  #  2440: li    s11,7
  0x00098b13,  #  2444: mv    s6,s3
  0x00100c93,  #  2448: li    s9,1
  0x00070993,  #  2452: mv    s3,a4
  0x02d12223,  #  2456: sw    a3,36(sp)
  0x02012703,  #  2460: lw    a4,32(sp)
  0x00048593,  #  2464: mv    a1,s1
  0x00040a93,  #  2468: mv    s5,s0
  0x0240006f,  #  2472: j     2508
  0x01fd8db3,  #  2476: add   s11,s11,t6
  0x00190913,  #  2480: addi  s2,s2,1
  0x25b74463,  #  2484: blt   a4,s11,3068
  0x02412603,  #  2488: lw    a2,36(sp)
  0x00797693,  #  2492: andi  a3,s2,7
  0x00269693,  #  2496: slli  a3,a3,0x2
  0x00d606b3,  #  2500: add   a3,a2,a3
  0x0006af83,  #  2504: lw    t6,0(a3)
  0x01ba8633,  #  2508: add   a2,s5,s11
  0x00064683,  #  2512: lbu   a3,0(a2)
  0xfc069ce3,  #  2516: bnez  a3,2476
  0x03bd86b3,  #  2520: mul   a3,s11,s11
  0x01960023,  #  2524: sb    s9,0(a2)
  0x001d9513,  #  2528: slli  a0,s11,0x1
  0x00d5ca63,  #  2532: blt   a1,a3,2552
  0x01568633,  #  2536: add   a2,a3,s5
  0x01960023,  #  2540: sb    s9,0(a2)
  0x00a686b3,  #  2544: add   a3,a3,a0
  0xfed5dae3,  #  2548: bge   a1,a3,2536
  0x23a05263,  #  2552: blez  s10,3100
  0x002d1813,  #  2556: slli  a6,s10,0x2
  0x00000d13,  #  2560: li    s10,0
  0x01880833,  #  2564: add   a6,a6,s8
  0x000c0b93,  #  2568: mv    s7,s8
  0x03212623,  #  2572: sw    s2,44(sp)
  0x03f12a23,  #  2576: sw    t6,52(sp)
  0x000a0913,  #  2580: mv    s2,s4
  0x000c0f93,  #  2584: mv    t6,s8
  0x41f9de93,  #  2588: srai  t4,s3,0x1f
  0x000a8c13,  #  2592: mv    s8,s5
  0x02e12823,  #  2596: sw    a4,48(sp)
  0x000a0a93,  #  2600: mv    s5,s4
  0x02b12423,  #  2604: sw    a1,40(sp)
  0x000d8a13,  #  2608: mv    s4,s11
  0x02f12c23,  #  2612: sw    a5,56(sp)
  0x000d0d93,  #  2616: mv    s11,s10
  0x000b0d13,  #  2620: mv    s10,s6
  0x00098b13,  #  2624: mv    s6,s3
  0x0800006f,  #  2628: j     2756
  0x00639663,  #  2632: bne   t2,t1,2644
  0x02812783,  #  2636: lw    a5,40(sp)
  0x0ac7e263,  #  2640: bltu  a5,a2,2804
  0x00165693,  #  2644: srli  a3,a2,0x1
  0x00269693,  #  2648: slli  a3,a3,0x2
  0x00dd06b3,  #  2652: add   a3,s10,a3
  0x0006a603,  #  2656: lw    a2,0(a3)
  0x41660633,  #  2660: sub   a2,a2,s6
  0x00361613,  #  2664: slli  a2,a2,0x3
  0x00ca8633,  #  2668: add   a2,s5,a2
  0x00062683,  #  2672: lw    a3,0(a2)
  0x00462603,  #  2676: lw    a2,4(a2)
  0x40d986b3,  #  2680: sub   a3,s3,a3
  0x00d9b9b3,  #  2684: sltu  s3,s3,a3
  0x40c40633,  #  2688: sub   a2,s0,a2
  0x016685b3,  #  2692: add   a1,a3,s6
  0x41360633,  #  2696: sub   a2,a2,s3
  0x003d9393,  #  2700: slli  t2,s11,0x3
  0x00d5b6b3,  #  2704: sltu  a3,a1,a3
  0x01d60633,  #  2708: add   a2,a2,t4
  0x007a83b3,  #  2712: add   t2,s5,t2
  0x00c68633,  #  2716: add   a2,a3,a2
  0x002d9693,  #  2720: slli  a3,s11,0x2
  0x00b3a023,  #  2724: sw    a1,0(t2)
  0x00c3a223,  #  2728: sw    a2,4(t2)
  0x00df86b3,  #  2732: add   a3,t6,a3
  0x0096a023,  #  2736: sw    s1,0(a3)
  0x001d8d93,  #  2740: addi  s11,s11,1
  0x004b8b93,  #  2744: addi  s7,s7,4
  0x00890913,  #  2748: addi  s2,s2,8
  0x09780a63,  #  2752: beq   a6,s7,2900
  0x000ba483,  #  2756: lw    s1,0(s7)
  0x009c06b3,  #  2760: add   a3,s8,s1
  0x0006c683,  #  2764: lbu   a3,0(a3)
  0xfe0694e3,  #  2768: bnez  a3,2744
  0x034493b3,  #  2772: mulh  t2,s1,s4
  0x01012503,  #  2776: lw    a0,16(sp)
  0x00c12583,  #  2780: lw    a1,12(sp)
  0x00092983,  #  2784: lw    s3,0(s2)
  0x00492403,  #  2788: lw    s0,4(s2)
  0x03448633,  #  2792: mul   a2,s1,s4
  0x00038693,  #  2796: mv    a3,t2
  0xf4735ce3,  #  2800: bge   t1,t2,2632
  0x03d12023,  #  2804: sw    t4,32(sp)
  0x00612e23,  #  2808: sw    t1,28(sp)
  0x01f12c23,  #  2812: sw    t6,24(sp)
  0x01012a23,  #  2816: sw    a6,20(sp)
  0x290000ef,  #  2820: jal   3476 <__divdi3>
  0xfff50693,  #  2824: addi  a3,a0,-1
  0x0016d693,  #  2828: srli  a3,a3,0x1
  0x00269693,  #  2832: slli  a3,a3,0x2
  0x00dd06b3,  #  2836: add   a3,s10,a3
  0x0006a683,  #  2840: lw    a3,0(a3)
  0x02012e83,  #  2844: lw    t4,32(sp)
  0x01c12303,  #  2848: lw    t1,28(sp)
  0x01812f83,  #  2852: lw    t6,24(sp)
  0x01412803,  #  2856: lw    a6,20(sp)
  0x41f6d613,  #  2860: srai  a2,a3,0x1f
  0xf49ff06f,  #  2864: j     2680
  0x260000ef,  #  2868: jal   3476 <__divdi3>
  0xfff50713,  #  2872: addi  a4,a0,-1
  0x00175713,  #  2876: srli  a4,a4,0x1
  0x00271713,  #  2880: slli  a4,a4,0x2
  0x00ec8733,  #  2884: add   a4,s9,a4
  0x00072703,  #  2888: lw    a4,0(a4)
  0x41f75693,  #  2892: srai  a3,a4,0x1f
  0xd25ff06f,  #  2896: j     2164
  0x000b0993,  #  2900: mv    s3,s6
  0x02c12903,  #  2904: lw    s2,44(sp)
  0x000d0b13,  #  2908: mv    s6,s10
  0x03012703,  #  2912: lw    a4,48(sp)
  0x000d8d13,  #  2916: mv    s10,s11
  0x02812583,  #  2920: lw    a1,40(sp)
  0x000a0d93,  #  2924: mv    s11,s4
  0x03812783,  #  2928: lw    a5,56(sp)
  0x000a8a13,  #  2932: mv    s4,s5
  0x000c0a93,  #  2936: mv    s5,s8
  0x000f8c13,  #  2940: mv    s8,t6
  0x03412f83,  #  2944: lw    t6,52(sp)
  0x03b5ceb3,  #  2948: div   t4,a1,s11
  0xfffe8e93,  #  2952: addi  t4,t4,-1
  0x001eee93,  #  2956: ori   t4,t4,1
  0x07bec263,  #  2960: blt   t4,s11,3060
  0x03dd83b3,  #  2964: mul   t2,s11,t4
  0x03c12683,  #  2968: lw    a3,60(sp)
  0x41b00433,  #  2972: neg   s0,s11
  0x00141413,  #  2976: slli  s0,s0,0x1
  0x401ed613,  #  2980: srai  a2,t4,0x1
  0x00261613,  #  2984: slli  a2,a2,0x2
  0x00cb0633,  #  2988: add   a2,s6,a2
  0x00062803,  #  2992: lw    a6,0(a2)
  0x4013d893,  #  2996: srai  a7,t2,0x1
  0x41380833,  #  3000: sub   a6,a6,s3
  0x0316c663,  #  3004: blt   a3,a7,3048
  0x00269693,  #  3008: slli  a3,a3,0x2
  0x00289513,  #  3012: slli  a0,a7,0x2
  0x016686b3,  #  3016: add   a3,a3,s6
  0x00a78533,  #  3020: add   a0,a5,a0
  0x0006a603,  #  3024: lw    a2,0(a3)
  0xffc68693,  #  3028: addi  a3,a3,-4
  0x41060633,  #  3032: sub   a2,a2,a6
  0x00c6a223,  #  3036: sw    a2,4(a3)
  0xfed518e3,  #  3040: bne   a0,a3,3024
  0xfff88693,  #  3044: addi  a3,a7,-1
  0xffee8e93,  #  3048: addi  t4,t4,-2
  0x008383b3,  #  3052: add   t2,t2,s0
  0xfbbedae3,  #  3056: bge   t4,s11,2980
  0x00198993,  #  3060: addi  s3,s3,1
  0xdb5ff06f,  #  3064: j     2476
  0x00098713,  #  3068: mv    a4,s3
  0x00ed06b3,  #  3072: add   a3,s10,a4
  0x000b0993,  #  3076: mv    s3,s6
  0x000d0793,  #  3080: mv    a5,s10
  0x000a0a93,  #  3084: mv    s5,s4
  0x000c0913,  #  3088: mv    s2,s8
  0x00e686b3,  #  3092: add   a3,a3,a4
  0xea4ff06f,  #  3096: j     700
  0x00000d13,  #  3100: li    s10,0
  0xf65ff06f,  #  3104: j     2948
  0x00478693,  #  3108: addi  a3,a5,4
  0x00200713,  #  3112: li    a4,2
  0xe90ff06f,  #  3116: j     700
  0x00000793,  #  3120: li    a5,0
  0xca1ff06f,  #  3124: j     2260
  # main:
  0xfd010113,  #  3128: addi  sp,sp,-48
  0x02112623,  #  3132: sw    ra,44(sp)
  0x00c00893,  #  3136: li    a7,12
  0x00000073,  #  3140: ecall
  0x00900793,  #  3144: li    a5,9
  0xfd050513,  #  3148: addi  a0,a0,-48
  0x00a7fa63,  #  3152: bgeu  a5,a0,3172
  0x00c00893,  #  3156: li    a7,12
  0x00000073,  #  3160: ecall
  0xfd050513,  #  3164: addi  a0,a0,-48
  0xfea7eae3,  #  3168: bltu  a5,a0,3156
  0x00000793,  #  3172: li    a5,0
  0x00000593,  #  3176: li    a1,0
  0x00900813,  #  3180: li    a6,9
  0x01e7d613,  #  3184: srli  a2,a5,0x1e
  0x00279713,  #  3188: slli  a4,a5,0x2
  0x00259693,  #  3192: slli  a3,a1,0x2
  0x00f707b3,  #  3196: add   a5,a4,a5
  0x00d666b3,  #  3200: or    a3,a2,a3
  0x00b686b3,  #  3204: add   a3,a3,a1
  0x00e7b733,  #  3208: sltu  a4,a5,a4
  0x00d70733,  #  3212: add   a4,a4,a3
  0x00171713,  #  3216: slli  a4,a4,0x1
  0x01f7d693,  #  3220: srli  a3,a5,0x1f
  0x00179793,  #  3224: slli  a5,a5,0x1
  0x00f507b3,  #  3228: add   a5,a0,a5
  0x00e6e733,  #  3232: or    a4,a3,a4
  0x41f55593,  #  3236: srai  a1,a0,0x1f
  0x00e585b3,  #  3240: add   a1,a1,a4
  0x00a7b533,  #  3244: sltu  a0,a5,a0
  0x00b505b3,  #  3248: add   a1,a0,a1
  0x00c00893,  #  3252: li    a7,12
  0x00000073,  #  3256: ecall
  0xfd050513,  #  3260: addi  a0,a0,-48
  0xfaa878e3,  #  3264: bgeu  a6,a0,3184
  0x00078513,  #  3268: mv    a0,a5
  0xb68ff0ef,  #  3272: jal   48 <pi(long long)>
  0xccccd637,  #  3276: lui   a2,0xccccd
  0xccccde37,  #  3280: lui   t3,0xccccd
  0x00000813,  #  3284: li    a6,0
  0x00c10313,  #  3288: addi  t1,sp,12
  0x00500e93,  #  3292: li    t4,5
  0xccd60613,  #  3296: addi  a2,a2,-819
  0xccce0e13,  #  3300: addi  t3,t3,-820
  0x00900f13,  #  3304: li    t5,9
  0x00b507b3,  #  3308: add   a5,a0,a1
  0x00a7b733,  #  3312: sltu  a4,a5,a0
  0x00e787b3,  #  3316: add   a5,a5,a4
  0x03d7f7b3,  #  3320: remu  a5,a5,t4
  0x00058893,  #  3324: mv    a7,a1
  0x00180813,  #  3328: addi  a6,a6,1
  0x010306b3,  #  3332: add   a3,t1,a6
  0x00050293,  #  3336: mv    t0,a0
  0x40f507b3,  #  3340: sub   a5,a0,a5
  0x00f53733,  #  3344: sltu  a4,a0,a5
  0x40e585b3,  #  3348: sub   a1,a1,a4
  0x03c78fb3,  #  3352: mul   t6,a5,t3
  0x02c585b3,  #  3356: mul   a1,a1,a2
  0x02c7b733,  #  3360: mulhu a4,a5,a2
  0x01f585b3,  #  3364: add   a1,a1,t6
  0x02c787b3,  #  3368: mul   a5,a5,a2
  0x00e585b3,  #  3372: add   a1,a1,a4
  0x01f59713,  #  3376: slli  a4,a1,0x1f
  0x0015d593,  #  3380: srli  a1,a1,0x1
  0x0017d793,  #  3384: srli  a5,a5,0x1
  0x00f767b3,  #  3388: or    a5,a4,a5
  0x00279713,  #  3392: slli  a4,a5,0x2
  0x00f70733,  #  3396: add   a4,a4,a5
  0x00171713,  #  3400: slli  a4,a4,0x1
  0x40e50733,  #  3404: sub   a4,a0,a4
  0x03070713,  #  3408: addi  a4,a4,48
  0xfee68fa3,  #  3412: sb    a4,-1(a3)
  0x00078513,  #  3416: mv    a0,a5
  0xf80898e3,  #  3420: bnez  a7,3308
  0xf85f66e3,  #  3424: bltu  t5,t0,3308
  0x00068793,  #  3428: mv    a5,a3
  0xfff7c503,  #  3432: lbu   a0,-1(a5)
  0x00b00893,  #  3436: li    a7,11
  0x00000073,  #  3440: ecall
  0xfff78793,  #  3444: addi  a5,a5,-1
  0xfef318e3,  #  3448: bne   t1,a5,3432
  0x00a00513,  #  3452: li    a0,10
  0x00000073,  #  3456: ecall
  0x02c12083,  #  3460: lw    ra,44(sp)
  0x00000513,  #  3464: li    a0,0
  0x03010113,  #  3468: addi  sp,sp,48
  0x00008067,  #  3472: ret
  # __divdi3:
  0x00050313,  #  3476: mv    t1,a0
  0x00058e13,  #  3480: mv    t3,a1
  0x00000893,  #  3484: li    a7,0
  0x0005dc63,  #  3488: bgez  a1,3512
  0x00a037b3,  #  3492: snez  a5,a0
  0x40b00e33,  #  3496: neg   t3,a1
  0x40fe0e33,  #  3500: sub   t3,t3,a5
  0x40a00333,  #  3504: neg   t1,a0
  0xfff00893,  #  3508: li    a7,-1
  0x0006dc63,  #  3512: bgez  a3,3536
  0x00c037b3,  #  3516: snez  a5,a2
  0x40d006b3,  #  3520: neg   a3,a3
  0xfff8c893,  #  3524: not   a7,a7
  0x40f686b3,  #  3528: sub   a3,a3,a5
  0x40c00633,  #  3532: neg   a2,a2
  0x00060713,  #  3536: mv    a4,a2
  0x00030813,  #  3540: mv    a6,t1
  0x000e0793,  #  3544: mv    a5,t3
  0x28069c63,  #  3548: bnez  a3,4212
  0x00001597,  #  3552: auipc a1,0x1
  0x87c58593,  #  3556: addi  a1,a1,-1924
  0x0ece7663,  #  3560: bgeu  t3,a2,3796
  0x000106b7,  #  3564: lui   a3,0x10
  0x0cd67863,  #  3568: bgeu  a2,a3,3776
  0x10063693,  #  3572: sltiu a3,a2,256
  0x0016b693,  #  3576: seqz  a3,a3
  0x00369693,  #  3580: slli  a3,a3,0x3
  0x00d65533,  #  3584: srl   a0,a2,a3
  0x00a585b3,  #  3588: add   a1,a1,a0
  0x0005c583,  #  3592: lbu   a1,0(a1)
  0x02000513,  #  3596: li    a0,32
  0x00d586b3,  #  3600: add   a3,a1,a3
  0x40d505b3,  #  3604: sub   a1,a0,a3
  0x00d50c63,  #  3608: beq   a0,a3,3632
  0x00be17b3,  #  3612: sll   a5,t3,a1
  0x00d356b3,  #  3616: srl   a3,t1,a3
  0x00b61733,  #  3620: sll   a4,a2,a1
  0x00f6e7b3,  #  3624: or    a5,a3,a5
  0x00b31833,  #  3628: sll   a6,t1,a1
  0x01075593,  #  3632: srli  a1,a4,0x10
  0x02b7de33,  #  3636: divu  t3,a5,a1
  0x01071613,  #  3640: slli  a2,a4,0x10
  0x01065613,  #  3644: srli  a2,a2,0x10
  0x02b7f7b3,  #  3648: remu  a5,a5,a1
  0x000e0513,  #  3652: mv    a0,t3
  0x03c60333,  #  3656: mul   t1,a2,t3
  0x01079693,  #  3660: slli  a3,a5,0x10
  0x01085793,  #  3664: srli  a5,a6,0x10
  0x00d7e7b3,  #  3668: or    a5,a5,a3
  0x0067fe63,  #  3672: bgeu  a5,t1,3700
  0x00f707b3,  #  3676: add   a5,a4,a5
  0xfffe0513,  #  3680: addi  a0,t3,-1
  0x00e7e863,  #  3684: bltu  a5,a4,3700
  0x0067f663,  #  3688: bgeu  a5,t1,3700
  0xffee0513,  #  3692: addi  a0,t3,-2
  0x00e787b3,  #  3696: add   a5,a5,a4
  0x406787b3,  #  3700: sub   a5,a5,t1
  0x02b7d333,  #  3704: divu  t1,a5,a1
  0x01081813,  #  3708: slli  a6,a6,0x10
  0x01085813,  #  3712: srli  a6,a6,0x10
  0x02b7f7b3,  #  3716: remu  a5,a5,a1
  0x026606b3,  #  3720: mul   a3,a2,t1
  0x01079793,  #  3724: slli  a5,a5,0x10
  0x00f86833,  #  3728: or    a6,a6,a5
  0x00030793,  #  3732: mv    a5,t1
  0x00d87c63,  #  3736: bgeu  a6,a3,3760
  0x01070833,  #  3740: add   a6,a4,a6
  0xfff30793,  #  3744: addi  a5,t1,-1
  0x00e86663,  #  3748: bltu  a6,a4,3760
  0x00d87463,  #  3752: bgeu  a6,a3,3760
  0xffe30793,  #  3756: addi  a5,t1,-2
  0x01051513,  #  3760: slli  a0,a0,0x10
  0x00f56533,  #  3764: or    a0,a0,a5
  0x00000593,  #  3768: li    a1,0
  0x0e00006f,  #  3772: j     3996
  0x01000537,  #  3776: lui   a0,0x1000
  0x01800693,  #  3780: li    a3,24
  0xf2a67ce3,  #  3784: bgeu  a2,a0,3584
  0x01000693,  #  3788: li    a3,16
  0xf31ff06f,  #  3792: j     3584
  0x00000693,  #  3796: li    a3,0
  0x00060c63,  #  3800: beqz  a2,3824
  0x000107b7,  #  3804: lui   a5,0x10
  0x0cf67a63,  #  3808: bgeu  a2,a5,4020
  0x10063693,  #  3812: sltiu a3,a2,256
  0x0016b693,  #  3816: seqz  a3,a3
  0x00369693,  #  3820: slli  a3,a3,0x3
  0x00d657b3,  #  3824: srl   a5,a2,a3
  0x00f585b3,  #  3828: add   a1,a1,a5
  0x0005c783,  #  3832: lbu   a5,0(a1)
  0x00d787b3,  #  3836: add   a5,a5,a3
  0x02000693,  #  3840: li    a3,32
  0x40f685b3,  #  3844: sub   a1,a3,a5
  0x0cf69063,  #  3848: bne   a3,a5,4040
  0x40ce07b3,  #  3852: sub   a5,t3,a2
  0x00100593,  #  3856: li    a1,1
  0x01075313,  #  3860: srli  t1,a4,0x10
  0x0267deb3,  #  3864: divu  t4,a5,t1
  0x01071613,  #  3868: slli  a2,a4,0x10
  0x01065613,  #  3872: srli  a2,a2,0x10
  0x01085693,  #  3876: srli  a3,a6,0x10
  0x0267f7b3,  #  3880: remu  a5,a5,t1
  0x000e8513,  #  3884: mv    a0,t4
  0x03d60e33,  #  3888: mul   t3,a2,t4
  0x01079793,  #  3892: slli  a5,a5,0x10
  0x00f6e7b3,  #  3896: or    a5,a3,a5
  0x01c7fe63,  #  3900: bgeu  a5,t3,3928
  0x00f707b3,  #  3904: add   a5,a4,a5
  0xfffe8513,  #  3908: addi  a0,t4,-1
  0x00e7e863,  #  3912: bltu  a5,a4,3928
  0x01c7f663,  #  3916: bgeu  a5,t3,3928
  0xffee8513,  #  3920: addi  a0,t4,-2
  0x00e787b3,  #  3924: add   a5,a5,a4
  0x41c787b3,  #  3928: sub   a5,a5,t3
  0x0267de33,  #  3932: divu  t3,a5,t1
  0x01081813,  #  3936: slli  a6,a6,0x10
  0x01085813,  #  3940: srli  a6,a6,0x10
  0x0267f7b3,  #  3944: remu  a5,a5,t1
  0x03c606b3,  #  3948: mul   a3,a2,t3
  0x01079793,  #  3952: slli  a5,a5,0x10
  0x00f86833,  #  3956: or    a6,a6,a5
  0x000e0793,  #  3960: mv    a5,t3
  0x00d87c63,  #  3964: bgeu  a6,a3,3988
  0x01070833,  #  3968: add   a6,a4,a6
  0xfffe0793,  #  3972: addi  a5,t3,-1
  0x00e86663,  #  3976: bltu  a6,a4,3988
  0x00d87463,  #  3980: bgeu  a6,a3,3988
  0xffee0793,  #  3984: addi  a5,t3,-2
  0x01051513,  #  3988: slli  a0,a0,0x10
  0x00f56533,  #  3992: or    a0,a0,a5
  0x00088a63,  #  3996: beqz  a7,4016
  0x00a037b3,  #  4000: snez  a5,a0
  0x40b005b3,  #  4004: neg   a1,a1
  0x40f585b3,  #  4008: sub   a1,a1,a5
  0x40a00533,  #  4012: neg   a0,a0
  0x00008067,  #  4016: ret
  0x010007b7,  #  4020: lui   a5,0x1000
  0x01800693,  #  4024: li    a3,24
  0xf2f67ae3,  #  4028: bgeu  a2,a5,3824
  0x01000693,  #  4032: li    a3,16
  0xf2dff06f,  #  4036: j     3824
  0x00b61733,  #  4040: sll   a4,a2,a1
  0x00fe56b3,  #  4044: srl   a3,t3,a5
  0x01075513,  #  4048: srli  a0,a4,0x10
  0x00be1e33,  #  4052: sll   t3,t3,a1
  0x00f357b3,  #  4056: srl   a5,t1,a5
  0x01c7e7b3,  #  4060: or    a5,a5,t3
  0x02a6de33,  #  4064: divu  t3,a3,a0
  0x01071613,  #  4068: slli  a2,a4,0x10
  0x01065613,  #  4072: srli  a2,a2,0x10
  0x00b31833,  #  4076: sll   a6,t1,a1
  0x02a6f6b3,  #  4080: remu  a3,a3,a0
  0x03c60333,  #  4084: mul   t1,a2,t3
  0x01069593,  #  4088: slli  a1,a3,0x10
  0x0107d693,  #  4092: srli  a3,a5,0x10
  0x00b6e6b3,  #  4096: or    a3,a3,a1
  0x000e0593,  #  4100: mv    a1,t3
  0x0066fe63,  #  4104: bgeu  a3,t1,4132
  0x00d706b3,  #  4108: add   a3,a4,a3
  0xfffe0593,  #  4112: addi  a1,t3,-1
  0x00e6e863,  #  4116: bltu  a3,a4,4132
  0x0066f663,  #  4120: bgeu  a3,t1,4132
  0xffee0593,  #  4124: addi  a1,t3,-2
  0x00e686b3,  #  4128: add   a3,a3,a4
  0x406686b3,  #  4132: sub   a3,a3,t1
  0x02a6d333,  #  4136: divu  t1,a3,a0
  0x01079793,  #  4140: slli  a5,a5,0x10
  0x0107d793,  #  4144: srli  a5,a5,0x10
  0x02a6f6b3,  #  4148: remu  a3,a3,a0
  0x02660633,  #  4152: mul   a2,a2,t1
  0x01069693,  #  4156: slli  a3,a3,0x10
  0x00d7e7b3,  #  4160: or    a5,a5,a3
  0x00030693,  #  4164: mv    a3,t1
  0x00c7fe63,  #  4168: bgeu  a5,a2,4196
  0x00f707b3,  #  4172: add   a5,a4,a5
  0xfff30693,  #  4176: addi  a3,t1,-1
  0x00e7e863,  #  4180: bltu  a5,a4,4196
  0x00c7f663,  #  4184: bgeu  a5,a2,4196
  0xffe30693,  #  4188: addi  a3,t1,-2
  0x00e787b3,  #  4192: add   a5,a5,a4
  0x01059593,  #  4196: slli  a1,a1,0x10
  0x40c787b3,  #  4200: sub   a5,a5,a2
  0x00d5e5b3,  #  4204: or    a1,a1,a3
  0xea5ff06f,  #  4208: j     3860
  0x18de6663,  #  4212: bltu  t3,a3,4608
  0x000107b7,  #  4216: lui   a5,0x10
  0x04f6f463,  #  4220: bgeu  a3,a5,4292
  0x1006b713,  #  4224: sltiu a4,a3,256
  0x00173713,  #  4228: seqz  a4,a4
  0x00371713,  #  4232: slli  a4,a4,0x3
  0x00e6d5b3,  #  4236: srl   a1,a3,a4
  0x00000797,  #  4240: auipc a5,0x0
  0x5cc78793,  #  4244: addi  a5,a5,1484
  0x00b787b3,  #  4248: add   a5,a5,a1
  0x0007c783,  #  4252: lbu   a5,0(a5)
  0x00e787b3,  #  4256: add   a5,a5,a4
  0x02000713,  #  4260: li    a4,32
  0x40f705b3,  #  4264: sub   a1,a4,a5
  0x02f71663,  #  4268: bne   a4,a5,4312
  0x00100513,  #  4272: li    a0,1
  0xefc6e4e3,  #  4276: bltu  a3,t3,3996
  0x00c33533,  #  4280: sltu  a0,t1,a2
  0x00153513,  #  4284: seqz  a0,a0
  0xeddff06f,  #  4288: j     3996
  0x010007b7,  #  4292: lui   a5,0x1000
  0x01800713,  #  4296: li    a4,24
  0xfcf6f0e3,  #  4300: bgeu  a3,a5,4236
  0x01000713,  #  4304: li    a4,16
  0xfb9ff06f,  #  4308: j     4236
  0x00f65733,  #  4312: srl   a4,a2,a5
  0x00b696b3,  #  4316: sll   a3,a3,a1
  0x00d766b3,  #  4320: or    a3,a4,a3
  0x00fe5733,  #  4324: srl   a4,t3,a5
  0x00be1e33,  #  4328: sll   t3,t3,a1
  0x00f357b3,  #  4332: srl   a5,t1,a5
  0x01c7e7b3,  #  4336: or    a5,a5,t3
  0x0106de13,  #  4340: srli  t3,a3,0x10
  0x03c75f33,  #  4344: divu  t5,a4,t3
  0x01069813,  #  4348: slli  a6,a3,0x10
  0x01085813,  #  4352: srli  a6,a6,0x10
  0x00b61633,  #  4356: sll   a2,a2,a1
  0x03c77733,  #  4360: remu  a4,a4,t3
  0x03e80eb3,  #  4364: mul   t4,a6,t5
  0x01071513,  #  4368: slli  a0,a4,0x10
  0x0107d713,  #  4372: srli  a4,a5,0x10
  0x00a76733,  #  4376: or    a4,a4,a0
  0x000f0513,  #  4380: mv    a0,t5
  0x01d77e63,  #  4384: bgeu  a4,t4,4412
  0x00e68733,  #  4388: add   a4,a3,a4
  0xffff0513,  #  4392: addi  a0,t5,-1
  0x00d76863,  #  4396: bltu  a4,a3,4412
  0x01d77663,  #  4400: bgeu  a4,t4,4412
  0xffef0513,  #  4404: addi  a0,t5,-2
  0x00d70733,  #  4408: add   a4,a4,a3
  0x41d70733,  #  4412: sub   a4,a4,t4
  0x03c75eb3,  #  4416: divu  t4,a4,t3
  0x01079793,  #  4420: slli  a5,a5,0x10
  0x0107d793,  #  4424: srli  a5,a5,0x10
  0x03c77733,  #  4428: remu  a4,a4,t3
  0x03d80833,  #  4432: mul   a6,a6,t4
  0x01071713,  #  4436: slli  a4,a4,0x10
  0x00e7e7b3,  #  4440: or    a5,a5,a4
  0x000e8713,  #  4444: mv    a4,t4
  0x0107fe63,  #  4448: bgeu  a5,a6,4476
  0x00f687b3,  #  4452: add   a5,a3,a5
  0xfffe8713,  #  4456: addi  a4,t4,-1
  0x00d7e863,  #  4460: bltu  a5,a3,4476
  0x0107f663,  #  4464: bgeu  a5,a6,4476
  0xffee8713,  #  4468: addi  a4,t4,-2
  0x00d787b3,  #  4472: add   a5,a5,a3
  0x01051513,  #  4476: slli  a0,a0,0x10
  0x00010eb7,  #  4480: lui   t4,0x10
  0x00e56533,  #  4484: or    a0,a0,a4
  0xfffe8693,  #  4488: addi  a3,t4,-1
  0x00d57733,  #  4492: and   a4,a0,a3
  0x410787b3,  #  4496: sub   a5,a5,a6
  0x00d676b3,  #  4500: and   a3,a2,a3
  0x01055813,  #  4504: srli  a6,a0,0x10
  0x01065613,  #  4508: srli  a2,a2,0x10
  0x02d70e33,  #  4512: mul   t3,a4,a3
  0x02d806b3,  #  4516: mul   a3,a6,a3
  0x02c70733,  #  4520: mul   a4,a4,a2
  0x02c80833,  #  4524: mul   a6,a6,a2
  0x00d70633,  #  4528: add   a2,a4,a3
  0x010e5713,  #  4532: srli  a4,t3,0x10
  0x00c70733,  #  4536: add   a4,a4,a2
  0x00d77463,  #  4540: bgeu  a4,a3,4548
  0x01d80833,  #  4544: add   a6,a6,t4
  0x01075693,  #  4548: srli  a3,a4,0x10
  0x010686b3,  #  4552: add   a3,a3,a6
  0x02d7e663,  #  4556: bltu  a5,a3,4600
  0xced794e3,  #  4560: bne   a5,a3,3768
  0x000107b7,  #  4564: lui   a5,0x10
  0xfff78793,  #  4568: addi  a5,a5,-1
  0x00f77733,  #  4572: and   a4,a4,a5
  0x01071713,  #  4576: slli  a4,a4,0x10
  0x00fe7e33,  #  4580: and   t3,t3,a5
  0x00b31333,  #  4584: sll   t1,t1,a1
  0x01c70733,  #  4588: add   a4,a4,t3
  0x00000593,  #  4592: li    a1,0
  0xdae374e3,  #  4596: bgeu  t1,a4,3996
  0xfff50513,  #  4600: addi  a0,a0,-1
  0xcbdff06f,  #  4604: j     3768
  0x00000593,  #  4608: li    a1,0
  0x00000513,  #  4612: li    a0,0
  0xd95ff06f,  #  4616: j     3996
  # __udivdi3:
  0x00050893,  #  4620: mv    a7,a0
  0x00058313,  #  4624: mv    t1,a1
  0x00060713,  #  4628: mv    a4,a2
  0x00050813,  #  4632: mv    a6,a0
  0x00058793,  #  4636: mv    a5,a1
  0x28069263,  #  4640: bnez  a3,5284
  0x00000597,  #  4644: auipc a1,0x0
  0x43858593,  #  4648: addi  a1,a1,1080
  0x0ec37663,  #  4652: bgeu  t1,a2,4888
  0x000106b7,  #  4656: lui   a3,0x10
  0x0cd67863,  #  4660: bgeu  a2,a3,4868
  0x10063693,  #  4664: sltiu a3,a2,256
  0x0016b693,  #  4668: seqz  a3,a3
  0x00369693,  #  4672: slli  a3,a3,0x3
  0x00d65533,  #  4676: srl   a0,a2,a3
  0x00a585b3,  #  4680: add   a1,a1,a0
  0x0005c583,  #  4684: lbu   a1,0(a1)
  0x02000513,  #  4688: li    a0,32
  0x00d586b3,  #  4692: add   a3,a1,a3
  0x40d505b3,  #  4696: sub   a1,a0,a3
  0x00d50c63,  #  4700: beq   a0,a3,4724
  0x00b317b3,  #  4704: sll   a5,t1,a1
  0x00d8d6b3,  #  4708: srl   a3,a7,a3
  0x00b61733,  #  4712: sll   a4,a2,a1
  0x00f6e7b3,  #  4716: or    a5,a3,a5
  0x00b89833,  #  4720: sll   a6,a7,a1
  0x01075593,  #  4724: srli  a1,a4,0x10
  0x02b7d333,  #  4728: divu  t1,a5,a1
  0x01071613,  #  4732: slli  a2,a4,0x10
  0x01065613,  #  4736: srli  a2,a2,0x10
  0x02b7f7b3,  #  4740: remu  a5,a5,a1
  0x00030513,  #  4744: mv    a0,t1
  0x026608b3,  #  4748: mul   a7,a2,t1
  0x01079693,  #  4752: slli  a3,a5,0x10
  0x01085793,  #  4756: srli  a5,a6,0x10
  0x00d7e7b3,  #  4760: or    a5,a5,a3
  0x0117fe63,  #  4764: bgeu  a5,a7,4792
  0x00f707b3,  #  4768: add   a5,a4,a5
  0xfff30513,  #  4772: addi  a0,t1,-1
  0x00e7e863,  #  4776: bltu  a5,a4,4792
  0x0117f663,  #  4780: bgeu  a5,a7,4792
  0xffe30513,  #  4784: addi  a0,t1,-2
  0x00e787b3,  #  4788: add   a5,a5,a4
  0x411787b3,  #  4792: sub   a5,a5,a7
  0x02b7d8b3,  #  4796: divu  a7,a5,a1
  0x01081813,  #  4800: slli  a6,a6,0x10
  0x01085813,  #  4804: srli  a6,a6,0x10
  0x02b7f7b3,  #  4808: remu  a5,a5,a1
  0x031606b3,  #  4812: mul   a3,a2,a7
  0x01079793,  #  4816: slli  a5,a5,0x10
  0x00f86833,  #  4820: or    a6,a6,a5
  0x00088793,  #  4824: mv    a5,a7
  0x00d87c63,  #  4828: bgeu  a6,a3,4852
  0x01070833,  #  4832: add   a6,a4,a6
  0xfff88793,  #  4836: addi  a5,a7,-1
  0x00e86663,  #  4840: bltu  a6,a4,4852
  0x00d87463,  #  4844: bgeu  a6,a3,4852
  0xffe88793,  #  4848: addi  a5,a7,-2
  0x01051513,  #  4852: slli  a0,a0,0x10
  0x00f56533,  #  4856: or    a0,a0,a5
  0x00000593,  #  4860: li    a1,0
  0x00008067,  #  4864: ret
  0x01000537,  #  4868: lui   a0,0x1000
  0x01800693,  #  4872: li    a3,24
  0xf2a67ce3,  #  4876: bgeu  a2,a0,4676
  0x01000693,  #  4880: li    a3,16
  0xf31ff06f,  #  4884: j     4676
  0x00000693,  #  4888: li    a3,0
  0x00060c63,  #  4892: beqz  a2,4916
  0x000107b7,  #  4896: lui   a5,0x10
  0x0cf67063,  #  4900: bgeu  a2,a5,5092
  0x10063693,  #  4904: sltiu a3,a2,256
  0x0016b693,  #  4908: seqz  a3,a3
  0x00369693,  #  4912: slli  a3,a3,0x3
  0x00d657b3,  #  4916: srl   a5,a2,a3
  0x00f585b3,  #  4920: add   a1,a1,a5
  0x0005c783,  #  4924: lbu   a5,0(a1)
  0x00d787b3,  #  4928: add   a5,a5,a3
  0x02000693,  #  4932: li    a3,32
  0x40f685b3,  #  4936: sub   a1,a3,a5
  0x0af69663,  #  4940: bne   a3,a5,5112
  0x40c307b3,  #  4944: sub   a5,t1,a2
  0x00100593,  #  4948: li    a1,1
  0x01075893,  #  4952: srli  a7,a4,0x10
  0x0317de33,  #  4956: divu  t3,a5,a7
  0x01071613,  #  4960: slli  a2,a4,0x10
  0x01065613,  #  4964: srli  a2,a2,0x10
  0x01085693,  #  4968: srli  a3,a6,0x10
  0x0317f7b3,  #  4972: remu  a5,a5,a7
  0x000e0513,  #  4976: mv    a0,t3
  0x03c60333,  #  4980: mul   t1,a2,t3
  0x01079793,  #  4984: slli  a5,a5,0x10
  0x00f6e7b3,  #  4988: or    a5,a3,a5
  0x0067fe63,  #  4992: bgeu  a5,t1,5020
  0x00f707b3,  #  4996: add   a5,a4,a5
  0xfffe0513,  #  5000: addi  a0,t3,-1
  0x00e7e863,  #  5004: bltu  a5,a4,5020
  0x0067f663,  #  5008: bgeu  a5,t1,5020
  0xffee0513,  #  5012: addi  a0,t3,-2
  0x00e787b3,  #  5016: add   a5,a5,a4
  0x406787b3,  #  5020: sub   a5,a5,t1
  0x0317d333,  #  5024: divu  t1,a5,a7
  0x01081813,  #  5028: slli  a6,a6,0x10
  0x01085813,  #  5032: srli  a6,a6,0x10
  0x0317f7b3,  #  5036: remu  a5,a5,a7
  0x026606b3,  #  5040: mul   a3,a2,t1
  0x01079793,  #  5044: slli  a5,a5,0x10
  0x00f86833,  #  5048: or    a6,a6,a5
  0x00030793,  #  5052: mv    a5,t1
  0x00d87c63,  #  5056: bgeu  a6,a3,5080
  0x01070833,  #  5060: add   a6,a4,a6
  0xfff30793,  #  5064: addi  a5,t1,-1
  0x00e86663,  #  5068: bltu  a6,a4,5080
  0x00d87463,  #  5072: bgeu  a6,a3,5080
  0xffe30793,  #  5076: addi  a5,t1,-2
  0x01051513,  #  5080: slli  a0,a0,0x10
  0x00f56533,  #  5084: or    a0,a0,a5
  0x00008067,  #  5088: ret
  0x010007b7,  #  5092: lui   a5,0x1000
  0x01800693,  #  5096: li    a3,24
  0xf4f674e3,  #  5100: bgeu  a2,a5,4916
  0x01000693,  #  5104: li    a3,16
  0xf41ff06f,  #  5108: j     4916
  0x00b61733,  #  5112: sll   a4,a2,a1
  0x00f356b3,  #  5116: srl   a3,t1,a5
  0x01075513,  #  5120: srli  a0,a4,0x10
  0x00b31333,  #  5124: sll   t1,t1,a1
  0x00f8d7b3,  #  5128: srl   a5,a7,a5
  0x0067e7b3,  #  5132: or    a5,a5,t1
  0x02a6d333,  #  5136: divu  t1,a3,a0
  0x01071613,  #  5140: slli  a2,a4,0x10
  0x01065613,  #  5144: srli  a2,a2,0x10
  0x00b89833,  #  5148: sll   a6,a7,a1
  0x02a6f6b3,  #  5152: remu  a3,a3,a0
  0x026608b3,  #  5156: mul   a7,a2,t1
  0x01069593,  #  5160: slli  a1,a3,0x10
  0x0107d693,  #  5164: srli  a3,a5,0x10
  0x00b6e6b3,  #  5168: or    a3,a3,a1
  0x00030593,  #  5172: mv    a1,t1
  0x0116fe63,  #  5176: bgeu  a3,a7,5204
  0x00d706b3,  #  5180: add   a3,a4,a3
  0xfff30593,  #  5184: addi  a1,t1,-1
  0x00e6e863,  #  5188: bltu  a3,a4,5204
  0x0116f663,  #  5192: bgeu  a3,a7,5204
  0xffe30593,  #  5196: addi  a1,t1,-2
  0x00e686b3,  #  5200: add   a3,a3,a4
  0x411686b3,  #  5204: sub   a3,a3,a7
  0x02a6d8b3,  #  5208: divu  a7,a3,a0
  0x01079793,  #  5212: slli  a5,a5,0x10
  0x0107d793,  #  5216: srli  a5,a5,0x10
  0x02a6f6b3,  #  5220: remu  a3,a3,a0
  0x03160633,  #  5224: mul   a2,a2,a7
  0x01069693,  #  5228: slli  a3,a3,0x10
  0x00d7e7b3,  #  5232: or    a5,a5,a3
  0x00088693,  #  5236: mv    a3,a7
  0x00c7fe63,  #  5240: bgeu  a5,a2,5268
  0x00f707b3,  #  5244: add   a5,a4,a5
  0xfff88693,  #  5248: addi  a3,a7,-1
  0x00e7e863,  #  5252: bltu  a5,a4,5268
  0x00c7f663,  #  5256: bgeu  a5,a2,5268
  0xffe88693,  #  5260: addi  a3,a7,-2
  0x00e787b3,  #  5264: add   a5,a5,a4
  0x01059593,  #  5268: slli  a1,a1,0x10
  0x40c787b3,  #  5272: sub   a5,a5,a2
  0x00d5e5b3,  #  5276: or    a1,a1,a3
  0xeb9ff06f,  #  5280: j     4952
  0x18d5e663,  #  5284: bltu  a1,a3,5680
  0x000107b7,  #  5288: lui   a5,0x10
  0x04f6f463,  #  5292: bgeu  a3,a5,5364
  0x1006b713,  #  5296: sltiu a4,a3,256
  0x00173713,  #  5300: seqz  a4,a4
  0x00371713,  #  5304: slli  a4,a4,0x3
  0x00e6d5b3,  #  5308: srl   a1,a3,a4
  0x00000797,  #  5312: auipc a5,0x0
  0x19c78793,  #  5316: addi  a5,a5,412
  0x00b787b3,  #  5320: add   a5,a5,a1
  0x0007c783,  #  5324: lbu   a5,0(a5)
  0x00e787b3,  #  5328: add   a5,a5,a4
  0x02000713,  #  5332: li    a4,32
  0x40f705b3,  #  5336: sub   a1,a4,a5
  0x02f71663,  #  5340: bne   a4,a5,5384
  0x00100513,  #  5344: li    a0,1
  0xe066eee3,  #  5348: bltu  a3,t1,4864
  0x00c8b533,  #  5352: sltu  a0,a7,a2
  0x00153513,  #  5356: seqz  a0,a0
  0x00008067,  #  5360: ret
  0x010007b7,  #  5364: lui   a5,0x1000
  0x01800713,  #  5368: li    a4,24
  0xfcf6f0e3,  #  5372: bgeu  a3,a5,5308
  0x01000713,  #  5376: li    a4,16
  0xfb9ff06f,  #  5380: j     5308
  0x00f65733,  #  5384: srl   a4,a2,a5
  0x00b696b3,  #  5388: sll   a3,a3,a1
  0x00d766b3,  #  5392: or    a3,a4,a3
  0x00f35733,  #  5396: srl   a4,t1,a5
  0x00b31333,  #  5400: sll   t1,t1,a1
  0x00f8d7b3,  #  5404: srl   a5,a7,a5
  0x0067e7b3,  #  5408: or    a5,a5,t1
  0x0106d313,  #  5412: srli  t1,a3,0x10
  0x02675eb3,  #  5416: divu  t4,a4,t1
  0x01069813,  #  5420: slli  a6,a3,0x10
  0x01085813,  #  5424: srli  a6,a6,0x10
  0x00b61633,  #  5428: sll   a2,a2,a1
  0x02677733,  #  5432: remu  a4,a4,t1
  0x03d80e33,  #  5436: mul   t3,a6,t4
  0x01071513,  #  5440: slli  a0,a4,0x10
  0x0107d713,  #  5444: srli  a4,a5,0x10
  0x00a76733,  #  5448: or    a4,a4,a0
  0x000e8513,  #  5452: mv    a0,t4
  0x01c77e63,  #  5456: bgeu  a4,t3,5484
  0x00e68733,  #  5460: add   a4,a3,a4
  0xfffe8513,  #  5464: addi  a0,t4,-1
  0x00d76863,  #  5468: bltu  a4,a3,5484
  0x01c77663,  #  5472: bgeu  a4,t3,5484
  0xffee8513,  #  5476: addi  a0,t4,-2
  0x00d70733,  #  5480: add   a4,a4,a3
  0x41c70733,  #  5484: sub   a4,a4,t3
  0x02675e33,  #  5488: divu  t3,a4,t1
  0x01079793,  #  5492: slli  a5,a5,0x10
  0x0107d793,  #  5496: srli  a5,a5,0x10
  0x02677733,  #  5500: remu  a4,a4,t1
  0x03c80833,  #  5504: mul   a6,a6,t3
  0x01071713,  #  5508: slli  a4,a4,0x10
  0x00e7e7b3,  #  5512: or    a5,a5,a4
  0x000e0713,  #  5516: mv    a4,t3
  0x0107fe63,  #  5520: bgeu  a5,a6,5548
  0x00f687b3,  #  5524: add   a5,a3,a5
  0xfffe0713,  #  5528: addi  a4,t3,-1
  0x00d7e863,  #  5532: bltu  a5,a3,5548
  0x0107f663,  #  5536: bgeu  a5,a6,5548
  0xffee0713,  #  5540: addi  a4,t3,-2
  0x00d787b3,  #  5544: add   a5,a5,a3
  0x01051513,  #  5548: slli  a0,a0,0x10
  0x00010e37,  #  5552: lui   t3,0x10
  0x00e56533,  #  5556: or    a0,a0,a4
  0xfffe0693,  #  5560: addi  a3,t3,-1
  0x00d57733,  #  5564: and   a4,a0,a3
  0x410787b3,  #  5568: sub   a5,a5,a6
  0x00d676b3,  #  5572: and   a3,a2,a3
  0x01055813,  #  5576: srli  a6,a0,0x10
  0x01065613,  #  5580: srli  a2,a2,0x10
  0x02d70333,  #  5584: mul   t1,a4,a3
  0x02d806b3,  #  5588: mul   a3,a6,a3
  0x02c70733,  #  5592: mul   a4,a4,a2
  0x02c80833,  #  5596: mul   a6,a6,a2
  0x00d70633,  #  5600: add   a2,a4,a3
  0x01035713,  #  5604: srli  a4,t1,0x10
  0x00c70733,  #  5608: add   a4,a4,a2
  0x00d77463,  #  5612: bgeu  a4,a3,5620
  0x01c80833,  #  5616: add   a6,a6,t3
  0x01075693,  #  5620: srli  a3,a4,0x10
  0x010686b3,  #  5624: add   a3,a3,a6
  0x02d7e663,  #  5628: bltu  a5,a3,5672
  0xced79ee3,  #  5632: bne   a5,a3,4860
  0x000107b7,  #  5636: lui   a5,0x10
  0xfff78793,  #  5640: addi  a5,a5,-1
  0x00f77733,  #  5644: and   a4,a4,a5
  0x01071713,  #  5648: slli  a4,a4,0x10
  0x00f37333,  #  5652: and   t1,t1,a5
  0x00b898b3,  #  5656: sll   a7,a7,a1
  0x00670733,  #  5660: add   a4,a4,t1
  0x00000593,  #  5664: li    a1,0
  0xcce8fee3,  #  5668: bgeu  a7,a4,4864
  0xfff50513,  #  5672: addi  a0,a0,-1
  0xcd1ff06f,  #  5676: j     4860
  0x00000593,  #  5680: li    a1,0
  0x00000513,  #  5684: li    a0,0
  0x00008067,  #  5688: ret
  # ---- data ----
  0x00000004,  #  5692: ".\0\0\0"
  0x00000002,  #  5696: ".\0\0\0"
  0x00000004,  #  5700: ".\0\0\0"
  0x00000002,  #  5704: ".\0\0\0"
  0x00000004,  #  5708: ".\0\0\0"
  0x00000006,  #  5712: ".\0\0\0"
  0x00000002,  #  5716: ".\0\0\0"
  0x00000006,  #  5720: ".\0\0\0"
  0x02020100,  #  5724: "\0..."
  0x03030303,  #  5728: "...."
  0x04040404,  #  5732: "...."
  0x04040404,  #  5736: "...."
  0x05050505,  #  5740: "...."
  0x05050505,  #  5744: "...."
  0x05050505,  #  5748: "...."
  0x05050505,  #  5752: "...."
  0x06060606,  #  5756: "...."
  0x06060606,  #  5760: "...."
  0x06060606,  #  5764: "...."
  0x06060606,  #  5768: "...."
  0x06060606,  #  5772: "...."
  0x06060606,  #  5776: "...."
  0x06060606,  #  5780: "...."
  0x06060606,  #  5784: "...."
  0x07070707,  #  5788: "...."
  0x07070707,  #  5792: "...."
  0x07070707,  #  5796: "...."
  0x07070707,  #  5800: "...."
  0x07070707,  #  5804: "...."
  0x07070707,  #  5808: "...."
  0x07070707,  #  5812: "...."
  0x07070707,  #  5816: "...."
  0x07070707,  #  5820: "...."
  0x07070707,  #  5824: "...."
  0x07070707,  #  5828: "...."
  0x07070707,  #  5832: "...."
  0x07070707,  #  5836: "...."
  0x07070707,  #  5840: "...."
  0x07070707,  #  5844: "...."
  0x07070707,  #  5848: "...."
  0x08080808,  #  5852: "...."
  0x08080808,  #  5856: "...."
  0x08080808,  #  5860: "...."
  0x08080808,  #  5864: "...."
  0x08080808,  #  5868: "...."
  0x08080808,  #  5872: "...."
  0x08080808,  #  5876: "...."
  0x08080808,  #  5880: "...."
  0x08080808,  #  5884: "...."
  0x08080808,  #  5888: "...."
  0x08080808,  #  5892: "...."
  0x08080808,  #  5896: "...."
  0x08080808,  #  5900: "...."
  0x08080808,  #  5904: "...."
  0x08080808,  #  5908: "...."
  0x08080808,  #  5912: "...."
  0x08080808,  #  5916: "...."
  0x08080808,  #  5920: "...."
  0x08080808,  #  5924: "...."
  0x08080808,  #  5928: "...."
  0x08080808,  #  5932: "...."
  0x08080808,  #  5936: "...."
  0x08080808,  #  5940: "...."
  0x08080808,  #  5944: "...."
  0x08080808,  #  5948: "...."
  0x08080808,  #  5952: "...."
  0x08080808,  #  5956: "...."
  0x08080808,  #  5960: "...."
  0x08080808,  #  5964: "...."
  0x08080808,  #  5968: "...."
  0x08080808,  #  5972: "...."
  0x08080808,  #  5976: "...."
  0x00000010,  #  5980: ".\0\0\0"
  0x00000000,  #  5984: "\0\0\0\0"
  0x00527a03,  #  5988: ".zR\0"
  0x01017c01,  #  5992: ".|.."
  0x00020d1b,  #  5996: "...\0"
  0x00000010,  #  6000: ".\0\0\0"
  0x00000018,  #  6004: ".\0\0\0"
  0xfffff61c,  #  6008: "...."
  0x00000478,  #  6012: "x.\0\0"
  0x00000000,  #  6016: "\0\0\0\0"
  0x00000010,  #  6020: ".\0\0\0"
  0x0000002c,  #  6024: ",\0\0\0"
  0xfffffa80,  #  6028: "...."
  0x00000430,  #  6032: "0.\0\0"
  0x00000000,  #  6036: "\0\0\0\0"
  # heap:
  0x000017a0]  #  6040: "..\0\0"

# zero-initialized data (.bss), not part of the image:
#    6048: _end

m = machine(mem_size=0x400000)
m.write_i32_vec(prog, 0)
m.run(start=0)
