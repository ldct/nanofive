/* flat memory starting at address 0, stack at the top (MEM_SIZE bytes total) */
MEM_SIZE    = DEFINED(MEM_SIZE)   ? MEM_SIZE   : 0x100000;  /* 1 MiB */
STACK_SIZE  = DEFINED(STACK_SIZE) ? STACK_SIZE : 0x10000;   /* 64 KiB */
ENTRY(_start)
SECTIONS
{
  . = 0;
  .text   : { *(.text.init) *(.text .text.*) }
  .rodata : { *(.rodata .rodata.* .srodata .srodata.*) }
  .preinit_array : {
    PROVIDE_HIDDEN(__preinit_array_start = .);
    KEEP(*(.preinit_array))
    PROVIDE_HIDDEN(__preinit_array_end = .);
  }
  .init_array : {
    PROVIDE_HIDDEN(__init_array_start = .);
    KEEP(*(SORT(.init_array.*)))
    KEEP(*(.init_array))
    PROVIDE_HIDDEN(__init_array_end = .);
  }
  .fini_array : {
    PROVIDE_HIDDEN(__fini_array_start = .);
    KEEP(*(SORT(.fini_array.*)))
    KEEP(*(.fini_array))
    PROVIDE_HIDDEN(__fini_array_end = .);
  }
  .data   : { *(.data .data.*) }
  .sdata  : { __global_pointer$ = . + 0x800; *(.sdata .sdata.*) }
  __bss_start = .;
  .sbss   : { *(.sbss .sbss.*) }
  .bss    : { *(.bss .bss.*) *(COMMON) }
  . = ALIGN(16);
  _end = .;
  __stack_top   = MEM_SIZE;
  __stack_limit = MEM_SIZE - STACK_SIZE;
}
