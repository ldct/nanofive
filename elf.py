"""Load RISC-V ELF executables into nanofive's memory, for the projects whose
programs are compiled C (newlib, ratpoints, urlh)."""

import struct

from machine import machine, machine64

def elf_machine(path, mem_size):
  """a fresh machine (RV32) or machine64 (RV64), matching the ELF's class"""
  ei_class = open(path, 'rb').read(5)[4]
  return {1: machine, 2: machine64}[ei_class](mem_size=mem_size)

def load_elf(m, path):
  """copy the PT_LOAD segments of a little-endian RISC-V ELF into mem[], return
  the entry point. The ELF class (32/64-bit) must match the machine's XLEN"""
  data = open(path, 'rb').read()
  assert data[:4] == b'\x7fELF' and data[5] == 1, 'not little-endian ELF'
  assert data[4] == {32: 1, 64: 2}[m.XLEN], 'ELF class does not match XLEN'
  e_machine, = struct.unpack_from('<H', data, 18)
  assert e_machine == 243, 'not RISC-V'
  if m.XLEN == 32:
    e_entry, e_phoff = struct.unpack_from('<II', data, 24)
    e_phentsize, e_phnum = struct.unpack_from('<HH', data, 42)
  else:
    e_entry, e_phoff = struct.unpack_from('<QQ', data, 24)
    e_phentsize, e_phnum = struct.unpack_from('<HH', data, 54)
  for i in range(e_phnum):
    off = e_phoff + i * e_phentsize
    if m.XLEN == 32:
      p_type, p_offset, _, p_paddr, p_filesz, p_memsz = \
        struct.unpack_from('<IIIIII', data, off)
    else:
      p_type, _, p_offset, _, p_paddr, p_filesz, p_memsz = \
        struct.unpack_from('<IIQQQQQ', data, off)
    if p_type != 1: continue  # PT_LOAD
    assert p_paddr + p_memsz <= len(m.mem), 'segment does not fit in memory'
    m.mem[p_paddr : p_paddr + p_filesz] = data[p_offset : p_offset + p_filesz]
    m.mem[p_paddr + p_filesz : p_paddr + p_memsz] = bytes(p_memsz - p_filesz)
  return e_entry
