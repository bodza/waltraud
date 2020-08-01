#!/usr/bin/env python3

import argparse, subprocess

def print_usage(bios,regions, triple):
    ram_usage = 0

    readelf = triple + "-readelf"

    result = subprocess.run([readelf, '-e', '-W', bios], stdout=subprocess.PIPE)
    result = result.stdout.decode('utf-8')
    result = result.split('\n')

    with open(regions, "r") as regfile:
        for line in regfile:
           if line == 0:
               break
           if 'sram' in line:
               ram_size = int(line.split(' ')[-1], 16)

    for line in result:
        if '.text' in line:
            if 'PROGBITS' in line:
                tokens = list(filter(None,line.split(' ')))
                ram_usage += int(tokens[6], 16)
        if '.rodata' in line:
            if 'PROGBITS' in line:
                tokens = list(filter(None,line.split(' ')))
                ram_usage += int(tokens[6], 16)
        if '.data' in line:
            if 'PROGBITS' in line:
                tokens = list(filter(None,line.split(' ')))
                ram_usage += int(tokens[6], 16)
        if '.commands' in line:
            if 'PROGBITS' in line:
                tokens = list(filter(None,line.split(' ')))
                ram_usage += int(tokens[6], 16)
        if '.bss' in line:
            if 'NOBITS' in line:
                tokens = list(filter(None,line.split(' ')))
                ram_usage += int(tokens[6], 16)

    print("\nRAM usage: {:.2f}KiB \t({:.2f}%)\n".format(ram_usage / 1024.0, ram_usage / ram_size * 100.0))

def main():
    parser = argparse.ArgumentParser(description="Print bios memory usage")
    parser.add_argument("input", help="input file")
    parser.add_argument("regions", help="regions definitions")
    parser.add_argument("triple", help="toolchain triple")
    args = parser.parse_args()
    print_usage(args.input, args.regions, args.triple)

if __name__ == "__main__":
    main()
