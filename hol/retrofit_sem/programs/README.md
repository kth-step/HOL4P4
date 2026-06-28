Extracting and compiling a software switch:

1. Run `setup_cake.sh` in the `compilation` directory.
2. Run `build_cake.sh` with the name of the P4 program you want to use as an argument (for example `./build_cake.sh port_swap`).

The resulting `.cake` file in `compilation` is the resulting binary. Run it with `-i` flags to map port numbers to interfaces. For example, `port_swap.cake -i 1@s1-eth1 -i 2@s1-eth2` runs the port_swap program with the interface `s1-eth1` interpreted as port 1, and `s1-eth2` as port 2. This means that packets sent to these interfaces will appear on those ports from the perspective of the P4 program, and vice versa.
