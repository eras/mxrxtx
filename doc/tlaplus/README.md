# Protocol specification

Refer to [v1/README.md](v1/README.md).

# Running check.sh

You will need [TLA plus toolbox](https://github.com/tlaplus/tlaplus) and a shell-script for invoking
`tlc` to run the script (contents similar to: `java -cp tla2tools.jar tlc2.TLC`). You may also [The
VSCode extension](https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus) to run
the checks, however I don't know how to run the script with that setup (that does include TLC).

Invoke it in the v1 directory like: `../check.sh`

Note: before running the [`check.sh`](../check.sh), you may want to comment out `-dump
dot,colorize,actionlabels model` if you have two Monitors (e.g. `CanMonitor={1, 2}` in
[`MC.cfg`](v1/MC.cfg)) . Otherwise the resulting dot files will be unwieldly large and—in particular
the liveness dot file—can become quite large (e.g. 35 gigabytes) and slow down the process.

With two monitors and the default properties the model checking takes 25 minutes on my system (AMD
Ryzen 9 3900X 12-Core Processor, 64GB). Without the `PROPERTY` definitions in the .cfg it takes just
25 seconds.

# Runing tlsd.sh

Invoke it in the v1 directory like `../tlsd.sh`. You will need to install
[`tlsd`](https://github.com/eras/tlsd) first.
