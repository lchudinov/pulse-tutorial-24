# run in `steel` directory
fstar.exe --include lib/steel --include lib/steel/pulse --include share/steel/examples/pulse/lib --include /workspaces/pulse-tutorial-24/my-steps --include ./share/steel/examples/pulse/_output --include src/ocaml/_build/install/default/lib/steel --include /workspaces/pulse-tutorial-24/my_steps --load_cmxs steel --odir /workspaces/pulse-tutorial-24/my_steps Pulse.Ch16.fst --extract 'Pulse.Ch16' --codegen Extension
./home/vscode/FStar/ocaml/_build/default/fstar/main.exe /workspaces/pulse-tutorial-24/my_steps/Pulse.Ch16.ast -o /workspaces/pulse-tutorial-24/my_steps/voting.rs


fstar.exe --include lib/steel --include lib/steel/pulse --include share/steel/examples/pulse/lib --include /workspaces/pulse-tutorial-24/my-steps --include ./share/steel/examples/pulse/_output --include src/ocaml/_build/install/default/lib/steel --include /workspaces/pulse-tutorial-24/my_steps --load_cmxs steel --odir /workspaces/pulse-tutorial-24/my_steps Pulse.Ch16.fst --extract 'FStar.Pervasives.Native Pulse.Ch16' --codegen krml
