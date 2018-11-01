# PCGE
Project Call Graph Explorer

This is a simple Frama-C plugin devoted to analyse C projects and to produce retro-design information. 
This plugin enable to generate:
  - function call-graph
  - module call-graph (deduced from function call-graph)
  - automatic call dependencies of each module (.c file)
  - computation of the longuest branch in the calltree for stack analysis usage (stack usage of each function shall be entered as input)
  
  ## Installation
  
  Prerequisite:
  - Ocaml (>= 4.02.3)
  - Frama-C ( >= Sulfur)
very easu to adapt to prior versions of OCaml and Frama-C

2 ways to use it:
1. Without installing it with `-load-script` option
```shell
frama-c -load-script <absolute-path>/plug.ml -pcge-help # to check is the plugin is available
````
2. By installing it as a real plugin in your Frama-C
```shell
make
make install
frama-c -pcge-help # to check is the plugin is available
````

