# PCGE
Project Call Graph Explorer

This is a simple [Frama-C](https://frama-c.com) plugin devoted to analyse C projects and to produce retro-design information. 
This plugin is able to generate:
  - function call-graph
  - module call-graph (deduced from function call-graph)
  - automatic call dependencies of each module (.c file)
  - computation of the longuest branch in the calltree for stack analysis usage (stack usage of each function shall be entered as input)

Graphs are generated in dot format. Use [graphviz](https://www.graphviz.org/) to generate .png, .svg of other formats.
This plugin is easy to modify for other usages.
  
  ## Installation
  
  Prerequisite:
  - Ocaml (>= 4.02.3)
  - Frama-C ( >= Sulfur)
very easy to adapt to prior versions of OCaml and Frama-C

2 ways to use it:
1. Without installing it with `-load-script` option
```shell
frama-c -load-script <absolute-path>/plug.ml -pcg-help # to check is the plugin is available
````
2. By installing it as a real plugin in your Frama-C
```shell
make
make install
frama-c -pcg-help # to check is the plugin is available
```

## Examples

```shell
frama-c -no-annot <source files> -load-script ~/Tools/FRAMAC/PLUGINS/PCGE_Argon/plug.ml -pcg-m m.dot -pcg-f f.dot
dot -Tsvg m.dot -o m.svg
dot -Tsvg f.dot -o f.svg
firefox m.svg f.sv
```

* function call graph
![f](https://user-images.githubusercontent.com/18215280/47879869-03defd80-de22-11e8-8361-712655271e4d.png)

* module call graph
![m](https://user-images.githubusercontent.com/18215280/47879871-04779400-de22-11e8-81ef-b2da023b9049.png)

