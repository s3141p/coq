https://softwarefoundations.cis.upenn.edu/

1. First create a file named _CoqProject 
```
echo '-Q . LF' > _CoqProject
```

2. Init Makefile
```
coq_makefile -f _CoqProject *.v -o Makefile
```

3. Compile

`make` to compile all

`make basics.vo` to compile basics.v

`coqc -Q . LF basics.v`
