uniclo
======

A Clojure-like language intended to be compilable into a host of target languages and environments.

It deliberately has a host phase and a target phase, where the former executes inside a JVM, and include features like macros,
In that sense, it is similar to ClojureScript.

Uniclo can target multiple languages and execution environments, even in the same code fragment.

There are two specific features that enable this:

* Compiler directives mentioning what target platforms are supported/intended; one can have **many** concurrent targets.
* Native interfaces; or "FFI"s.

This is similar to Haxe, but instead of relying on an awkward ECMA-like syntax and vague semantics, Uniclo has a very
stringent semantics and clearly delineates the platform-independent parts from the platform-dependent parts.

The target platform is defined by a set of features, whereof some are mutually exclusive.

All the compiler directives start with either `(comment *feature*` or `($`.

## Example Code

`
($? [:c++ :c] ;; if we are targeting C/C++
  ($! ;; this means that we simply output the string literal as is
    "std::cout << \"This is C/C++\" << std::endl;"
($? :java
  ($! "System.println(\"This is Java\")"))
