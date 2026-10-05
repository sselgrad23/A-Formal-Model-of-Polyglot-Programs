# A Formal Model of Polyglot Programs

A formalisation of C/Python polyglot programs in the Isabelle/HOL proof assistant, with machine-checked proofs that the construction produces valid programs. BSc dissertation, University of Exeter, 2021. The full report is [`ECM3428_Report.pdf`](ECM3428_Report.pdf).

## Background

A polyglot program is a single file that is a valid program in more than one language. Polyglots matter for security because they can act as payloads for multi-stage attacks: a file that one layer of a system accepts as harmless input of one type can be interpreted as executable code of another type deeper inside the system. Magazinius et al. (2013), "Polyglots: Crossing Origins by Crossing Formats", showed such attacks against PDF readers and cloud storage services, and motivated this project.

Tools such as Truepolyglot generate polyglot files, but at the time of writing no formal model of polyglot payloads existed. This project provides one for C/Python polyglots.

## The construction

Both languages must ignore each other's code. The construction uses two features:

- The C preprocessor skips everything between `#if 0` and `#endif`. Python treats these lines as comments, because they start with `#`.
- Python treats text between `"""` delimiters as a string literal, which hides the C code from Python.

The resulting polyglot, as it appears in `polyglot.thy`:

```
#if 0
if __name__ == '__main__':
    print("Hello Python")
#endif
#if 0
""" "
#endif
#include <stdio.h>
int main() {
  printf("Hello in C\n");
  return 0;
}
#if 0
" """
#endif
```

Run with Python 3, it prints the Python message. Compiled with GCC, the executable prints the C message. Both run without errors or warnings.

## The model

**`program.thy`** defines an abstract representation of programs that keeps only the features needed to build polyglots:

- `program`: a datatype with five constructors: `SKIP`, a code `block`, a `linecomment`, a `blockcomment` that wraps another program, and `semi` for sequencing two programs.
- `pl`: a record describing a programming language by its identifier, block-comment and line-comment notation, and string-literal notation. Definitions are given for C, Python, HTML, Pascal, Z3 and SQL. Only C and Python are used in the polyglot construction.
- `validP` (written `PL ⊨ P`): whether program `P` is valid in language `PL` under this model.
- `comments2skip`, `rmskip` and `rmcomments`: functions that remove comments from a program, with lemmas showing that they are idempotent and preserve validity.

**`polyglot.thy`** defines polyglots on top of this model:

- `valid_poly`: a polyglot is valid if each version is valid in its language and all versions have the same string representation.
- `compose_c_poly` and `compose_python_poly`: build the C view and the Python view of the polyglot from a C program and a Python program.
- `mk_c_python_poly`: builds the polyglot only if the C input is valid C and the Python input is valid Python, and returns the empty set otherwise.

## What is proved

- **`valid_poly_compose_c_poly`:** for any valid C program and any valid Python program, the composed program is valid C. This holds under the additional condition `python_valid_ifdef_c`, which requires that the Python program contains no `#` character once comments are removed. The proof is by induction over the structure of the C program, with a nested induction over the Python program in each case.
- **`valid_poly_c_python_poly`:** the hello-world polyglot above is valid in both C and Python.
- **Comment-removal lemmas**, including `rmcomments_p1_p2_general`: removing comments from two sequenced programs is equivalent to removing comments from each program, joining them, and removing comments from the result.
- Supporting lemmas on validity of sequenced programs and on sublists of strings.

## Method

The project used test-driven development adapted to theorem proving. The requirements were first written as proof statements. The definitions were then developed and checked with Isabelle `value` commands until they produced the expected output. Finally the proof statements were turned into lemmas and proved. As a final check, a generated polyglot was exported as text, compiled with GCC and run with a Python 3 interpreter.

## Limitations

- The model covers only the syntax that matters for building polyglots: comments and string literals. It does not model full program semantics, such as whether variables are declared or whether a program terminates.
- The general theorem covers the C side of the polyglot. Validity in both languages is proved for the concrete example.
- Only C/Python polyglots are formalised. Extending the model to other formats, such as PDF/ZIP polyglots, is future work.

## Files

| File | Contents |
|---|---|
| `program.thy` | Abstract program representation, language records, validity, comment removal |
| `polyglot.thy` | Polyglot definition, C/Python composition, proofs |
| `ECM3428_Report.pdf` | Dissertation report |

## Requirements

[Isabelle/HOL](https://isabelle.in.tum.de/). The theories import `String_Cartouche` and `HOL-Library.Sublist`. Open `polyglot.thy` in Isabelle/jEdit to check the proofs.
