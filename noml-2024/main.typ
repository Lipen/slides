#import "@preview/touying:0.5.3": *
#import themes.metropolis: *

#import "@preview/codly:1.0.0"
#show: codly.codly-init.with()
#codly.codly-disable()

#show: metropolis-theme.with(
  aspect-ratio: "16-9",
  footer: self => [#self.info.title: #self.info.subtitle],
  config-info(
    title: [From SAT to SMT],
    subtitle: [The Next Frontier in Problem Solving and Formal Verification],
    author: link("https://github.com/Lipen")[Konstantin Chukharev],
    date: [November 2024],
    institution: [ITMO University],
    logo: image("img/logo-itmo.png", height: 1em),
  ),
)

#let my-email = "kchukharev@itmo.ru"
#let url-email = "mailto:" + my-email
#let my-github = "Lipen"
#let url-github = "https://github.com/" + my-github
#let my-linkedin = "kchukharev"
#let url-linkedin = "https://www.linkedin.com/in/" + my-linkedin
#let my-telegram = "Lipenx"
#let url-telegram = "https://t.me/" + my-telegram

#import "@preview/cetz:0.3.1"
#import "@preview/fletcher:0.5.2" as fletcher: node, edge
#import "@preview/numbly:0.1.0": numbly
#import "@preview/fontawesome:0.5.0": *
#import "@preview/showybox:2.0.3": showybox
#import "@preview/chronos:0.1.0"
#import "@preview/cades:0.3.0"
#import "@preview/curryst:0.3.0"
#import "@preview/lovelace:0.3.0": *

// Setup the formatting
#set text(font: "Libertinus Sans", size: 20pt)
#set par(justify: true)
#set heading(numbering: numbly("{1}.", default: "1.1"))

// Style the quote block
#set quote(block: true)
#show quote: set par(justify: false)
#show quote: set align(left)

// Fix emptyset symbol
#show sym.emptyset: set text(font: "Libertinus Sans")

// Do not justify text in tables
#show table.cell: set par(justify: false)

// cetz and fletcher bindings for touying
#let cetz-canvas = touying-reducer.with(reduce: cetz.canvas, cover: cetz.draw.hide.with(bounds: true))
#let fletcher-diagram = touying-reducer.with(reduce: fletcher.diagram, cover: fletcher.hide)

// blob for fletcher diagrams
#let blob(
  pos,
  label,
  tint: white,
  ..args,
) = node(
  pos,
  align(center, label),
  fill: tint.lighten(80%),
  stroke: 1pt + tint.darken(20%),
  corner-radius: 5pt,
  ..args,
)

// Aliases
#let imply = sym.arrow.r
#let iff = sym.arrow.l.r
#let maps = sym.arrow.bar

// ===============================================

#title-slide()

= About the Speaker <touying:hidden>

#grid(
  columns: (auto, auto),
  gutter: 1em,
  block(
    width: 10em,
    height: 10em,
    radius: 50%,
    stroke: 2pt + black,
    clip: true,
    image(
      fit: "contain",
      height: 100%,
      "img/me.png",
    ),
  ),
  [
    #set par(justify: false)

    #grid(
      row-gutter: 1em,
      text(size: 1.5em)[
        *Konstantin Chukharev*
      ],
      [
        #link(url-github)[#fa-github() #my-github]
        #h(0.5em)
        #link(url-telegram)[#fa-telegram() #my-telegram]
        #h(0.5em)
        #link(url-linkedin)[#fa-linkedin() #my-linkedin]
        #h(0.5em)
        #link(url-email)[#fa-mail-bulk() #raw(my-email)]
      ]
    )

    PhD student, researcher and lecturer at ITMO University. \
    Senior academic consultant at Huawei R&D Toolchain Lab.

    Received Bachelor's degree in Robotics and Master's degree in Computer Science from ITMO University. Finished one-year program in Bioinformatics Insitute, Saint Petersburg.

    *Research interests:* SAT, formal methods, software verification, automata synthesis, model checking, #box(baseline: 3pt, fa-rust())ust.
  ],
)


= About the Talk <touying:hidden>

#[
  #grid(
    row-gutter: 1em,
    text(size: 1.5em)[*From SAT to SMT*],
    [_The Next Frontier in Problem Solving and Formal Verification._]
  )

  *Abstract:* This talk introduces the transition from the classical Boolean Satisfiability Problem (SAT) to the more expressive Satisfiability Modulo Theories (SMT). We explore the motivations behind SMT, and the key theories that extend the capabilities of SAT solvers. The talk also covers the architecture of SMT solvers and their applications in software analysis, in particular, for symbolic execution.
]

#focus-slide[
  #quote(attribution: [William Paul Thurston])[
    _Mathematics is not about numbers, equations, computations, or algorithms: it is about *understanding*._
  ]
]


= Introduction to SAT

== Boolean Satisfiability Problem (SAT)

*SAT* is the classical *NP-complete* problem of determining if a given *Boolean formula* is satisfiable, that is, if there *exists a model* an assignment of truth values to the variables that makes the formula true, or *proving* that no such assignment exists.

$
  exists X . F(X) = 1
$

*Example:*

$(#`TIE` imply #`SHIRT`) and (#`TIE` or #`SHIRT`) and not (#`TIE` and #`SHIRT`) #text(fill: red.darken(20%))[$and #`TIE`$]$

*Limitations of SAT:*

- Restricted to propositional variables.
- Most SAT solvers are limited to CNF formulas.
- Cannot handle arithmetic expressions (e.g., $x + y > 5$) natively.
- Lacks support for data structures like arrays or lists.

== SAT Solvers

#[
  #import fletcher.shapes: *

  #set align(center)
  #fletcher.diagram(
    // debug: true,
    spacing: 4em,
    edge-stroke: 1pt,
    edge-corner-radius: 5pt,
    mark-scale: 150%,

    blob((0, 0), [Constraints \ (CNF formula)], shape: rect, tint: teal, height: 3em, name: <input>),
    edge("-|>"),
    blob((1, 0), [SAT solver], shape: hexagon, tint: purple, height: 2em, name: <solver>),
    blob((2, -0.5), [Satisfiable model \ (valuation)], shape: rect, tint: green, height: 3em, name: <sat>),
    blob((2, 0.5), [Unsatisfiability \ certificate (proof)], shape: rect, tint: red, height: 3em, name: <unsat>),

    edge(<solver>, <sat>, "-|>", [SAT], label-angle: auto),
    edge(<solver>, <unsat>, "-|>", [UNSAT], label-angle: auto),
  )
]

#v(1em)
#showybox(
  frame: (
    body-color: purple.lighten(80%).transparentize(50%),
    title-color: purple.lighten(50%),
  ),
  sep: (
    thickness: 0.4pt,
    dash: "loosely-dashed",
  ),
  title-style: (
    boxed-style: (:),
    color: black,
  ),
  [
    To interact with SAT solvers from Java/Kotlin, use #link("https://github.com/Lipen/kotlin-satlib")[`kotlin-satlib`] library.
  ],
  [
    To interact with SAT solvers from Rust, use #link("https://github.com/Lipen/sat-nexus")[`sat-nexus`] library.
  ],
)

== Solving SAT: DPLL and CDCL Algorithms

#grid(
  columns: (auto, 1fr),
  [
    #pseudocode-list(
      title: smallcaps[CDCL Algorithm],
    )[
      + *while* true *do*
        + *while* propagate_gives_conflict() *do*
          + *if* decision_level == 0 *then* return UNSAT
          + *else* analyze_conflict()
        + *end*

        + restart_if_applicable()
        + remove_lemmas_if_applicable()

        + *if* not decide() *then* return SAT
      + *end*
    ]
  ],
  [
    #set align(right + bottom)
    #cetz.canvas({
      import cetz.draw: *
      import cetz.tree

      let data = (
        $x_1$,
        (
          $x_2$,
          0,
          ($x_3$, 0, 0),
        ),
        (
          $x_2$,
          ($x_3$, ($x_4$, 0, 0), ($x_4$, 1, [])),
          [],
        ),
      )
      tree.tree(
        data,
        grow: 2,
        spread: 1.5,
        name: "T",
        draw-node: (node, ..) => {
          if node.content == 0 {
            circle((), radius: 0.6, fill: red.lighten(80%))
            content((), $bot$)
          } else if node.content == 1 {
            circle((), radius: 0.6, fill: green.lighten(80%))
            content((), $top$)
          } else if node.content == [] {
            circle((), stroke: none)
          } else {
            circle((), radius: 0.6, fill: blue.lighten(80%))
            content((), node.content)
          }
        },
        draw-edge: (from, to, parent, child) => {
          if child.content != [] {
            let (a, b) = (from + ".center", to + ".center")
            line((a, .6, b), (b, .7, a), mark: (end: "stealth", scale: 1.5, fill: black))
            assert(parent.children.len() == 2)
            let p = (a, 50%, b)
            let dx = 0.3 // + 0.1 / child.depth
            let dy = 0.4 // + 0.1 / child.depth
            if child.n == 0 {
              content((rel: (-dx, dy), to: p), text(fill: red.darken(20%))[0])
            } else if child.n == 1 {
              content((rel: (dx, dy), to: p), text(fill: green.darken(20%))[1])
            }
          }
        },
      )
    })
  ],
)

= From SAT to SMT

== Satisfiability Modulo Theories (SMT)

SMT = SAT + Theories.

== Theories in SMT

A *theory* is a set of logical formulas modeling a particular domain.

Common components of theories:

- *Logic*: Propositional and first-order logic.
- *Arithmetic*: Numbers, math operations, inequalities.
- *Arrays*: Access (`read`) and update (`write`) operations.
- *Bit-Vectors*: Bitwise operations on fixed-size (e.g. 32-bit) binary representations.
- *Uninterpreted Functions*: Functions without a fixed interpretation.

#[
  #import fletcher: diagram, node, edge
  #import fletcher.shapes: *

  #set align(center)
  #diagram(
    // debug: true,
    spacing: 0.5em,
    node-inset: 0.5em,

    blob((0, 0), [Logic \ $forall x thin exists y . (x imply y)$], tint: yellow, shape: rect),
    blob((2, 0), [Arithmetic \ $2x + 3 gt.eq y$], tint: green, shape: rect),
    blob((4, 0), [Arrays \ $A[i] = x$], tint: blue, shape: rect),
    blob((6, 0), [Bit-Vectors \ $x_32 = y_32 xor z_32$], tint: purple, shape: rect),
    blob((8, 0), [Uninterpreted \ Functions \ $f(x) = y$], tint: orange, shape: rect),
  )
]

== SMT Solvers and SMT-LIB

#[
  #import fletcher: diagram, node, edge
  #import fletcher.shapes: *

  #let smaller = 0.7em

  #set align(center)
  #diagram(
    // debug: true,
    spacing: (2em, 0.5em),
    node-inset: 0.5em,

    node((0, -1), [#link("https://smt-lib.org/")[SMT-LIB]], inset: 0pt, name: <smtlib>),
    blob((0, 0), [Logic \ #text(smaller)[`(set-logic QF_LIA)`]], tint: teal, shape: rect, name: <logic>),
    blob((0, 1), [Configuration \ #text(smaller)[`(set-option :produce-models true)`]], tint: teal, shape: rect, name: <theory>),
    blob((0, 2), [Declarations \ #text(smaller)[`(declare-const x Int)`]], tint: teal, shape: rect, name: <declare>),
    blob((0, 3), [Constraints \ #text(smaller)[`(assert (>= x 0))`]], tint: teal, shape: rect, name: <assert>),
    blob((0, 4), [Queries \ #text(smaller)[`(check-sat)`]], tint: teal, shape: rect, name: <query>),
    blob((0, 2), [], enclose: (<smtlib>, <logic>, <theory>, <declare>, <assert>, <query>), tint: yellow, shape: rect, inset: 1em, name: <enclosed>),
    blob((2, 2), [SMT Solver], tint: purple, shape: hexagon, height: 2em, name: <solver>),
    blob((3, 2-0.5), [SAT], shape: rect, tint: green, height: 2em, name: <sat>),
    blob((3, 2+0.5), [UNSAT], shape: rect, tint: red, height: 2em, name: <unsat>),

    edge(<enclosed>, <solver>, "-|>"),
    edge(<solver>, <sat>, "-|>"),
    edge(<solver>, <unsat>, "-|>"),
  )
]

== SMT Theories: Background Logic (Core)

The basis of almost all "practical" SMT theories is a classical *first-order logic with equality*.

- *Variables*: Boolean ($x,y,z in bb(B)$) or from some domain $bb(D)$ (numbers, objects, ...).
- *Logical connectives*: $and$, $or$, $not$, $imply$, $iff$.
- *Quantifiers*: universal ($forall$) and existential ($exists$).
- *Functions* and *Predicates*: $f : bb(D) arrow bb(D)$ and $P: bb(D) arrow bb(B)$.
- *Equality*: "$=$" is a binary relation symbol with the following axioms:
  - Reflexivity: $forall x . (x = x)$.
  - Substitution for functions: $forall x, y . (x = y) imply (f(...,x,...) = f(...,y,...))$.
  - Substitution for formulas: $forall x, y . (x = y) imply (phi(x) imply phi(y))$.

*Examples:*
$quad forall x thin exists y . (x imply y)
  quad exists x . P(x)
  quad forall x forall y . P(f(x)) imply not (P(x) imply Q(f(y),x,z))$


== SMT Theories: Equality with Uninterpreted Functions (EUF)

- "$=$" is *equality*, $f$ is an *uninterpreted function*.

- If the background logic is *FOL with equality*, then EUF is *empty* theory.

  - *Example* (UNSAT formula):
    $
      a dot (f(b) + f(c)) = d quad and quad b dot (f(a) + f(c)) != d quad and quad (a = b)
    $

  - Abstracted formula (still UNSAT):
    $
      #let myred = red.darken(20%)
      #let mygreen = green.darken(20%)
      h(#text(fill: myred)[$a$], g(#text(fill: mygreen)[$f(b)$], f(c))) = d
      quad and quad
      h(#text(fill: myred)[$b$], g(#text(fill: mygreen)[$f(a)$], f(c))) != d
      quad and quad
      (a = b)
    $

  - Both formulas are *unsatisfiable*, without any arithmetic reasoning.

- EUF is used to abstract "non-supported constructions", e.g. non-linear multiplication.


== SMT Theories: Arithmetics (Ints, Reals, Floating Point)

*Restricted* fragments support more efficient methods.

#table(
  columns: (auto, auto),
  inset: 0.5em,
  stroke: (x, y) => if y == 0 {
    (bottom: 1pt + black)
  },
  align: (x, y) => (
    if y == 0 {
      left + bottom
    } else {
      left + top
    }
  ),
  table.header([*Logic*], [*Example expression*]),
  [*Linear arithmetic* (LIA, LRA)],
  [
    $x + 2y lt.eq 5$
  ],

  [*Non-linear arithmetic* (NIA, NRA)],
  [
    $2 x y + 4 x z^2 - 5y lt.eq 10$
  ],

  [*Difference logic* (DL)],
  [
    $x - y join 3$,~ where $join in {lt, gt, lt.eq, gt, =}$
  ],

  [*UTVPI* (Unit Two-Variable Per Inequality)],
  [
    $a x + b y join d$,~ where $a,b in {-1, 0, 1}$
  ],
)

Commonly, variables are *Reals* or *Integers*. But there are also:

- Floating-point arithmetic (IEEE 754 standard).
- Rational arithmetic.


== SMT Theories: Arrays

Theory of arrays defines two "interpreted" functions: *`read`* and *`write`*.

*Axioms:*
- $forall a forall i forall v . ("read"("write"(a, i, v), i) = v)$
- $forall a forall i forall j forall v . (i != j) imply ("read"("write"(a, i, v), j) = "read"(a, j))$

*Extensionality:*
$forall a forall b med (forall i med ("read"(a, i) = "read"(b, i))) imply (a = b)$

*Example:*
$
  Gamma = {"write"(a, i, x) != b, med "read"(b, i) = y, med "read"("write"(b, i, x), j) = y, med a = b, med i = j}
$

== Arrays Theory: Axiom 1

*First axiom:*
$forall a forall i forall v . ("read"("write"(a, i, v), i) = v)$

#chronos.diagram({
  import chronos: *
  _par("user", display-name: [User])
  _par("A", display-name: [Array $a$])
  _par("B", display-name: [Array $a'$])

  _seq("user", "A", comment: [$"write"(a, i, v)$])
  _note("left", [$a[i] := v$])

  _seq("A", "user", comment: [$a' = "write"(a, i, v)$])
  _note("right", [$a'$ is a modified array])

  _seq("user", "B", comment: [$"read"(a', i)$])
  _note("left", [$a'[i]$])

  _seq("B", "user", comment: [$v$])
  _note("right", [$v$ is the value at index $i$ \ in the modified array $a'$])
})

== Arrays Theory: Axiom 2

*Second axiom:*
$forall a forall i forall j forall v . (i != j) imply ("read"("write"(a, i, v), j) = "read"(a, j))$

#chronos.diagram({
  import chronos: *
  _par("user", display-name: [User])
  _par("A", display-name: [Array $a$])
  _par("B", display-name: [Array $a'$])

  _seq("user", "A", comment: [$"write"(a, i, v)$])
  _note("left", [$a[i] := v$])

  _seq("A", "user", comment: [$a' = "write"(a, i, v)$])

  _seq("user", "B", comment: [$"read"(a', j)$])
  _note("left", [$a'[j]$])
  _seq("B", "user", comment: [$v$])
  _note("right", [$a'[j] = v$])

  _seq("user", "A", comment: [$"read"(a, j)$])
  _note("left", [$a[j]$])
  _seq("A", "user", comment: [$v$])
  _note("right", [$a[j] = v$])

  _note("over", [$a'[j] = a[j] = v$], pos: "user", shape: "hex")
})

== Arrays Theory: Example

#showybox(
  frame: (
    title-color: orange.lighten(80%),
    body-color: orange.lighten(80%).transparentize(50%),
    footer-color: orange.lighten(80%),
    border-color: orange.darken(20%),
    body-inset: (x: 1em, top: -1.5em, bottom: 0.5em),
  ),
  title-style: (
    color: orange.darken(40%),
    boxed-style: (
      anchor: (x: right),
      radius: 10pt,
    ),
  ),
  footer-style: (
    color: orange.darken(40%),
  ),
  title: [
    Try it online! \ https://compsys-tools.ens-lyon.fr/z3 \ https://jfmc.github.io/z3-play/
  ],
  footer: $
    Gamma = {"write"(a, i, x) != b, med "read"(b, i) = y, med "read"("write"(b, i, x), j) = y, med a = b, med i = j}
  $,
)[
  #set text(size: 0.65em)
  ```smtlib
  (set-logic QF_AX) ; Arrays theory

  (declare-sort Index)
  (declare-sort Element)
  (declare-fun a () (Array Index Element))
  (declare-fun b () (Array Index Element))
  (declare-fun i () Index)
  (declare-fun j () Index)
  (declare-fun x () Element)
  (declare-fun y () Element)

  (assert (distinct (store a i x) b))      ; write(a, i, x) != b
  (assert (= (select b i) y))              ; read(b, i) = y
  (assert (= (select (store b i x) j) y))  ; read(write(b, i, x), j) = y
  (assert (= a b))                         ; a = b
  (assert (= i j))                         ; i = j

  (check-sat)  ; Check satisfiability
  (get-model)  ; Get a model if possible
  ```
]


== SMT Theories: Bit-Vectors

*Bit-vector* is a vector of bits of some fixed size.

"Numbers" (integers) are represented in binary form as bit-vectors.

*Operations* on bit-vectors:
- String-like: `concat` and `extract`.
- Logical: `bvnot`, `bvor`, `bvand`, `bvxor`, ...
- Arithmetic: `bvadd`, `bvsub`, `bvmul`, `bvudiv`, `bvurem`, ...
- Comparisons, shifts, rotations, ...

*Example:* (assume all bit-vectors are of size 3)
$
  a[0..1] != b[0..1] quad and quad (a | b) = c quad and quad c[0] = 0 quad and quad a[1] + b[1] = 0
$
// TODO: SMT-LIB code
// ```
// (set-logic QF_BV)
// (declare-fun a () (_ BitVec 3))
// (declare-fun b () (_ BitVec 3))
// (declare-fun c () (_ BitVec 3))
// (assert (distinct ((_ extract 1 0) a) ((_ extract 1 0) b)))
// (assert (= (bvor a b) c))
// (assert (= ((_ extract 0 0) c) #b0))
// (assert (= (bvadd ((_ extract 1 1) a) ((_ extract 1 1) b)) #b0))
// ```


== Modern SMT Solvers

#table(
  columns: 2,
  inset: 0.5em,
  stroke: (x, y) => if y == 0 {
    (bottom: 1pt + black)
  },
  align: (x, y) => (
    if y == 0 {
      left + bottom
    } else {
      left + top
    }
  ),
  table.header([*Solver*], [*Distinctive feature*]),
  [#link("https://github.com/Z3Prover/z3")[Z3]], [Supports many theories],
  [#link("https://github.com/cvc5/cvc5")[CVC5]], [Academic cutting-edge],
  [#link("https://github.com/SRI-CSL/yices2")[Yices]], [Ultra fast],
  [#link("https://github.com/bitwuzla/bitwuzla")[Bitwuzla]], [Top choice for bit-vectors],
  [#link("https://mathsat.fbk.eu/")[MathSAT]], [Combination of theories],
  [#link("https://alt-ergo.ocamlpro.com/")[Alt-Ergo]], [Deductive reasoning],
)

#showybox(
  frame: (
    body-color: purple.lighten(80%).transparentize(50%),
    title-color: purple.lighten(50%),
  ),
  title-style: (
    boxed-style: (:),
    color: black,
  ),
)[
  To interact with SMT solvers from Java/Kotlin, use #link("https://github.com/UnitTestBot/ksmt")[`KSMT`] library.
]


= Advanced Topics in SMT

== Solving SMT

There are *two* main approaches to solving SMT:

- *Eager* approach $#emoji.eagle$

  Encode SMT as SAT and solve using a SAT solver.

- *Lazy* approach $#emoji.sloth$

  Use SAT solver for Boolean part and theory solver for theory-specific parts.


== Eager Approach for Solving SMT

#[
  #import fletcher.shapes: *

  #set align(center)
  #fletcher.diagram(
    // debug: true,
    spacing: (3em, 2em),
    edge-stroke: 1pt,
    edge-corner-radius: 5pt,
    mark-scale: 150%,

    blob((0, 0), [SMT formula], shape: rect, tint: teal, height: 2em, name: <input>),
    edge("-|>"),
    blob((1, 0), [SAT encoding], shape: rect, tint: yellow, height: 2em, name: <encoding>),
    edge("-|>"),
    blob((2, 0), [SAT solver], shape: hexagon, tint: purple, height: 2em, name: <solver>),
    blob((3, -0.5), [SAT], shape: rect, tint: green, height: 2em, name: <sat>),
    blob((3, 0.5), [UNSAT], shape: rect, tint: red, height: 2em, name: <unsat>),
    edge(<solver>, <sat>, "-|>"),
    edge(<solver>, <unsat>, "-|>"),
  )
]

#table(
  columns: 2,
  inset: 0.5em,
  stroke: (x, y) => if y == 0 {
    (bottom: 1pt + black)
  },
  align: (x, y) => (
    if y == 0 {
      left + bottom
    } else {
      left + top
    }
  ),
  table.header([*Pros*], [*Cons*]),
  list(marker: fa-check())[
    Can use the best avaliable SAT solver
  ][
    Simple modular architecture
  ][
    Ideal for finite domains and bounded integers (bit-blasting of bit-vectors)
  ],
  list(marker: fa-times())[
    Complex encodings for some theories
  ][
    Scalability issues for large theories
  ][
    Unbounded integers and quantifiers can~lead to intractable problems
  ],
)


== Eager Approach Example: Encoding of EUF

*Step 1:* Eliminate function and predicate symbols.

Consider a EUF-formula with functions $f(a)$, $f(b)$ and $f(c)$.

- *Ackermann* reduction:
  - Replace each function/predicate with a fresh variable: $A$, $B$, $C$, ...
  - Add clauses: $
    (a = b) imply (A = B), quad
    (a = c) imply (A = C), quad
    (b = c) imply (B = C)$
- *Bryant* reduction:
  - Replace $f(a)$ with $A$
  - Replace $f(b)$ with $"ITE"(b = a, A, B)$
  - Replace $f(c)$ with $"ITE"(c = a, A, "ITE"(c = b, B, C))$
  - Here, $"ITE"$ stands for "If-Then-Else" conditional expression.

#showybox(
  frame: (
    body-color: blue.lighten(80%),
  ),
  [After the first step, atoms in the formula are *equalities* between *constants*.],
)

---

*Step 2:* Encode into propositional logic.

- *Small-domain* encoding:
  - If there are $n$ different constants, there is a model with size at most $n$.
  - Given $n$ constants, we need $log n$ bits to represent each constant.
  - Equalities, such as $(a = b)$, are encoded using the bits of $a$ and $b$.

- *Per-constraint* encoding:
  - Replace each equality $(a = b)$ with a propositional variable $P_(a,b)$.
  - Add transitivity constraints: $P_(a,b) and P_(b,c) imply P_(a,c)$.

#showybox(
  frame: (
    body-color: green.lighten(80%),
  ),
  [Done. Throw it into a *SAT solver* and let it do its *magic*!],
)


== Lazy Approach for Solving SMT

*"Lazy"* means the theory information is used lazily, on demand, when checking the consistency of propositional models found by the SAT solver.


== Theory Solver

#[
  #import fletcher.shapes: *

  #set align(center)
  #fletcher.diagram(
    // debug: true,
    spacing: 3em,
    edge-stroke: 1pt,
    edge-corner-radius: 5pt,
    mark-scale: 150%,

    blob((0, 0), [Set of literals], shape: rect, tint: teal, height: 2em, name: <input>),
    edge("-|>"),
    blob((1, 0), [$cal(T)$-solver], shape: hexagon, tint: purple, height: 2em, name: <solver>),
    blob((2, -0.5), [Consistent \ (SAT)], shape: rect, tint: green, height: 3em, name: <sat>),
    blob((2, 0.5), [Inconsistent \ (UNSAT)], shape: rect, tint: red, height: 3em, name: <unsat>),
    edge(<solver>, <sat>, "-|>"),
    edge(<solver>, <unsat>, "-|>"),
  )
]


== The DPLL(T) Framework

#[
  #import fletcher.shapes: *

  #set align(center)
  #fletcher.diagram(
    // debug: true,
    spacing: 2em,
    edge-stroke: 1pt,
    edge-corner-radius: 5pt,
    mark-scale: 150%,

    blob((0, 0), [$cal(T)$-formula], shape: rect, tint: teal, height: 2em, name: <input>),
    edge("-|>", [convert]),
    blob((0, 2), [Propositional \ formula], shape: rect, tint: yellow, height: 3em, name: <propositional>),
    edge("-|>", [solve], label-angle: auto),
    blob((2, 2), [SAT Solver], shape: hexagon, tint: purple, height: 2em, name: <sat-solver>),
    edge("-|>", [SAT], label-side: left),
    blob((2, 1), [Satisfiable \ model], shape: rect, tint: green, height: 3em, name: <model>),
    edge("-|>", [check], label-side: left),
    blob((2, 0), [$cal(T)$-solver], shape: hexagon, tint: purple, height: 2em, name: <theory-solver>),
    blob((4, 0), [$cal(T)$-consistent \ solution], shape: rect, tint: green, height: 3em, name: <solution>),
    blob((3.5, 1), [$cal(T)$-inconsistent \ model], shape: rect, tint: orange, height: 3em, name: <conflict>),
    blob((4, 2), [Unsatisfiable], shape: rect, tint: red, height: 2em, name: <unsat>),

    edge(<input>, <theory-solver>, "--|>"),
    edge(<theory-solver>, <solution>, "-|>", [OK]),
    edge(<sat-solver>, <unsat>, "-|>", [UNSAT]),
    edge(<theory-solver>, <conflict>, "-|>", [conflict!], label-angle: auto),
    edge(<conflict>, <sat-solver>, "-|>", [forbid (ban)], label-angle: auto),
  )
]


== Combining Multiple Theories

Formulas often involve *multiple* theories, for example:
$
  & (a = b + 2)
  and \
  & (A = "write"(B, a+1, 4))
  and \
  & (
    ("read"(A, b+3) = 2)
    or
    (f(a-1) != f(b+1))
  )
$

Here, we have "$+$" from $cal(T)_"LIA"$, "$"read"$" and "$"write"$" from $cal(T)_"AX"$, and "$f(dot)$" from $cal(T)_"UF"$.


== Nelson--Oppen Method

*Step 1:* Purify literals so that each belongs to a single theory.

#[
  #import fletcher.shapes: *
  #set align(center)

  #fletcher.diagram(
    // debug: true,
    spacing: 3em,
    edge-stroke: 1pt,
    edge-corner-radius: 5pt,
    mark-scale: 150%,

    blob((0, 0), $
      f(f(x) - f(y)) = a
    $, shape: rect, tint: teal),
    edge("-|>"),
    blob((1, 0),$
      f(e_1) &= a, \
      e_1 &= f(x) - f(y)
    $, shape: rect, tint: teal),
    edge("-|>"),
    blob((2, 0), $
      f(e_1) &= a \
      e_1 &= e_2 - e_3 \
      e_2 &= f(x) \
      e_3 &= f(y)
    $, shape: rect, tint: green)
  )

  #fletcher.diagram(
    // debug: true,
    spacing: 3em,
    edge-stroke: 1pt,
    edge-corner-radius: 5pt,
    mark-scale: 150%,

    blob((0, 0), $
      f(0) > a + 2
    $, shape: rect, tint: teal),
    edge("-|>"),
    blob((1, 0),$
      f(e_4) &= a + 2, \
      e_4 &= 0
    $, shape: rect, tint: teal),
    edge("-|>"),
    blob((2, 0), $
      f(e_4) &= e_5 \
      e_4 &= 0 \
      e_5 &> a + 2
    $, shape: rect, tint: green)
  )
]

---

*Step 2:* Exchange entailed *interface equalities* (over shared constants $e_1, e_2, e_3, e_4, e_5, a$).

$L_1 = {f(e_1) = a ,med f(x) = e_2 ,med f(y) = e_3 ,med f(e_4) = e_5 ,med x = y ,med #text(fill: orange)[$e_1 = e_4$]}$

$L_2 = {e_2 - e_3 = e_1 ,med e_4 = 0 ,med e_5 > a + 2 ,med #text(fill: orange)[$e_2 = e_3 ,med a = e_5$]}$

#[
  #import curryst: rule, proof-tree
  #set align(center)
  #proof-tree(
    prem-min-spacing: 1em,
    title-inset: 0.5em,
    rule(
      name: [$cal(T)_"UF"$],
      $a = e_5$,
      $f(e_1) = a$,
      $f(e_4) = e_5$,
      rule(
        name: [$cal(T)_"LRA"$],
        $e_1 = e_4$,
        $e_4 = 0$,
        $e_2 - e_3 = e_1$,
        rule(
          name: [$cal(T)_"UF"$],
          $e_2 = e_3$,
          $f(x) = e_2$,
          $f(y) = e_3$,
          $x = y$,
        ),
      ),
    ),
  )
]

*Step 3:* Check for satisfiability.

#grid(
  columns: (auto, 1fr),
  align: (left, center),
  [
    - #text(fill: green.darken(20%))[$L_1 scripts(tack.double.not)_"UF" bot$]
    - #text(fill: red.darken(20%))[$L_2 scripts(tack.double)_"LRA" bot$]
    - Thus, the whole formula is *unsatisfiable*.
  ],
  [
    #import curryst: rule, proof-tree
    #proof-tree(
      prem-min-spacing: 1em,
      title-inset: 0.5em,
      rule(
        name: [$cal(T)_"LRA"$],
        $bot$,
        $e_5 > a + 2$,
        $a = e_5$,
      ),
    )
  ],
)


= Applications of SMT

== Symbolic Execution with SMT

#[
  #import fletcher: diagram, node, edge
  #import fletcher.shapes: *

  #set align(center)
  #diagram(
    // debug: true,
    spacing: 4em,
    node-inset: 0.5em,
    edge-stroke: 1pt,
    edge-corner-radius: 5pt,
    mark-scale: 150%,

    blob((-10cm, 3cm), [
      ```c
      void func(int x, int y) {
        int z = 2 * y;
        if (z == x) {
          if (x > y + 10) {
            assert(false); // !
          }
        }
      }

      int main() {
        int x = sym_input();
        int y = sym_input();
        func(x, y);
        return 0;
      }
      ```
    ], tint: yellow, shape: rect, fill: yellow.lighten(80%).transparentize(50%), name: <code>),
    edge("-|>", bend: -10deg),
    blob((0, 0), [Symbolic \ execution \ engine], tint: blue, shape: rect, name: <engine>),
    blob((0, -1), [SMT solver], tint: purple, shape: hexagon, height: 2em, name: <solver>),
    blob((1, 0), [High coverage \ test inputs], tint: green, shape: rect, name: <coverage>),
    blob((1, -1), [Unreachable], tint: red, shape: rect, height: 2em, name: <unsat>),

    edge(<engine>, <solver>, "-|>", [Path constraints \ *"reachable?"*], bend: 30deg),
    edge(<solver>, <engine>, "-|>", [Model (variable values) \ *"yes"*], bend: 30deg),
    edge(<engine>, <coverage>, "-|>"),
    edge(<solver>, <unsat>, "-|>", [UNSAT]),
  )
]

== Symbolic Execution: Example

#codly.local(
  highlights: (
    (line: 7, start: 3, tag: [$x maps x_0$]),
    (line: 8, start: 3, tag: [$ & x maps x_0 \ & y maps y_0 $]),
    (line: 9, start: 3, tag: [~PC: $top$]),
    (line: 1, start: 3, tag: [$\ & x maps x_0 \ & y maps y_0 \ & z maps 2 dot y_0$]),
    (line: 2, start: 3, tag: [~PC: $(x_0 = 2 dot y_0) $]),
    (line: 3, start: 5, tag: [~PC: $(x_0 = 2 dot y_0) and (x_0 > y_0 + 10) $]),
    (line: 4, start: 13, tag: [~Reachable with $x_0 = 40, y_0 = 20$]),
  ),
  highlight-fill: color => color.lighten(80%).transparentize(80%),
  default-color: green,
  inset: 0.2em,
  display-name: false,
)[
  #codly.codly-enable()
  ```python
  def func(x: int, y: int):
    z = 2 * y
    if x == z:
      if x > y + 10:
        raise RuntimeError("???")

  def main():
    x = sym_input()
    y = sym_input()
    func(x, y)
  ```
]


= Conclusion

#slide[
  - SMT *extends* the capabilities of SAT by incorporating *rich theories*.

  - SMT solvers are *precise* which makes them a critical tool for verification and analysis.

  - As SMT *evolves*, its role in modern computing is becoming more prominent.
]

#focus-slide[
  Thanks.


  #fa-mail-bulk() #raw(my-email)

  // #link(url-telegram)[#fa-telegram() #my-telegram]

  #link(url-github)[#fa-github() #my-github]

  #place(bottom + right, link(url-github, cades.qr-code(url-github, width: 5em)))
]
