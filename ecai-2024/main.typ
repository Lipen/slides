#import "theme.typ": *
#show: presentation.with(
  author: [Alexander Andreev, *Konstantin Chukharev*, Stepan Kochemazov, Alexander Semenov],
  title: [Using Backdoors to Generate Learnt Information in SAT Solving],
  occasion: [27th European Conference on Artificial Intelligence --- ECAI-2024 --- Santiago de Compostela, Spain],
  date: [24 October 2024],
  logo_height: 20%,
  footer: [#link("https://www.ecai2024.eu/")[ECAI-2024] :: #link("https://doi.org/10.3233/FAIA240989")[Using Backdoors to Generate Learnt Information in SAT Solving]],
  show_toc: true,
)

// Fix 'emptyset' math symbol to be a normal circle:
#show sym.emptyset: set text(font: font)

// Green/red colors for positive and negative literals:
#let color-pos = oklch(60%, 0.300, 145deg)
#let color-neg = oklch(60%, 0.300, 35deg)

// Colors for easy/hard tasks and text over them:
#let col-easy = oklch(60%, 0.3, 155deg, 20%)
#let col-hard = oklch(60%, 0.3, 35deg, 20%)
#let col-easy-text = luma(20%)
#let col-hard-text = luma(20%)

// #slide[
//   #metropolis-outline
// ]

#section[Background: Backdoors]

#slide(title: [Backdoors by Williams (2003)])[
  Consider a SAT problem for a CNF $C$ over the set of variables $X$.

  A *strong backdoor* (_with respect to an algorithm $A$_) is a subset of variables $B subset.eq X$ such that for *each* assignment $alpha$ of these variables, $C[alpha slash B]$ is _easy_, that is, polynomially decidable using $A$. [1]

  Overall, strong backdoor is a complete *unsatisfiability certificate* which can be verified in $O(p(|C|) dot 2^(|B|))$.

  \
  #text(size: 0.7em)[
    [1] R. Williams, C. P. Gomes, and B. Selman, "Backdoors to Typical Case Complexity," in IJCAI, 2003.
  ]
]

#slide(title: [Sub-solver])[
  A *sub-solver* is a (SAT/CSP) solving algorithm that, for a given input~$C$, in _polynomial time_ (i.e. $O(p(|C|))$), either "_determines_" $C$ correctly (UNSAT or SAT with a model) or "_rejects_" the input ("UNKNOWN" result).

  For a *sub-solver*, one can employ the *unit propatation (UP)* rule.

  #import fletcher: diagram, node, edge
  #import fletcher.shapes: *

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

  #set align(center)
  #diagram(
    // debug: true,
    spacing: (32pt, 8pt),
    edge-stroke: 2pt,
    edge-corner-radius: 5pt,
    mark-scale: 70%,

    blob((0, 0), [Input CNF], tint: blue, shape: parallelogram, height: 2.5em, name: <input>),
    edge("-|>"),
    blob((2, 0), [Polynomial \ sub-solver], tint: purple, shape: hexagon, name: <solver>),
    blob((3.3, -1), [SAT], tint: green, shape: pill, height: 2.5em, width: 3em, name: <sat>),
    blob((3.7, 0), [UNSAT], tint: red, shape: pill, height: 2.5em, name: <unsat>),
    blob((3.5, 1), [UNKNOWN], tint: orange, shape: pill, height: 2.5em, name: <unknown>),
    edge(<solver>, "-|>", <sat>),
    edge(<solver>, "-|>", <unsat>),
    edge(<solver>, "-|>", <unknown>),
  )
]

#slide(title: [Strong backdoors: Visualized])[
  #let ex(i, pos) = if pos {
    $text(fill: #color-pos, x_#i)$
  } else {
    $text(fill: #color-neg, overline(x)_#i)$
  }

  #fa-triangle-exclamation()
  Hereinafter, assume that the considered CNF $C$ is *unsatisfiable*.

  For each assignment $alpha in {0,1}^(|B|)$, unit propagation on $C[alpha slash B]$ can return either UNSAT (*conflict* under assignment), or UNKNOWN (*no conflict*).

  For a strong backdoor, *all* assignments lead to a conflict:
  $
    C and (ex(1, #true) and ex(2, #true) and dots and ex(n,#true)) op(tack.r.long)_"UP" bot "(conflict)" \
    C and (ex(1, #false) and ex(2, #true) and dots and ex(n,#true)) op(tack.r.long)_"UP" bot "(conflict)" \
    // C and (ex(1, #true) and ex(2, #false) and dots and ex(n,#true)) op(tack.r.long)_"UP" bot "(conflict)" \
    dots \
    C and (ex(1, #false) and ex(2, #false) and dots and ex(n,#false)) op(tack.r.long)_"UP" bot "(conflict)"
  $
]

#section[Main matter: $rho$-backdoors]

#slide(title: [Desired properties of "better" backdoors])[
  Our goal is to construct *a thing* with the following properties:

  - It is similar to a strong backdoor.
  - It is a _partial_ unsatisfiability certificate.
  - It is small and easy to find.
  - It can be used to obtain logical entailments of the original formula, which might be beneficial for a SAT solver.

  We are going to show that *"$rho$-backdoors"* have these properties.
]

#slide(title: [$rho$-backdoors: Visualized])[
  #set align(center)
  #cetz.canvas({
    import cetz.draw: *

    scale(125%)

    set-style(
      stroke: (thickness: 0.4pt, cap: "round"),
      content: (padding: 0.3em),
    )

    let ex(i, pos) = if pos {
      $text(fill: #color-pos, x_#i)$
    } else {
      $text(fill: #color-neg, overline(x)_#i)$
    }

    // Backdoor
    let w = 10
    let h = 8
    rect((0, 0), (rel: (w, h)), name: "tasks", stroke: 1pt)

    content("tasks.north", anchor: "south", $B = {x_1, x_2, x_3}$)

    let cube(lits) = $C and (ex(1, lits.at(#0)) and ex(2, lits.at(#1)) and ex(3, lits.at(#2)))$
    let task(pos, lits, ans) = {
      rect(
        pos,
        (rel: (w, 1)),
        fill: if ans {
          col-easy
        } else {
          col-hard
        },
        name: "task",
      )
      content(
        "task.center",
        text(
          fill: if ans {
            col-easy-text
          } else {
            col-hard-text
          },
          $#cube(lits) op(#if ans { $tack.r.long$ } else { $cancel(tack.r.long)$ })_"UP" bot$,
        ),
      )
    }

    task((0, 7), (false, false, false), true)
    task((0, 6), (false, false, true), true)
    task((0, 5), (false, true, false), false)
    task((0, 4), (false, true, true), false)
    task((0, 3), (true, false, false), true)
    task((0, 2), (true, false, true), true)
    task((0, 1), (true, true, false), true)
    task((0, 0), (true, true, true), false)

    // Brace with rho
    cetz.decorations.brace("tasks.north-east", "tasks.south-east", stroke: 1pt, amplitude: 1, name: "tasks-brace")
    content("tasks-brace.spike", anchor: "mid-west", $rho = 1 - 3 slash 8 = 0.625$, name: "rho-text")

    // Arrow with clarification
    let p1 = (rel: (0.5, 0), to: "rho-text.south-west")
    let p2 = (rel: (0.5, -1), to: p1)
    line(p2, p1, mark: (end: "stealth"))
    content(p2, anchor: "north-west", padding: 2pt)[$rho$ is the proportion \ ~~ of "easy" tasks]

    // Legend
    content((w+1, h), anchor: "north-west", "Legend:", name: "legend-text")
    rect((rel: (1.5, 0), to: "legend-text.east"), (rel: (2, 1)), anchor: "north-east", fill: col-easy, name: "legend-easy")
    rect((rel: (1.5, 0), to: "legend-easy.east"), (rel: (2, 1)), anchor: "north-east", fill: col-hard, name: "legend-hard")
    content("legend-easy.center", text(fill: col-easy-text, "easy"))
    content("legend-hard.center", text(fill: col-hard-text, "hard"))
  })
]

#slide(title: [Properties of $rho$-backdoors])[
  #list-one-by-one(mode: "transparent", tight: false)[
    $rho$-backdoor is a *partial* unsatisfiability certificate: _not for all_ assignments $alpha in {0,1}^(|B|)$ the formula $C[alpha slash B]$ has an "easy" proof.
  ][
    Generally, there are *many* small $rho$-backdoors with $rho$ close to 1. \
    80% of SAT Comp instances have $rho$-backdoors with $|B| < 20$ and $rho > 0.8$
  ][
    $rho$ can be calculated very fast using *tree-based* unit propagation. [AAAI'23]
  ][
    Multiple small $rho$-backdoors can be combined into larger $rho$-backdoors with *strictly* greater~$rho$. [AAAI'22, *ECAI-2024*]
  ][
    New *learnt clauses* can be derived from a $rho$-backdoor. [*ECAI-2024*]
  ]
]

#slide(title: [Searching for $rho$-backdoors])[
  #import fletcher: diagram, node, edge
  #import fletcher.shapes: *

  #let blob(
    pos,
    label,
    tint: white,
    ..args,
  ) = node(
    pos, align(center, label),
    fill: tint.lighten(80%),
    stroke: 1pt + tint.darken(20%),
    corner-radius: 5pt,
    ..args,
  )

  #set align(center)
  #diagram(
    // debug: true,
    spacing: 16pt,
    cell-size: (1em, 1em),
    edge-stroke: 2pt,
    edge-corner-radius: 5pt,
    mark-scale: 70%,

    blob((0, -2), [Random\ $B subset.eq X$], tint: red, shape: parallelogram, height: 2.5em),
    edge("-|>"),
    blob((0, 0), [Backdoor $B$], tint: teal, shape: pill, height: 2.5em),
    edge("-|>"),
    blob((2, 0), [Done?], tint: purple, shape: diamond, height: 2em, name: <if>),
    edge("-|>"),
    blob((4, 0), [Mutate $B$], tint: yellow, shape: hexagon, height: 2.5em),
    edge("-|>"),
    blob((6, 0), [Fitness\ $rho$ for $B$], tint: yellow, shape: hexagon, height: 2.5em),
    edge("-|>"),
    blob((8, 0), [Selection\ (1+1)-EA], tint: yellow, shape: hexagon, height: 2.5em),
    edge("dd", (rel: (0, 2), to: (0, 0)), (0, 0), "-|>"),

    blob((4, -2), [Best $B$], tint: green, shape: parallelogram, height: 2.5em, name: <best>),
    edge(<if>, <best>, "-|>", [done!], label-angle: auto, bend: 30deg),
  )
]

#slide(title: [Combining $rho$-backdoors])[
  *Theorem.* It is possible to use two small $rho$-backdoors $B_1$ and $B_2$ (for simplicity, assume $B_1 sect B_2 = emptyset$) to construct a $rho$-backdoor $B' = B_1 union B_2$ of larger size $|B'| = |B_1| + |B_2|$ with $rho_3 > max(rho_1, rho_2)$.

  For this, just perform a *Cartesian product* of the two sets of hard tasks, *concatenating* the cubes and filtering out all trivially conflicting ones.

  *Note*: no need to check all $2^(|B_1| + |B_2|)$ cubes, since most of them ($rho_1$ and $rho_2$) have been proven to be conflicting.
  We get *larger* $rho$-backdoor *for free*!
]

#slide(title: [Combination of $rho$-backdoors: Visualized])[
  #cetz.canvas({
    import cetz.draw: *

    scale(150%)

    set-style(
      stroke: (thickness: 0.4pt, cap: "round"),
      content: (padding: 0.3em),
    )

    let backdoor(name, origin, w, h, answers) = {
      rect(origin, (rel: (w, h * answers.len())), stroke: 1pt, name: name)
      for (i, ans) in answers.rev().enumerate() {
        let y = i * h
        rect(
          (rel: (0, y), to: origin),
          (rel: (w, h)),
          stroke: 0.5pt,
          fill: if ans {
            col-easy
          } else {
            col-hard
          },
        )
      }
    }

    let count(answers) = answers.filter(it => it).len()
    let rho_(answers) = count(answers) / answers.len()

    // First backdoor
    let answers1 = (true, true, true, false)
    backdoor("first", (0, 0), 2, 1, answers1)
    cetz.decorations.brace("first.north-west", "first.north-east", stroke: 1pt, name: "first-brace")
    content("first-brace.content", $|B_1|$)
    content("first.south", anchor: "north", $rho = #count(answers1) slash #answers1.len()$)

    // Second backdoor
    let answers2 = (false, true, false, true)
    backdoor("second", (4, 0), 2, 1, answers2)
    cetz.decorations.brace("second.north-west", "second.north-east", stroke: 1pt, name: "second-brace")
    content("second-brace.content", $|B_2|$)
    content("second.south", anchor: "north", $rho = #count(answers2) slash #answers2.len()$)

    // Merged backdoor
    let answers_merged = for i in answers1 {
      for j in answers2 {
        (i or j,)
      }
    }
    backdoor("merged", (10, 0), 4, 0.35, answers_merged)
    cetz.decorations.brace("merged.north-west", "merged.north-east", stroke: 1pt, name: "merged-brace")
    content("merged-brace.content", $|B_1| + |B_2|$)
    content(
      "merged.south",
      anchor: "north",
      padding: 0.5em,
      $rho = #count(answers_merged) slash #answers_merged.len() > #if rho_(answers1) > rho_(answers2) {
        $#count(answers1) slash #answers1.len()$
      } else {
        $#count(answers2) slash #answers2.len()$
      }$,
    )

    // Times
    content(("first.east", 50%, "second.west"), anchor: "base", text(size: 2em, $times.circle$))
    // Arrow
    content(
      ("second.east", 50%, ("second.east", "-|", "merged.west")),
      anchor: "base",
      text(size: 2em, $arrow.long_"combine"$),
    )

    // Legend
    content((0, 6), anchor: "mid-west", "Legend:", name: "legend-text")
    rect((2.5, 5.5), (rel: (2, 1)), fill: col-easy, name: "legend-easy")
    rect((5.5, 5.5), (rel: (2, 1)), fill: col-hard, name: "legend-hard")
    content("legend-easy.center", text(fill: col-easy-text, "easy"))
    content("legend-hard.center", text(fill: col-hard-text, "hard"))
  })
]

#slide(title: [Deriving clauses from $rho$-backdoors])[
  // This hack (for increasing the canvas area to fit the possibly wide table) might be unnecessary, but is does not hurt.
  #show: pad.with(right: -6%)

  #let cubes = (
    (-1, 2, -3, -4, -5),
    (-1, 2, 3, -4, -5),
    (1, -2, -3, 4, 5),
    (1, -2, 3, 4, -5),
    (1, 2, -3, 4, 5),
  ).sorted()
  #assert(cubes.all(cube => cube.len() == cubes.at(0).len()))
  #let ex(i) = if i < 0 {
    $text(fill: #color-neg, overline(x)_#(-i))$
  } else {
    $text(fill: #color-pos, x_#i)$
  }
  #let m-cubes = cubes.map(cube => cube.map(ex))
  #let matrix = math.mat(..m-cubes, delim: none, gap: 0.2em)

  #let count(x, y) = cubes.map(cube => int(x in cube and y in cube)).sum()
  #let clause(x, y) = $(#ex(x), #ex(y))$
  #let body = for (i, j) in ((1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)) {
    (
      $(x_#i, x_#j)$,
      [#count(i, j)],
      [#count(i, -j)],
      [#count(-i, j)],
      [#count(-i, -j)],
      [
        #(
          (i, j),
          (i, -j),
          (-i, j),
          (-i, -j),
        ).map(((x, y)) =>
          if count(x, y) == 0 {
            clause(-x, -y)
          } else {
            none
          }
        ).filter(it => it != none).join(", ")
      ],
    ).flatten()
  }

  #grid(
    columns: 2,
    gutter: 1em,
    align: top,
    [
      Hard cubes:
      $ #matrix $
      $rho &= 1 - #cubes.len() slash #calc.pow(2, cubes.at(0).len()) \ &= #calc.round(1 - cubes.len() / calc.pow(2, cubes.at(0).len()), digits: 3)$
    ],
    [
      Count table:
      #table(
        stroke: none,
        columns: 6,
        align: (x, _) => if x == 5 {
          left
        } else {
          center
        },
        inset: (x, y) => if y == 0 {
          (
            x: if x >= 1 and x <= 4 {
              5pt
            } else {
              10pt
            },
            bottom: 0.5em,
          )
        } else {
          3pt
        },
        table.vline(x: 1),
        table.header(
          $(x_i, x_j)$,
          $text(fill: #color-pos, x_i) text(fill: #color-pos, x_j)$,
          $text(fill: #color-pos, x_i) text(fill: #color-neg, overline(x)_j)$,
          $text(fill: #color-neg, overline(x)_i) text(fill: #color-pos, x_j)$,
          $text(fill: #color-neg, overline(x)_i) text(fill: #color-neg, overline(x)_j)$,
          [Derived clauses],
        ),
        table.hline(),
        ..body,
      )
    ],
  )
]

#section[#smallcaps[Interleave] procedure]

#slide(title: [Overview of the #smallcaps[Interleave] procedure])[
  - *Alternate* between the two phases:
    + *$bold(rho)$-backdoor phase*: identify and combine $rho$-backdoors, derive clauses.
    + *CDCL solving phase*: just run CaDiCaL for some time.

  - Each phase is granted an initial conflict *budget*, which increases incrementally (e.g., by a factor of $1.1$) after each round.
]

#let s = counter("steps")

#slide(title: [Step-by-Step process (#context { (s.final().at(0)-1) } steps)])[
  #set enum(numbering: it => (
    context {
      s.step()
      s.display("1.")
    }
  ))

  + *Initialize* the CDCL SAT solver on the given CNF.

  + *Pre-solve* the CNF using a limited conflict budget (e.g., #num[10000] conflicts).

  + #underline[*Iterative process*]: alternate $rho$-backdoor phase and plain CDCL solving.
]

#slide(title: [Iterative process: $rho$-backdoor identification])[
  #set enum(numbering: it => (
    context {
      s.step()
      s.display("1.")
    }
  ))

  + *Identify $bold(rho)$-backdoor* using Evolutionary Algorithm.
    - Determine hard tasks for the $rho$-backdoor using UP.
    - Augment CaDiCaL to propagate multiple cubes in a tree-like manner.

  + *Combine $rho$-backdoors* using Cartesian product.
    - Combine previously found hard tasks with those for the new backdoor.
    - Reset the large set of hard tasks (e.g, once it exceeds #num[10000] cubes).
]

#slide(title: [Iterative process: Limited filtering])[
  #set enum(numbering: it => (
    context {
      s.step()
      s.display("1.")
    }
  ))

  + *Filter* the set of hard tasks using _limited_ solver (yet polynomial).
    - Use conflict budget of, e.g., #num[1000] conflicts per cube, and #num[100000] total.
    - Use heuristic to select the most promising cubes.

  + *Derive clauses* from the set of hard tasks.
]

#slide(title: [Iterative process: Exit condition])[
  #set enum(numbering: it => (
    context {
      s.step()
      s.display("1.")
    }
  ))

  + *Exit* the iterative process if:
    - The satisfying assignment is found --- problem is SAT.
    - The set of hard tasks is empty, i.e., the strong backdoor is found --- problem is UNSAT with a polynomial certificate.
    - *Else*, switch to other mode (plain CDCL) and continue.
]

#section[Experimental evaluation]

#slide(title: [Results: Cactus plot on 116 instances from SAT Competition])[
  #set align(center)
  #image("img/plot_cactus_on116.svg", width: 110%)
]

#slide(title: [Results: Scatter plot for the best configuration and VBS])[
  #set align(center)
  #image("img/plot_scatters_on116.svg", width: 100%)
]

#section[Conclusion]

#slide(title: [Conclusion and Future plans])[
  - In this work, we further explored the concept of $rho$-backdoors:
    - Partial unsatisfiability certificates.
    - Easy to search for using evolutionary algorithms.
    - Can be used to derive new clauses that are beneficial for a SAT solver.

  - #block(width: 100%)[
      Open-source implementation is available on GitHub: \
      https://github.com/Lipen/backdoor-solver

      #place(
        top + right,
        link(
          "https://github.com/Lipen/backdoor-solver",
          cades.qr-code("https://github.com/Lipen/backdoor-solver", width: 6cm),
        ),
      )
    ]

  - Future plans:
    - Parallel implementation.
    - Proofs!
]

#focus-slide[
  #v(1fr)
  Thank you for your attention!
  \
  #fa-mail-bulk() `kchukharev@itmo.ru`
  \
  #fa-github() #link("https://github.com/Lipen")[Lipen]
  #v(1fr)

  #set text(size: 0.666em)
  #set align(left)
  Some questions you _might_ want to ask:
  #list(marker: [#fa-star()])[
    How long the EA runs comparing to solving?
    #h(1fr)
    #text(size: 0.75em)[[_Very little._]]
  ][
    Have you tried BDDs for storing hard tasks?
    #h(1fr)
    #text(size: 0.75em)[[_Yes! It exploded. #fa-explosion()_]]
  ][
    Have you tried using a sub-solver other than UP?
    #h(1fr)
    #text(size: 0.75em)[[_Yes, we tried._]]
  ]
]
