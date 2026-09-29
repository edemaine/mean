# Mean

***Mean*** is a language layer built on top of Lean that aims to make
formal definitions and theorem statements in Lean read like ordinary
mathematical English, while still representing a precise formalization.

The main goal is to help a human check that an LLM-generated formalization says
what the mathematician intended, *without having to understand Lean syntax*.
Lean checks that a proof establishes the claimed theorems. A human still needs
to check that the definitions, hypotheses, and theorems express the intended
mathematics. Mean aims to make that human review easier by presenting those
statements as mathematical English.

Mean supports two complementary workflows:

- **Translate existing Lean into Mean.** Render formal definitions and
  statements into controlled English, with a checked round trip back to Lean.
- **Write mathematics directly in Mean.** Humans or LLMs can use the same
  readable language to define predicates and express propositions that
  elaborate into ordinary Lean and work with Lean proofs and mathlib.

Both workflows are implemented in an ordinary Lean 4 library, using its
[flexible metaprogramming features](https://leanprover-community.github.io/lean4-metaprogramming-book/).

The current implementation is a proof of concept, with a small vocabulary and
partial rendering coverage.

## Review a Lean formalization

1. An LLM or a human writes definitions and theorem statements in Lean.
2. Mean renders the actual elaborated expressions into readable mathematical text.
3. The printed text is parsed and elaborated back into Lean, and its meaning is
   checked against the original.
4. A human reviews the Mean presentation, with the underlying Lean available for
   inspection and unfamiliar definitions available for further review.

For example, ordinary Lean can say:

```lean
def preconnected {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ _p : G.Path u v, True
```

Mean renders it as:

```lean
Definition:
  a simple graph G is preconnected if
    for all vertices u and v of G:
      there is a path in G from u to v.
```

The focus is on **definitions and theorem statements**. Explaining proofs,
accepting unrestricted English, and producing persuasive but unchecked paraphrases
are outside the current scope.

## Write directly in Mean

After `import Mean`, the readable definition above is executable Lean syntax.
It creates a normal predicate named `preconnected`, usable in ordinary Lean theorem
statements and proofs. Mean propositions can also be embedded within Lean, and
Mean definition bodies can contain ordinary Lean expressions.

`import Mean` provides the complete library; use `import Mean.Syntax` if you only
want the writing syntax, without the renderer.

This supports starting with a readable formal specification, whether written by
a mathematician or an LLM. Use `#print preconnected` to inspect the resulting Lean.
Use `#mean preconnected` to read its canonical Mean
rendering as a check on how the input was interpreted. The renderer may choose different words or omit redundant
names; it checks meaning rather than preserving the original spelling.

The two directions should grow together. Writing needs a precise, compositional
grammar; rendering needs predictable wording and enough coverage to make existing
Lean readable. Both benefit from reviewed vocabulary and access to the underlying
formal definitions.

## What is checked, and what still needs review?

The renderer reads `Lean.Expr`, where names and implicit arguments have been
resolved, rather than translating source text. It is implemented separately from
the forward syntax macros. This gives two implementations to compare, although
independence alone is not a correctness guarantee.

Every successful rendering is checked by parsing the actual output text,
elaborating its expression or definition body, testing definitional equality,
and asking Lean's kernel to check an equality certificate. The comparison permits
renaming fresh universe parameters introduced by `Type*`, but does not specialize
them to fixed levels. Checks reject unresolved metavariables and expressions
containing `sorry`. A failed round trip produces an error instead of a displayed
rendering.

**This checks preservation of formal meaning, not agreement with human intent.**
The vocabulary still needs review. If both directions consistently use a misleading
English phrase for a Lean concept, the round trip cannot detect that. A small,
compositional collection of mappings makes this review more manageable.

The graph example illustrates why conventions matter. `G.Path u v` permits a
zero-length path, and the pairwise-path definition holds vacuously for an empty
graph. It is equivalent to mathlib's `G.Preconnected`. Mathlib's `G.Connected`
additionally requires a vertex. `Examples/MeanToLean.lean` proves both the first equivalence
and the second under `[Nonempty V]`.

Different phrasings can have exactly the same interpretation. The parser can
accept alternatives while the renderer chooses a consistent style—for example,
`for all` rather than `for every`. Different *mathematical formulations* may require
more than definitional equality: `Nonempty (G.Path u v)` and
`∃ p : G.Path u v, True` are logically equivalent but not definitionally equal.
Checked equivalence rules are a future extension. The renderer preserves
`Nonempty T` as `T is nonempty`, rather than rewriting it to an existential.
Similarly, `IsEmpty T` renders as `T is empty`. These phrases describe types.

## Try it

With [elan](https://github.com/leanprover/elan) installed, run from this directory:

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
lake build
```

Lean and mathlib are pinned to v4.31.0. `lake build` checks both directions and the
round-trip tests.

To also check the examples' exact before/after output, using Python 3.9 or newer:

```sh
python test.py
```

This builds the project, runs the renderer examples, and compares their output
with [Examples/LeanToMean.out](Examples/LeanToMean.out). Changes produce
a diff and a nonzero exit status. Source locations are ignored; wording,
parentheses, indentation, and blank lines are checked. LF and CRLF are equivalent.
The forward examples and round-trip meaning checks still run as part of the build.

After an intentional output change, regenerate the snapshot and review its diff:

```sh
python test.py --update
```

There are runnable examples in both directions:

| Direction | File | What it demonstrates |
|---|---|---|
| Mean → Lean | [Examples/MeanToLean.lean](Examples/MeanToLean.lean) | Mean definitions and propositions, checked against explicit Lean expressions and used in ordinary proofs |
| Lean → Mean | [Examples/LeanToMean.lean](Examples/LeanToMean.lean) | Before/after renderings of elaborated Lean, with checked round trips |

Run either from this directory:

```sh
lake env lean Examples/MeanToLean.lean
lake env lean Examples/LeanToMean.lean
```

`Examples/MeanToLean.lean` checks its definitions and proofs without printing them. In a Lean
editor, add `#print preconnected` after the definition to inspect the resulting
Lean in the Infoview. `Examples/LeanToMean.lean` prints the before/after comparisons;
in the editor, place the cursor on a comparison command to see its output.

Comparisons have this format, with a blank line between examples:

```text
∃ (n : ℕ), n = 0
-> MEAN
there is a natural number n such that
  n = 0
```

| Command | Output |
|---|---|
| `#mean name` | A definition's rendering, or a theorem's statement without its proof |
| `#mean_term expression` | A rendering of an expression; section variables are supported |
| `#mean_compare name` | Ordinary Lean and Mean for a declaration |
| `#mean_term_compare expression` | Ordinary Lean and Mean for an expression |
| `#print name` | Lean's own display of the definition |

The comparison's before view prints the elaborated expression, not the original
source spelling. Rendering commands display text without adding declarations.
Output is checked in its original namespace, import, variable, and universe
context; it is not a standalone export file.

## Compositional syntax

The grammar separates logical structure from mathematical vocabulary:

| Component | Examples |
|---|---|
| Definition clause | `Definition: <subject> is <name> if <proposition>.` |
| Subject | `a simple graph G`, `a natural number n`, `a boolean x`, `an element x of T` |
| Universal quantifier | `for all <bindings>: <proposition>`, `for every …` |
| Quantified bindings | `u and v in V`, `vertices u and v of G` |
| Existential quantifier | `there is <witness description> [such that <proposition>]` |
| Negated existential | `there is no <witness noun> [such that <proposition>]` |
| Witness description | `a path p in G from u to v`, `a natural number n`, `a boolean x`, `an element x of T` |
| Properties | `the edge set of G`, `G's edge set` |
| Adjectives | `<term> is <adjective>` |
| Logical connectives | `P and Q`, `P or Q`, `if P then Q` |

Here `T` is any type in scope. Standard scalar vocabulary works in subjects, universal quantifiers,
and existential witnesses (where the name is optional):

| Mean | Lean type | Mathematical notation |
| --- | --- | --- |
| `a natural number n` | `Nat` | `ℕ` |
| `an integer n` | `Int` | `ℤ` |
| `a rational number x` | `Rat` | `ℚ` |
| `a real number x` | `Real` | `ℝ` |
| `a complex number z` | `Complex` | `ℂ` |
| `a boolean x` | `Bool` | — |

`there is no` replaces the article (`a` or `an`) with `no`, keeping the noun
singular: `there is no integer`, or `there is no path p in G from u to v such that …`.
It means `¬ ∃ …`, with `True` as the default body when `such that` is omitted.
An existential with body `False` stays `there is … such that False`; it is not
negated existence.

`Real` and `Complex` are mathlib types, not floating-point approximations.
All forward scalar forms share `scalarType%`: subjects, existential witnesses,
and singular or plural universal domains. Plurals delegate to the singular noun.
The renderer keeps its independent inverse vocabulary for round-trip checking.
Universal quantifiers accept one or two names, for example `for every real number x:`
and `for all integers x and y:`. Both `for all` and `for every` accept these domains,
including natural numbers and booleans. The renderer uses singular nouns for one
name and plural nouns for two.

`and` and `or` mean Lean's `∧` and `∨`, with the same precedence and right
associativity: `P or Q and R` means `P ∨ (Q ∧ R)`. Parentheses change the grouping.
`if P then Q` means propositional implication `P → Q`; its conclusion can contain
connectives or another implication. Lean's `if P then X else Y` remains an ordinary
conditional. The renderer prefers the English forms and adds parentheses where
needed to preserve grouping and quantifier scope. Embedded implications stay
inline (for example, `if (if P then Q) then …`); standalone implications put their
conclusion on an indented line. Quantifiers retain their block layout.

For example:

```lean
there is a path p in G from u to v such that p.val.length = 0
```

means `∃ p : G.Path u v, p.val.length = 0`. The name is optional; without
`such that`, the condition defaults to `True`. Unnamed witnesses do not capture
surrounding variables. Paths are represented as walks with a proof that vertices
do not repeat; `p.val.length` accesses the walk's length.

The explicit graph subject also works:

```lean
Definition:
  a simple graph G = (V, E) is preconnected if
    for every u and v in V:
      there is a path in G from u to v.
```

Here `V` is a vertex type and `E` is bound to `G.edgeSet`, not supplied independently.
Neither name needs to appear in the body. Simple graphs are undirected and have no
loops; neither finiteness nor nonemptiness is assumed. The abbreviation `G.V`
exposes mathlib's existing vertex-type parameter without changing its representation.

To extend the forward language, add a subject, domain, or witness description and
its interpretation. A new witness noun implements `existsWitness%`; it does
not require another rule for `there is … such that …`. The corresponding renderer
vocabulary can be extended independently.

## Properties

`the <property> of <term>` and `<name>'s <property>` share `propertyOf%` mappings.
The renderer chooses the first form, including inside equalities, membership,
and other Lean expressions. Complex owners use parentheses, such as
`the edge set of (G ⊔ H)`; the possessive form currently takes an identifier.

| Property phrase | Lean expression |
| --- | --- |
| `the edge set of G` | `G.edgeSet` |
| `the vertex type of G` | `G.V` |
| `the set of neighbors of u in G` | `G.neighborSet u` |
| `the set of edges incident to u in G` | `G.incidenceSet u` |

Vertex-relative properties share `the <property> <vertex> in <graph>` syntax.
The shorter forms `the neighbor set of u in G` and `the incidence set of u in G`
are also accepted, as is `the set of u's neighbors in G`. They share the same
interpretations; the renderer uses the
longer phrases in the table. Possessive forms are `u's neighbor set in G` and
`u's incidence set in G`: the vertex owns the set, and the graph is its context.
All variants share one `vertexSetOf%` interpretation per set kind.

For example, `G's edge set = ∅` defines the same proposition as `G.edgeSet = ∅`.
The vertex property is called a **type**, matching Lean's representation. Neighbors
are a set of vertices; the incidence set contains edges incident to the given vertex.
These are explicit mappings, not automatic conversions of arbitrary field names.
Ordinary Lean output in before/after comparisons retains its original notation.

## Adjectives

`<term> is <adjective>` uses one grammar rule. Each adjective supplies a Lean
predicate through `adjectivePredicate%`; Lean checks the subject's type.
The renderer maintains an independent inverse mapping and checks each round trip.

| Adjective | Lean predicate | Subject |
| --- | --- | --- |
| `nonempty` | `Nonempty` | Type |
| `empty` | `IsEmpty` | Type |
| `finite` | `Finite` | Type |
| `infinite` | `Infinite` | Type |
| `countable` | `Countable` | Type |
| `injective` | `Function.Injective` | Function |
| `surjective` | `Function.Surjective` | Function |
| `bijective` | `Function.Bijective` | Function |

For example, `f is injective and f is surjective` preserves both predicates.
`finite` asserts finiteness without supplying a `Fintype` enumeration. Set predicates
such as `Set.Finite` are not yet overloaded onto this vocabulary.

## Current coverage and limitations

The renderer recognizes the current graph, standard scalar, and typed-element
subjects; paired universal quantifiers and single scalar quantifiers; positive and negative existential witnesses; optional
conditions; conjunctions, disjunctions, and nondependent propositional implications.
It canonically omits unused witness names and graph component names.
It substitutes local `let` aliases, so `E` may render as `G.edgeSet`.

Unsupported forms remain ordinary Lean, provided that text passes the same
round-trip check. **Identical before/after examples show gaps in rendering
coverage, not failed verification.** Current gaps include:

- Single-variable quantifiers outside the standard scalar domains, and general
  dependent domains; their unsupported portions remain ordinary Lean.
- Definition subjects with additional parameters or hypotheses.
- Fixed or compound universe signatures, which cannot safely use the current
  universe-polymorphic graph subject.
- Recursive rendering inside some unsupported outer structures. In particular,
  an outer implicit binder can cause a whole theorem statement to remain Lean.
- Additional English connectives such as general negation and equivalence, unrestricted
  predicate applications after `is`, and broader mathematical vocabulary.

Some gaps require more Mean syntax; others only require the renderer to translate
supported subexpressions while retaining an ordinary Lean outer structure.

Indentation is currently for readability: **dedenting does not close a scope**.
The grammar determines scope. The renderer removes unnecessary grouping, but some
parentheses remain necessary. For example, `(n = 0).` prevents the final `0.` from
being read as a Lean decimal token. Compound field projections may also need
parentheses. English keywords such as `a` and `graph` are reserved after importing
Mean; Lean identifiers with those names need escaping, as in `«a»`.

## Development direction

The next steps are to expand binders and hypotheses, add reviewed mathematical
vocabulary, and improve rendering inside partially supported expressions. These
extend both what authors can write in Mean and what readers can inspect through it.
A small, explicit collection of kernel-checked equivalence rules could then support
useful changes of mathematical formulation beyond definitional equality.

The guiding constraint is that added readability should remain tied to the formal
statement being written or reviewed. Canonical wording, inspectable mappings, and
checked round trips are the tools for doing that; the human still decides whether
the statement expresses the intended mathematics.

## Related projects

- **[Verbose Lean 4](https://github.com/PatrickMassot/verbose-lean4)** provides
  controlled-language tactics and commands inside Lean 4, with teaching examples
  and exercise libraries. This is an implemented Lean library, aimed primarily at
  teaching students to write proofs that transfer to paper. Its
  [configuration guide](https://github.com/PatrickMassot/verbose-lean4/blob/master/basic-configuration.md)
  describes how to customize its behavior; adapting teaching support to a new
  subject can require configuring automation or extending the library. Verbose Lean
  served as the model for Mean's approach to controlled mathematical language
  implemented directly inside Lean. Mean extends this direction toward rendering
  existing definitions and statements with checked round trips.

- **[ForTheL / Naproche](https://github.com/naproche/naproche)** is an implemented
  system for checking mathematical texts in controlled language, including LaTeX.
  ForTheL is the language; Naproche is a checker using automated theorem provers,
  with a distributed Isabelle/jEdit integration. Its documented end-user workflow
  does not use Lean. There have been real Lean translation experiments:
  [Koepke's 2020 talk](https://www.andrew.cmu.edu/user/avigad/meetings/fomm2020/slides/fomm_koepke.pdf)
  shows generated Lean declarations, with a theorem proof omitted, and discusses
  the remaining translation work. As of September 2026, we did not find a
  documented, maintained, general ForTheL-to-Lean-4 bridge in these project
  materials. Its language design is relevant to Mean, but its checking
  infrastructure is separate from Lean.

- **[GFLean](https://github.com/pkshashank/GFLeanTransfer)** translates a simplified
  ForTheL into Lean expressions using Grammatical Framework and Haskell. The
  [2024 paper](https://arxiv.org/html/2404.01234v1) reports translating 42 of 62
  statements from a textbook chapter after minor rephrasing. It also documents a
  small fixed vocabulary, no runtime extension through new definitions, and no
  communication with Lean's environment; examples contain `sorry` proofs. This is
  a concrete controlled-language-to-Lean prototype, not a general mathlib frontend
  or a checked Lean-to-English renderer.

- **[Informath](https://github.com/GrammaticalFramework/informath)** is especially
  close to Mean's readability goal: symbolic translation between formal statements
  and several natural languages, using Dedukti as an intermediate language and
  Grammatical Framework for linguistic structure. Its README gives a working
  recipe for generating Lean text and checking examples after adding
  `BaseConstants.lean`. However, its
  [implementation notes](https://github.com/GrammaticalFramework/informath/blob/main/doc/informath-under-the-hood.md)
  explicitly describe partial conversions: valid Dedukti input can produce code
  that fails Lean type checking. Import from Lean relies on external translators,
  and readable domain vocabulary needs symbol mappings. It should not be treated
  as an established arbitrary-mathlib round-trip pipeline. Its grammar and
  separation of meaning from wording are valuable references for Mean.

- **[Lean2dk](https://github.com/Deducteam/lean2dk)** is relevant to that external
  translation step: it exports Lean to Dedukti, rather than to English. Its README
  labels it work in progress and documents a branch that checks a Lean natural-number
  module using a patched Dedukti kernel and some stubbed constants. This is useful
  interoperability research, but does not by itself establish a complete,
  meaning-preserving Lean–Informath pipeline.

- **[Informalean](https://github.com/sglasman/informalean)** trains a language model
  to turn Lean theorem statements into English and provides generated examples.
  It directly addresses informalization of Lean, but uses learned paraphrasing;
  the project does not document a deterministic inverse or a Lean-checked
  meaning-preservation guarantee for those outputs. It is a useful comparison for
  fluent output whose fidelity still requires human review.

Mean's particular experiment is to keep both directions inside Lean and check the
actual rendered text against the elaborated original, while accepting a much
smaller vocabulary and falling back to Lean for unsupported expressions.

## Files

| File | Purpose |
|---|---|
| `Mean.lean` | Imports the complete library |
| `Mean/Syntax.lean` | Mean → Lean grammar and interpretations |
| `Mean/RoundTrip.lean` | Checks rendered text against its original Lean expression |
| `Mean/Render.lean` | Lean → Mean renderer and display commands |
| [Examples/MeanToLean.lean](Examples/MeanToLean.lean) | Forward-language examples, exact-meaning checks, and mathlib equivalence proofs |
| [Examples/LeanToMean.lean](Examples/LeanToMean.lean) | Before/after examples and round-trip checks, including rejection of changed predicates and universe signatures |
| `test.py` | Builds the project and checks the rendered examples against their expected output |
| `Examples/LeanToMean.out` | Reviewed before/after output, including exact formatting |
