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
  readable language to define values and predicates and express propositions that
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

Named values use `Definition: <name> is <value>.`:

```lean
Definition: double is the function mapping a natural number n to 2 * n.
```

This creates `def double := fun (n : Nat) => 2 * n`. The function phrase is an
expression that also works inside ordinary Lean terms, independently of
`Definition`. It accepts the same subjects as predicate definitions, including
`an integer n`, `an element x of T`, and `a simple graph G`. Its body can be any
Lean or Mean expression, including another function or a proposition:

```lean
Definition: add is the function mapping a natural number n to
  the function mapping a natural number m to n + m.
Definition: answer is the integer 42.
```

Use `Abbreviation:` with the same value or predicate clauses to create Lean
`abbrev` declarations:

```lean
Abbreviation: Natural is Nat.
Abbreviation: a natural number n is zero if (n = 0).
```

These definitions are reducible: Lean unfolds them readily, including during
overload resolution and typeclass inference. `#mean` renders them with
`Abbreviation:` and checks that the declaration kind is preserved alongside
the defined value.

`the <scalar> <value>` is a typed expression, usable independently of `Definition`.
For example, `the integer 42` means `(42 : Int)`, and `the natural number 42`
means `(42 : Nat)`. It uses the same scalar nouns as bindings, including rational,
real, and complex numbers and booleans. Group compound operands with parentheses:

```lean
the integer (2 * n)
the boolean false
```

A scalar numeral can directly precede the definition's final period, as in
`the integer 42.` or `the integer -42.`. Decimal fractions and scientific
notation retain their usual Lean meaning, for example `the rational number 1.5`.

Join full subject phrases with `and` to bind successive arguments:

```lean
Definition: shifted is
  the function mapping a natural number offset and a natural number n to n + offset.
Definition: indexValue is
  the function mapping a natural number n and an element i of Fin n to i.val.
```

These mean `fun (offset n : Nat) => n + offset` and
`fun (n : Nat) (i : Fin n) => i.val`. Earlier names are in scope in later subjects
and the body. Subjects may have different types, and more than two can be joined.
The renderer combines consecutive explicit, implicit, strict implicit, and instance function
binders this way. Nested function phrases remain accepted. Parameter types such as
`Type`, `Sort u`, `Fin n`, and `SimpleGraph V` need no surrounding parentheses.
Parentheses delimit a conjunction used as a subject type, such as
`a proof h that (P and Q)`, because `and` also separates parameters.

Lists and functions have noun phrases that keep their original Lean type names:

```lean
a list T of Tile elements
a function t from ℤ and ℤ to Tile
```

These bind `T : List Tile` and `t : ℤ → ℤ → Tile`. `Tile` can be any type in
scope, including an ordinary user-defined type; no English vocabulary declaration
or pluralization of its name is needed. Group compound list element types, as in
`a list T of (Fin n) elements`.

Function domains separated by `and` are curried arguments. A product domain stays
explicit: `a function f from (ℤ × ℤ) to Tile` means `(ℤ × ℤ) → Tile`.
Group function-valued domains too, as in `from (ℕ → ℕ) to ℕ`.
The renderer uses from/to wording for anonymous, explicit, nondependent arrow signatures.
Dependent or implicit signatures, and named parameters inside function types,
retain their exact Lean notation in element phrases.

Both nouns work in predicate subjects and function parameters, including
`an implicit list T of Tile elements`, `a strictly implicit list T of Tile elements`,
and the corresponding implicit function forms. Existential witnesses use the
same descriptions with optional names:

```lean
there is a list T of Tile elements such that T = []
there is a function t from ℤ and ℤ to Tile such that t = t
there is no list of Tile elements
```

Use `an implicit <scalar> <name>` or `an implicit element <name> of <type>`
for an argument Lean may infer from context:

```lean
Definition: implicitAdd is
  the function mapping a natural number n and an implicit natural number m to n + m.
```

This means `fun (n : Nat) {m : Nat} => n + m`. For example,
`implicitAdd 3 (m := 4)` returns `7`. Implicit and explicit subjects may appear
in any order, with earlier names still in scope in later types. For example,
`an implicit natural number n and an element i of Fin n` lets Lean infer `n`
from the type of `i`. The optional function type applies to these forms too.

Use `a strictly implicit <scalar> <name>` or
`a strictly implicit element <name> of <type>` for Lean's `⦃…⦄` binders:

```lean
Definition: strictIndex is
  the function mapping a strictly implicit natural number n and
    an element i of Fin n to i.val.
```

This means `fun ⦃n : Nat⦄ (i : Fin n) => i.val`. Lean inserts a strict implicit
argument when a later explicit argument is supplied, so `strictIndex (2 : Fin 3)`
infers `n = 3`. Ordinary implicit arguments are inserted eagerly. Prefer strict
implicit parameters with a later explicit parameter that determines them.
These forms also support the optional whole-function type.

Instance parameters use `an instance of typeclass C` or
`an instance inst of typeclass C`:

```lean
Definition: defaultValue is
  the function mapping an implicit element A of Type and
    an instance of typeclass Inhabited A to (default : A).
```

This means `fun {A : Type} [Inhabited A] => (default : A)`. A named instance,
`an instance inst of typeclass Inhabited A`, means `[inst : Inhabited A]`.
Lean finds instance arguments through typeclass search; ordinary implicit
arguments use inference from type constraints. Strict implicit arguments use
the same inference, triggered by a later explicit argument.
The class application is checked, including proposition-valued classes such as
`Fact P`. Instance witnesses also work, for example
`there is an instance of typeclass Inhabited A`.

All parameter descriptions allow an omitted name, including scalar, element,
proof, list, function, graph, and instance descriptions:

```lean
the function mapping a natural number to true
the function mapping an implicit list of Tile elements and a boolean b to b
```

An omitted name introduces a fresh hygienic binder and cannot capture a name in
the body. Anonymous instances still participate in typeclass search. Name a
parameter when later types or the body need to refer to it. Existential witness
names remain optional too.

The renderer preserves public parameter names, including unused ones, because
Lean permits calls such as `f (n := 3)`. It follows the names in a declaration's
type when they differ from its lambda variable names. Generated anonymous names
can be omitted when the rendered remainder does not reference them. Some aliases
retain an explicit Lean declaration type to preserve this interface.

For a parameter whose type is a proposition, use `a proof <name> that <proposition>`:

```lean
the function mapping a natural number n and a proof h that n > 0 to h
```

This means `fun (n : Nat) (h : n > 0) => h`. The forms
`an implicit proof h that P` and `a strictly implicit proof h that P` preserve
their corresponding Lean binder kinds. Proof subjects also work in predicate
definitions, for example `Definition: a proof h that True is reflexive if h = h.`
The proposition after `that` is checked to have type `Prop`.

The renderer prefers proof wording wherever it would otherwise describe an
element of a proposition, including definition subjects and existential witnesses:
`there is a proof h that P such that h = h`, `there is a proof that P`, and
`there is no proof that P`. These retain the existing existential semantics,
including the default condition `True`; they are not simplified to `P` or `¬ P`.
Generic element syntax remains accepted. An element of `Prop` itself is a
proposition, so it continues to use element wording.

Definitions end with a period, as in the predicate form. Function bodies extend
as far as the term grammar permits; dedenting does not close them. Use parentheses
to apply a function or use it as an adjective's subject:

```lean
(the function mapping a natural number n to 2 * n) 3
(the function mapping a natural number n to n + 1) is injective
```

An optional type annotates the whole function and guides inference in its body:

```lean
Definition: zeroInteger is
  the function : Nat → Int mapping a natural number _n to (0).
```

Here `0` is an integer. Lean checks that the type's domain agrees with the subject.
Types can include dependent arrows; the typed function phrase works anywhere
the untyped one does, including with subjects joined by `and`.

`#mean double` renders a checked named value definition. The renderer uses
`the function : <type> mapping …` only when the untyped phrase cannot infer the
correct type. Scalar literals render as typed value phrases, such as `the integer 42`;
more complicated values may retain ordinary type annotations.
Predicate definitions continue to render with the existing `is … if …` form.

Theorems use the same proposition syntax, followed by an ordinary Lean proof:

```lean
Theorem natTrans3:
  for all natural numbers x and y:
    for all natural numbers z and w:
      if x = y and z = y and z = w then x = w
Proof: by
  intro x y z w ⟨hxy, hzy, hzw⟩
  exact hxy.trans (hzy.symm.trans hzw)
```

`Proof:` accepts any Lean proof term, including `by` tactic blocks. There is no
period after the statement. Namespaces and section variables work as in Lean;
parameters can also be quantified in the statement using Mean or Lean syntax.
The command creates an ordinary Lean theorem named `natTrans3`.
`#mean natTrans3` renders its `Theorem natTrans3:` header and statement, omitting
the proof. Add `Proof: …` to turn that statement view into a declaration.

`Lemma name:` is an alias for `Theorem name:`. Both render canonically as
`Theorem`, since Lean does not retain the distinction. Similarly, Mathlib provides
[`lemma`](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/Tactic/Lemma.lean)
as a macro expanding to core Lean's `theorem`. Mean expands to `theorem` through
its own `Theorem` syntax; going through Mathlib's `lemma` would add an equivalent
step without preserving the label.

`Example:` checks an anonymous declaration with the same statement and proof syntax:

```lean
Example:
  for every natural number n:
    n + 0 = n
Proof: by
  intro n
  rfl
```

Examples do not introduce a name for use with `#mean`; use `#mean_term` to render
their propositions.

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

Every successful rendering is checked by parsing its actual output text.
For expressions and theorem statements, Mean elaborates the text, tests
definitional equality, and asks Lean's kernel to check an equality certificate.
For named definitions, Mean elaborates a renamed copy of the complete printed
command in a temporary environment. It checks the resulting type and value,
function binder information, public parameter names, universe parameters, definition/abbreviation kind,
effective reducibility, and safety against the original declaration. Expected
metadata is read independently from Lean's environment. The temporary declaration
and elaboration state are discarded afterward.

These metadata checks are necessary because kernel definitional equality ignores
properties such as implicit argument flags and declaration reducibility. The
comparison permits renaming universe parameters, but does not specialize them to
fixed levels. Checks reject unresolved metavariables and compared expressions
containing `sorry`. A failed round trip produces an error instead of displayed
output. Theorems are checked through their statements; their proofs may contain
`sorry` without weakening that statement check.

The guarantee covers these expressions and metadata, rather than every aspect of
Lean behavior. Other attributes such as `[simp]` and instance registration,
compiled code behavior, and performance are outside the current check. Unsupported
changes to the checked metadata, such as dropping an `irreducible` attribute,
cause rejection. The internal value-only annotation probe is separate from the
final declaration check.

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
lake exe cache get Mathlib.Computability.RE Mathlib.Computability.Primrec.List
lake build
```

Lean and mathlib are pinned to v4.35.0. `lake build` checks both directions and the
round-trip tests.

To also check the examples' exact generated output, using Python 3.9 or newer:

```sh
python test.py
```

This builds the project, runs the renderer examples, and checks two views:

- Mean output only: [Examples/LeanToMean.mean](Examples/LeanToMean.mean) and
  [Examples/Wang.mean](Examples/Wang.mean).
- Paired Lean/Mean comparisons: [Examples/LeanToMean.compare](Examples/LeanToMean.compare)
  and [Examples/Wang.compare](Examples/Wang.compare).

Changes produce a diff and a nonzero exit status. Source locations are ignored; wording,
parentheses, indentation, and blank lines are checked. LF and CRLF are equivalent.
The `.mean` files contain only the checked Mean renderings; `.compare` files
also show the original elaborated Lean, separated by `-- LEAN INPUT:` and
`-- MEAN OUTPUT:` comments. These are generated views, not standalone programs:
for example, rendered theorem statements omit proofs and term examples can refer
to their original section variables. Each file begins with a comment identifying
its Lean source and regeneration command.
Upstream source and license links in the input's opening comment
are copied to the generated header.
The repository's `.gitattributes` selects Lean 4 syntax highlighting for both
extensions on [GitHub](https://github.com/github-linguist/linguist/blob/main/docs/overrides.md#using-gitattributes).
VS Code uses a separate mechanism: the repository's
[workspace settings](.vscode/settings.json) use
[`files.associations`](https://code.visualstudio.com/docs/languages/overview#_add-a-file-extension-to-a-language)
to associate both extensions with `lean4`.
Install the Lean 4 extension and open the repository folder to use these associations.
The forward examples and round-trip meaning checks still run as part of the build.

After an intentional output change, regenerate both views and review the diff:

```sh
python test.py --update
```

There are runnable examples in both directions:

| Direction | File | What it demonstrates |
|---|---|---|
| Mean → Lean | [Examples/MeanToLean.lean](Examples/MeanToLean.lean) | Mean definitions and propositions, checked against explicit Lean expressions and used in ordinary proofs |
| Lean → Mean | [Examples/LeanToMean.lean](Examples/LeanToMean.lean) | Before/after renderings of elaborated Lean, with checked round trips |
| Lean → Mean | [Examples/Wang.lean](Examples/Wang.lean) | Definitions and main theorem statements from a Wang tiling formalization |

Run these from this directory:

```sh
lake env lean Examples/MeanToLean.lean
lake env lean Examples/LeanToMean.lean
lake env lean Examples/Wang.lean
```

`Examples/MeanToLean.lean` checks its definitions and proofs without printing them. In a Lean
editor, add `#print preconnected` after the definition to inspect the resulting
Lean in the Infoview. `Examples/LeanToMean.lean` prints the before/after comparisons;
in the editor, place the cursor on a comparison command to see its output.

Comparisons have this format, with a blank line between examples:

```text
-- LEAN INPUT:
∃ (n : ℕ), n = 0
-- MEAN OUTPUT:
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
The Lean input view preserves `abbrev` for abbreviations; the Mean output uses
`Abbreviation:`. Both the defined value and this declaration kind are checked.
Output is checked in its original namespace, import, variable, and universe
context; it is not a standalone export file.

## Wang tiling example

[Examples/Wang.lean](Examples/Wang.lean) adapts the formal abstract
from [lean-wang at commit 64268a3](https://github.com/edemaine/lean-wang/blob/64268a3aaaef3eac65559352ef94f62ab9c00482/LeanWang/Abstract.lean).
It keeps the original nine definitions/abbreviations and compares the statements
of co-RE-completeness and undecidability. The upstream attribution and
[Apache 2.0 license](Examples/Wang.LICENSE) are retained.
The [upstream license](https://github.com/edemaine/lean-wang/blob/64268a3aaaef3eac65559352ef94f62ab9c00482/LICENSE)
is linked in `Wang.lean` and both generated headers. A local license copy accompanies
the adapted source, as required by [Apache 2.0 §4(a)](https://www.apache.org/licenses/LICENSE-2.0#redistribution).

Mean and lean-wang both use Lean/mathlib 4.35.0.
The original lambda parameter `a` is spelled `«a»` because Mean reserves `a`;
this escapes the identifier without renaming it.
The two theorem declarations are retained with `sorry` proofs and rendered by
`#mean_compare`. Only their statements are checked here; the complete proofs
remain upstream. The `sorry` warning is disabled locally for these two copied
declarations, while other renderer warnings and errors remain checked.

[Examples/Wang.mean](Examples/Wang.mean) contains the generated Mean output;
[Examples/Wang.compare](Examples/Wang.compare) pairs it with the Lean input.
Each rendering passes the usual checked round trip,
and `python test.py` checks the exact output. This is a baseline for improving
the translation of real mathematics; unsupported portions retain Lean syntax.
The tiling definition renders existential and integer quantifiers and conjunctions.
The complexity definitions use `an instance of typeclass Primcodable α` for their
instance parameters. `CoRE` describes the function mapping `«a»` to `«a» is not p`
as recursively enumerable. Named predicates without registered English wording
use their Lean names after `is`. `CoREComplete` renders its function-valued universal and
existential quantifiers, implication, conjunction, and equivalence in Mean.

## Compositional syntax

The grammar separates logical structure from mathematical vocabulary:

| Component | Examples |
|---|---|
| Definition clause | `Definition: <subject> is <name> if <proposition>.` |
| Named value clause | `Definition: <name> is <value>.` |
| Abbreviation clause | `Abbreviation: <name> is <value>.`, `Abbreviation: <subject> is <name> if <proposition>.` |
| Function expression | `the function [: <type>] mapping <subject> [and <subject> …] to <value>` |
| Typed scalar value | `the <scalar> <value>`, `the integer 42`, `the real number (2 * x)` |
| Theorem clause | `Theorem <name>: <proposition> Proof: <Lean proof>` |
| Lemma clause | `Lemma <name>: <proposition> Proof: <Lean proof>` |
| Example clause | `Example: <proposition> Proof: <Lean proof>` |
| Subject | `a simple graph G`, `a natural number n`, `a boolean x`, `an element x of T` |
| Implicit subject | `an implicit natural number n`, `an implicit element x of T` |
| Strict implicit subject | `a strictly implicit natural number n`, `a strictly implicit element x of T` |
| Proof subject | `a proof h that P`, `an implicit proof h that P`, `a strictly implicit proof h that P` |
| Instance subject | `an instance of typeclass C`, `an instance inst of typeclass C` |
| List subject | `a list T of Tile elements`, `a list T of (Fin n) elements` |
| Function subject | `a function f from A to B`, `a function f from A and B to C` |
| Universal quantifier | `for all <bindings>: <proposition>`, `for every …` |
| Quantified bindings | `function q from ℕ to Prop`, `list xs of T elements`, `element x of T`, `u and v in V`, `vertices u and v of G` |
| Existential quantifier | `there is <witness description> [such that <proposition>]` |
| Negated existential | `there is no <witness noun> [such that <proposition>]` |
| Witness description | `a path p in G from u to v`, `a natural number n`, `a boolean x`, `an element x of T`, `a proof h that P` |
| Properties | `the edge set of G`, `G's edge set` |
| Adjectives | `<term> is <adjective>`, `<term> is not <adjective>`, `x is FooPred` |
| Logical connectives | `P and Q`, `P or Q`, `if P then Q`, `P if and only if Q` |

Here `T` is any type in scope. Standard scalar vocabulary works in subjects, function bindings, universal quantifiers,
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
All forward scalar forms share `scalarType%`: typed values, subjects, existential witnesses,
and singular or plural universal domains. Plurals delegate to the singular noun.
The renderer keeps its independent inverse vocabulary for round-trip checking.
Universal quantifiers accept one or two names, for example `for every real number x:`
and `for all integers x and y:`. Both `for all` and `for every` accept these domains,
including natural numbers and booleans. The renderer uses singular nouns for one
name and plural nouns for two.

Single-variable universal quantifiers also accept the existential witness nouns,
without an article: `for every function q from ℕ to Prop: …`,
`for every list xs of T elements: …`, or `for every element i of Fin n: …`.
Proof, path, and instance nouns work too. Names are optional; earlier names are
in scope in later domains and the body. These bind explicit parameters; an
instance noun checks that its domain is a typeclass. Dependent function types retain Lean notation
inside an element phrase.

`and` and `or` mean Lean's `∧` and `∨`, with the same precedence and right
associativity: `P or Q and R` means `P ∨ (Q ∧ R)`. Parentheses change the grouping.
`if P then Q` means propositional implication `P → Q`; its conclusion can contain
connectives or another implication. `P if and only if Q` means `P ↔ Q`, with the
same precedence as `↔`, below implication, `or`, and `and`. Nested equivalences
require parentheses. Group implications when combining them with equivalence:
`(if P then Q) if and only if R` and `if P then (Q if and only if R)`.
Lean's `if P then X else Y` remains an ordinary
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
its interpretation. A subject implements `functionOn%`, shared by function expressions
and predicate definitions; `predicateOn%` additionally requires a proposition body.
A new witness noun implements `existsWitness%`; it does
not require another rule for `there is … such that …`. The corresponding renderer
vocabulary can be extended independently.

## Properties

`the <property> of <term>` and `<name>'s <property>` share `propertyOf%` mappings.
The renderer chooses the first form, including inside equalities, membership,
and other Lean expressions. Complex owners use parentheses, such as
`the edge set of (G ⊔ H)`; the possessive form currently takes an identifier.
Property phrases bind above comparisons but below arithmetic and set operations:
`the vertex type of G is nonempty` needs no parentheses, while a union renders as
`(the edge set of G) ∪ (the edge set of H)`.

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

`<term> is <adjective>` applies the corresponding Lean predicate.
`<term> is not <adjective>` negates that application.
Registered adjectives supply a Lean predicate through `adjectivePredicate%`;
`computable` selects its predicate from the subject's codomain.
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
| `recursively enumerable` | `REPred` | Predicate |
| `computable` | `Computable` | Function with values in a type |
| `computable` | `ComputablePred` | Predicate with values in `Prop` |

For example, `f is injective and f is surjective` preserves both predicates.
`finite` asserts finiteness without supplying a `Fintype` enumeration. Set predicates
such as `Set.Finite` are not yet overloaded onto this vocabulary.

An unregistered predicate can use its Lean identifier: if `p : α → Prop`,
`x is p` means `p x`, and `x is not p` means `¬ p x`. No `Pred` suffix or
vocabulary registration is required. The application must produce a proposition;
Boolean-valued functions are rejected instead of coerced to propositions.
The renderer uses this wording for named predicates with one explicit subject
argument, preceded by any implicit type or instance arguments. Predicates with
additional explicit arguments retain ordinary Lean application notation.
Parenthesized predicates are also accepted, such as `n is (relates m)`, and let
the renderer retain explicit hidden arguments when inference would change them.

Adjective subjects render recursively, including function bodies:

```lean
(the function mapping an element «a» of α to
  «a» is not p) is recursively enumerable
```

This means `REPred (fun «a» : α => ¬ p «a»)`. Parentheses keep the outer adjective
outside the function body. Only negated predicate applications receive `is not`
wording; general negations remain ordinary Lean.

## Current coverage and limitations

The renderer recognizes graph, scalar, list, function, proof, and generic element
subjects; paired universal quantifiers and single explicit quantifiers over arbitrary
domains; positive and negative existential witnesses; optional
conditions; conjunctions, disjunctions, equivalences, and nondependent propositional implications;
and functions with explicit, implicit, strict implicit, and instance binders, including nested and dependent functions.
It omits unused witness names and unnecessary generated parameter names, while
preserving public parameter names, including graph carrier parameters.
It substitutes local `let` aliases, so `E` may render as `G.edgeSet`.
Graph carrier types with fixed or compound universes can render through generic
typed-element function bindings; the dedicated graph subject still uses `Type*`.

Unsupported forms remain ordinary Lean, provided that text passes the same
round-trip check. **Identical before/after examples show gaps in rendering
coverage, not failed verification.** Current gaps include:

- Predicate subject forms with additional parameters or hypotheses; named values
  can express these through nested function bindings.
- Recursive rendering inside some unsupported outer structures. In particular,
  an outer implicit universal binder can cause a whole theorem statement to remain Lean.
- General negation outside predicate applications, automatic English wording for
  predicates with multiple explicit arguments, and broader mathematical vocabulary.

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
| `Examples/*.mean` | Generated Mean output only, including exact formatting |
| `Examples/*.compare` | Generated paired Lean/Mean comparisons |
