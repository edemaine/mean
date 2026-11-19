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
  a simple graph G satisfies preconnected if
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

Predicates with multiple explicit arguments use `satisfy` (`are` remains an alias):

```lean
Definition:
  elements p and q of Point satisfy adjacent if
    (the sum over indices i in [0, 3) of |p i - q i| = 1).
```

Here `Point` is an existing type, such as `Fin 3 → ℤ`. Group two or more names
with `elements x and y of T`, scalar plurals such as `integers x and y`, or
`indices i and j in [0, n)`. Mixed or dependent subjects retain their individual
descriptions: `a natural number n and an index i in [0, n) satisfy below if i.val < n.`
Earlier subjects are in scope in later types and the proposition. `Abbreviation:`
accepts the same forms. The renderer preserves the predicate's Lean name.

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
Abbreviation: a Natural is a natural number.
Abbreviation: a natural number n satisfies zero if (n = 0).
```

These definitions are reducible: Lean unfolds them readily, including during
overload resolution and typeclass inference. `#mean` renders them with
`Abbreviation:` and checks that the declaration kind is preserved alongside
the defined value.

Named types can put an article before their name and use an anonymous binding
phrase on the right:

```lean
Abbreviation: a Prototile is a list of Point elements.
Abbreviation: a Direction is an index in [0, 4).
Definition: a DefinedPrototile is a list of Point elements.
```

The first two forms create `abbrev Prototile := List Point` and
`abbrev Direction := Fin 4`; the last creates `def DefinedPrototile := List Point`.
Use `a` or `an` before the name. The right-hand description must be anonymous
and must denote a type: it introduces no list, index, or other value. The same
nouns serve ordinary bindings and type declarations, including functions,
scalars, generic elements, proofs, paths, and typeclass instances.
The renderer uses this form when a declaration names a type directly and
preserves the original `def`/`abbrev` distinction. Type families with parameters
keep the ordinary function form. Existing named-value forms remain accepted.

`the <scalar> <value>` is a typed expression, usable independently of `Definition`.
For example, `the integer 42` means `(42 : Int)`, and `the natural number 42`
means `(42 : Nat)`. It uses the same scalar nouns as bindings, including rational,
real, and complex numbers and booleans. Group compound operands with parentheses:

```lean
the integer (2 * n)
the boolean false
```

Use `as` to request a Lean coercion to a scalar or custom type:

```lean
(p i as a real number) ≤ x i
n as an integer
x as Foo
x as Box A
```

`p i as a real number` means `(↑(p i) : ℝ)`. Lean infers the source type and
checks that a conversion exists. Parentheses around source arithmetic preserve
its type: `(n - m) as an integer` subtracts natural numbers before converting
the result when `n` and `m` are natural numbers. A custom target uses its Lean
type expression directly; parenthesize a function type, as in `f as (Nat → Nat)`.
Lean must have an appropriate coercion, such as a `Coe` instance. The renderer
uses scalar nouns for known scalar targets and the type expression for other
registered value coercions. Lean's function and sort coercion forms (`⇑`, `↥`)
retain Lean notation.

A scalar numeral can directly precede the definition's final period, as in
`the integer 42.` or `the integer -42.`. Decimal fractions and scientific
notation retain their usual Lean meaning, for example `the rational number 1.5`.

Join full subject phrases with `and` to bind successive arguments:

```lean
Definition: shifted is
  the function mapping a natural number offset and a natural number n to n + offset.
Definition: indexValue is
  the function mapping a natural number n and an index i in [0, n) to i.val.
```

These mean `fun (offset n : Nat) => n + offset` and
`fun (n : Nat) (i : Fin n) => i.val`. Earlier names are in scope in later subjects
and the body. Subjects may have different types, and more than two can be joined.
The renderer combines consecutive explicit, implicit, strict implicit, and instance function
binders this way. Nested function phrases remain accepted. Parameter types such as
`Type`, `Sort u`, `Fin n`, and `SimpleGraph V` need no surrounding parentheses.
Parentheses delimit a conjunction used as a subject type, such as
`a proof h that (P and Q)`, because `and` also separates parameters.

Lists, sets, and functions have noun phrases, with familiar scalar plurals and original
names for custom types:

```lean
a list T of Tile elements
a list xs of natural numbers
a set S of Point elements
a function t from ℤ and ℤ to Tile
```

These bind `T : List Tile`, `S : Set Point`, and `t : ℤ → ℤ → Tile`. `Tile` can be any type in
scope, including an ordinary user-defined type; no English vocabulary declaration
or pluralization of its name is needed. Group compound collection element types, as in
`a list T of (the type of indices in [0, n)) elements`. Known scalar types use their usual plurals:
natural numbers, integers, rational numbers, real numbers, complex numbers, and
booleans. The original `a list xs of Nat elements` form remains accepted.

Type descriptions use plural nouns with an explicit `the type of` introducer:

```lean
the type of lists of Point elements
the type of sets of Point elements
the type of indices in [0, 4)
```

Here `the type of lists of Point elements` denotes `List Point`.
`the type of sets of Point elements` denotes `Set Point`; sets may be infinite.
`the type of lists of natural numbers` similarly means `List Nat`, and
`the type of natural numbers` means `Nat`. Standard symbols such as `ℕ` remain
available. Bindings stay singular, even when their name is omitted:
`a list of Point elements` is an anonymous binding phrase, not a type expression.
These type phrases also work inside function signatures and compound types.
The renderer preserves custom type names such as `Point` without pluralizing them.
Collections of functions can use phrases such as
`the type of sets of functions from indices in [0, n) to ℝ`.

Set phrases work in function and predicate subjects, universal quantifiers, and
positive, negative, and unique existential witnesses:

```lean
there is a set T of Point elements such that T = ∅
for every set S of integers where 0 ∈ S: 0 ∈ S
a function f from sets of Point elements to sets of integers
```

Implicit and strictly implicit set parameters use `an implicit set S of …` and
`a strictly implicit set S of …`, following the other subject nouns.

Set comprehensions bind an element and describe its membership condition:

```lean
the set of elements x of RealPoint such that
  there is an element p of Point such that
    p ∈ P and (for every index i in [0, 3):
      (p i : ℝ) ≤ x i and x i ≤ (p i : ℝ) + 1)
```

This is Lean's `{x : RealPoint | …}` (`Set.ofPred`). The name is optional when
the condition does not use it, as in `the set of elements of ℕ such that True`.
For a set of functions, write
`the set of functions f from indices in [0, n) to ℝ such that …`.
The renderer translates the condition recursively, including quantifiers and
logical connectives, even when the set occurs inside otherwise ordinary Lean
syntax. Parentheses group a comprehension used as an operand or argument.

`the type of indices in [0, n)` means `Fin n`: natural-number indices starting at zero
and strictly less than `n`. It is a type expression, not a real interval or a
set. `the type of indices in [0, 0)` is empty; a bound of one admits just the index zero.
The lower endpoint must be the numeral `0`; symbolic or compound upper bounds
are allowed. Index bindings use either an explicit range or a collection:

```lean
an index i in [0, n)
an index i into xs
```

For a list `xs`, the second form means `i : Fin xs.length`; for an array,
it means `i : Fin xs.size`. Omitting `i` gives an anonymous binding phrase;
`the type of indices into xs` denotes its domain type. The older type spelling
`indices [0, n)` remains accepted. For example:

```lean
the function mapping a list xs of natural numbers and
  an index i into xs to xs[i]
```

Both forms support optional names, implicit and strictly implicit parameters,
predicate subjects, and universal and existential quantifiers:

```lean
an implicit index i in [0, n)
a strictly implicit index i into xs
for every index i into xs: xs[i] = xs[i]
there is no index in [0, 0)
```

The renderer prefers `into xs` for direct list-length and array-size bounds and
range wording for other `Fin` bounds. It keeps user-defined aliases such as
`Direction` intact. In Wang, its declaration renders as
`Abbreviation: a Direction is an index in [0, 4).`

Function domains separated by `and` are curried arguments. A product domain stays
explicit: `a function f from (ℤ × ℤ) to Tile` means `(ℤ × ℤ) → Tile`.
Group function-valued domains too, as in `from (ℕ → ℕ) to ℕ`.
The `from` and `to` context also accepts plural type descriptions directly:

```lean
a function from indices in [0, 3) to ℤ
a function from lists of Point elements to indices in [0, n)
a function from natural numbers and indices in [0, n) to integers
```

These mean `Fin 3 → Int`, `List Point → Fin n`, and `Nat → Fin n → Int`.
No `the type of` wrapper or grouping parentheses are needed around these
descriptions. `indices into xs` also works here. The renderer uses the bare
plural descriptions for `Fin` and `List`, retaining ordinary notation for
other types, including familiar symbols such as `ℕ` and `ℤ` and custom aliases.
Singular phrases still describe individual function parameters, as in
`the function mapping an index i in [0, n) to …`.
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
`an implicit natural number n and an index i in [0, n)` lets Lean infer `n`
from the type of `i`. The optional function type applies to these forms too.

Use `a strictly implicit <scalar> <name>` or
`a strictly implicit element <name> of <type>` for Lean's `⦃…⦄` binders:

```lean
Definition: strictIndex is
  the function mapping a strictly implicit natural number n and
    an index i in [0, n) to i.val.
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
definitions, for example `Definition: a proof h that True satisfies reflexive if h = h.`
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

Axioms use `Axiom name: <type>` with no proof. The type may be a proposition
or a data signature. In a data signature, `we have` describes the supplied
value's type. The phrase `an injective function from A to B` means Lean's
`A ↪ B`.

```lean
Axiom encode:
  for every natural number n:
    we have an injective function from indices in [0, n) to lists of booleans
```

Mean checks the complete axiom declaration, including its universe order and named arguments.
Universe parameters can be declared with `Axiom name.{u, v}:`. Lean's
`unsafe` modifier is also supported.

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
`Nonempty T` as `T is a nonempty type`, rather than rewriting it to an existential.
Similarly, `IsEmpty T` renders as `T is an empty type`. For lists, `xs ≠ []`
and `xs = []` render as `xs is a nonempty list` and `xs is an empty list`.

## Try it

With [elan](https://github.com/leanprover/elan) installed, run from this directory:

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
lake exe cache get Mathlib.Computability.RE Mathlib.Computability.Primrec.List
lake exe cache get Mathlib.Computability.Halting Mathlib.Computability.Reduce Mathlib.MeasureTheory.Measure.Lebesgue.Basic
lake build
```

Lean and mathlib are pinned to v4.35.0. `lake build` checks both directions and the
round-trip tests.

To also check the examples' exact generated output, using Python 3.9 or newer:

```sh
python test.py
```

This builds the project, runs the renderer examples, and checks two views:

- Mean output only: [LeanToMean.mean](Examples/LeanToMean.mean),
  [Wang.mean](Examples/Wang.mean), and [TranslationTiling.mean](Examples/TranslationTiling.mean).
- Paired Lean/Mean comparisons: [LeanToMean.compare](Examples/LeanToMean.compare),
  [Wang.compare](Examples/Wang.compare), and [TranslationTiling.compare](Examples/TranslationTiling.compare).

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

The comparison's input view preserves the original expression or declaration
source from the active module, including its notation, formatting, and comments.
Imported declarations whose source is unavailable in the active module use an
explicitly labelled reconstruction. Line endings are normalized for snapshots.
Rendering commands display text without adding declarations.
The Lean input view preserves `abbrev` for abbreviations; the Mean output uses
`Abbreviation:`. Both the defined value and this declaration kind are checked.
Declaration headings omit the current namespace: inside `TranslationTiling.Abstract`,
`Point` renders as `Point`. Nested names retain their relative path, and declarations
outside the current namespace retain their qualification, even when their namespace
is open. Reconstructed input headings use the same convention; original source
keeps its original spelling.

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
The original lambda parameter `a` is renamed to `x` because Mean reserves `a`.
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
instance parameters. `CoRE` describes the function mapping `x` to `x does not satisfy p`
as recursively enumerable. Named predicates without registered English wording
use their Lean names after `is`. `CoREComplete` renders its function-valued universal and
existential quantifiers, implication, conjunction, and equivalence in Mean.

## Translation tiling example

[Examples/TranslationTiling.lean](Examples/TranslationTiling.lean) adapts the
[formal abstract at commit 79b39ab](https://github.com/edemaine/translation-tiling-paper/blob/79b39abcd4f6bd070610657d1c2ef187b3e2bd1a/lean/TranslationTiling/Abstract.lean)
from [Tiling 3D by Translates of a Single Polycube is Undecidable](https://edemaine.github.io/translation-tiling-paper/).
It retains all 13 definitions/abbreviations and nine theorem declarations from
the November 12, 2026 update. They cover each fixed dimension `d ≥ 3`, lattice
translations, and real translations with optional rotations and reflections.
The reduction theorems now provide computable functions with explicit cube bounds.
Rigid reductions preserve tileability for every permitted motion set containing
all translations, with a dimension-dependent size factor and a sharper factor
of 64000 in dimension three. The nine bridge proofs are replaced with
`sorry`, as in Wang; the complete proofs remain upstream.

The input imports [Examples/Wang.lean](Examples/Wang.lean) and uses
`LeanWang.Abstract.CoREComplete` in its completeness statements. Upstream
uses `LeanWang.CoREComplete`, which quantifies over all encoded source types of
the same universe; the Wang abstract instead uses predicates on natural numbers
as source problems. These are equivalent formulations here, but are not
definitionally identical in Lean. This interface adaptation is recorded in the
input's top comment. A companion `LeanWang.Abstract.CoREHard` definition is added
in this example for the new hardness theorem, using the same source encoding.
Its relation to the existing completeness definition is checked by `Iff.rfl`.
The reduction statements likewise use `List LeanWang.Abstract.Tile`
and `LeanWang.Abstract.TilesPlane` from our Wang example. Upstream uses lists of
four-field Wang-tile structures; our abstract uses functions from `Fin 4` to `ℕ`.
The correspondence preserves edge colors, list lengths, and tileability, but the
types and predicates are not definitionally identical. No external Wang package is needed.
Point binders `a`, `b` are renamed to `p`, `q` because Mean reserves `a`;
`Connected` uses `x`, `y` for its outer endpoints to avoid shadowing.
Mean and both upstream projects use Lean/mathlib 4.35.0.

The pinned TranslationTiling repository does not declare a project-wide license.
Its source link and this license status are recorded in the input's top comment
and both output headers. The imported Wang example retains its Apache 2.0
license and notices.

[TranslationTiling.mean](Examples/TranslationTiling.mean) contains the checked
Mean output; [TranslationTiling.compare](Examples/TranslationTiling.compare)
pairs it with Lean input. `python test.py` checks all 23 comparisons, including
the added hardness interface. Unsupported
structures retain Lean syntax and pass the same round-trip checks.

The November 12 update prompted these general rendering improvements:

1. **Identify set literals locally.** The motion-policy condition in
   `real_tiling_coRE_complete` needs the type of its finite set of sets. Compact
   printing previously lost that information. Finite set literals now use
   `the set {…}`, distinguishing `Set` from `Finset` while inferring the element
   type from the surrounding statement. The checked
   explicit-argument fallback remains available. `finiteSetChoice` is a regression
   example for this distinction.
2. **Normalize scalar cast targets and Euclidean coordinates.** In `Solid`, the
   target `(fun i => ℝ) i` is beta-reduced before recognizing scalar vocabulary,
   and coordinate access renders as `x i`, restoring
   `p i as a real number ≤ x i`. Named type aliases and the Euclidean norm on
   `RealPoint d` are preserved. A different local coordinate coercion triggers
   the checked explicit fallback.
3. **Extend bounded quantifiers to existence and add set-image wording.** `RealTiles`
   uses “there is a subset T of motions,” “there is exactly one f ∈ T,” and
   “the image of (Solid P) under f.” Uniqueness remains restricted to motions
   in T; ordinary and negated existence support membership restrictions too.
4. **Keep project-specific predicate wording local.** The generic subject-list rule
   produces `P and motions satisfy RealTiles`; “P tiles real space using motions”
   would express those roles. That wording, and names such as “co-RE-hard,”
   belong with local declarations rather than global TranslationTiling rules.
   Predicate definitions with implicit dimension parameters retain their current
   function descriptions.
5. **Add geometry vocabulary.** Euclidean spaces, bijective affine isometries,
   linear parts, determinants, perpendicular bisectors, and reflections now have
   general wording. The isometry type explicitly retains bijectivity and its
   scalar field. Multiplication keeps its order: `t * r` applies r first, then t.
   Reflection tests include the degenerate bisector case p = q.
6. **Shorten collection properties.** `List.length (f T)` renders as
   `the length of (f T)`; `Set.univ` names the set of all elements of its type.
7. **Describe functions returning types clearly.** `Point`, `Prototile`, `RealPoint`,
   and `Motion` use `the function mapping …` with a type description as the
   result. In particular, `Point d` describes the type of functions from indices
   in `[0, d)` to integers, preserving the explicit dimension parameter.

## Definitions by cases

Simple constructor-pattern functions can be written and rendered by cases:

```lean
Definition:
  twice maps a natural number n to a natural number
  by cases on n:
    zero gives 0;
    succ k gives (twice k + 2).
```

The inputs after `maps` reuse function-subject binding syntax. The noun phrase
after `to` specifies the result type. Patterns bind the constructor's fields.
Semicolons separate cases and a period ends the definition. `Abbreviation:` is
also supported. The renderer recovers flat, exhaustive constructor cases on
the last function argument from Lean's equation theorems, including structural
recursion. It tries dot notation and leaves casts implicit when Lean can infer
them. The audit checks the printed definition's type, value, public argument
names, and declaration metadata. Unsupported patterns retain the ordinary
checked rendering.

For example, Canny's `Term.eval` and `Formula.solutionSet` expose their defining
cases instead of Lean's generated `brecOn` recursors and helper definitions.

## Inductive types

`#mean` and `#mean_compare` display the complete constructor interface of safe,
single, non-nested inductive types, including parameters and indices:

```lean
Inductive type Term parameterized by a natural number n
with constructors:
  const from an integer;
  var from an index in [0, n);
  add from two elements of Term n;
  mul from two elements of Term n.
```

Ordinary constructors return the declared type with the same parameters, so
`to …` can be omitted. Indexed families state each constructor's result:

```lean
Inductive family Vector parameterized by a type A
indexed by a natural number
with constructors:
  nil to (Vector A 0);
  cons from an implicit natural number n and an element x of A
    and an element xs of Vector A n to Vector A (n + 1).
```

Semicolons separate constructor clauses; a final period closes the declaration.
Indentation is for readability. An empty constructor list is written
`with constructors: .`. Inputs and parameters reuse function-subject vocabulary, including named dependent inputs,
implicit binders, and typeclass instances. `two elements of T` is shorthand for
two anonymous explicit inputs of type T. A nullary constructor needs only its
name before the separator or closing period. `a type A` binds `A : Type`; other sorts can use an element
binding such as `an element A of Type u`. `with values in Type u` preserves a
nondefault result universe (the default is `Type`).

The earlier `Inductive Name … : … where | …` form remains available as a precise
fallback. The round-trip checker elaborates the actual printed declaration and
compares the type and every constructor, preserving names, order, binder
implicitness, universes, and the parameter/index split. Mutual, nested, and unsafe
inductive declarations currently report an explicit unsupported-form error.

## Real-algebraic complexity example

[Examples/Canny.lean](Examples/Canny.lean) adapts the unified abstract from
[lean-canny at commit 6b758a2](https://github.com/edemaine/lean-canny/blob/6b758a2abff2b2ef69d245dad37505f9fb790921/LeanCanny/Abstract.lean).
It covers integer polynomial expressions, Boolean formulas and real solution
sets, ETR and ∃∀ℝ, whole-space connectivity, and point reachability. The seven
theorem statements include Canny's PSPACE bounds and the counting-hierarchy
bounds attributed upstream to OpenAI. The source attribution and
[Apache 2.0 license](Examples/Canny.LICENSE) are retained.

This example imports `Examples.Wang` and runs under Mean's existing toolchain
with `python test.py`. It does not depend on CSLib Frontier. Instead, an explicit
`Background` namespace declares interfaces for binary encodings, polynomial-time
reductions, PSPACE, and counting levels. Their intended meanings are documented;
their machine semantics and encoding layouts are **not implemented or verified
in this adaptation**. All seven theorem proofs are replaced by `sorry`, as in
the tiling examples. This checks rendering of statements relative to those
interfaces, not the upstream complexity proofs or equivalence with CSLib Frontier.

[Canny.mean](Examples/Canny.mean) contains Mean output;
[Canny.compare](Examples/Canny.compare) pairs its 21 checked renderings with Lean. The inductive syntax
types include their constructor signatures in both views.

## Compositional syntax

The grammar separates logical structure from mathematical vocabulary:

| Component | Examples |
|---|---|
| Definition clause | `Definition: <subject> satisfies <name> if <proposition>.` |
| Multiple predicate subjects | `Definition: <subject> and <subject> [and …] satisfy <name> if <proposition>.` |
| Named value clause | `Definition: <name> is <value>.` |
| Abbreviation clause | `Abbreviation: <name> is <value>.`, `Abbreviation: <subject> satisfies <name> if <proposition>.` |
| Named type clause | `Definition: a <name> is <anonymous description>.`, `Abbreviation: an <name> is <anonymous description>.` |
| Function expression | `the function [: <type>] mapping <subject> [and <subject> …] to <value>` |
| Function type | `the type of functions from A to B` |
| Finite sum | `the sum over indices i in [0, n) of f i`, `the sum over i in s of f i` |
| Indexed set union | `the union over natural numbers n of S n` |
| Indexed set intersection | `the intersection over natural numbers n of S n` |
| Typed scalar value | `the <scalar> <value>`, `the integer 42`, `the real number (2 * x)` |
| Scalar coercion | `<term> as a real number`, `<term> as an integer` |
| Custom target coercion | `<term> as Foo`, `<term> as Box A` |
| Theorem clause | `Theorem <name>: <proposition> Proof: <Lean proof>` |
| Axiom | `Axiom <name>: <type>` |
| Lemma clause | `Lemma <name>: <proposition> Proof: <Lean proof>` |
| Example clause | `Example: <proposition> Proof: <Lean proof>` |
| Subject | `a simple graph G`, `a natural number n`, `a boolean x`, `an element x of T` |
| Implicit subject | `an implicit natural number n`, `an implicit element x of T` |
| Strict implicit subject | `a strictly implicit natural number n`, `a strictly implicit element x of T` |
| Proof subject | `a proof h that P`, `an implicit proof h that P`, `a strictly implicit proof h that P` |
| Instance subject | `an instance of typeclass C`, `an instance inst of typeclass C` |
| Scalar type | `the type of natural numbers`, `the type of integers` |
| Index type | `the type of indices in [0, n)`, `the type of indices into xs` |
| List type | `the type of lists of Point elements`, `the type of lists of natural numbers` |
| Set type | `the type of sets of Point elements`, `the type of sets of integers` |
| Index subject | `an index i in [0, n)`, `an index i into xs` |
| List subject | `a list T of Tile elements`, `a list xs of natural numbers` |
| Set subject | `a set S of Point elements`, `a set S of integers` |
| Set comprehension | `the set of elements x of T such that <proposition>` |
| Set literal | `the set {x, y}`, `the set ∅` |
| Set image | `the image of S under f` |
| Set complement | `the complement of S` |
| Collection properties | `the length of xs`, `the set of all elements of T` |
| Function subject | `a function f from A to B`, `a function f from A and B to C` |
| Universal quantifier | `for all <bindings> [where <condition>]: <proposition>`, `for every …` |
| Predicate qualifier | `for every function q from ℕ to Prop satisfying CoRE: P`, `for all integers x and y satisfying R: P` |
| Membership quantifier | `for every x ∈ S: <proposition>`, `for all x ∈ S: <proposition>` |
| Superset quantifier | `for every superset S of T: P`, `for every set S ⊇ T: P`, `for all S ⊇ T: P` |
| Almost-everywhere quantifier | `for almost every <witness noun> [with respect to <measure>] [where <condition>]: <proposition>` |
| Quantified bindings | `function q from ℕ to Prop`, `list xs of T elements`, `element x of T`, `u and v in V`, `vertices u and v of G` |
| Existential quantifier | `there is <witness description> [such that <proposition>]` |
| Unique existential | `there is a unique <witness noun> [such that <proposition>]` |
| Bounded existence | `there is x ∈ S such that P`, `there is exactly one x ∈ S such that P`, `there is no x ∈ S such that P` |
| Subset existence | `there is a subset T of S such that P` |
| Negated existential | `there is no <witness noun> [such that <proposition>]` |
| Witness description | `a path p in G from u to v`, `a natural number n`, `a boolean x`, `an element x of T`, `a proof h that P` |
| Properties | `the edge set of G`, `G's edge set` |
| Adjectives | `<term> is <adjective>`, `<term> is not <adjective>` |
| Generic predicates | `x satisfies FooPred`, `x does not satisfy FooPred` |
| Predicate subject lists | `u and v satisfy Adjacent`, `x and y and z satisfy R`, `u and v do not satisfy Adjacent` |
| Relation closure | `x is related to y by the reflexive transitive closure of R` |
| Relation composition | `x is related to z by the composition of R followed by S` |
| Logarithm | `ln x`, `log base b of x` |
| Geometry types | `the real Euclidean space of dimension d`, `the type of bijective affine isometries from A to B over K` |
| Geometry properties | `the linear part of f`, `the determinant of L`, `the perpendicular bisector of p and q`, `the reflection across S` |
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

`there is a unique` means Lean's `∃!`, using the same witness nouns after `unique`:
`there is a unique element t of Point such that P t`. The equivalent spelling
`there is exactly one element t of Point such that P t` is also accepted.
The name is optional; omitting `such that` uses `True` as the condition and still
requires exactly one value of that type. The renderer uses `a unique` for
`ExistsUnique`, including when its predicate is a named function.

`Real` and `Complex` are mathlib types, not floating-point approximations.

Finite sums use `the sum over … of …`, for example:

```text
the sum over indices i in [0, 3) of |p i - q i| = 1
the sum over indices i into xs of xs[i]
the sum over elements x of T of f x
the sum over i in s of f i
```

Index and element domains sum over all values of a type with a `Fintype` instance (`Finset.univ`);
`s` is an explicit `Finset`. The index is bound only in the summand. Arithmetic
following `of` belongs to the summand; comparisons and logical connectives stay
outside it. Write `(the sum over indices i in [0, n) of f i) + 1` to add one to
the completed sum. Parentheses also group summands with lower precedence.

Indexed set unions and intersections use the same index descriptions. For example,
`the union over natural numbers n of S n` means `⋃ n : ℕ, S n`.
In `the union over n in s of S n`, the index ranges over the set `s`.
Write `the union over natural numbers r and s of S r s` for two successive
unions over the same domain. The same form works for two intersections.

Real logarithms use `log base b of x`, meaning `Real.logb b x`:

```lean
log base 2 of (log base 2 of (T.length as a real number + 4))
```

Parentheses delimit compound bases and arguments. Arithmetic outside those
parentheses stays outside the logarithm: `log base 2 of x + y` means
`Real.logb 2 x + y`. The renderer uses this wording inside larger arithmetic
expressions too, while ordinary Lean output retains `Real.logb`.
The natural logarithm `Real.log x` renders as `ln x`, using the abbreviation
`Mean.ln`. Compound arguments are parenthesized, as in `ln (x + 4)` or
`ln (ln x)`. Local functions named `ln` keep their usual Lean meaning; the
renderer retains `Real.log` when a local name would make the abbreviation ambiguous.

Functions can return types:

```lean
the function mapping a natural number d to
  the type of functions from indices in [0, d) to ℤ
```

This means `fun d : Nat => Fin d → Int`, using the ordinary function syntax.
Named aliases are retained inside the resulting type descriptions.

A `satisfying` qualifier applies a predicate directly to the bound subjects:
`for every function q from ℕ to Prop satisfying CoRE: P q` means
`∀ q : ℕ → Prop, CoRE q → P q`. For paired subjects,
`for all integers x and y satisfying R: P x y` uses `R x y`, preserving their
order. The qualifier also works with membership and superset bindings and can
be followed by an additional `where` condition. The renderer uses it for a
generic predicate applied exactly to the subjects being bound. Conditions on
other expressions, quantifiers used as conditions, and registered adjectives
retain `where` wording; the existing `where q satisfies CoRE` form remains valid.

Almost-everywhere quantifiers use the same qualifier: `for almost every element
x of A satisfying P with respect to μ: Q x` means `∀ᵐ x ∂μ, P x → Q x`.
The measure stays μ; the qualifier is an implication inside the almost-everywhere
statement. The measure can be omitted for canonical volume, and the qualifier
may also follow an explicit measure. An additional `where` condition is supported.
A plain `∀ᵐ x, P x` remains an assertion and is not turned into a restriction.

Existential witnesses also accept `satisfying`: `there is an element x of A
satisfying P such that Q x` means `∃ x : A, P x ∧ Q x`.
Omitting `such that` gives `∃ x : A, P x`; an explicit `such that True`
retains the conjunction with `True`. The unique form counts witnesses satisfying
both conditions: `there is a unique element x of A satisfying P such that Q x`
means `∃! x : A, P x ∧ Q x`. Negated existence applies to that whole condition.
Membership and subset witnesses accept the same qualifier, for example
`there is x ∈ S satisfying P` and `there is a subset T of S satisfying R`.
Registered adjectives and conditions on other expressions retain `such that`.

Quantifiers share witness-domain binding, predicate application, and restriction
composition. Universal and almost-everywhere conditions use implication;
existential conditions use conjunction. Their renderers share qualifier recognition
and restriction decomposition; universal and almost-everywhere headers use the
same formatter. Unique and negated existence wrap the same existential condition.

Superset quantifiers range over sets containing a given set:
`for every superset S of T: P S` means `∀ S : Set _, T ⊆ S → P S`.
The symbolic forms `for every set S ⊇ T: P S` and `for every S ⊇ T: P S`
have the same meaning; all forms also accept `for all` and an extra `where`
condition. The renderer prefers the word form when the element type can be
inferred, retaining typed wording when inference or a local subset instance
would change the meaning. Arbitrary order relations are not treated as subsets.

Bounded existential phrases preserve the original conjunction with membership:
`there is x ∈ S such that P x` means `∃ x, x ∈ S ∧ P x`; the unique form means
`∃! x, x ∈ S ∧ P x`, counting only witnesses in S. Negation applies to the
whole bounded existence. `there is a subset T of S such that P T` similarly
means `∃ T, T ⊆ S ∧ P T`. Omit `such that` when the remaining condition is True.
The renderer uses typed witnesses when inference would change their type or
membership instance.

The image phrase uses the function's usual coercion when it is a bijection or
other function-like value. For example, `the image of S under f` means `f '' S`
for an affine isometry f. Geometry phrases retain Mathlib's objects and scalar
field: `the linear part of f` means `f.linear`, and determinants of linear
equivalences retain their units-valued type. `the reflection across S` is
reflection in an affine subspace; it does not require S to be a hyperplane.
Parenthesize compound operands of these phrases.

All forward scalar forms share `scalarType%`: typed values, subjects, existential witnesses,
and singular or plural universal domains. Plurals delegate to the singular noun.
The renderer keeps its independent inverse vocabulary for round-trip checking.
Universal quantifiers accept one or two names, for example `for every real number x:`
and `for all integers x and y:`. Both `for all` and `for every` accept these domains,
including natural numbers and booleans. The renderer uses singular nouns for one
name and plural nouns for two.

Universal quantifiers accept a restriction before the colon:

```lean
for every p ∈ P:
  for every q ∈ P:
    Adjacent p q
```

`for every x ∈ S: …` means Lean's `∀ x ∈ S, …`, inferring the element type
from membership. Sets, lists, finsets, and other membership domains use the same
syntax; compound domains can be parenthesized. Both `for every` and `for all`
also accept `where C` after the domain.

`where C` means `C → …` inside the quantified bindings. The bound names are in
scope in both the condition and body. Both `for every` and `for all` support it,
including paired bindings. Parenthesize a condition containing its own quantifier,
such as `where (for every natural number m: n ≤ m): …`. The renderer uses this
form for an immediate implication whose proof is unused in the conclusion.
When that condition is membership of the bound element, it prefers the shorter
`for every x ∈ S:` wording. Typed bindings remain available when inference
would lose information, or when the membership proof is used in the body.

`for almost every` means Lean's `∀ᵐ`: the condition holds outside a set of
measure zero. It binds one witness noun, including an element, scalar, set, or
function, and renders the body recursively:

```lean
for almost every element x of RealPoint:
  there is a unique element t of RealPoint such that
    t ∈ T and x - t ∈ Solid P
```

The omitted measure is the type's canonical `MeasureTheory.volume`, supplied by
its `MeasureSpace` instance (Lebesgue volume on the real coordinate space here).
Use `with respect to μ` for another measure. An optional `where C` means that
`C → …` holds almost everywhere; it does not change or restrict the measure.
The renderer omits the measure only when it agrees definitionally with the
canonical measure in the current context. Ordinary filter quantifiers keep their
Lean notation.

Single-variable universal quantifiers also accept the existential witness nouns,
without an article: `for every function q from ℕ to Prop: …`,
`for every list xs of T elements: …`, or `for every index i in [0, n): …`.
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
  a simple graph G = (V, E) satisfies preconnected if
    for every u and v in V:
      there is a path in G from u to v.
```

Here `V` is a vertex type and `E` is bound to `G.edgeSet`, not supplied independently.
Neither name needs to appear in the body. Simple graphs are undirected and have no
loops; neither finiteness nor nonemptiness is assumed. The abbreviation `G.V`
exposes mathlib's existing vertex-type parameter without changing its representation.

To extend the forward language, add a subject, domain, or witness description and
its interpretation. A subject implements `functionOn%`, shared by function expressions
and predicate definitions; `predicateOn%` and `predicateOver%` additionally require a proposition body.

Built-in function subjects and quantified witnesses share noun decoding. A universal
domain implements `forallOver%`: its named explicit forall binders become the
subjects of `satisfying`, in order. Arrow premises retain domain restrictions;
the user's body is not inspected for additional subjects. Qualifiers therefore
need no separate domain rule.

A new witness noun implements `existsWitness%`; it does
not require another rule for `there is … such that …`. The corresponding renderer
vocabulary can be extended independently.

## Properties

`the <property> of <term>` and `<name>'s <property>` share `propertyOf%` mappings.
The renderer chooses the first form, including inside equalities, membership,
and other Lean expressions. Complex owners use parentheses, such as
`the edge set of (G ⊔ H)`; the possessive form currently takes an identifier.
Property phrases bind above comparisons but below arithmetic and set operations:
`the vertex type of G is a nonempty type` needs no parentheses, while a union renders as
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
emptiness selects its interpretation from the subject's domain, and `computable`
selects its predicate from the subject's codomain.
The renderer maintains an independent inverse mapping and checks each round trip.

| Adjective | Lean predicate | Subject |
| --- | --- | --- |
| `a nonempty type` | `Nonempty` | Type |
| `an empty type` | `IsEmpty` | Type |
| `a nonempty list` | `xs ≠ []` | List |
| `an empty list` | `xs = []` | List |
| `a nonempty set` | `Set.Nonempty` | Set |
| `an empty set` | `S = ∅` | Set |
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
The short forms `is nonempty` and `is empty` remain accepted for types and lists;
the renderer includes the noun. Explicit nouns check the subject's domain.
List phrases preserve equality or inequality with `[]` directly, including
negation; they do not replace it with an existential or a length comparison.
`finite` asserts finiteness without supplying a `Fintype` enumeration. Set predicates
such as `Set.Finite` are not yet overloaded onto this vocabulary.

An unregistered predicate can use its Lean identifier: if `p : α → Prop`,
`x satisfies p` means `p x`, and `x does not satisfy p` means `¬ p x`.
The existing `x is p` and `x is not p` remain accepted aliases. No `Pred`
suffix or vocabulary registration is required. The application must produce a
proposition; Boolean-valued functions are rejected instead of coerced to propositions.

Two or more subjects use `u and v satisfy Adjacent`, meaning `Adjacent u v`,
or `x and y and z satisfy R`, meaning `R x y z`. Negate the whole application
with `u and v do not satisfy Adjacent`. The existing `are` and `are not` forms
remain aliases. Arguments remain in order, including when their types differ
or later types depend on earlier arguments. A parenthesized predicate expression
also works, such as `u and v satisfy (relation parameter)`.
Agreement follows the number of subjects: a list `xs` is one subject, so
`xs satisfies Sorted` applies `Sorted` to that list. Multiple subjects jointly
satisfy one predicate; the wording does not assert a separate property of each.

The phrase binds at the same precedence as `is`, above logical `and`. Longer
subject lists can also admit an outer-conjunction parse; delimit them inside
a conjunction or disjunction with parentheses:

```lean
P and (u and v satisfy Adjacent)
(u and v satisfy Adjacent) and (x and y and z satisfy R)
p ∈ P and q ∈ P and (p and q satisfy Adjacent)
```

The renderer always adds this grouping inside logical `and` and `or`.
Conjunction and disjunction chains stay inline when their rendered text is single-line
and fits `format.width` (120 by default). Otherwise, the renderer puts a newline after each
logical `and` or `or` in the chain, aligning the clauses. Parentheses retain logical
grouping and quantifier scope; subject lists keep their own `and` inline.

A quantifier at the end of the enclosing expression needs no outer parentheses:
`P and for every natural number n: R n` means `P ∧ ∀ n : Nat, R n`.
The renderer retains parentheses when subsequent text belongs outside that scope,
including a following conjunct or the other side of an equivalence. Dedenting
alone does not close a quantifier's scope.

Parenthesize a logical proposition used as one of the predicate arguments too.
`P and Q and R satisfy r` applies `r` to three propositions; it does not introduce
an outer logical conjunction.

The renderer uses `satisfies/satisfy` for generic named predicates and `is/are`
for registered adjectives such as `finite`, `injective`, and `computable`.
This distinction uses registered declarations rather than guessing from a name's
spelling. Predicate definitions and abbreviations also render with
`satisfies/satisfy`; both the old and new forms are accepted as input. Named-value
and type declarations retain `is`.

Named predicates need trailing explicit subject arguments, preceded by implicit
type or instance arguments. Native relation notation such as `=`, `≤`, `∈`, and
`⊆` is retained. Predicates with implicit parameters interleaved among the
subjects retain Lean application notation. The declared codomain must be `Prop`
with formal type parameters still in place. Specializing a value operation such
as `id`, `iInf`, or a coercion to return propositions does not turn it into a predicate.
Known connectives and quantifiers are rendered before this generic rule. A
quantifier applied to a predicate must keep its quantifier wording; ordinary
predicates on functions can still use satisfaction wording.
Parenthesized predicates are also accepted, such as `n satisfies (relates m)`,
and let the renderer retain explicit hidden arguments when inference would change them.

Relation closures have dedicated wording:

```lean
x is related to y by the reflexive transitive closure of R
```

This means `Relation.ReflTransGen R x y`: a finite sequence of `R` links from
`x` to `y`, including zero links when `x = y`. It preserves direction and does
not assert symmetry. The available closures are:

| Wording | Lean | Meaning |
| --- | --- | --- |
| `the transitive closure of R` | `Relation.TransGen R` | One or more links |
| `the reflexive closure of R` | `Relation.ReflGen R` | One link or equality |
| `the reflexive transitive closure of R` | `Relation.ReflTransGen R` | Zero or more links |
| `the symmetric closure of R` | `Relation.SymmGen R` | One link in either direction |
| `the equivalence closure of R` | `Relation.EqvGen R` | Zero or more links in either direction |

Each closure phrase is itself a relation. `x is related to y by R` applies any
binary relation in that order; use `x is not related to y by …` for negation.
Composition also produces a relation:

```lean
x is related to z by the composition of R followed by S
```

This means `Relation.Comp R S x z`, or `∃ y, R x y ∧ S y z`.
The source, intermediate, and target types may differ.
Compound relation expressions, including nested closures and inline function
phrases, go in parentheses:

```lean
the composition of (the reflexive closure of R) followed by (the symmetric closure of S)
```

The renderer handles these operators before generic predicate subject lists,
and renders nested operators and inline function bodies recursively.

Predicate subjects render recursively, including function bodies:

```lean
(the function mapping an element x of α to
  x does not satisfy p) is recursively enumerable
```

This means `REPred (fun x : α => ¬ p x)`. Parentheses keep the outer adjective
outside the function body. Negated generic predicate applications use
`does not satisfy` or `do not satisfy`; registered adjectives retain `is not`
or `are not`. General negations remain ordinary Lean.

## Current coverage and limitations

The renderer recognizes graph, scalar, index, list, set, function, proof, and generic element
subjects; paired universal quantifiers and single explicit quantifiers over arbitrary
domains; positive and negative existential witnesses; optional
conditions; set comprehensions; finite sums; conjunctions, disjunctions, equivalences, and nondependent propositional implications;
and functions with explicit, implicit, strict implicit, and instance binders, including nested and dependent functions.
Functions also render inside otherwise ordinary Lean applications, constructors,
and type expressions, for example
`List.map (the function mapping a natural number n to n + 1) xs`.
Their bodies use the same logical wording as standalone functions.
Other native binder notation inside the Lean fallback, such as unique existence,
retains its own syntax.
It omits unused witness names and unnecessary generated parameter names, while
preserving public parameter names, including graph carrier parameters.
It substitutes local `let` aliases, so `E` may render as `G.edgeSet`.
Graph carrier types with fixed or compound universes can render through generic
typed-element function bindings; the dedicated graph subject still uses `Type*`.

Unsupported forms remain ordinary Lean, provided that text passes the same
round-trip check. **Identical before/after examples show gaps in rendering
coverage, not failed verification.** Current gaps include:

- Rendering predicates with implicit parameters as subject lists; named values
  retain these through nested function bindings.
- Recursive rendering inside some unsupported outer structures. In particular,
  an outer implicit universal binder can cause a whole theorem statement to remain Lean.
- General negation outside predicate applications and broader mathematical vocabulary.

Some gaps require more Mean syntax; others only require the renderer to translate
supported subexpressions while retaining an ordinary Lean outer structure.

Indentation is currently for readability: **dedenting does not close a scope**.
The grammar determines scope. The renderer removes unnecessary grouping, but some
parentheses remain necessary. For example, `(n = 0).` prevents the final `0.` from
being read as a Lean decimal token. Compound field projections may also need
parentheses. English keywords such as `a`, `graph`, `satisfies`, `satisfy`, `satisfying`, and `does` are reserved after importing
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
