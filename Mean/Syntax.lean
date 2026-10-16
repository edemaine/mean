import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Countable.Defs
import Lean

/-! # Mean: compositional controlled mathematical syntax inside Lean.

A trailing `%` marks internal helper syntax in Mean. These forms connect the
surface grammar to binding rules and disappear during macro expansion; authors
need not write them. This is a naming convention, not enforced privacy.
-/

/-- Expose the vertex type carried by a mathlib graph's type parameter as `G.V`. -/
abbrev SimpleGraph.V {α : Type*} (_ : SimpleGraph α) := α

namespace Mean

/-! Logical connectives use Lean's usual precedence: `and` binds tighter than
`or`; both associate to the right. An `if … then …` without `else` is implication.
Lean's ordinary `if … then … else …` remains available. -/
syntax:35 term:36 " and " term:35 : term
syntax:30 term:31 " or " term:30 : term
syntax:25 "if" term "then" term:25 : term
macro_rules
  | `($p:term and $q:term) => `(And $p $q)
  | `($p:term or $q:term) => `(Or $p $q)
  | `(if $premise:term then $conclusion:term) =>
      `(∀ (_ : ($premise : Prop)), ($conclusion : Prop))

/-! Adjectives share one application rule. New adjectives implement
`adjectivePredicate%` with their Lean predicate; Lean checks the subject's type. -/
declare_syntax_cat meanAdjective
syntax "nonempty" : meanAdjective
syntax "empty" : meanAdjective
syntax "finite" : meanAdjective
syntax "infinite" : meanAdjective
syntax "countable" : meanAdjective
syntax "injective" : meanAdjective
syntax "surjective" : meanAdjective
syntax "bijective" : meanAdjective
syntax "adjectivePredicate%" meanAdjective : term
syntax:50 term:51 " is " meanAdjective : term
macro_rules
  | `($subject:term is $adjective:meanAdjective) =>
      `((adjectivePredicate% $adjective) $subject)
  | `(adjectivePredicate% nonempty) => `(Nonempty)
  | `(adjectivePredicate% empty) => `(IsEmpty)
  | `(adjectivePredicate% finite) => `(Finite)
  | `(adjectivePredicate% infinite) => `(Infinite)
  | `(adjectivePredicate% countable) => `(Countable)
  | `(adjectivePredicate% injective) => `(Function.Injective)
  | `(adjectivePredicate% surjective) => `(Function.Surjective)
  | `(adjectivePredicate% bijective) => `(Function.Bijective)

/-! Properties share both surface forms; each noun supplies its interpretation.
Lean lexes `G's` as one identifier, so the possessive rule removes that suffix. -/
declare_syntax_cat meanProperty
syntax "edge" "set" : meanProperty
syntax "vertex" "type" : meanProperty
syntax "propertyOf%" meanProperty "of" term:arg : term
-- Bind above comparisons but below arithmetic, so printing groups property operands.
syntax:60 "the " meanProperty " of " term:arg : term
def possessiveOwner : Lean.Parser.Parser :=
  Lean.Parser.identNoAntiquot >> Lean.Parser.checkStackTop
    (fun stx => stx.getId.toString.endsWith "'s") "possessive identifier such as G's"
syntax:max (name := possessiveProperty) possessiveOwner meanProperty : term

/-- Recover the name shared by possessive property and neighbor phrases. -/
private def possessiveName (owner : Lean.Syntax) : Lean.MacroM (Lean.TSyntax `ident) := do
  let .str namePrefix last := owner.getId
    | Lean.Macro.throwErrorAt owner "expected a possessive identifier such as G's"
  unless last.length > 2 do
    Lean.Macro.throwErrorAt owner "expected a name before 's"
  return Lean.mkIdentFrom owner (.str namePrefix (last.dropEnd 2).toString)

@[macro possessiveProperty]
def expandPossessiveProperty : Lean.Macro := fun stx => do
  let owner ← possessiveName stx[0]
  let property : Lean.TSyntax `meanProperty := ⟨stx[1]⟩
  `(propertyOf% $property of $owner:ident)

macro_rules
  | `(the $property:meanProperty of $owner:term) =>
      `(propertyOf% $property of $owner)
  | `(propertyOf% edge set of $g:term) => `(SimpleGraph.edgeSet $g)
  | `(propertyOf% vertex type of $g:term) => `(SimpleGraph.V $g)

/-! Vertex-relative properties share one interpretation per set kind.
Surface variants place the vertex before the ambient graph. -/
declare_syntax_cat meanVertexSet
syntax "neighbor" "set" : meanVertexSet
syntax "incidence" "set" : meanVertexSet
syntax "vertexSetOf%" meanVertexSet "at" term:arg "in" term:arg : term
macro_rules
  | `(vertexSetOf% neighbor set at $v:term in $g:term) => `(SimpleGraph.neighborSet $g $v)
  | `(vertexSetOf% incidence set at $v:term in $g:term) => `(SimpleGraph.incidenceSet $g $v)

declare_syntax_cat meanVertexProperty
syntax meanVertexSet "of" : meanVertexProperty
syntax "set" "of" "neighbors" "of" : meanVertexProperty
syntax "set" "of" "edges" "incident" "to" : meanVertexProperty
syntax "vertexPropertyOf%" meanVertexProperty term:arg "in" term:arg : term
syntax:60 "the " meanVertexProperty ppSpace term:arg " in " term:arg : term
macro_rules
  | `(the $property:meanVertexProperty $v:term in $g:term) =>
      `(vertexPropertyOf% $property $v in $g)
  | `(vertexPropertyOf% $kind:meanVertexSet of $v:term in $g:term) =>
      `(vertexSetOf% $kind at $v in $g)
  | `(vertexPropertyOf% set of neighbors of $v:term in $g:term) =>
      `(vertexSetOf% neighbor set at $v in $g)
  | `(vertexPropertyOf% set of edges incident to $v:term in $g:term) =>
      `(vertexSetOf% incidence set at $v in $g)

syntax:max (name := possessiveVertexSet) possessiveOwner meanVertexSet "in" term:arg : term
@[macro possessiveVertexSet]
def expandPossessiveVertexSet : Lean.Macro := fun stx => do
  let v ← possessiveName stx[0]
  let kind : Lean.TSyntax `meanVertexSet := ⟨stx[1]⟩
  let g : Lean.TSyntax `term := ⟨stx[3]⟩
  `(vertexSetOf% $kind at $v:ident in $g)

syntax:max (name := possessiveNeighbors)
  "the" "set" "of" possessiveOwner "neighbors" "in" term:arg : term
@[macro possessiveNeighbors]
def expandPossessiveNeighbors : Lean.Macro := fun stx => do
  let v ← possessiveName stx[3]
  let g : Lean.TSyntax `term := ⟨stx[6]⟩
  `(vertexSetOf% neighbor set at $v:ident in $g)

/-- Keep the sentence's period out of Lean's field-completion parser. -/
def sentenceBody : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "." Lean.Parser.termParser

/-- Definitions end a subject type at `is`; function lists end it at `and`.
Parentheses disable these delimiters inside a compound type. -/
def subjectType : Lean.Parser.Parser :=
  Lean.Parser.adaptCacheableContext
    (fun ctx => if ctx.forbiddenTks.contains "and" then ctx
      else { ctx with forbiddenTks := #["is"] }) Lean.Parser.termParser

/-- List descriptions end their element type at the explicit plural noun. -/
def listElementType : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "elements" Lean.Parser.termParser

/-- Function domains and results stop before the surrounding phrase's separators.
Parentheses retain ordinary Lean types containing these tokens. -/
def functionDomain : Lean.Parser.Parser :=
  Lean.Parser.withForbiddens #["and", "to"] Lean.Parser.termParser

def functionResult : Lean.Parser.Parser :=
  Lean.Parser.withForbiddens #["and", "to", "is"] Lean.Parser.termParser

declare_syntax_cat meanFunctionSignature
syntax "from" functionDomain ("and" functionDomain)* "to" functionResult : meanFunctionSignature

/-- The signature owns its internal `and`s, even within a function parameter list.
Its result parser restores the delimiter for the next parameter. -/
def functionSignature : Lean.Parser.Parser :=
  Lean.Parser.adaptCacheableContext
    (fun ctx => { ctx with forbiddenTks := ctx.forbiddenTks.filter (· != "and") })
    (Lean.Parser.categoryParser `meanFunctionSignature 0)

syntax "functionType%" functionSignature : term
macro_rules
  | `(functionType% from $domain:term $[and $domains:term]* to $result:term) => do
      let mut result := result
      for domain in domains.reverse do
        result ← `($domain → $result)
      `($domain → $result)

/-! One scalar noun-to-type mapping serves subjects and all quantifiers.
Plural domains delegate to their singular noun through `scalarDomainType%`. -/
declare_syntax_cat meanScalar
syntax "natural" "number" : meanScalar
syntax "integer" : meanScalar
syntax "rational" "number" : meanScalar
syntax "real" "number" : meanScalar
syntax "complex" "number" : meanScalar
syntax "boolean" : meanScalar
syntax "scalarType%" meanScalar : term

macro_rules
  | `(scalarType% natural number) => `(Nat)
  | `(scalarType% integer) => `(Int)
  | `(scalarType% rational number) => `(Rat)
  | `(scalarType% real number) => `(Real)
  | `(scalarType% complex number) => `(Complex)
  | `(scalarType% boolean) => `(Bool)

/-- Treat a bare trailing decimal point as sentence punctuation in a typed
scalar operand. Decimal fractions, exponents, and ordinary Lean terms retain
their normal parsing. The numeral node preserves its original source range. -/
def scalarOperandFn (normalFn : Lean.Parser.ParserFn) : Lean.Parser.ParserFn :=
  fun ctx s =>
    if ctx.forbiddenTks.contains "." && (ctx.get s.pos).isDigit then
      let digits := Lean.Parser.takeDigitsFn Char.isDigit "decimal number" true ctx s
      let following := ctx.get (ctx.next digits.pos)
      if !digits.hasError && ctx.get digits.pos == '.' &&
          !following.isDigit && following != 'e' && following != 'E' && following != '.' then
        Lean.Parser.mkNodeToken Lean.numLitKind s.pos true ctx digits
      else normalFn ctx s
    else normalFn ctx s

-- Preserve Lean's term formatter and parenthesizer for the operand.
def scalarOperand : Lean.Parser.Parser :=
  Lean.Parser.withFn scalarOperandFn (Lean.Parser.termParser Lean.Parser.argPrec)

-- Scalar descriptions annotate values independently of definitions and binders.
syntax:max "the" meanScalar ppSpace scalarOperand : term
syntax:max "the" meanScalar "-" scalarOperand : term
macro_rules
  | `(the $noun:meanScalar $value:term) => `(($value : scalarType% $noun))
  | `(the $noun:meanScalar - $value:term) => `((-$value : scalarType% $noun))

declare_syntax_cat meanScalarDomain
syntax meanScalar : meanScalarDomain
syntax "natural" "numbers" : meanScalarDomain
syntax "integers" : meanScalarDomain
syntax "rational" "numbers" : meanScalarDomain
syntax "real" "numbers" : meanScalarDomain
syntax "complex" "numbers" : meanScalarDomain
syntax "booleans" : meanScalarDomain
syntax "scalarDomainType%" meanScalarDomain : term

macro_rules
  | `(scalarDomainType% $noun:meanScalar) => `(scalarType% $noun)
  | `(scalarDomainType% natural numbers) => `(scalarType% natural number)
  | `(scalarDomainType% integers) => `(scalarType% integer)
  | `(scalarDomainType% rational numbers) => `(scalarType% rational number)
  | `(scalarDomainType% real numbers) => `(scalarType% real number)
  | `(scalarDomainType% complex numbers) => `(scalarType% complex number)
  | `(scalarDomainType% booleans) => `(scalarType% boolean)

/-! Subjects specify bindings, independently of the definition clause.
New subject forms implement `functionOn%`, shared by functions and predicates. -/
declare_syntax_cat meanSubject
syntax "a" "simple" "graph" (ppSpace ident)? : meanSubject
syntax "a" "simple" "graph" (ppSpace ident)? "=" "(" ident "," ident ")" : meanSubject
syntax "an" "element" (ppSpace ident)? "of" subjectType : meanSubject
syntax "a" meanScalar (ppSpace ident)? : meanSubject
syntax "an" meanScalar (ppSpace ident)? : meanSubject
syntax "an" "implicit" meanScalar (ppSpace ident)? : meanSubject
syntax "an" "implicit" "element" (ppSpace ident)? "of" subjectType : meanSubject
syntax "a" "strictly" "implicit" meanScalar (ppSpace ident)? : meanSubject
syntax "a" "strictly" "implicit" "element" (ppSpace ident)? "of" subjectType : meanSubject
syntax "a" "proof" (ppSpace ident)? "that" subjectType : meanSubject
syntax "an" "implicit" "proof" (ppSpace ident)? "that" subjectType : meanSubject
syntax "a" "strictly" "implicit" "proof" (ppSpace ident)? "that" subjectType : meanSubject
syntax "a" "list" (ppSpace ident)? "of" listElementType "elements" : meanSubject
syntax "an" "implicit" "list" (ppSpace ident)? "of" listElementType "elements" : meanSubject
syntax "a" "strictly" "implicit" "list" (ppSpace ident)? "of" listElementType "elements" : meanSubject
syntax "a" "function" (ppSpace ident)? functionSignature : meanSubject
syntax "an" "implicit" "function" (ppSpace ident)? functionSignature : meanSubject
syntax "a" "strictly" "implicit" "function" (ppSpace ident)? functionSignature : meanSubject

syntax "an" "instance" (ppSpace ident)? "of" "typeclass" subjectType : meanSubject

/-- Omitted names are hygienic: they cannot capture references in the user's body. -/
private def parameterName (name : Option (Lean.TSyntax `ident)) : Lean.MacroM (Lean.TSyntax `ident) :=
  match name with
  | some name => pure name
  | none => `(ident| _anonymousParameter)

/-- The word `typeclass` requires a class application, including proposition-valued classes. -/
elab "typeclassType%" t:term : term => do
  let ty ← Lean.Elab.Term.elabType t
  unless (← Lean.Meta.isClass? ty).isSome do
    Lean.throwErrorAt t "expected a typeclass application"
  return ty

/-- Keep binder separators out of an unparenthesized element type. -/
def functionSubject : Lean.Parser.Parser :=
  Lean.Parser.withForbidden "and" (Lean.Parser.categoryParser `meanSubject 0)

-- Internal composition point: subject bindings scoped over a value.
syntax "functionOn%" meanSubject "=>" term : term
syntax "functionOver%" functionSubject ("and" functionSubject)* "=>" term : term
syntax "predicateOn%" meanSubject "=>" term : term
syntax "the" "function" "mapping" functionSubject ("and" functionSubject)* "to" term : term
syntax "the" "function" ":" term "mapping" functionSubject ("and" functionSubject)* "to" term : term

macro_rules
  | `(the function mapping $subject:meanSubject $[and $subjects:meanSubject]* to $body:term) =>
      `(functionOver% $subject $[and $subjects]* => $body)
  | `(the function : $ty:term mapping $subject:meanSubject $[and $subjects:meanSubject]* to $body:term) =>
      `(((functionOver% $subject $[and $subjects]* => $body) : $ty))
  | `(functionOver% $subject:meanSubject $[and $subjects:meanSubject]* => $body:term) => do
      let mut body := body
      for subject in subjects.reverse do
        body ← `(functionOn% $subject => $body)
      `(functionOn% $subject => $body)
  | `(predicateOn% $subject:meanSubject => $body:term) =>
      `(functionOn% $subject => ($body : Prop))
  | `(functionOn% a simple graph $[$g:ident]? => $body:term) => do
      let g ← parameterName g
      `(fun {Vertex : Type*} ($g : SimpleGraph Vertex) => $body)
  | `(functionOn% a simple graph $[$g:ident]? = ($vs:ident, $es:ident) => $body:term) => do
      let g ← parameterName g
      let names := [g.getId, vs.getId, es.getId]
      unless names.eraseDups.length == names.length do
        Lean.Macro.throwErrorAt g
          "the graph, vertex type, and edge set must have distinct names"
      `(fun {$vs : Type*} ($g : SimpleGraph $vs) =>
          let $es := SimpleGraph.edgeSet $g
          $body)
  | `(functionOn% an element $[$x:ident]? of $ty:term => $body:term) => do
      let x ← parameterName x
      `(fun ($x : $ty) => $body)
  | `(functionOn% an implicit element $[$x:ident]? of $ty:term => $body:term) => do
      let x ← parameterName x
      `(fun {$x : $ty} => $body)
  | `(functionOn% an implicit $noun:meanScalar $[$x:ident]? => $body:term) =>
      `(functionOn% an implicit element $[$x:ident]? of (scalarType% $noun) => $body)
  | `(functionOn% a strictly implicit element $[$x:ident]? of $ty:term => $body:term) => do
      let x ← parameterName x
      `(fun ⦃$x : $ty⦄ => $body)
  | `(functionOn% a strictly implicit $noun:meanScalar $[$x:ident]? => $body:term) =>
      `(functionOn% a strictly implicit element $[$x:ident]? of (scalarType% $noun) => $body)
  | `(functionOn% a list $[$x:ident]? of $ty:term elements => $body:term) =>
      `(functionOn% an element $[$x:ident]? of (List $ty) => $body)
  | `(functionOn% an implicit list $[$x:ident]? of $ty:term elements => $body:term) =>
      `(functionOn% an implicit element $[$x:ident]? of (List $ty) => $body)
  | `(functionOn% a strictly implicit list $[$x:ident]? of $ty:term elements => $body:term) =>
      `(functionOn% a strictly implicit element $[$x:ident]? of (List $ty) => $body)
  | `(functionOn% a function $[$x:ident]? $signature:meanFunctionSignature => $body:term) =>
      `(functionOn% an element $[$x:ident]? of (functionType% $signature) => $body)
  | `(functionOn% an implicit function $[$x:ident]? $signature:meanFunctionSignature => $body:term) =>
      `(functionOn% an implicit element $[$x:ident]? of (functionType% $signature) => $body)
  | `(functionOn% a strictly implicit function $[$x:ident]? $signature:meanFunctionSignature => $body:term) =>
      `(functionOn% a strictly implicit element $[$x:ident]? of (functionType% $signature) => $body)
  | `(functionOn% a proof $[$h:ident]? that $p:term => $body:term) =>
      `(functionOn% an element $[$h:ident]? of ($p : Prop) => $body)
  | `(functionOn% an implicit proof $[$h:ident]? that $p:term => $body:term) =>
      `(functionOn% an implicit element $[$h:ident]? of ($p : Prop) => $body)
  | `(functionOn% a strictly implicit proof $[$h:ident]? that $p:term => $body:term) =>
      `(functionOn% a strictly implicit element $[$h:ident]? of ($p : Prop) => $body)
  | `(functionOn% a $noun:meanScalar $[$x:ident]? => $body:term) =>
      `(functionOn% an element $[$x:ident]? of (scalarType% $noun) => $body)
  | `(functionOn% an $noun:meanScalar $[$x:ident]? => $body:term) =>
      `(functionOn% an element $[$x:ident]? of (scalarType% $noun) => $body)

  | `(functionOn% an instance $[$x:ident]? of typeclass $ty:term => $body:term) => do
      let x ← parameterName x
      `(fun [$x : typeclassType% $ty] => $body)

/-! The definition clause knows nothing about graphs or other subject types. -/
syntax "Definition" ":" meanSubject
  "is" ident "if" sentenceBody "." : command
syntax "Definition" ":" ident "is" sentenceBody "." : command
syntax "Abbreviation" ":" meanSubject
  "is" ident "if" sentenceBody "." : command
syntax "Abbreviation" ":" ident "is" sentenceBody "." : command

macro_rules
  | `(command| Definition: $subject:meanSubject
        is $name:ident if $body:term .) =>
      `(command| def $name:ident := predicateOn% $subject => $body)
  | `(command| Definition: $name:ident is $value:term .) =>
      `(command| def $name:ident := $value)
  | `(command| Abbreviation: $subject:meanSubject
        is $name:ident if $body:term .) =>
      `(command| abbrev $name:ident := predicateOn% $subject => $body)
  | `(command| Abbreviation: $name:ident is $value:term .) =>
      `(command| abbrev $name:ident := $value)

/-! Theorem statements reuse ordinary terms, including all Mean propositions.
The separate statement category also supports rendering without a proof. -/
declare_syntax_cat meanTheoremStatement
syntax "Theorem" ident ":" term : meanTheoremStatement
syntax meanTheoremStatement "Proof" ":" term : command

macro_rules
  | `(command| Theorem $name:ident : $statement:term Proof: $proofTerm:term) =>
      `(command| theorem $name:ident : $statement := $proofTerm)

-- Lemmas share theorem semantics; examples use Lean's anonymous declaration form.
macro "Lemma" name:ident ":" statement:term "Proof" ":" proofTerm:term : command =>
  `(command| Theorem $name:ident : $statement Proof: $proofTerm)

macro "Example" ":" statement:term "Proof" ":" proofTerm:term : command =>
  `(command| example : $statement := $proofTerm)

/-! Quantified bindings are independent of both the definition and its subject.
New domains implement `forallOver%`, shared by `for all` and `for every`. -/
declare_syntax_cat meanQuantified
syntax meanScalarDomain ident ("and" ident)? : meanQuantified
syntax ident "and" ident "in" term : meanQuantified
syntax "vertices" ident "and" ident "of" term : meanQuantified
syntax "forallOver%" meanQuantified "=>" term : term
syntax "for" "every" meanQuantified ":" term : term
syntax "for" "all" meanQuantified ":" term : term

macro_rules
  | `(for every $binding:meanQuantified : $body:term) =>
      `(forallOver% $binding => $body)
  | `(for all $binding:meanQuantified : $body:term) =>
      `(forallOver% $binding => $body)
  | `(forallOver% $domain:meanScalarDomain $x:ident $[and $y:ident]? => $body:term) => do
      match y with
      | some y => `(∀ ($x : scalarDomainType% $domain) ($y : scalarDomainType% $domain), $body)
      | none => `(∀ ($x : scalarDomainType% $domain), $body)
  | `(forallOver% $u:ident and $v:ident in $ty:term => $body:term) =>
      `(∀ ($u : $ty) ($v : $ty), $body)
  | `(forallOver% vertices $u:ident and $v:ident of $g:term => $body:term) =>
      `(forallOver% $u:ident and $v:ident in SimpleGraph.V $g => $body)

/-! Existential quantification is independent of its witness description.
New noun phrases implement `existsWitness%`; `existsOver%` handles articles.
Positive and negative existence share the noun and optional condition. -/
declare_syntax_cat meanWitnessNoun
syntax "element" (ppSpace ident)? "of" term : meanWitnessNoun
syntax "proof" (ppSpace ident)? "that" term : meanWitnessNoun
syntax meanScalar (ppSpace ident)? : meanWitnessNoun
syntax "path" (ppSpace ident)? "in" term "from" term "to" term : meanWitnessNoun
syntax "list" (ppSpace ident)? "of" listElementType "elements" : meanWitnessNoun
syntax "function" (ppSpace ident)? functionSignature : meanWitnessNoun
syntax "instance" (ppSpace ident)? "of" "typeclass" term : meanWitnessNoun

declare_syntax_cat meanWitness
syntax "a" meanWitnessNoun : meanWitness
syntax "an" meanWitnessNoun : meanWitness

syntax "existsWitness%" meanWitnessNoun "=>" term : term
syntax "existsOver%" meanWitness "=>" term : term
syntax "there" "is" "no" meanWitnessNoun ("such" "that" term)? : term
syntax "there" "is" meanWitness ("such" "that" term)? : term

macro_rules
  | `(there is no $description:meanWitnessNoun
        $[such that $condition:term]?) => do
      let condition ← match condition with
        | some body => pure body
        | none => `(True)
      `(¬ (existsWitness% $description => $condition))
  | `(existsOver% a $description:meanWitnessNoun => $body:term) =>
      `(existsWitness% $description => $body)
  | `(existsOver% an $description:meanWitnessNoun => $body:term) =>
      `(existsWitness% $description => $body)
  | `(there is $description:meanWitness
        $[such that $condition:term]?) => do
      let condition ← match condition with
        | some body => pure body
        | none => `(True)
      `(existsOver% $description => $condition)
  | `(existsWitness% element $[$x:ident]? of $ty:term => $body:term) => do
      let witness ← match x with
        | some name => pure name
        | none => `(ident| existentialWitness)
      `(∃ ($witness:ident : $ty), $body)
  | `(existsWitness% $noun:meanScalar $[$x:ident]? => $body:term) =>
      `(existsOver% an element $[$x:ident]? of (scalarType% $noun) => $body)
  | `(existsWitness% proof $[$h:ident]? that $p:term => $body:term) =>
      `(existsWitness% element $[$h:ident]? of ($p : Prop) => $body)
  | `(existsWitness% list $[$x:ident]? of $ty:term elements => $body:term) =>
      `(existsWitness% element $[$x:ident]? of (List $ty) => $body)
  | `(existsWitness% function $[$x:ident]? $signature:meanFunctionSignature => $body:term) =>
      `(existsWitness% element $[$x:ident]? of (functionType% $signature) => $body)
  | `(existsWitness% instance $[$x:ident]? of typeclass $ty:term => $body:term) =>
      `(existsWitness% element $[$x:ident]? of (typeclassType% $ty) => $body)
  | `(existsWitness% path $[$p:ident]? in $g:term from $u:term to $v:term
        => $body:term) =>
      `(existsOver% an element $[$p:ident]? of SimpleGraph.Path $g $u $v => $body)

/-- Neither `V` nor `E` needs to occur in the definition body.
`V` already occurs in the generated type `G : SimpleGraph V`, so only `E`
needs an unused-variable exemption. Keep all other diagnostics. -/
@[unused_variables_ignore_fn]
def ignoreUnusedEdgeSet : Lean.Linter.IgnoreFunction := fun binder stack _ =>
  stack.any fun (parent, _) =>
    match parent with
    | `(meanSubject| a simple graph $[$_:ident]? = ($_:ident, $es:ident)) =>
        binder.getRange? == es.raw.getRange?
    | _ => false

end Mean
