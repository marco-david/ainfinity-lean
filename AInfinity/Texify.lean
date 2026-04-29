module

public import Lean
public import ProofWidgets
public import Lean.Compiler.Options

public section

open Lean Elab Command Widget ProofWidgets
open ProofWidgets.Jsx

universe u

class Texify (α : Type u) where
  protected texify : α → String
  /-- If further constructions that make use of this should add parentheses around it -/
  protected requiresParentheses : Bool := false

def texify {α : Type u} [Texify α] : α → String := Texify.texify

def texifyWithBrackets {α : Type u} [Texify α] (x : α) := s!"\{{texify x}}"

def texifyWithBracketsAndParenthesesIfNecessary {α : Type u} [Texify α] (x : α) :=
  if Texify.requiresParentheses α then
    s!"\{\\left({texify x}\\right)}"
  else
    s!"\{{texify x}}"

def texifyToMd {α : Type u} [Texify α] (a : α) : String :=
  s!"$${texify a}$$"

-- Based on https://github.com/kmill/LeanTeX/blob/d66db4582b6cb4d9fa0b6309168103a248a5fd46/LeanTeX/Widget.lean#L9
meta def displayMd (md : String) (stx : Syntax) : CoreM Unit := do
  let html := <MarkdownDisplay contents={md} />
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

meta unsafe def evalStringUnsafe (stx : Term) : TermElabM String := do
  let newStx ← `(texifyToMd $stx)
  /-
  Without these options, we would get weird errors like
  ```
  Invalid `meta` definition `_tmp✝`, `SimplexCategory.mk` is not accessible here;
  consider adding `public meta import Mathlib.AlgebraicTopology.SimplexCategory.Defs`
  ```
  These options are a solution suggested by Robin Arnez:
  https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/SimplexCategory.2Emk.20.2B.20module.20system.20breaks.20evalTerm/near/591707795
  -/
  withOptions (fun opts =>
    if Elab.inServer.get opts then
      Compiler.compiler.checkMeta.set opts false
    else
      Compiler.compiler.relaxedMetaCheck.set opts true) do
  withOptions (Compiler.compiler.postponeCompile.set · false) do
    Term.evalTerm _ (mkConst ``String) newStx

/--
Evaluates a term of type `ProofWidgets.Html`
-/
@[implemented_by evalStringUnsafe]
meta opaque evalString : Term → TermElabM String

elab tk:"#texify" t:term : command => do
  let term ← liftTermElabM <| evalString t
  liftCoreM <| displayMd term tk

instance : Texify Nat where
  texify n := s!"{n}"

instance : Texify Int where
  texify n := s!"{n}"
