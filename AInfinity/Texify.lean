module

public import Lean
public import ProofWidgets

public section

open Lean Elab Command Widget ProofWidgets
open ProofWidgets.Jsx

universe u

class Texify (α : Type u) where
  protected texify : α → String

def texify {α : Type u} [Texify α] : α → String := Texify.texify

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
