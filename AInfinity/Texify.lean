module

public import Lean
public import ProofWidgets

public section

open Lean Elab Command Widget ProofWidgets
open ProofWidgets.Jsx

universe u

class Texify (α : Type u) where
  texify : α → String

meta def texifyToHtml {α : Type u} [Texify α] (a : α) : ProofWidgets.Html :=
  let md := s!"$${Texify.texify a}$$";
  <MarkdownDisplay contents={md} />

-- Based on https://github.com/kmill/LeanTeX/blob/d66db4582b6cb4d9fa0b6309168103a248a5fd46/LeanTeX/Widget.lean#L9
meta def displayHtml (html : ProofWidgets.Html) (stx : Syntax) : CoreM Unit := do
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

meta unsafe def evalHtmlUnsafe (stx : Term) : TermElabM Html := do
  let newStx ← `(texifyToHtml $stx)
  Term.evalTerm _ (mkConst ``Html) newStx

/--
Evaluates a term of type `ProofWidgets.Html`
-/
@[implemented_by evalHtmlUnsafe]
meta opaque evalHtml : Term → TermElabM Html

elab tk:"#texify" t:term : command => do
  let term ← liftTermElabM <| evalHtml t
  liftCoreM <| displayHtml term tk

instance : Texify Nat where
  texify n := s!"{n}"

instance : Texify Int where
  texify n := s!"{n}"
