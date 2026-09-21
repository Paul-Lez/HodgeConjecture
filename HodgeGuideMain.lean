/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HodgeGuide
import VersoManual

open Verso.Genre Manual
open Verso.Output.Html

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1
  extraCss := {CSS.mk (HodgeGuide.wipCss ++ "
.content-wrapper {
  display: flex;
  flex-direction: column;
}
.fc-wip-global {
  order: -1;
  width: 100%;
  box-sizing: border-box;
}
")}
  extraContents := #[{{
    <div class="fc-wip fc-wip-global" role="note">
      <p>"This guide is currently work in progress."</p>
    </div>
  }}]

def main := manualMain (%doc HodgeGuide) (config := config)
