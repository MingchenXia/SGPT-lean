import SGPT.Trace.OTMarginExistence
import SGPT.Trace.OTExtGlobal

/-!
# `thm:OT_ext_global` is proved

Blueprint `claude-ot3.tex`, node `claude-ot3:OT-ext-global`.

`otExtGlobalStatement`: the global Ohsawa--Takegoshi extension theorem for the trace operator
(`thm:OT_ext_global`, `chapter_trace.tex` 527--532), unconditionally: the book's reduction
(`otExtGlobalStatement_of_marginExistence`, lane OT2) applied to the margin existence part of
`thm:OT_ext` (`otExtMarginExistenceStatement`, this lane).
-/

set_option autoImplicit false

namespace SGPT.Trace.OTMargin

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Trace.OTExt

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

variable (n X) in
/-- **`thm:OT_ext_global`** (Xia, *Singularities in global pluripotential theory*,
`chapter_trace.tex` 527--532), for all data. -/
theorem otExtGlobalStatement : OTExtGlobalStatement n X :=
  otExtGlobalStatement_of_marginExistence otExtMarginExistenceStatement

end SGPT.Trace.OTMargin
