import SGPT.Foundations.Analysis.Pending.HironakaG8BFamilyClassStep
import SGPT.Foundations.Analysis.Pending.HironakaG8BFamilyTangent
import SGPT.Foundations.Analysis.Pending.HironakaG11InvBMPadInv

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Plan module 6 for lower invariants with per-sequence local finiteness (the input `TangentIndepStepBM` of the induction)

Blueprint: `hironaka-g8b-family-tangent.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6d (module 12 applies
module 6 to the padded lower invariants `padInvSeq R m`, structure `ResolutionInvariantSeq.ResolutionInvariant`).

`HironakaG8BFamilyTangent.tangentIndepBM_of_classFunctorial_of_expAgreeSucc` is stated for the structure
`ResolutionInvariantExt.ResolutionInvariant`; its proof uses only `R.inv` and the `HironakaG8ClassStep.inv_eq_on_inter`, so
`transport_ext_to_seq_module` (reusing the copies of `HironakaG8BFamilySeq` and `HironakaG8BFamilyClassStep`) gives a
kernel-checked copy for `ResolutionInvariantSeq.ResolutionInvariant` (namespace `SGPT.Foundations.Analysis.Pending.Seq`):

* **`tangentIndepStepBM_of_expAgreeSucc`**: `TangentExpAgreeSuccBM n k → HironakaG8BFamily.TangentIndepStepBM n k` — the
  module-6 input of the induction (`HironakaG8BFamily.StepInputsBM.tangentIndep`) from the single `R`-free input at the levels
  `≥ 1` of the lower ideals;
* `tangentIndepBM_padInvSeq`: the instance for the padded lower invariants `padInvSeq R m` of the decided family (lane G11B's
  `HironakaG11InvBMPadInv`), in the shape of the hypothesis `hTI` of plan module 8 (`isMaxOrderValue_stepOneInvBM_pad`).

Sorry-free.  Import discipline (Hironaka phase): no import of `Pending.RelativePrincipalization` or
`Pending.EmbeddedResolution`.
-/

open SGPT.Foundations.Analysis.Pending.ExtSeqTransport

/-! ### The transport of plan module 6 -/

transport_ext_to_seq_module SGPT.Foundations.Analysis.Pending.HironakaG8BFamilyTangent

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.HironakaG8BFamilyTangentSeq

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.MarkedIdeals SGPT.Foundations.Analysis.Pending.MarkedIdeals.MarkedIdeal
  SGPT.Foundations.Analysis.Pending.BlowupTowers SGPT.Foundations.Analysis.Pending.ResolutionInvariantSeq
open SGPT.Foundations.Analysis.Pending.ResolutionInvariantSpec (IsInvDomain)
open SGPT.Foundations.Analysis.Pending.HomogenizedIdealAlong (IsMaximalOrderAlong)
open SGPT.Foundations.Analysis.Pending.HironakaG8LocalHistory (LocWPEquiv)
open SGPT.Foundations.Analysis.Pending.HironakaG11InvBMClass (ClassFunctorialFor)
open SGPT.Foundations.Analysis.Pending.HironakaG8BFamilyTangent (TangentExpAgreeSuccBM)

noncomputable section

variable {n : ℕ}

/-- **The module-6 input of the induction from the boundary exponents of the lower ideals of levels `≥ 1`**: plan module 6 for
every lower invariant of the structure `ResolutionInvariantSeq.ResolutionInvariant` (the statement
`HironakaG8BFamily.TangentIndepStepBM n k`). -/
theorem tangentIndepStepBM_of_expAgreeSucc {k : ℕ} (hsucc : TangentExpAgreeSuccBM n k) :
    HironakaG8BFamily.TangentIndepStepBM n k :=
  fun hn R hR _ 𝔍 h hmax =>
    Seq.HironakaG8BFamilyTangent.tangentIndepBM_of_classFunctorial_of_expAgreeSucc hsucc hn R hR 𝔍 h hmax

/-- **Plan module 6 for the padded lower invariants** (the decided family, BPRIME-PLAN §6d): for a lower invariant `R`
class functorial for `LocWPEquiv`, every padded invariant `padInvSeq R m` has the independence of the hypersurface of maximal
contact on every marked ideal of the domain of maximal order — in particular with `m = |𝔍.E|`, the hypothesis `hTI` of
`HironakaG11PresM8Assembly.isMaxOrderValue_stepOneInvBM_pad` (transported) for `Rm := padInvSeq R`. -/
theorem tangentIndepBM_padInvSeq {k : ℕ} (hsucc : TangentExpAgreeSuccBM n k) (hn : 0 < n) {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariant.{0, 0} n (k - 1) Λ)
    (hR : ClassFunctorialFor (fun {Y} A B => LocWPEquiv (X := Y) A B) (k - 1) R.inv) (m : ℕ) {X : CMfd.{0} n}
    (𝔍 : MarkedIdeal n X) (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) :
    Seq.HironakaG11InvBMTangentIndep.TangentIndepBM (k := k) 𝔍 (HironakaG11InvBMPadInv.padInvSeq R m) :=
  tangentIndepStepBM_of_expAgreeSucc hsucc hn _ (HironakaG11InvBMPadInv.classFunctorial_padInv R m hR) 𝔍 h hmax

end

end SGPT.Foundations.Analysis.Pending.HironakaG8BFamilyTangentSeq
