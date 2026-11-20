import SGPT.Foundations.Analysis.Pending.RawPshACTruncationDomination
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler
import SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
import SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame

set_option autoImplicit false

/-! Actual patch AC finiteness from the internally supplied raw reader and
true compact Kähler NP truncation-mass producer. Complete BP math/proof
precede Lean. No input approximation, finite bound or class cert. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.ThetaPshPatchACFinite
open FirstPass FirstPass.GlobalPotentialPatches LocalProductCurrents LocalBedfordTaylorProducts
  ScalarLeviPositiveCurrent PositiveCurrentACTopMeasure RawPshACTruncationDomination
  GlobalCurrentPotentials CanonicalCurrentFrame FirstPass.PositiveClasses

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]

/-- Genuine σ-PSH and any actual potential patch internally supply the raw
L1 reader, SAME positive current and finite AC on ALL interior compact sets. -/
theorem exists_patch_ac_domination_and_finite
    (omega : KahlerBackground (m+1) M) (σ : ClosedRealOneOneForm (m+1) M)
    {u : M → EReal} (hu : IsThetaPshPotential σ.val u)
    (P : Patch (fun _ : Fin (m+1) => σ) (fun _ => u)) :
    ∃ hL : LocallyIntegrableOn (fun z => (P.corrected 0 z).toReal) P.domain volume,
    ∃ hT : IsPositive (ddc (scalarTopCurrent (regularDistribution volume
      (fun z => (P.corrected 0 z).toReal) hL))),
      acTopMeasure hT ≤ MongeAmpere.truncationLimitMeasure P.domain (P.corrected 0)
        (P.plurisubharmonic 0) ∧
      ∀ K : Set (ComplexModel (m+1)), IsCompact K → K ⊆ P.domain → acTopMeasure hT K < ⊤ := by
  classical
  have hraw : ∀ᵐ z ∂volume.restrict P.domain,
      chartFunction u P.chart z ≠ ⊤ ∧ chartFunction u P.chart z ≠ ⊥ := by
    have h := quasiPsh_chart_ae_finite (canonicalBasis (m+1)) (Nat.succ_pos m)
      u hu.quasiPshPotential P.chart
    rw [addHaar_canonicalBasis] at h
    exact h.filter_mono (ae_mono (Measure.restrict_mono_set volume P.domain_le_target))
  have hfin : ∀ᵐ z ∂volume.restrict P.domain,
      P.corrected 0 z ≠ ⊤ ∧ P.corrected 0 z ≠ ⊥ := by
    filter_upwards [hraw] with z hz
    have hc := EReal.coe_toReal hz.1 hz.2
    change chartFunction u P.chart z + (P.potential 0 z : EReal) ≠ ⊤ ∧
      chartFunction u P.chart z + (P.potential 0 z : EReal) ≠ ⊥
    rw [← hc, ← EReal.coe_add]
    exact ⟨EReal.coe_ne_top _,EReal.coe_ne_bot _⟩
  have hcorr : (fun z => (chartFunction u P.chart z).toReal + P.potential 0 z)
      =ᵐ[volume.restrict P.domain] fun z => (P.corrected 0 z).toReal := by
    filter_upwards [hraw] with z hz
    dsimp only [Patch.corrected]
    rw [EReal.toReal_add hz.1 hz.2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  have hL : LocallyIntegrableOn (fun z => (P.corrected 0 z).toReal) P.domain volume :=
    (((hu.quasiPshPotential.locallyIntegrableOn_chart_toReal P.chart).mono_set P.domain_le_target).add
      ((P.localPotential 0).2.2.1.continuousOn.locallyIntegrableOn
        P.domain.isOpen.measurableSet)).congr hcorr
  obtain ⟨hT, _hstep, hle⟩ :=
    acTopMeasure_le_truncationLimitMeasure (P.plurisubharmonic 0) hfin hL
  refine ⟨hL,hT,hle,?_⟩
  let Q : Patch (fun _ : Fin (m+1) => σ) (fun _ => u) := {
    chart := P.chart
    domain := P.domain
    domain_le_target := P.domain_le_target
    potential := fun _ => P.potential 0
    localPotential := fun _ => P.localPotential 0
    plurisubharmonic := fun _ => P.plurisubharmonic 0 }
  have hdiag : MixedNonPluripolar.mixedTruncationLimitMeasure
      Q.domain Q.corrected Q.plurisubharmonic =
      MongeAmpere.truncationLimitMeasure P.domain (P.corrected 0) (P.plurisubharmonic 0) :=
    MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal (Nat.succ_pos m) (P.plurisubharmonic 0)
  intro K hK hKP
  have hnp := GlobalNonPluripolar.patch_coordinateMeasure_finiteOnCompacts
    omega (fun _ : Fin (m+1) => hu.1) Q hK hKP
  rw [hdiag] at hnp
  exact (lt_of_le_of_lt (Measure.le_iff'.mp hle K) hnp)

end SGPT.Foundations.Analysis.Pending.ThetaPshPatchACFinite
