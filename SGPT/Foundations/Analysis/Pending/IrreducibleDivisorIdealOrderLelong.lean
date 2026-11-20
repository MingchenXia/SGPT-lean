import SGPT.Foundations.Analysis.Pending.QuasiPshLelongUpperSemicontinuity
import SGPT.Foundations.Analysis.Pending.FiniteBlowupRegularHypersurfaceIdealOrder
import SGPT.Foundations.Analysis.Pending.PureDimension
import SGPT.Foundations.Analysis.Pending.AnalyticRegularStratumTopology
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback

set_option autoImplicit false

/-! # Actual regular-locus Lelong readers and forward ideal order on finite blowup towers -/

open Set Filter
open scoped Topology ENNReal NNReal Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.IrreducibleDivisorIdealOrderLelong

open FirstPass FirstPass.NonKahlerLocus FirstPass.PositiveClasses
  FirstPass.BlowupSequences FirstPass.IEnvelope DemaillyApproximantDivisorialLelong
  QuasiPshLelongUpperSemicontinuity FiniteBlowupRegularHypersurfaceIdealOrder

noncomputable section

/-- Actual regular density, purity and Lelong upper semicontinuity identify
the literal whole-subvariety reader with its regular-locus reader. -/
theorem iInf_lelongNumber_eq_regularLocus {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {u : Y → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (E : ClosedIrreducibleAnalyticSubvariety n Y) :
    (⨅ x ∈ E.carrier, lelongNumber (n := n) u x) =
      ⨅ x ∈ regularLocus (n := n) E.carrier E.dim, lelongNumber (n := n) u x := by
  have hdense : E.carrier ⊆ closure (regularLocus (n := n) E.carrier E.dim) := by
    intro x hx
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨y, hyU, k, hy⟩ := RegularLocusDense.exists_regularAtDim_mem_nhds E.analytic hx hU
    refine ⟨y, hyU, ?_⟩
    change RegularAtDim (n := n) E.carrier y E.dim
    rwa [PureDimension.eq_dim_of_regularAtDim E hy] at hy
  let L : ℝ≥0∞ := ⨅ x ∈ regularLocus (n := n) E.carrier E.dim, lelongNumber (n := n) u x
  have hclosed : IsClosed ((fun x => lelongNumber (n := n) u x) ⁻¹' Ici L) :=
    (upperSemicontinuous_lelongNumber hu).isClosed_preimage L
  have hreg : regularLocus (n := n) E.carrier E.dim ⊆
      (fun x => lelongNumber (n := n) u x) ⁻¹' Ici L := by
    intro x hx
    change L ≤ lelongNumber (n := n) u x
    exact iInf₂_le x hx
  have hall : E.carrier ⊆ (fun x => lelongNumber (n := n) u x) ⁻¹' Ici L :=
    hdense.trans (closure_minimal hreg hclosed)
  refine le_antisymm ?_ ?_
  · exact le_iInf₂ fun x hx => iInf₂_le x ((regularLocus_subset E.carrier E.dim) hx)
  · exact le_iInf₂ fun x hx => hall hx

universe u

/-- Every actual irreducible codimension-one analytic subvariety on a finite
blowup tower satisfies forward ideal-order comparison, including its singular points. -/
theorem divisorialLelongNumber_comp_le_of_iOrder_irreducible_blowupSequence
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    (omega : KahlerBackground (m + 1) X) (θ : ClosedRealOneOneForm (m + 1) X)
    {u v : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (hI : IOrderOnManifold (n := m + 1) u v)
    {π : Y → X} (hπ : IsBlowupSequence (m + 1) X Y π)
    (E : ClosedIrreducibleAnalyticSubvariety (m + 1) Y) (hEdim : E.dim = m) :
    divisorialLelongNumber m (fun y => v (π y)) E.carrier ≤
      divisorialLelongNumber m (fun y => u (π y)) E.carrier := by
  have huP := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
    hπ.contMDiff hu.1.quasiPlurisubharmonic
  have hvP := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
    hπ.contMDiff hv.1.quasiPlurisubharmonic
  have huReader := iInf_lelongNumber_eq_regularLocus huP E
  have hvReader := iInf_lelongNumber_eq_regularLocus hvP E
  rw [hEdim] at huReader hvReader
  change divisorialLelongNumber m (fun y => u (π y)) E.carrier =
    divisorialLelongNumber m (fun y => u (π y)) (regularLocus (n := m + 1) E.carrier m) at huReader
  change divisorialLelongNumber m (fun y => v (π y)) E.carrier =
    divisorialLelongNumber m (fun y => v (π y)) (regularLocus (n := m + 1) E.carrier m) at hvReader
  rw [huReader, hvReader]
  obtain ⟨O, hO, hEO⟩ :=
    AnalyticRegularStratumTopology.exists_isOpen_inter_eq_regularLocus (n := m + 1) E.carrier m
  have hsub : regularLocus (n := m + 1) E.carrier m ⊆ O := by
    intro x hx
    rw [← hEO] at hx
    exact hx.2
  have hlocal : E.carrier ∩ O = regularLocus (n := m + 1) E.carrier m ∩ O := by
    rw [hEO]
    exact (inter_eq_left.mpr hsub).symm
  apply divisorialLelongNumber_comp_le_of_iOrder_regular_blowupSequence omega θ hu hv hI hπ
  intro x hx
  exact RegularPointDimension.regularAtDim_of_inter_eq hO (hsub hx) hlocal hx

end
end SGPT.Foundations.Analysis.Pending.IrreducibleDivisorIdealOrderLelong
