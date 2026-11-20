import SGPT.Foundations.Analysis.Pending.ActualChartCapacityNegativeWell
import SGPT.Foundations.Analysis.Pending.ThetaPshCollarGluing
import SGPT.Foundations.Analysis.Pending.OpensRestriction
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacity

set_option autoImplicit false

/-! # Actual globalization of bounded local capacity competitors

An independent negative-well and genuine collar-gluing construction.
The capacity comparison and unbounded mixed weak lower semicontinuity
remain separate consumers. All dimensions and the empty compact are kept.
-/

open Set Filter TopologicalSpace
open scoped Topology ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.ActualChartCapacityCompetitor

open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  FirstPass.AnalyticGluingData FirstPass.LocalPotentialPullback
  BedfordTaylor QuasiEquisingularCollarGluing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- One geometric scale and open core globalize every actual local capacity
competitor; the smooth local potential is natural chart geometry. -/
theorem exists_global_capacity_competitor (omega : KahlerBackground n M)
    (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential omega.form.val e D ρ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ δ : ℝ, 0 < δ ∧ 3 * δ ≤ 1 ∧ ∃ O : Set M,
      IsOpen O ∧ e.val.symm '' K ⊆ O ∧
      O ⊆ e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n)) ∧
      ∀ (f : ComplexModel n → ℝ), FirstPass.MongeAmpere.IsLocallyBoundedPshOn D f →
        (∀ z ∈ D, -1 ≤ f z ∧ f z ≤ 0) →
        ∃ v : M → EReal, IsThetaPshPotential omega.form.val v ∧
          (∀ x, (-1 : EReal) ≤ v x ∧ v x ≤ 0) ∧
          ∀ x ∈ O, v x = ((δ * f (e.val x) - δ : ℝ) : EReal) := by
  obtain ⟨δ, hδ, h3δ, χ, hχ, hχ01, hχsupp, hχK, hψ, hψ01⟩ :=
    ActualChartCapacityNegativeWell.exists_chart_negative_well omega e hDt hK hKD
  let U : Set M := e.val.source ∩ e.val ⁻¹' (D : Set (ComplexModel n))
  let O : Set M := U ∩ {x | (2 / 3 : ℝ) < χ x}
  have hU : IsOpen U := e.val.continuousOn.isOpen_inter_preimage e.val.open_source D.isOpen
  have hO : IsOpen O := hU.inter
    (isOpen_lt continuous_const (ProductTestForms.ChartSmooth.continuous hχ))
  have hKO : e.val.symm '' K ⊆ O := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨⟨e.val.map_target (hDt (hKD hz)), ?_⟩, ?_⟩
    · change e.val (e.val.symm z) ∈ (D : Set (ComplexModel n))
      rw [e.val.right_inv (hDt (hKD hz))]
      exact hKD hz
    · change (2 / 3 : ℝ) < χ (e.val.symm z)
      rw [hχK z hz]
      norm_num
  refine ⟨δ, hδ, h3δ, O, hO, hKO, inter_subset_left, fun f hf hb => ?_⟩
  let a : M → EReal := fun x => ((δ * f (e.val x) - δ : ℝ) : EReal)
  let ψ : M → EReal := fun x => ((-3 * δ * χ x : ℝ) : EReal)
  have hzero := (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have hρpsh : PlurisubharmonicOn (fun z => (ρ z : EReal)) (D : Set (ComplexModel n)) := by
    simpa [chartFunction] using
      BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn hzero.1 e hρ
  have hcorr : PlurisubharmonicOn (fun z => ((δ * f z - δ + ρ z : ℝ) : EReal))
      (D : Set (ComplexModel n)) := by
    have hh := ((hf.1.const_mul hδ).add_const (-δ)).add hρpsh
    simpa only [← EReal.coe_mul, ← EReal.coe_add, sub_eq_add_neg] using hh
  have haps : PlurisubharmonicOn (fun z => chartFunction a e z + (ρ z : EReal))
      (D : Set (ComplexModel n)) := by
    apply plurisubharmonicOn_congr D.isOpen hcorr
    intro z hz
    dsimp only [chartFunction, a]
    rw [e.val.right_inv (hDt hz), ← EReal.coe_add]
  have ha : ThetaPlurisubharmonicOn omega.form.val a U := by
    intro e' z hz hx
    have hxe' : e'.val.symm z ∈ e'.val.source := e'.val.map_target hz
    obtain ⟨W, r, hzW, hr, hp⟩ := OpensRestriction.exists_witness_of_chart
      e' e hxe' hx.1 hx.2 hρ haps
    rw [e'.val.right_inv hz] at hzW
    exact ⟨W, r, hzW, hr, hp⟩
  have hclosure : closure (tsupport χ) ⊆ U := by
    rw [(isClosed_tsupport χ).closure_eq]
    exact hχsupp
  have hcollar : ∀ x ∈ U \ tsupport χ, a x ≤ ψ x := by
    intro x hx
    have hx0 : χ x = 0 := by
      by_contra hne
      exact hx.2 (subset_tsupport χ hne)
    dsimp only [a, ψ]
    rw [hx0]
    apply EReal.coe_le_coe_iff.mpr
    have hh := hb (e.val x) hx.1.2
    nlinarith
  let v : M → EReal := gluedMax U a ψ
  have hv : IsThetaPshPotential omega.form.val v :=
    isThetaPshPotential_gluedMax hU hclosure hcollar ha hψ
  refine ⟨v, hv, fun x => ?_, fun x hx => ?_⟩
  · by_cases hx : x ∈ U
    · change (-1 : EReal) ≤ gluedMax U a ψ x ∧ gluedMax U a ψ x ≤ 0
      rw [gluedMax_eq_max hx]
      have ha0 : a x ≤ 0 := by
        dsimp only [a]
        change _ ≤ ((0 : ℝ) : EReal)
        apply EReal.coe_le_coe_iff.mpr
        have hh := hb (e.val x) hx.2
        nlinarith
      exact ⟨(hψ01 x).1.trans (le_max_right _ _), max_le ha0 (hψ01 x).2⟩
    · change (-1 : EReal) ≤ gluedMax U a ψ x ∧ gluedMax U a ψ x ≤ 0
      simp only [gluedMax, if_neg hx]
      exact hψ01 x
  · change gluedMax U a ψ x = _
    rw [gluedMax_eq_max hx.1]
    apply max_eq_left
    dsimp only [a, ψ]
    apply EReal.coe_le_coe_iff.mpr
    have hh := hb (e.val x) hx.1.2
    have hχx : (2 / 3 : ℝ) < χ x := hx.2
    nlinarith

end
end SGPT.Foundations.Analysis.Pending.ActualChartCapacityCompetitor
