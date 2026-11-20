import SGPT.Foundations.Analysis.Pending.SingularRealCutoffLocalLone
import SGPT.Foundations.Analysis.Pending.SubgeodesicChartPotential
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicAffineTranslation

set_option autoImplicit false

/-! # The genuine maximum cutoff subgeodesic and its actual Perron barrier -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularCutoffSubgeodesicBarrier

open FirstPass SingularModelNormalizedMixedCutoff SingularRealCutoffLocalLone

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- One actual common smooth local potential and genuine joint PSH maximum closure internally produce the full interior subgeodesic maximum witness. -/
theorem isSubgeodesicInterior_max {θ : SmoothRealForm n M 2}
    {U V : ℝ → M → EReal} (hU : IsSubgeodesicInterior θ U)
    (hV : IsSubgeodesicInterior θ V) :
    IsSubgeodesicInterior θ (fun t x => max (U t x) (V t x)) := by
  constructor
  · intro t ht
    exact IsThetaPshPotential.max (hU.thetaPshPotential ht) (hV.thetaPshPotential ht)
  · intro e z hz
    obtain ⟨W, ρ, hzW, hρ, hpshU⟩ := hU.complexified_psh e hz
    have hpshV := SubgeodesicChartPotential.plurisubharmonicOn_subgeodesicChartFunction hV e hρ
    refine ⟨W, ρ, hzW, hρ, ?_⟩
    convert hpshU.max hpshV using 2 with p
    exact (max_add_add_right _ _ _).symm

/-- The actual real cutoff at affine time is a genuine endpoint subgeodesic; its joint PSH and both actual chart local L1 endpoint limits are produced internally. -/
theorem isSubgeodesicFrom_realCutoff_time {θ : ClosedRealOneOneForm n M}
    {φ u : M → EReal} (hp : IsThetaPshPotential θ.val φ)
    (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ) (C : ℝ) :
    IsSubgeodesicFrom θ.val (fun t => realCutoff φ u (C * t)) φ (realCutoff φ u C) := by
  have hdown : IsSubgeodesicInterior θ.val (fun t x => φ x - ((C * t : ℝ) : EReal)) := by
    have h := (isSubgeodesicInterior_const hp).affineTranslated (-C) 0
    have heq : affineTranslatedCurve (fun _ : ℝ => φ) (-C) 0 =
        fun t x => φ x - ((C * t : ℝ) : EReal) := by
      funext t x
      rw [affineTranslatedCurve_apply]
      simp only [add_zero, neg_mul, EReal.coe_neg, sub_eq_add_neg]
    rw [heq] at h
    exact h
  have hinterior : IsSubgeodesicInterior θ.val (fun t => realCutoff φ u (C * t)) :=
    isSubgeodesicInterior_max (isSubgeodesicInterior_const hu) hdown
  have hzero : realCutoff φ u 0 = φ := by
    funext x
    simp only [realCutoff, EReal.coe_zero, sub_zero, max_eq_right (hup x)]
  have hc0 : Tendsto (fun t : ℝ => C * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => C * t) := by fun_prop
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa only [mul_zero] using hcont.tendsto 0
  have hc1 : Tendsto (fun t : ℝ => C * t) (𝓝[<] (1 : ℝ)) (𝓝 C) := by
    have hcont : Continuous (fun t : ℝ => C * t) := by fun_prop
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa only [mul_one] using hcont.tendsto 1
  have hpTop : ∀ x, φ x ≠ ⊤ := hp.1.quasiPlurisubharmonic.ne_top
  have huTop : ∀ x, u x ≠ ⊤ := hu.1.quasiPlurisubharmonic.ne_top
  have hleft := manifoldL1LocallyTendsto_realCutoff (n := n) hpTop huTop hc0
  rw [hzero] at hleft
  exact ⟨hp, IsThetaPshPotential.max hu (hp.sub_const C), hinterior, hleft,
    manifoldL1LocallyTendsto_realCutoff (n := n) hpTop huTop hc1⟩

/-- The internally constructed genuine cutoff subgeodesic belongs to the actual Perron competitor family and gives its actual pointwise slice lower barrier. -/
theorem realCutoff_time_le_finiteGeodesic {θ : ClosedRealOneOneForm n M}
    {φ u : M → EReal} (hp : IsThetaPshPotential θ.val φ)
    (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ) (C t : ℝ) :
    realCutoff φ u (C * t) ≤ finiteGeodesic θ.val φ (realCutoff φ u C) t := by
  exact competitor_slice_le_finiteGeodesic
    (isSubgeodesicFrom_realCutoff_time hp hu hup C).mem_finiteGeodesicCompetitors t

end

end SGPT.Foundations.Analysis.Pending.SingularCutoffSubgeodesicBarrier
