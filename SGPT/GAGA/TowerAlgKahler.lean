import SGPT.GAGA.SmoothFlagsScheme
import SGPT.Projective.FubiniStudy
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.Pending.KahlerPerturbation

/-!
# A holomorphic embedding into `ℙᴺ` pulls back the Fubini–Study Kähler form


Let `M` be a complex manifold of dimension `n` (in the `SGPT.Foundations.Analysis` charts) and
`Ψ : M → ℙᴺ` a holomorphic embedding in the sense of lane H0-GAGA2
(`SGPT.GAGA.H0S.IsHolomorphicEmbedding`: continuous, injective, holomorphic with injective
derivative in the affine charts of `ℙᴺ` and the preferred charts of `M`).

* `injective_fderiv_coordinateMap_of_isHolomorphicEmbedding`: the real derivative of `Ψ` in
  *every* pair of atlas charts is injective (the immersion condition is stated only at the
  preferred chart of each point; chart changes of `M` have invertible derivatives).
* `kahlerBackgroundOfHolomorphicEmbedding`: `Ψ^* ω_FS` is a Kähler form on `M`
  (`SGPT.Projective.ComplexProjectiveSpace.fsBackground`, pulled back along `Ψ`).  This is the
  classical fact that projective manifolds are Kähler; it is the analytic-model counterpart of
  `SGPT.Okounkov.schemeProjectiveTNKahlerBackground` (which does the same for `X(ℂ)` of a closed
  projective scheme).
* `nonempty_kahlerBackground_of_isHolomorphicEmbedding`: a complex manifold with a holomorphic
  embedding into some `ℙᴺ` carries a Kähler background.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.TowerAlg

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {n N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {Ψ : M → ComplexProjectiveSpace N}

/-- **The derivative of a holomorphic embedding is injective in every pair of atlas charts.** -/
theorem injective_fderiv_coordinateMap_of_isHolomorphicEmbedding
    (hΨ : SGPT.GAGA.H0S.IsHolomorphicEmbedding (n := n) Ψ) (e : ComplexChart n M)
    (d : ComplexChart N (ComplexProjectiveSpace N)) (z : ComplexModel n)
    (hz : z ∈ coordinateDomain Ψ e d) :
    Function.Injective (fderiv ℝ (coordinateMap Ψ e d) z) := by
  have hs : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ Ψ :=
    SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΨ
  set p := e.val.symm z with hp
  set e' : ComplexChart n M := complexChartAt (n := n) p with he'
  obtain ⟨i, hi⟩ := (mem_atlas_iff d.val).mp d.property
  have hpe' : p ∈ e'.val.source := mem_complexChartAt_source p
  have hΨp : Ψ p ∈ (affineChart i).source := by
    have h2 := hz.2
    rw [hi] at h2
    exact h2
  -- the point in the preferred chart
  have hw : e'.val p ∈ coordinateDomain Ψ e' d := by
    refine mem_coordinateDomain hpe' ?_
    rw [hi]
    exact hΨp
  -- injectivity at the preferred chart (the immersion condition)
  have hinjC : Function.Injective (fderiv ℂ (coordinateMap Ψ e' d) (e'.val p)) := by
    have h := hΨ.immersion p i hΨp
    have hfun : coordinateMap Ψ e' d = SGPT.GAGA.H0S.chartMap (n := n) Ψ p i := by
      funext w
      simp only [coordinateMap, Function.comp_apply, SGPT.GAGA.H0S.chartMap, hi, he']
    rw [hfun]
    exact h
  have hinjR : Function.Injective (fderiv ℝ (coordinateMap Ψ e' d) (e'.val p)) := by
    rw [coordinateMap_fderiv_restrictScalars hs e' d hw]
    exact hinjC
  -- change of source chart
  have hzt : z ∈ (chartTransition e e').source := by
    refine ⟨hz.1, ?_⟩
    change e.val.symm z ∈ e'.val.source
    exact hpe'
  have hT : chartTransition e e' z = e'.val p := rfl
  rw [coordinateMap_fderiv_change_source hs e e' d hzt hz, hT]
  exact hinjR.comp
    (SGPT.Foundations.Analysis.Pending.KahlerPerturbation.chartTransitionDerivative_injective e e' hzt)

/-- **`Ψ^* ω_FS` is a Kähler background** for every holomorphic embedding `Ψ : M → ℙᴺ`. -/
def kahlerBackgroundOfHolomorphicEmbedding
    (hΨ : SGPT.GAGA.H0S.IsHolomorphicEmbedding (n := n) Ψ) : KahlerBackground n M where
  form := ClosedRealOneOneForm.pullback
    (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΨ) fsBackground.form
  isKahler := SmoothRealForm.IsKahler.pullback_of_injective
    (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΨ)
    (injective_fderiv_coordinateMap_of_isHolomorphicEmbedding hΨ) fsBackground.isKahler

/-- The form of `kahlerBackgroundOfHolomorphicEmbedding` is the pull-back of `ω_FS`. -/
theorem kahlerBackgroundOfHolomorphicEmbedding_form
    (hΨ : SGPT.GAGA.H0S.IsHolomorphicEmbedding (n := n) Ψ) :
    (kahlerBackgroundOfHolomorphicEmbedding hΨ).form =
      ClosedRealOneOneForm.pullback
        (SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΨ) fsBackground.form :=
  rfl

/-- **Projective manifolds are Kähler**: a complex manifold with a holomorphic embedding into some
`ℙᴺ` carries a Kähler background. -/
theorem nonempty_kahlerBackground_of_isHolomorphicEmbedding
    (hΨ : SGPT.GAGA.H0S.IsHolomorphicEmbedding (n := n) Ψ) : Nonempty (KahlerBackground n M) :=
  ⟨kahlerBackgroundOfHolomorphicEmbedding hΨ⟩

end SGPT.GAGA.TowerAlg

end
