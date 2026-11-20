import SGPT.Okounkov.TranscendentalCoreDefs
import SGPT.Okounkov.TranscendentalMainStatement
import SGPT.Foundations.Analysis.Pending.ProductTestForms
import SGPT.Foundations.Analysis.Pending.DemaillyAnalyticType
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Independence of the representative (transcendental Okounkov bodies)

Source: blueprint nodes `tok:def-classes` (the classes `𝒜(ξ)`, `𝒜ᵍ(ξ)`, `𝒢(ξ)`, `Ω(ξ)` depend only
on `ξ`) and `tok:rep-independence`, i.e. the open part of the book's `def:tradOk`: the Okounkov
body `Δ_{Y•}(α)` does not depend on the representative `θ` of `α`.

If `θ' = θ + dd^c g` with `g` smooth, then `φ ↦ φ - g` is a bijection `PSH(X, θ) → PSH(X, θ')`
with `θ'_{φ - g} = θ_φ`. It preserves analytic singularities, analytic singularities of a global
type, gentle analytic singularities and Kähler currents, and it does not change the valuation
(the potentials `φ` and `φ - g` differ by a bounded function, so they have the same multiplier
ideals). Hence the generating sets `ν(𝒢({θ}))` and `ν(𝒢({θ'}))` coincide.

## Main results

* `hasManifoldAnalyticSingularityType_sub_continuous`,
  `hasAnalyticSingularitiesOfType_sub_continuous`,
  `hasGentleAnalyticSingularitiesOfType_sub_smooth`: perturbation by smooth functions.
* `sub_mem_analyticCurrents`, `sub_mem_globalAnalyticCurrents`, `sub_mem_gentleCurrents`,
  `sub_mem_gentleKahlerCurrents`: the classes only depend on `ξ`.
* `flagValuation_sub_smooth`: `ν(φ - g) = ν(φ)`.
* `tradOkounkovBody_eq_of_class_eq` and `representativeIndependence`
  (`RepresentativeIndependence F`, the first conjunct of `OkounkovTranMainStatement`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalCore

open Set Filter
open scoped Topology Manifold ContDiff NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.PSH

/-! ### Extended-real arithmetic -/

/-- `(a + r) - s = a + (r - s)` for real `r`, `s`. -/
theorem ereal_add_coe_sub_coe (a : EReal) (r s : ℝ) :
    a + (r : EReal) - (s : EReal) = a + ((r - s : ℝ) : EReal) := by
  rw [EReal.coe_sub, sub_eq_add_neg, sub_eq_add_neg, add_assoc]

/-- `r (a - s) = r a - r s` for `r > 0` and real `s`, including `a = ±∞`. -/
theorem ereal_coe_mul_sub_coe_of_pos {r : ℝ} (hr : 0 < r) (a : EReal) (s : ℝ) :
    (r : EReal) * (a - (s : EReal)) = (r : EReal) * a - ((r * s : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => rw [EReal.bot_sub, EReal.coe_mul_bot_of_pos hr, EReal.bot_sub]
  | top => rw [EReal.top_sub_coe, EReal.coe_mul_top_of_pos hr, EReal.top_sub_coe]
  | coe a =>
      rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub, mul_sub]

/-- `a - s = a + (-s)` for real `s`. -/
theorem ereal_sub_coe_eq_add_coe_neg (a : EReal) (s : ℝ) :
    a - (s : EReal) = a + ((-s : ℝ) : EReal) := by
  rw [sub_eq_add_neg, EReal.coe_neg]

section Perturbation

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Perturbation of singularity types by smooth functions -/

omit [IsComplexManifold n M] in
/-- Analytic singularities (in every chart) are preserved by subtracting a continuous
function. -/
theorem hasManifoldAnalyticSingularityType_sub_continuous {φ : M → EReal}
    (hφ : HasManifoldAnalyticSingularityType (n := n) φ) {g : M → ℝ} (hg : Continuous g) :
    HasManifoldAnalyticSingularityType (n := n) (fun x => φ x - (g x : EReal)) := by
  intro e z hz
  have hcont : ContinuousAt (fun w => -g (e.val.symm w)) z :=
    (hg.continuousAt.comp (e.val.continuousAt_symm hz)).neg
  refine Pending.DemaillyAnalyticType.HasAnalyticSingularityTypeAt.of_eventuallyEq_add_bounded
    (hφ e z hz) (boundedRealGermAt_of_continuousAt hcont) (Eventually.of_forall fun w => ?_)
  exact ereal_sub_coe_eq_add_coe_neg _ _

omit [IsComplexManifold n M] in
/-- Analytic singularities of a global type `(c, 𝔞)` are preserved by subtracting a continuous
function. -/
theorem hasAnalyticSingularitiesOfType_sub_continuous {φ : M → EReal} {c : ℚ}
    {𝔞 : GermIdeal n M} (h : HasAnalyticSingularitiesOfType (n := n) φ c 𝔞) {g : M → ℝ}
    (hg : Continuous g) :
    HasAnalyticSingularitiesOfType (n := n) (fun x => φ x - (g x : EReal)) c 𝔞 := by
  obtain ⟨hc, hcoh, hloc⟩ := h
  refine ⟨hc, hcoh, fun x => ?_⟩
  obtain ⟨U, hU, hxU, N, s, hs, hspan, R, C, hRC, heq⟩ := hloc x
  refine ⟨U ∩ g ⁻¹' Metric.ball (g x) 1, hU.inter (Metric.isOpen_ball.preimage hg),
    ⟨hxU, Metric.mem_ball_self one_pos⟩, N, s, fun i => (hs i).mono inter_subset_left,
    fun y hy => hspan y hy.1, fun y => R y - g y, C + (|g x| + 1), ?_, ?_⟩
  · intro y hy
    have h1 := hRC y hy.1
    have h2 : |g y - g x| < 1 := by simpa [Real.dist_eq] using hy.2
    have h3 : |g y| ≤ |g x| + 1 := by
      have := abs_sub_abs_le_abs_sub (g y) (g x)
      linarith
    calc |R y - g y| ≤ |R y| + |g y| := abs_sub _ _
      _ ≤ C + (|g x| + 1) := add_le_add h1 h3
  · intro y hy
    change φ y - (g y : EReal) = _
    rw [heq y hy.1, ereal_add_coe_sub_coe]

/-- Gentle analytic singularities of type `(c, 𝔞)` (source `def:analy-sing`) are preserved by
subtracting a smooth function `g` (provided the result is quasi-psh): `e^{(φ - g)/c} =
e^{φ/c} e^{-g/c}` is smooth, and on the resolution the smooth remainder changes by `g ∘ f`. -/
theorem hasGentleAnalyticSingularitiesOfType_sub_smooth {φ : M → EReal} {c : ℚ}
    {𝔞 : GermIdeal n M} (hφ : HasGentleAnalyticSingularitiesOfType (n := n) φ c 𝔞)
    {g : M → ℝ} (hg : ChartSmooth (n := n) g)
    (hq : IsGlobalQuasiPshPotential (n := n) (fun x => φ x - (g x : EReal))) :
    HasGentleAnalyticSingularitiesOfType (n := n) (fun x => φ x - (g x : EReal)) c 𝔞 := by
  obtain ⟨-, htype, hexp, hsmooth, Y, iT, iC, iM, f, D, hf, hK, hloc⟩ := hφ
  have hc : (0 : ℝ) < c := by exact_mod_cast htype.1
  have hcinv : (0 : ℝ) < (c : ℝ)⁻¹ := inv_pos.mpr hc
  have hexp_eq : ∀ x, EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) * (φ x - (g x : EReal))) =
      EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) * φ x) *
        ENNReal.ofReal (Real.exp (-((c : ℝ)⁻¹ * g x))) := by
    intro x
    rw [ereal_coe_mul_sub_coe_of_pos hcinv, ereal_sub_coe_eq_add_coe_neg, EReal.exp_add,
      EReal.exp_coe]
  refine ⟨hq, hasAnalyticSingularitiesOfType_sub_continuous htype
    (Pending.ProductTestForms.ChartSmooth.continuous hg), ?_, ?_, ?_⟩
  · intro x
    rw [hexp_eq]
    exact ENNReal.mul_ne_top (hexp x) ENNReal.ofReal_ne_top
  · have hfun : (fun x => (EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) *
          (φ x - (g x : EReal)))).toReal) =
        fun x => (EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) * φ x)).toReal *
          Real.exp (-((c : ℝ)⁻¹ * g x)) := by
      funext x
      rw [hexp_eq, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [hfun]
    have hE : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-((c : ℝ)⁻¹ * t))) :=
      Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).neg)
    exact fun e => (hsmooth e).mul (hE.comp_contDiffOn (hg e))
  · refine ⟨Y, iT, iC, iM, f, D, hf, hK, fun y => ?_⟩
    obtain ⟨V, hV, hyV, s, hs, hsne, hsD, Φ, hΦsrc, hΦ0, h, r, hr, hball, hh, heq⟩ := hloc y
    have hG : ChartSmooth (n := n) (fun p : Y => g (f p)) :=
      Pending.ProductTestForms.chartSmooth_comp hf.1 hg
    have h1 := hG (complexChartAt (n := n) y)
    have h2 : ContDiffOn ℝ ∞ Φ.invFun Φ.target :=
      contDiffOn_real_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target
    have h3 := h1.comp h2 (fun z hz => hΦsrc (Φ.mapsTo_invFun hz))
    refine ⟨V, hV, hyV, s, hs, hsne, hsD, Φ, hΦsrc, hΦ0,
      fun z => h z - g (f ((complexChartAt (n := n) y).val.symm (Φ.invFun z))), r, hr, hball,
      hh.sub (h3.mono hball), fun z hz => ?_⟩
    obtain ⟨hmem, hzeq⟩ := heq z hz
    refine ⟨hmem, ?_⟩
    change φ (f _) - (g (f _) : EReal) = _
    rw [hzeq, ereal_add_coe_sub_coe]

/-- The project's gentle analytic singularities (`SourceGentleAnalyticSingularities`) are
preserved by subtracting a smooth function, when the result is `θ'`-psh. -/
theorem sourceGentleAnalyticSingularities_sub_smooth {φ : M → EReal} {c : ℚ}
    {𝔞 : GermIdeal n M} (hφ : SourceGentleAnalyticSingularities φ c 𝔞)
    {g : M → ℝ} (hg : ChartSmooth (n := n) g) {θ' : ClosedRealOneOneForm n M}
    (hθ' : IsThetaPshPotential θ'.val (fun x => φ x - (g x : EReal))) :
    SourceGentleAnalyticSingularities (fun x => φ x - (g x : EReal)) c 𝔞 :=
  ⟨⟨θ', hθ'⟩, hasGentleAnalyticSingularitiesOfType_sub_smooth hφ.2 hg hθ'.quasiPshPotential⟩

/-! ### The classes depend only on the cohomology class -/

variable {θ θ' : ClosedRealOneOneForm n M} {g : M → ℝ}

/-- The Kähler condition is transported along `θ' = θ + dd^c g`. -/
theorem isKahlerCurrentPotential_sub_smooth (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : M → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    IsKahlerCurrentPotential θ' (fun x => φ x - (g x : EReal)) := by
  obtain ⟨κ, hκ⟩ := hφ
  refine ⟨κ, thetaPshPotential_sub_smooth hg ?_ hκ⟩
  intro e z hz
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
    hθθ' e z hz]
  abel

/-- `𝒜(ξ)` depends only on `ξ`: `φ ∈ 𝒜({θ})` gives `φ - g ∈ 𝒜({θ + dd^c g})`. -/
theorem sub_mem_analyticCurrents (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : M → EReal} (hφ : φ ∈ analyticCurrents θ) :
    (fun x => φ x - (g x : EReal)) ∈ analyticCurrents θ' :=
  ⟨thetaPshPotential_sub_smooth hg hθθ' hφ.1,
    hasManifoldAnalyticSingularityType_sub_continuous hφ.2
      (Pending.ProductTestForms.ChartSmooth.continuous hg)⟩

/-- `𝒜ᵍ(ξ)` depends only on `ξ`. -/
theorem sub_mem_globalAnalyticCurrents (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : M → EReal} (hφ : φ ∈ globalAnalyticCurrents θ) :
    (fun x => φ x - (g x : EReal)) ∈ globalAnalyticCurrents θ' := by
  obtain ⟨hpsh, c, 𝔞, htype⟩ := hφ
  exact ⟨thetaPshPotential_sub_smooth hg hθθ' hpsh, c, 𝔞,
    hasAnalyticSingularitiesOfType_sub_continuous htype
      (Pending.ProductTestForms.ChartSmooth.continuous hg)⟩

/-- `𝒢(ξ)` depends only on `ξ`. -/
theorem sub_mem_gentleCurrents (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : M → EReal} (hφ : φ ∈ gentleCurrents θ) :
    (fun x => φ x - (g x : EReal)) ∈ gentleCurrents θ' := by
  obtain ⟨hpsh, c, 𝔞, hgentle⟩ := hφ
  have hpsh' := thetaPshPotential_sub_smooth hg hθθ' hpsh
  exact ⟨hpsh', c, 𝔞, sourceGentleAnalyticSingularities_sub_smooth hgentle hg hpsh'⟩

/-- `Ω(ξ)` depends only on `ξ`. -/
theorem sub_mem_gentleKahlerCurrents (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {φ : M → EReal} (hφ : φ ∈ gentleKahlerCurrents θ) :
    (fun x => φ x - (g x : EReal)) ∈ gentleKahlerCurrents θ' :=
  ⟨sub_mem_gentleCurrents hg hθθ' hφ.1, isKahlerCurrentPotential_sub_smooth hg hθθ' hφ.2⟩

/-- On a compact manifold, subtracting a smooth function does not change the singularity
type: `φ - g ⪯ ψ - g` iff `φ ⪯ ψ`. -/
theorem singularityLE_sub_smooth_iff [CompactSpace M] (hg : ChartSmooth (n := n) g)
    {φ ψ : M → EReal} :
    SingularityLE (fun x => φ x - (g x : EReal)) (fun x => ψ x - (g x : EReal)) ↔
      SingularityLE φ ψ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (Pending.ProductTestForms.ChartSmooth.continuous hg).continuousOn
  simp only [singularityLE_iff_exists_real]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A + 2 * C, fun x => ?_⟩
    have hx := hA x
    have hgx : |g x| ≤ C := by simpa using hC x (mem_univ x)
    rw [ereal_sub_coe_eq_add_coe_neg, ereal_sub_coe_eq_add_coe_neg] at hx
    calc φ x = φ x + ((-g x : ℝ) : EReal) + ((g x : ℝ) : EReal) := by
            rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
      _ ≤ ψ x + ((-g x : ℝ) : EReal) + (A : EReal) + ((g x : ℝ) : EReal) :=
            add_le_add hx le_rfl
      _ = ψ x + ((A : ℝ) : EReal) := by
            rw [add_assoc, add_assoc, ← EReal.coe_add, ← EReal.coe_add]
            congr 2
            ring
      _ ≤ ψ x + ((A + 2 * C : ℝ) : EReal) := by
            gcongr
            linarith [abs_nonneg (g x), le_abs_self (g x)]
  · rintro ⟨A, hA⟩
    refine ⟨A, fun x => ?_⟩
    rw [ereal_sub_coe_eq_add_coe_neg, ereal_sub_coe_eq_add_coe_neg, add_right_comm]
    exact add_le_add (hA x) le_rfl

end Perturbation

/-! ### The valuation and the Okounkov body -/

section Valuation

variable {n : ℕ} {F : OriginalFlagGeometry.{u} n}

/-- A continuous function on the compact manifold `X` is bounded, so subtracting it does not
change multiplier ideals. -/
theorem iEquivalentOnManifold_sub_continuous {φ : F.carrier → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {g : F.carrier → ℝ} (hg : Continuous g)
    (hφg : ManifoldQuasiPlurisubharmonic (n := n) (fun x => φ x - (g x : EReal))) :
    IEquivalentOnManifold (n := n) (fun x => φ x - (g x : EReal)) φ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hgx : ∀ x, |g x| ≤ C := fun x => by simpa using hC x (mem_univ x)
  constructor
  · refine Pending.iOrderOnManifold_of_le_add hφ (C := C) fun x => ?_
    rw [ereal_sub_coe_eq_add_coe_neg]
    refine add_le_add (le_refl (φ x)) (EReal.coe_le_coe_iff.mpr ?_)
    linarith [neg_abs_le (g x), hgx x]
  · refine Pending.iOrderOnManifold_of_le_add hφg (C := C) fun x => ?_
    rw [ereal_sub_coe_eq_add_coe_neg, add_assoc, ← EReal.coe_add]
    have h0 : (0 : EReal) ≤ ((-g x + C : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (by linarith [le_abs_self (g x), hgx x])
    simpa only [add_zero] using add_le_add (le_refl (φ x)) h0

/-- `ν(θ'_{φ - g}) = ν(θ_φ)`: the valuation of the transported potential is unchanged. -/
theorem flagValuation_sub_smooth {θ θ' : ClosedRealOneOneForm n F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) {g : F.carrier → ℝ}
    (hg : ChartSmooth (n := n) g)
    (hφg : IsThetaPshPotential θ'.val (fun x => φ x - (g x : EReal))) :
    flagValuation F (fun x => φ x - (g x : EReal)) = flagValuation F φ :=
  flagValuation_eq_of_iEquivalent hφg hφ
    (iEquivalentOnManifold_sub_continuous hφ.quasiPshPotential.1
      (Pending.ProductTestForms.ChartSmooth.continuous hg) hφg.quasiPshPotential.1)

/-- The valuations of a class of potentials are transported along `θ' = θ + dd^c g`. -/
private theorem image_subset_of_transport {θ θ' : ClosedRealOneOneForm n F.carrier}
    {S : Set (F.carrier → EReal)} {S' : Set (F.carrier → EReal)} {g : F.carrier → ℝ}
    (hg : ChartSmooth (n := n) g)
    (hθθ' : ∀ (e : ComplexChart n F.carrier) (z : ComplexModel n), z ∈ e.val.target →
      θ'.val.coeff e z = θ.val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    (hS : ∀ φ ∈ S, IsThetaPshPotential θ.val φ)
    (hSS' : ∀ φ ∈ S, (fun x => φ x - (g x : EReal)) ∈ S') :
    flagValuation F '' S ⊆ flagValuation F '' S' := by
  rintro x ⟨φ, hφ, rfl⟩
  exact ⟨_, hSS' φ hφ,
    flagValuation_sub_smooth (hS φ hφ) hg (thetaPshPotential_sub_smooth hg hθθ' (hS φ hφ))⟩

theorem image_gentleCurrents_subset_of_bottChernRel {θ θ' : ClosedRealOneOneForm n F.carrier}
    (h : ClosedRealOneOneForm.BottChernRel θ θ') :
    flagValuation F '' gentleCurrents θ ⊆ flagValuation F '' gentleCurrents θ' := by
  obtain ⟨g, hg, hθθ'⟩ := h
  exact image_subset_of_transport hg hθθ' (fun _ hφ => hφ.1)
    (fun _ hφ => sub_mem_gentleCurrents hg hθθ' hφ)

theorem image_gentleKahlerCurrents_subset_of_bottChernRel
    {θ θ' : ClosedRealOneOneForm n F.carrier} (h : ClosedRealOneOneForm.BottChernRel θ θ') :
    flagValuation F '' gentleKahlerCurrents θ ⊆ flagValuation F '' gentleKahlerCurrents θ' := by
  obtain ⟨g, hg, hθθ'⟩ := h
  exact image_subset_of_transport hg hθθ' (fun _ hφ => hφ.1.1)
    (fun _ hφ => sub_mem_gentleKahlerCurrents hg hθθ' hφ)

theorem image_analyticCurrents_subset_of_bottChernRel
    {θ θ' : ClosedRealOneOneForm n F.carrier} (h : ClosedRealOneOneForm.BottChernRel θ θ') :
    flagValuation F '' analyticCurrents θ ⊆ flagValuation F '' analyticCurrents θ' := by
  obtain ⟨g, hg, hθθ'⟩ := h
  exact image_subset_of_transport hg hθθ' (fun _ hφ => hφ.1)
    (fun _ hφ => sub_mem_analyticCurrents hg hθθ' hφ)

theorem image_globalAnalyticCurrents_subset_of_bottChernRel
    {θ θ' : ClosedRealOneOneForm n F.carrier} (h : ClosedRealOneOneForm.BottChernRel θ θ') :
    flagValuation F '' globalAnalyticCurrents θ ⊆
      flagValuation F '' globalAnalyticCurrents θ' := by
  obtain ⟨g, hg, hθθ'⟩ := h
  exact image_subset_of_transport hg hθθ' (fun _ hφ => hφ.1)
    (fun _ hφ => sub_mem_globalAnalyticCurrents hg hθθ' hφ)

variable {θ θ' : ClosedRealOneOneForm n F.carrier}

/-- `ν(𝒢(ξ))` depends only on `ξ`. -/
theorem image_gentleCurrents_eq_of_class_eq
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    flagValuation F '' gentleCurrents θ = flagValuation F '' gentleCurrents θ' := by
  have hrel := (RealBottChern.ofRepresentative_eq_iff θ θ').mp h
  exact (image_gentleCurrents_subset_of_bottChernRel hrel).antisymm
    (image_gentleCurrents_subset_of_bottChernRel hrel.symm)

/-- `ν(Ω(ξ))` depends only on `ξ`. -/
theorem image_gentleKahlerCurrents_eq_of_class_eq
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    flagValuation F '' gentleKahlerCurrents θ = flagValuation F '' gentleKahlerCurrents θ' := by
  have hrel := (RealBottChern.ofRepresentative_eq_iff θ θ').mp h
  exact (image_gentleKahlerCurrents_subset_of_bottChernRel hrel).antisymm
    (image_gentleKahlerCurrents_subset_of_bottChernRel hrel.symm)

/-- `ν(𝒜(ξ))` depends only on `ξ`. -/
theorem image_analyticCurrents_eq_of_class_eq
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    flagValuation F '' analyticCurrents θ = flagValuation F '' analyticCurrents θ' := by
  have hrel := (RealBottChern.ofRepresentative_eq_iff θ θ').mp h
  exact (image_analyticCurrents_subset_of_bottChernRel hrel).antisymm
    (image_analyticCurrents_subset_of_bottChernRel hrel.symm)

/-- `ν(𝒜ᵍ(ξ))` depends only on `ξ`. -/
theorem image_globalAnalyticCurrents_eq_of_class_eq
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    flagValuation F '' globalAnalyticCurrents θ =
      flagValuation F '' globalAnalyticCurrents θ' := by
  have hrel := (RealBottChern.ofRepresentative_eq_iff θ θ').mp h
  exact (image_globalAnalyticCurrents_subset_of_bottChernRel hrel).antisymm
    (image_globalAnalyticCurrents_subset_of_bottChernRel hrel.symm)

/-- Source `def:tradOk`, blueprint `tok:rep-independence`: if `{θ} = {θ'}` then
`Δ_{Y•}(θ) = Δ_{Y•}(θ')`. -/
theorem tradOkounkovBody_eq_of_class_eq
    (h : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative θ') :
    tradOkounkovBody F θ = tradOkounkovBody F θ' := by
  rw [tradOkounkovBody_eq_closure_image, tradOkounkovBody_eq_closure_image,
    image_gentleCurrents_eq_of_class_eq h]

end Valuation

/-- **Source `def:tradOk`, independence of the representative** (blueprint
`tok:rep-independence`; the first conjunct `RepresentativeIndependence` of
`OkounkovTranMainStatement`): `Δ_{Y•}(θ)` only depends on the class `{θ}`. -/
theorem representativeIndependence {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1)) :
    TranscendentalMain.RepresentativeIndependence F := by
  intro θ
  exact tradOkounkovBody_eq_of_class_eq (Quotient.out_eq _).symm

end SGPT.Okounkov.TranscendentalCore
