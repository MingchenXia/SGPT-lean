import SGPT.Okounkov.TranscendentalSkodaL2Statements
import SGPT.Foundations.Analysis.Pending.OTWeakDbar
import SGPT.Foundations.Analysis.Pending.WeakDbarWeyl
import SGPT.Foundations.Analysis.Pending.HormanderDensity
import SGPT.Foundations.Analysis.Pending.HormanderTestPairing
import SGPT.Foundations.Analysis.Pending.LeviWirtinger
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Skoda's division for surjective tuples from the kernel-bundle `L²` estimate

Blueprint `claude-tok-skoda`, node `skoda:surjective-division`:
`TwistedHormanderStatement → SurjectiveSkodaStatement`.

For a tuple `G` without common zeros on `D` and `f` holomorphic on `D`, the smooth lifting
`h⁰ = f Ḡ / |G|²` satisfies `G · h⁰ = f`; its `∂̄`, `v = ∂̄ h⁰`, is a `∂̄`-closed form with values in
the kernel bundle `S = ker G`. With the weight `Φ = p log |G|²`, Skoda's curvature inequality
(`secondFundamental_le_leviForm`) gives the curvature hypothesis of the kernel-bundle estimate
with `t = (p - n)/(2n)`, and `|⟨α, v⟩|² = |f|² B(α)/|G|²` gives its twisted bound with
`g = |f|²/(t |G|²)`. The solution `u` of `∂̄ u = v` in `S` yields `H = h⁰ - u`, holomorphic by
Weyl's lemma, with `G · H = f` and `|H|² = |f|²/|G|² + |u|²`.

This file contains the smooth lifting and its pointwise algebra.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalSkoda

open Filter MeasureTheory Set SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.Hormander.Density
open scoped Topology ComplexConjugate ContDiff ENNReal

variable {n R : ℕ}

/-! ### Smoothness -/

theorem contDiffOn_real_of_holo {D : Set (ComplexModel n)} (hD : IsOpen D)
    {F : ComplexModel n → ℂ} (hF : DifferentiableOn ℂ F D) : ContDiffOn ℝ ∞ F D :=
  SGPT.Foundations.Analysis.FirstPass.contDiffOn_real_of_differentiableOn_complex hF hD

theorem contDiffOn_generatorNormSq {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D) :
    ContDiffOn ℝ ∞ (generatorNormSq G) D := by
  have : generatorNormSq G = fun y => ∑ i, ‖G i y‖ ^ 2 := rfl
  rw [this]
  exact ContDiffOn.sum fun i _ =>
    (contDiff_norm_sq ℝ).comp_contDiffOn (contDiffOn_real_of_holo hD (hG i))

/-- The smooth lifting `h⁰ᵢ = f Ḡᵢ / |G|²`. -/
def skodaLift (G : Fin R → ComplexModel n → ℂ) (f : ComplexModel n → ℂ) (i : Fin R)
    (y : ComplexModel n) : ℂ :=
  f y * conj (G i y) * (((generatorNormSq G y)⁻¹ : ℝ) : ℂ)

/-- Its `∂̄`: `vᵢⱼ = ∂̄ⱼ h⁰ᵢ`. -/
def skodaForm (G : Fin R → ComplexModel n → ℂ) (f : ComplexModel n → ℂ) (i : Fin R) (j : Fin n)
    (y : ComplexModel n) : ℂ :=
  dbarDir (coordVec j) (skodaLift G f i) y

theorem contDiffOn_skodaLift {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f D) (i : Fin R) : ContDiffOn ℝ ∞ (skodaLift G f i) D := by
  have h1 := contDiffOn_real_of_holo hD hf
  have h2 : ContDiffOn ℝ ∞ (fun y => conj (G i y)) D :=
    Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_real_of_holo hD (hG i))
  have h3 : ContDiffOn ℝ ∞ (fun y => (((generatorNormSq G y)⁻¹ : ℝ) : ℂ)) D :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiffOn_generatorNormSq hD hG).inv fun z hz => (hpos z hz).ne')
  exact (h1.mul h2).mul h3

/-- `G · h⁰ = f` on `D`. -/
theorem sum_mul_skodaLift {D : Set (ComplexModel n)} {G : Fin R → ComplexModel n → ℂ}
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) (f : ComplexModel n → ℂ) {z : ComplexModel n}
    (hz : z ∈ D) : ∑ i, G i z * skodaLift G f i z = f z := by
  have hS := hpos z hz
  simp only [skodaLift]
  have hterm : ∀ i, G i z * (f z * conj (G i z) * (((generatorNormSq G z)⁻¹ : ℝ) : ℂ)) =
      (f z * (((generatorNormSq G z)⁻¹ : ℝ) : ℂ)) * ((‖G i z‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, ← Complex.ofReal_sum]
  have hsum : ∑ i, ‖G i z‖ ^ 2 = generatorNormSq G z := rfl
  rw [hsum, mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hS.ne', Complex.ofReal_one, mul_one]

/-! ### Wirtinger calculus helpers -/

theorem contDiffOn_dbarDir {D : Set (ComplexModel n)} (hD : IsOpen D) {F : ComplexModel n → ℂ}
    (hF : ContDiffOn ℝ ∞ F D) (v : ComplexModel n) : ContDiffOn ℝ ∞ (dbarDir v F) D := by
  have h1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x) D := hF.fderiv_of_isOpen hD (by simp)
  have h2 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x v) D := h1.clm_apply contDiffOn_const
  have h3 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x (Complex.I • v)) D :=
    h1.clm_apply contDiffOn_const
  have : dbarDir v F = fun x => (fderiv ℝ F x v + Complex.I * fderiv ℝ F x (Complex.I • v)) / 2 :=
    rfl
  rw [this]
  exact (h2.add (contDiffOn_const.mul h3)).div_const 2

theorem dbarDir_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ComplexModel n → ℂ}
    {x v : ComplexModel n} (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) x) :
    dbarDir v (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, dbarDir v (F i) x := by
  simp only [dbarDir, fderiv_fun_sum hF, _root_.sum_apply, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, Finset.sum_div]

/-! ### The pointwise algebra of `v = ∂̄ h⁰` -/

/-- `vᵢⱼ = f (conj(∂ⱼGᵢ) |G|⁻² + Ḡᵢ cⱼ)` with `cⱼ = ∂̄ⱼ(|G|⁻²)`. -/
theorem skodaForm_eq {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f D) {z : ComplexModel n} (hz : z ∈ D) (i : Fin R) (j : Fin n) :
    skodaForm G f i j z = f z * (conj (dDir (coordVec j) (G i) z) *
      (((generatorNormSq G z)⁻¹ : ℝ) : ℂ) + conj (G i z) *
        dbarDir (coordVec j) (fun y => (((generatorNormSq G y)⁻¹ : ℝ) : ℂ)) z) := by
  have hfz : DifferentiableAt ℂ f z := hf.differentiableAt (hD.mem_nhds hz)
  have hGz : DifferentiableAt ℂ (G i) z := (hG i).differentiableAt (hD.mem_nhds hz)
  have hfR : DifferentiableAt ℝ f z := hfz.restrictScalars ℝ
  have hcR : DifferentiableAt ℝ (fun y => conj (G i y)) z :=
    Complex.conjCLE.differentiableAt.comp z (hGz.restrictScalars ℝ)
  have hsR : DifferentiableAt ℝ (fun y => (((generatorNormSq G y)⁻¹ : ℝ) : ℂ)) z := by
    have hS : ContDiffOn ℝ ∞ (fun y => (((generatorNormSq G y)⁻¹ : ℝ) : ℂ)) D :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((contDiffOn_generatorNormSq hD hG).inv fun z hz => (hpos z hz).ne')
    exact (hS.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
  have hprod : DifferentiableAt ℝ (fun y => f y * conj (G i y)) z := hfR.mul hcR
  have e1 : skodaForm G f i j z = dbarDir (coordVec j)
      (fun y => (f y * conj (G i y)) * (((generatorNormSq G y)⁻¹ : ℝ) : ℂ)) z := rfl
  rw [e1, dbarDir_mul hprod hsR, dbarDir_mul hfR hcR,
    SGPT.Foundations.Analysis.Pending.OTChen.dbarDir_eq_zero_of_differentiableAt hfz,
    dbarDir_conj (hGz.restrictScalars ℝ)]
  ring

/-- `G · v = 0`: `v` takes values in the kernel bundle. -/
theorem sum_mul_skodaForm {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f D) {z : ComplexModel n} (hz : z ∈ D) (j : Fin n) :
    ∑ i, G i z * skodaForm G f i j z = 0 := by
  have hev : (fun y => ∑ i, G i y * skodaLift G f i y) =ᶠ[𝓝 z] f :=
    Filter.eventually_of_mem (hD.mem_nhds hz) fun y hy => sum_mul_skodaLift hpos f hy
  have hfz : DifferentiableAt ℂ f z := hf.differentiableAt (hD.mem_nhds hz)
  have hGR : ∀ i, DifferentiableAt ℝ (G i) z :=
    fun i => ((hG i).differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
  have hLR : ∀ i, DifferentiableAt ℝ (skodaLift G f i) z := fun i =>
    ((contDiffOn_skodaLift hD hG hpos hf i).contDiffAt (hD.mem_nhds hz)).differentiableAt
      (by simp)
  have h := dbarDir_congr (v := coordVec j) hev
  rw [SGPT.Foundations.Analysis.Pending.OTChen.dbarDir_eq_zero_of_differentiableAt hfz,
    dbarDir_finset_sum (F := fun i y => G i y * skodaLift G f i y) _
      fun i _ => (hGR i).mul (hLR i)] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dbarDir_mul (hGR i) (hLR i), SGPT.Foundations.Analysis.Pending.OTChen.dbarDir_eq_zero_of_differentiableAt
    ((hG i).differentiableAt (hD.mem_nhds hz))]
  simp [skodaForm]

/-- `∑ᵢⱼ ᾱᵢⱼ vᵢⱼ = f · conj(∑ᵢⱼ ∂ⱼGᵢ αᵢⱼ) / |G|²` for `α` in the kernel bundle. -/
theorem sum_conj_mul_skodaForm {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f D) {z : ComplexModel n} (hz : z ∈ D)
    {α : Fin R → Fin n → ℂ} (hα : InKernel G z α) :
    ∑ i, ∑ j, conj (α i j) * skodaForm G f i j z =
      f z * conj (kernelPairing G z α) * (((generatorNormSq G z)⁻¹ : ℝ) : ℂ) := by
  simp_rw [skodaForm_eq hD hG hpos hf hz]
  set s : ℂ := (((generatorNormSq G z)⁻¹ : ℝ) : ℂ)
  set c : Fin n → ℂ := fun j =>
    dbarDir (coordVec j) (fun y => (((generatorNormSq G y)⁻¹ : ℝ) : ℂ)) z with hc
  have hker : ∀ j, ∑ i, conj (α i j) * conj (G i z) = 0 := by
    intro j
    have h : (starRingEnd ℂ) (∑ i, G i z * α i j) = 0 := by rw [hα j, map_zero]
    rw [map_sum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_comm]
  calc ∑ i, ∑ j, conj (α i j) * (f z * (conj (dDir (coordVec j) (G i) z) * s +
        conj (G i z) * c j))
      = ∑ i, ∑ j, (f z * s * conj (dDir (coordVec j) (G i) z * α i j) +
          f z * c j * (conj (α i j) * conj (G i z))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [map_mul]
        ring
    _ = f z * s * ∑ i, ∑ j, conj (dDir (coordVec j) (G i) z * α i j) +
          ∑ j, f z * c j * ∑ i, conj (α i j) * conj (G i z) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
    _ = f z * conj (kernelPairing G z α) * s := by
        simp only [hker, mul_zero, Finset.sum_const_zero, add_zero, kernelPairing, map_sum]
        ring

/-! ### Weak `∂̄` relations on a subdomain -/

/-- `∂̄ h⁰ᵢ = vᵢ` weakly on an open `D' ⊆ D`. -/
theorem weakDbarEq_skodaLift {D D' : Set (ComplexModel n)} (hD : IsOpen D) (hD'D : D' ⊆ D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f D) (i : Fin R) :
    WeakDbarEq D' (skodaLift G f i) (skodaForm G f i) := by
  intro h hh j
  exact SGPT.Foundations.Analysis.Pending.OTChen.integral_mul_dbarDir_eq_neg_of_contDiffOn
    (μ := volume) hD ((contDiffOn_skodaLift hD hG hpos hf i).of_le (by simp))
    (hh.1.of_le (by simp)) hh.2.1 (hh.2.2.trans hD'D) (coordVec j)

/-- `vᵢ = ∂̄ h⁰ᵢ` is weakly `∂̄`-closed on an open `D' ⊆ D`. -/
theorem weakDbarClosed_skodaForm {D D' : Set (ComplexModel n)} (hD : IsOpen D) (hD'D : D' ⊆ D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f D) (i : Fin R) :
    WeakDbarClosed D' (skodaForm G f i) := by
  intro h hh j k
  have hL := contDiffOn_skodaLift hD hG hpos hf i
  have hv : ∀ l, ContDiffOn ℝ ∞ (skodaForm G f i l) D := fun l => contDiffOn_dbarDir hD hL _
  have hhD : tsupport h ⊆ D := hh.2.2.trans hD'D
  have hh1 : ContDiff ℝ 1 h := hh.1.of_le (by simp)
  have hint : ∀ a b : Fin n, Integrable fun x => skodaForm G f i a x * dbarDir (coordVec b) h x := by
    intro a b
    have hc : Continuous (dbarDir (coordVec b) h) := continuous_dbarDir hh1
    refine (continuous_mul_of_continuousOn hD (hv a).continuousOn hc
      ((SGPT.Foundations.Analysis.Pending.OTChen.tsupport_dbarDir_subset _ h).trans hhD)
      ).integrable_of_hasCompactSupport ?_
    exact (hasCompactSupport_dbarDir hh.2.1).mul_left
  rw [integral_sub (hint k j) (hint j k),
    SGPT.Foundations.Analysis.Pending.OTChen.integral_mul_dbarDir_eq_neg_of_contDiffOn (μ := volume)
      hD ((hv k).of_le (by simp)) hh1 hh.2.1 hhD,
    SGPT.Foundations.Analysis.Pending.OTChen.integral_mul_dbarDir_eq_neg_of_contDiffOn (μ := volume)
      hD ((hv j).of_le (by simp)) hh1 hh.2.1 hhD, sub_eq_zero, neg_inj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ D
  · have h2 : ContDiffAt ℝ 2 (skodaLift G f i) x :=
      (hL.contDiffAt (hD.mem_nhds hx)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    show dbarDir (coordVec j) (dbarDir (coordVec k) (skodaLift G f i)) x * h x =
      dbarDir (coordVec k) (dbarDir (coordVec j) (skodaLift G f i)) x * h x
    rw [dbarDir_dbarDir_comm h2]
  · have hxs : x ∉ tsupport h := fun h' => hx (hhD h')
    simp [image_eq_zero_of_notMem_tsupport hxs]

/-! ### The weight `Φ = p log |G|²`: curvature and the twisted bound -/

theorem contDiffOn_skodaWeight {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) (p : ℝ) :
    ContDiffOn ℝ ∞ (fun z => p * Real.log (generatorNormSq G z)) D :=
  contDiffOn_const.mul ((contDiffOn_generatorNormSq hD hG).log fun z hz => (hpos z hz).ne')

theorem vectorLevi_skodaWeight {D : Set (ComplexModel n)} (hD : IsOpen D)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) (p : ℝ) {z : ComplexModel n} (hz : z ∈ D)
    (α : Fin R → Fin n → ℂ) :
    vectorLevi (fun y => p * Real.log (generatorNormSq G y)) z α =
      p * vectorLevi (fun y => Real.log (generatorNormSq G y)) z α := by
  have hlog : ContDiffAt ℝ 2 (fun y => Real.log (generatorNormSq G y)) z :=
    ((((contDiffOn_generatorNormSq hD hG).log fun z hz => (hpos z hz).ne').contDiffAt
      (hD.mem_nhds hz))).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hfun : (fun y => p * Real.log (generatorNormSq G y)) =
      p • fun y => Real.log (generatorNormSq G y) := by
    funext _; simp [smul_eq_mul]
  rw [vectorLevi, vectorLevi, hfun, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => leviForm_smul hlog p _

theorem eventually_differentiableAt_of_isOpen {D : Set (ComplexModel n)} (hD : IsOpen D)
    {F : ComplexModel n → ℂ} (hF : DifferentiableOn ℂ F D) {z : ComplexModel n} (hz : z ∈ D) :
    ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ F y :=
  Filter.eventually_of_mem (hD.mem_nhds hz) fun _ hy => hF.differentiableAt (hD.mem_nhds hy)

/-- With `t = (p - n)/(2n)`, `L_Φ - (1 + t) B ≥ t B` on the kernel bundle. -/
theorem skodaWeight_curvature {D : Set (ComplexModel n)} (hD : IsOpen D) (hn : 0 < n)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) {p : ℝ} (hp : (n : ℝ) < p)
    {z : ComplexModel n} (hz : z ∈ D) {α : Fin R → Fin n → ℂ} (hα : InKernel G z α) :
    ((p - n) / (2 * n)) * secondFundamental G z α ≤
      vectorLevi (fun y => p * Real.log (generatorNormSq G y)) z α -
        (1 + (p - n) / (2 * n)) * secondFundamental G z α := by
  have hB := secondFundamental_le_leviForm
    (fun i => eventually_differentiableAt_of_isOpen hD (hG i) hz) (hpos z hz) hα
  rw [vectorLevi_skodaWeight hD hG hpos p hz]
  set B := secondFundamental G z α
  set L := vectorLevi (fun y => Real.log (generatorNormSq G y)) z α
  have hB0 : 0 ≤ B := div_nonneg (sq_nonneg _) (generatorNormSq_nonneg G z)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- `p L ≥ (p / n) B` and `p/n = 1 + 2t`
  have hpL : p / n * B ≤ p * L := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hnR]
    nlinarith [hB, hp]
  have heq : p / n = 1 + 2 * ((p - n) / (2 * n)) := by field_simp; ring
  rw [heq] at hpL
  linarith

/-- The twisted bound with `g = |f|² / (t |G|²)`. -/
theorem skodaForm_twisted_bound {D : Set (ComplexModel n)} (hD : IsOpen D) (hn : 0 < n)
    {G : Fin R → ComplexModel n → ℂ} (hG : ∀ i, DifferentiableOn ℂ (G i) D)
    (hpos : ∀ z ∈ D, 0 < generatorNormSq G z) {f : ComplexModel n → ℂ}
    (hf : DifferentiableOn ℂ f D) {p : ℝ} (hp : (n : ℝ) < p) {z : ComplexModel n} (hz : z ∈ D)
    {α : Fin R → Fin n → ℂ} (hα : InKernel G z α) :
    ‖∑ i, ∑ j, conj (α i j) * skodaForm G f i j z‖ ^ 2 ≤
      ‖f z‖ ^ 2 / ((p - n) / (2 * n) * generatorNormSq G z) *
        (vectorLevi (fun y => p * Real.log (generatorNormSq G y)) z α -
          (1 + (p - n) / (2 * n)) * secondFundamental G z α) := by
  have hcurv := skodaWeight_curvature hD hn hG hpos hp hz hα
  rw [sum_conj_mul_skodaForm hD hG hpos hf hz hα]
  have hS : 0 < generatorNormSq G z := hpos z hz
  set t := (p - n) / (2 * n)
  have ht : 0 < t := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos (by linarith) (by positivity)
  have hlhs : ‖f z * conj (kernelPairing G z α) * (((generatorNormSq G z)⁻¹ : ℝ) : ℂ)‖ ^ 2 =
      ‖f z‖ ^ 2 / generatorNormSq G z * secondFundamental G z α := by
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg
      (inv_nonneg.mpr hS.le), secondFundamental]
    field_simp
  rw [hlhs]
  calc ‖f z‖ ^ 2 / generatorNormSq G z * secondFundamental G z α
      = ‖f z‖ ^ 2 / (t * generatorNormSq G z) * (t * secondFundamental G z α) := by
        field_simp
    _ ≤ _ := by gcongr

/-! ### Weighted `L²` helpers -/

/-- A bounded measurable function on a bounded open set is in `L²` of a weight bounded below. -/
theorem memLp_weightedVolume_of_bounded {D : Set (ComplexModel n)} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) {w : ComplexModel n → ℝ} (hw : ContinuousOn w D) {B : ℝ}
    (hwB : ∀ x ∈ D, -B ≤ w x) {F : ComplexModel n → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict D)) {C : ℝ} (hFC : ∀ x ∈ D, ‖F x‖ ≤ C) :
    MemLp F 2 (weightedVolume D w) := by
  have hfin : ∫⁻ x, ENNReal.ofReal (Real.exp (-w x)) ∂(volume.restrict D) ≠ ⊤ := by
    have hle : ∫⁻ x, ENNReal.ofReal (Real.exp (-w x)) ∂(volume.restrict D) ≤
        ∫⁻ _x, ENNReal.ofReal (Real.exp B) ∂(volume.restrict D) := by
      refine setLIntegral_mono' hD.measurableSet fun x hx => ?_
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hwB x hx]))
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDb.measure_lt_top.ne
  have : IsFiniteMeasure (weightedVolume D w) := isFiniteMeasure_withDensity hfin
  refine MemLp.of_bound ((aestronglyMeasurable_weightedVolume_iff hD hw).mpr hF) C ?_
  exact ae_of_ae_restrict_of_ae_weightedVolume_le hD hw hFC
where
  /-- auxiliary -/
  ae_of_ae_restrict_of_ae_weightedVolume_le (hD : IsOpen D) (hw : ContinuousOn w D)
      (hFC : ∀ x ∈ D, ‖F x‖ ≤ C) : ∀ᵐ x ∂(weightedVolume D w), ‖F x‖ ≤ C :=
    (withDensity_absolutelyContinuous _ _).ae_le
      ((ae_restrict_iff' hD.measurableSet).mpr (Filter.Eventually.of_forall hFC))

/-- `u ∈ L²(e^{-w})` gives `|u|² e^{-w}` integrable on `D`. -/
theorem integrable_sq_mul_exp_of_memLp {D : Set (ComplexModel n)} (hD : IsOpen D)
    {w : ComplexModel n → ℝ} (hw : ContinuousOn w D) {u : ComplexModel n → ℂ}
    (hu : MemLp u 2 (weightedVolume D w)) :
    Integrable (fun x => ‖u x‖ ^ 2 * Real.exp (-w x)) (volume.restrict D) := by
  have h1 : Integrable (fun x => ‖u x‖ ^ 2) (weightedVolume D w) :=
    (memLp_two_iff_integrable_sq_norm hu.1).mp hu
  rw [weightedVolume_eq_withDensity_weightDensity hD, integrable_withDensity_iff
    (measurable_weightDensity hD hw) (Eventually.of_forall fun x => weightDensity_lt_top x)] at h1
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
  simp [weightDensity, hx, (Real.exp_pos _).le]

/-! ### Assembly -/

/-- `|f|²/(t S) · e^{-p log S} = |f|² S^{-(p+1)} / t` for `S > 0`. -/
theorem skoda_g_mul_exp {S t p a : ℝ} (hS : 0 < S) :
    a / (t * S) * Real.exp (-(p * Real.log S)) = a * S ^ (-(p + 1)) / t := by
  rw [show -(p * Real.log S) = Real.log S * (-p) by ring, ← Real.rpow_def_of_pos hS,
    Real.rpow_neg hS.le, Real.rpow_neg hS.le, Real.rpow_add hS, Real.rpow_one]
  field_simp

/-- `∑ |h⁰ᵢ - uᵢ|² = |f|²/S + ∑ |uᵢ|²` when `∑ Gᵢ uᵢ = 0`. -/
theorem skoda_pythagoras {G : Fin R → ComplexModel n → ℂ} {f : ComplexModel n → ℂ}
    {u : Fin R → ComplexModel n → ℂ} {x : ComplexModel n} (hS : 0 < generatorNormSq G x)
    (hker : ∑ i, G i x * u i x = 0) :
    ∑ i, ‖skodaLift G f i x - u i x‖ ^ 2 =
      ‖f x‖ ^ 2 / generatorNormSq G x + ∑ i, ‖u i x‖ ^ 2 := by
  set s : ℝ := (generatorNormSq G x)⁻¹
  have hexp : ∀ i, ‖skodaLift G f i x - u i x‖ ^ 2 = ‖skodaLift G f i x‖ ^ 2 + ‖u i x‖ ^ 2 -
      2 * (conj (skodaLift G f i x) * u i x).re := by
    intro i
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub]
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hcross : ∑ i, 2 * (conj (skodaLift G f i x) * u i x).re = 0 := by
    rw [← Finset.mul_sum, ← Complex.re_sum]
    have : ∑ i, conj (skodaLift G f i x) * u i x =
        conj (f x) * ((s : ℝ) : ℂ) * ∑ i, G i x * u i x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [skodaLift, map_mul, Complex.conj_conj, Complex.conj_ofReal]
      ring
    rw [this, hker, mul_zero, Complex.zero_re, mul_zero]
  have hlift : ∑ i, ‖skodaLift G f i x‖ ^ 2 = ‖f x‖ ^ 2 / generatorNormSq G x := by
    have hterm : ∀ i, ‖skodaLift G f i x‖ ^ 2 = ‖f x‖ ^ 2 * s ^ 2 * ‖G i x‖ ^ 2 := by
      intro i
      simp only [skodaLift, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr hS.le)]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    have hsum : ∑ i, ‖G i x‖ ^ 2 = generatorNormSq G x := rfl
    rw [hsum]
    simp only [s]
    field_simp
  rw [hcross, hlift, sub_zero]

/-- **Skoda's division for surjective tuples from the kernel-bundle estimate**
(`skoda:surjective-division`). -/
theorem surjectiveSkodaStatement_of_twisted (hVH : TwistedHormanderStatement) :
    SurjectiveSkodaStatement := by
  intro n hn D hDo hDc hDb K hK hKD p hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := (p - n) / (2 * n) with htdef
  have ht : 0 < t := div_pos (by linarith) (by positivity)
  obtain ⟨D', U, lam₁, lam₂, hD'o, -, hD'D, hUo, hKU, hUD', hlam₁, hlam₂, hlam, hlamU, hmain⟩ :=
    hVH n D hDo hDc hDb K hK hKD t ht
  have hD'sub : D' ⊆ D := subset_closure.trans hD'D
  refine ⟨U, hUo, hKU, hUD'.trans hD'sub, ?_⟩
  intro R G hG hpos f hf hI
  set I : ℝ≥0∞ := ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)))
    with hIdef
  set Φ : ComplexModel n → ℝ := fun y => p * Real.log (generatorNormSq G y) with hΦdef
  have hΦ : ContDiffOn ℝ ∞ Φ D := contDiffOn_skodaWeight hDo hG hpos p
  have hclc : IsCompact (closure D') :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (hDb.subset hD'D)
  have hD'b : Bornology.IsBounded D' := hDb.subset hD'sub
  -- curvature hypothesis
  have hcurv : ∀ z ∈ D, ∀ α : Fin R → Fin n → ℂ, InKernel G z α →
      (1 + t) * secondFundamental G z α ≤ vectorLevi Φ z α := by
    intro z hz α hα
    have h := skodaWeight_curvature hDo hn hG hpos hp hz hα
    have hB0 : 0 ≤ secondFundamental G z α :=
      div_nonneg (sq_nonneg _) (generatorNormSq_nonneg G z)
    nlinarith [mul_nonneg ht.le hB0]
  -- the form `v`
  have hvcont : ∀ i j, ContinuousOn (skodaForm G f i j) D := fun i j =>
    (contDiffOn_dbarDir hDo (contDiffOn_skodaLift hDo hG hpos hf i) _).continuousOn
  have hvbd : ∀ i j, ∃ C, ∀ x ∈ D', ‖skodaForm G f i j x‖ ≤ C := by
    intro i j
    obtain ⟨C, hC⟩ := hclc.exists_bound_of_continuousOn ((hvcont i j).mono hD'D)
    exact ⟨C, fun x hx => hC x (subset_closure hx)⟩
  obtain ⟨B, hB⟩ := hclc.exists_bound_of_continuousOn (hΦ.continuousOn.mono hD'D)
  have hw₂ : ContinuousOn (fun x => Φ x + lam₂ x) D' := (hΦ.continuousOn.mono hD'sub).add hlam₂
  have hw₁ : ContinuousOn (fun x => Φ x + lam₁ x) D' := (hΦ.continuousOn.mono hD'sub).add hlam₁
  have hv : ∀ i j, MemLp (skodaForm G f i j) 2 (weightedVolume D' fun x => Φ x + lam₂ x) := by
    intro i j
    obtain ⟨C, hC⟩ := hvbd i j
    refine memLp_weightedVolume_of_bounded hD'o hD'b hw₂ (B := B) (fun x hx => ?_)
      (((hvcont i j).mono hD'sub).aestronglyMeasurable hD'o.measurableSet) hC
    have h1 := hB x (subset_closure hx)
    rw [Real.norm_eq_abs] at h1
    linarith [(abs_le.mp h1).1, (hlam x hx).1, (hlam x hx).2]
  have hvker : ∀ z ∈ D', InKernel G z fun i j => skodaForm G f i j z :=
    fun z hz j => sum_mul_skodaForm hDo hG hpos hf (hD'sub hz) j
  have hvcl : ∀ i, WeakDbarClosed D' (skodaForm G f i) :=
    fun i => weakDbarClosed_skodaForm hDo hD'sub hG hpos hf i
  -- the function `g`
  set g : ComplexModel n → ℝ := fun z => ‖f z‖ ^ 2 / (t * generatorNormSq G z) with hgdef
  have hg0 : ∀ x ∈ D', 0 ≤ g x := fun x _ =>
    div_nonneg (sq_nonneg _) (mul_nonneg ht.le (generatorNormSq_nonneg G x))
  have hgb : ∀ z ∈ D', ∀ α : Fin R → Fin n → ℂ, InKernel G z α →
      ‖∑ i, ∑ j, conj (α i j) * skodaForm G f i j z‖ ^ 2 ≤
        g z * (vectorLevi Φ z α - (1 + t) * secondFundamental G z α) :=
    fun z hz α hα => skodaForm_twisted_bound hDo hn hG hpos hf hp (hD'sub hz) hα
  have hgle : ∀ x ∈ D', g x * Real.exp (-(Φ x + lam₁ x)) ≤
      ‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) / t := by
    intro x hx
    rw [← skoda_g_mul_exp (hpos x (hD'sub hx))]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hg0 x hx)
    simp only [hΦdef]; linarith [(hlam x hx).1]
  have hIt : ∫⁻ x in D', ENNReal.ofReal (‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) / t) ≤
      ENNReal.ofReal t⁻¹ * I := by
    calc ∫⁻ x in D', ENNReal.ofReal (‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1)) / t)
        = ∫⁻ x in D', ENNReal.ofReal t⁻¹ *
            ENNReal.ofReal (‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1))) := by
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le), div_eq_inv_mul]
      _ = ENNReal.ofReal t⁻¹ *
            ∫⁻ x in D', ENNReal.ofReal (‖f x‖ ^ 2 * generatorNormSq G x ^ (-(p + 1))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal t⁻¹ * I := by gcongr; exact lintegral_mono_set hD'sub
  have hgmeas : AEStronglyMeasurable (fun x => g x * Real.exp (-(Φ x + lam₁ x)))
      (volume.restrict D') := by
    have hgc : ContinuousOn g D' := by
      refine ContinuousOn.div ((hf.continuousOn.mono hD'sub).norm.pow 2)
        (continuousOn_const.mul ((contDiffOn_generatorNormSq hDo hG).continuousOn.mono hD'sub))
        fun x hx => (mul_pos ht (hpos x (hD'sub hx))).ne'
    exact (hgc.mul (Real.continuous_exp.comp_continuousOn hw₁.neg)).aestronglyMeasurable
      hD'o.measurableSet
  have hgint : Integrable (fun x => g x * Real.exp (-(Φ x + lam₁ x))) (volume.restrict D') := by
    refine ⟨hgmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · refine lt_of_le_of_lt (setLIntegral_mono' hD'o.measurableSet fun x hx =>
        ENNReal.ofReal_le_ofReal (hgle x hx)) (lt_of_le_of_lt hIt ?_)
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hI)
    · filter_upwards [ae_restrict_mem hD'o.measurableSet] with x hx
      exact mul_nonneg (hg0 x hx) (Real.exp_pos _).le
  obtain ⟨u, hu2, huker, hueq, hubd⟩ :=
    hmain R G hG hpos Φ hΦ hcurv (skodaForm G f) hv hvker hvcl g hg0 hgb hgint
  -- holomorphy of `H = h⁰ - u` (Weyl's lemma)
  have hLcont : ∀ i, ContinuousOn (skodaLift G f i) D := fun i =>
    (contDiffOn_skodaLift hDo hG hpos hf i).continuousOn
  have hHex : ∀ i, ∃ H : ComplexModel n → ℂ, DifferentiableOn ℂ H D' ∧
      ∀ᵐ x ∂(volume.restrict D'), skodaLift G f i x - u i x = H x := by
    intro i
    have hu₀loc : LocallyIntegrableOn (u i) D' :=
      SGPT.Foundations.Analysis.Pending.OTChen.locallyIntegrableOn_of_memLp_weightedVolume hD'o hw₁
        (hu2 i)
    have haloc : LocallyIntegrableOn (skodaLift G f i) D' :=
      ((hLcont i).mono hD'sub).locallyIntegrableOn hD'o.measurableSet
    have hFloc : LocallyIntegrableOn (fun z => skodaLift G f i z - u i z) D' := haloc.sub hu₀loc
    have hcoord : ∀ h, IsTestFunctionOn D' h → ∀ j,
        ∫ x, (skodaLift G f i x - u i x) * dbarDir (coordVec j) h x = 0 := by
      intro h hh j
      have hdc : Continuous (dbarDir (coordVec j) h) :=
        SGPT.Foundations.Analysis.Pending.OTChen.continuous_dbarDir'
          (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
      have hdcs := hasCompactSupport_dbarDir (v := coordVec j) hh.2.1
      have hdts := (SGPT.Foundations.Analysis.Pending.OTChen.tsupport_dbarDir_subset (coordVec j) h).trans
        hh.2.2
      have i1 := SGPT.Foundations.Analysis.Pending.OTChen.integrable_mul_of_locallyIntegrableOn haloc hdc
        hdcs hdts
      have i2 := SGPT.Foundations.Analysis.Pending.OTChen.integrable_mul_of_locallyIntegrableOn hu₀loc
        hdc hdcs hdts
      simp only [sub_mul]
      rw [integral_sub i1 i2, weakDbarEq_skodaLift hDo hD'sub hG hpos hf i h hh j, hueq i h hh j]
      ring
    exact SGPT.Foundations.Analysis.Pending.exists_differentiableOn_ae_eq_of_weak_dbar hD'o hFloc
      (SGPT.Foundations.Analysis.Pending.OTChen.integral_mul_dbarDir_eq_zero_of_coord hFloc hcoord)
  choose H hHhol hHae using hHex
  have hHae' : ∀ᵐ x ∂(volume.restrict D'), ∀ i, skodaLift G f i x - u i x = H i x :=
    ae_all_iff.mpr hHae
  -- `f = ∑ Gᵢ Hᵢ` on `D'`
  have hid : EqOn f (fun z => ∑ i, G i z * H i z) D' := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hD'o (hf.continuousOn.mono hD'sub) ?_
    · filter_upwards [hHae', huker, ae_restrict_mem hD'o.measurableSet] with x hx hxk hxD
      simp_rw [← hx, mul_sub, Finset.sum_sub_distrib, hxk, sub_zero]
      exact (sum_mul_skodaLift hpos f (hD'sub hxD)).symm
    · exact continuousOn_finsetSum _ fun i _ =>
        ((hG i).continuousOn.mono hD'sub).mul (hHhol i).continuousOn
  -- the pointwise Pythagoras identity
  have hpyth : ∀ᵐ x ∂(volume.restrict D'), ∑ i, ‖H i x‖ ^ 2 =
      ‖f x‖ ^ 2 / generatorNormSq G x + ∑ i, ‖u i x‖ ^ 2 := by
    filter_upwards [hHae', huker, ae_restrict_mem hD'o.measurableSet] with x hx hxk hxD
    have hS := hpos x (hD'sub hxD)
    simp_rw [← hx]
    exact skoda_pythagoras hS hxk
  -- the estimate
  refine ⟨H, fun i => (hHhol i).mono hUD', fun z hz => hid (hUD' hz), ?_⟩
  have hexpΦ : ∀ z ∈ D, Real.exp (-Φ z) = generatorNormSq G z ^ (-p) := by
    intro z hz
    rw [Real.rpow_def_of_pos (hpos z hz)]
    simp only [hΦdef]; ring_nf
  have hu_int : Integrable (fun x => (∑ i, ‖u i x‖ ^ 2) * Real.exp (-(Φ x + lam₁ x)))
      (volume.restrict D') := by
    have h := integrable_finsetSum Finset.univ fun i _ =>
      integrable_sq_mul_exp_of_memLp hD'o hw₁ (hu2 i)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Finset.sum_mul]
  have hgI : ∫ x in D', g x * Real.exp (-(Φ x + lam₁ x)) ≤ t⁻¹ * I.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (by
      filter_upwards [ae_restrict_mem hD'o.measurableSet] with x hx
      exact mul_nonneg (hg0 x hx) (Real.exp_pos _).le) hgmeas]
    have h1 : ∫⁻ x in D', ENNReal.ofReal (g x * Real.exp (-(Φ x + lam₁ x))) ≤
        ENNReal.ofReal t⁻¹ * I :=
      (setLIntegral_mono' hD'o.measurableSet fun x hx =>
        ENNReal.ofReal_le_ofReal (hgle x hx)).trans hIt
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le)] at h2
  have hupart : ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p)) ≤
      ENNReal.ofReal ((1 + t) * t⁻¹) * I := by
    calc ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p))
        = ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * Real.exp (-(Φ z + lam₁ z))) := by
          refine setLIntegral_congr_fun hUo.measurableSet fun z hz => ?_
          rw [(hlamU z hz).1, add_zero, hexpΦ z (hD'sub (hUD' hz))]
      _ ≤ ∫⁻ z in D', ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * Real.exp (-(Φ z + lam₁ z))) :=
          lintegral_mono_set hUD'
      _ = ENNReal.ofReal (∫ z in D', (∑ i, ‖u i z‖ ^ 2) * Real.exp (-(Φ z + lam₁ z))) :=
          (ofReal_integral_eq_lintegral_ofReal hu_int (Filter.Eventually.of_forall fun x =>
            mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Real.exp_pos _).le)).symm
      _ ≤ ENNReal.ofReal ((1 + t) * (t⁻¹ * I.toReal)) :=
          ENNReal.ofReal_le_ofReal (hubd.trans (mul_le_mul_of_nonneg_left hgI (by linarith)))
      _ = ENNReal.ofReal ((1 + t) * t⁻¹) * I := by
          rw [← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hI]
  have hfmeas : AEMeasurable (fun z => ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1))))
      (volume.restrict U) := by
    have hc : ContinuousOn (fun z => ‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1))) U := by
      refine ((hf.continuousOn.mono (hUD'.trans hD'sub)).norm.pow 2).mul ?_
      exact ContinuousOn.rpow_const ((contDiffOn_generatorNormSq hDo hG).continuousOn.mono
        (hUD'.trans hD'sub)) fun z hz => Or.inl (hpos z (hD'sub (hUD' hz))).ne'
    exact (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hUo.measurableSet
  have hpythU := ae_restrict_of_ae_restrict_of_subset hUD' hpyth
  calc ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖H i z‖ ^ 2) * generatorNormSq G z ^ (-p))
      = ∫⁻ z in U, ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)) +
          (∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hpythU, ae_restrict_mem hUo.measurableSet] with z hz hzU
        have hS := hpos z (hD'sub (hUD' hzU))
        rw [hz, add_mul]
        congr 2
        rw [Real.rpow_neg hS.le, Real.rpow_neg hS.le, Real.rpow_add hS, Real.rpow_one]
        field_simp
    _ ≤ ∫⁻ z in U, (ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1))) +
          ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p))) :=
        lintegral_mono fun z => ENNReal.ofReal_add_le
    _ = (∫⁻ z in U, ENNReal.ofReal (‖f z‖ ^ 2 * generatorNormSq G z ^ (-(p + 1)))) +
          ∫⁻ z in U, ENNReal.ofReal ((∑ i, ‖u i z‖ ^ 2) * generatorNormSq G z ^ (-p)) :=
        lintegral_add_left' hfmeas _
    _ ≤ I + ENNReal.ofReal ((1 + t) * t⁻¹) * I := by
        gcongr
        exact lintegral_mono_set (hUD'.trans hD'sub)
    _ = ENNReal.ofReal (2 + 2 * n / (p - n)) * I := by
        have hval : 2 + 2 * (n : ℝ) / (p - n) = 1 + (1 + t) * t⁻¹ := by
          have hpn : p - n ≠ 0 := by linarith
          have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
          simp only [htdef]
          field_simp
          ring
        rw [hval, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
        ring

end SGPT.Okounkov.TranscendentalSkoda
