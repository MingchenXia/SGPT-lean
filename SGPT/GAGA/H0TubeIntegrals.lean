import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Integrals of powers of the distance to a complex submanifold


A set `C ⊆ ℂ^m` is a *local holomorphic graph of codimension `r`* at `p`
(`IsLocalGraphAt C r p`) if, in suitable complex linear coordinates `ℂ^m ≅ ℂ^{n'} × ℂ^r`, `C` is
near `p` the graph `{y = g(x)}` of a holomorphic map `g` (this is what it means for `C` to be a
complex submanifold of codimension `r` near `p`, by the implicit function theorem).

For such `C` (closed) and `p ∈ C`, with `r > 0` (so the real codimension is `2r`):

* `IsLocalGraphAt.exists_lintegral_infDist_rpow_lt_top`: `dist(·, C)^{2-2r}` is integrable on a
  ball around `p`;
* `IsLocalGraphAt.lintegral_infDist_rpow_eq_top`: `dist(·, C)^{-2r}` is not integrable on any
  ball around `p`.

Proof: `dist(Z, C)` is comparable to `|y - g(x)|` near `p` (`g` is Lipschitz near `p`), and the
shear `(x, y) ↦ (x, g(x) + y)` composed with the linear coordinates changes Lebesgue measure
only by a constant factor (`exists_shear_lintegral`: Haar uniqueness and translation invariance
in `y`); in the coordinates `(x, y)` the integrals are products of the volume of a ball in
`ℂ^{n'}` and `∫_{|y| < σ} |y|^s dy`, which is finite for `s = 2 - 2r > -2r` and infinite for
`s = -2r` (radial integration, `integrableOn_fun_norm_addHaar`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
open SGPT.Foundations.Analysis.FirstPass

/-! ### Radial integrals in `ℂ^r` -/

theorem finrank_real_complexModel (r : ℕ) : Module.finrank ℝ (ComplexModel r) = 2 * r := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]

/-- `|y|^{2-2r}` is integrable near `0` in `ℂ^r`. -/
theorem lintegral_ball_norm_rpow_lt_top {r : ℕ} (hr : 0 < r) (σ : ℝ) :
    ∫⁻ y in ball (0 : ComplexModel r) σ, ENNReal.ofReal (‖y‖ ^ (2 - 2 * (r : ℝ))) < ⊤ := by
  have hd : Module.finrank ℝ (ComplexModel r) = 2 * r := finrank_real_complexModel r
  have hint : IntegrableOn (fun y : ComplexModel r => ‖y‖ ^ (2 - 2 * (r : ℝ))) (ball 0 σ) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2 * (r : ℝ) - 2) ?_ ?_ ?_ ?_
    · rw [hd]; omega
    · rw [hd]; push_cast; linarith
    · refine Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
      exact le_of_eq (by ring_nf)
    · exact (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  exact hint.lintegral_lt_top

/-- `|y|^{-2r}` is not integrable near `0` in `ℂ^r`. -/
theorem lintegral_ball_norm_rpow_eq_top {r : ℕ} (hr : 0 < r) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ y in ball (0 : ComplexModel r) σ, ENNReal.ofReal (‖y‖ ^ (-(2 * (r : ℝ)))) = ⊤ := by
  have hd : Module.finrank ℝ (ComplexModel r) = 2 * r := finrank_real_complexModel r
  have : Nontrivial (ComplexModel r) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [hd]; omega
  by_contra hne
  have hint : IntegrableOn (fun y : ComplexModel r => ‖y‖ ^ (-(2 * (r : ℝ)))) (ball 0 σ) := by
    refine ⟨(continuous_norm.measurable.pow_const _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
      Real.rpow_nonneg (norm_nonneg _) _)]
    exact lt_top_iff_ne_top.mpr hne
  have h1 := (integrableOn_fun_norm_addHaar (volume : Measure (ComplexModel r))
    (f := fun t : ℝ => t ^ (-(2 * (r : ℝ)))) (r := σ)).mp hint
  rw [hd] at h1
  have h2 : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 σ) := by
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioo
    have ht0 : 0 < t := ht.1
    simp only [smul_eq_mul]
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
    congr 1
    have : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; ring
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hσ] at h2
  exact lt_irrefl _ h2

/-- The scaled version: `∫_{|y| < σ} (|y|/B)^{2-2r} < ∞`. -/
theorem lintegral_ball_norm_div_rpow_lt_top {r : ℕ} (hr : 0 < r) (σ : ℝ) {B : ℝ} (hB : 0 < B) :
    ∫⁻ y in ball (0 : ComplexModel r) σ, ENNReal.ofReal ((‖y‖ / B) ^ (2 - 2 * (r : ℝ))) < ⊤ := by
  have heq : ∀ y : ComplexModel r, ENNReal.ofReal ((‖y‖ / B) ^ (2 - 2 * (r : ℝ))) =
      ENNReal.ofReal ((B ^ (2 - 2 * (r : ℝ)))⁻¹) * ENNReal.ofReal (‖y‖ ^ (2 - 2 * (r : ℝ))) := by
    intro y
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg hB.le _)),
      Real.div_rpow (norm_nonneg _) hB.le, div_eq_inv_mul]
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_ball_norm_rpow_lt_top hr σ)

/-- The scaled version: `∫_{|y| < σ} (A |y|)^{-2r} = ∞`. -/
theorem lintegral_ball_mul_norm_rpow_eq_top {r : ℕ} (hr : 0 < r) {σ : ℝ} (hσ : 0 < σ) {A : ℝ}
    (hA : 0 < A) :
    ∫⁻ y in ball (0 : ComplexModel r) σ, ENNReal.ofReal ((A * ‖y‖) ^ (-(2 * (r : ℝ)))) = ⊤ := by
  have heq : ∀ y : ComplexModel r, ENNReal.ofReal ((A * ‖y‖) ^ (-(2 * (r : ℝ)))) =
      ENNReal.ofReal (A ^ (-(2 * (r : ℝ)))) * ENNReal.ofReal (‖y‖ ^ (-(2 * (r : ℝ)))) := by
    intro y
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hA.le _), Real.mul_rpow hA.le (norm_nonneg _)]
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_ball_norm_rpow_eq_top hr hσ,
    ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hA _)).ne']

/-! ### The shear change of variables -/

section Shear

variable {m n' r : ℕ}

/-- **Shear change of variables.** For linear coordinates `L : ℂ^m ≅ ℂ^{n'} × ℂ^r` and a
measurable `g : ℂ^{n'} → ℂ^r`, Lebesgue measure on `ℂ^m` is a constant multiple of the image of
Lebesgue measure under `(x, y) ↦ L⁻¹(x, g(x) + y)`. -/
theorem exists_shear_lintegral (L : ComplexModel m ≃L[ℂ] ComplexModel n' × ComplexModel r)
    {g : ComplexModel n' → ComplexModel r} (hg : Measurable g) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ f : ComplexModel m → ℝ≥0∞, Measurable f →
      ∫⁻ Z, f Z = c * ∫⁻ w : ComplexModel n' × ComplexModel r, f (L.symm (w.1, g w.1 + w.2)) := by
  set μ : Measure (ComplexModel m) := Measure.map L.symm volume with hμdef
  have : (volume : Measure (ComplexModel n' × ComplexModel r)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
  have : μ.IsAddHaarMeasure := L.symm.isAddHaarMeasure_map volume
  have hμ := Measure.isAddLeftInvariant_eq_smul (volume : Measure (ComplexModel m)) μ
  set c : ℝ≥0 := Measure.addHaarScalarFactor (volume : Measure (ComplexModel m)) μ with hc
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h0
    have hpos : 0 < (volume : Measure (ComplexModel m)) (ball 0 1) :=
      measure_ball_pos _ _ one_pos
    have hc' : c = 0 := by exact_mod_cast h0
    rw [hμ, hc', zero_smul] at hpos
    simp at hpos
  have hLm : Measurable L.symm := L.symm.continuous.measurable
  refine ⟨c, hc0, ENNReal.coe_ne_top, fun f hf => ?_⟩
  have h1 : ∫⁻ Z, f Z = (c : ℝ≥0∞) * ∫⁻ Z, f Z ∂μ := by
    conv_lhs => rw [hμ]
    rw [lintegral_smul_measure]
    rfl
  rw [h1, lintegral_map hf hLm]
  congr 1
  have hF : Measurable fun w : ComplexModel n' × ComplexModel r => f (L.symm w) := hf.comp hLm
  have hG : Measurable fun w : ComplexModel n' × ComplexModel r =>
      f (L.symm (w.1, g w.1 + w.2)) :=
    hf.comp (hLm.comp (measurable_fst.prodMk ((hg.comp measurable_fst).add measurable_snd)))
  rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable,
    lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun x => ?_
  exact (lintegral_add_left_eq_self (fun y => f (L.symm (x, y))) (g x)).symm

end Shear

/-! ### Local holomorphic graphs -/

variable {m : ℕ}

/-- `C ⊆ ℂ^m` is, near `p`, a complex submanifold of codimension `r` written as a graph: in
complex linear coordinates `L : ℂ^m ≅ ℂ^{n'} × ℂ^r`, for `Z` in a ball around `p`,
`Z ∈ C ↔ (L Z)₂ = g((L Z)₁)` for a map `g` that is holomorphic on a neighbourhood of `(L p)₁`. -/
def IsLocalGraphAt (C : Set (ComplexModel m)) (r : ℕ) (p : ComplexModel m) : Prop :=
  ∃ (n' : ℕ) (L : ComplexModel m ≃L[ℂ] ComplexModel n' × ComplexModel r) (ε : ℝ)
    (U' : Set (ComplexModel n')) (g : ComplexModel n' → ComplexModel r),
    0 < ε ∧ IsOpen U' ∧ (L p).1 ∈ U' ∧ DifferentiableOn ℂ g U' ∧
    ∀ Z ∈ ball p ε, (Z ∈ C ↔ (L Z).2 = g (L Z).1)

/-- Normalized data of a local graph: a measurable `g`, Lipschitz with constant `K` on a ball
`B((L p)₁, ρ)` on which it represents `C`. -/
theorem IsLocalGraphAt.exists_data {C : Set (ComplexModel m)} {r : ℕ} {p : ComplexModel m}
    (h : IsLocalGraphAt C r p) :
    ∃ (n' : ℕ) (L : ComplexModel m ≃L[ℂ] ComplexModel n' × ComplexModel r) (ε ρ K : ℝ)
      (g : ComplexModel n' → ComplexModel r),
      0 < ε ∧ 0 < ρ ∧ 0 ≤ K ∧ Measurable g ∧
      (∀ x ∈ ball (L p).1 ρ, ∀ x' ∈ ball (L p).1 ρ, ‖g x - g x'‖ ≤ K * ‖x - x'‖) ∧
      ∀ Z ∈ ball p ε, (L Z).1 ∈ ball (L p).1 ρ → (Z ∈ C ↔ (L Z).2 = g (L Z).1) := by
  obtain ⟨n', L, ε, U', g, hε, hU', hpU', hg, hC⟩ := h
  have hgC : ContDiffAt ℂ 1 g (L p).1 :=
    (contDiffAt_of_differentiableOn_complex hg hU' hpU').of_le (by exact_mod_cast le_top)
  obtain ⟨K, t, ht, hK⟩ := (hgC.restrict_scalars ℝ).exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hρt⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht (hU'.mem_nhds hpU'))
  set x₀ := (L p).1
  classical
  let g' : ComplexModel n' → ComplexModel r := (ball x₀ ρ).piecewise g fun _ => g x₀
  have hgcont : ContinuousOn g (ball x₀ ρ) :=
    hg.continuousOn.mono fun x hx => (hρt hx).2
  have hg'm : Measurable g' := hgcont.measurable_piecewise continuousOn_const
    isOpen_ball.measurableSet
  refine ⟨n', L, ε, ρ, K, g', hε, hρ, K.coe_nonneg, hg'm, fun x hx x' hx' => ?_,
    fun Z hZ hZ1 => ?_⟩
  · change ‖(ball x₀ ρ).piecewise g (fun _ => g x₀) x -
      (ball x₀ ρ).piecewise g (fun _ => g x₀) x'‖ ≤ K * ‖x - x'‖
    rw [Set.piecewise_eq_of_mem _ _ _ hx, Set.piecewise_eq_of_mem _ _ _ hx']
    exact hK.norm_sub_le (hρt hx).1 (hρt hx').1
  · change Z ∈ C ↔ (L Z).2 = (ball x₀ ρ).piecewise g (fun _ => g x₀) (L Z).1
    rw [Set.piecewise_eq_of_mem _ _ _ hZ1]
    exact hC Z hZ

/-- The squared-norm bound for the second coordinate. -/
theorem norm_snd_sub_le {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (a b : E × F) : ‖a.2 - b.2‖ ≤ ‖a - b‖ := norm_snd_le (a - b)

theorem norm_fst_sub_le {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (a b : E × F) : ‖a.1 - b.1‖ ≤ ‖a - b‖ := norm_fst_le (a - b)

/-- **`dist(·, C)^{2-2r}` is integrable near a point of a local graph of codimension
`r > 0`.** -/
theorem IsLocalGraphAt.exists_lintegral_infDist_rpow_lt_top {C : Set (ComplexModel m)} {r : ℕ}
    {p : ComplexModel m} (hp : p ∈ C) (h : IsLocalGraphAt C r p)
    (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ Z in ball p δ, ENNReal.ofReal (infDist Z C ^ (2 - 2 * (r : ℝ))) < ⊤ := by
  obtain ⟨n', L, ε, ρ, K, g, hε, hρ, hK, hgm, hgL, hC⟩ := h.exists_data
  set x₀ := (L p).1 with hx₀
  set A : ℝ := ‖(L : ComplexModel m →L[ℂ] ComplexModel n' × ComplexModel r)‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have hLle : ∀ Z Z' : ComplexModel m, ‖L Z - L Z'‖ ≤ A * ‖Z - Z'‖ := fun Z Z' => by
    rw [← map_sub]
    exact (L : ComplexModel m →L[ℂ] ComplexModel n' × ComplexModel r).le_opNorm _
  set B : ℝ := A * (1 + K) + 1 with hB
  have hB0 : 0 < B := by positivity
  set η : ℝ := min ε (ρ / (A + 1)) with hη
  have hη0 : 0 < η := lt_min hε (by positivity)
  set δ : ℝ := η / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hfirst : ∀ Z ∈ ball p η, (L Z).1 ∈ ball x₀ ρ := by
    intro Z hZ
    rw [mem_ball, dist_eq_norm]
    calc ‖(L Z).1 - x₀‖ ≤ ‖L Z - L p‖ := norm_fst_sub_le _ _
      _ ≤ A * ‖Z - p‖ := hLle Z p
      _ ≤ A * η := by gcongr; exact (mem_ball_iff_norm.mp hZ).le
      _ ≤ A * (ρ / (A + 1)) := by gcongr; exact min_le_right _ _
      _ < ρ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have hpη : p ∈ ball p η := mem_ball_self hη0
  have hpgraph : (L p).2 = g x₀ := (hC p (mem_ball_self hε) (hfirst p hpη)).mp hp
  -- the defect `y(Z) = (L Z)₂ - g((L Z)₁)`
  set y : ComplexModel m → ComplexModel r := fun Z => (L Z).2 - g (L Z).1 with hy
  have hkey : ∀ Z ∈ ball p δ, ∀ Z' ∈ C, ‖y Z‖ ≤ B * ‖Z - Z'‖ := by
    intro Z hZ Z' hZ'
    have hZη : Z ∈ ball p η := ball_subset_ball (by rw [hδ]; linarith) hZ
    by_cases hZ'η : Z' ∈ ball p η
    · have hgr : (L Z').2 = g (L Z').1 :=
        (hC Z' (ball_subset_ball (min_le_left _ _) hZ'η) (hfirst Z' hZ'η)).mp hZ'
      calc ‖y Z‖ = ‖((L Z).2 - (L Z').2) + (g (L Z').1 - g (L Z).1)‖ := by
            simp only [hy, hgr]; congr 1; abel
        _ ≤ ‖(L Z).2 - (L Z').2‖ + ‖g (L Z').1 - g (L Z).1‖ := norm_add_le _ _
        _ ≤ A * ‖Z - Z'‖ + K * (A * ‖Z - Z'‖) := by
            gcongr
            · exact (norm_snd_sub_le _ _).trans (hLle Z Z')
            · refine (hgL _ (hfirst Z' hZ'η) _ (hfirst Z hZη)).trans ?_
              gcongr
              rw [norm_sub_rev]
              exact (norm_fst_sub_le _ _).trans (hLle Z Z')
        _ ≤ B * ‖Z - Z'‖ := by rw [hB]; nlinarith [norm_nonneg (Z - Z')]
    · have hfar : δ ≤ ‖Z - Z'‖ := by
        have h1 : η ≤ ‖Z' - p‖ := by
          rw [mem_ball, dist_eq_norm, not_lt] at hZ'η; exact hZ'η
        have h2 : ‖Z - p‖ < δ := mem_ball_iff_norm.mp hZ
        have h3 : ‖Z' - p‖ ≤ ‖Z' - Z‖ + ‖Z - p‖ := by
          calc ‖Z' - p‖ = ‖(Z' - Z) + (Z - p)‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        have h4 : ‖Z' - Z‖ = ‖Z - Z'‖ := norm_sub_rev Z' Z
        rw [hδ] at h2 ⊢
        linarith
      have hZp : ‖Z - p‖ < δ := mem_ball_iff_norm.mp hZ
      calc ‖y Z‖ = ‖((L Z).2 - (L p).2) + (g x₀ - g (L Z).1)‖ := by
            simp only [hy, hpgraph]; congr 1; abel
        _ ≤ ‖(L Z).2 - (L p).2‖ + ‖g x₀ - g (L Z).1‖ := norm_add_le _ _
        _ ≤ A * ‖Z - p‖ + K * (A * ‖Z - p‖) := by
            gcongr
            · exact (norm_snd_sub_le _ _).trans (hLle Z p)
            · refine (hgL _ (mem_ball_self hρ) _ (hfirst Z hZη)).trans ?_
              gcongr
              rw [norm_sub_rev]
              exact (norm_fst_sub_le _ _).trans (hLle Z p)
        _ ≤ B * δ := by
            have : A * ‖Z - p‖ + K * (A * ‖Z - p‖) = A * (1 + K) * ‖Z - p‖ := by ring
            rw [this, hB]
            have h0 : 0 ≤ A * (1 + K) := by positivity
            nlinarith [norm_nonneg (Z - p)]
        _ ≤ B * ‖Z - Z'‖ := by gcongr
  have hCne : C.Nonempty := ⟨p, hp⟩
  set s : ℝ := 2 - 2 * (r : ℝ) with hs
  have hs0 : s ≤ 0 := by
    rw [hs]; have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  -- pointwise bound on `B(p, δ)`
  have hpt : ∀ Z ∈ ball p δ, infDist Z C ^ s ≤ (‖y Z‖ / B) ^ s := by
    intro Z hZ
    have hZη : Z ∈ ball p η := ball_subset_ball (by rw [hδ]; linarith) hZ
    by_cases hy0 : y Z = 0
    · have hZC : Z ∈ C := (hC Z (ball_subset_ball (min_le_left _ _) hZη) (hfirst Z hZη)).mpr
        (sub_eq_zero.mp hy0)
      rw [infDist_zero_of_mem hZC, hy0, norm_zero, zero_div]
    · have hle : ‖y Z‖ / B ≤ infDist Z C := by
        rw [le_infDist hCne]
        intro Z' hZ'
        rw [div_le_iff₀ hB0, dist_eq_norm, mul_comm]
        exact hkey Z hZ Z' hZ'
      exact Real.rpow_le_rpow_of_nonpos (div_pos (norm_pos_iff.mpr hy0) hB0) hle hs0
  -- change of variables
  obtain ⟨c, hc0, hctop, hcv⟩ := exists_shear_lintegral L hgm
  have hym : Measurable y := by
    have hLc : Continuous L := L.continuous
    exact ((continuous_snd.comp hLc).measurable).sub (hgm.comp (continuous_fst.comp hLc).measurable)
  set f : ComplexModel m → ℝ≥0∞ :=
    (ball p δ).indicator fun Z => ENNReal.ofReal ((‖y Z‖ / B) ^ s) with hfdef
  have hfm : Measurable f :=
    (ENNReal.measurable_ofReal.comp (((hym.norm).div_const B).pow_const s)).indicator
      isOpen_ball.measurableSet
  have hLsymm : ∀ w : ComplexModel n' × ComplexModel r,
      L (L.symm (w.1, g w.1 + w.2)) = (w.1, g w.1 + w.2) := fun w => L.apply_symm_apply _
  have hyshear : ∀ w : ComplexModel n' × ComplexModel r,
      y (L.symm (w.1, g w.1 + w.2)) = w.2 := by
    intro w
    simp only [hy, hLsymm]
    abel
  refine ⟨δ, hδ0, ?_⟩
  calc ∫⁻ Z in ball p δ, ENNReal.ofReal (infDist Z C ^ s)
      ≤ ∫⁻ Z in ball p δ, ENNReal.ofReal ((‖y Z‖ / B) ^ s) :=
        setLIntegral_mono' isOpen_ball.measurableSet fun Z hZ =>
          ENNReal.ofReal_le_ofReal (hpt Z hZ)
    _ = ∫⁻ Z, f Z := (lintegral_indicator isOpen_ball.measurableSet _).symm
    _ = c * ∫⁻ w : ComplexModel n' × ComplexModel r, f (L.symm (w.1, g w.1 + w.2)) :=
        hcv f hfm
    _ ≤ c * ∫⁻ w : ComplexModel n' × ComplexModel r,
          (ball x₀ ρ ×ˢ ball (0 : ComplexModel r) (B * δ)).indicator
            (fun w => ENNReal.ofReal ((‖w.2‖ / B) ^ s)) w := by
        gcongr with w
        by_cases hw : L.symm (w.1, g w.1 + w.2) ∈ ball p δ
        · have hwη : L.symm (w.1, g w.1 + w.2) ∈ ball p η :=
            ball_subset_ball (by rw [hδ]; linarith) hw
          have h1 : w.1 ∈ ball x₀ ρ := by
            have := hfirst _ hwη
            rwa [hLsymm] at this
          have h2 : w.2 ∈ ball (0 : ComplexModel r) (B * δ) := by
            rw [mem_ball_zero_iff]
            have := hkey _ hw p hp
            rw [hyshear] at this
            calc ‖w.2‖ ≤ B * ‖L.symm (w.1, g w.1 + w.2) - p‖ := this
              _ < B * δ := by gcongr; exact mem_ball_iff_norm.mp hw
          rw [hfdef, Set.indicator_of_mem hw, Set.indicator_of_mem (Set.mk_mem_prod h1 h2),
            hyshear]
        · rw [hfdef, Set.indicator_of_notMem hw]
          exact zero_le
    _ = c * (volume (ball x₀ ρ) *
          ∫⁻ y in ball (0 : ComplexModel r) (B * δ), ENNReal.ofReal ((‖y‖ / B) ^ s)) := by
        congr 1
        rw [lintegral_indicator (isOpen_ball.measurableSet.prod isOpen_ball.measurableSet),
          Measure.volume_eq_prod, ← Measure.prod_restrict,
          lintegral_prod (fun w : ComplexModel n' × ComplexModel r =>
            ENNReal.ofReal ((‖w.2‖ / B) ^ s)) ((ENNReal.measurable_ofReal.comp
              (((measurable_snd.norm).div_const B).pow_const s)).aemeasurable)]
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        rw [mul_comm]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hctop)
          (ENNReal.mul_lt_top measure_ball_lt_top ?_)
        rw [hs]
        exact lintegral_ball_norm_div_rpow_lt_top hr _ hB0

/-- **`dist(·, C)^{-2r}` is not integrable near a point of a closed local graph of codimension
`r > 0`.** -/
theorem IsLocalGraphAt.lintegral_infDist_rpow_eq_top {C : Set (ComplexModel m)} {r : ℕ}
    {p : ComplexModel m} (hCc : IsClosed C) (hp : p ∈ C) (h : IsLocalGraphAt C r p)
    (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ Z in ball p δ, ENNReal.ofReal (infDist Z C ^ (-(2 * (r : ℝ)))) = ⊤ := by
  obtain ⟨n', L, ε, ρ, K, g, hε, hρ, hK, hgm, hgL, hC⟩ := h.exists_data
  set x₀ := (L p).1 with hx₀
  set A : ℝ := ‖(L : ComplexModel m →L[ℂ] ComplexModel n' × ComplexModel r)‖ with hA
  set A' : ℝ := ‖(L.symm : ComplexModel n' × ComplexModel r →L[ℂ] ComplexModel m)‖ with hA'
  have hA0 : 0 ≤ A := norm_nonneg _
  have hA'0 : 0 ≤ A' := norm_nonneg _
  have hLle : ∀ Z Z' : ComplexModel m, ‖L Z - L Z'‖ ≤ A * ‖Z - Z'‖ := fun Z Z' => by
    rw [← map_sub]
    exact (L : ComplexModel m →L[ℂ] ComplexModel n' × ComplexModel r).le_opNorm _
  have hLsle : ∀ w w' : ComplexModel n' × ComplexModel r,
      ‖L.symm w - L.symm w'‖ ≤ A' * ‖w - w'‖ := fun w w' => by
    rw [← map_sub]
    exact (L.symm : ComplexModel n' × ComplexModel r →L[ℂ] ComplexModel m).le_opNorm _
  -- radius on which the first coordinate stays in the Lipschitz ball
  set η : ℝ := min ε (ρ / (A + 1)) with hη
  have hη0 : 0 < η := lt_min hε (by positivity)
  have hfirst : ∀ Z ∈ ball p η, (L Z).1 ∈ ball x₀ ρ := by
    intro Z hZ
    rw [mem_ball, dist_eq_norm]
    calc ‖(L Z).1 - x₀‖ ≤ ‖L Z - L p‖ := norm_fst_sub_le _ _
      _ ≤ A * ‖Z - p‖ := hLle Z p
      _ ≤ A * η := by gcongr; exact (mem_ball_iff_norm.mp hZ).le
      _ ≤ A * (ρ / (A + 1)) := by gcongr; exact min_le_right _ _
      _ < ρ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have hpgraph : (L p).2 = g x₀ := (hC p (mem_ball_self hε) (hfirst p (mem_ball_self hη0))).mp hp
  set y : ComplexModel m → ComplexModel r := fun Z => (L Z).2 - g (L Z).1 with hy
  -- the graph point over `Z` is close to `p`
  set D : ℝ := A' * (1 + K) * A + 1 with hD
  have hD0 : 0 < D := by positivity
  set δ₁ : ℝ := min η (ε / D) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hη0 (div_pos hε hD0)
  have hgraphpt : ∀ Z ∈ ball p δ₁, L.symm ((L Z).1, g (L Z).1) ∈ C := by
    intro Z hZ
    have hZη : Z ∈ ball p η := ball_subset_ball (min_le_left _ _) hZ
    have h1 := hfirst Z hZη
    set Z' := L.symm ((L Z).1, g (L Z).1) with hZ'
    have hLZ' : L Z' = ((L Z).1, g (L Z).1) := L.apply_symm_apply _
    have hZ'ε : Z' ∈ ball p ε := by
      rw [mem_ball, dist_eq_norm]
      have hp' : p = L.symm (x₀, g x₀) := by
        rw [← hpgraph]; exact (L.symm_apply_apply p).symm
      have hdiff : ‖((L Z).1, g (L Z).1) - (x₀, g x₀)‖ ≤ (1 + K) * (A * ‖Z - p‖) := by
        rw [Prod.norm_def]
        refine max_le ?_ ?_
        · simp only [Prod.fst_sub]
          have h3 : ‖(L Z).1 - x₀‖ ≤ A * ‖Z - p‖ := (norm_fst_sub_le (L Z) (L p)).trans (hLle Z p)
          have h5 : 0 ≤ A * ‖Z - p‖ := by positivity
          nlinarith
        · simp only [Prod.snd_sub]
          have h2 := hgL _ h1 _ (mem_ball_self hρ)
          have h3 : ‖(L Z).1 - x₀‖ ≤ A * ‖Z - p‖ := (norm_fst_sub_le (L Z) (L p)).trans (hLle Z p)
          have h4 : K * ‖(L Z).1 - x₀‖ ≤ K * (A * ‖Z - p‖) := by gcongr
          have h5 : 0 ≤ A * ‖Z - p‖ := by positivity
          nlinarith
      calc ‖Z' - p‖ = ‖L.symm ((L Z).1, g (L Z).1) - L.symm (x₀, g x₀)‖ := by rw [← hp']
        _ ≤ A' * ‖((L Z).1, g (L Z).1) - (x₀, g x₀)‖ := hLsle _ _
        _ ≤ A' * ((1 + K) * (A * ‖Z - p‖)) := by gcongr
        _ = (A' * (1 + K) * A) * ‖Z - p‖ := by ring
        _ ≤ D * ‖Z - p‖ := by gcongr; rw [hD]; linarith
        _ < D * (ε / D) := by
            gcongr
            exact lt_of_lt_of_le (mem_ball_iff_norm.mp hZ) (min_le_right _ _)
        _ = ε := by field_simp
    refine (hC Z' hZ'ε ?_).mpr ?_
    · rw [hLZ']; exact h1
    · rw [hLZ']
  have hupper : ∀ Z ∈ ball p δ₁, infDist Z C ≤ (A' + 1) * ‖y Z‖ := by
    intro Z hZ
    refine (infDist_le_dist_of_mem (hgraphpt Z hZ)).trans ?_
    rw [dist_eq_norm]
    have hZeq : Z = L.symm (L Z) := (L.symm_apply_apply Z).symm
    calc ‖Z - L.symm ((L Z).1, g (L Z).1)‖
        = ‖L.symm (L Z) - L.symm ((L Z).1, g (L Z).1)‖ := by rw [← hZeq]
      _ ≤ A' * ‖L Z - ((L Z).1, g (L Z).1)‖ := hLsle _ _
      _ = A' * ‖y Z‖ := by
          congr 1
          rw [Prod.norm_def]
          simp only [Prod.fst_sub, sub_self, norm_zero, Prod.snd_sub, hy]
          exact max_eq_right (norm_nonneg _)
      _ ≤ (A' + 1) * ‖y Z‖ := by gcongr; linarith
  set t : ℝ := -(2 * (r : ℝ)) with ht
  have ht0 : t ≤ 0 := by rw [ht]; have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hCne : C.Nonempty := ⟨p, hp⟩
  have hpt : ∀ Z ∈ ball p δ₁, ((A' + 1) * ‖y Z‖) ^ t ≤ infDist Z C ^ t := by
    intro Z hZ
    by_cases hy0 : y Z = 0
    · have htne : t ≠ 0 := by
        rw [ht]
        have : (0 : ℝ) < r := by exact_mod_cast hr
        linarith
      rw [hy0, norm_zero, mul_zero, Real.zero_rpow htne]
      exact Real.rpow_nonneg infDist_nonneg _
    · have hZη : Z ∈ ball p η := ball_subset_ball (min_le_left _ _) hZ
      have hZC : Z ∉ C := by
        intro hZC
        exact hy0 (sub_eq_zero.mpr ((hC Z (ball_subset_ball (min_le_left _ _) hZη)
          (hfirst Z hZη)).mp hZC))
      have hpos : 0 < infDist Z C := (hCc.notMem_iff_infDist_pos hCne).mp hZC
      exact Real.rpow_le_rpow_of_nonpos hpos (hupper Z hZ) ht0
  -- change of variables
  obtain ⟨c, hc0, hctop, hcv⟩ := exists_shear_lintegral L hgm
  have hym : Measurable y := by
    have hLc : Continuous L := L.continuous
    exact ((continuous_snd.comp hLc).measurable).sub (hgm.comp (continuous_fst.comp hLc).measurable)
  set δ₂ : ℝ := min δ δ₁ with hδ₂
  have hδ₂0 : 0 < δ₂ := lt_min hδ hδ₁0
  set f : ComplexModel m → ℝ≥0∞ :=
    (ball p δ₂).indicator fun Z => ENNReal.ofReal (((A' + 1) * ‖y Z‖) ^ t) with hfdef
  have hfm : Measurable f :=
    (ENNReal.measurable_ofReal.comp (((hym.norm).const_mul (A' + 1)).pow_const t)).indicator
      isOpen_ball.measurableSet
  have hLsymm : ∀ w : ComplexModel n' × ComplexModel r,
      L (L.symm (w.1, g w.1 + w.2)) = (w.1, g w.1 + w.2) := fun w => L.apply_symm_apply _
  have hyshear : ∀ w : ComplexModel n' × ComplexModel r,
      y (L.symm (w.1, g w.1 + w.2)) = w.2 := by
    intro w
    simp only [hy, hLsymm]
    abel
  -- a small box mapped into `B(p, δ₂)`
  set σ : ℝ := min ρ (δ₂ / (A' * (K + 2) + 1)) with hσ
  have hσ0 : 0 < σ := lt_min hρ (by positivity)
  have hbox : ∀ w : ComplexModel n' × ComplexModel r, w.1 ∈ ball x₀ σ →
      w.2 ∈ ball (0 : ComplexModel r) σ → L.symm (w.1, g w.1 + w.2) ∈ ball p δ₂ := by
    intro w h1 h2
    have h1' : ‖w.1 - x₀‖ < σ := mem_ball_iff_norm.mp h1
    have h2' : ‖w.2‖ < σ := mem_ball_zero_iff.mp h2
    have hw1ρ : w.1 ∈ ball x₀ ρ := ball_subset_ball (min_le_left _ _) h1
    have hp' : p = L.symm (x₀, g x₀) := by
      rw [← hpgraph]; exact (L.symm_apply_apply p).symm
    rw [mem_ball, dist_eq_norm, hp']
    have hdiff : ‖(w.1, g w.1 + w.2) - (x₀, g x₀)‖ ≤ (K + 2) * σ := by
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · simp only [Prod.fst_sub]
        nlinarith
      · simp only [Prod.snd_sub]
        have h3 := hgL _ hw1ρ _ (mem_ball_self hρ)
        calc ‖g w.1 + w.2 - g x₀‖ = ‖(g w.1 - g x₀) + w.2‖ := by congr 1; abel
          _ ≤ ‖g w.1 - g x₀‖ + ‖w.2‖ := norm_add_le _ _
          _ ≤ K * σ + σ := by
              gcongr
              exact h3.trans (by gcongr)
          _ ≤ (K + 2) * σ := by nlinarith
    calc ‖L.symm (w.1, g w.1 + w.2) - L.symm (x₀, g x₀)‖
        ≤ A' * ‖(w.1, g w.1 + w.2) - (x₀, g x₀)‖ := hLsle _ _
      _ ≤ A' * ((K + 2) * σ) := by gcongr
      _ < (A' * (K + 2) + 1) * σ := by nlinarith
      _ ≤ (A' * (K + 2) + 1) * (δ₂ / (A' * (K + 2) + 1)) := by
          gcongr; exact min_le_right _ _
      _ = δ₂ := by field_simp
  have hbig : ⊤ ≤ ∫⁻ Z in ball p δ, ENNReal.ofReal (infDist Z C ^ t) := by
    calc ⊤ = c * (volume (ball x₀ σ) *
          ∫⁻ y in ball (0 : ComplexModel r) σ, ENNReal.ofReal (((A' + 1) * ‖y‖) ^ t)) := by
          rw [ht, lintegral_ball_mul_norm_rpow_eq_top hr hσ0 (by linarith),
            ENNReal.mul_top (measure_ball_pos _ _ hσ0).ne', ENNReal.mul_top hc0]
      _ = c * ∫⁻ w : ComplexModel n' × ComplexModel r,
            (ball x₀ σ ×ˢ ball (0 : ComplexModel r) σ).indicator
              (fun w => ENNReal.ofReal (((A' + 1) * ‖w.2‖) ^ t)) w := by
          congr 1
          rw [lintegral_indicator (isOpen_ball.measurableSet.prod isOpen_ball.measurableSet),
            Measure.volume_eq_prod, ← Measure.prod_restrict,
            lintegral_prod (fun w : ComplexModel n' × ComplexModel r =>
              ENNReal.ofReal (((A' + 1) * ‖w.2‖) ^ t)) ((ENNReal.measurable_ofReal.comp
                (((measurable_snd.norm).const_mul (A' + 1)).pow_const t)).aemeasurable)]
          simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
          rw [mul_comm]
      _ ≤ c * ∫⁻ w : ComplexModel n' × ComplexModel r, f (L.symm (w.1, g w.1 + w.2)) := by
          gcongr with w
          by_cases hw : w ∈ ball x₀ σ ×ˢ ball (0 : ComplexModel r) σ
          · rw [Set.indicator_of_mem hw, hfdef, Set.indicator_of_mem (hbox w hw.1 hw.2),
              hyshear]
          · rw [Set.indicator_of_notMem hw]; exact zero_le
      _ = ∫⁻ Z, f Z := (hcv f hfm).symm
      _ = ∫⁻ Z in ball p δ₂, ENNReal.ofReal (((A' + 1) * ‖y Z‖) ^ t) :=
          lintegral_indicator isOpen_ball.measurableSet _
      _ ≤ ∫⁻ Z in ball p δ₂, ENNReal.ofReal (infDist Z C ^ t) :=
          setLIntegral_mono' isOpen_ball.measurableSet fun Z hZ =>
            ENNReal.ofReal_le_ofReal (hpt Z (ball_subset_ball (min_le_right _ _) hZ))
      _ ≤ ∫⁻ Z in ball p δ, ENNReal.ofReal (infDist Z C ^ t) :=
          lintegral_mono_set (ball_subset_ball (min_le_left _ _))
  exact top_le_iff.mp hbig

end SGPT.GAGA.H0
