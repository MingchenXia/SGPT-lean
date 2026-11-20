import SGPT.Bergman.Quant2SharpSubmean
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.LiminfLimsup
import SGPT.Bergman.Quant2SharpSectionBound
import SGPT.Bergman.SourcePartialBergmanDensity

/-!
# Quant2SharpDensityLimsup

Limsup of the normalized Bergman density by Gaussian masses (signed curvature version).

Support for source `prop:smooth_weak_conv` (sharp upper bound `τ ≤ θ^n_{P_{θ,X}[φ]_I(v)}` for every
weak cluster point `τ` of the Bergman measures). Ported verbatim (modulo module names) from the
previous team's drafts under `wip/RESUME-20261109/KODAIRA-TRANSPORT/` and re-checked.
-/

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpGaussianMassLimits.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory Filter
open scoped Topology BigOperators

/-- Every signed scalar Gaussian has strictly positive mass on every actual
positive disk; this uses the existing Lebesgue measure, not a mass hypothesis. -/
theorem sourceSharp_disk_gaussian_mass_pos (d : ℝ) {R : ℝ} (hR : 0 < R) :
    0 < ∫ z in ball (0 : ℂ) R, Real.exp (-d * ‖z‖ ^ 2) := by
  have hp : 0 < (volume : Measure ℂ) (ball 0 R) :=
    isOpen_ball.measure_pos volume (nonempty_ball.mpr hR)
  have hne : NeZero ((volume : Measure ℂ).restrict (ball 0 R)) :=
    ⟨fun h => (ne_of_gt hp) (Measure.restrict_eq_zero.mp h)⟩
  have hc : Continuous (fun z : ℂ => Real.exp (-d * ‖z‖ ^ 2)) := by fun_prop
  exact integral_exp_pos (hμ := hne) ((hc.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) R)).mono_set ball_subset_closedBall)

/-- Signed scalar Gaussian mass is monotone under actual disk inclusion. -/
theorem sourceSharp_disk_gaussian_mass_mono (d : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ z in ball (0 : ℂ) a, Real.exp (-d * ‖z‖ ^ 2)) ≤
      ∫ z in ball (0 : ℂ) b, Real.exp (-d * ‖z‖ ^ 2) := by
  have hc : Continuous (fun z : ℂ => Real.exp (-d * ‖z‖ ^ 2)) := by fun_prop
  apply setIntegral_mono_set ((hc.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) b)).mono_set ball_subset_closedBall)
  · exact ae_of_all _ (fun z => (Real.exp_pos _).le)
  · exact ae_of_all _ (fun _ hz => ball_subset_ball hab hz)

/-- The true zero/negative-eigenvalue branch grows at least quadratically.
The total nonintegrable Bochner integral is never used as a denominator. -/
theorem sourceSharp_disk_gaussian_nonpositive_lower {d R : ℝ}
    (hd : d ≤ 0) (hR : 0 < R) :
    Real.pi * R ^ 2 ≤ ∫ z in ball (0 : ℂ) R, Real.exp (-d * ‖z‖ ^ 2) := by
  rw [sourceSharp_disk_gaussian_eq_radial d hR]
  exact sourceSharp_radial_factor_nonpositive hd hR.le

/-- On the positive spectral locus the actual finite polydisc Gaussian
masses converge to the already accepted exact SAME-eigenvalue Gaussian mass. -/
theorem sourceSharp_positive_gaussian_mass_tendsto {n : ℕ} {d : Fin n → ℝ}
    (hd : ∀ j, 0 < d j) :
    Tendsto (fun m : ℕ => ∫ z in ball (0 : Fin n → ℂ) ((m : ℝ) + 1),
      sourceDiagonalGaussian d z) atTop (𝓝 (∏ j, Real.pi / d j)) := by
  let g := sourceDiagonalGaussian d
  let T := fun m : ℕ => (ball (0 : Fin n → ℂ) ((m : ℝ) + 1)).indicator g
  have hg : Continuous g := by unfold g sourceDiagonalGaussian; fun_prop
  have hnonneg (z : Fin n → ℂ) : 0 ≤ g z := (Real.exp_pos _).le
  have hlim : ∀ᵐ z : Fin n → ℂ ∂volume, Tendsto (fun m => T m z) atTop (𝓝 (g z)) := by
    apply ae_of_all
    intro z
    obtain ⟨M, hM⟩ := exists_nat_gt ‖z‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop M] with m hm
    have hzm : ‖z‖ < (m : ℝ) + 1 := by
      have hMm : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hz : z ∈ ball (0 : Fin n → ℂ) ((m : ℝ) + 1) := by
      simpa only [mem_ball, dist_zero_right] using hzm
    simp only [T, indicator_of_mem hz]
  have ht := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (Fin n → ℂ))) g
    (fun m => hg.aestronglyMeasurable.indicator measurableSet_ball)
    (sourceDiagonalGaussian_integrable hd)
    (fun m => ae_of_all _ (fun z => by
      by_cases hz : z ∈ ball (0 : Fin n → ℂ) ((m : ℝ) + 1)
      · simp only [indicator_of_mem hz, Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
        exact le_rfl
      · simp only [indicator_of_notMem hz, norm_zero]
        exact hnonneg z)) hlim
  simpa only [T, integral_indicator measurableSet_ball, g, sourceDiagonalGaussian_integral hd] using ht
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpNonpositiveGaussianMass.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory Filter
open scoped Topology BigOperators
/-- One genuinely zero or negative direction forces the ACTUAL truncated
finite-product Gaussian mass to grow at least C R², with C>0 produced from
the other actual disk masses. No divergent total Bochner integral is used. -/
theorem sourceSharp_nonpositive_gaussian_mass_lower {n : ℕ} (d : Fin n → ℝ)
    (hbad : ∃ j, d j ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      C * R ^ 2 ≤ ∫ z in ball (0 : Fin n → ℂ) R, sourceDiagonalGaussian d z := by
  classical
  obtain ⟨j, hj⟩ := hbad
  let a := fun i : Fin n => ∫ s in ball (0 : ℂ) 1, Real.exp (-d i * ‖s‖ ^ 2)
  let C := Real.pi * ∏ i ∈ Finset.univ.erase j, a i
  have ha (i : Fin n) : 0 < a i := sourceSharp_disk_gaussian_mass_pos (d i) zero_lt_one
  have hprod : 0 < ∏ i ∈ Finset.univ.erase j, a i := Finset.prod_pos (fun i _ => ha i)
  refine ⟨C, mul_pos Real.pi_pos hprod, fun R hR => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let b := fun i : Fin n => ∫ s in ball (0 : ℂ) R, Real.exp (-d i * ‖s‖ ^ 2)
  have hm (i : Fin n) : a i ≤ b i := sourceSharp_disk_gaussian_mass_mono (d i) hR
  have hp : (∏ i ∈ Finset.univ.erase j, a i) ≤ ∏ i ∈ Finset.univ.erase j, b i :=
    Finset.prod_le_prod (fun i _ => (ha i).le) (fun i _ => hm i)
  have hfirst : Real.pi * R ^ 2 ≤ b j := sourceSharp_disk_gaussian_nonpositive_lower hj hRpos
  have hbj : 0 ≤ b j := (sourceSharp_disk_gaussian_mass_pos (d j) hRpos).le
  rw [sourceSharp_polydisc_gaussian_mass hRpos d]
  calc
    C * R ^ 2 = (Real.pi * R ^ 2) * (∏ i ∈ Finset.univ.erase j, a i) := by dsimp [C]; ring
    _ ≤ b j * (∏ i ∈ Finset.univ.erase j, b i) := mul_le_mul hfirst hp hprod.le hbj
    _ = ∏ i : Fin n, b i := Finset.mul_prod_erase Finset.univ b (Finset.mem_univ j)

/-- In the zero/negative spectral branch the finite Gaussian denominators
actually diverge to +infinity, rather than reading Lean's total integral0. -/
theorem sourceSharp_nonpositive_gaussian_mass_tendsto {n : ℕ} (d : Fin n → ℝ)
    (hbad : ∃ j, d j ≤ 0) :
    Tendsto (fun m : ℕ => ∫ z in ball (0 : Fin n → ℂ) ((m : ℝ) + 1),
      sourceDiagonalGaussian d z) atTop atTop := by
  obtain ⟨C, hC, hbound⟩ := sourceSharp_nonpositive_gaussian_mass_lower d hbad
  have hr : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).comp
      (tendsto_add_atTop_nat 1)
  have hg : Tendsto (fun m : ℕ => C * ((m : ℝ) + 1) ^ 2) atTop atTop :=
    (tendsto_const_mul_pow_atTop (by decide : (2 : ℕ) ≠ 0) hC).comp hr
  apply tendsto_atTop_mono _ hg
  intro m
  exact hbound _ (by have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith)
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpSignedLimsup.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Set Metric MeasureTheory Filter
open scoped Topology BigOperators ENNReal
/-- The numerical passage used by the original Bergman supremum: an actual
fixed-radius mass bound controls its limsup, without choosing maximizing
sections or inverting a nonintegrable total real integral. -/
theorem sourceSharp_limsup_le_inverse_mass {b : ℕ → ℝ≥0∞} {C M : ℝ}
    (h : ∀ᶠ k : ℕ in atTop, b k * ENNReal.ofReal (C * M) ≤ 1) :
    limsup b atTop ≤ (ENNReal.ofReal (C * M))⁻¹ := by
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [h] with k hk
  simpa only [one_div] using
    (ENNReal.le_div_iff_mul_le (Or.inr one_ne_zero) (Or.inl ENNReal.ofReal_ne_top)).mpr hk

/-- On the positive spectral locus, taking the actual increasing polydiscs
retains the SAME-eigenvalue Gaussian normalization. -/
theorem sourceSharp_positive_limsup_bound {n : ℕ} {b : ℕ → ℝ≥0∞}
    {d : Fin n → ℝ} (hd : ∀ j, 0 < d j) (C : ℝ)
    (h : ∀ R : ℝ, 0 < R → ∀ᶠ k : ℕ in atTop,
      b k * ENNReal.ofReal (C * (∫ z in ball (0 : Fin n → ℂ) R,
        sourceDiagonalGaussian d z)) ≤ 1) :
    limsup b atTop ≤ (ENNReal.ofReal (C * ∏ j, Real.pi / d j))⁻¹ := by
  have ht := (sourceSharp_positive_gaussian_mass_tendsto hd).const_mul C
  have ho := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  apply ge_of_tendsto (tendsto_inv_iff.mpr ho)
  apply Filter.Eventually.of_forall
  intro m
  exact sourceSharp_limsup_le_inverse_mass (h ((m : ℝ) + 1) (by positivity))

/-- Any actual zero or negative eigenvalue forces the normalized original
kernel upper limsup to zero. Only truncated finite masses are used. -/
theorem sourceSharp_nonpositive_limsup_zero {n : ℕ} {b : ℕ → ℝ≥0∞}
    (d : Fin n → ℝ) (hbad : ∃ j, d j ≤ 0) {C : ℝ} (hC : 0 < C)
    (h : ∀ R : ℝ, 0 < R → ∀ᶠ k : ℕ in atTop,
      b k * ENNReal.ofReal (C * (∫ z in ball (0 : Fin n → ℂ) R,
        sourceDiagonalGaussian d z)) ≤ 1) :
    limsup b atTop = 0 := by
  have ht := Tendsto.const_mul_atTop hC (sourceSharp_nonpositive_gaussian_mass_tendsto d hbad)
  have ho := ENNReal.tendsto_ofReal_atTop.comp ht
  have hi := tendsto_inv_iff.mpr ho
  have hb : limsup b atTop ≤ 0 := by
    apply ge_of_tendsto (by simpa only [ENNReal.inv_top] using hi)
    apply Filter.Eventually.of_forall
    intro m
    exact sourceSharp_limsup_le_inverse_mass (h ((m : ℝ) + 1) (by positivity))
  exact le_antisymm hb bot_le
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpDensityLimsup.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Set Metric MeasureTheory Filter
open scoped Topology BigOperators ENNReal
/-- Removing the actual chart-density error after the fixed-radius signed
Gaussian limit retains the exact chart density at the original center. -/
theorem sourceSharp_positive_density_limsup {n : ℕ} {b : ℕ → ℝ≥0∞}
    {d : Fin n → ℝ} (hd : ∀ j, 0 < d j) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ ε : ℝ, 0 < ε → ε < ρ → ∀ R : ℝ, 0 < R →
      ∀ᶠ k : ℕ in atTop,
        b k * ENNReal.ofReal (((ρ - ε) * Real.exp (-ε)) *
          (∫ z in ball (0 : Fin n → ℂ) R, sourceDiagonalGaussian d z)) ≤ 1) :
    limsup b atTop ≤ (ENNReal.ofReal (ρ * ∏ j, Real.pi / d j))⁻¹ := by
  let ε : ℕ → ℝ := fun m => ρ / ((m : ℝ) + 2)
  have hε (m : ℕ) : 0 < ε m ∧ ε m < ρ := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hden : 0 < (m : ℝ) + 2 := by linarith
    refine ⟨div_pos hρ hden, ?_⟩
    change ρ / ((m : ℝ) + 2) < ρ
    rw [div_lt_iff₀ hden]
    nlinarith
  have he : Tendsto ε atTop (𝓝 0) := by
    have ht := (tendsto_add_atTop_iff_nat 2).mpr (tendsto_const_div_atTop_nhds_zero_nat ρ)
    simpa only [ε, Nat.cast_add, Nat.cast_ofNat] using ht
  have ht : Tendsto (fun m => (ρ - ε m) * Real.exp (-ε m)) atTop (𝓝 ρ) := by
    simpa only [sub_zero, neg_zero, Real.exp_zero, mul_one, Function.comp_apply] using
      (tendsto_const_nhds (x := ρ) |>.sub he).mul
        (Real.continuous_exp.continuousAt.tendsto.comp he.neg)
  have ho := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (ht.mul_const (∏ j, Real.pi / d j))
  apply ge_of_tendsto (tendsto_inv_iff.mpr ho)
  apply Filter.Eventually.of_forall
  intro m
  exact sourceSharp_positive_limsup_bound hd ((ρ - ε m) * Real.exp (-ε m))
    (h (ε m) (hε m).1 (hε m).2)

/-- One fixed positive chart-density error already resolves every actual
zero/negative spectral branch; dimension-zero bad spectra are impossible. -/
theorem sourceSharp_nonpositive_density_limsup {n : ℕ} {b : ℕ → ℝ≥0∞}
    (d : Fin n → ℝ) (hbad : ∃ j, d j ≤ 0) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ ε : ℝ, 0 < ε → ε < ρ → ∀ R : ℝ, 0 < R →
      ∀ᶠ k : ℕ in atTop,
        b k * ENNReal.ofReal (((ρ - ε) * Real.exp (-ε)) *
          (∫ z in ball (0 : Fin n → ℂ) R, sourceDiagonalGaussian d z)) ≤ 1) :
    limsup b atTop = 0 := by
  apply sourceSharp_nonpositive_limsup_zero d hbad
    (C := (ρ - ρ / 2) * Real.exp (-(ρ / 2)))
  · exact mul_pos (by linarith) (Real.exp_pos _)
  · exact h (ρ / 2) (by linarith) (by linarith)
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalSignedUpper.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter Metric MeasureTheory WithLp
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.BernsteinMarkov SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal BigOperators
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
/-- Actual original Bergman kernels retain both signed spectral branches,
with the exact same chart density and no section maximizer. -/
theorem sourceSharp_original_Bergman_signed_limsup
    (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (x : X) (e : AtlasFrame L) (f : AtlasFrame T)
    (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet) (φ : X → EReal) :
    let c := complexChartAt (n := n) x
    let a := c.val x
    ∃ ρ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ρ c.val.target ∧
      Measure.map c.val (μ.restrict c.val.source) =
        (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)) ∧
      0 < ρ a ∧
    ∀ (S : ComplexModel n →ₗ[ℂ] ComplexModel n) (d : Fin n → ℝ),
      Complex.normSq (LinearMap.det S) = 1 →
      (∀ z : ComplexModel n,
        hermitianHessianQuadratic
          (fderiv ℝ (fderiv ℝ (sourcePhysicalChartWeight L v c e)) a) (S z) =
          -∑ j, d j * ‖z j‖ ^ 2) →
      ((∀ j, 0 < d j) → limsup (fun k : ℕ => ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) *
          sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
            ⟨x, Set.mem_univ x⟩) atTop ≤
        (ENNReal.ofReal (ρ a * ∏ j, Real.pi / d j))⁻¹) ∧
      ((∃ j, d j ≤ 0) → limsup (fun k : ℕ => ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) *
          sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
            ⟨x, Set.mem_univ x⟩) atTop = 0) := by
  intro c a
  obtain ⟨ρ,hρsm,hmap,hρ,hbound⟩ := sourceSharp_original_Bergman_fixed_radius_bound L T hL hT v hv μ hμ x e f he hf φ
  refine ⟨ρ,hρsm,hmap,hρ,fun S d hS hQ => ?_⟩
  let b : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) *
    sourcePartialBergmanDensity L T (wholeWeightedSubset v)
      (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
      ⟨x, Set.mem_univ x⟩
  have hb : ∀ ε : ℝ, 0 < ε → ε < ρ a → ∀ R : ℝ, 0 < R →
      ∀ᶠ k : ℕ in atTop,
        b k * ENNReal.ofReal (((ρ a - ε) * Real.exp (-ε)) *
          (∫ z in ball (0 : Fin n → ℂ) R, sourceDiagonalGaussian d z)) ≤ 1 := by
    intro ε hε hερ R hR
    have hC : 0 ≤ (ρ a - ε) * Real.exp (-ε) := mul_nonneg (sub_pos.mpr hερ).le (Real.exp_pos _).le
    filter_upwards [hbound S d hS hQ R ε hR hε hερ] with k hk
    rw [ENNReal.ofReal_mul hC]
    simpa only [b, c, a, mul_assoc, mul_left_comm, mul_comm] using hk
  exact ⟨fun hd => sourceSharp_positive_density_limsup hd hρ hb,
    fun hbad => sourceSharp_nonpositive_density_limsup d hbad hρ hb⟩
end SGPT.Bergman.SharpLocalUpper
end
end
