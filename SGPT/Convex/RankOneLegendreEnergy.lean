import SGPT.Convex.BoundedLegendreVariation
import SGPT.Convex.MixedAlexandrovIdentities

set_option autoImplicit false

/-!
# Genuine rank-one affine Legendre energy

Actual one-slot mixed Alexandrov identities manufacture the affine measure
formula. The bounded integrated Legendre variation then identifies the actual
endpoint energy integral by a quadratic-increment rigidity argument.
-/

noncomputable section

namespace SGPT.Convex

open Set Filter MeasureTheory SGPT.PSH
open scoped Topology NNReal RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "B" => innerₗ E

/-- The literal finite affine profile of the two original functions. -/
def affineProfile (f g : RealConvexFunction E) (t : ℝ) (x : E) : ℝ :=
  (1 - t) * f.val x + t * g.val x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem convexOn_affineProfile (f g : RealConvexFunction E) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ConvexOn ℝ univ (affineProfile f g t) :=
  (ConvexOn.smul (sub_nonneg.mpr ht.2) f.property).add
    (ConvexOn.smul ht.1 g.property)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Actual bounded growth is preserved along the literal finite affine path. -/
theorem boundedGrowthClass_affineProfile {P : Set E} {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => (affineProfile f g t x : EReal)) ∈ BoundedGrowthClass B P := by
  have hcv := convexOn_affineProfile f g ht
  have hc : Continuous (affineProfile f g t) :=
    continuousOn_univ.mp (hcv.continuousOn isOpen_univ)
  have hproper : IsProper (fun x => (affineProfile f g t x : EReal)) :=
    ⟨isConvex_coe_iff.mpr hcv, ⟨0, EReal.coe_lt_top _⟩, fun _ => EReal.coe_ne_bot _⟩
  refine ⟨Or.inr (Or.inr ⟨hproper,
    (continuous_coe_real_ereal.comp hc).lowerSemicontinuous⟩), ?_⟩
  obtain ⟨C, hC⟩ := boundedGrowthPair_exists_abs_sub_le hf hg
  have hbound (x : E) : |affineProfile f g t x - f.val x| ≤ C := by
    have he : affineProfile f g t x - f.val x = t * (g.val x - f.val x) := by
      unfold affineProfile
      ring
    rw [he, abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans (by simpa using hC x)
  apply singularityEquiv_trans _ hf.2
  constructor
  · apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨C, fun x => ?_⟩
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith [(abs_le.mp (hbound x)).2]
  · apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨C, fun x => ?_⟩
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith [(abs_le.mp (hbound x)).1]

/-- The original one-slot mixed measure identifies the actual pure rank-one
measure of a nonnegative linear combination, including its singular parts. -/
theorem alexandrovMeasure_rankOne_linear_combination (μ : Measure E)
    [μ.IsAddHaarMeasure] (b : OrthonormalBasis (Fin 1) ℝ E)
    (c d : ℝ≥0) (f g : RealConvexFunction E) :
    alexandrovMeasure B μ (fun x => ((c * f.val x + d * g.val x : ℝ) : EReal)) =
      c • alexandrovMeasure B μ (fun x => (f.val x : EReal)) +
      d • alexandrovMeasure B μ (fun x => (g.val x : EReal)) := by
  have hup (k : RealConvexFunction E) :
      Function.update (fun _ : Fin 1 => f) (0 : Fin 1) k = fun _ => k := by
    funext i
    fin_cases i
    simp
  have h := mixedAlexandrovMeasure_update_linear_combination μ b
    (fun _ => f) (0 : Fin 1) c d f g
  simp only [hup, mixedAlexandrovMeasure_diagonal] at h
  exact h

private theorem integrable_gap_alexandrov (μ : Measure E) [μ.IsAddHaarMeasure]
    {P : Set E} (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f g k : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hk : (fun x => (k.val x : EReal)) ∈ BoundedGrowthClass B P) :
    Integrable (fun x => g.val x - f.val x)
      (alexandrovMeasure B μ (fun x => (k.val x : EReal))) := by
  have hfull := mem_fullMassClass_of_mem_boundedGrowthClass B hP hne hconv hk
  let : IsFiniteMeasure (alexandrovMeasure B μ (fun x => (k.val x : EReal))) := by
    refine ⟨?_⟩
    rw [alexandrovMeasure_univ_eq_body_of_mem_fullMassClass B hP hne hconv hfull]
    exact ENNReal.mul_lt_top (by simp) hP.measure_lt_top
  obtain ⟨C, hC⟩ := boundedGrowthPair_exists_abs_sub_le hf hg
  have hh : Measurable (fun x => g.val x - f.val x) :=
    (continuousOn_univ.mp (g.property.continuousOn isOpen_univ)).measurable.sub
      (continuousOn_univ.mp (f.property.continuousOn isOpen_univ)).measurable
  exact Integrable.of_bound hh.aestronglyMeasurable C
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x))

/-- The genuine original rank-one affine path has the actual affine signed
tangent integral; endpoint integrability is manufactured internally. -/
theorem integral_gap_affineProfile_rankOne (μ : Measure E) [μ.IsAddHaarMeasure]
    (b : OrthonormalBasis (Fin 1) ℝ E) {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, (g.val x - f.val x)
      ∂alexandrovMeasure B μ (fun x => (affineProfile f g t x : EReal))) =
        (1 - t) * (∫ x, (g.val x - f.val x)
          ∂alexandrovMeasure B μ (fun x => (f.val x : EReal))) +
        t * (∫ x, (g.val x - f.val x)
          ∂alexandrovMeasure B μ (fun x => (g.val x : EReal))) := by
  have ifh := integrable_gap_alexandrov μ hP hne hconv hf hg hf
  have igh := integrable_gap_alexandrov μ hP hne hconv hf hg hg
  let c : ℝ≥0 := ⟨1 - t, sub_nonneg.mpr ht.2⟩
  let d : ℝ≥0 := ⟨t, ht.1⟩
  rw [show (fun x => (affineProfile f g t x : EReal)) =
    (fun x => ((c * f.val x + d * g.val x : ℝ) : EReal)) from rfl,
    alexandrovMeasure_rankOne_linear_combination μ b c d f g,
    integral_add_measure ifh.smul_measure_nnreal igh.smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  rfl

private theorem endpoints_eq_of_quadratic_increment_bound (D : ℝ → ℝ) (K : ℝ)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |D t - D s| ≤ K * (t - s) ^ 2) : D 1 = D 0 := by
  have hbound (n : ℕ) : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |D t - D s| ≤ K * (1 / 2 : ℝ) ^ n * (t - s) ^ 2 := by
    induction n with
    | zero => simpa using hD
    | succ n ih =>
      intro s hs t ht
      let m : ℝ := (s + t) / 2
      have hm : m ∈ Icc (0 : ℝ) 1 := by
        dsimp only [m]
        constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      calc
        |D t - D s| = |(D t - D m) + (D m - D s)| := by ring_nf
        _ ≤ |D t - D m| + |D m - D s| := by
          apply abs_le.mpr
          constructor <;> linarith [neg_abs_le (D t - D m), neg_abs_le (D m - D s),
            le_abs_self (D t - D m), le_abs_self (D m - D s)]
        _ ≤ K * (1 / 2 : ℝ) ^ n * (t - m) ^ 2 +
            K * (1 / 2 : ℝ) ^ n * (m - s) ^ 2 :=
          add_le_add (ih m hm t ht) (ih s hs m hm)
        _ = K * (1 / 2 : ℝ) ^ (n + 1) * (t - s) ^ 2 := by
          rw [pow_succ]
          dsimp only [m]
          ring
  have ht := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  have htK : Tendsto (fun n : ℕ => K * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ht
  have hz : |D 1 - D 0| ≤ 0 := ge_of_tendsto htK
    (Eventually.of_forall (fun n => by
      simpa using hbound n 0 (by norm_num) 1 (by norm_num)))
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

/-- Actual affine rank-one MA variation identifies the genuine bounded Legendre
energy integral. Neither an energy identity nor a derivative certificate is a
premise; quadratic increments are proved from the actual endpoint measures. -/
theorem integral_conjugate_difference_eq_rankOneEnergy (μ : Measure E)
    [μ.IsAddHaarMeasure] (b : OrthonormalBasis (Fin 1) ℝ E) {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    {f g : RealConvexFunction E}
    (hf : (fun x => (f.val x : EReal)) ∈ BoundedGrowthClass B P)
    (hg : (fun x => (g.val x : EReal)) ∈ BoundedGrowthClass B P) :
    (∫ m in P, ((conjugate B (fun x => (f.val x : EReal)) m).toReal -
      (conjugate B (fun x => (g.val x : EReal)) m).toReal) ∂μ) =
        ((∫ x, (g.val x - f.val x)
          ∂alexandrovMeasure B μ (fun x => (f.val x : EReal))) +
         (∫ x, (g.val x - f.val x)
          ∂alexandrovMeasure B μ (fun x => (g.val x : EReal)))) / 2 := by
  let L : ℝ → ℝ := fun t => ∫ m in P,
    (conjugate B (fun x => (affineProfile f g t x : EReal)) m).toReal ∂μ
  let C : ℝ → ℝ := fun t => L 0 - L t
  let A : ℝ := ∫ x, (g.val x - f.val x)
    ∂alexandrovMeasure B μ (fun x => (f.val x : EReal))
  let D : ℝ := ∫ x, (g.val x - f.val x)
    ∂alexandrovMeasure B μ (fun x => (g.val x : EReal))
  let Q : ℝ → ℝ := fun t => A * t + (D - A) * t ^ 2 / 2
  have hfin : Module.finrank ℝ E = 1 := by
    simpa using Module.finrank_eq_card_basis b.toBasis
  have hi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Integrable (fun m =>
        (conjugate B (fun x => (affineProfile f g t x : EReal)) m).toReal)
        (μ.restrict P) :=
    integrable_conjugateToReal_of_mem_boundedGrowthClass μ hP hne hconv
      (f := ⟨affineProfile f g t, convexOn_affineProfile f g ht⟩)
      (boundedGrowthClass_affineProfile hf hg ht)
  have hvar (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (t - s) * ((1 - t) * A + t * D) ≤ C t - C s ∧
      C t - C s ≤ (t - s) * ((1 - s) * A + s * D) := by
    have hv := integral_conjugate_variation_bounds μ hP hne hconv
      (f := ⟨affineProfile f g s, convexOn_affineProfile f g hs⟩)
      (g := ⟨affineProfile f g t, convexOn_affineProfile f g ht⟩)
      (boundedGrowthClass_affineProfile hf hg hs)
      (boundedGrowthClass_affineProfile hf hg ht)
    have hgap : (fun x => affineProfile f g t x - affineProfile f g s x) =
        (fun x => (t - s) * (g.val x - f.val x)) := by
      funext x
      dsimp only [affineProfile]
      ring
    have hdiff : (∫ m in P,
        ((conjugate B (fun x => (affineProfile f g s x : EReal)) m).toReal -
          (conjugate B (fun x => (affineProfile f g t x : EReal)) m).toReal) ∂μ) =
        C t - C s := by
      rw [integral_sub (hi s hs) (hi t ht)]
      dsimp only [C, L]
      ring
    dsimp only at hv
    rw [hfin] at hv
    norm_num only [Nat.factorial_one, Nat.cast_one, one_mul] at hv
    rw [hgap, integral_const_mul, integral_const_mul,
      integral_gap_affineProfile_rankOne μ b hP hne hconv hf hg ht,
      integral_gap_affineProfile_rankOne μ b hP hne hconv hf hg hs,
      hdiff] at hv
    exact hv
  have hquad : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |(C t - Q t) - (C s - Q s)| ≤ (|D - A| / 2) * (t - s) ^ 2 := by
    intro s hs t ht
    have hv := hvar s hs t ht
    have hminus := mul_le_mul_of_nonneg_right (neg_abs_le (D - A)) (sq_nonneg (t - s))
    have hplus := mul_le_mul_of_nonneg_right (le_abs_self (D - A)) (sq_nonneg (t - s))
    dsimp only [Q]
    apply abs_le.mpr
    constructor <;> nlinarith [hv.1, hv.2]
  have he := endpoints_eq_of_quadratic_increment_bound (fun t => C t - Q t)
    (|D - A| / 2) hquad
  have hi0 := hi 0 (by norm_num)
  have hi1 := hi 1 (by norm_num)
  simp only [affineProfile, sub_zero, one_mul, zero_mul, add_zero] at hi0
  simp only [affineProfile, sub_self, zero_mul, one_mul, zero_add] at hi1
  rw [integral_sub hi0 hi1]
  dsimp only [C, Q, L, affineProfile] at he
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add,
    one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div] at he
  dsimp only [A, D] at he ⊢
  linarith

end SGPT.Convex
