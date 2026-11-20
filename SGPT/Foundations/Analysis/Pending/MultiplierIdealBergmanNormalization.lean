import SGPT.Foundations.Analysis.Pending.UniformLocalBergmanPatch
import SGPT.Foundations.Analysis.Pending.LocalBergmanMeasureTransport

set_option autoImplicit false

/-!
# Finite multiplier-germ families normalized for a local Bergman patch

The local Demailly construction controls every member of a *unit* weighted
Bergman ball.  This file records the quantitative finite-family step needed
to feed independently given local multiplier representatives into that
construction: a finite family with finite weighted masses admits one common
positive scalar making all of its members unit-ball functions.  The subsequent
lemmas make the Borel measure convention and the common domain explicit.

No coherence or global generation is used here: the input is an actual finite
family of holomorphic representatives with actual weighted `L²` witnesses.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNormalization

open FirstPass
open BergmanGenerators

noncomputable section

variable {n : ℕ}

/-- The converse of the existing Borel-to-preferred local mass transport.
It passes through the same Euclidean model, so the preferred `WithLp` volume
and the local Borel volume are never identified by instance equality. -/
theorem weightedL2On_to_borelVolume
    {φ : ComplexModel n → EReal} {c : ℝ}
    {f : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (h : WeightedL2On φ c f U volume) :
    by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact WeightedL2On φ c f U volume := by
  have hcommon : WeightedL2On (φ ∘ (localBergmanShiftZero n).symm) c
      (f ∘ (localBergmanShiftZero n).symm)
      ((localBergmanShiftZero n) '' U) volume := by
    let e : ComplexModel n ≃ᵐ EuclideanSpace ℂ (Fin n ⊕ Fin 0) :=
      (localBergmanShiftZero n).toMeasurableEquiv
    have he : MeasurePreserving e volume volume := by
      change MeasurePreserving (localBergmanShiftZero n) volume volume
      exact LinearIsometryEquiv.measurePreserving (localBergmanShiftZero n)
    exact weightedL2On_map_measurableEquiv e he h
  have hback : by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact WeightedL2On
        ((φ ∘ (localBergmanShiftZero n).symm) ∘ (localBergmanShiftZero n)) c
        ((f ∘ (localBergmanShiftZero n).symm) ∘ (localBergmanShiftZero n))
        ((fun x : ComplexModel n => x) '' U) volume := by
    let _ : MeasurableSpace (ComplexModel n) := borel _
    have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
    let e : ComplexModel n ≃ᵐ EuclideanSpace ℂ (Fin n ⊕ Fin 0) :=
      (localBergmanShiftZero n).toMeasurableEquiv
    have he : MeasurePreserving e volume volume := by
      change MeasurePreserving (localBergmanShiftZero n) volume volume
      exact LinearIsometryEquiv.measurePreserving (localBergmanShiftZero n)
    have hback' := weightedL2On_map_measurableEquiv e.symm he.symm hcommon
    simpa only [e, LinearIsometryEquiv.coe_toMeasurableEquiv,
      LinearIsometryEquiv.coe_symm_toMeasurableEquiv, MeasurableEquiv.symm_symm,
      Function.comp_apply, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.apply_symm_apply, Set.image_image] using hback'
  have hφ : (φ ∘ (localBergmanShiftZero n).symm) ∘
      (localBergmanShiftZero n) = φ := by
    funext z
    change φ ((localBergmanShiftZero n).symm ((localBergmanShiftZero n) z)) = φ z
    rw [LinearIsometryEquiv.symm_apply_apply]
  have hf : (f ∘ (localBergmanShiftZero n).symm) ∘
      (localBergmanShiftZero n) = f := by
    funext z
    change f ((localBergmanShiftZero n).symm ((localBergmanShiftZero n) z)) = f z
    rw [LinearIsometryEquiv.symm_apply_apply]
  simpa only [hφ, hf, Set.image_id'] using hback

/-- The preceding transport preserves each explicit local witness and hence
also transports preferred `MultiplierIntegrableAt` data into the Borel measure
convention required by `bergmanUnitBall`. -/
theorem multiplierIntegrableAt_to_borelVolume
    {φ : ComplexModel n → EReal} {c : ℝ}
    {f : ComplexModel n → ℂ} {x : ComplexModel n}
    (h : MultiplierIntegrableAt φ c f x volume) :
    by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact MultiplierIntegrableAt φ c f x volume := by
  rcases h with ⟨hc, U, hU, hx, hf, hL2⟩
  exact ⟨hc, U, hU, hx, hf, weightedL2On_to_borelVolume hL2⟩

/-- Finitely many actual multiplier-integrable representatives at one point
have a common ball of definition.  This uses the finite intersection of their
given open witness domains, then shrinks once to a metric ball; it does not
assume a common representative or invoke coherence. -/
theorem exists_common_ball_weightedL2On_of_multiplierIntegrableAt
    {φ : ComplexModel n → EReal} {c : ℝ} {z : ComplexModel n}
    {q : ℕ} {f : Fin q → ComplexModel n → ℂ}
    (h : ∀ i, MultiplierIntegrableAt φ c (f i) z volume) :
    ∃ R : ℝ, 0 < R ∧ ∀ i,
      DifferentiableOn ℂ (f i) (ball z (2 * R)) ∧
      WeightedL2On φ c (f i) (ball z (2 * R)) volume := by
  have hdata : ∀ i, ∃ U : Set (ComplexModel n), IsOpen U ∧ z ∈ U ∧
      DifferentiableOn ℂ (f i) U ∧ WeightedL2On φ c (f i) U volume :=
    fun i => (h i).2
  choose U hU hz hdiff hL2 using hdata
  let W : Set (ComplexModel n) := ⋂ i, U i
  have hWopen : IsOpen W := by
    exact isOpen_iInter_of_finite hU
  have hzW : z ∈ W := by
    exact Set.mem_iInter.mpr hz
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds hzW)
  set R : ℝ := ε / 2
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, fun i => ?_⟩
  have hball : ball z (2 * R) ⊆ U i := by
    rw [show 2 * R = ε by dsimp [R]; ring]
    exact hεW.trans (Set.iInter_subset U i)
  exact ⟨(hdiff i).mono hball, (hL2 i).mono hball⟩

/-- The common ball just obtained may be read in the Borel measure convention
of the Bergman unit ball by applying the explicit measure transport separately
to every witness. -/
theorem exists_common_borel_ball_weightedL2On_of_multiplierIntegrableAt
    {φ : ComplexModel n → EReal} {c : ℝ} {z : ComplexModel n}
    {q : ℕ} {f : Fin q → ComplexModel n → ℂ}
    (h : ∀ i, MultiplierIntegrableAt φ c (f i) z volume) :
    ∃ R : ℝ, 0 < R ∧ ∀ i,
      DifferentiableOn ℂ (f i) (ball z (2 * R)) ∧
      (by
        letI : MeasurableSpace (ComplexModel n) := borel _
        letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
        exact WeightedL2On φ c (f i) (ball z (2 * R)) volume) := by
  obtain ⟨R, hR, hball⟩ := exists_common_ball_weightedL2On_of_multiplierIntegrableAt h
  refine ⟨R, hR, fun i => ⟨(hball i).1, ?_⟩⟩
  exact weightedL2On_to_borelVolume (hball i).2

/-- If the weight is plurisubharmonic on an explicitly supplied open set,
finitely many multiplier-integrable representatives admit one common open
subdomain inside it.  This records both the holomorphic and weighted `L²`
witnesses before a Demailly construction chooses its own integration ball. -/
theorem exists_common_open_weightedL2On_of_multiplierIntegrableAt
    {φ : ComplexModel n → EReal} {c : ℝ} {z : ComplexModel n}
    {q : ℕ} {f : Fin q → ComplexModel n → ℂ} {V : Set (ComplexModel n)}
    (hV : IsOpen V) (hzV : z ∈ V)
    (h : ∀ i, MultiplierIntegrableAt φ c (f i) z volume) :
    ∃ W : Set (ComplexModel n), IsOpen W ∧ z ∈ W ∧ W ⊆ V ∧ ∀ i,
      DifferentiableOn ℂ (f i) W ∧ WeightedL2On φ c (f i) W volume := by
  have hdata : ∀ i, ∃ U : Set (ComplexModel n), IsOpen U ∧ z ∈ U ∧
      DifferentiableOn ℂ (f i) U ∧ WeightedL2On φ c (f i) U volume :=
    fun i => (h i).2
  choose U hU hz hdiff hL2 using hdata
  let W : Set (ComplexModel n) := V ∩ ⋂ i, U i
  have hW : IsOpen W := hV.inter (isOpen_iInter_of_finite hU)
  have hzW : z ∈ W := ⟨hzV, Set.mem_iInter.mpr hz⟩
  refine ⟨W, hW, hzW, inter_subset_left, fun i => ?_⟩
  exact ⟨(hdiff i).mono (inter_subset_right.trans (Set.iInter_subset U i)),
    (hL2 i).mono (inter_subset_right.trans (Set.iInter_subset U i))⟩

/-- A common finite real upper bound for a finite family of finite extended
nonnegative numbers.  The slack `+ 1` keeps the eventual normalizing scalar
strictly positive even for the zero family. -/
theorem exists_common_real_bound_of_finite
    {q : ℕ} {I : Fin q → ℝ≥0∞} (hI : ∀ i, I i < ∞) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i, I i ≤ ENNReal.ofReal A := by
  classical
  let A : ℝ := ∑ j, (I j).toReal + 1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hsum : 0 ≤ ∑ j, (I j).toReal :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    linarith
  refine ⟨A, hA0, fun i => ?_⟩
  apply (ENNReal.le_ofReal_iff_toReal_le (ne_of_lt (hI i)) hA0).mpr
  dsimp [A]
  have hsum : (I i).toReal ≤ ∑ j, (I j).toReal :=
    Finset.single_le_sum (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)
  linarith

/-- A finite family whose weighted squared norms share a finite real bound can
be normalized by one positive scalar into the weighted Bergman unit ball. -/
theorem exists_common_scale_mem_bergmanUnitBall_of_weighted_bounds
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    {z : ComplexModel n} {R A : ℝ} {w : ComplexModel n → ℝ≥0∞}
    {q : ℕ} {f : Fin q → ComplexModel n → ℂ}
    (hA0 : 0 ≤ A)
    (hfdiff : ∀ i, DifferentiableOn ℂ (f i) (ball z (2 * R)))
    (hbound : ∀ i, ∫⁻ x in ball z (2 * R), ENNReal.ofReal (‖f i x‖ ^ 2) * w x ≤
      ENNReal.ofReal A) :
    ∃ s : ℝ, 0 < s ∧ ∀ i,
      (fun x => (s : ℂ) * f i x) ∈ bergmanUnitBall z R w := by
  set s : ℝ := (A + 1)⁻¹ with hs
  have hspos : 0 < s := by
    rw [hs]
    positivity
  refine ⟨s, hspos, fun i => ⟨(hfdiff i).const_mul _, ?_⟩⟩
  have hpoint : ∀ x, ENNReal.ofReal (‖(s : ℂ) * f i x‖ ^ 2) * w x =
      ENNReal.ofReal (s ^ 2) * (ENNReal.ofReal (‖f i x‖ ^ 2) * w x) := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hspos.le, mul_pow,
      ENNReal.ofReal_mul (sq_nonneg s)]
    ring
  simp_rw [hpoint]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    ENNReal.ofReal (s ^ 2) * ∫⁻ x in ball z (2 * R),
        ENNReal.ofReal (‖f i x‖ ^ 2) * w x
      ≤ ENNReal.ofReal (s ^ 2) * ENNReal.ofReal A := by
        exact mul_le_mul_of_nonneg_left (hbound i) bot_le
    _ = ENNReal.ofReal (s ^ 2 * A) := by
      rw [ENNReal.ofReal_mul (sq_nonneg s)]
    _ ≤ 1 := ENNReal.ofReal_le_one.mpr (by
      rw [hs]
      have hden : 0 < A + 1 := by linarith
      rw [inv_pow, ← div_eq_inv_mul]
      apply (div_le_one₀ (sq_pos_of_pos hden)).mpr
      nlinarith)

/-- The preceding normalization applies directly to finitely many actual
weighted `L²` witnesses on the common Bergman ball.  Both the holomorphic
domain and the measure are parameters; in particular this theorem does not
silently replace a germwise neighborhood by a global one. -/
theorem exists_common_scale_mem_bergmanUnitBall_of_weightedL2On
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    {z : ComplexModel n} {R c : ℝ} {φ : ComplexModel n → EReal}
    {q : ℕ} {f : Fin q → ComplexModel n → ℂ}
    (hfdiff : ∀ i, DifferentiableOn ℂ (f i) (ball z (2 * R)))
    (hL2 : ∀ i, WeightedL2On φ c (f i) (ball z (2 * R)) volume) :
    ∃ s : ℝ, 0 < s ∧ ∀ i,
      (fun x => (s : ℂ) * f i x) ∈ bergmanUnitBall z R
        (fun x => multiplierWeight c (φ x)) := by
  obtain ⟨A, hA0, hA⟩ := exists_common_real_bound_of_finite
    (I := fun i => ∫⁻ x in ball z (2 * R), multiplierDensity φ c (f i) x)
    fun i => (hL2 i).2
  apply exists_common_scale_mem_bergmanUnitBall_of_weighted_bounds hA0 hfdiff
  intro i
  simpa only [multiplierDensity] using hA i

/-- On one `UniformLocalBergmanPatch`, a finite family with explicit Borel
weighted `L²` evidence on the patch's *whole* Bergman ball has one common
normalization.  The retained uniform estimate then controls the logarithmic
generator norm of that normalized family by the exact generator family defining
the patch branch. -/
theorem UniformLocalBergmanPatch.exists_normalized_generatorLog_domination
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : QuasiEquisingularBergmanAtlas.UniformLocalBergmanPatch θ u m)
    {q : ℕ} {f : Fin q → ComplexModel n → ℂ}
    (hfdiff : ∀ i, DifferentiableOn ℂ (f i) (ball D.center (2 * D.radius)))
    (hL2 : by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ i, WeightedL2On D.weight (m : ℝ) (f i)
        (ball D.center (2 * D.radius)) volume) :
    ∃ s A : ℝ, 0 < s ∧ 0 < A ∧
      (by
        letI : MeasurableSpace (ComplexModel n) := borel _
        letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
        exact ∀ i, (fun x => (s : ℂ) * f i x) ∈ bergmanUnitBall D.center D.radius
          (fun x => multiplierWeight (m : ℝ) (D.weight x))) ∧
      ∀ y ∈ D.patch.domain,
        generatorLog (fun i x => (s : ℂ) * f i x) y ≤
          generatorLog D.patch.generator y + (Real.log A : EReal) := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  obtain ⟨s, hs, hunit⟩ := exists_common_scale_mem_bergmanUnitBall_of_weightedL2On
    (z := D.center) (R := D.radius) (φ := D.weight) (c := (m : ℝ)) hfdiff hL2
  obtain ⟨A, hA, hdom⟩ := D.exists_generatorLog_domination hunit
  exact ⟨s, A, hs, hA, hunit, hdom⟩

end
end SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNormalization
