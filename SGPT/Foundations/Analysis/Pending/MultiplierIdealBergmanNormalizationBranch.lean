import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNormalization

set_option autoImplicit false

/-!
# A local Bergman branch from finite multiplier-integrable germs

This module uses the integration-ball containment retained by
`UniformWeightedL2Generators`.  Given actual local multiplier-integrability
witnesses for a finite family on a plurisubharmonic coordinate neighborhood,
it first intersects their witness domains, constructs the Demailly Bergman
branch on that common open set, then normalizes the family on the *same* ball
which defines the branch's weighted unit space.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNormalization

open FirstPass
open BergmanGenerators
open DemaillyApproximation
open DemaillyAnalyticType

noncomputable section

variable {n : ℕ}

/-- Keeping the uniform weighted-unit-ball estimate gives a logarithmic
generator bound for every finite normalized family on this Demailly branch. -/
theorem uniformWeightedL2Generators_exists_generatorLog_domination
    {W : Set (ComplexModel n)} {P : ComplexModel n → EReal}
    {z : ComplexModel n} {m : ℕ}
    (B : UniformWeightedL2Generators W P z m)
    {q : ℕ} {f : Fin q → ComplexModel n → ℂ}
    (hf : by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ i, f i ∈ bergmanUnitBall z B.radius
        (fun x => multiplierWeight (m : ℝ) (P x))) :
    ∃ A : ℝ, 0 < A ∧ ∀ y ∈ B.domain,
      generatorLog f y ≤ generatorLog B.generator y + (Real.log A : EReal) := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  set K' : ℝ := max B.uniform_constant 0 + 1 with hK'
  have hK'pos : 0 < K' := by
    rw [hK']
    linarith [le_max_right B.uniform_constant 0]
  set A : ℝ := ((q : ℝ) + 1) * K' with hA
  have hApos : 0 < A := by
    rw [hA]
    positivity
  refine ⟨A, hApos, fun y hy => ?_⟩
  apply QuasiEquisingularBergmanAtlas.generatorLog_le_add_of_generatorNormSq_le hApos
  have hsum : 0 ≤ ∑ l, ‖B.generator l y‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hKle : B.uniform_constant ≤ K' := by
    rw [hK']
    linarith [le_max_left B.uniform_constant 0]
  have hterm : ∀ i, ‖f i y‖ ^ 2 ≤ K' * ∑ l, ‖B.generator l y‖ ^ 2 := by
    intro i
    exact (B.uniform_domination (f i) (hf i) y hy).trans
      (mul_le_mul_of_nonneg_right hKle hsum)
  rw [generatorNormSq, generatorNormSq]
  calc
    (∑ i, ‖f i y‖ ^ 2) ≤
        ∑ _i : Fin q, K' * ∑ l, ‖B.generator l y‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (q : ℝ) * (K' * ∑ l, ‖B.generator l y‖ ^ 2) := by simp
    _ = ((q : ℝ) * K') * ∑ l, ‖B.generator l y‖ ^ 2 := by ring
    _ ≤ (((q : ℝ) + 1) * K') * ∑ l, ‖B.generator l y‖ ^ 2 := by
      gcongr
      nlinarith
    _ = A * ∑ l, ‖B.generator l y‖ ^ 2 := by rw [hA]

/-- A finite family of actual multiplier-integrable representatives produces
one Demailly Bergman branch on a common open subdomain.  The field
`B.double_radius_subset` is the crucial domain statement: it restricts every
given local `L²` witness to precisely the ball used by `B.bergmanUnitBall`.
-/
theorem exists_uniformBergmanBranch_normalizing_multiplierFamily
    {W : Set (ComplexModel n)} {P : ComplexModel n → EReal}
    {z : ComplexModel n} {m : ℕ} {q : ℕ} {f : Fin q → ComplexModel n → ℂ}
    (hW : IsOpen W) (hP : PlurisubharmonicOn P W) (hz : z ∈ W) (hm : 0 < m)
    (hf : ∀ i, MultiplierIntegrableAt P (m : ℝ) (f i) z volume) :
    ∃ (W' : Set (ComplexModel n)) (B : UniformWeightedL2Generators W' P z m)
      (s A : ℝ), IsOpen W' ∧ z ∈ W' ∧ W' ⊆ W ∧ 0 < s ∧ 0 < A ∧
      (by
        letI : MeasurableSpace (ComplexModel n) := borel _
        letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
        exact ∀ i, (fun x => (s : ℂ) * f i x) ∈ bergmanUnitBall z B.radius
          (fun x => multiplierWeight (m : ℝ) (P x))) ∧
      ∀ y ∈ B.domain,
        generatorLog (fun i x => (s : ℂ) * f i x) y ≤
          generatorLog B.generator y + (Real.log A : EReal) := by
  obtain ⟨W', hW', hzW', hW'W, hlocal⟩ :=
    exists_common_open_weightedL2On_of_multiplierIntegrableAt hW hz hf
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  obtain ⟨B⟩ := exists_uniform_weightedL2_generators W' P hW' (hP.mono hW'W) z hzW' m hm
  have hdiff : ∀ i, DifferentiableOn ℂ (f i) (ball z (2 * B.radius)) := fun i =>
    (hlocal i).1.mono B.double_radius_subset
  have hL2 : ∀ i, WeightedL2On P (m : ℝ) (f i) (ball z (2 * B.radius)) volume := fun i =>
    (weightedL2On_to_borelVolume (hlocal i).2).mono B.double_radius_subset
  obtain ⟨s, hs, hunit⟩ := exists_common_scale_mem_bergmanUnitBall_of_weightedL2On
    (z := z) (R := B.radius) (φ := P) (c := (m : ℝ)) hdiff hL2
  obtain ⟨A, hA, hdom⟩ :=
    uniformWeightedL2Generators_exists_generatorLog_domination B hunit
  exact ⟨W', B, s, A, hW', hzW', hW'W, hs, hA, hunit, hdom⟩

/-- At a manifold point, any finite family of members of the actual preferred
multiplier ideal can be read in the centre chart, transported across the
smooth local potential, and normalized on one newly constructed uniform local
Bergman patch.  The conclusion retains the patch, the common scalar, and the
precise Borel unit-ball statement; no coherence or global generation is used.
-/
theorem exists_uniformLocalBergmanPatch_normalizing_multiplierIdealFamily
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {θ : SmoothRealForm n M 2} {u : M → EReal}
    {m : ℕ} {q : ℕ} {g : Fin q → M → ℂ}
    (hu : IsThetaPshPotential θ u) (hm : 0 < m) (x : M)
    (hg : ∀ i, (FirstPass.HolomorphicIdealSheaves.multiplierIdeal (n := n)
      (m : ℝ) u).mem x (g i)) :
    ∃ (D : QuasiEquisingularBergmanAtlas.UniformLocalBergmanPatch θ u m)
      (s A : ℝ), x ∈ D.patch.source ∧ 0 < s ∧ 0 < A ∧
      (by
        letI : MeasurableSpace (ComplexModel n) := borel _
        letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
        exact ∀ i, (fun z => (s : ℂ) * g i (D.patch.chart.val.symm z)) ∈
          bergmanUnitBall D.center D.radius
            (fun z => multiplierWeight (m : ℝ) (D.weight z))) ∧
      ∀ y ∈ D.patch.domain,
        generatorLog (fun i z => (s : ℂ) * g i (D.patch.chart.val.symm z)) y ≤
          generatorLog D.patch.generator y + (Real.log A : EReal) := by
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨V, ρ, hzV, hρ, hpsh⟩ := hu.1 e (e.val x) hz
  let P : ComplexModel n → EReal := fun z => chartFunction u e z + (ρ z : EReal)
  have hraw : ∀ i, MultiplierIntegrableAt (chartFunction u e) (m : ℝ)
      (fun z => g i (e.val.symm z)) (e.val x) volume := by
    intro i
    simpa only [e] using (hg i).2
  have hPq : QuasiPlurisubharmonicAt P (e.val x) := by
    exact (hpsh (e.val x) hzV).quasiPlurisubharmonicAt
  have hbounded : BoundedRealGermAt ρ (e.val x) :=
    boundedRealGermAt_of_continuousAt
      ((hρ.2.2.1 (e.val x) hzV).contDiffAt (hρ.1.mem_nhds hzV)).continuousAt
  have htype : SameSingularityTypeAt P (chartFunction u e) (e.val x) :=
    sameSingularityTypeAt_of_bounded_remainder hbounded (by rfl)
  have hcorrected : ∀ i, MultiplierIntegrableAt P (m : ℝ)
      (fun z => g i (e.val.symm z)) (e.val x) volume := fun i =>
    multiplierIntegrableAt_of_moreSingularAt hPq htype.2 (hraw i)
  obtain ⟨W, B, s, A, hW, hzW, hWV, hs, hA, hunit, hdom⟩ :=
    exists_uniformBergmanBranch_normalizing_multiplierFamily hρ.1 hpsh hzV hm hcorrected
  let D : QuasiEquisingularBergmanAtlas.LocalBergmanPatch θ u m := {
    chart := e
    domain := ⟨B.domain, B.domain_open⟩
    domain_le_target := B.domain_subset.trans hWV |>.trans hρ.2.1
    potential := ρ
    localPotential := hρ.mono B.domain_open (B.domain_subset.trans hWV)
    plurisubharmonic := hpsh.mono (B.domain_subset.trans hWV)
    N := B.N
    generator := B.generator
    generator_analytic := B.generator_analytic
    generator_weighted := by
      let _ : MeasurableSpace (ComplexModel n) := borel _
      have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
      change ∀ l, WeightedL2On P m (B.generator l) B.domain volume
      exact B.generator_weighted
    domination := ⟨B.C, B.C_ne_top, B.pointwise_domination⟩
    analyticType := fun y hy =>
      hasAnalyticSingularityTypeAt_inv_nat_generatorLog hm B.domain_open
        B.generator_analytic hy }
  let D' : QuasiEquisingularBergmanAtlas.UniformLocalBergmanPatch θ u m := {
    patch := D
    center := e.val x
    radius := B.radius
    radius_pos := B.radius_pos
    center_mem_domain := B.center_mem_domain
    weight := P
    weight_eq_corrected := by rfl
    uniform_radius := B.uniform_radius
    uniform_radius_pos := B.uniform_radius_pos
    generator_unitBall := by simpa only [D, P] using B.generator_unitBall
    double_radius_subset_target := B.double_radius_subset.trans hWV |>.trans hρ.2.1
    domain_subset_uniformBall := B.domain_subset_uniformBall
    uniform_constant := B.uniform_constant
    uniform_domination := by
      let _ : MeasurableSpace (ComplexModel n) := borel _
      have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
      change ∀ f ∈ bergmanUnitBall (e.val x) B.radius
        (fun z => multiplierWeight (m : ℝ) (P z)), ∀ y ∈ B.domain,
          ‖f y‖ ^ 2 ≤ B.uniform_constant * ∑ l, ‖B.generator l y‖ ^ 2
      exact B.uniform_domination }
  refine ⟨D', s, A, ?_, hs, hA, ?_, ?_⟩
  · change x ∈ e.val.source ∩ e.val ⁻¹' B.domain
    exact ⟨hx, B.center_mem_domain⟩
  · simpa only [D', D, P] using hunit
  · intro y hy
    change y ∈ B.domain at hy
    change generatorLog (fun i z => (s : ℂ) * g i (e.val.symm z)) y ≤
      generatorLog B.generator y + (Real.log A : EReal)
    exact hdom y hy

end
end SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNormalization
