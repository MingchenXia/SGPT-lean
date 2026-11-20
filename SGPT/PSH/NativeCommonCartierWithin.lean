import SGPT.PSH.NativeCommonPrimeLogarithms
import SGPT.PSH.LocalIntegralGeometricQDivisor
import SGPT.PSH.CartierOpenRestriction

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves AnalyticGermDecomposition InvertibleIdealQuotient
open HironakaEffectiveDivisorSum
open scoped Topology Manifold ContDiff

private theorem full_cartier_eq_of_generators_unit {n : ℕ} {Z : Type*}
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    (D E : EffectiveDivisor n Z) (g h v : Z → ℂ)
    (hD : ∀ y b, D.ideal.mem y b ↔ IsInSpanAt (n := n) (· = g) y b)
    (hE : ∀ y b, E.ideal.mem y b ↔ IsInSpanAt (n := n) (· = h) y b)
    (hv : ∀ y, HolomorphicAt n v y) (hne : ∀ y, v y ≠ 0)
    (hfactor : ∀ y, g y = h y * v y) : D = E := by
  apply effectiveDivisor_eq_of_ideal_eq
  apply GermIdeal.ext
  funext y b
  apply propext
  rw [hD y b, hE y b]
  constructor
  · intro hb
    obtain ⟨hbhol, t, ht, hbt⟩ := isInSpanAt_eq_iff.mp hb
    apply isInSpanAt_eq_iff.mpr
    refine ⟨hbhol, (fun z => t z * v z), ht.mul (hv y), ?_⟩
    filter_upwards [hbt] with z hz
    rw [hz, hfactor z]
    ring
  · intro hb
    obtain ⟨hbhol, t, ht, hbt⟩ := isInSpanAt_eq_iff.mp hb
    have hinv : HolomorphicAt n (fun z => (v z)⁻¹) y := by
      filter_upwards [hv y] with z hz
      exact hz.inv (hne z)
    apply isInSpanAt_eq_iff.mpr
    refine ⟨hbhol, (fun z => t z * (v z)⁻¹), ht.mul hinv, ?_⟩
    filter_upwards [hbt] with z hz
    rw [hz, hfactor z]
    field_simp [hne z]

universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- ORIGINAL native equation and bounded germ produce one prescribed open
with genuine DISTINCT reduced primes, literal unit/product, FULL finite
Cartier equality and a bound/log identity on ALL of the SAME open. -/
theorem exists_native_common_open_cartier_prime_logarithms_within
    (D : EffectiveDivisor (m + 1) M) (x : M) (g : M → ℂ)
    (hgen : ∀ᶠ y in 𝓝 x, HolomorphicAt (m + 1) g y ∧ ∀ b,
      D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b)
    (c : ℚ) (hc : 0 < c) (u : M → EReal) (R : M → ℝ) (hR : BoundedRealGermAt R x)
    (hu : u =ᶠ[𝓝 x] fun y => ((c : ℝ) : EReal) * logNormSq (g y) + (R y : EReal))
    (N : Set M) (hN : N ∈ 𝓝 x) :
    ∃ U : Opens M, x ∈ U ∧ (U : Set M) ⊆ N ∧
      (∀ y ∈ U, HolomorphicAt (m + 1) g y ∧ ∀ b,
        D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b) ∧
      ∃ (r : ℕ) (W : Fin r → GeometricPrimeCarrier (m + 1) U) (a : Fin r → ℕ)
        (p : Fin r → U → ℂ) (v : U → ℂ) (bU : U → ℝ) (C : ℝ),
        Function.Injective W ∧ (∀ i, 0 < a i) ∧
        (∀ i y, HolomorphicAt (m + 1) (p i) y) ∧
        (∀ i y b, (vanishingIdeal (n := m + 1) (W i).val).mem y b ↔
          IsInSpanAt (n := m + 1) (· = p i) y b) ∧
        (∀ y, HolomorphicAt (m + 1) v y ∧ v y ≠ 0) ∧
        (∀ y : U, g y = (∏ i, p i y ^ a i) * v y) ∧
        cartierOpenRestriction D U = ∑ i, a i • geometricPrimeCarrierEffectiveDivisor (W i) ∧
        0 ≤ C ∧ (∀ y, |bU y| ≤ C) ∧
        ∀ y : U, u y =
          (∑ i, (((c * (a i : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (p i y)) + (bU y : EReal) := by
  classical
  obtain ⟨hf, hF⟩ := exists_original_generator_nonzero_centered_germ
    D x g hgen.self_of_nhds.1 hgen.self_of_nhds.2
  let e := (complexChartAt (n := m + 1) x).val
  let f : ComplexModel (m + 1) → ℂ := fun z => g (e.symm (z + e x))
  obtain ⟨r, q, hq, a, v, hv, hprime, hnot, hmult, hv0, hvnon, hfactor⟩ :=
    exists_original_distinct_prime_factorization f hf hF
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hchart : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxE] using
      (e.continuousAt_symm (e.map_source hxE)).tendsto.comp ht
  have hRc : BoundedRealGermAt (fun z => R (e.symm (z + e x))) 0 := by
    obtain ⟨C, hC, hRC⟩ := hR
    exact ⟨C, hC, hchart.eventually hRC⟩
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hlogcont : ContinuousAt (fun z => Real.log (‖v z‖ ^ 2)) 0 :=
    (hv.self_of_nhds.continuousAt.norm.pow 2).log
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0))
  let b : ComplexModel (m + 1) → ℝ := fun z =>
    R (e.symm (z + e x)) + (c : ℝ) * Real.log (‖v z‖ ^ 2)
  obtain ⟨C, hC, hbC⟩ := hRc.add
    (boundedRealGermAt_of_continuousAt (continuousAt_const.mul hlogcont))
  let N' : Set (ComplexModel (m + 1)) := {z | e.symm (z + e x) ∈ N ∧ z + e x ∈ e.target ∧
    (HolomorphicAt (m + 1) g (e.symm (z + e x)) ∧ ∀ d,
      D.ideal.mem (e.symm (z + e x)) d ↔
        IsInSpanAt (n := m + 1) (· = g) (e.symm (z + e x)) d) ∧
    OkaRelationSheaf.HolAt v z ∧ v z ≠ 0 ∧ f z = (∏ i, q i z ^ a i) * v z ∧ |b z| ≤ C ∧
    u (e.symm (z + e x)) = ((c : ℝ) : EReal) * logNormSq (f z) + (R (e.symm (z + e x)) : EReal)}
  have hN' : N' ∈ 𝓝 0 := by
    filter_upwards [hchart.eventually hN,
      ht.eventually (e.open_target.mem_nhds (e.map_source hxE)), hchart.eventually hgen,
      OkaRelationSheaf.HolAt.eventually hv, hvnon, hfactor, hbC, hchart.eventually hu]
      with z hzN hzT hgz hvz hvnz hfac hbz huz
    exact ⟨hzN, hzT, hgz, hvz, hvnz, hfac, hbz, huz⟩
  obtain ⟨Ω, h0Ω, hΩN, V, hV⟩ := exists_common_open_prime_carriers q hq hprime hnot N' hN'
  have htarget : ∀ z ∈ Ω, z + e x ∈ e.target := fun z hz => (hΩN hz).2.1
  let U := centeredChartOpen x Ω
  let κ := centeredChartHomeomorph x Ω htarget
  choose T hT using fun i => exists_original_chart_prime_transport x Ω htarget (V i)
    (fun z : Ω => q i z) (hV i).2.2.1 (hV i).2.2.2.2
  let W : Fin r → GeometricPrimeCarrier (m + 1) U := fun i =>
    ⟨(T i).carrier, T i, rfl, by rw [(hT i).2.1, (hV i).2.1]⟩
  let p : Fin r → U → ℂ := fun i y => q i (κ y)
  let vU : U → ℂ := fun y => v (κ y)
  let bU : U → ℝ := fun y => b (κ y)
  have hinv (y : U) : e.symm ((κ y : ComplexModel (m + 1)) + e x) = y := by
    change e.symm (e y - e x + e x) = y
    rw [sub_add_cancel, e.left_inv y.2.1]
  have hxU : x ∈ U := by
    refine ⟨hxE, ?_⟩
    change e x - e x ∈ Ω
    simpa only [sub_self] using h0Ω
  have hUN : (U : Set M) ⊆ N := by
    intro y hy
    have h := (hΩN (κ ⟨y, hy⟩).2).1
    rwa [hinv ⟨y, hy⟩] at h
  have hgenU (y : M) (hy : y ∈ U) : HolomorphicAt (m + 1) g y ∧ ∀ d,
      D.ideal.mem y d ↔ IsInSpanAt (n := m + 1) (· = g) y d := by
    have h := (hΩN (κ ⟨y, hy⟩).2).2.2.1
    rwa [hinv ⟨y, hy⟩] at h
  have hp (i : Fin r) (y : U) : HolomorphicAt (m + 1) (p i) y := (hT i).2.2.1 y
  have hideal (i : Fin r) (y : U) (d : U → ℂ) :
      (vanishingIdeal (n := m + 1) (W i).val).mem y d ↔
        IsInSpanAt (n := m + 1) (· = p i) y d := (hT i).2.2.2 y d
  have hcarrier (i : Fin r) : (W i).val = {y | p i y = 0} := by
    change (T i).carrier = _
    rw [(hT i).1, (hV i).1]
    rfl
  have hpoint (i : Fin r) (z : Ω) : p i (κ.symm z) = q i z := by
    change q i (κ (κ.symm z)) = q i z
    rw [κ.apply_symm_apply]
  have hdistinct : Function.Injective W := by
    intro i j heq
    by_contra hij
    apply hnot i j hij
    apply Ideal.mem_span_singleton.mp
    rw [← (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible
      (q i) (hq i) (hprime i)).1]
    apply mem_vanishingIdeal_mk.mpr
    filter_upwards [Ω.isOpen.mem_nhds h0Ω] with z hz hqiz
    have hy : κ.symm ⟨z, hz⟩ ∈ (W i).val := by
      rw [hcarrier i]
      exact (hpoint i ⟨z, hz⟩).trans hqiz
    rw [heq, hcarrier j] at hy
    exact (hpoint j ⟨z, hz⟩).symm.trans hy
  have hκval : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞
      (fun y : U => (κ y : ComplexModel (m + 1))) :=
    contMDiff_subtype_val.comp (centeredChartHomeomorph_contMDiff x Ω htarget)
  have hvU (y : U) : HolomorphicAt (m + 1) vU y ∧ vU y ≠ 0 := by
    have h := hΩN (κ y).2
    have hvNative : HolomorphicAt (m + 1) v (κ y : ComplexModel (m + 1)) := by
      filter_upwards [h.2.2.2.1] with z hz
      exact hz.mdifferentiableAt
    exact ⟨hvNative.comp_contMDiff (f := fun z : U => (κ z : ComplexModel (m + 1)))
      (Eventually.of_forall fun z => hκval z), h.2.2.2.2.1⟩
  have hfacU (y : U) : g y = (∏ i, p i y ^ a i) * vU y := by
    have h := (hΩN (κ y).2).2.2.2.2.2.1
    change g (e.symm ((κ y : ComplexModel (m + 1)) + e x)) = _ at h
    rwa [hinv y] at h
  let E := ∑ i, a i • geometricPrimeCarrierEffectiveDivisor (W i)
  let P : U → ℂ := fun y => ∏ i, p i y ^ a i
  have hE (y : U) (d : U → ℂ) : E.ideal.mem y d ↔
      IsInSpanAt (n := m + 1) (· = P) y d := by
    apply finite_cartier_sum_generator_product Finset.univ
      (fun i => geometricPrimeCarrierEffectiveDivisor (W i)) a p y (fun i _ => hp i y)
    intro i _ d
    rw [geometricPrimeCarrierEffectiveDivisor_ideal]
    exact hideal i y d
  have hfull : cartierOpenRestriction D U = E :=
    full_cartier_eq_of_generators_unit (cartierOpenRestriction D U) E
      (fun y : U => g y) P vU
      (fun y => cartierOpenRestriction_generator D U y g (hgenU y y.2).1 (hgenU y y.2).2)
      hE (fun y => (hvU y).1) (fun y => (hvU y).2) hfacU
  refine ⟨U, hxU, hUN, hgenU, r, W, a, p, vU, bU, C, hdistinct,
    (fun i => (hmult i).1), hp, hideal, hvU, hfacU, hfull, hC, ?_, ?_⟩
  · intro y
    exact (hΩN (κ y).2).2.2.2.2.2.2.1
  · intro y
    have h := hΩN (κ y).2
    have heq : u y = ((c : ℝ) : EReal) * logNormSq (f (κ y)) + (R y : EReal) := by
      have hu' := h.2.2.2.2.2.2.2
      rwa [hinv y] at hu'
    rw [heq, h.2.2.2.2.2.1, logNormSq_geometric_product,
      logNormSq_of_ne_zero h.2.2.2.2.1,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hcR.le) (EReal.coe_ne_top (c : ℝ)),
      MeteredDivisorSingleGenerator.coe_mul_finsetSum hcR.le]
    have hsum : (∑ i : Fin r, ((c : ℝ) : EReal) *
        (((a i : ℝ) : EReal) * logNormSq (q i (κ y)))) =
        ∑ i : Fin r, (((c * (a i : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (p i y) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, ← EReal.coe_mul]
      congr 2
      norm_cast
    rw [hsum]
    dsimp only [bU, b]
    rw [hinv y, EReal.coe_add, EReal.coe_mul]
    ac_rfl

end SGPT.PSH
