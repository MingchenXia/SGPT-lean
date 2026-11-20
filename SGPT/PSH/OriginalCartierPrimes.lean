import SGPT.PSH.CenteredChartPrimes
import SGPT.PSH.CartierPrimeGermMultiplicity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves AnalyticGermDecomposition AnalyticSubsetOpens InvertibleIdealQuotient
open scoped Topology Manifold ContDiff


private theorem holomorphicAt_comp_map {n k : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y]
    {g : Y → X} (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g)
    {f : X → ℂ} {y : Y} (hf : HolomorphicAt n f (g y)) :
    HolomorphicAt k (fun z => f (g z)) y := by
  filter_upwards [(hg.continuous.tendsto y).eventually hf] with z hz
  exact hz.comp z ((hg z).mdifferentiableAt (by simp))

private theorem holomorphicAt_model_open {n : ℕ} (Ω : Opens (ComplexModel n))
    (f : ComplexModel n → ℂ) (y : Ω) (hf : OkaRelationSheaf.HolAt f (y : ComplexModel n)) :
    HolomorphicAt n (fun z : Ω => f z) y := by
  have hy := mem_complexChartAt_source (n := n) y
  have heval : (complexChartAt (n := n) y).val y = (y : ComplexModel n) := by
    simp [complexChartAt, chartAt_opens_apply, chartAt_self_eq]
  have h := CartanLocalReduction.holomorphicAt_comp_chart (x := y) hy (heval ▸ hf)
  simpa only [complexChartAt, chartAt_opens_apply, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, id_eq] using h

universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The ORIGINAL D and x alone produce actual primes on ONE original U,
the SAME original ideal generator, all reduced stalks and genuine D orders. -/
theorem exists_original_cartier_common_open_primes (D : EffectiveDivisor (m + 1) M) (x : M) :
    ∃ (g : M → ℂ)
      (hf : OkaRelationSheaf.HolAt (fun z => g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) 0),
      HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) hf ≠ 0 ∧
      ∃ Ω : Opens (ComplexModel (m + 1)), (0 : ComplexModel (m + 1)) ∈ Ω ∧
      ∃ htarget : ∀ z ∈ Ω, z + (complexChartAt (n := m + 1) x).val x ∈
        (complexChartAt (n := m + 1) x).val.target,
      x ∈ centeredChartOpen x Ω ∧
      (∀ y ∈ centeredChartOpen x Ω, HolomorphicAt (m + 1) g y ∧ ∀ b,
        D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b) ∧
      ∃ (r : ℕ) (q : Fin r → ComplexModel (m + 1) → ℂ)
        (hq : ∀ i, OkaRelationSheaf.HolAt (q i) 0) (a : Fin r → ℕ)
        (p : Fin r → centeredChartOpen x Ω → ℂ) (vU : centeredChartOpen x Ω → ℂ)
        (W : Fin r → ClosedIrreducibleAnalyticSubvariety (m + 1) (centeredChartOpen x Ω))
        (B : Fin r → GlobalComponents.globalComponents (n := m + 1) D.support),
        (∀ i, Prime (HolGerm.mk (q i) (hq i))) ∧
        (∀ i j, i ≠ j → ¬HolGerm.mk (q i) (hq i) ∣ HolGerm.mk (q j) (hq j)) ∧
        (∀ i, 0 < a i ∧
          a i = multiplicity (HolGerm.mk (q i) (hq i))
            (HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
              (z + (complexChartAt (n := m + 1) x).val x))) hf) ∧
          a i = regularComponentOrder D D.support (B i) ∧
          p i = (fun y => q i (centeredChartHomeomorph x Ω htarget y)) ∧
          (W i).carrier = {y | p i y = 0} ∧ (W i).dim = m ∧
          (∀ y ∈ (W i).carrier, (y : M) ∈ (cartierPrimeComponent D (B i)).carrier) ∧
          (∀ y, HolomorphicAt (m + 1) (p i) y) ∧
          ∀ (y : centeredChartOpen x Ω) (b : centeredChartOpen x Ω → ℂ),
            (HolomorphicIdealSheaves.vanishingIdeal (n := m + 1) (W i).carrier).mem y b ↔
              IsInSpanAt (n := m + 1) (· = p i) y b) ∧
        (∀ y, HolomorphicAt (m + 1) vU y ∧ vU y ≠ 0) ∧
        (∀ y : centeredChartOpen x Ω, g (y : M) = (∏ i, p i y ^ a i) * vU y) ∧
        ∀ y : centeredChartOpen x Ω, (y : M) ∈ D.support ↔ ∃ i, y ∈ (W i).carrier := by
  classical
  obtain ⟨g, hf, hF, hgen, hzero⟩ := exists_cartier_centered_stalk_generator D x
  let e := (complexChartAt (n := m + 1) x).val
  let f : ComplexModel (m + 1) → ℂ := fun z => g (e.symm (z + e x))
  obtain ⟨r, q, hq, a, v, hv, hprime, hnot, hmult, _, hvnon, hfactor⟩ :=
    exists_original_distinct_prime_factorization f hf hF
  have hsub (i : Fin r) : {z | q i z = 0} ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := m + 1) D.support x := by
    filter_upwards [hfactor, Filter.eventuallyEq_set.mp hzero] with z hz heq hqz
    apply heq.mpr
    change f z = 0
    rw [hz]
    have hprod : (∏ j, q j z ^ a j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hqz, zero_pow (hmult i).1.ne'])
    rw [hprod, zero_mul]
  have hB : ∀ i, ∃ B : GlobalComponents.globalComponents (n := m + 1) D.support,
      {z | q i z = 0} ≤ᶠ[𝓝 0]
        AnalyticDescendingChain.chartGerm (n := m + 1) (cartierPrimeComponent D B).carrier x := by
    intro i
    obtain ⟨B, hB, _⟩ := exists_unique_cartierPrimeComponent_of_chart_prime D x
      (q i) (hq i) (hprime i) (hsub i)
    exact ⟨B, hB.1⟩
  choose B hB using hB
  have hcoef (i : Fin r) : a i = regularComponentOrder D D.support (B i) :=
    (hmult i).2.trans (regularComponentOrder_eq_primeGerm_multiplicity D x g hf hF
      hgen hzero (q i) (hq i) (hprime i) (B i) (hB i)).symm
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hchart : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxE] using
      (e.continuousAt_symm (e.map_source hxE)).tendsto.comp ht
  let N : Set (ComplexModel (m + 1)) := {z | z + e x ∈ e.target ∧
    (HolomorphicAt (m + 1) g (e.symm (z + e x)) ∧ ∀ b,
      D.ideal.mem (e.symm (z + e x)) b ↔ IsInSpanAt (n := m + 1) (· = g)
        (e.symm (z + e x)) b) ∧ OkaRelationSheaf.HolAt v z ∧ v z ≠ 0 ∧
    f z = (∏ i, q i z ^ a i) * v z ∧ ∀ i, q i z = 0 →
      z ∈ AnalyticDescendingChain.chartGerm (n := m + 1) (cartierPrimeComponent D (B i)).carrier x}
  have hN : N ∈ 𝓝 0 := by
    filter_upwards [ht.eventually (e.open_target.mem_nhds (e.map_source hxE)),
      hchart.eventually hgen, OkaRelationSheaf.HolAt.eventually hv, hvnon, hfactor,
      Filter.eventually_all.mpr hB] with z hzT hgz hvz hvnz hfac hBz
    exact ⟨hzT, hgz, hvz, hvnz, hfac, hBz⟩
  obtain ⟨Ω, h0Ω, hΩN, V, hV⟩ := exists_common_open_prime_carriers q hq hprime hnot N hN
  have htarget : ∀ z ∈ Ω, z + e x ∈ e.target := fun z hz => (hΩN hz).1
  let κ := centeredChartHomeomorph x Ω htarget
  have hκ := centeredChartHomeomorph_contMDiff x Ω htarget
  choose W hW using fun i => exists_original_chart_prime_transport x Ω htarget (V i)
    (fun z : Ω => q i z) (hV i).2.2.1 (hV i).2.2.2.2
  let p : Fin r → centeredChartOpen x Ω → ℂ := fun i y => q i (κ y)
  let vU : centeredChartOpen x Ω → ℂ := fun y => v (κ y)
  have hfacU (y : centeredChartOpen x Ω) : g (y : M) = (∏ i, p i y ^ a i) * vU y := by
    have h := (hΩN (κ y).2).2.2.2.2.1
    change g (e.symm (e y - e x + e x)) = (∏ i, p i y ^ a i) * vU y at h
    simpa only [sub_add_cancel, e.left_inv y.2.1] using h
  have hcarrier (i : Fin r) : (W i).carrier = {y | p i y = 0} := by
    rw [(hW i).1, (hV i).1]
    rfl
  have hvUne (y : centeredChartOpen x Ω) : vU y ≠ 0 := (hΩN (κ y).2).2.2.2.1
  have hgenU (y : M) (hy : y ∈ centeredChartOpen x Ω) :
      HolomorphicAt (m + 1) g y ∧ ∀ b,
        D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b := by
    have h := (hΩN (κ ⟨y, hy⟩).2).2.1
    have hinv : e.symm ((κ ⟨y, hy⟩ : ComplexModel (m + 1)) + e x) = y := by
      change e.symm (e y - e x + e x) = y
      rw [sub_add_cancel, e.left_inv hy.1]
    rwa [hinv] at h
  refine ⟨g, hf, hF, Ω, h0Ω, htarget, ⟨hxE, ?_⟩, hgenU,
    r, q, hq, a, p, vU, W, B, hprime, hnot, ?_, ?_, hfacU, ?_⟩
  · change e x - e x ∈ Ω
    simpa only [sub_self] using h0Ω
  · intro i
    refine ⟨(hmult i).1, (hmult i).2, hcoef i, rfl, hcarrier i,
      (hW i).2.1.trans (hV i).2.1, ?_, (hW i).2.2.1, (hW i).2.2.2⟩
    intro y hy
    have hqzero : q i (κ y) = 0 := by rwa [hcarrier i] at hy
    have h := (hΩN (κ y).2).2.2.2.2.2 i hqzero
    change (e y - e x + e x ∈ e.target ∧
      e.symm (e y - e x + e x) ∈ (cartierPrimeComponent D (B i)).carrier) at h
    simpa only [sub_add_cancel, e.left_inv y.2.1] using h.2
  · intro y
    refine ⟨holomorphicAt_comp_map hκ (holomorphicAt_model_open Ω v (κ y)
      ((hΩN (κ y).2).2.2.1)), hvUne y⟩
  · intro y
    have hsupport : (y : M) ∈ D.support ↔ g y = 0 := by
      constructor
      · intro hyD
        exact hyD g ((hgenU y y.2).2 g |>.mpr (isInSpanAt_self rfl (hgenU y y.2).1))
      · intro hgy b hb
        obtain ⟨_, c, _, heq⟩ := isInSpanAt_eq_iff.mp ((hgenU y y.2).2 b |>.mp hb)
        simpa only [hgy, mul_zero] using heq.self_of_nhds
    rw [hsupport, hfacU y, mul_eq_zero, or_iff_left (hvUne y), Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨i, _, hi⟩
      refine ⟨i, ?_⟩
      rw [hcarrier i]
      exact eq_zero_of_pow_eq_zero hi
    · rintro ⟨i, hi⟩
      rw [hcarrier i] at hi
      exact ⟨i, Finset.mem_univ i, by rw [hi, zero_pow (hmult i).1.ne']⟩

#print axioms exists_original_cartier_common_open_primes

end SGPT.PSH
