import SGPT.PSH.OriginalCartierPrimes

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH
open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves AnalyticGermDecomposition InvertibleIdealQuotient
open DivisorExponent RegularLocusComponent
open scoped Topology Manifold ContDiff


universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The original D,x produce DISTINCT actual common-U primes with literal
original D-order and all finite divisibility witnesses along those SAME carriers. -/
theorem exists_original_common_open_prime_order_witnesses
    (D : EffectiveDivisor (m + 1) M) (x : M) :
    ∃ U : Opens M, x ∈ U ∧ ∃ (r : ℕ)
      (W : Fin r → ClosedIrreducibleAnalyticSubvariety (m + 1) U)
      (p : Fin r → U → ℂ) (a : Fin r → ℕ) (g : M → ℂ) (v : U → ℂ),
      (∀ y ∈ U, HolomorphicAt (m + 1) g y ∧ ∀ b,
        D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b) ∧
      (∀ i j, i ≠ j → (W i).carrier ≠ (W j).carrier) ∧
      (∀ i, 0 < a i ∧ (W i).dim = m ∧ (W i).carrier = {y | p i y = 0} ∧
        (∀ y, HolomorphicAt (m + 1) (p i) y) ∧
        ∀ (y : U) (b : U → ℂ), (vanishingIdeal (n := m + 1) (W i).carrier).mem y b ↔
          IsInSpanAt (n := m + 1) (· = p i) y b) ∧
      (∀ y : U, HolomorphicAt (m + 1) v y ∧ v y ≠ 0) ∧
      (∀ y : U, g y = (∏ i, p i y ^ a i) * v y) ∧
      (∀ y : U, (y : M) ∈ D.support ↔ ∃ i, y ∈ (W i).carrier) ∧
      ∀ i, ∃ y : U, y ∈ (W i).carrier ∧ RegularAtDim (n := m + 1) D.support (y : M) m ∧
        divExp (m + 1) D.ideal (Subtype.val '' (W i).carrier) (y : M) = a i ∧
        ∀ b : ℕ, IsDivNear (m + 1) D.ideal (Subtype.val '' (W i).carrier) b (y : M) ↔ b ≤ a i := by
  classical
  obtain ⟨g, hf, hF, Ω, h0Ω, htarget, hxU, hgenU, r, q, hq, a, p, v, W, B,
    hprime, hnot, hdata, hv, hfac, hsupport⟩ := exists_original_cartier_common_open_primes D x
  let U := centeredChartOpen x Ω
  let κ := centeredChartHomeomorph x Ω htarget
  let e := (complexChartAt (n := m + 1) x).val
  have hpeq (i : Fin r) : p i = (fun y => q i (κ y)) := (hdata i).2.2.2.1
  have hcarrier (i : Fin r) : (W i).carrier = {y | p i y = 0} := (hdata i).2.2.2.2.1
  have hpoint (i : Fin r) (z : Ω) : p i (κ.symm z) = q i z := by
    rw [hpeq i]
    change q i (κ (κ.symm z)) = q i z
    rw [κ.apply_symm_apply]
  have hchartmem (z : ComplexModel (m + 1)) (hz : z ∈ Ω) :
      z ∈ AnalyticDescendingChain.chartGerm (n := m + 1) D.support x ↔ ∃ j, q j z = 0 := by
    change (z + e x ∈ e.target ∧ e.symm (z + e x) ∈ D.support) ↔ _
    constructor
    · intro h
      have hy : (κ.symm ⟨z, hz⟩ : M) ∈ D.support := h.2
      obtain ⟨j, hj⟩ := (hsupport (κ.symm ⟨z, hz⟩)).mp hy
      rw [hcarrier j] at hj
      exact ⟨j, (hpoint j ⟨z, hz⟩).symm.trans hj⟩
    · rintro ⟨j, hj⟩
      refine ⟨htarget z hz, ?_⟩
      apply (hsupport (κ.symm ⟨z, hz⟩)).mpr
      refine ⟨j, ?_⟩
      rw [hcarrier j]
      exact (hpoint j ⟨z, hz⟩).trans hj
  have hdistinct (i j : Fin r) (hij : i ≠ j) : (W i).carrier ≠ (W j).carrier := by
    intro heq
    have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), q i z = 0 → q j z = 0 := by
      filter_upwards [Ω.isOpen.mem_nhds h0Ω] with z hz hqiz
      have hy : κ.symm ⟨z, hz⟩ ∈ (W i).carrier := by
        rw [hcarrier i]
        exact (hpoint i ⟨z, hz⟩).trans hqiz
      rw [heq, hcarrier j] at hy
      exact (hpoint j ⟨z, hz⟩).symm.trans hy
    apply hnot i j hij
    apply Ideal.mem_span_singleton.mp
    rw [← (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible
      (q i) (hq i) (hprime i)).1]
    exact mem_vanishingIdeal_mk.mpr hvan
  refine ⟨U, hxU, r, W, p, a, g, v, hgenU, hdistinct, ?_, hv, hfac, hsupport, ?_⟩
  · intro i
    exact ⟨(hdata i).1, (hdata i).2.2.2.2.2.1, hcarrier i,
      (hdata i).2.2.2.2.2.2.2.1, (hdata i).2.2.2.2.2.2.2.2⟩
  · intro i
    let t : Fin r → ComplexModel (m + 1) → ℂ := fun j z => if j = i then 1 else q j z
    have ht : ∀ j, OkaRelationSheaf.HolAt (t j) 0 := by
      intro j
      by_cases hji : j = i
      · simp only [t, if_pos hji]
        exact Eventually.of_forall (fun _ => differentiableAt_const (1 : ℂ))
      · simpa only [t, if_neg hji] using hq j
    have hnt : ∀ j, ¬HolGerm.mk (q i) (hq i) ∣ HolGerm.mk (t j) (ht j) := by
      intro j
      by_cases hji : j = i
      · have hone : t j = (1 : ComplexModel (m + 1) → ℂ) := by
          funext z
          simp only [t, if_pos hji, Pi.one_apply]
        simpa only [hone, HolGerm.mk_one] using (hprime i).not_dvd_one
      · simpa only [t, if_neg hji] using hnot i j (Ne.symm hji)
    have hfreq := ActualPrimeRegularFiniteAvoidance.frequently_regular_zero_avoiding_finite_family
      (q i) (hq i) (hprime i) t ht hnt
    have hhols : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), ∀ j, OkaRelationSheaf.HolAt (q j) z :=
      Filter.eventually_all.mpr (fun j => OkaRelationSheaf.HolAt.eventually (hq j))
    obtain ⟨z, hzΩ, ⟨hqzero, hqreg, htests⟩, hhol⟩ := Filter.frequently_iff.mp
      (hfreq.and_eventually hhols) (Ω.isOpen.mem_nhds h0Ω)
    have hothers (j : Fin r) (hji : j ≠ i) : q j z ≠ 0 := by
      simpa only [t, if_neg hji] using htests j
    have hnear : ∀ᶠ w in 𝓝 z, w ∈ Ω ∧ ∀ j, j ≠ i → q j w ≠ 0 := by
      have hΩnear : ∀ᶠ w in 𝓝 z, w ∈ Ω := Ω.isOpen.mem_nhds hzΩ
      apply hΩnear.and
      apply Filter.eventually_all.mpr
      intro j
      by_cases hji : j = i
      · exact Eventually.of_forall (fun _ h => (h hji).elim)
      · exact ((hhol j).self_of_nhds.continuousAt.eventually_ne (hothers j hji)).mono
          (fun _ hw _ => hw)
    obtain ⟨O, hOsub, hO, hzO⟩ := _root_.mem_nhds_iff.mp hnear
    have hlocalChart (w : ComplexModel (m + 1)) (hw : w ∈ O) :
        q i w = 0 ↔ w ∈ AnalyticDescendingChain.chartGerm (n := m + 1) D.support x := by
      rw [hchartmem w (hOsub hw).1]
      constructor
      · intro hi
        exact ⟨i, hi⟩
      · rintro ⟨j, hj⟩
        by_cases hji : j = i
        · simpa only [hji] using hj
        · exact ((hOsub hw).2 j hji hj).elim
    have heqChart : {w | q i w = 0} ∩ O =
        AnalyticDescendingChain.chartGerm (n := m + 1) D.support x ∩ O := by
      ext w
      exact and_congr_left (hlocalChart w)
    have hregChart := RegularPointDimension.regularAtDim_of_inter_eq hO hzO heqChart hqreg
    let y : U := κ.symm ⟨z, hzΩ⟩
    have hreg : RegularAtDim (n := m + 1) D.support (y : M) m :=
      DimensionMonotone.regularAtDim_of_chartGerm hregChart
    have hyW : y ∈ (W i).carrier := by
      rw [hcarrier i]
      exact (hpoint i ⟨z, hzΩ⟩).trans hqzero
    have hyD : (y : M) ∈ D.support := (hsupport y).mpr ⟨i, hyW⟩
    have hyB : (y : M) ∈ (B i : Set M) := by
      rw [← cartierPrimeComponent_carrier D (B i)]
      exact (hdata i).2.2.2.2.2.2.1 y hyW
    have hcoef : a i = divExp (m + 1) D.ideal D.support (y : M) :=
      (hdata i).2.2.1.trans (regularComponentOrder_eq D D.support (B i) hreg
        (globalComponent_eq_closure_of_regular_mem (B i) hreg hyB))
    have hcoord : e y - e x = z := congrArg Subtype.val (κ.apply_symm_apply ⟨z, hzΩ⟩)
    have hforward : Tendsto (fun w : M => e w - e x) (𝓝 (y : M)) (𝓝 z) := by
      simpa only [hcoord] using (e.continuousAt y.2.1).sub_const (e x)
    have hlocal : ∀ᶠ w in 𝓝 (y : M),
        w ∈ (Subtype.val '' (W i).carrier : Set M) ↔ w ∈ D.support := by
      filter_upwards [U.isOpen.mem_nhds y.2, hforward.eventually (hO.mem_nhds hzO)] with w hwU hwO
      constructor
      · rintro ⟨v, hvW, rfl⟩
        exact (hsupport v).mpr ⟨i, hvW⟩
      · intro hwD
        obtain ⟨j, hj⟩ := (hsupport ⟨w, hwU⟩).mp hwD
        have hji : j = i := by
          by_contra hbad
          apply (hOsub hwO).2 j hbad
          rw [hcarrier j] at hj
          rw [hpeq j] at hj
          exact hj
        subst j
        exact ⟨⟨w, hwU⟩, hj, rfl⟩
    have hyImage : (y : M) ∈ (Subtype.val '' (W i).carrier : Set M) := ⟨y, hyW, rfl⟩
    have horder : divExp (m + 1) D.ideal (Subtype.val '' (W i).carrier) (y : M) = a i :=
      (cartierOrder_eq_of_carrier_eventuallyEq D hyImage hyD hlocal).trans hcoef.symm
    refine ⟨y, hyW, hreg, horder, ?_⟩
    intro b
    have hhol : ∀ w f, D.ideal.mem w f → HolomorphicAt (m + 1) f w :=
      fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hf
    rw [isDivNear_iff_le_divExp hhol hyImage
      (HironakaDivisorPowers.isNonzeroAt_of_isInvertible D.isInvertible y), horder]

#print axioms exists_original_common_open_prime_order_witnesses
end SGPT.PSH
