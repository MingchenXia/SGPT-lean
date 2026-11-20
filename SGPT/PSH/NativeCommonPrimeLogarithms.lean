import SGPT.PSH.CommonOpenPrimeLogarithms
import SGPT.PSH.CenteredChartPrimes

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves AnalyticGermDecomposition InvertibleIdealQuotient
open scoped Topology Manifold ContDiff


universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem centered_original_holomorphic (x : M) (g : M → ℂ) (hg : HolomorphicAt n g x) :
    OkaRelationSheaf.HolAt (fun z => g ((complexChartAt (n := n) x).val.symm
      (z + (complexChartAt (n := n) x).val x))) 0 := by
  let e := (complexChartAt (n := n) x).val
  have ht : Tendsto (fun z : ComplexModel n => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hcoord : OkaRelationSheaf.HolAt (fun w : ComplexModel n => g (e.symm w)) (e x) :=
    CartanLocalReduction.holAt_comp_chart_symm (mem_complexChartAt_source x) hg
  filter_upwards [ht.eventually hcoord] with z hz
  change DifferentiableAt ℂ
    ((fun w : ComplexModel n => g (e.symm w)) ∘ fun z => z + e x) z
  exact hz.comp z (differentiableAt_id.add_const (e x))

omit [IsComplexManifold n M] in
private theorem support_iff_original_generator_zero (D : EffectiveDivisor n M)
    (y : M) (g : M → ℂ) (hg : HolomorphicAt n g y)
    (hgen : ∀ b, D.ideal.mem y b ↔ IsInSpanAt (n := n) (· = g) y b) :
    y ∈ D.support ↔ g y = 0 := by
  constructor
  · intro hyD
    exact hyD g ((hgen g).mpr (isInSpanAt_self rfl hg))
  · intro hgy b hb
    obtain ⟨_, a, _, heq⟩ := isInSpanAt_eq_iff.mp ((hgen b).mp hb)
    simpa only [hgy, mul_zero] using heq.self_of_nhds

/-- ANY actual ORIGINAL Cartier stalk generator internally has a nonzero
centered germ; nonzeroness is not an incoming chart-function certificate. -/
theorem exists_original_generator_nonzero_centered_germ
    (D : EffectiveDivisor n M) (x : M) (g : M → ℂ) (hg : HolomorphicAt n g x)
    (hgen : ∀ b, D.ideal.mem x b ↔ IsInSpanAt (n := n) (· = g) x b) :
    ∃ hf : OkaRelationSheaf.HolAt (fun z => g ((complexChartAt (n := n) x).val.symm
      (z + (complexChartAt (n := n) x).val x))) 0,
      HolGerm.mk (fun z => g ((complexChartAt (n := n) x).val.symm
        (z + (complexChartAt (n := n) x).val x))) hf ≠ 0 := by
  obtain ⟨U, hU, hxU, g0, hg0, hnon0, hgen0⟩ := D.isInvertible x
  have h0hol : HolomorphicAt n g0 x := holomorphicAt_of_mdifferentiableOn hU hg0 hxU
  let e := (complexChartAt (n := n) x).val
  let f0 : ComplexModel n → ℂ := fun z => g0 (e.symm (z + e x))
  have hf0 := centered_original_holomorphic x g0 h0hol
  have hF0 : HolGerm.mk f0 hf0 ≠ 0 := by
    intro hbad
    have hz : ∀ᶠ z in 𝓝 (0 : ComplexModel n), f0 z = 0 := HolGerm.mk_eq_mk_iff.mp
      (hbad.trans (HolGerm.mk_zero (E := ComplexModel n)).symm)
    have hxE : x ∈ e.source := mem_complexChartAt_source x
    have ht : Tendsto (fun y : M => e y - e x) (𝓝 x) (𝓝 0) := by
      simpa only [sub_self] using (e.continuousAt hxE).sub_const (e x)
    have hgzero : ∀ᶠ y in 𝓝 x, g0 y = 0 := by
      filter_upwards [ht.eventually hz, e.open_source.mem_nhds hxE] with y hy hyE
      change g0 (e.symm (e y - e x + e x)) = 0 at hy
      simpa only [sub_add_cancel, e.left_inv hyE] using hy
    obtain ⟨W, hWsub, hW, hxW⟩ := _root_.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hxU) hgzero)
    obtain ⟨y, hyW, hgne⟩ := hnon0 W hW (fun _ hy => (hWsub hy).1) ⟨x, hxW⟩
    exact hgne (hWsub hyW).2
  obtain ⟨v, hv, hv0, _, htrans⟩ := exists_centered_unit_transition_of_cartier_generators
    D x g g0 hg h0hol hgen (hgen0 x hxU)
  have hf := centered_original_holomorphic x g hg
  have hvunit : IsUnit (HolGerm.mk v hv) := (HolGerm.isUnit_iff_eval_ne_zero _).mpr
    (by simpa only [HolGerm.eval_mk] using hv0)
  refine ⟨hf, ?_⟩
  have heq : HolGerm.mk (fun z => g (e.symm (z + e x))) hf =
      HolGerm.mk f0 hf0 * HolGerm.mk v hv := by
    rw [← HolGerm.mk_mul f0 v hf0 hv]
    exact HolGerm.mk_eq_mk_iff.mpr htrans
  rw [heq]
  exact mul_ne_zero hF0 hvunit.ne_zero


section Native
variable {m : ℕ} {Z : Type u} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]

/-- ORIGINAL D,g,u,R produce actual DISTINCT original common-U primes,
all reduced stalks, genuine original D coefficients and ONE uniform bound
for the literal extended logarithmic remainder on ALL of the SAME U. -/
theorem exists_native_common_open_prime_logarithmic_remainder
    (D : EffectiveDivisor (m + 1) Z) (x : Z) (g : Z → ℂ)
    (hgen : ∀ᶠ y in 𝓝 x, HolomorphicAt (m + 1) g y ∧ ∀ b,
      D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b)
    (c : ℚ) (hc : 0 < c) (u : Z → EReal) (R : Z → ℝ) (hR : BoundedRealGermAt R x)
    (hu : u =ᶠ[𝓝 x] fun y => ((c : ℝ) : EReal) * logNormSq (g y) + (R y : EReal)) :
    ∃ Ω : Opens (ComplexModel (m + 1)), (0 : ComplexModel (m + 1)) ∈ Ω ∧
      ∃ htarget : ∀ z ∈ Ω, z + (complexChartAt (n := m + 1) x).val x ∈
        (complexChartAt (n := m + 1) x).val.target,
      x ∈ centeredChartOpen x Ω ∧
      (∀ y ∈ centeredChartOpen x Ω, HolomorphicAt (m + 1) g y ∧ ∀ b,
        D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b) ∧
      ∃ (r : ℕ) (q : Fin r → ComplexModel (m + 1) → ℂ)
        (hq : ∀ i, OkaRelationSheaf.HolAt (q i) 0) (a : Fin r → ℕ)
        (p : Fin r → centeredChartOpen x Ω → ℂ)
        (W : Fin r → ClosedIrreducibleAnalyticSubvariety (m + 1) (centeredChartOpen x Ω))
        (B : Fin r → GlobalComponents.globalComponents (n := m + 1) D.support)
        (bU : centeredChartOpen x Ω → ℝ) (C : ℝ),
        (∀ i j, i ≠ j → (W i).carrier ≠ (W j).carrier) ∧
        (∀ i, Prime (HolGerm.mk (q i) (hq i)) ∧ 0 < a i ∧
          (∃ hf : OkaRelationSheaf.HolAt (fun z => g ((complexChartAt (n := m + 1) x).val.symm
            (z + (complexChartAt (n := m + 1) x).val x))) 0,
            a i = multiplicity (HolGerm.mk (q i) (hq i))
              (HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
                (z + (complexChartAt (n := m + 1) x).val x))) hf)) ∧
          0 < c * (a i : ℚ) ∧ a i = regularComponentOrder D D.support (B i) ∧
          p i = (fun y => q i (centeredChartHomeomorph x Ω htarget y)) ∧
          (W i).carrier = {y | p i y = 0} ∧ (W i).dim = m ∧
          (∀ y, HolomorphicAt (m + 1) (p i) y) ∧
          ∀ (y : centeredChartOpen x Ω) (b : centeredChartOpen x Ω → ℂ),
            (vanishingIdeal (n := m + 1) (W i).carrier).mem y b ↔
              IsInSpanAt (n := m + 1) (· = p i) y b) ∧
        (∀ y : centeredChartOpen x Ω, (y : Z) ∈ D.support ↔ ∃ i, y ∈ (W i).carrier) ∧
        0 ≤ C ∧ (∀ y, |bU y| ≤ C) ∧
        ∀ y : centeredChartOpen x Ω, u y =
          (∑ i, (((c * (a i : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (p i y)) + (bU y : EReal) := by
  classical
  obtain ⟨hf, hF⟩ := exists_original_generator_nonzero_centered_germ
    D x g hgen.self_of_nhds.1 hgen.self_of_nhds.2
  let e := (complexChartAt (n := m + 1) x).val
  let f : ComplexModel (m + 1) → ℂ := fun z => g (e.symm (z + e x))
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hchart : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxE] using
      (e.continuousAt_symm (e.map_source hxE)).tendsto.comp ht
  let N : Set (ComplexModel (m + 1)) := {z | z + e x ∈ e.target ∧
    HolomorphicAt (m + 1) g (e.symm (z + e x)) ∧ ∀ b,
      D.ideal.mem (e.symm (z + e x)) b ↔
        IsInSpanAt (n := m + 1) (· = g) (e.symm (z + e x)) b}
  have hN : N ∈ 𝓝 0 := by
    filter_upwards [ht.eventually (e.open_target.mem_nhds (e.map_source hxE)),
      hchart.eventually hgen] with z hzT hgz
    exact ⟨hzT, hgz⟩
  have hzero : AnalyticDescendingChain.chartGerm (n := m + 1) D.support x =ᶠ[𝓝 0]
      {z | f z = 0} := by
    apply Filter.eventuallyEq_set.mpr
    filter_upwards [hN] with z hz
    change (z + e x ∈ e.target ∧ e.symm (z + e x) ∈ D.support) ↔ _
    exact (and_iff_right hz.1).trans
      (support_iff_original_generator_zero D _ g hz.2.1 hz.2.2)
  have hRc : BoundedRealGermAt (fun z => R (e.symm (z + e x))) 0 := by
    obtain ⟨C, hC, hRC⟩ := hR
    exact ⟨C, hC, hchart.eventually hRC⟩
  obtain ⟨Ω, h0Ω, hΩN, r, q, hq, a, V, b, C, hprime, hnot, hdata, hC, hbC, hlog, hfsupport⟩ :=
    exists_common_open_prime_logarithmic_remainder f hf hF N hN c hc
      (fun z => u (e.symm (z + e x))) (fun z => R (e.symm (z + e x))) hRc
      (hchart.eventually hu)
  have htarget : ∀ z ∈ Ω, z + e x ∈ e.target := fun z hz => (hΩN hz).1
  let κ := centeredChartHomeomorph x Ω htarget
  have hV (i : Fin r) : (V i).carrier = {y : Ω | q i y = 0} ∧ (V i).dim = m ∧
      (∀ y : Ω, HolomorphicAt (m + 1) (fun z : Ω => q i z) y) ∧
      (vanishingIdeal (n := m + 1) (V i).carrier).IsInvertible ∧
      ∀ (y : Ω) (d : Ω → ℂ), (vanishingIdeal (n := m + 1) (V i).carrier).mem y d ↔
        IsInSpanAt (n := m + 1) (· = fun z : Ω => q i z) y d := (hdata i).2.2.2
  choose W hW using fun i => exists_original_chart_prime_transport x Ω htarget (V i)
    (fun z : Ω => q i z) (hV i).2.2.1 (hV i).2.2.2.2
  let p : Fin r → centeredChartOpen x Ω → ℂ := fun i y => q i (κ y)
  have hcarrier (i : Fin r) : (W i).carrier = {y | p i y = 0} := by
    rw [(hW i).1, (hV i).1]
    rfl
  have hpoint (i : Fin r) (z : Ω) : p i (κ.symm z) = q i z := by
    change q i (κ (κ.symm z)) = q i z
    rw [κ.apply_symm_apply]
  have hinv (y : centeredChartOpen x Ω) : e.symm ((κ y : ComplexModel (m + 1)) + e x) = y := by
    change e.symm (e y - e x + e x) = y
    rw [sub_add_cancel, e.left_inv y.2.1]
  have hgenU (y : Z) (hy : y ∈ centeredChartOpen x Ω) : HolomorphicAt (m + 1) g y ∧ ∀ d,
      D.ideal.mem y d ↔ IsInSpanAt (n := m + 1) (· = g) y d := by
    have h := (hΩN (κ ⟨y, hy⟩).2).2
    rwa [hinv ⟨y, hy⟩] at h
  have hsub (i : Fin r) : {z | q i z = 0} ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := m + 1) D.support x := by
    filter_upwards [Ω.isOpen.mem_nhds h0Ω, Filter.eventuallyEq_set.mp hzero] with z hz heq hqz
    apply heq.mpr
    apply (hfsupport ⟨z, hz⟩).mpr
    refine ⟨i, ?_⟩
    rw [(hV i).1]
    exact hqz
  have hB : ∀ i, ∃ B : GlobalComponents.globalComponents (n := m + 1) D.support,
      {z | q i z = 0} ≤ᶠ[𝓝 0]
        AnalyticDescendingChain.chartGerm (n := m + 1) (cartierPrimeComponent D B).carrier x := by
    intro i
    obtain ⟨B, hB, _⟩ := exists_unique_cartierPrimeComponent_of_chart_prime D x
      (q i) (hq i) (hprime i) (hsub i)
    exact ⟨B, hB.1⟩
  choose B hB using hB
  have hcoef (i : Fin r) : a i = regularComponentOrder D D.support (B i) :=
    (hdata i).2.1.trans (regularComponentOrder_eq_primeGerm_multiplicity D x g hf hF hgen hzero
      (q i) (hq i) (hprime i) (B i) (hB i)).symm
  refine ⟨Ω, h0Ω, htarget, ⟨hxE, ?_⟩, hgenU, r, q, hq, a, p, W, B,
    (fun y => b (κ y)), C, ?_, ?_, ?_, hC, (fun y => hbC (κ y) (κ y).2), ?_⟩
  · change e x - e x ∈ Ω
    simpa only [sub_self] using h0Ω
  · intro i j hij heq
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
  · intro i
    exact ⟨hprime i, (hdata i).1, ⟨hf, (hdata i).2.1⟩, (hdata i).2.2.1, hcoef i,
      rfl, hcarrier i, (hW i).2.1.trans (hV i).2.1, (hW i).2.2.1, (hW i).2.2.2⟩
  · intro y
    rw [support_iff_original_generator_zero D y g (hgenU y y.2).1 (hgenU y y.2).2]
    have h := hfsupport (κ y)
    change g (e.symm ((κ y : ComplexModel (m + 1)) + e x)) = 0 ↔ _ at h
    rw [hinv y] at h
    rw [h]
    apply exists_congr
    intro i
    rw [(hW i).1]
    rfl
  · intro y
    have h := hlog (κ y) (κ y).2
    change u (e.symm ((κ y : ComplexModel (m + 1)) + e x)) = _ at h
    rwa [hinv y] at h
end Native

#print axioms exists_original_generator_nonzero_centered_germ
#print axioms exists_native_common_open_prime_logarithmic_remainder
end SGPT.PSH
