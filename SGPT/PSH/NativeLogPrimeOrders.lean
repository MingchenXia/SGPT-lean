import SGPT.PSH.NativeCommonPrimeLogarithms

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolomorphicIdealSheaves AnalyticGermDecomposition InvertibleIdealQuotient
open DivisorExponent GermIdealOrder OrderTaylor IdealOrderArithmetic GermOrderProduct IdealWeightPowers
open scoped Topology Manifold ContDiff
universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem exists_same_prime_carrier_order_witness
    (D : EffectiveDivisor (m + 1) M) (x : M) (g : M → ℂ)
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ
      (fun z => g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) z)
    (hF : HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
      (z + (complexChartAt (n := m + 1) x).val x))) hf ≠ 0)
    (hgen : ∀ᶠ y in 𝓝 x, HolomorphicAt (m + 1) g y ∧ ∀ b,
      D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b)
    (hzero : AnalyticDescendingChain.chartGerm (n := m + 1) D.support x =ᶠ[𝓝 0]
      {z | g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x)) = 0})
    (q : ComplexModel (m + 1) → ℂ)
    (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z) (hQ : Prime (HolGerm.mk q hq))
    (hapos : 0 < multiplicity (HolGerm.mk q hq)
      (HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) hf))
    (Ω : Opens (ComplexModel (m + 1))) (h0Ω : (0 : ComplexModel (m + 1)) ∈ Ω)
    (htarget : ∀ z ∈ Ω, z + (complexChartAt (n := m + 1) x).val x ∈
      (complexChartAt (n := m + 1) x).val.target)
    (W : ClosedIrreducibleAnalyticSubvariety (m + 1) (centeredChartOpen x Ω))
    (hW : W.carrier = {y | q (centeredChartHomeomorph x Ω htarget y) = 0}) :
    ∃ y : centeredChartOpen x Ω, y ∈ W.carrier ∧
      RegularAtDim (n := m + 1) D.support (y : M) m ∧
      divExp (m + 1) D.ideal (Subtype.val '' W.carrier) (y : M) =
        multiplicity (HolGerm.mk q hq) (HolGerm.mk (fun z => g
          ((complexChartAt (n := m + 1) x).val.symm
            (z + (complexChartAt (n := m + 1) x).val x))) hf) ∧
      ∀ b : ℕ, IsDivNear (m + 1) D.ideal (Subtype.val '' W.carrier) b (y : M) ↔
        b ≤ multiplicity (HolGerm.mk q hq) (HolGerm.mk (fun z => g
          ((complexChartAt (n := m + 1) x).val.symm
            (z + (complexChartAt (n := m + 1) x).val x))) hf) := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  let e := (complexChartAt (n := m + 1) x).val
  let f : ComplexModel (m + 1) → ℂ := fun z => g (e.symm (z + e x))
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  obtain ⟨G, hfactor, hnot⟩ :=
    (FiniteMultiplicity.of_prime_left hQ hF).exists_eq_pow_mul_and_not_dvd
  obtain ⟨H, hH, hGrep⟩ := HolGerm.exists_eq_mk G
  let a := multiplicity (HolGerm.mk q hq) (HolGerm.mk f hf)
  have ha : 0 < a := hapos
  have hfactor' : f =ᶠ[𝓝 0] fun z => q z ^ a * H z := by
    apply HolGerm.mk_eq_mk_iff.mp
    rw [HolGerm.mk_mul (fun z => q z ^ a) H (eventually_differentiableAt_pow hq a) hH,
      HolGerm.mk_pow q hq a, ← hGrep]
    exact hfactor
  have hnot' : ¬HolGerm.mk q hq ∣ HolGerm.mk H hH := by
    simpa only [hGrep] using hnot
  obtain ⟨v, _hv, hfreq⟩ :=
    ActualPrimeRegularDifferentialAvoidance.exists_direction_frequently_regular_avoiding_tests
      q hq hQ (fun _ : Fin 1 => H) (fun _ => hH) (fun _ => hnot')
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hchart : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxE] using
      (e.continuousAt_symm (e.map_source hxE)).tendsto.comp ht
  have hconditions : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ q z ∧ DifferentiableAt ℂ H z ∧ f z = q z ^ a * H z ∧
      (z ∈ AnalyticDescendingChain.chartGerm (n := m + 1) D.support x ↔ f z = 0) ∧
      z ∈ Ω ∧ z + e x ∈ e.target ∧
      (∀ᶠ w in 𝓝 (e.symm (z + e x)), HolomorphicAt (m + 1) g w ∧ ∀ b,
        D.ideal.mem w b ↔ IsInSpanAt (n := m + 1) (· = g) w b) := by
    filter_upwards [hq, hH, hfactor', Filter.eventuallyEq_set.mp hzero, Ω.isOpen.mem_nhds h0Ω,
      ht.eventually (e.open_target.mem_nhds (e.map_source hxE)),
      hchart.eventually hgen.eventually_nhds] with z hqz hHz hfz heq hzB hzT hgz
    exact ⟨hqz, hHz, hfz, heq, hzB, hzT, hgz⟩
  obtain ⟨N, hNsub, hN, h0N⟩ := _root_.mem_nhds_iff.mp hconditions
  obtain ⟨z, hzN, hqzero, hqreg, _hqdz, hdq, htests⟩ :=
    Filter.frequently_iff.mp hfreq (hN.mem_nhds h0N)
  obtain ⟨hqz, hHz, hfz, hzeq, hzB, hzT, hgeny⟩ := hNsub hzN
  have hHne : H z ≠ 0 := htests 0
  have hzNnear : ∀ᶠ w in 𝓝 z, w ∈ N := hN.mem_nhds hzN
  obtain ⟨O, hOsub, hO, hzO⟩ := _root_.mem_nhds_iff.mp
    (hzNnear.and (hHz.continuousAt.eventually_ne hHne))
  have hqiff : ∀ w ∈ O, q w = 0 ↔
      w ∈ AnalyticDescendingChain.chartGerm (n := m + 1) D.support x := by
    intro w hwO
    obtain ⟨_hqw, _hHw, hfw, heq, _hwB, _hwT, _hgw⟩ := hNsub (hOsub hwO).1
    constructor
    · intro hqw
      apply heq.mpr
      rw [hfw, hqw, zero_pow ha.ne', zero_mul]
    · intro hwD
      have hmul : q w ^ a * H w = 0 := hfw.symm.trans (heq.mp hwD)
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hmul).resolve_right (hOsub hwO).2)
  have heq : {w | q w = 0} ∩ O =
      AnalyticDescendingChain.chartGerm (n := m + 1) D.support x ∩ O := by
    ext w
    exact and_congr_left fun hwO => hqiff w hwO
  have hregchart := RegularPointDimension.regularAtDim_of_inter_eq hO hzO heq hqreg
  let y := e.symm (z + e x)
  let κ := centeredChartHomeomorph x Ω htarget
  let yU : centeredChartOpen x Ω := κ.symm ⟨z, hzB⟩
  have hyE : y ∈ e.source := e.map_target hzT
  have hreg : RegularAtDim (n := m + 1) D.support y m :=
    DimensionMonotone.regularAtDim_of_chartGerm hregchart
  let Qloc : M → ℂ := fun w => q (e w - e x)
  let Hloc : M → ℂ := fun w => H (e w - e x)
  have hshift : Tendsto (fun w : ComplexModel (m + 1) => w - e x) (𝓝 (e y)) (𝓝 z) := by
    simpa only [y, e.right_inv hzT, add_sub_cancel_right] using
      (show ContinuousAt (fun w : ComplexModel (m + 1) => w - e x) (e y) from
        continuousAt_id.sub_const (e x)).tendsto
  have hcomp (W : ComplexModel (m + 1) → ℂ)
      (hW : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ W w) :
      HolomorphicAt (m + 1) (fun w : M => W (e w - e x)) y := by
    apply DerivativeIdeal.holomorphicAt_comp_chart (complexChartAt (n := m + 1) x)
      (W := fun w => W (w - e x)) hyE
    filter_upwards [hshift.eventually hW] with w hw
    exact hw.comp w (differentiableAt_id.sub_const (e x))
  have hQhol : HolomorphicAt (m + 1) Qloc y :=
    hcomp q (hzNnear.mono fun w hw => (hNsub hw).1)
  have hHhol : HolomorphicAt (m + 1) Hloc y :=
    hcomp H (hzNnear.mono fun w hw => (hNsub hw).2.1)
  have hQzero : Qloc y = 0 := by
    simpa only [Qloc, y, e.right_inv hzT, add_sub_cancel_right] using hqzero
  have hHunit : Hloc y ≠ 0 := by
    simpa only [Hloc, y, e.right_inv hzT, add_sub_cancel_right] using hHne
  have hQorder : ¬(idealPow (pointIdeal (m + 1) y) 2).mem y Qloc := by
    intro hbad
    have hdeq : (Qloc ∘ e.symm) =ᶠ[𝓝 (e y)] fun w => q (w - e x) := by
      filter_upwards [e.open_target.mem_nhds (e.map_source hyE)] with w hw
      simp only [Function.comp_apply, Qloc, e.right_inv hw]
    have hdz := OrderTaylor.iterChartDeriv_eq_zero_of_mem_idealPow
      (e := complexChartAt (n := m + 1) x) hyE hbad [v] (by simp)
    change fderiv ℂ (Qloc ∘ e.symm) (e y) v = 0 at hdz
    have htrans : fderiv ℂ (fun w => q (w - e x)) (e y) =
        fderiv ℂ q (e y - e x) := by
      simpa only [sub_eq_add_neg] using (fderiv_comp_add_right (𝕜 := ℂ) (f := q) (-e x) (x := e y))
    rw [hdeq.fderiv_eq, htrans] at hdz
    have hcoord : e y - e x = z := by
      simp only [y, e.right_inv hzT, add_sub_cancel_right]
    rw [hcoord] at hdz
    exact hdq hdz
  have hforward : Tendsto (fun w : M => e w - e x) (𝓝 y) (𝓝 z) := by
    simpa only [y, e.right_inv hzT, add_sub_cancel_right] using (e.continuousAt hyE).sub_const (e x)
  have hlocalC : ∀ᶠ w in 𝓝 y,
      w ∈ (Subtype.val '' W.carrier : Set M) ↔ Qloc w = 0 := by
    filter_upwards [(centeredChartOpen x Ω).isOpen.mem_nhds yU.2] with w hwU
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hW] at hv
      exact hv
    · intro hw
      refine ⟨⟨w, hwU⟩, ?_, rfl⟩
      rw [hW]
      exact hw
  have hlocalfactor : g =ᶠ[𝓝 y] fun w => Qloc w ^ a * Hloc w := by
    filter_upwards [e.open_source.mem_nhds hyE,
      hforward.eventually (hN.mem_nhds hzN)] with w hwE hwN
    have hfw : g (e.symm (e w - e x + e x)) = q (e w - e x) ^ a * H (e w - e x) :=
      (hNsub hwN).2.2.1
    simpa only [sub_add_cancel, e.left_inv hwE] using hfw
  have horder : divExp (m + 1) D.ideal (Subtype.val '' W.carrier) y = a :=
    cartierOrder_eq_of_principal_power_unit D g Qloc Hloc a hQhol hHhol hQzero hHunit hQorder
      (hgeny.mono fun w hw => hw.2) hlocalfactor hlocalC
  have hyW : yU ∈ W.carrier := by
    rw [hW]
    change q (κ (κ.symm ⟨z, hzB⟩)) = 0
    rw [κ.apply_symm_apply]
    exact hqzero
  refine ⟨yU, hyW, hreg, horder, ?_⟩
  intro b
  have hhol : ∀ w f, D.ideal.mem w f → HolomorphicAt (m + 1) f w :=
    fun _ _ hf => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hf
  have hyC : (yU : M) ∈ (Subtype.val '' W.carrier : Set M) := ⟨yU, hyW, rfl⟩
  rw [isDivNear_iff_le_divExp hhol hyC
    (HironakaDivisorPowers.isNonzeroAt_of_isInvertible D.isInvertible yU)]
  change b ≤ divExp (m + 1) D.ideal (Subtype.val '' W.carrier) y ↔ b ≤ a
  rw [horder]

/-- The SAME original log-selected prime family has literal original Cartier
orders and every natural divisibility reader, with its entire-U bound retained. -/
theorem exists_native_common_open_log_prime_orders
    (D : EffectiveDivisor (m + 1) M) (x : M) (g : M → ℂ)
    (hgen : ∀ᶠ y in 𝓝 x, HolomorphicAt (m + 1) g y ∧ ∀ b,
      D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b)
    (c : ℚ) (hc : 0 < c) (u : M → EReal) (R : M → ℝ) (hR : BoundedRealGermAt R x)
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
        (∀ y : centeredChartOpen x Ω, (y : M) ∈ D.support ↔ ∃ i, y ∈ (W i).carrier) ∧
        0 ≤ C ∧ (∀ y, |bU y| ≤ C) ∧
        (∀ y : centeredChartOpen x Ω, u y =
          (∑ i, (((c * (a i : ℚ) : ℚ) : ℝ) : EReal) * logNormSq (p i y)) + (bU y : EReal)) ∧
        ∀ i, ∃ y : centeredChartOpen x Ω, y ∈ (W i).carrier ∧
          RegularAtDim (n := m + 1) D.support (y : M) m ∧
          divExp (m + 1) D.ideal (Subtype.val '' (W i).carrier) (y : M) = a i ∧
          ∀ d : ℕ, IsDivNear (m + 1) D.ideal (Subtype.val '' (W i).carrier) d (y : M) ↔ d ≤ a i := by
  classical
  obtain ⟨hf, hF⟩ := exists_original_generator_nonzero_centered_germ
    D x g hgen.self_of_nhds.1 hgen.self_of_nhds.2
  let e := (complexChartAt (n := m + 1) x).val
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hchart : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxE] using
      (e.continuousAt_symm (e.map_source hxE)).tendsto.comp ht
  have hzero : AnalyticDescendingChain.chartGerm (n := m + 1) D.support x =ᶠ[𝓝 0]
      {z | g (e.symm (z + e x)) = 0} := by
    apply Filter.eventuallyEq_set.mpr
    filter_upwards [ht.eventually (e.open_target.mem_nhds (e.map_source hxE)),
      hchart.eventually hgen] with z hzT hgz
    change (z + e x ∈ e.target ∧ e.symm (z + e x) ∈ D.support) ↔ _
    refine (and_iff_right hzT).trans ?_
    constructor
    · intro hzD
      exact hzD g ((hgz.2 g).mpr (isInSpanAt_self rfl hgz.1))
    · intro hgy b hb
      obtain ⟨_, d, _, heq⟩ := isInSpanAt_eq_iff.mp ((hgz.2 b).mp hb)
      simpa only [hgy, mul_zero] using heq.self_of_nhds
  obtain ⟨Ω, h0Ω, htarget, hxU, hgenU, r, q, hq, a, p, W, B, bU, C,
    hdistinct, hdata, hsupport, hC, hbound, hlog⟩ :=
    exists_native_common_open_prime_logarithmic_remainder D x g hgen c hc u R hR hu
  refine ⟨Ω, h0Ω, htarget, hxU, hgenU, r, q, hq, a, p, W, B, bU, C,
    hdistinct, hdata, hsupport, hC, hbound, hlog, ?_⟩
  intro i
  have hmult : a i = multiplicity (HolGerm.mk (q i) (hq i)) (HolGerm.mk (fun z =>
      g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) hf) := by
    obtain ⟨_, h⟩ := (hdata i).2.2.1
    exact h
  have hapos : 0 < multiplicity (HolGerm.mk (q i) (hq i)) (HolGerm.mk (fun z =>
      g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) hf) := hmult ▸ (hdata i).2.1
  have hW : (W i).carrier = {y | q i (centeredChartHomeomorph x Ω htarget y) = 0} := by
    rw [(hdata i).2.2.2.2.2.2.1, (hdata i).2.2.2.2.2.1]
  obtain ⟨y, hyW, hreg, horder, hdiv⟩ := exists_same_prime_carrier_order_witness
    D x g hf hF hgen hzero (q i) (hq i) (hdata i).1 hapos Ω h0Ω htarget (W i) hW
  refine ⟨y, hyW, hreg, horder.trans hmult.symm, ?_⟩
  intro d
  simpa only [← hmult] using hdiv d

#print axioms exists_native_common_open_log_prime_orders

end SGPT.PSH
