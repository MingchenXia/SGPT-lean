import SGPT.PSH.CartierLocalPrimeEquations
import SGPT.Foundations.Analysis.Pending.ActualPrimeRegularDifferentialAvoidance
import SGPT.Foundations.Analysis.Pending.CompanionReduction

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open InvertibleIdealQuotient RegularLocusComponent AnalyticGermDecomposition
open DivisorExponent GermIdealOrder OrderTaylor IdealOrderArithmetic GermOrderProduct IdealWeightPowers
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual nearby principal generation, a genuine order-one equation and
an actual unit cofactor determine the literal finite Cartier exponent. -/
theorem cartierOrder_eq_of_principal_power_unit (D : EffectiveDivisor n M)
    {C : Set M} {y : M} (g q H : M → ℂ) (a : ℕ)
    (hq : HolomorphicAt n q y) (hH : HolomorphicAt n H y)
    (hqzero : q y = 0) (hHne : H y ≠ 0)
    (hqorder : ¬(idealPow (pointIdeal n y) 2).mem y q)
    (hgen : ∀ᶠ z in 𝓝 y, ∀ b, D.ideal.mem z b ↔ IsInSpanAt (n := n) (· = g) z b)
    (hfactor : g =ᶠ[𝓝 y] fun z => q z ^ a * H z)
    (hC : ∀ᶠ z in 𝓝 y, z ∈ C ↔ q z = 0) :
    divExp n D.ideal C y = a := by
  have hhol : ∀ z b, D.ideal.mem z b → HolomorphicAt n b z :=
    fun _ _ hb => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hb
  have hyC : y ∈ C := hC.self_of_nhds.mpr hqzero
  have hghol : HolomorphicAt n g y :=
    ((CompanionReduction.holomorphicAt_pow_of hq a).mul hH).congr hfactor.symm
  have hgmem : D.ideal.mem y g := hgen.self_of_nhds g |>.mpr (isInSpanAt_self rfl hghol)
  have hdiv : IsDivNear n D.ideal C a y := by
    filter_upwards [hq.eventually, hH.eventually, hgen, hfactor.eventually_nhds, hC]
      with z hqz hHz hgenz hfactorz hCz hzC
    have hqmem : (pointIdeal n z).mem z q := mem_pointIdeal_of_apply_eq_zero hqz (hCz.mp hzC)
    have hpow := MonomialPart.pow_mem_idealPow hqmem hqz a
    have hgm : (idealPow (pointIdeal n z) a).mem z g := by
      apply mem_idealPow_congr (mul_mem_idealPow hHz hpow)
      filter_upwards [hfactorz] with w hw
      exact (mul_comm (H w) (q w ^ a)).trans hw.symm
    refine ⟨mem_univ z, fun b hb => IsInSpanAt.vanishesToOrderOn ((hgenz b).mp hb) ?_⟩
    rintro _ rfl
    exact vanishesToOrderOn_of_mem hgm
  have hHorder : ¬(idealPow (pointIdeal n y) (0 + 1)).mem y H := by
    intro h
    exact hHne (apply_eq_zero_of_mem_idealPow_pointIdeal (le_refl 1) h)
  have hqpow : ¬(idealPow (pointIdeal n y) (a + 1)).mem y (fun z => q z ^ a) := by
    simpa only [Nat.mul_one] using CompanionReduction.pow_notMem_idealPow hq hqorder a
  have hprod : ¬(idealPow (pointIdeal n y) (a + 1)).mem y (fun z => q z ^ a * H z) := by
    simpa only [Nat.add_zero] using
      mul_notMem_idealPow (CompanionReduction.holomorphicAt_pow_of hq a) hH hqpow hHorder
  have hnot : ¬IsDivNear n D.ideal C (a + 1) y := by
    intro hbad
    exact hprod (mem_idealPow_congr
      (mem_idealPow_of_vanishesToOrderOn_univ ((hbad.self_of_nhds hyC).2 g hgmem)) hfactor)
  have hnon := HironakaDivisorPowers.isNonzeroAt_of_isInvertible D.isInvertible y
  have hle := (isDivNear_iff_le_divExp hhol hyC hnon).mp hdiv
  have hlt : ¬a + 1 ≤ divExp n D.ideal C y := by
    intro h
    exact hnot ((isDivNear_iff_le_divExp hhol hyC hnon).mpr h)
  omega


section Branch

variable {m : ℕ} {Z : Type u} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]

/-- Every original prime branch of a retained actual Cartier generator has
its germ multiplicity equal to the SAME produced geometric coefficient.
The actual nonzero differential and transversal unit piece are produced internally. -/
theorem regularComponentOrder_eq_primeGerm_multiplicity
    (D : EffectiveDivisor (m + 1) Z) (x : Z) (g : Z → ℂ)
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
    (B : GlobalComponents.globalComponents (n := m + 1) D.support)
    (hbranch : {z | q z = 0} ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := m + 1) (cartierPrimeComponent D B).carrier x) :
    regularComponentOrder D D.support B = multiplicity (HolGerm.mk q hq)
      (HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) hf) := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  let e := (complexChartAt (n := m + 1) x).val
  let f : ComplexModel (m + 1) → ℂ := fun z => g (e.symm (z + e x))
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  have hsubB : (B : Set Z) ⊆ D.support :=
    GlobalComponents.subset_of_mem_globalComponents (cartierSupport_isComplexAnalytic D) B.property
  have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), q z = 0 → f z = 0 := by
    filter_upwards [hbranch, Filter.eventuallyEq_set.mp hzero] with z hzB hzF hzQ
    have hyB := (hzB hzQ).2
    rw [cartierPrimeComponent_carrier] at hyB
    exact hzF.mp ⟨(hzB hzQ).1, hsubB hyB⟩
  have hdiv : HolGerm.mk q hq ∣ HolGerm.mk f hf := by
    apply Ideal.mem_span_singleton.mp
    rw [← (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1]
    exact mem_vanishingIdeal_mk.mpr hvan
  obtain ⟨G, hfactor, hnot⟩ :=
    (FiniteMultiplicity.of_prime_left hQ hF).exists_eq_pow_mul_and_not_dvd
  obtain ⟨H, hH, hGrep⟩ := HolGerm.exists_eq_mk G
  let a := multiplicity (HolGerm.mk q hq) (HolGerm.mk f hf)
  have ha : 0 < a := multiplicity_pos_of_dvd hdiv
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
      (q z = 0 → z ∈ AnalyticDescendingChain.chartGerm (n := m + 1)
        (cartierPrimeComponent D B).carrier x) ∧ z + e x ∈ e.target ∧
      (∀ᶠ w in 𝓝 (e.symm (z + e x)), HolomorphicAt (m + 1) g w ∧ ∀ b,
        D.ideal.mem w b ↔ IsInSpanAt (n := m + 1) (· = g) w b) := by
    filter_upwards [hq, hH, hfactor', Filter.eventuallyEq_set.mp hzero, hbranch,
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
  have hyE : y ∈ e.source := e.map_target hzT
  have hreg : RegularAtDim (n := m + 1) D.support y m :=
    DimensionMonotone.regularAtDim_of_chartGerm hregchart
  have hyB : y ∈ (B : Set Z) := by
    rw [← cartierPrimeComponent_carrier D B]
    exact (hzB hqzero).2
  let Qloc : Z → ℂ := fun w => q (e w - e x)
  let Hloc : Z → ℂ := fun w => H (e w - e x)
  have hshift : Tendsto (fun w : ComplexModel (m + 1) => w - e x) (𝓝 (e y)) (𝓝 z) := by
    simpa only [y, e.right_inv hzT, add_sub_cancel_right] using
      (show ContinuousAt (fun w : ComplexModel (m + 1) => w - e x) (e y) from
        continuousAt_id.sub_const (e x)).tendsto
  have hcomp (W : ComplexModel (m + 1) → ℂ)
      (hW : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ W w) :
      HolomorphicAt (m + 1) (fun w : Z => W (e w - e x)) y := by
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
  have hforward : Tendsto (fun w : Z => e w - e x) (𝓝 y) (𝓝 z) := by
    simpa only [y, e.right_inv hzT, add_sub_cancel_right] using (e.continuousAt hyE).sub_const (e x)
  have hlocalC : ∀ᶠ w in 𝓝 y, w ∈ D.support ↔ Qloc w = 0 := by
    filter_upwards [e.open_source.mem_nhds hyE,
      hforward.eventually (hO.mem_nhds hzO)] with w hwE hwO
    have hchartiff : e w - e x ∈ AnalyticDescendingChain.chartGerm (n := m + 1) D.support x ↔
        w ∈ D.support := by
      change (e w - e x + e x ∈ e.target ∧ e.symm (e w - e x + e x) ∈ D.support) ↔ _
      rw [sub_add_cancel, e.left_inv hwE]
      exact and_iff_right (e.map_source hwE)
    exact hchartiff.symm.trans (hqiff _ hwO).symm
  have hlocalfactor : g =ᶠ[𝓝 y] fun w => Qloc w ^ a * Hloc w := by
    filter_upwards [e.open_source.mem_nhds hyE,
      hforward.eventually (hN.mem_nhds hzN)] with w hwE hwN
    have hfw : g (e.symm (e w - e x + e x)) = q (e w - e x) ^ a * H (e w - e x) :=
      (hNsub hwN).2.2.1
    simpa only [sub_add_cancel, e.left_inv hwE] using hfw
  have horder : divExp (m + 1) D.ideal D.support y = a :=
    cartierOrder_eq_of_principal_power_unit D g Qloc Hloc a hQhol hHhol hQzero hHunit hQorder
      (hgeny.mono fun w hw => hw.2) hlocalfactor hlocalC
  exact (regularComponentOrder_eq D D.support B hreg
    (globalComponent_eq_closure_of_regular_mem B hreg hyB)).trans horder

end Branch
end SGPT.PSH
