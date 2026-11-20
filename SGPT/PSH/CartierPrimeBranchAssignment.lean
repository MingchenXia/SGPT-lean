import SGPT.PSH.CartierPrimeOrders
import SGPT.Foundations.Analysis.Pending.ActualPrimeGermFiniteCover

set_option autoImplicit false
noncomputable section


namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open InvertibleIdealQuotient RegularLocusComponent AnalyticGermDecomposition
open scoped Topology Manifold ContDiff

universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- At EVERY point the original invertible Cartier ideal produces an actual
nonzero equation of its literal support in the original centered chart. -/
theorem exists_cartier_centered_equation (D : EffectiveDivisor (m + 1) M) (x : M) :
    ∃ (f : ComplexModel (m + 1) → ℂ)
      (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z),
      HolGerm.mk f hf ≠ 0 ∧
        AnalyticDescendingChain.chartGerm (n := m + 1) D.support x =ᶠ[𝓝 0] {z | f z = 0} := by
  obtain ⟨U, hU, hxU, g, hg, hnon, hgen⟩ := D.isInvertible x
  have hhol : ∀ y ∈ U, HolomorphicAt (m + 1) g y :=
    fun y hy => holomorphicAt_of_mdifferentiableOn hU hg hy
  have hzeros : ∀ y ∈ U, y ∈ D.support ↔ g y = 0 := by
    intro y hy
    constructor
    · intro hyD
      exact hyD g ((hgen y hy g).mpr (isInSpanAt_self rfl (hhol y hy)))
    · intro hgy
      change ∀ a, D.ideal.mem y a → a y = 0
      intro a ha
      obtain ⟨_, b, _, heq⟩ :=
        isInSpanAt_eq_iff.mp ((hgen y hy a).mp ha)
      simpa only [hgy, mul_zero] using heq.self_of_nhds
  let e := (complexChartAt (n := m + 1) x).val
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  let f : ComplexModel (m + 1) → ℂ := fun z => g (e.symm (z + e x))
  have hchartHol : ∀ᶠ w in 𝓝 (e x),
      DifferentiableAt ℂ (fun w : ComplexModel (m + 1) => g (e.symm w)) w :=
    CartanLocalReduction.holAt_comp_chart_symm (x := x) hxE (hhol x hxU)
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z := by
    filter_upwards [ht.eventually hchartHol] with z hz
    change DifferentiableAt ℂ
      ((fun w : ComplexModel (m + 1) => g (e.symm w)) ∘ fun z => z + e x) z
    exact hz.comp z (differentiableAt_id.add_const (e x))
  have hF : HolGerm.mk f hf ≠ 0 := by
    intro hbad
    have hz : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f z = 0 :=
      HolGerm.mk_eq_mk_iff.mp
        (hbad.trans (HolGerm.mk_zero (E := ComplexModel (m + 1))).symm)
    have hce : Tendsto (fun y : M => e y - e x) (𝓝 x) (𝓝 0) := by
      simpa only [sub_self] using (e.continuousAt hxE).sub_const (e x)
    have hgzero : ∀ᶠ y in 𝓝 x, g y = 0 := by
      filter_upwards [hce.eventually hz, e.open_source.mem_nhds hxE] with y hy hyE
      change g (e.symm ((e y - e x) + e x)) = 0 at hy
      simpa only [sub_add_cancel, e.left_inv hyE] using hy
    obtain ⟨W, hWsub, hW, hxW⟩ :=
      _root_.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hxU) hgzero)
    obtain ⟨y, hyW, hgy⟩ := hnon W hW (fun _ hy => (hWsub hy).1) ⟨x, hxW⟩
    exact hgy (hWsub hyW).2
  have hr : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxE] using
      (e.continuousAt_symm (e.map_source hxE)).tendsto.comp ht
  have htarget : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z + e x ∈ e.target :=
    ht.eventually (e.open_target.mem_nhds (e.map_source hxE))
  have hcoordU : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), e.symm (z + e x) ∈ U :=
    hr.eventually (hU.mem_nhds hxU)
  refine ⟨f, hf, hF, Filter.eventuallyEq_set.mpr ?_⟩
  filter_upwards [htarget, hcoordU] with z hzT hzU
  change (z + e x ∈ e.target ∧ e.symm (z + e x) ∈ D.support) ↔ f z = 0
  exact (and_iff_right hzT).trans (hzeros _ hzU)

/-- EVERY specified actual prime factor of the original nonzero equation
produces frequent regular points of the original support on that same branch. -/
theorem frequently_regular_zero_on_prime_factor
    (f : ComplexModel (m + 1) → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hF : HolGerm.mk f hf ≠ 0)
    (q : ComplexModel (m + 1) → ℂ)
    (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
    (hQ : Prime (HolGerm.mk q hq)) (hdiv : HolGerm.mk q hq ∣ HolGerm.mk f hf) :
    ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      q z = 0 ∧ RegularAtDim (n := m + 1) {w | f w = 0} z m := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  obtain ⟨G, hfactor, hnot⟩ :=
    (FiniteMultiplicity.of_prime_left hQ hF).exists_eq_pow_mul_and_not_dvd
  obtain ⟨g, hg, hGrep⟩ := HolGerm.exists_eq_mk G
  let a := multiplicity (HolGerm.mk q hq) (HolGerm.mk f hf)
  have ha : 0 < a := multiplicity_pos_of_dvd hdiv
  have heq : f =ᶠ[𝓝 0] fun z => q z ^ a * g z := by
    apply HolGerm.mk_eq_mk_iff.mp
    rw [HolGerm.mk_mul (fun z => q z ^ a) g (eventually_differentiableAt_pow hq a) hg,
      HolGerm.mk_pow q hq a, ← hGrep]
    exact hfactor
  have hnot' : ¬HolGerm.mk q hq ∣ HolGerm.mk g hg := by
    simpa only [hGrep] using hnot
  have hfreq := ActualPrimeRegularFiniteAvoidance.frequently_regular_zero_avoiding_finite_family
    q hq hQ (fun _ : Fin 1 => g) (fun _ => hg) (fun _ => hnot')
  obtain ⟨N, hNsub, hN, h0N⟩ := _root_.mem_nhds_iff.mp (hg.and heq)
  rw [Filter.frequently_iff]
  intro S hS
  obtain ⟨z, hzS, ⟨⟨hqzero, hqreg, hgtest⟩, hzN⟩⟩ :=
    Filter.frequently_iff.mp (hfreq.and_eventually (hN.mem_nhds h0N)) hS
  have hgne : g z ≠ 0 := hgtest 0
  have hznear : ∀ᶠ w in 𝓝 z, w ∈ N := hN.mem_nhds hzN
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ N ∧ g w ≠ 0 :=
    hznear.and ((hNsub hzN).1.continuousAt.eventually_ne hgne)
  obtain ⟨O, hOsub, hO, hzO⟩ := _root_.mem_nhds_iff.mp hnear
  have hzeros : {w | q w = 0} ∩ O = {w | f w = 0} ∩ O := by
    ext w
    constructor
    · rintro ⟨hqw, hwO⟩
      refine ⟨?_, hwO⟩
      change q w = 0 at hqw
      change f w = 0
      have hfw : f w = q w ^ a * g w := (hNsub (hOsub hwO).1).2
      rw [hfw, hqw, zero_pow ha.ne', zero_mul]
    · rintro ⟨hfw, hwO⟩
      refine ⟨?_, hwO⟩
      have hmul : q w ^ a * g w = 0 := (hNsub (hOsub hwO).1).2.symm.trans hfw
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hmul).resolve_right (hOsub hwO).2)
  exact ⟨z, hzS, hqzero,
    RegularPointDimension.regularAtDim_of_inter_eq hO hzO hzeros hqreg⟩

section Regular

variable {n : ℕ} {Z : Type u} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- A true regular point belongs to exactly the closure of its own actual
regular component, even when the original support has singular branches elsewhere. -/
theorem globalComponent_eq_closure_of_regular_mem {A : Set Z}
    (B : GlobalComponents.globalComponents (n := n) A) {x : Z} {k : ℕ}
    (hx : RegularAtDim (n := n) A x k) (hxB : x ∈ (B : Set Z)) :
    (B : Set Z) = closure (component (n := n) A x) := by
  obtain ⟨c, ⟨j, hc⟩, hB⟩ := B.property
  obtain ⟨W, hW, hxW, hWC, _, _⟩ := exists_isOpen_inter_subset (mem_component_self hx) hx
  obtain ⟨y, hyW, hyC⟩ := _root_.mem_closure_iff.mp (hB ▸ hxB) W hW hxW
  have hyX := hWC ⟨component_subset A c hyC, hyW⟩
  exact hB.trans (congrArg closure
    ((connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hyX).symm))

end Regular

/-- Each original singular prime branch selects a UNIQUE member of the SAME
actual locally finite Cartier prime family, with the actual reduced-ideal relation.
The only branch input is containment in the ORIGINAL support chart germ. -/
theorem exists_unique_cartierPrimeComponent_of_chart_prime
    (D : EffectiveDivisor (m + 1) M) (x : M)
    (q : ComplexModel (m + 1) → ℂ)
    (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
    (hQ : Prime (HolGerm.mk q hq))
    (hsub : {z | q z = 0} ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := m + 1) D.support x) :
    ∃! B : GlobalComponents.globalComponents (n := m + 1) D.support,
      ({z | q z = 0} ≤ᶠ[𝓝 0]
        AnalyticDescendingChain.chartGerm (n := m + 1) (cartierPrimeComponent D B).carrier x) ∧
      vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1)
        (cartierPrimeComponent D B).carrier x) ≤ Ideal.span {HolGerm.mk q hq} := by
  classical
  let e := (complexChartAt (n := m + 1) x).val
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hr : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxE] using
      (e.continuousAt_symm (e.map_source hxE)).tendsto.comp ht
  obtain ⟨T, hxT, hfinite⟩ := locallyFinite_cartierPrimeComponents D x
  let S := {B : GlobalComponents.globalComponents (n := m + 1) D.support |
    ((cartierPrimeComponent D B).carrier ∩ T).Nonempty}
  let : Fintype S := hfinite.fintype
  let A : S → Set (ComplexModel (m + 1)) := fun B =>
    AnalyticDescendingChain.chartGerm (n := m + 1) (cartierPrimeComponent D B.val).carrier x
  have hcover : {z | q z = 0} ≤ᶠ[𝓝 0] (⋃ B, A B) := by
    filter_upwards [hsub, hr.eventually hxT] with z hz hzT
    intro hqz
    have hzD := hz hqz
    change z + e x ∈ e.target ∧ e.symm (z + e x) ∈ D.support at hzD
    obtain ⟨B, hzB⟩ := mem_iUnion.mp ((cartierPrimeComponents_cover D).symm ▸ hzD.2)
    have hBS : B ∈ S := ⟨e.symm (z + e x), hzB, hzT⟩
    exact mem_iUnion.mpr ⟨⟨B, hBS⟩, hzD.1, hzB⟩
  obtain ⟨B, hbranch, hideal⟩ := ActualPrimeGermFiniteCover.exists_member_and_vanishingIdeal_le
    q hq hQ A (fun B => AnalyticDescendingChain.isAnalyticGerm_chartGerm
      (cartierPrimeComponent D B.val).analytic x) hcover
  refine ⟨B.val, ⟨hbranch, hideal⟩, ?_⟩
  intro W hW
  obtain ⟨f, hf, hF, hzeroeq⟩ := exists_cartier_centered_equation D x
  have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), q z = 0 → f z = 0 := by
    filter_upwards [hsub, Filter.eventuallyEq_set.mp hzeroeq] with z hz heq hzQ
    exact heq.mp (hz hzQ)
  have hdiv : HolGerm.mk q hq ∣ HolGerm.mk f hf := by
    apply Ideal.mem_span_singleton.mp
    rw [← (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible
      q hq hQ).1]
    exact mem_vanishingIdeal_mk.mpr hvan
  have hconditions : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      (z ∈ AnalyticDescendingChain.chartGerm (n := m + 1) D.support x ↔ f z = 0) ∧
      (q z = 0 → z ∈ AnalyticDescendingChain.chartGerm (n := m + 1)
        (cartierPrimeComponent D B.val).carrier x) ∧
      (q z = 0 → z ∈ AnalyticDescendingChain.chartGerm (n := m + 1)
        (cartierPrimeComponent D W).carrier x) := by
    filter_upwards [Filter.eventuallyEq_set.mp hzeroeq, hbranch, hW.1] with z hz hzB hzW
    exact ⟨hz, hzB, hzW⟩
  obtain ⟨N, hNsub, hN, h0N⟩ := _root_.mem_nhds_iff.mp hconditions
  obtain ⟨z, hzN, hzQ, hzreg⟩ := Filter.frequently_iff.mp
    (frequently_regular_zero_on_prime_factor f hf hF q hq hQ hdiv) (hN.mem_nhds h0N)
  have heq : {z | f z = 0} ∩ N =
      AnalyticDescendingChain.chartGerm (n := m + 1) D.support x ∩ N := by
    ext z
    exact and_congr_left fun hzN => (hNsub hzN).1.symm
  have hregchart := RegularPointDimension.regularAtDim_of_inter_eq hN hzN heq hzreg
  have hreg : RegularAtDim (n := m + 1) D.support (e.symm (z + e x)) m :=
    DimensionMonotone.regularAtDim_of_chartGerm hregchart
  have hzB : e.symm (z + e x) ∈ (B.val : Set M) := by
    rw [← cartierPrimeComponent_carrier D B.val]
    exact ((hNsub hzN).2.1 hzQ).2
  have hzW : e.symm (z + e x) ∈ (W : Set M) := by
    rw [← cartierPrimeComponent_carrier D W]
    exact ((hNsub hzN).2.2 hzQ).2
  exact Subtype.ext ((globalComponent_eq_closure_of_regular_mem W hreg hzW).trans
    (globalComponent_eq_closure_of_regular_mem B.val hreg hzB).symm)

end SGPT.PSH
