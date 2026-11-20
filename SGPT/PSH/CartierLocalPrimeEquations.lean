import SGPT.PSH.CartierPrimeBranchAssignment
import SGPT.Foundations.Analysis.Pending.ActualReducedHolomorphicEquation

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

/-- The original nearby divisor stalk generator is retained together with
its actual nonzero centered germ and literal support equation. -/
theorem exists_cartier_centered_stalk_generator (D : EffectiveDivisor (m + 1) M) (x : M) :
    ∃ (g : M → ℂ)
      (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ
        (fun z => g ((complexChartAt (n := m + 1) x).val.symm
          (z + (complexChartAt (n := m + 1) x).val x))) z),
      HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) hf ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, HolomorphicAt (m + 1) g y ∧ ∀ a,
        D.ideal.mem y a ↔ IsInSpanAt (n := m + 1) (· = g) y a) ∧
      AnalyticDescendingChain.chartGerm (n := m + 1) D.support x =ᶠ[𝓝 0]
        {z | g ((complexChartAt (n := m + 1) x).val.symm
          (z + (complexChartAt (n := m + 1) x).val x)) = 0} := by
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
  refine ⟨g, hf, hF, ?_, Filter.eventuallyEq_set.mpr ?_⟩
  · filter_upwards [hU.mem_nhds hxU] with y hy
    exact ⟨hhol y hy, hgen y hy⟩
  · filter_upwards [htarget, hcoordU] with z hzT hzU
    change (z + e x ∈ e.target ∧ e.symm (z + e x) ∈ D.support) ↔ f z = 0
    exact (and_iff_right hzT).trans (hzeros _ hzU)

/-- The SAME actual possibly singular geometric carrier internally produces
its nonzero squarefree original chart equation and exact reduced HolGerm ideal. -/
theorem exists_reduced_cartierPrimeComponent_equation (D : EffectiveDivisor (m + 1) M)
    (B : GlobalComponents.globalComponents (n := m + 1) D.support) (x : M) :
    ∃ (r : ComplexModel (m + 1) → ℂ)
      (hr : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ r z),
      HolGerm.mk r hr ≠ 0 ∧ Squarefree (HolGerm.mk r hr) ∧
      vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1)
        (cartierPrimeComponent D B).carrier x) = Ideal.span {HolGerm.mk r hr} ∧
      AnalyticDescendingChain.chartGerm (n := m + 1)
        (cartierPrimeComponent D B).carrier x =ᶠ[𝓝 0] {z | r z = 0} := by
  obtain ⟨f, hf, hF, hzero⟩ := ActualCodimensionOneLocalEquations.exists_nonzero_local_equation
    (cartierPrimeComponent D B) (cartierPrimeComponent_dim D B) x
  obtain ⟨r, hr, hR, hsR, hI, hfr⟩ :=
    ActualReducedHolomorphicEquation.exists_reduced_equation f hf hF
  exact ⟨r, hr, hR, hsR, (vanishingIdeal_congr hzero).trans hI,
    hzero.trans (Filter.eventuallyEq_set.mpr hfr)⟩

private theorem prime_dvd_iff_zeroGerm_le {n : ℕ}
    (f q : ComplexModel n → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
    (hQ : Prime (HolGerm.mk q hq)) :
    HolGerm.mk q hq ∣ HolGerm.mk f hf ↔ {z | q z = 0} ≤ᶠ[𝓝 0] {z | f z = 0} := by
  rw [← Ideal.mem_span_singleton,
    ← (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1]
  exact mem_vanishingIdeal_mk


/-- The ORIGINAL divisor and point internally produce the actual nearby
stalk generator, a finite same-carrier catalog and reduced equations, with
COMPLETE prime-support and pairwise disjoint factor relations at singular points. -/
theorem exists_cartier_local_prime_equations (D : EffectiveDivisor (m + 1) M) (x : M) :
    ∃ (g : M → ℂ)
      (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ
        (fun z => g ((complexChartAt (n := m + 1) x).val.symm
          (z + (complexChartAt (n := m + 1) x).val x))) z),
      HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) hf ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, HolomorphicAt (m + 1) g y ∧ ∀ a,
        D.ideal.mem y a ↔ IsInSpanAt (n := m + 1) (· = g) y a) ∧
      AnalyticDescendingChain.chartGerm (n := m + 1) D.support x =ᶠ[𝓝 0]
        {z | g ((complexChartAt (n := m + 1) x).val.symm
          (z + (complexChartAt (n := m + 1) x).val x)) = 0} ∧
      ∃ T ∈ 𝓝 x, ∃ S : Finset (GlobalComponents.globalComponents (n := m + 1) D.support),
        (∀ y ∈ T, y ∈ D.support ↔ ∃ B ∈ S, y ∈ (cartierPrimeComponent D B).carrier) ∧
        ∃ (r : GlobalComponents.globalComponents (n := m + 1) D.support →
            ComplexModel (m + 1) → ℂ)
          (hr : ∀ B, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (r B) z),
          (∀ B, HolGerm.mk (r B) (hr B) ≠ 0 ∧ Squarefree (HolGerm.mk (r B) (hr B)) ∧
            vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1)
              (cartierPrimeComponent D B).carrier x) = Ideal.span {HolGerm.mk (r B) (hr B)} ∧
            AnalyticDescendingChain.chartGerm (n := m + 1)
              (cartierPrimeComponent D B).carrier x =ᶠ[𝓝 0] {z | r B z = 0}) ∧
          (∀ Q : HolGerm (ComplexModel (m + 1)), Prime Q →
            (Q ∣ HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
              (z + (complexChartAt (n := m + 1) x).val x))) hf ↔
                ∃ B ∈ S, Q ∣ HolGerm.mk (r B) (hr B))) ∧
          (∀ Q : HolGerm (ComplexModel (m + 1)), Prime Q → ∀ B C,
            Q ∣ HolGerm.mk (r B) (hr B) → Q ∣ HolGerm.mk (r C) (hr C) → B = C) := by
  classical
  obtain ⟨g, hf, hF, hgen, hzero⟩ := exists_cartier_centered_stalk_generator D x
  let e := (complexChartAt (n := m + 1) x).val
  let f : ComplexModel (m + 1) → ℂ := fun z => g (e.symm (z + e x))
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 (e x) (zero_add _)
  have hchart : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxE] using
      (e.continuousAt_symm (e.map_source hxE)).tendsto.comp ht
  obtain ⟨T, hxT, hfinite⟩ := locallyFinite_cartierPrimeComponents D x
  let S : Finset (GlobalComponents.globalComponents (n := m + 1) D.support) := hfinite.toFinset
  have hS (B : GlobalComponents.globalComponents (n := m + 1) D.support) :
      B ∈ S ↔ ((cartierPrimeComponent D B).carrier ∩ T).Nonempty := hfinite.mem_toFinset
  have hcover : ∀ y ∈ T, y ∈ D.support ↔ ∃ B ∈ S, y ∈ (cartierPrimeComponent D B).carrier := by
    intro y hyT
    constructor
    · intro hyD
      obtain ⟨B, hyB⟩ := mem_iUnion.mp ((cartierPrimeComponents_cover D).symm ▸ hyD)
      exact ⟨B, (hS B).mpr ⟨y, hyB, hyT⟩, hyB⟩
    · rintro ⟨B, _, hyB⟩
      exact (cartierPrimeComponents_cover D) ▸ mem_iUnion.mpr ⟨B, hyB⟩
  choose r hr hR hsR hI hzR using fun B => exists_reduced_cartierPrimeComponent_equation D B x
  have hPsub (B : GlobalComponents.globalComponents (n := m + 1) D.support) :
      AnalyticDescendingChain.chartGerm (n := m + 1) (cartierPrimeComponent D B).carrier x ≤ᶠ[𝓝 0]
        AnalyticDescendingChain.chartGerm (n := m + 1) D.support x := by
    refine Eventually.of_forall fun z hz => ⟨hz.1, ?_⟩
    have hzB := hz.2
    rw [cartierPrimeComponent_carrier] at hzB
    exact GlobalComponents.subset_of_mem_globalComponents (cartierSupport_isComplexAnalytic D)
      B.property hzB
  have hbranch (q : ComplexModel (m + 1) → ℂ)
      (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z) (hQ : Prime (HolGerm.mk q hq))
      (B : GlobalComponents.globalComponents (n := m + 1) D.support)
      (hdiv : HolGerm.mk q hq ∣ HolGerm.mk (r B) (hr B)) :
      {z | q z = 0} ≤ᶠ[𝓝 0]
        AnalyticDescendingChain.chartGerm (n := m + 1) (cartierPrimeComponent D B).carrier x := by
    filter_upwards [(prime_dvd_iff_zeroGerm_le (r B) q (hr B) hq hQ).mp hdiv,
      Filter.eventuallyEq_set.mp (hzR B)] with z hz heq hzQ
    exact heq.mpr (hz hzQ)
  have hideal (q : ComplexModel (m + 1) → ℂ)
      (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
      (B : GlobalComponents.globalComponents (n := m + 1) D.support)
      (hdiv : HolGerm.mk q hq ∣ HolGerm.mk (r B) (hr B)) :
      vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1)
        (cartierPrimeComponent D B).carrier x) ≤ Ideal.span {HolGerm.mk q hq} := by
    rw [hI B]
    exact Ideal.span_le.mpr (by rintro _ rfl; exact Ideal.mem_span_singleton.mpr hdiv)
  refine ⟨g, hf, hF, hgen, hzero, T, hxT, S, hcover, r, hr,
    (fun B => ⟨hR B, hsR B, hI B, hzR B⟩), ?_, ?_⟩
  · intro Q hQ
    obtain ⟨q, hq, rfl⟩ := HolGerm.exists_eq_mk Q
    constructor
    · intro hdiv
      have hsub : {z | q z = 0} ≤ᶠ[𝓝 0]
          AnalyticDescendingChain.chartGerm (n := m + 1) D.support x := by
        filter_upwards [(prime_dvd_iff_zeroGerm_le f q hf hq hQ).mp hdiv,
          Filter.eventuallyEq_set.mp hzero] with z hz heq hzQ
        exact heq.mpr (hz hzQ)
      let A : {B // B ∈ S} → Set (ComplexModel (m + 1)) := fun B =>
        AnalyticDescendingChain.chartGerm (n := m + 1) (cartierPrimeComponent D B.val).carrier x
      have hqcover : {z | q z = 0} ≤ᶠ[𝓝 0] (⋃ B, A B) := by
        filter_upwards [hsub, hchart.eventually hxT] with z hz hzT hzQ
        have hzD := hz hzQ
        obtain ⟨B, hBS, hzB⟩ := (hcover _ hzT).mp hzD.2
        exact mem_iUnion.mpr ⟨⟨B, hBS⟩, hzD.1, hzB⟩
      obtain ⟨B, _, hBI⟩ := ActualPrimeGermFiniteCover.exists_member_and_vanishingIdeal_le
        q hq hQ A (fun B => AnalyticDescendingChain.isAnalyticGerm_chartGerm
          (cartierPrimeComponent D B.val).analytic x) hqcover
      refine ⟨B.val, B.property, Ideal.mem_span_singleton.mp (hBI ?_)⟩
      rw [hI B.val]
      exact Ideal.mem_span_singleton_self _
    · rintro ⟨B, _, hdiv⟩
      apply (prime_dvd_iff_zeroGerm_le f q hf hq hQ).mpr
      filter_upwards [hbranch q hq hQ B hdiv, hPsub B,
        Filter.eventuallyEq_set.mp hzero] with z hz hzsub heq hzQ
      exact heq.mp (hzsub (hz hzQ))
  · intro Q hQ B C hQB hQC
    obtain ⟨q, hq, rfl⟩ := HolGerm.exists_eq_mk Q
    have hqB := hbranch q hq hQ B hQB
    have hqC := hbranch q hq hQ C hQC
    have hsub : {z | q z = 0} ≤ᶠ[𝓝 0]
        AnalyticDescendingChain.chartGerm (n := m + 1) D.support x := hqB.trans (hPsub B)
    obtain ⟨E, _, huniq⟩ := exists_unique_cartierPrimeComponent_of_chart_prime D x q hq hQ hsub
    exact (huniq B ⟨hqB, hideal q hq B hQB⟩).trans (huniq C ⟨hqC, hideal q hq C hQC⟩).symm

end SGPT.PSH
