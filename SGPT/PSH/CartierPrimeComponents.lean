import SGPT.PSH.NonzeroHypersurfaceRegular
import SGPT.Foundations.Analysis.Pending.CartanLocalReduction
import SGPT.Foundations.Analysis.Pending.DimensionMonotone
import SGPT.Foundations.Analysis.Pending.IrreducibleComponentFilling
import SGPT.Foundations.Analysis.Pending.StepFourNoComponentContainsW

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open InvertibleIdealQuotient RegularLocusComponent
open scoped Topology Manifold ContDiff

universe u
variable {m : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Coherence of the actual invertible ideal produces analyticity of its
literal support; no analytic-support certificate is supplied. -/
theorem cartierSupport_isComplexAnalytic (D : EffectiveDivisor (m + 1) M) :
    IsComplexAnalyticSubset (n := m + 1) D.support :=
  StepFourNoComponentContainsW.isComplexAnalyticSubset_zeroLocus
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)

/-- The actual nonzero generators of every divisor stalk internally supply
dense regular hypersurface points of the SAME literal support. -/
theorem cartierSupport_subset_closure_regularLocus (D : EffectiveDivisor (m + 1) M) :
    D.support ⊆ closure (regularLocus (n := m + 1) D.support m) := by
  intro x hx
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
  have hfzero : f 0 = 0 := by
    change g (e.symm (0 + e x)) = 0
    simpa only [zero_add, e.left_inv hxE] using (hzeros x hxU).mp hx
  have hr : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv hxE] using
      (e.continuousAt_symm (e.map_source hxE)).tendsto.comp ht
  have htarget : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z + e x ∈ e.target :=
    ht.eventually (e.open_target.mem_nhds (e.map_source hxE))
  have hcoordU : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), e.symm (z + e x) ∈ U :=
    hr.eventually (hU.mem_nhds hxU)
  obtain ⟨N, hNsub, hN, h0N⟩ := _root_.mem_nhds_iff.mp (htarget.and hcoordU)
  let A := AnalyticDescendingChain.chartGerm (n := m + 1) D.support x
  have heq : A ∩ N = {z | f z = 0} ∩ N := by
    ext z
    constructor
    · rintro ⟨hzA, hzN⟩
      change z + e x ∈ e.target ∧ e.symm (z + e x) ∈ D.support at hzA
      exact ⟨(hzeros _ (hNsub hzN).2).mp hzA.2, hzN⟩
    · rintro ⟨hzf, hzN⟩
      refine ⟨?_, hzN⟩
      change z + e x ∈ e.target ∧ e.symm (z + e x) ∈ D.support
      exact ⟨(hNsub hzN).1, (hzeros _ (hNsub hzN).2).mpr hzf⟩
  apply _root_.mem_closure_iff.mpr
  intro O hO hxO
  have hcoordO : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), e.symm (z + e x) ∈ O :=
    hr.eventually (hO.mem_nhds hxO)
  obtain ⟨z, ⟨hzN, hzO⟩, _, hzreg⟩ := Filter.frequently_iff.mp
    (frequently_regular_zero_of_nonzero_holomorphic_germ f hf hF hfzero)
    (inter_mem (hN.mem_nhds h0N) hcoordO)
  have hregA : RegularAtDim (n := m + 1) (M := ComplexModel (m + 1)) A z m :=
    RegularPointDimension.regularAtDim_of_inter_eq hN hzN heq.symm hzreg
  exact ⟨e.symm (z + e x), hzO, DimensionMonotone.regularAtDim_of_chartGerm hregA⟩

/-- An actual flattening and the produced hypersurface density identify
the dimension at EVERY regular point of the literal Cartier support. -/
theorem cartierSupport_regular_dimension (D : EffectiveDivisor (m + 1) M)
    {x : M} {k : ℕ} (hx : RegularAtDim (n := m + 1) D.support x k) : k = m := by
  obtain ⟨F, _⟩ := exists_flatBall hx (N := univ) isOpen_univ (mem_univ x)
  obtain ⟨z, hzN, hzreg⟩ := _root_.mem_closure_iff.mp
    (cartierSupport_subset_closure_regularLocus D hx.2.1) F.nbhd F.isOpen_nbhd F.mem_nbhd
  exact RegularPointDimension.eq_of_regularAtDim
    (F.regularAtDim_of_mem hzreg.2.1 hzN) hzreg

/-- The actual global component witness and the actual support analyticity
produce the SAME closed irreducible geometric carrier internally. -/
def cartierPrimeComponent (D : EffectiveDivisor (m + 1) M)
    (B : GlobalComponents.globalComponents (n := m + 1) D.support) :
    ClosedIrreducibleAnalyticSubvariety (m + 1) M :=
  IrreducibleComponentFilling.componentSubvariety (cartierSupport_isComplexAnalytic D)
    (Classical.choose_spec (Classical.choose_spec B.property).1)

/-- The produced geometric prime has exactly the original component carrier. -/
theorem cartierPrimeComponent_carrier (D : EffectiveDivisor (m + 1) M)
    (B : GlobalComponents.globalComponents (n := m + 1) D.support) :
    (cartierPrimeComponent D B).carrier = (B : Set M) :=
  (Classical.choose_spec B.property).2.symm

/-- Actual hypersurface density and regularity comparison supply codimension
one for every SAME produced global component, without a dimension premise. -/
theorem cartierPrimeComponent_dim (D : EffectiveDivisor (m + 1) M)
    (B : GlobalComponents.globalComponents (n := m + 1) D.support) :
    (cartierPrimeComponent D B).dim = m :=
  cartierSupport_regular_dimension D (Classical.choose_spec (Classical.choose_spec B.property).1)

/-- Actual local finiteness holds for the SAME internally constructed
geometric prime carrier family; neither compactness nor a finite catalog is assumed. -/
theorem locallyFinite_cartierPrimeComponents (D : EffectiveDivisor (m + 1) M) :
    LocallyFinite (fun B : GlobalComponents.globalComponents (n := m + 1) D.support =>
      (cartierPrimeComponent D B).carrier) := by
  simpa only [cartierPrimeComponent_carrier] using
    GlobalComponents.locallyFinite_globalComponents (cartierSupport_isComplexAnalytic D)

end SGPT.PSH
