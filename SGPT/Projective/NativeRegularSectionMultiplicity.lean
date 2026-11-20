import SGPT.Projective.NativeBertiniWholeMember
import SGPT.Trace.BertiniDefiningSectionCoordinates
import SGPT.Foundations.Analysis.Pending.DivisorRegularLocus

/-! Actual multiplicity-one presentations of the SAME original regular
native power section. Blueprint: `native-regular-section-multiplicity.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L : HermitianHolomorphicLineBundle.{0,0} n X)
  (s : Fin (N + 1) → HolomorphicSections (n := n) L.Fiber)
  (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N)

/-- Exact SAME physical coefficient: original hyperplane equation times
the original nonzero family-coordinate coefficient in any original frame. -/
theorem linearSection_coefficient_eq_memberEquation
    (e : AtlasFrame L) (j : Fin (N + 1)) (x : X)
    (he : x ∈ e.val.baseSet)
    (hx : sourceNativeFiniteSectionProjectiveMap L s hgen x ∈ (affineChart j).source) :
    sectionCoefficient L.Fiber e.val (linearSection L s l) x =
      memberEquation (sourceNativeFiniteSectionProjectiveMap L s hgen) l j x *
        sectionCoefficient L.Fiber e.val (s j) x := by
  classical
  let := e.property
  let ev : HolomorphicSections (n := n) L.Fiber →ₗ[ℂ] L.Fiber x := {
    toFun t := t x
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have heval : linearSection L s l x = ∑ i, l.rep i • s i x := by
    change ev (∑ i, l.rep i • s i) = _
    rw [map_sum]
    rfl
  have hphys := (nativeSectionFamily_affine_formula L s hgen j x hx).2 l.rep
  have hphys' : linearSection L s l x =
      memberEquation (sourceNativeFiniteSectionProjectiveMap L s hgen) l j x • s j x := by
    rw [heval]
    exact hphys
  change (e.val.linearEquivAt ℂ x he) (linearSection L s l x) = _
  rw [hphys', map_smul, smul_eq_mul]
  rfl

/-- Smoothness of the actual original member forces a nonzero derivative
of its SAME section coefficient in an actual original manifold chart. -/
theorem exists_chart_coefficient_derivative_ne_zero
    (hl : IsSmoothHypersurfaceMember n (sourceNativeFiniteSectionProjectiveMap L s hgen) l)
    (e : AtlasFrame L) (x : X) (he : x ∈ e.val.baseSet)
    (hx : x ∈ member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) :
    ∃ c : ComplexChart n X, x ∈ c.val.source ∧
      fderiv ℂ (sectionCoefficient L.Fiber e.val (linearSection L s l) ∘ c.val.symm)
        (c.val x) ≠ 0 := by
  let p := sourceNativeFiniteSectionProjectiveMap L s hgen
  have hp := sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen
  let j := chartIndex (p x)
  have hxj : p x ∈ (affineChart j).source := mem_affineChart_chartIndex (p x)
  obtain ⟨c, v, hxc, hne⟩ := hl x hx j hxj
  let a := memberEquation p l j
  let b := sectionCoefficient L.Fiber e.val (s j)
  let g := sectionCoefficient L.Fiber e.val (linearSection L s l)
  have ha : HolomorphicAt n a x := holomorphicAt_memberEquation p hp l j hxj
  have hb : HolomorphicAt n b x :=
    SGPT.BDivisor.NSKodaira.nativeSectionCoefficient_holomorphicAt L (s j) e he
  have had : DifferentiableAt ℂ (a ∘ c.val.symm) (c.val x) :=
    (DerivativeIdeal.eventually_differentiableAt_comp_symm c hxc ha).self_of_nhds
  have hbd : DifferentiableAt ℂ (b ∘ c.val.symm) (c.val x) :=
    (DerivativeIdeal.eventually_differentiableAt_comp_symm c hxc hb).self_of_nhds
  have ha0 : a x = 0 := (mem_member_iff_memberEquation p l j hxj).mp hx
  have hb0 : b x ≠ 0 := by
    let := e.property
    have hsj := (nativeSectionFamily_affine_formula L s hgen j x hxj).1
    intro hz
    apply hsj
    apply (e.val.linearEquivAt ℂ x he).injective
    exact hz.trans (map_zero _).symm
  have heq : (g ∘ c.val.symm) =ᶠ[𝓝 (c.val x)]
      (fun z => (a ∘ c.val.symm) z * (b ∘ c.val.symm) z) := by
    have hU : IsOpen (p ⁻¹' (affineChart j).source ∩ e.val.baseSet) :=
      ((affineChart j).open_source.preimage hp.continuous).inter e.val.open_baseSet
    have ht := c.val.continuousAt_symm (c.val.map_source hxc)
    have hmem : c.val.symm (c.val x) ∈ p ⁻¹' (affineChart j).source ∩ e.val.baseSet := by
      rw [c.val.left_inv hxc]
      exact ⟨hxj, he⟩
    filter_upwards [ht.preimage_mem_nhds (hU.mem_nhds hmem)] with z hz
    exact linearSection_coefficient_eq_memberEquation L s hgen l e j _ hz.2 hz.1
  have hprod := (had.hasFDerivAt.mul hbd.hasFDerivAt).congr_of_eventuallyEq heq
  refine ⟨c, hxc, ?_⟩
  intro hz
  have h := DFunLike.congr_fun hprod.fderiv v
  rw [hz] at h
  simp only [_root_.zero_apply, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul, Function.comp_apply,
    c.val.left_inv hxc, ha0, zero_mul, zero_add] at h
  have hh : fderiv ℂ (a ∘ c.val.symm) (c.val x) v ≠ 0 := hne
  exact (mul_ne_zero hb0 hh) h.symm

/-- Every zero of the actual regular native section produces an actual
original regular divisor presentation of multiplicity ONE in an original
manifold chart and ANY prescribed original bundle frame. -/
theorem exists_regularPresentation_linearSection
    (hl : IsSmoothHypersurfaceMember n (sourceNativeFiniteSectionProjectiveMap L s hgen) l)
    (e : AtlasFrame L) (x : X) (he : x ∈ e.val.baseSet)
    (hx : x ∈ member (sourceNativeFiniteSectionProjectiveMap L s hgen) l) :
    ∃ (c : ComplexChart n X) (_hxc : x ∈ c.val.source)
      (P : DivisorRegularLocus.RegularPresentation
        (sectionCoefficient L.Fiber e.val (linearSection L s l) ∘ c.val.symm) (c.val x)),
      P.m = 1 ∧ ∀ z ∈ P.U,
        (sectionCoefficient L.Fiber e.val (linearSection L s l) ∘ c.val.symm) z = 0 →
          DivisorRegularLocus.divisorMult
            (sectionCoefficient L.Fiber e.val (linearSection L s l) ∘ c.val.symm) z = 1 := by
  obtain ⟨c, hxc, hD⟩ := exists_chart_coefficient_derivative_ne_zero L s hgen l hl e x he hx
  let g := sectionCoefficient L.Fiber e.val (linearSection L s l) ∘ c.val.symm
  let U := c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet
  have hU : IsOpen U := c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hxU : c.val x ∈ U := by
    refine ⟨c.val.map_source hxc, ?_⟩
    change c.val.symm (c.val x) ∈ e.val.baseSet
    rwa [c.val.left_inv hxc]
  have hd : DifferentiableOn ℂ g U :=
    SGPT.Bergman.NativeHermitianMetric.sourceSectionCoefficient_chart_holomorphic
      L (linearSection L s l) c e
  have hDcont : ContinuousOn (fderiv ℂ g) U :=
    (contDiffOn_of_differentiableOn_complex hd hU).continuousOn_fderiv_of_isOpen hU (by simp)
  let V := U ∩ (fderiv ℂ g) ⁻¹' ({0} : Set (ComplexModel n →L[ℂ] ℂ))ᶜ
  have hV : IsOpen V := hDcont.isOpen_inter_preimage hU isOpen_compl_singleton
  have hxV : c.val x ∈ V := ⟨hxU, hD⟩
  have hg0 : g (c.val x) = 0 := by
    let := e.property
    change sectionCoefficient L.Fiber e.val (linearSection L s l) (c.val.symm (c.val x)) = 0
    rw [c.val.left_inv hxc]
    change (e.val.linearEquivAt ℂ x he) (linearSection L s l x) = 0
    rw [(linearSection_zero_iff L s hgen l x).mpr hx, map_zero]
  let P : DivisorRegularLocus.RegularPresentation g (c.val x) := {
    U := V
    isOpen := hV
    mem := hxV
    m := 1
    m_pos := one_pos
    h := g
    v := fun _ => 1
    h_diff := hd.mono inter_subset_left
    v_diff := differentiableOn_const _
    h_zero := hg0
    dh_ne := fun _ hy => hy.2
    v_ne := fun _ _ => one_ne_zero
    eq := fun _ _ => by simp }
  exact ⟨c, hxc, P, rfl, fun z hz hg => by
    simpa only [P] using P.divisorMult_of_mem hz hg⟩

end SGPT.Projective.NumEq.CompleteIntersections
