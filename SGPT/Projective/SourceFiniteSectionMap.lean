import SGPT.Bergman.SourceTensorDictionary
import SGPT.Projective.Maps

/-! A finite actual native globally generating section family constructs
a genuine holomorphic map into the actual original complex projective space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Bergman.AnalyticSectionProducts
open Bundle Set Filter
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Manifold
variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private def familyFrameLift
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber) (e : AtlasFrame E)
    (x : X) : Fin (N+1) → ℂ := fun j => (e.val ⟨x,s j x⟩).2

private theorem familyFrameLift_ne_zero
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (hGen : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0)
    (e : AtlasFrame E) (x : X) (hx : x ∈ e.val.baseSet) :
    familyFrameLift E s e x ≠ 0 := by
  intro h
  obtain ⟨j,hj⟩ := hGen x
  have hz := congrFun h j
  change e.val.linearEquivAt ℂ x hx (s j x) = 0 at hz
  apply hj
  apply (e.val.linearEquivAt ℂ x hx).injective
  rw [hz,map_zero]

/-- The actual projective point represented by genuine original native
section coefficients in a preferred original frame. The next theorem
removes the frame choice. Explicit genuine global generation is a premise
of this supporting constructor; the strict geometry producer must supply it. -/
def sourceNativeFiniteSectionProjectiveMap
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (hGen : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0) :
    X → SGPT.Projective.ComplexProjectiveSpace N := fun x =>
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x,inferInstance⟩
  SGPT.Projective.ComplexProjectiveSpace.mk (familyFrameLift E s e x)
    (familyFrameLift_ne_zero E s hGen e x (mem_baseSet_trivializationAt ℂ E.Fiber x))

/-- The actual native section projective map has the literal expected
homogeneous coefficients in EVERY original line frame. The preferred
frame choice is removed by genuine linear fiber algebra, not a supplied
projectivization or frame-transition certificate. -/
theorem sourceNativeFiniteSectionProjectiveMap_frame
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (hGen : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0)
    (e : AtlasFrame E) (x : X) (hx : x ∈ e.val.baseSet) :
    sourceNativeFiniteSectionProjectiveMap E s hGen x =
      SGPT.Projective.ComplexProjectiveSpace.mk (fun j => (e.val ⟨x,s j x⟩).2)
        (familyFrameLift_ne_zero E s hGen e x hx) := by
  let f : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x,inferInstance⟩
  have hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
  let a := f.val.linearEquivAt ℂ x hf
  let b := e.val.linearEquivAt ℂ x hx
  have hu (v : E.Fiber x) : v = a v • a.symm 1 := by
    apply a.injective
    rw [map_smul,LinearEquiv.apply_symm_apply,smul_eq_mul,mul_one]
  have hCoeff (j : Fin (N+1)) : b (s j x) = a (s j x) * b (a.symm 1) := by
    calc
      _ = b (a (s j x) • a.symm 1) := congrArg b (hu (s j x))
      _ = _ := by rw [map_smul,smul_eq_mul]
  change SGPT.Projective.ComplexProjectiveSpace.mk (familyFrameLift E s f x) _ = _
  symm
  apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff
    (familyFrameLift_ne_zero E s hGen e x hx) (familyFrameLift_ne_zero E s hGen f x hf)).mpr
  refine ⟨b (a.symm 1),?_⟩
  ext j
  change b (a.symm 1) * a (s j x) = b (s j x)
  rw [hCoeff j]
  exact mul_comm _ _

/-- The actual native finite-section projective map is genuinely
holomorphic as a map between the original complex manifold structures.
Native section coefficient lifts, nonvanishing and their projectivized
readback are proved locally in actual original atlas frames. -/
theorem sourceNativeFiniteSectionProjectiveMap_contMDiff
    (E : HermitianHolomorphicLineBundle.{0,0} n X)
    (s : Fin (N+1) → HolomorphicSections (n := n) E.Fiber)
    (hGen : ∀ x : X, ∃ j : Fin (N+1), s j x ≠ 0) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel N) ∞
      (sourceNativeFiniteSectionProjectiveMap E s hGen) := by
  intro x
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x,inferInstance⟩
  let := e.property
  have hx : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ E.Fiber x
  let F : X → Fin (N+1) → ℂ := fun y => familyFrameLift E s e y
  have hF : ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,Fin (N+1) → ℂ) ∞ F x := by
    apply contMDiffAt_pi_space.mpr
    intro j
    exact (e.val.contMDiffAt_section_iff hx).mp ((s j).contMDiff x)
  have hF0 : F x ≠ 0 := familyFrameLift_ne_zero E s hGen e x hx
  apply SGPT.Projective.ComplexProjectiveSpace.contMDiffAt_of_lift hF hF0
  filter_upwards [e.val.open_baseSet.mem_nhds hx] with y hy
  exact ⟨familyFrameLift_ne_zero E s hGen e y hy,
    sourceNativeFiniteSectionProjectiveMap_frame E s hGen e y hy⟩

end SGPT.Bergman.AnalyticSectionProducts
