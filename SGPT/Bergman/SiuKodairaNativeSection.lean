import SGPT.Bergman.SourceTensorDictionary
import SGPT.PSH.GlobalL2Correction
import SGPT.Projective.SourceFiniteSectionMap

/-!
# Actual native holomorphic section regularity

The local MDifferentiable definition is converted to a genuine complex
smooth section on the same original fibres.  No section model or metric
comparison is supplied as additional data.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:native-section`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.LineBundleMetric SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (E : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- The genuine globally holomorphic section map is complex smooth in the
original total-space manifold structure. -/
theorem contMDiff_of_isHolomorphicSectionOn_univ (s : (x : X) → E.Fiber x)
    (hs : IsHolomorphicSectionOn (n := n) E.Fiber s univ) :
    ContMDiff 𝓘(ℂ, ComplexModel n) (𝓘(ℂ, ComplexModel n).prod 𝓘(ℂ, ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (s x)) := by
  intro x
  let e := prefFrame E x
  let := e.property
  let c := complexChartAt (n := n) x
  have hx : x ∈ e.val.baseSet := mem_prefFrame E x
  have hxc : x ∈ c.val.source := mem_complexChartAt_source x
  have hd := differentiableOn_coord_of_holomorphicSectionOn e.val c isOpen_univ hs
  have hO : IsOpen (c.val.target ∩ c.val.symm ⁻¹' (univ ∩ e.val.baseSet)) :=
    c.val.isOpen_inter_preimage_symm (isOpen_univ.inter e.val.open_baseSet)
  have hctr : c.val x ∈ c.val.target ∩ c.val.symm ⁻¹' (univ ∩ e.val.baseSet) :=
    ⟨c.val.map_source hxc, by rw [mem_preimage, c.val.left_inv hxc]; exact ⟨mem_univ x, hx⟩⟩
  have hcd := contDiffAt_of_differentiableOn_complex hd hO hctr
  apply (e.val.contMDiffAt_section_iff hx).mpr
  have hcomp := hcd.contMDiffAt.comp x
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas c.property) hxc)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(c.val.open_source.inter e.val.open_baseSet).mem_nhds ⟨hxc, hx⟩] with y hy
  change (e.val (TotalSpace.mk' ℂ y (s y))).2 =
    e.val.continuousLinearMapAt ℂ (c.val.symm (c.val y)) (s (c.val.symm (c.val y)))
  rw [c.val.left_inv hy.1]
  exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hy.2 _).symm

/-- The exact original fibrewise function, bundled in the actual finite-H0
section module. -/
def nativeSectionOfHolomorphic (s : (x : X) → E.Fiber x)
    (hs : IsHolomorphicSectionOn (n := n) E.Fiber s univ) : HolomorphicSections (n := n) E.Fiber where
  toFun := s
  contMDiff_toFun := contMDiff_of_isHolomorphicSectionOn_univ E s hs

@[simp] theorem nativeSectionOfHolomorphic_apply (s : (x : X) → E.Fiber x)
    (hs : IsHolomorphicSectionOn (n := n) E.Fiber s univ) (x : X) :
    nativeSectionOfHolomorphic E s hs x = s x := rfl

end SGPT.Bergman.SiuKodaira
