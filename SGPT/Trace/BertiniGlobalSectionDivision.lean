import SGPT.Trace.BertiniLocalOriginalChartNormal
import SGPT.Trace.BertiniSectionMultiplication
import SGPT.Foundations.Analysis.Pending.LocalGiraudTransform

/-! Actual local and global native holomorphic division by ORIGINAL smooth member sections. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember n p (affinePoint i ζ))
  (E : HermitianHolomorphicLineBundle.{0,0} n X)
  (S : HolomorphicSections (n := n) (tensor E (nativeBertiniHyperplaneBundle p)).Fiber)
  (hS : ∀ x ∈ member p (affinePoint i ζ), S x = 0)

include hsm hS in
theorem exists_nativeBertini_local_section_division (x : X) :
    ∃ u : ∀ y, E.Fiber y,
      (∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℂ, ComplexModel n)
        ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞ (fun z => (⟨z,u z⟩ : TotalSpace ℂ E.Fiber)) y) ∧
      ∀ᶠ y in 𝓝 x, S y = u y ⊗ₜ[ℂ] nativeBertiniAffineSection p i ζ y := by
  classical
  let P := nativeBertiniHyperplaneBundle p
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x,inferInstance⟩
  let f : AtlasFrame P := ⟨trivializationAt ℂ P.Fiber x,inferInstance⟩
  let t := tensorAtlasFrame e f
  let := e.property
  let := f.property
  let := t.property
  let j := chartIndex (p x)
  let g := nativeBertiniLocalEquation p i ζ j
  let U : Set X := e.val.baseSet ∩ (f.val.baseSet ∩ p ⁻¹' (affineChart j).source)
  have hU : IsOpen U := e.val.open_baseSet.inter (f.val.open_baseSet.inter
    ((affineChart j).open_source.preimage p.contMDiff.continuous))
  have hxU : x ∈ U := ⟨mem_baseSet_trivializationAt ℂ _ _,mem_baseSet_trivializationAt ℂ _ _,mem_affineChart_chartIndex _⟩
  let cp : X → ℂ := fun y => (f.val ⟨y,nativeBertiniCoordinateSection p j y⟩).2
  let cs : X → ℂ := fun y => (t.val ⟨y,S y⟩).2
  let σ : X → ℂ := fun y => cs y / cp y
  have hcpne (y : X) (hy : y ∈ U) : cp y ≠ 0 := by
    intro hz
    apply nativeBertiniCoordinateSection_ne_zero p j y hy.2.2
    apply (f.val.linearEquivAt ℂ y hy.2.1).injective
    exact hz.trans (map_zero _).symm
  have hσ (y : X) (hy : y ∈ U) : HolomorphicAt n σ y := by
    have hcs := originalSectionCoefficient_holomorphicAt (n := n) (tensor E P).Fiber t S ⟨hy.1,hy.2.1⟩
    have hcp := originalSectionCoefficient_holomorphicAt (n := n) P.Fiber f (nativeBertiniCoordinateSection p j) hy.2.1
    have hcs' : HolomorphicAt n cs y := hcs
    have hcp' : HolomorphicAt n cp y := hcp
    simpa only [σ,div_eq_mul_inv] using hcs'.mul (RelativePrincipalizationSpan.holomorphicAt_inv hcp' (hcpne y hy))
  have hg (y : X) (hy : y ∈ U) : HolomorphicAt n g y :=
    nativeBertiniLocalEquation_holomorphicAt p i ζ j y hy.2.2
  have hmem (y : X) (hy : y ∈ U) (hgy : g y = 0) : y ∈ member p (affinePoint i ζ) := by
    apply (nativeBertiniAffineSection_zero_iff p i ζ y).mp
    rw [nativeBertiniAffineSection_eq_originalEquation_smul p i ζ j y hy.2.2]
    change g y • _ = 0
    rw [hgy,zero_smul]
  have hreg (y : X) (hy : y ∈ U) (hgy : g y = 0) :
      ∃ (a : ComplexChart n X) (v : ComplexModel n), y ∈ a.val.source ∧ chartDeriv a v g y ≠ 0 := by
    obtain ⟨m,hm⟩ := exists_nativeBertiniChartPartial_ne_zero p i ζ j (complexChartAt (n := n) y) y
      (mem_complexChartAt_source y) hy.2.2 (hmem y hy hgy) hsm
    exact ⟨complexChartAt (n := n) y,EuclideanSpace.single m 1,mem_complexChartAt_source y,hm⟩
  have hv : (vanishingIdeal (n := n) ({y | g y = 0} ∩ U)).mem x σ := by
    refine ⟨hσ x hxU,Eventually.of_forall fun y hy => ?_⟩
    change cs y / cp y = 0
    have hs := hS y (hmem y hy.2 hy.1)
    change (t.val.linearEquivAt ℂ y ⟨hy.2.1,hy.2.2.1⟩) (S y) / cp y = 0
    rw [hs,map_zero,zero_div]
  obtain ⟨_,k,b,a,hb,ha,heq⟩ :=
    (LocalGiraudTransform.vanishingIdeal_zeroSet_mem_iff hU hg hreg hxU σ).mp hv
  let h : X → ℂ := fun y => ∑ j, a j y
  have hh : HolomorphicAt n h x := HolomorphicAt.sum Finset.univ (fun j _ => ha j)
  have heqh : σ =ᶠ[𝓝 x] fun y => h y * g y := by
    filter_upwards [heq] with y hy
    rw [hy]
    simp only [hb,h,Finset.sum_mul]
  let u : ∀ y, E.Fiber y := fun y => if hy : y ∈ e.val.baseSet then
    (e.val.linearEquivAt ℂ y hy).symm (h y) else 0
  have hread (y : X) (hy : y ∈ e.val.baseSet) : (e.val ⟨y,u y⟩).2 = h y := by
    change (e.val.linearEquivAt ℂ y hy) (u y) = h y
    simp only [u,dif_pos hy,LinearEquiv.apply_symm_apply]
  refine ⟨u,?_,?_⟩
  · have hhn : ∀ᶠ y in 𝓝 x, HolomorphicAt n h y := eventually_eventually_nhds.mpr hh
    filter_upwards [hU.mem_nhds hxU,hhn] with y hy hhy
    apply (e.val.contMDiffAt_section_iff hy.1).mpr
    apply (contMDiffAt_of_eventually_mdifferentiableAt hhy).congr_of_eventuallyEq
    filter_upwards [e.val.open_baseSet.mem_nhds hy.1] with z hz
    exact hread z hz
  · filter_upwards [hU.mem_nhds hxU,heqh] with y hy hσy
    apply (t.val.linearEquivAt ℂ y ⟨hy.1,hy.2.1⟩).injective
    change cs y = tensorCoordinate E.Fiber P.Fiber e.val f.val y
      (u y ⊗ₜ[ℂ] nativeBertiniAffineSection p i ζ y)
    rw [tensorCoordinate_tmul,Trivialization.coe_linearMapAt_of_mem e.val hy.1,
      Trivialization.coe_linearMapAt_of_mem f.val hy.2.1]
    change cs y = (e.val ⟨y,u y⟩).2 * (f.val ⟨y,nativeBertiniAffineSection p i ζ y⟩).2
    have hr : (f.val ⟨y,nativeBertiniAffineSection p i ζ y⟩).2 = g y * cp y := by
      rw [nativeBertiniAffineSection_eq_originalEquation_smul p i ζ j y hy.2.2]
      change (f.val.linearEquivAt ℂ y hy.2.1) (g y • nativeBertiniCoordinateSection p j y) = _
      exact map_smul _ _ _
    rw [hread y hy.1,hr]
    have hcs : cs y = (h y * g y) * cp y := by
      rw [← hσy]
      exact (div_mul_cancel₀ (cs y) (hcpne y hy)).symm
    exact hcs.trans (mul_assoc _ _ _)

private theorem actualLocalQuotient_unique_at
    (hd : Dense {y | nativeBertiniAffineSection p i ζ y ≠ 0}) (x : X)
    (a b : ∀ y, E.Fiber y)
    (ha : ContMDiffAt 𝓘(ℂ, ComplexModel n) ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun y => (⟨y,a y⟩ : TotalSpace ℂ E.Fiber)) x)
    (hb : ContMDiffAt 𝓘(ℂ, ComplexModel n) ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun y => (⟨y,b y⟩ : TotalSpace ℂ E.Fiber)) x)
    (heq : ∀ᶠ y in 𝓝 x, a y ⊗ₜ[ℂ] nativeBertiniAffineSection p i ζ y =
      b y ⊗ₜ[ℂ] nativeBertiniAffineSection p i ζ y) : a x = b x := by
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x,inferInstance⟩
  let := e.property
  have hx : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hca : ContinuousAt (fun y => (e.val ⟨y,a y⟩).2) x :=
    ((e.val.contMDiffAt_section_iff hx).mp ha).continuousAt
  have hcb : ContinuousAt (fun y => (e.val ⟨y,b y⟩).2) x :=
    ((e.val.contMDiffAt_section_iff hx).mp hb).continuousAt
  have hf : ∃ᶠ y in 𝓝 x, nativeBertiniAffineSection p i ζ y ≠ 0 := mem_closure_iff_frequently.mp (hd x)
  have heqf : ∃ᶠ y in 𝓝 x, (e.val ⟨y,a y⟩).2 = (e.val ⟨y,b y⟩).2 := by
    apply (hf.and_eventually heq).mono
    intro y hy
    have ht : (a y - b y) ⊗ₜ[ℂ] nativeBertiniAffineSection p i ζ y = 0 := by
      rw [TensorProduct.sub_tmul,hy.2,sub_self]
    have hn : ‖a y - b y‖ * ‖nativeBertiniAffineSection p i ζ y‖ = 0 := by
      rw [← TensorProduct.norm_tmul (𝕜 := ℂ),ht,norm_zero]
    have hab : a y = b y := sub_eq_zero.mp (norm_eq_zero.mp
      ((mul_eq_zero.mp hn).resolve_right (norm_ne_zero_iff.mpr hy.1)))
    exact congrArg (fun v : E.Fiber y => (e.val ⟨y,v⟩).2) hab
  apply (e.val.linearEquivAt ℂ x hx).injective
  exact tendsto_nhds_unique_of_frequently_eq hca hcb heqf

include hsm hS in
theorem exists_nativeBertini_global_section_division [ConnectedSpace X]
    (hproper : ∃ x : X, x ∉ member p (affinePoint i ζ)) :
    ∃ u : HolomorphicSections (n := n) E.Fiber,
      nativeTensorSection E (nativeBertiniHyperplaneBundle p) u (nativeBertiniAffineSection p i ζ) = S := by
  classical
  let P := nativeBertiniHyperplaneBundle p
  let s := nativeBertiniAffineSection p i ζ
  have hs : s ≠ 0 := nativeBertiniAffineSection_ne_zero p i ζ hproper
  have hZ := sectionZeroSet_isComplexAnalytic P.Fiber s
  have hi := SGPT.Foundations.Analysis.Pending.PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ
    hZ (sectionZeroSet_ne_univ P.Fiber s hs)
  have hd : Dense {y | s y ≠ 0} := interior_eq_empty_iff_dense_compl.mp hi
  have hlocal (x : X) := exists_nativeBertini_local_section_division p i ζ hsm E S hS x
  let U (x : X) := (hlocal x).choose
  have hU (x : X) := (hlocal x).choose_spec
  let u : ∀ y, E.Fiber y := fun y => U y y
  have heq (x : X) : ∀ᶠ y in 𝓝 x, u y = U x y := by
    filter_upwards [(hU x).1,(hU x).2.eventually_nhds] with y hy hxy
    exact (actualLocalQuotient_unique_at p i ζ E hd y (U x) (U y) hy (hU y).1.self_of_nhds
      (by filter_upwards [hxy,(hU y).2] with z hxz hyz; exact hxz.symm.trans hyz)).symm
  let R : HolomorphicSections (n := n) E.Fiber := {
    toFun := u
    contMDiff_toFun := by
      intro x
      apply (hU x).1.self_of_nhds.congr_of_eventuallyEq
      filter_upwards [heq x] with y hy
      exact congrArg (fun v : E.Fiber y => (⟨y,v⟩ : TotalSpace ℂ E.Fiber)) hy }
  refine ⟨R,?_⟩
  apply ContMDiffSection.ext
  intro x
  exact (hU x).2.self_of_nhds.symm

end SGPT.Trace.Bertini
