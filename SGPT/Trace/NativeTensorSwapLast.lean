import SGPT.Trace.BertiniSectionMultiplication

/-! Actual native tensor permutation, holomorphy and original multiplier
membership. All original physical fibres and native tensor frames are used. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.NativeTensorSwap
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf

private theorem actualTensorFrame_tmul {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {E F : HermitianHolomorphicLineBundle n M} (e : AtlasFrame E) (f : AtlasFrame F)
    (x : M) (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet)
    (u : E.Fiber x) (v : F.Fiber x) :
    ((tensorAtlasFrame e f).val ⟨x, u ⊗ₜ[ℂ] v⟩).2 =
      (e.val ⟨x, u⟩).2 * (f.val ⟨x, v⟩).2 := by
  let := e.property
  let := f.property
  change tensorCoordinate _ _ e.val f.val x (u ⊗ₜ[ℂ] v) = _
  rw [tensorCoordinate_tmul, Trivialization.coe_linearMapAt_of_mem e.val he,
    Trivialization.coe_linearMapAt_of_mem f.val hf]

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (E F G : HermitianHolomorphicLineBundle n X)

def swapLastFiber (x : X) :
    (tensor (tensor E F) G).Fiber x ≃ₗ[ℂ] (tensor (tensor E G) F).Fiber x :=
  (TensorProduct.assoc ℂ (E.Fiber x) (F.Fiber x) (G.Fiber x)).trans
    ((TensorProduct.congr (LinearEquiv.refl ℂ (E.Fiber x))
      (TensorProduct.comm ℂ (F.Fiber x) (G.Fiber x))).trans
      (TensorProduct.assoc ℂ (E.Fiber x) (G.Fiber x) (F.Fiber x)).symm)

theorem swapLastFiber_tmul (x : X) (u : E.Fiber x) (v : F.Fiber x) (w : G.Fiber x) :
    swapLastFiber E F G x ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = (u ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] v := by
  rfl

theorem swapLastFrame_coefficient (e : AtlasFrame E) (f : AtlasFrame F) (g : AtlasFrame G)
    (x : X) (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet) (hg : x ∈ g.val.baseSet)
    (T : (tensor (tensor E F) G).Fiber x) :
    ((tensorAtlasFrame (tensorAtlasFrame e g) f).val ⟨x,swapLastFiber E F G x T⟩).2 =
      ((tensorAtlasFrame (tensorAtlasFrame e f) g).val ⟨x,T⟩).2 := by
  let q := tensorAtlasFrame (tensorAtlasFrame e f) g
  let r := tensorAtlasFrame (tensorAtlasFrame e g) f
  let := e.property
  let := f.property
  let := g.property
  let := q.property
  let := r.property
  have hq : x ∈ q.val.baseSet := ⟨⟨he,hf⟩,hg⟩
  have hr : x ∈ r.val.baseSet := ⟨⟨he,hg⟩,hf⟩
  let A := (r.val.linearEquivAt ℂ x hr).toLinearMap.comp (swapLastFiber E F G x).toLinearMap
  let B := (q.val.linearEquivAt ℂ x hq).toLinearMap
  have hAB : A = B := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro ef
    apply LinearMap.ext
    intro w
    change A (ef ⊗ₜ[ℂ] w) = B (ef ⊗ₜ[ℂ] w)
    induction ef using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
    | tmul u v =>
      change (r.val ⟨x,swapLastFiber E F G x ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w)⟩).2 =
        (q.val ⟨x,(u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w⟩).2
      rw [swapLastFiber_tmul,
        actualTensorFrame_tmul (tensorAtlasFrame e g) f x ⟨he,hg⟩ hf,
        actualTensorFrame_tmul (tensorAtlasFrame e f) g x ⟨he,hf⟩ hg,
        actualTensorFrame_tmul e g x he hg,
        actualTensorFrame_tmul e f x he hf]
      ring
    | add u v hu hv => rw [TensorProduct.add_tmul, map_add, map_add, hu, hv]
  exact LinearMap.congr_fun hAB T

def swapLastSection (S : HolomorphicSections (n := n) (tensor (tensor E F) G).Fiber) :
    HolomorphicSections (n := n) (tensor (tensor E G) F).Fiber := by
  refine { toFun := fun x => swapLastFiber E F G x (S x), contMDiff_toFun := ?_ }
  intro x
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x,inferInstance⟩
  let f : AtlasFrame F := ⟨trivializationAt ℂ F.Fiber x,inferInstance⟩
  let g : AtlasFrame G := ⟨trivializationAt ℂ G.Fiber x,inferInstance⟩
  let q := tensorAtlasFrame (tensorAtlasFrame e f) g
  let r := tensorAtlasFrame (tensorAtlasFrame e g) f
  let := e.property
  let := f.property
  let := g.property
  let := q.property
  let := r.property
  have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ x
  have hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ _ x
  have hg : x ∈ g.val.baseSet := mem_baseSet_trivializationAt ℂ _ x
  have hs := (q.val.contMDiffAt_section_iff (show x ∈ q.val.baseSet from ⟨⟨he,hf⟩,hg⟩)).mp
    (S.contMDiff x)
  apply (r.val.contMDiffAt_section_iff (show x ∈ r.val.baseSet from ⟨⟨he,hg⟩,hf⟩)).mpr
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.val.open_baseSet.mem_nhds he,f.val.open_baseSet.mem_nhds hf,
    g.val.open_baseSet.mem_nhds hg] with y hyE hyF hyG
  exact swapLastFrame_coefficient E F G e f g y hyE hyF hyG (S y)

theorem swapLastSection_apply (S : HolomorphicSections (n := n) (tensor (tensor E F) G).Fiber)
    (x : X) : swapLastSection E F G S x = swapLastFiber E F G x (S x) := rfl

theorem swapLastSection_mem_multiplier {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (S : nativeMultiplierSections (tensor (tensor E F) G) φ) :
    swapLastSection E F G S.val ∈ fullHolomorphicIdealSections (n := n)
      (tensor (tensor E G) F).Fiber (sourceDegreeMultiplierIdeal 1 φ) := by
  let I := sourceDegreeMultiplierIdeal (n := n) 1 φ
  have hI : I.IsCoherent := sourceDegreeMultiplierIdeal_isCoherent 1 hφ
  change globalSectionSheafEquiv (n := n) (tensor (tensor E G) F).Fiber
    (swapLastSection E F G S.val) ∈ idealOpenSectionSubmodule (n := n)
      (tensor (tensor E G) F).Fiber I ⊤
  intro q₀ x hx₀
  let e : AtlasFrame E := ⟨trivializationAt ℂ E.Fiber x.val,inferInstance⟩
  let f : AtlasFrame F := ⟨trivializationAt ℂ F.Fiber x.val,inferInstance⟩
  let g : AtlasFrame G := ⟨trivializationAt ℂ G.Fiber x.val,inferInstance⟩
  let q := tensorAtlasFrame (tensorAtlasFrame e f) g
  let r := tensorAtlasFrame (tensorAtlasFrame e g) f
  have he : x.val ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ x.val
  have hf : x.val ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ _ x.val
  have hg : x.val ∈ g.val.baseSet := mem_baseSet_trivializationAt ℂ _ x.val
  have hq : x.val ∈ q.val.baseSet := ⟨⟨he,hf⟩,hg⟩
  have hr : x.val ∈ r.val.baseSet := ⟨⟨he,hg⟩,hf⟩
  apply (localFrameCoefficientGerm_mem_iff (n := n) (tensor (tensor E G) F).Fiber I ⊤ q₀ r
    (globalSectionSheafEquiv (n := n) (tensor (tensor E G) F).Fiber (swapLastSection E F G S.val))
      x hx₀ hr).mpr
  apply (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n)
    (tensor (tensor E G) F).Fiber I hI r (swapLastSection E F G S.val) hr).mpr
  have hS := (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n)
    (tensor (tensor E F) G).Fiber I hI q S.val hq).mp (S.property q x hq)
  apply SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison.mem_multiplierIdeal_congr hS
  filter_upwards [e.val.open_baseSet.mem_nhds he,f.val.open_baseSet.mem_nhds hf,
    g.val.open_baseSet.mem_nhds hg] with y hyE hyF hyG
  exact (swapLastFrame_coefficient E F G e f g y hyE hyF hyG (S.val y)).symm

end SGPT.Trace.NativeTensorSwap
