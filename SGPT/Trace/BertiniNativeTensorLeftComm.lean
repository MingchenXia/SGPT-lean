import SGPT.Trace.BertiniMemberPullbackAdjunctionMultiplier
import SGPT.Trace.NativeTensorPullbackSectionRestriction

/-! Actual tensor first-factor interchange, genuine global/member-pullback
section holomorphy and SAME original full multiplier H0 preservation. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf
open SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

private theorem nativeTensorFrame_tmul {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    {E F : HermitianHolomorphicLineBundle n X} (e : AtlasFrame E) (f : AtlasFrame F)
    (x : X) (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet)
    (u : E.Fiber x) (v : F.Fiber x) :
    ((tensorAtlasFrame e f).val ⟨x,u ⊗ₜ[ℂ] v⟩).2 = (e.val ⟨x,u⟩).2 * (f.val ⟨x,v⟩).2 := by
  let := e.property
  let := f.property
  change tensorCoordinate _ _ e.val f.val x (u ⊗ₜ[ℂ] v) = _
  rw [tensorCoordinate_tmul,Trivialization.coe_linearMapAt_of_mem e.val he,
    Trivialization.coe_linearMapAt_of_mem f.val hf]

variable {n m : ℕ} {X Y : Type}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
  (E F G : HermitianHolomorphicLineBundle.{0,0} n X)

def nativeTensorLeftCommFiber (x : X) :
    (tensor E (tensor F G)).Fiber x ≃ₗ[ℂ] (tensor F (tensor E G)).Fiber x :=
  TensorProduct.leftComm ℂ (E.Fiber x) (F.Fiber x) (G.Fiber x)

theorem nativeTensorLeftCommFrame_coefficient (e : AtlasFrame E) (f : AtlasFrame F) (g : AtlasFrame G)
    (x : X) (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet) (hg : x ∈ g.val.baseSet)
    (T : (tensor E (tensor F G)).Fiber x) :
    ((tensorAtlasFrame f (tensorAtlasFrame e g)).val ⟨x,nativeTensorLeftCommFiber E F G x T⟩).2 =
      ((tensorAtlasFrame e (tensorAtlasFrame f g)).val ⟨x,T⟩).2 := by
  let q := tensorAtlasFrame e (tensorAtlasFrame f g)
  let r := tensorAtlasFrame f (tensorAtlasFrame e g)
  let := e.property
  let := f.property
  let := g.property
  let := q.property
  let := r.property
  have hq : x ∈ q.val.baseSet := ⟨he,hf,hg⟩
  have hr : x ∈ r.val.baseSet := ⟨hf,he,hg⟩
  let A := (r.val.linearEquivAt ℂ x hr).toLinearMap.comp (nativeTensorLeftCommFiber E F G x).toLinearMap
  let B := (q.val.linearEquivAt ℂ x hq).toLinearMap
  have hAB : A = B := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro fg
    change A (u ⊗ₜ[ℂ] fg) = B (u ⊗ₜ[ℂ] fg)
    induction fg using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero,map_zero,map_zero]
    | tmul v w =>
      change (r.val ⟨x,v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)⟩).2 = (q.val ⟨x,u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)⟩).2
      rw [nativeTensorFrame_tmul f (tensorAtlasFrame e g) x hf ⟨he,hg⟩,
        nativeTensorFrame_tmul e (tensorAtlasFrame f g) x he ⟨hf,hg⟩,
        nativeTensorFrame_tmul e g x he hg,nativeTensorFrame_tmul f g x hf hg]
      ring
    | add a b ha hb => rw [TensorProduct.tmul_add,map_add,map_add,ha,hb]
  exact LinearMap.congr_fun hAB T

theorem nativeTensorLeftCommFiber_roundtrip (x : X) (T : (tensor E (tensor F G)).Fiber x) :
    nativeTensorLeftCommFiber F E G x (nativeTensorLeftCommFiber E F G x T) = T := by
  let A := (nativeTensorLeftCommFiber F E G x).toLinearMap.comp (nativeTensorLeftCommFiber E F G x).toLinearMap
  have hA : A = LinearMap.id := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro fg
    change A (u ⊗ₜ[ℂ] fg) = u ⊗ₜ[ℂ] fg
    induction fg using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero,map_zero]
    | tmul v w => rfl
    | add a b ha hb => rw [TensorProduct.tmul_add,map_add,ha,hb]
  exact LinearMap.congr_fun hA T

def nativeTensorLeftCommSection
    (S : HolomorphicSections (n := n) (tensor E (tensor F G)).Fiber) :
    HolomorphicSections (n := n) (tensor F (tensor E G)).Fiber := by
  refine { toFun := fun x => nativeTensorLeftCommFiber E F G x (S x), contMDiff_toFun := ?_ }
  intro x
  let e : AtlasFrame E := ⟨trivializationAt ℂ _ x,inferInstance⟩
  let f : AtlasFrame F := ⟨trivializationAt ℂ _ x,inferInstance⟩
  let g : AtlasFrame G := ⟨trivializationAt ℂ _ x,inferInstance⟩
  let q := tensorAtlasFrame e (tensorAtlasFrame f g)
  let r := tensorAtlasFrame f (tensorAtlasFrame e g)
  let := q.property
  let := r.property
  have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hg : x ∈ g.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hs := (q.val.contMDiffAt_section_iff (show x ∈ q.val.baseSet from ⟨he,hf,hg⟩)).mp (S.contMDiff x)
  apply (r.val.contMDiffAt_section_iff (show x ∈ r.val.baseSet from ⟨hf,he,hg⟩)).mpr
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.val.open_baseSet.mem_nhds he,f.val.open_baseSet.mem_nhds hf,g.val.open_baseSet.mem_nhds hg]
    with y hyE hyF hyG
  exact nativeTensorLeftCommFrame_coefficient E F G e f g y hyE hyF hyG (S y)

def nativeTensorLeftCommPullbackSection
    (qmap : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    (S : HolomorphicSections (n := m) (nativeHolomorphicPullbackBundle (tensor E (tensor F G)) qmap).Fiber) :
    HolomorphicSections (n := m) (nativeHolomorphicPullbackBundle (tensor F (tensor E G)) qmap).Fiber := by
  refine { toFun := fun y => nativeTensorLeftCommFiber E F G (qmap y) (S y), contMDiff_toFun := ?_ }
  intro y
  let e : AtlasFrame E := ⟨trivializationAt ℂ _ (qmap y),inferInstance⟩
  let f : AtlasFrame F := ⟨trivializationAt ℂ _ (qmap y),inferInstance⟩
  let g : AtlasFrame G := ⟨trivializationAt ℂ _ (qmap y),inferInstance⟩
  let q := NativeTensorRestriction.pullbackFrame _ qmap (tensorAtlasFrame e (tensorAtlasFrame f g))
  let r := NativeTensorRestriction.pullbackFrame _ qmap (tensorAtlasFrame f (tensorAtlasFrame e g))
  let := q.property
  let := r.property
  have he : qmap y ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hf : qmap y ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hg : qmap y ∈ g.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hs := (q.val.contMDiffAt_section_iff (show y ∈ q.val.baseSet from ⟨he,hf,hg⟩)).mp (S.contMDiff y)
  apply (r.val.contMDiffAt_section_iff (show y ∈ r.val.baseSet from ⟨hf,he,hg⟩)).mpr
  apply hs.congr_of_eventuallyEq
  have hn := qmap.contMDiff.continuous.continuousAt.eventually
    ((e.val.open_baseSet.inter (f.val.open_baseSet.inter g.val.open_baseSet)).mem_nhds ⟨he,hf,hg⟩)
  filter_upwards [hn] with z hz
  exact nativeTensorLeftCommFrame_coefficient E F G e f g (qmap z) hz.1 hz.2.1 hz.2.2 (S z)

theorem nativeTensorLeftCommSection_mem_originalIdeal {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (S : HolomorphicSections (n := n) (tensor E (tensor F G)).Fiber)
    (hS : S ∈ fullHolomorphicIdealSections (n := n) (tensor E (tensor F G)).Fiber
      (sourceDegreeMultiplierIdeal 1 φ)) :
    nativeTensorLeftCommSection E F G S ∈ fullHolomorphicIdealSections (n := n)
      (tensor F (tensor E G)).Fiber (sourceDegreeMultiplierIdeal 1 φ) := by
  let B := tensor E (tensor F G)
  let D := tensor F (tensor E G)
  let R := nativeTensorLeftCommSection E F G S
  let I := sourceDegreeMultiplierIdeal (n := n) 1 φ
  have hIeq : I = multiplierIdeal (n := n) 1 φ := by
    simpa only [I,Nat.cast_one] using (sourceDegreeMultiplierIdeal_pos (n := n) 1 one_pos φ)
  have hI : I.IsCoherent := by rw [hIeq]; exact raw_qpsh_multiplier_isCoherent_allDimensions hφ one_pos
  change globalSectionSheafEquiv (n := n) D.Fiber R ∈ idealOpenSectionSubmodule (n := n) D.Fiber I ⊤
  intro t x htx
  let e : AtlasFrame E := ⟨trivializationAt ℂ _ x.val,inferInstance⟩
  let f : AtlasFrame F := ⟨trivializationAt ℂ _ x.val,inferInstance⟩
  let g : AtlasFrame G := ⟨trivializationAt ℂ _ x.val,inferInstance⟩
  let q := tensorAtlasFrame e (tensorAtlasFrame f g)
  let r := tensorAtlasFrame f (tensorAtlasFrame e g)
  have he : x.val ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hf : x.val ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hg : x.val ∈ g.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hq : x.val ∈ q.val.baseSet := ⟨he,hf,hg⟩
  have hr : x.val ∈ r.val.baseSet := ⟨hf,he,hg⟩
  apply (localFrameCoefficientGerm_mem_iff (n := n) D.Fiber I ⊤ t r
    (globalSectionSheafEquiv (n := n) D.Fiber R) x htx hr).mpr
  apply (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) D.Fiber I hI r R hr).mpr
  have hs := (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) B.Fiber I hI q S hq).mp (hS q x hq)
  rw [hIeq] at hs ⊢
  apply mem_multiplierIdeal_congr hs
  filter_upwards [e.val.open_baseSet.mem_nhds he,f.val.open_baseSet.mem_nhds hf,g.val.open_baseSet.mem_nhds hg]
    with y hyE hyF hyG
  exact (nativeTensorLeftCommFrame_coefficient E F G e f g y hyE hyF hyG (S y)).symm

theorem nativeTensorLeftCommPullbackSection_mem_originalIdeal
    (qmap : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) Y X ∞)
    {φ : Y → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := m) φ)
    (S : HolomorphicSections (n := m) (nativeHolomorphicPullbackBundle (tensor E (tensor F G)) qmap).Fiber)
    (hS : S ∈ fullHolomorphicIdealSections (n := m)
      (nativeHolomorphicPullbackBundle (tensor E (tensor F G)) qmap).Fiber (sourceDegreeMultiplierIdeal 1 φ)) :
    nativeTensorLeftCommPullbackSection E F G qmap S ∈ fullHolomorphicIdealSections (n := m)
      (nativeHolomorphicPullbackBundle (tensor F (tensor E G)) qmap).Fiber (sourceDegreeMultiplierIdeal 1 φ) := by
  let B := nativeHolomorphicPullbackBundle (tensor E (tensor F G)) qmap
  let D := nativeHolomorphicPullbackBundle (tensor F (tensor E G)) qmap
  let R := nativeTensorLeftCommPullbackSection E F G qmap S
  let I := sourceDegreeMultiplierIdeal (n := m) 1 φ
  have hIeq : I = multiplierIdeal (n := m) 1 φ := by
    simpa only [I,Nat.cast_one] using (sourceDegreeMultiplierIdeal_pos (n := m) 1 one_pos φ)
  have hI : I.IsCoherent := by rw [hIeq]; exact raw_qpsh_multiplier_isCoherent_allDimensions hφ one_pos
  change globalSectionSheafEquiv (n := m) D.Fiber R ∈ idealOpenSectionSubmodule (n := m) D.Fiber I ⊤
  intro t y hty
  let e : AtlasFrame E := ⟨trivializationAt ℂ _ (qmap y.val),inferInstance⟩
  let f : AtlasFrame F := ⟨trivializationAt ℂ _ (qmap y.val),inferInstance⟩
  let g : AtlasFrame G := ⟨trivializationAt ℂ _ (qmap y.val),inferInstance⟩
  let q := NativeTensorRestriction.pullbackFrame _ qmap (tensorAtlasFrame e (tensorAtlasFrame f g))
  let r := NativeTensorRestriction.pullbackFrame _ qmap (tensorAtlasFrame f (tensorAtlasFrame e g))
  have he : qmap y.val ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hf : qmap y.val ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hg : qmap y.val ∈ g.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hq : y.val ∈ q.val.baseSet := ⟨he,hf,hg⟩
  have hr : y.val ∈ r.val.baseSet := ⟨hf,he,hg⟩
  apply (localFrameCoefficientGerm_mem_iff (n := m) D.Fiber I ⊤ t r
    (globalSectionSheafEquiv (n := m) D.Fiber R) y hty hr).mpr
  apply (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := m) D.Fiber I hI r R hr).mpr
  have hs := (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := m) B.Fiber I hI q S hq).mp (hS q y hq)
  rw [hIeq] at hs ⊢
  apply mem_multiplierIdeal_congr hs
  have hn := qmap.contMDiff.continuous.continuousAt.eventually
    ((e.val.open_baseSet.inter (f.val.open_baseSet.inter g.val.open_baseSet)).mem_nhds ⟨he,hf,hg⟩)
  filter_upwards [hn] with z hz
  exact (nativeTensorLeftCommFrame_coefficient E F G e f g (qmap z) hz.1 hz.2.1 hz.2.2 (S z)).symm

end SGPT.Trace.Bertini
