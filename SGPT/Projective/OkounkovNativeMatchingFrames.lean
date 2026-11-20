import SGPT.LineBundle.TMetricSections

/-! Genuine native fiber/frame descent, toward literal mixed original GAGA.
Blueprint: okounkov-native-matching-frames.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.NativeFrames
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle SGPT.LineBundle.TMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {B C : HermitianHolomorphicLineBundle.{0,0} n X} {I : Type}
  (e : I → AtlasFrame B) (g : I → AtlasFrame C)
  (hbase : ∀ i, (e i).val.baseSet = (g i).val.baseSet)
  (hcover : ∀ x : X, ∃ i, x ∈ (e i).val.baseSet)
  (htrans : ∀ i j (x : X), x ∈ (e i).val.baseSet → x ∈ (e j).val.baseSet →
    ((e i).val.coordChangeL ℂ (e j).val x) 1 =
      ((g i).val.coordChangeL ℂ (g j).val x) 1)

private def nativeFrameIndex (x : X) : I := Classical.choose (hcover x)
private theorem nativeFrameIndex_mem (x : X) :
    x ∈ (e (nativeFrameIndex e hcover x)).val.baseSet := Classical.choose_spec (hcover x)

private def matchingNativeFibreEquiv (x : X) : B.Fiber x ≃ₗ[ℂ] C.Fiber x :=
  ((e (nativeFrameIndex e hcover x)).val.linearEquivAt ℂ x
    (nativeFrameIndex_mem e hcover x)).trans
    ((g (nativeFrameIndex e hcover x)).val.linearEquivAt ℂ x
      (by rw [← hbase]; exact nativeFrameIndex_mem e hcover x)).symm

private theorem native_coordinate_transition {D : HermitianHolomorphicLineBundle.{0,0} n X}
    (a b : AtlasFrame D) {x : X} (ha : x ∈ a.val.baseSet) (hb : x ∈ b.val.baseSet)
    (z : ℂ) : (b.val ⟨x,a.val.symm x z⟩).2 = z * (a.val.coordChangeL ℂ b.val x) 1 := by
  rw [← Trivialization.coordChangeL_apply (R:=ℂ) a.val b.val ⟨ha,hb⟩]
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

include htrans in
private theorem matchingNativeFibreEquiv_frame (i : I) {x : X}
    (hx : x ∈ (e i).val.baseSet) (w : B.Fiber x) :
    ((g i).val ⟨x,matchingNativeFibreEquiv e g hbase hcover x w⟩).2 = ((e i).val ⟨x,w⟩).2 := by
  let j := nativeFrameIndex e hcover x
  have hj : x ∈ (e j).val.baseSet := nativeFrameIndex_mem e hcover x
  have hjg : x ∈ (g j).val.baseSet := by rw [← hbase]; exact hj
  have hig : x ∈ (g i).val.baseSet := by rw [← hbase]; exact hx
  change ((g i).val ⟨x,(g j).val.symm x (((e j).val ⟨x,w⟩).2)⟩).2 = _
  rw [native_coordinate_transition (g j) (g i) hjg hig, ← htrans j i x hj hx]
  calc
    _ = ((e i).val ⟨x,(e j).val.symm x (((e j).val ⟨x,w⟩).2)⟩).2 :=
      (native_coordinate_transition (e j) (e i) hj hx _).symm
    _ = _ := by rw [(e j).val.symm_apply_apply_mk hj w]

/-- Actual cover frames and their genuine scalar transition laws manufacture a true holomorphic isomorphism. -/
def matchingNativeFrameEquiv : FrameIdentityEquiv B.Fiber C.Fiber where
  equiv := matchingNativeFibreEquiv e g hbase hcover
  exists_frames x := by
    obtain ⟨i,hi⟩ := hcover x
    refine ⟨e i,g i,hi,(by rw [← hbase]; exact hi),?_⟩
    intro y hy w
    exact matchingNativeFibreEquiv_frame e g hbase hcover htrans i hy.1 w

/-- EVERY original cover-frame coordinate is literally preserved by the manufactured fiber isomorphism. -/
theorem matchingNativeFrameEquiv_frame (i : I) {x : X}
    (hx : x ∈ (e i).val.baseSet) (w : B.Fiber x) :
    ((g i).val ⟨x,(matchingNativeFrameEquiv e g hbase hcover htrans).equiv x w⟩).2 =
      ((e i).val ⟨x,w⟩).2 :=
  matchingNativeFibreEquiv_frame e g hbase hcover htrans i hx w

end SGPT.Okounkov.NativeFrames
