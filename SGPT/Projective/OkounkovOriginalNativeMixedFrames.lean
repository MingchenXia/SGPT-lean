import SGPT.Projective.OkounkovNativeMatchingFrames
import SGPT.GAGA.H0LSections
import SGPT.IGood.DXMainTensorMetric

/-! Actual ORIGINAL mixed sheaf powers/native tensor frames, before any section.
Blueprint: okounkov-original-native-mixed-frames.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.NativeFrames
open Set Filter Bundle CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle SGPT.LineBundle.TMetric
open SGPT.NAPotential.GAGAMult SGPT.GAGA.H0L

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
  {N A : X.Modules} (a : LineBundleAtlas N) (b : LineBundleAtlas A)
  (H : SchemeLineBundleMetric f n E N) (K : SchemeLineBundleMetric f n E A)

local instance originalMixedFramesTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance originalMixedFramesCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance originalMixedFramesManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The LITERAL original power/tensor sheaf, with true restrictions BEFORE original powers. -/
def originalMixedPowerAtlas (m k : ℕ) :
    LineBundleAtlas (bundleTensor (bundleTensorPower N m) (bundleTensorPower A k)) where
  I := a.I × b.I
  opens ij := a.opens ij.1 ⊓ b.opens ij.2
  covers x := by
    obtain ⟨i,hi⟩ := a.covers x
    obtain ⟨j,hj⟩ := b.covers x
    exact ⟨(i,j),hi,hj⟩
  frame ij := ((leftRestrictedFrame a b ij).tensorPower m).tensor
    ((rightRestrictedFrame a b ij).tensorPower k)

/-- The SAME original native frames and genuine literal native tensor powers. -/
def originalMixedNativeFrame (m k : ℕ) (ij : a.I × b.I) :
    AtlasFrame (twistedPower (schemeHermitianLineBundle f n E a H)
      (positivePower (schemeHermitianLineBundle f n E b K) (k-1)) m) :=
  twistedPowerAtlasFrame (schemeHermitianAtlasFrame f n E a H (leftRestrictedFrame a b ij))
    (positivePowerAtlasFrame (schemeHermitianAtlasFrame f n E b K (rightRestrictedFrame a b ij)) (k-1)) m

private theorem positiveFrame_baseSet {D : HermitianHolomorphicLineBundle.{0,0} n (SchemeComplexPoint f)}
    (e : AtlasFrame D) (k : ℕ) : (positivePowerAtlasFrame e k).val.baseSet = e.val.baseSet := by
  induction k with
  | zero => rfl
  | succ k ih => change (positivePowerAtlasFrame e k).val.baseSet ∩ e.val.baseSet = _; rw [ih, inter_self]

private theorem mixedFrame_baseSet (m k : ℕ) (ij : a.I × b.I) :
    (originalMixedNativeFrame f n E a b H K m k ij).val.baseSet =
      schemeComplexPointImage f ⁻¹' (a.opens ij.1 ⊓ b.opens ij.2) := by
  cases m with
  | zero =>
    change Set.univ ∩ (positivePowerAtlasFrame _ (k-1)).val.baseSet = _
    rw [Set.univ_inter,positiveFrame_baseSet]
    rfl
  | succ m =>
    change (positivePowerAtlasFrame _ m).val.baseSet ∩ (positivePowerAtlasFrame _ (k-1)).val.baseSet = _
    rw [positiveFrame_baseSet,positiveFrame_baseSet]
    exact inter_self _

private theorem mixedFrame_cover (m k : ℕ) (p : SchemeComplexPoint f) :
    ∃ ij, p ∈ (originalMixedNativeFrame f n E a b H K m k ij).val.baseSet := by
  obtain ⟨i,hi⟩ := a.covers (schemeComplexPointImage f p)
  obtain ⟨j,hj⟩ := b.covers (schemeComplexPointImage f p)
  refine ⟨(i,j),?_⟩
  rw [mixedFrame_baseSet]
  exact ⟨hi,hj⟩

private theorem mixedFrame_transition (m k : ℕ) (hk : 0<k)
    (F : SchemeLineBundleMetric f n E (bundleTensor (bundleTensorPower N m) (bundleTensorPower A k)))
    (i j : a.I × b.I) (p : SchemeComplexPoint f)
    (hi : p ∈ (originalMixedNativeFrame f n E a b H K m k i).val.baseSet)
    (hj : p ∈ (originalMixedNativeFrame f n E a b H K m k j).val.baseSet) :
    ((originalMixedNativeFrame f n E a b H K m k i).val.coordChangeL ℂ
      (originalMixedNativeFrame f n E a b H K m k j).val p) 1 =
    ((schemeHermitianAtlasFrame f n E (originalMixedPowerAtlas a b m k) F
        ((originalMixedPowerAtlas a b m k).frame i)).val.coordChangeL ℂ
      (schemeHermitianAtlasFrame f n E (originalMixedPowerAtlas a b m k) F
        ((originalMixedPowerAtlas a b m k).frame j)).val p) 1 := by
  have hi' : schemeComplexPointImage f p ∈ a.opens i.1 ⊓ b.opens i.2 :=
    by
      rw [mixedFrame_baseSet] at hi
      exact ⟨hi.1,hi.2⟩
  have hj' : schemeComplexPointImage f p ∈ a.opens j.1 ⊓ b.opens j.2 :=
    by
      rw [mixedFrame_baseSet] at hj
      exact ⟨hj.1,hj.2⟩
  let ei := schemeHermitianAtlasFrame f n E a H (leftRestrictedFrame a b i)
  let ej := schemeHermitianAtlasFrame f n E a H (leftRestrictedFrame a b j)
  let gi := schemeHermitianAtlasFrame f n E b K (rightRestrictedFrame a b i)
  let gj := schemeHermitianAtlasFrame f n E b K (rightRestrictedFrame a b j)
  rw [coordChangeL_schemeHermitianAtlasFrame' (originalMixedPowerAtlas a b m k) F _ _ hi' hj']
  change ((twistedPowerAtlasFrame ei (positivePowerAtlasFrame gi (k-1)) m).val.coordChangeL ℂ
    (twistedPowerAtlasFrame ej (positivePowerAtlasFrame gj (k-1)) m).val p) 1 = _
  rw [twistedPower_frame_transition ei ej _ _ hi' hj'
      (positivePowerAtlasFrame_mem gi hi' _) (positivePowerAtlasFrame_mem gj hj' _) m,
    positivePower_frame_transition gi gj hi' hj' (k-1),
    coordChangeL_schemeHermitianAtlasFrame' a H _ _ hi' hj',
    coordChangeL_schemeHermitianAtlasFrame' b K _ _ hi' hj',Nat.sub_add_cancel hk]
  change _ = schemeFrameTransition f n E
    (((leftRestrictedFrame a b i).tensorPower m).tensor ((rightRestrictedFrame a b i).tensorPower k))
    (((leftRestrictedFrame a b j).tensorPower m).tensor ((rightRestrictedFrame a b j).tensorPower k)) p
  rw [SGPT.IGood.DXMain.schemeFrameTransition_tensor f n E _ _ _ _ p hi' hj',
    schemeFrameTransition_tensorPower f n E _ _ m p hi' hj',
    schemeFrameTransition_tensorPower f n E _ _ k p hi' hj']

/-- Genuine ORIGINAL mixed-native/sheaf fiber equivalence, with no comparison certificate input. -/
def originalMixedNativeEquiv (m k : ℕ) (hk : 0<k)
    (F : SchemeLineBundleMetric f n E (bundleTensor (bundleTensorPower N m) (bundleTensorPower A k))) :
    FrameIdentityEquiv
      (twistedPower (schemeHermitianLineBundle f n E a H)
        (positivePower (schemeHermitianLineBundle f n E b K) (k-1)) m).Fiber
      (schemeHermitianLineBundle f n E (originalMixedPowerAtlas a b m k) F).Fiber :=
  matchingNativeFrameEquiv (originalMixedNativeFrame f n E a b H K m k)
    (fun ij => schemeHermitianAtlasFrame f n E (originalMixedPowerAtlas a b m k) F
      ((originalMixedPowerAtlas a b m k).frame ij))
    (fun ij => mixedFrame_baseSet f n E a b H K m k ij)
    (mixedFrame_cover f n E a b H K m k)
    (mixedFrame_transition f n E a b H K m k hk F)

/-- EVERY original restricted power/tensor frame reads precisely the SAME original physical scalar. -/
theorem originalMixedNativeEquiv_frame (m k : ℕ) (hk : 0<k)
    (F : SchemeLineBundleMetric f n E (bundleTensor (bundleTensorPower N m) (bundleTensorPower A k)))
    (ij : a.I × b.I) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ a.opens ij.1 ⊓ b.opens ij.2)
    (w : (twistedPower (schemeHermitianLineBundle f n E a H)
      (positivePower (schemeHermitianLineBundle f n E b K) (k-1)) m).Fiber p) :
    ((schemeHermitianAtlasFrame f n E (originalMixedPowerAtlas a b m k) F
      ((originalMixedPowerAtlas a b m k).frame ij)).val
      ⟨p,(originalMixedNativeEquiv f n E a b H K m k hk F).equiv p w⟩).2 =
        ((originalMixedNativeFrame f n E a b H K m k ij).val ⟨p,w⟩).2 :=
  matchingNativeFrameEquiv_frame (originalMixedNativeFrame f n E a b H K m k)
    (fun ij => schemeHermitianAtlasFrame f n E (originalMixedPowerAtlas a b m k) F
      ((originalMixedPowerAtlas a b m k).frame ij))
    (fun ij => mixedFrame_baseSet f n E a b H K m k ij)
    (mixedFrame_cover f n E a b H K m k)
    (mixedFrame_transition f n E a b H K m k hk F) ij
    (by rw [mixedFrame_baseSet]; exact hp) w

end SGPT.Okounkov.NativeFrames
