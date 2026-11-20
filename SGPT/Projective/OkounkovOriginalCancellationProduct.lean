import SGPT.Projective.OkounkovOriginalSectionUnits
import SGPT.Okounkov.ValGen2Dual
import Mathlib.Tactic.Group

/-! Actual original dual cancellation through genuine sheaf frame descent.
Blueprint: okounkov-original-cancellation-product.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalCancellation
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2
open SGPT.Okounkov.OriginalUnits

variable {X : Scheme.{0}} {L L' A : X.Modules}
  (a : LineBundleAtlas L) (b : LineBundleAtlas L') (d : LineBundleAtlas A)

private def cancellationCover (i : a.I × b.I × d.I) : X.Opens :=
  a.opens i.1 ⊓ (b.opens i.2.1 ⊓ d.opens i.2.2)

private theorem cancellationCover_covers (x : X) : ∃ i, x ∈ cancellationCover a b d i := by
  obtain ⟨i,hi⟩ := a.covers x
  obtain ⟨j,hj⟩ := b.covers x
  obtain ⟨l,hl⟩ := d.covers x
  exact ⟨(i,j,l),hi,hj,hl⟩

private def cancellationSourceFrame (i : a.I × b.I × d.I) : LocalBundleFrame L (cancellationCover a b d i) :=
  bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf) (homOfLE inf_le_left) (a.frame i.1)

private def cancellationTargetFrame (i : a.I × b.I × d.I) : LocalBundleFrame L' (cancellationCover a b d i) :=
  bundleHomRestrictionIso L' (SheafOfModules.unit X.ringCatSheaf)
    (homOfLE (inf_le_right.trans inf_le_left)) (b.frame i.2.1)

private def cancellationAmpleFrame (i : a.I × b.I × d.I) : LocalBundleFrame A (cancellationCover a b d i) :=
  bundleHomRestrictionIso A (SheafOfModules.unit X.ringCatSheaf)
    (homOfLE (inf_le_right.trans inf_le_right)) (d.frame i.2.2)

private def cancellationTwistFrame (m k : ℕ) (i : a.I × b.I × d.I) :
    LocalBundleFrame
      (bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k))
      (cancellationCover a b d i) :=
  (((cancellationTargetFrame a b d i).tensor (cancellationSourceFrame a b d i).dual).tensorPower m).tensor
    ((cancellationAmpleFrame a b d i).tensorPower k)

private def cancellationResultFrame (m k : ℕ) (i : a.I × b.I × d.I) :
    LocalBundleFrame (bundleTensor (bundleTensorPower A k) (bundleTensorPower L' m))
      (cancellationCover a b d i) :=
  ((cancellationAmpleFrame a b d i).tensorPower k).tensor ((cancellationTargetFrame a b d i).tensorPower m)

private theorem cancellation_transitions (m k : ℕ) :
    ∀ i j (W : X.Opens) (h : W ⟶ cancellationCover a b d i) (l : W ⟶ cancellationCover a b d j),
      localBundleFrameTransition
        (((cancellationSourceFrame a b d i).tensorPower m).tensor (cancellationTwistFrame a b d m k i))
        (((cancellationSourceFrame a b d j).tensorPower m).tensor (cancellationTwistFrame a b d m k j)) h l =
      localBundleFrameTransition (cancellationResultFrame a b d m k i) (cancellationResultFrame a b d m k j) h l := by
  intro i j W h l
  dsimp only [cancellationTwistFrame,cancellationResultFrame]
  simp only [localBundleFrameTransition_tensor,localBundleFrameTransition_tensorPower,
    localBundleFrameTransition_dual,mul_pow,inv_pow]
  let u := localBundleFrameTransition (cancellationSourceFrame a b d i) (cancellationSourceFrame a b d j) h l
  let v := localBundleFrameTransition (cancellationTargetFrame a b d i) (cancellationTargetFrame a b d j) h l
  let w := localBundleFrameTransition (cancellationAmpleFrame a b d i) (cancellationAmpleFrame a b d j) h l
  change u^m * (v^m * (u^m)⁻¹ * w^k) = w^k * v^m
  calc
    _ = (u^m * (u^m)⁻¹) * (w^k * v^m) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel,one_mul]

/-- ACTUAL original ordinary target section from SAME source sections and genuine dual/tensor cancellation. -/
def originalCancellationProduct (m k : ℕ) (s : bundlePowerGlobalSections L m)
    (t : Γ(bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k),⊤)) :
    Γ(bundleTensor (bundleTensorPower A k) (bundleTensorPower L' m),⊤) :=
  coverProduct (cancellationCover a b d) (cancellationCover_covers a b d)
    (fun i => (cancellationSourceFrame a b d i).tensorPower m)
    (cancellationTwistFrame a b d m k) (cancellationResultFrame a b d m k)
    (cancellation_transitions a b d m k) s t

variable [IsIntegral X] {n : ℕ}
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X}

/-- Literal original value product, for ANY actual original source/target atlases. -/
theorem originalCancellationProduct_value (hc : IsNonnegAt v c) (m k : ℕ)
    (q : LineBundleAtlas (bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k)))
    (r : LineBundleAtlas (bundleTensor (bundleTensorPower A k) (bundleTensorPower L' m)))
    (s : bundlePowerGlobalSections L m)
    (t : Γ(bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k),⊤)) :
    plainSectionValue v c r (originalCancellationProduct a b d m k s t) =
      sectionValue v c a m s + plainSectionValue v c q t := by
  have h := plainSectionValue_coverProduct (cancellationCover a b d) (cancellationCover_covers a b d)
    (fun i => (cancellationSourceFrame a b d i).tensorPower m)
    (cancellationTwistFrame a b d m k) (cancellationResultFrame a b d m k)
    (cancellation_transitions a b d m k) v hc (a.tensorPower m) q r s t
  rw [← sectionValue_eq_plainSectionValue (a:=a) (v:=v) hc m s] at h
  exact h

include b d in
/-- A genuine original support-avoiding factor produces an ACTUAL nonzero target section with EXACT source value. -/
theorem exists_original_value_preserving_cancellation (hc : IsNonnegAt v c) (m k : ℕ)
    (q : LineBundleAtlas (bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k)))
    (r : LineBundleAtlas (bundleTensor (bundleTensorPower A k) (bundleTensorPower L' m)))
    (t : Γ(bundleTensor (bundleTensorPower (bundleTensor L' (bundleDual L)) m) (bundleTensorPower A k),⊤))
    (ht : c ∉ (sectionZeroIdealSheaf q t).support) (s : bundlePowerGlobalSections L m) (hs : s ≠ 0) :
    ∃ τ : Γ(bundleTensor (bundleTensorPower A k) (bundleTensorPower L' m),⊤),
      τ ≠ 0 ∧ plainSectionValue v c r τ = sectionValue v c a m s := by
  have hz := plainSectionValue_eq_zero_of_not_mem_zeroSupport v q t c hc ht
  have hval := originalCancellationProduct_value a b d v hc m k q r s t
  rw [hz,add_zero] at hval
  refine ⟨originalCancellationProduct a b d m k s t,?_,hval⟩
  intro hzero
  have htop := (plainSectionValue_eq_top_iff (v:=v) c r _).mpr hzero
  exact ((sectionValue_eq_top_iff (v:=v) c a m s).not.mpr hs) (hval.symm.trans htop)

end SGPT.Okounkov.OriginalCancellation
