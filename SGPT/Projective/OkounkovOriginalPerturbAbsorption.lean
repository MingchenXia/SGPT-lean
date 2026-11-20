import SGPT.Projective.OkounkovOriginalIdealProducts

/-! Genuine original twist/residue absorption into actual positive perturbation powers; same multipliers/values.
Blueprint: okounkov-original-perturb-absorption-product.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalPerturbAbsorption
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
variable {X : Scheme.{0}} {L T A : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (aA : LineBundleAtlas A)

private def absorptionCover (i : a.I × aT.I × aA.I) : X.Opens :=
  a.opens i.1 ⊓ (aT.opens i.2.1 ⊓ aA.opens i.2.2)
private theorem absorptionCover_covers (x : X) : ∃ i, x∈absorptionCover a aT aA i := by
  obtain ⟨i,hi⟩ := a.covers x
  obtain ⟨j,hj⟩ := aT.covers x
  obtain ⟨k,hk⟩ := aA.covers x
  exact ⟨(i,j,k),hi,hj,hk⟩
private def absorptionLineFrame (i : a.I × aT.I × aA.I) : LocalBundleFrame L (absorptionCover a aT aA i) :=
  bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf) (homOfLE inf_le_left) (a.frame i.1)
private def absorptionTwistFrame (i : a.I × aT.I × aA.I) : LocalBundleFrame T (absorptionCover a aT aA i) :=
  bundleHomRestrictionIso T (SheafOfModules.unit X.ringCatSheaf)
    (homOfLE (inf_le_right.trans inf_le_left)) (aT.frame i.2.1)
private def absorptionAmpleFrame (i : a.I × aT.I × aA.I) : LocalBundleFrame A (absorptionCover a aT aA i) :=
  bundleHomRestrictionIso A (SheafOfModules.unit X.ringCatSheaf)
    (homOfLE (inf_le_right.trans inf_le_right)) (aA.frame i.2.2)
private def absorptionSourceFrame (q g r : ℕ) (i : a.I × aT.I × aA.I) :
    LocalBundleFrame (bundleTensor T (bundleTensorPower L (q*g+r))) (absorptionCover a aT aA i) :=
  (absorptionTwistFrame a aT aA i).tensor ((absorptionLineFrame a aT aA i).tensorPower (q*g+r))
private def absorptionFactorFrame (p g r : ℕ) (i : a.I × aT.I × aA.I) :
    LocalBundleFrame (bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g)))
      (absorptionCover a aT aA i) :=
  ((absorptionTwistFrame a aT aA i).tensor ((absorptionLineFrame a aT aA i).tensorPower r)).dual.tensor
    ((absorptionAmpleFrame a aT aA i).tensorPower (p*g))
private def absorptionTargetFrame (q p g : ℕ) (i : a.I × aT.I × aA.I) :
    LocalBundleFrame (bundleTensorPower (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) g)
      (absorptionCover a aT aA i) :=
  (((absorptionLineFrame a aT aA i).tensorPower q).tensor ((absorptionAmpleFrame a aT aA i).tensorPower p)).tensorPower g
private theorem absorption_transitions (q p g r : ℕ) :
    ∀ i j (W : X.Opens) (h : W ⟶ absorptionCover a aT aA i) (k : W ⟶ absorptionCover a aT aA j),
      localBundleFrameTransition ((absorptionSourceFrame a aT aA q g r i).tensor (absorptionFactorFrame a aT aA p g r i))
        ((absorptionSourceFrame a aT aA q g r j).tensor (absorptionFactorFrame a aT aA p g r j)) h k =
      localBundleFrameTransition (absorptionTargetFrame a aT aA q p g i) (absorptionTargetFrame a aT aA q p g j) h k := by
  intro i j W h k
  dsimp only [absorptionSourceFrame,absorptionFactorFrame,absorptionTargetFrame]
  simp only [localBundleFrameTransition_tensor,localBundleFrameTransition_tensorPower,
    localBundleFrameTransition_dual,pow_add,mul_pow,pow_mul,mul_inv]
  let u := localBundleFrameTransition (absorptionLineFrame a aT aA i) (absorptionLineFrame a aT aA j) h k
  let v := localBundleFrameTransition (absorptionTwistFrame a aT aA i) (absorptionTwistFrame a aT aA j) h k
  let w := localBundleFrameTransition (absorptionAmpleFrame a aT aA i) (absorptionAmpleFrame a aT aA j) h k
  change (v*((u^q)^g*u^r))*((v⁻¹*(u^r)⁻¹)*(w^p)^g)=(u^q)^g*(w^p)^g
  calc
    _ = (v*v⁻¹)*(u^r*(u^r)⁻¹)*((u^q)^g*(w^p)^g) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel,mul_inv_cancel,one_mul,one_mul]

/-- A GENUINE ordinary original target section, from literal source/factor and actual matching-frame descent. -/
def absorptionProduct (q p g r : ℕ) (s : Γ(bundleTensor T (bundleTensorPower L (q*g+r)),⊤))
    (t : Γ(bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g)),⊤)) :
    bundlePowerGlobalSections (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) g :=
  coverProduct (absorptionCover a aT aA) (absorptionCover_covers a aT aA)
    (absorptionSourceFrame a aT aA q g r) (absorptionFactorFrame a aT aA p g r)
    (absorptionTargetFrame a aT aA q p g) (absorption_transitions a aT aA q p g r) s t

section Value
variable [IsIntegral X] {n : ℕ}
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X}
/-- Exact SAME original value identity in ANY original source/factor/target atlases. -/
theorem absorptionProduct_value (hc : IsNonnegAt v c) (q p g r : ℕ)
    (bS : LineBundleAtlas (bundleTensor T (bundleTensorPower L (q*g+r))))
    (bF : LineBundleAtlas (bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g))))
    (bM : LineBundleAtlas (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)))
    (s : Γ(bundleTensor T (bundleTensorPower L (q*g+r)),⊤))
    (t : Γ(bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g)),⊤)) :
    sectionValue v c bM g (absorptionProduct a aT aA q p g r s t)=plainSectionValue v c bS s+plainSectionValue v c bF t := by
  exact (sectionValue_eq_plainSectionValue (a:=bM) (v:=v) hc g _).trans
    (plainSectionValue_coverProduct (absorptionCover a aT aA) (absorptionCover_covers a aT aA)
      (absorptionSourceFrame a aT aA q g r) (absorptionFactorFrame a aT aA p g r)
      (absorptionTargetFrame a aT aA q p g) (absorption_transitions a aT aA q p g r) v hc bS bF (bM.tensorPower g) s t)
end Value

section Ideal
variable [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (E : ClosedProjectiveEmbedding f) [IsSeparated f] [QuasiCompact f]
local instance perturbAbsorptionTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance perturbAbsorptionCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance perturbAbsorptionManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
omit [IsIntegral X] in
/-- SAME actual multiplier ideal membership survives in EVERY original target frame. -/
theorem absorptionProduct_isPlainMultiplierIdealSection (q p g r : ℕ) (φ : SchemeComplexPoint f → EReal) (ell : ℝ)
    (s : Γ(bundleTensor T (bundleTensorPower L (q*g+r)),⊤))
    (hs : IsPlainIdealSection f n E (multiplierIdeal (n:=n) ell φ) s)
    (t : Γ(bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g)),⊤)) :
    IsPlainIdealSection f n E (multiplierIdeal (n:=n) ell φ) (absorptionProduct a aT aA q p g r s t) := by
  exact OriginalIdealProducts.coverProduct_isPlainMultiplierIdealSection f n E
    (absorptionCover a aT aA) (absorptionCover_covers a aT aA)
    (absorptionSourceFrame a aT aA q g r) (absorptionFactorFrame a aT aA p g r)
    (absorptionTargetFrame a aT aA q p g) (absorption_transitions a aT aA q p g r) φ ell s hs t

include a aT aA in
/-- Actual support-unit factor produces a nonzero ordinary target with SAME value and multiplier condition. -/
theorem exists_unit_absorptionSection
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (q p g r : ℕ) (bS : LineBundleAtlas (bundleTensor T (bundleTensorPower L (q*g+r))))
    (bF : LineBundleAtlas (bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g))))
    (bM : LineBundleAtlas (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)))
    (φ : SchemeComplexPoint f → EReal) (ell : ℝ)
    (s : Γ(bundleTensor T (bundleTensorPower L (q*g+r)),⊤)) (hs : s≠0)
    (hI : IsPlainIdealSection f n E (multiplierIdeal (n:=n) ell φ) s)
    (t : Γ(bundleTensor (bundleDual (bundleTensor T (bundleTensorPower L r))) (bundleTensorPower A (p*g)),⊤))
    (ht : c∉(sectionZeroIdealSheaf bF t).support) :
    ∃ τ : bundlePowerGlobalSections (bundleTensor (bundleTensorPower L q) (bundleTensorPower A p)) g,
      τ≠0 ∧ sectionValue v c bM g τ=plainSectionValue v c bS s ∧
      IsPlainIdealSection f n E (multiplierIdeal (n:=n) ell φ) τ := by
  have hz := OriginalUnits.plainSectionValue_eq_zero_of_not_mem_zeroSupport v bF t c hc ht
  have hvalue := absorptionProduct_value a aT aA v hc q p g r bS bF bM s t
  rw [hz,add_zero] at hvalue
  refine ⟨absorptionProduct a aT aA q p g r s t,?_,hvalue,
    absorptionProduct_isPlainMultiplierIdealSection a aT aA f n E q p g r φ ell s hI t⟩
  intro hzero
  have htop := (sectionValue_eq_top_iff (v:=v) c bM g _).mpr hzero
  exact ((plainSectionValue_eq_top_iff (v:=v) c bS s).not.mpr hs) (hvalue.symm.trans htop)
end Ideal
end SGPT.Okounkov.OriginalPerturbAbsorption
