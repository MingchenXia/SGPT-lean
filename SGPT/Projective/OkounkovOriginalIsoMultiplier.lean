import SGPT.Projective.OkounkovOriginalTensorMultiplier
import SGPT.Foundations.Schemes.NativeTensorPowerIsoFrames

/-! Genuine original sheaf-isomorphism transport of SAME multiplier coefficients, valuations and raw carriers.
Blueprint: okounkov-original-iso-multiplier.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalIsoMultiplier
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.OriginalAmpleUnits
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [IsSeparated f] [QuasiCompact f]
local instance isoMultiplierTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance isoMultiplierCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance isoMultiplierManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

omit [IsIntegral X] in
private theorem powerCoefficients_iso {L M : X.Modules} (e : L ≅ M) {U : X.Opens}
    (β : LocalBundleFrame M U) (k : ℕ) (s : bundlePowerGlobalSections L k) :
    (β.tensorPower k).coefficients (𝟙 U)
      ((bundleTensorPower M k).val.map U.leTop.op ((nativeLineTensorPowerIso e k).hom.val.app (.op ⊤) s))=
    ((transportFrame e β).tensorPower k).coefficients (𝟙 U)
      ((bundleTensorPower L k).val.map U.leTop.op s) := by
  have hmap : (bundleTensorPower M k).val.map U.leTop.op
      ((nativeLineTensorPowerIso e k).hom.val.app (.op ⊤) s)=
    (nativeLineTensorPowerIso e k).hom.val.app (.op U) ((bundleTensorPower L k).val.map U.leTop.op s) :=
    (PresheafOfModules.naturality_apply (nativeLineTensorPowerIso e k).hom.val U.leTop.op s).symm
  exact (congrArg ((β.tensorPower k).coefficients (𝟙 U)) hmap).trans
    (nativeTensorPowerIso_frame_coefficients e (transportFrame e β) β (fun _ _ _ => rfl) k (𝟙 U) _)

omit [IsIntegral X] [IsSeparated f] [QuasiCompact f] in
/-- The literal original power-isomorphism preserves EVERY actual original physical coefficient function. -/
theorem sectionFrameCoefficient_iso {L M : X.Modules} (e : L ≅ M) {U : X.Opens}
    (β : LocalBundleFrame M U) (k : ℕ) (s : bundlePowerGlobalSections L k) :
    sectionFrameCoefficient f n E β k ((nativeLineTensorPowerIso e k).hom.val.app (.op ⊤) s)=
      sectionFrameCoefficient f n E (transportFrame e β) k s :=
  congrArg (schemeOpenRegularFunction f n E U) (powerCoefficients_iso e β k s)

omit [IsIntegral X] [IsSeparated f] [QuasiCompact f] in
/-- ANY actual ideal membership survives the SAME original sheaf-isomorphism, with EVERY target frame retained. -/
theorem isIdealSection_iso {L M : X.Modules} (e : L ≅ M)
    {𝔞 : GermIdeal n (SchemeComplexPoint f)} {k : ℕ} {s : bundlePowerGlobalSections L k}
    (hs : IsIdealSection f n E 𝔞 k s) :
    IsIdealSection f n E 𝔞 k ((nativeLineTensorPowerIso e k).hom.val.app (.op ⊤) s) := by
  intro U β p hp
  rw [sectionFrameCoefficient_iso f n E e β k s]
  exact hs U (transportFrame e β) p hp

/-- The SAME actual original power-section map preserves values in ANY source and target atlases. -/
theorem sectionValue_iso {L M : X.Modules} (e : L ≅ M) (a : LineBundleAtlas L) (b : LineBundleAtlas M)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (k : ℕ) (s : bundlePowerGlobalSections L k) :
    sectionValue v c b k ((nativeLineTensorPowerIso e k).hom.val.app (.op ⊤) s)=sectionValue v c a k s := by
  let U := b.opens (b.centerIndex c)
  let β := b.frame (b.centerIndex c)
  let α := transportFrame e β
  let : Nonempty U := ⟨⟨c,b.centerIndex_mem c⟩⟩
  have hff : globalSectionToFunctionField (β.tensorPower k)
      ((nativeLineTensorPowerIso e k).hom.val.app (.op ⊤) s)=
      globalSectionToFunctionField (α.tensorPower k) s :=
    congrArg (X.germToFunctionField U) (powerCoefficients_iso e β k s)
  exact (sectionValue_eq_frame hc b β (b.centerIndex_mem c) k _).trans
    ((congrArg v hff).trans (sectionValue_eq_frame hc a α (b.centerIndex_mem c) k s).symm)

omit [IsSeparated f] [QuasiCompact f] in
/-- Genuine original isomorphisms transport the ENTIRE literal raw multiplier carrier, SAME weight/value/degree. -/
theorem multiplierSectionSet_subset_iso {L M : X.Modules} (e : L ≅ M) (a : LineBundleAtlas L) (b : LineBundleAtlas M)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (φ : SchemeComplexPoint f → EReal) :
    AlgebraicValuation.multiplierSectionSet f n E v c a φ ⊆ AlgebraicValuation.multiplierSectionSet f n E v c b φ := by
  rintro z ⟨k,s,hs,hI,hz⟩
  let t := (nativeLineTensorPowerIso e k).hom.val.app (.op ⊤) s
  have hvalue : sectionValue v c b k t=sectionValue v c a k s := sectionValue_iso n e a b v hc k s
  have ht : t≠0 := by
    intro h0
    have htop := (sectionValue_eq_top_iff (v:=v) c b k t).mpr h0
    exact ((sectionValue_eq_top_iff (v:=v) c a k s).not.mpr hs) (hvalue.symm.trans htop)
  have hIt : IsMultiplierSection f n E φ k t := by
    rcases hI with hk | hI
    · exact Or.inl hk
    · exact Or.inr (isIdealSection_iso f n E e hI)
  have hvec : sectionVector v c b k t ht=sectionVector v c a k s hs := by
    rw [sectionValue_eq_vector c b k t ht,sectionValue_eq_vector c a k s hs] at hvalue
    exact toLex.injective (WithTop.coe_injective hvalue)
  refine ⟨k,t,ht,hIt,?_⟩
  rw [hvec]
  exact hz
end SGPT.Okounkov.OriginalIsoMultiplier
