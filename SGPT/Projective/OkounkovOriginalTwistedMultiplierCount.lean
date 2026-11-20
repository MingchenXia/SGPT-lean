import SGPT.Projective.OkounkovOriginalFieldLeaves
import SGPT.Projective.OkounkovOriginalLeftUnitMultiplier
import SGPT.IGood.DXMainTwisted

/-! Actual original twisted multiplier value cardinality for arbitrary original full-rank valuations.
Blueprint: okounkov-original-twisted-multiplier-count.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalTwistedMultiplierCount
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.LineBundle SGPT.Okounkov.ValGen SGPT.Okounkov.AlgebraicValuation
open SGPT.Projective.NumEq.AlgebraicCurveDegree SGPT.Okounkov.OriginalLeftUnitMultiplier
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f] [Nonempty (SchemeComplexPoint f)]
local instance twistedCountTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance twistedCountCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance twistedCountManifold : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)
variable {L : X.Modules} (a : LineBundleAtlas L) (hbig : SGPT.LineBundle.IsBig f L (m+1))
  (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v) (c : X)
include a hbig hv

/-- SAME finite original twisted multiplier value set and independent original H0 dimension, all degrees/atlases. -/
theorem twistedMultiplierValues_finite_card {T : X.Modules} (k : ℕ)
    (r : LineBundleAtlas (bundleTensor T (bundleTensorPower L k)))
    {φ : SchemeComplexPoint f → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n:=m+1) φ) :
    (AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k r φ).Finite ∧
    Nat.card (AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k r φ) =
      SGPT.IGood.DXMain.twistedMultiplierH0 f (m+1) E hφ T L k := by
  classical
  let := schemeFunctionFieldAlgebra f
  let M := bundleTensor T (bundleTensorPower L k)
  have : FiniteDimensional ℂ (SectionSpace f M 1) := SectionSpace.finiteDimensional f E r 1
  let W := SGPT.IGood.DXMain.twistedMultiplierSubmodule f (m+1) E hφ T L k
  let F : SectionSpace f M 1 →ₗ[ℂ] X.functionField :=
    globalSectionToFunctionFieldOverBase f ((r.frame (r.centerIndex c)).tensorPower 1)
  let ι : W →ₗ[ℂ] X.functionField := F.comp W.subtype
  have hF : Function.Injective F := globalSectionToFunctionFieldOverBase_injective f (r.tensorPower 1) _
  have hι : Function.Injective ι := hF.comp Subtype.val_injective
  let j : (Fin (m+1) → ℤ) → WithTop (Lex (Fin (m+1) → ℤ)) := fun x =>
    ((toLex x : Lex (Fin (m+1) → ℤ)) : WithTop (Lex (Fin (m+1) → ℤ)))
  have hj : Function.Injective j := fun _ _ h => toLex.injective (WithTop.coe_injective h)
  have hread (s : SectionSpace f M 1) :
      v (F s) = plainSectionValue v c r ((bundleTensorLeftUnitIso M).hom.val.app (.op ⊤) s) :=
    congrArg v (originalLeftUnitHom_genericCoefficient s (r.frame (r.centerIndex c))).symm
  have himage : j '' AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k r φ = valueSet v ι := by
    ext w
    constructor
    · rintro ⟨x,⟨τ,hτ,hτI,rfl⟩,rfl⟩
      let s : SectionSpace f M 1 := originalSectionUnit τ
      have hs : s≠0 := (originalSectionUnit_ne_zero_iff (L:=M) τ).mpr hτ
      have hsI : s∈W := by
        change k=0 ∨ IsIdealSection f (m+1) E (multiplierIdeal (n:=m+1) (k:ℝ) φ) 1 s
        rcases hτI with hk | hτI
        · exact Or.inl hk
        · right
          apply (originalLeftUnitHom_multiplier_iff f (m+1) E s φ (k:ℝ)).mp
          simpa only [s,originalSectionUnit_hom] using hτI
      refine ⟨⟨s,hsI⟩,fun h => hs (congrArg Subtype.val h),?_⟩
      change v (F s)=j (plainSectionVector v c r τ hτ)
      rw [hread]
      simpa only [s,originalSectionUnit_hom,j] using plainSectionValue_eq_vector c r τ hτ
    · rintro ⟨s,hs,rfl⟩
      let τ : Γ(M,⊤) := (bundleTensorLeftUnitIso M).hom.val.app (.op ⊤) s.val
      have hτ : τ≠0 := by
        intro hz
        have hi := congrArg (fun t => (bundleTensorLeftUnitIso M).inv.val.app (.op ⊤) t) hz
        have hc := congr($((bundleTensorLeftUnitIso M).hom_inv_id).val.app (.op ⊤) |>.hom s.val)
        apply hs
        apply Subtype.ext
        exact hc.symm.trans (hi.trans (map_zero _))
      have hτI : k=0 ∨ IsPlainIdealSection f (m+1) E (multiplierIdeal (n:=m+1) (k:ℝ) φ) τ := by
        rcases s.property with hk | hI
        · exact Or.inl hk
        · exact Or.inr ((originalLeftUnitHom_multiplier_iff f (m+1) E s.val φ (k:ℝ)).mpr hI)
      refine ⟨plainSectionVector v c r τ hτ,⟨τ,hτ,hτI,rfl⟩,?_⟩
      change j (plainSectionVector v c r τ hτ)=v (F s.val)
      rw [hread]
      exact (plainSectionValue_eq_vector c r τ hτ).symm
  have hfinite : (valueSet v ι).Finite :=
    valueSet_finite v ι hι (fun d hd => valuation_algebraMap_complex v hd)
  have hcard := OriginalFieldLeaves.card_originalFieldValueSet_eq_finrank f E a hbig v hv ι hι
  have hcount : Nat.card (AlgebraicValuation.twistedMultiplierValues f (m+1) E v c k r φ)=
      Module.finrank ℂ W := by
    rw [←himage,Nat.card_image_of_injective hj] at hcard
    exact hcard
  refine ⟨?_,hcount⟩
  rw [←himage] at hfinite
  exact hfinite.of_finite_image (fun _ _ _ _ h => hj h)

end SGPT.Okounkov.OriginalTwistedMultiplierCount
