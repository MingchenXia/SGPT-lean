import SGPT.Foundations.Schemes.BundleMorphismGluing
import SGPT.Foundations.Schemes.NativeLinePullbackFrames
import SGPT.Foundations.Schemes.GenericBundleFrameTransition
import SGPT.Foundations.Schemes.NativeProjectiveCoordinateExtension
import SGPT.Foundations.Schemes.NativeGeneratorPullbackTransitions
import SGPT.Foundations.Schemes.NativePolynomialPullbackPower

/-! Actual original rational section pairs for arbitrary valuations.
Blueprint: okounkov-original-rational-pairs.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalRationalPairs
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace
variable {X : Scheme.{0}} [IsIntegral X]

/-- SAME actual original section quotient is independent of EVERY genuine nonempty frame. -/
theorem originalSectionRatio_frame_independent {L : X.Modules} {U V : X.Opens}
    [Nonempty U] [Nonempty V] (e : LocalBundleFrame L U) (d : LocalBundleFrame L V)
    (s t : Γ(L, ⊤)) :
    globalSectionToFunctionField d s / globalSectionToFunctionField d t =
      globalSectionToFunctionField e s / globalSectionToFunctionField e t := by
  let W := U ⊓ V
  let : Nonempty W := ⟨⟨genericPoint X, genericPoint_mem_nonempty_open U, genericPoint_mem_nonempty_open V⟩⟩
  let τ := X.germToFunctionField W
    (localBundleFrameTransition e d (Opens.infLELeft U V) (Opens.infLERight U V) : X.sheaf.obj.obj (op W))
  have hτ : τ ≠ 0 :=
    ((localBundleFrameTransition e d (Opens.infLELeft U V) (Opens.infLERight U V)).isUnit.map
      (X.germToFunctionField W).hom).ne_zero
  have hs := genericBundleFiberFrame_transition e d (Opens.infLELeft U V)
    (Opens.infLERight U V) (bundleGenericGerm L ⊤ s)
  have ht := genericBundleFiberFrame_transition e d (Opens.infLELeft U V)
    (Opens.infLERight U V) (bundleGenericGerm L ⊤ t)
  rw [genericBundleFiberFrame_global_germ, genericBundleFiberFrame_global_germ] at hs ht
  rw [hs, ht]
  exact mul_div_mul_left _ _ hτ

/-- Actual tensor atlas on every pairwise original open, with genuine restricted frames. -/
def originalPairwiseTensorAtlas {L M : X.Modules} (a : LineBundleAtlas L) (b : LineBundleAtlas M) :
    LineBundleAtlas (bundleTensor L M) where
  I := a.I × b.I
  opens ij := a.opens ij.1 ⊓ b.opens ij.2
  covers x := by
    obtain ⟨i, hi⟩ := a.covers x
    obtain ⟨j, hj⟩ := b.covers x
    exact ⟨(i,j), hi, hj⟩
  frame ij :=
    LocalBundleFrame.tensor (bundleHomRestrictionIso L (SheafOfModules.unit X.ringCatSheaf)
      (Opens.infLELeft (a.opens ij.1) (b.opens ij.2)) (a.frame ij.1))
    (bundleHomRestrictionIso M (SheafOfModules.unit X.ringCatSheaf)
      (Opens.infLERight (a.opens ij.1) (b.opens ij.2)) (b.frame ij.2))

omit [IsIntegral X] in
/-- Original projective extension manufactures a genuine ordinary section AND its same-line unit coefficient section. -/
theorem originalProjectiveCoordinatePair {N : ℕ} (i : X ⟶ polynomialProj ℂ N)
    [IsClosedImmersion i] (j : Fin (N+1))
    (a : Γ(X, i ⁻¹ᵁ polynomialProjCoordinateOpen ℂ N j)) :
    ∃ (Q : X.Modules) (_b : LineBundleAtlas Q)
      (e : LocalBundleFrame Q (i ⁻¹ᵁ polynomialProjCoordinateOpen ℂ N j)) (s u : Γ(Q, ⊤)),
      e.coefficients (𝟙 _) (Q.val.map (homOfLE le_top).op s) = a ∧
      e.coefficients (𝟙 _) (Q.val.map (homOfLE le_top).op u) = 1 := by
  obtain ⟨d, s, hs⟩ := nativeClosedProjectiveCoordinateSection_pullbackExtension ℂ N i
    (trivialIntrinsicLineBundle X).atlas j a
  let P := (Scheme.Modules.pullback i).obj (bundleTensorPower (polynomialProjTwistingLine ℂ N).sheaf d)
  let Q := bundleTensor P (SheafOfModules.unit X.ringCatSheaf)
  let e := nativePolynomialPowerPullbackFrame ℂ N i d j
  let α := nativePolynomialPowerCoordinateHom ℂ N d j
  let γ := nativePullbackGlobalHom i α
  let u : Γ(Q, ⊤) := tensorSection P (SheafOfModules.unit X.ringCatSheaf) ⊤
    (γ.val.app (op ⊤) (1 : Γ(X, ⊤))) (1 : Γ(X, ⊤))
  let bP := ((polynomialProjTwistingLine ℂ N).atlas.tensorPower d).nativePullback i
  let bQ := originalPairwiseTensorAtlas bP (trivialIntrinsicLineBundle X).atlas
  refine ⟨Q, bQ, e.tensorModule (SheafOfModules.unit X.ringCatSheaf), s, u, hs, ?_⟩
  change e.tensorModuleCoefficients (SheafOfModules.unit X.ringCatSheaf) (𝟙 _)
    (Q.val.map (homOfLE le_top).op u) = (1 : Γ(X, i ⁻¹ᵁ polynomialProjCoordinateOpen ℂ N j))
  dsimp only [u, Q]
  rw [tensorSection_restrict, LocalBundleFrame.tensorModuleCoefficients_tmul]
  let U := i ⁻¹ᵁ polynomialProjCoordinateOpen ℂ N j
  have hr : P.val.map (homOfLE (le_top : U ≤ ⊤)).op
      (γ.val.app (op ⊤) (1 : Γ(X, ⊤))) = γ.val.app (op U) (1 : Γ(X,U)) := by
    have h := PresheafOfModules.naturality_apply γ.val (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(X,⊤))
    change γ.val.app (op U) (X.presheaf.map (homOfLE le_top).op 1) = _ at h
    rw [map_one] at h
    exact h.symm
  rw [hr]
  have hc : e.coefficients (𝟙 _)
      (γ.val.app (op (i ⁻¹ᵁ polynomialProjCoordinateOpen ℂ N j))
        (1 : Γ(X, i ⁻¹ᵁ polynomialProjCoordinateOpen ℂ N j))) = 1 :=
    nativeGlobalGeneratorFrame_hom_one γ _ (𝟙 _)
  rw [hc]
  change (1 : Γ(X, U)) * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 1 = 1
  rw [map_one, mul_one]

/-- Every SAME original nonzero rational function is the quotient of actual ordinary sections of one manufactured original line. -/
theorem exists_originalSectionPair_of_functionField
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    (r : X.functionField) (hr : r ≠ 0) :
    ∃ (T : X.Modules) (_aT : LineBundleAtlas T) (s t : Γ(T, ⊤)),
      s ≠ 0 ∧ t ≠ 0 ∧ ∀ (V : X.Opens) (hV : Nonempty V) (e : LocalBundleFrame T V),
        letI := hV
        globalSectionToFunctionField e s / globalSectionToFunctionField e t = r := by
  classical
  let i := E.map
  let j := (nativePolynomialPullbackAtlas ℂ E.ambientDimension i).centerIndex (genericPoint X)
  let U := i ⁻¹ᵁ polynomialProjCoordinateOpen ℂ E.ambientDimension j
  have hxU : genericPoint X ∈ U :=
    (nativePolynomialPullbackAtlas ℂ E.ambientDimension i).centerIndex_mem (genericPoint X)
  let : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  have hU : IsAffineOpen U := (polynomialProjCoordinateOpen_isAffine ℂ E.ambientDimension j).preimage i
  let : IsFractionRing Γ(X,U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective Γ(X,U) r
  have hbK : X.germToFunctionField U b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have haK : X.germToFunctionField U a ≠ 0 := by
    intro h0
    apply hr
    change X.germToFunctionField U a / X.germToFunctionField U b = r at hab
    rw [h0, zero_div] at hab
    exact hab.symm
  obtain ⟨Qa,ba,ea,sa,ua,hsa,hua⟩ := originalProjectiveCoordinatePair i j a
  obtain ⟨Qb,bb,eb,sb,ub,hsb,hub⟩ := originalProjectiveCoordinatePair i j b
  change ea.coefficients (𝟙 U) (Qa.val.map U.leTop.op sa) = a at hsa
  change ea.coefficients (𝟙 U) (Qa.val.map U.leTop.op ua) = (1 : Γ(X,U)) at hua
  change eb.coefficients (𝟙 U) (Qb.val.map U.leTop.op sb) = b at hsb
  change eb.coefficients (𝟙 U) (Qb.val.map U.leTop.op ub) = (1 : Γ(X,U)) at hub
  let T := bundleTensor Qa Qb
  let aT := originalPairwiseTensorAtlas ba bb
  let e : LocalBundleFrame T U := ea.tensor eb
  let s : Γ(T,⊤) := tensorSection Qa Qb ⊤ sa ub
  let t : Γ(T,⊤) := tensorSection Qa Qb ⊤ ua sb
  have hsfield : globalSectionToFunctionField e s = X.germToFunctionField U a := by
    change X.germToFunctionField U (e.coefficients (𝟙 U) (T.val.map U.leTop.op s)) = _
    dsimp only [s, T, e]
    rw [tensorSection_restrict, LocalBundleFrame.tensor_coefficients]
    exact congrArg (X.germToFunctionField U) ((congrArg₂ (fun x y : Γ(X,U) => x*y) hsa hub).trans (mul_one a))
  have htfield : globalSectionToFunctionField e t = X.germToFunctionField U b := by
    change X.germToFunctionField U (e.coefficients (𝟙 U) (T.val.map U.leTop.op t)) = _
    dsimp only [t, T, e]
    rw [tensorSection_restrict, LocalBundleFrame.tensor_coefficients]
    exact congrArg (X.germToFunctionField U) ((congrArg₂ (fun x y : Γ(X,U) => x*y) hua hsb).trans (one_mul b))
  have hs : s ≠ 0 := by
    intro hzero
    apply haK
    rw [← hsfield, hzero, map_zero]
  have ht : t ≠ 0 := by
    intro hzero
    apply hbK
    rw [← htfield, hzero, map_zero]
  refine ⟨T,aT,s,t,hs,ht,?_⟩
  intro V hV d
  let := hV
  exact (originalSectionRatio_frame_independent e d s t).trans
    ((congrArg₂ (fun x y : X.functionField => x / y) hsfield htfield).trans hab)

end SGPT.Okounkov.OriginalRationalPairs
