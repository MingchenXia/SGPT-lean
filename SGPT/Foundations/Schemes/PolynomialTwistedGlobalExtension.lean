import SGPT.Foundations.Schemes.PolynomialTwistedSectionExtension
import SGPT.Foundations.Schemes.ProjectiveChartTripleOverlap
import SGPT.Foundations.Schemes.TwistedModuleLocalSectionExtension

/-! # Genuine global extensions of actual projective chart sections

True affine denominator lifts, actual finite overlap annihilators and native
sheaf gluing produce global tensor twists.  Neither global generation nor a
graded representation nor finite global sections is an input.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every actual coordinate-chart module section extends as a true global twist after a coordinate power. -/
theorem polynomialProjCoordinateSection_twistedGlobalExtension
    (M : (polynomialProj K n).Modules)
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]
    (i : Fin (n + 1)) (s : Γ(M, polynomialProjCoordinateOpen K n i)) :
    ∃ (d : ℕ) (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d),
      atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d i t = s := by
  classical
  let a := (polynomialProjTwistingLine K n).atlas
  obtain ⟨d, c, hc⟩ := polynomialProjCoordinateSection_actualLocalLifts K n M i s
  let z := polynomialProjTwistedGlobalCoordinatePower K n i d
  have hz : atlasPowerGlobalCoefficients a d i z = 1 := by
    rw [polynomialProjTwistedGlobalCoordinatePower_coefficient,
      polynomialProjCoordinateRatio_self, map_one, one_pow]
  have hcl : ∀ j, M.val.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op (c j) =
      (polynomialProj K n).sheaf.obj.map
        (homOfLE (inf_le_left : a.opens j ⊓ a.opens i ≤ a.opens j)).op
        (atlasPowerGlobalCoefficients a d j z) •
      M.val.map (homOfLE (inf_le_right : a.opens j ⊓ a.opens i ≤ a.opens i)).op s := by
    intro j
    rw [polynomialProjTwistedGlobalCoordinatePower_coefficient, map_pow]
    exact hc j
  let t := atlasTwistedLocalSectionOfCoefficients a M d c
  have hez : ∀ j k, M.presheaf.map
      (homOfLE (show polynomialProjCoordinateOpen K n j ⊓
          (polynomialProjCoordinateOpen K n k ⊓ polynomialProjCoordinateOpen K n i) ≤
          polynomialProjCoordinateOpen K n j ⊓ polynomialProjCoordinateOpen K n k from
        le_inf inf_le_left (inf_le_right.trans inf_le_left))).op
      (atlasTwistedLocalSectionError a M d t j k) = 0 := fun j k =>
    atlasTwistedLocalSectionError_zero_on_source a M d z i hz s c hcl j k
  choose e he using fun p : Fin (n + 1) × Fin (n + 1) =>
    polynomialProjChartOverlap_zero_after_ratio_power K n M p.1 p.2 i
      (atlasTwistedLocalSectionError a M d t p.1 p.2) (hez p.1 p.2)
  let r := Finset.univ.sup e
  let w := polynomialProjTwistedGlobalCoordinatePower K n i r
  have hw : atlasPowerGlobalCoefficients a r i w = 1 := by
    rw [polynomialProjTwistedGlobalCoordinatePower_coefficient,
      polynomialProjCoordinateRatio_self, map_one, one_pow]
  have hkill : ∀ (j k : Fin (n + 1)), (polynomialProj K n).sheaf.obj.map
      (homOfLE (inf_le_left : a.opens j ⊓ a.opens k ≤ a.opens j)).op
      (atlasPowerGlobalCoefficients a r j w) • atlasTwistedLocalSectionError a M d t j k = 0 := by
    intro j k
    rw [polynomialProjTwistedGlobalCoordinatePower_coefficient, map_pow]
    have hle : e (j, k) ≤ r := Finset.le_sup (Finset.mem_univ (j, k))
    let b : (polynomialProj K n).sheaf.obj.obj (op (a.opens j ⊓ a.opens k)) :=
      (polynomialProj K n).presheaf.map
        (homOfLE (inf_le_left : a.opens j ⊓ a.opens k ≤ a.opens j)).op
        (homogeneousPolynomialBasicOpenAwayEquiv j (polynomialProjCoordinateRatio K n j i))
    have h : b ^ e (j, k) • atlasTwistedLocalSectionError a M d t j k = 0 := he (j, k)
    change b ^ r • atlasTwistedLocalSectionError a M d t j k = 0
    calc
      _ = b ^ (r - e (j, k)) • (b ^ e (j, k) • atlasTwistedLocalSectionError a M d t j k) := by
        rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hle]
      _ = 0 := by rw [h, smul_zero]
  obtain ⟨u, hu, _⟩ := atlasTwistedLocalSectionAction_existsUnique a M r d w t hkill
  refine ⟨r + d, u, ?_⟩
  have hti := atlasTwistedLocalSectionOfCoefficients_source_frame a M d z i hz s c hcl i
    (V := a.opens i) le_rfl le_rfl
  change (((a.frame i).tensorPower d).tensorModuleCoefficients M (𝟙 _))
    ((bundleTensor (bundleTensorPower (polynomialProjTwistingLine K n).sheaf d) M).val.map
      (𝟙 (op (a.opens i))) (t i)) = M.val.map (𝟙 (op (a.opens i))) s at hti
  simp only [PresheafOfModules.map_id] at hti
  unfold atlasTwistedGlobalCoefficients
  rw [hu i]
  unfold atlasTwistedLocalSectionAction
  rw [LinearEquiv.apply_symm_apply, hw, one_smul]
  exact hti

/-- Actual closed-immersion line bundles supply all geometric hypotheses of the genuine global extension theorem. -/
theorem closedPolynomialProjPushforwardCoordinateSection_twistedGlobalExtension
    {X : Scheme} (f : X ⟶ polynomialProj K n) [IsClosedImmersion f]
    {L : X.Modules} (a : LineBundleAtlas L) (i : Fin (n + 1))
    (s : Γ((Scheme.Modules.pushforward f).obj L, polynomialProjCoordinateOpen K n i)) :
    ∃ (d : ℕ) (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
      ((Scheme.Modules.pushforward f).obj L) d),
      atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
        ((Scheme.Modules.pushforward f).obj L) d i t = s := by
  let : ∀ j, (polynomialProjModuleChart ((Scheme.Modules.pushforward f).obj L) j).IsQuasicoherent :=
    fun j => polynomialProjPushforwardChart_isQuasicoherent f a j
  exact polynomialProjCoordinateSection_twistedGlobalExtension K n ((Scheme.Modules.pushforward f).obj L) i s

end

end SGPT.Foundations.Schemes
