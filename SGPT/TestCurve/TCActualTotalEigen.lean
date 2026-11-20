import SGPT.TestCurve.GeomLinSection

/-! Genuine geometric total-space eigenvectors with the original t^{-lambda} sign. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.GeomLin.GeomLinearization
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin
open SGPT.TestCurve.GeomLin

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
  {a : LineBundleAtlas L} {T : TestConfiguration f a}

/-- The actual geometric pullback action has the exact original negative weight character. -/
theorem actSection_eq_negative_character_of_extends [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (Λ : GeomLinearization T)
    {m : ℕ} {lam : ℤ} {s : SectionSpace f L m}
    {σ : SectionSpace T.structureMap T.line m} (hσ : T.Extends lam m s σ) (c : ℂˣ) :
    Λ.actSection c m σ = ((c ^ (-lam) : ℂˣ) : ℂ) • σ := by
  let : IsIntegral T.space := T.isIntegral_space_of_embedding E
  apply T.eq_of_epsCoeff_eq
  intro k
  rw [Λ.epsCoeff_actSection, hσ k, map_mul, Λ.actAt_tUnit_zpow,
    Λ.action.actAt_pullFun, epsCoeff_smul, hσ k]
  ring

/-- Every original weight vector is an actual geometric eigenvector, in every degree. -/
theorem actSection_eq_negative_character_of_mem_weightSpace [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (Λ : GeomLinearization T)
    {m : ℕ} {lam : ℤ} {σ : SectionSpace T.structureMap T.line m}
    (hσ : σ ∈ weightSpace T m lam) (c : ℂˣ) :
    Λ.actSection c m σ = ((c ^ (-lam) : ℂˣ) : ℂ) • σ := by
  obtain ⟨s, hs⟩ := hσ
  exact actSection_eq_negative_character_of_extends E Λ hs c

end SGPT.TestCurve.GeomLin.GeomLinearization
