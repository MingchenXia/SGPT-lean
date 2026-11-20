import SGPT.Okounkov.OF4ValCurrCommonLifting
import SGPT.Okounkov.OF2ValCurrPresentation
import SGPT.Okounkov.FlagLelong

/-!
# `rmk:valcurr`: independence for presentations by flags lifted from `X`

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr` (`ν(T) := ν_{Y•}(π^*T) g` for a
presentation `ν = ν_{Y•} g` on a resolution `π`, independent of `π`).

Let `X` be an integral smooth projective complex scheme of dimension `n = m + 1` and consider
presentations `ν = (ν_{W•} ∘ π^*) G` on analytic modifications `π : X' → X(ℂ)` whose flag `W•` is
the lifting (`def:lifting`) of a smooth flag `Y•` of `X(ℂ)` itself (for instance `π = id`,
`W• = Y•`).

* `modificationFlagValuation_id_eq`: for `π = id` the induced valuation of `ℂ(X)` is the flag
  valuation `ν_{Y•}` of the original scheme (`schemeFubiniStudyFunctionFieldValuation`).
* `modificationPresentationValue_eq_of_lifted` (**independence across models**): two presentations
  of the same surjective `ν` on two (arbitrary, unrelated) modifications, by flags lifted from
  smooth flags `Y¹•`, `Y²•` of `X`, give the same value `ν(T)` for every closed positive
  `(1,1)`-current `T = θ + dd^c u` on `X(ℂ)`. Indeed `ν = ν_{Yⁱ•} (cor(Yⁱ•, πᵢ) Gᵢ)` (algebraic
  `prop:cormatrix`),
  so `Y¹• = Y²•` and `cor(Y¹•, π₁) G₁ = cor(Y²•, π₂) G₂` (flag reconstruction on `X` and uniqueness
  of the matrix), and both values equal `ν_{Y•}(T) cor(Yⁱ•, πᵢ) Gᵢ` (refinement invariance, i.e. the
  current `prop:cormatrix`).

Presentations by flags with an exceptional member (not liftings of flags of `X`) are not covered:
for them the coincidence of flags on a common model is the missing input (see
`OF4.modificationPresentationValue_eq_of_common_lifting`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF4

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValCurr SGPT.Okounkov.OF2
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
open scoped Matrix

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance of4LiftTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of4LiftCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of4LiftManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

omit [IsIntegral X] in
/-- The identity of `X(ℂ)`, viewed as a modification from the flag geometry of a smooth flag of
`X`. -/
theorem isAnalyticModification_flagGeometry_id (E : ClosedProjectiveEmbedding f)
    (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    IsAnalyticModification (n := m + 1)
      (id : (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY).carrier →
        SchemeComplexPoint f) :=
  isAnalyticModification_identity

/-- For `π = id`, the valuation of `ℂ(X)` induced by a smooth flag of `X` is its flag valuation. -/
theorem modificationFlagValuation_id_eq (E : ClosedProjectiveEmbedding f)
    (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    modificationFlagValuation f (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (isAnalyticModification_flagGeometry_id f E Y hY) =
      schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY := by
  set F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with hFdef
  set x : OriginalFlagGermPoint F := schemeProjectiveOriginalFlagPoint f (m + 1) E
    (schemeProjectiveTNKahlerBackground f (m + 1) E) Y hY with hxdef
  have hid := isAnalyticModification_flagGeometry_id f E Y hY
  have hstalk : ∀ g : X.presheaf.stalk (schemeComplexPointImage f x.1),
      modificationFlagValuation f F hid (algebraMap _ X.functionField g) =
        schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY
          (algebraMap _ X.functionField g) := by
    intro g
    refine (modificationFlagValuation_stalk_at f F hid x g).trans ?_
    refine Eq.trans ?_ (schemeOriginalFlagFunctionFieldValuation_stalk f (m + 1) E
      (schemeProjectiveTNKahlerBackground f (m + 1) E) Y hY g).symm
    change originalFlagGermValuation F x (NativeHolGerm.comap id hid.1 x.1
      (schemeNativeStalkGerm f (m + 1) x.1 g)) =
        originalFlagGermValuation F x (schemeNativeStalkGerm f (m + 1) x.1 g)
    congr 1
    obtain ⟨G, hG, hGe⟩ := NativeHolGerm.exists_eq_mk (schemeNativeStalkGerm f (m + 1) x.1 g)
    rw [hGe]
    exact Subtype.ext (NativeHolGerm.comap_mk id hid.1 x.1 G hG)
  apply AddValuation.ext
  intro q
  obtain ⟨a, b, -, rfl⟩ :=
    IsFractionRing.div_surjective (A := X.presheaf.stalk (schemeComplexPointImage f x.1)) q
  rw [AddValuation.map_div, AddValuation.map_div, hstalk a, hstalk b]

/-- A presentation by a flag lifted from a smooth flag `Y•` of `X` is a presentation by `Y•` on `X`
with the matrix `cor(Y•, p) G`, with the same value `ν(T)`. -/
theorem lifted_presentation_eq (E : ClosedProjectiveEmbedding f)
    (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    {W : OriginalFlagGeometry.{0} (m + 1)}
    {p : W.carrier → (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY).carrier}
    (hp : IsFlagLifting (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) W p)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    {G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hG : IsUnitUpperTriangular G)
    (hpres : v = lexMapValuation G hG (modificationFlagValuation f W
      (AnalyticModificationComposition.isAnalyticModification_comp
        (isAnalyticModification_flagGeometry_id f E Y hY) hp.1)))
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (u : SchemeComplexPoint f → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    v = lexMapValuation (flagLiftingCorrectionMatrix (m + 1) _ W p hp * G)
        ((isUnitUpperTriangular_flagLiftingCorrectionMatrix (m + 1) _ W p hp).mul hG)
        (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY) ∧
      modificationPresentationValue f W
          (AnalyticModificationComposition.isAnalyticModification_comp
            (isAnalyticModification_flagGeometry_id f E Y hY) hp.1) G θ u hu =
        modificationPresentationValue f (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
          (isAnalyticModification_flagGeometry_id f E Y hY)
          (flagLiftingCorrectionMatrix (m + 1) _ W p hp * G) θ u hu := by
  have hid := isAnalyticModification_flagGeometry_id f E Y hY
  have hC := isUnitUpperTriangular_flagLiftingCorrectionMatrix (m + 1) _ W p hp
  set C := flagLiftingCorrectionMatrix (m + 1) _ W p hp with hCdef
  have hcor := modificationFlagValuation_lifting f hid hp
  have hv : v = lexMapValuation (C * G) (hC.mul hG)
      (modificationFlagValuation f (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        hid) := by
    rw [hpres, hcor]
    apply AddValuation.ext
    intro r
    rw [lexMapValuation_apply, lexMapValuation_apply, lexMapValuation_apply, lexWithTopHom_mul]
  refine ⟨by rw [hv, modificationFlagValuation_id_eq f E Y hY], ?_⟩
  obtain ⟨-, hval⟩ := modificationPresentationValue_lifting f hid hp v (hC.mul hG) hv θ u hu
  rw [← hval]
  congr 1
  rw [← Matrix.mul_assoc, hC.inv_mul, Matrix.one_mul]

/-- **`rmk:valcurr`: independence across models for presentations by flags lifted from `X`.**
Two presentations `ν = (ν_{W¹} ∘ π₁^*) G₁ = (ν_{W²} ∘ π₂^*) G₂` of the same surjective valuation `ν`
on two analytic modifications, where `Wⁱ•` is the lifting of a smooth flag `Yⁱ•` of `X(ℂ)`, give the
same value `ν(T)` for every closed positive `(1,1)`-current `T = θ + dd^c u` on `X(ℂ)`. -/
theorem modificationPresentationValue_eq_of_lifted (E : ClosedProjectiveEmbedding f)
    (Y₁ Y₂ : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY₁ : IsSmoothFlag Y₁)
    (hY₂ : IsSmoothFlag Y₂) {W₁ W₂ : OriginalFlagGeometry.{0} (m + 1)}
    {p₁ : W₁.carrier → (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y₁ hY₁).carrier}
    (hp₁ : IsFlagLifting (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y₁ hY₁) W₁ p₁)
    {p₂ : W₂.carrier → (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y₂ hY₂).carrier}
    (hp₂ : IsFlagLifting (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y₂ hY₂) W₂ p₂)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hv : Function.Surjective v)
    {G₁ G₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hG₁ : IsUnitUpperTriangular G₁)
    (hG₂ : IsUnitUpperTriangular G₂)
    (h₁ : v = lexMapValuation G₁ hG₁ (modificationFlagValuation f W₁
      (AnalyticModificationComposition.isAnalyticModification_comp
        (isAnalyticModification_flagGeometry_id f E Y₁ hY₁) hp₁.1)))
    (h₂ : v = lexMapValuation G₂ hG₂ (modificationFlagValuation f W₂
      (AnalyticModificationComposition.isAnalyticModification_comp
        (isAnalyticModification_flagGeometry_id f E Y₂ hY₂) hp₂.1)))
    (θ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)) (u : SchemeComplexPoint f → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    modificationPresentationValue f W₁
        (AnalyticModificationComposition.isAnalyticModification_comp
          (isAnalyticModification_flagGeometry_id f E Y₁ hY₁) hp₁.1) G₁ θ u hu =
      modificationPresentationValue f W₂
        (AnalyticModificationComposition.isAnalyticModification_comp
          (isAnalyticModification_flagGeometry_id f E Y₂ hY₂) hp₂.1) G₂ θ u hu := by
  obtain ⟨hv₁, hval₁⟩ := lifted_presentation_eq f E Y₁ hY₁ hp₁ v hG₁ h₁ θ u hu
  obtain ⟨hv₂, hval₂⟩ := lifted_presentation_eq f E Y₂ hY₂ hp₂ v hG₂ h₂ θ u hu
  rw [hval₁, hval₂]
  -- the two presentations on `X` coincide
  have hYM : Y₁ = Y₂ := by
    have hequiv : ValuationsLexEquivalent
        (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y₁ hY₁)
        (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y₂ hY₂) :=
      valuationsLexEquivalent_equivalence.trans ⟨_, _, hv₁⟩
        (valuationsLexEquivalent_equivalence.symm ⟨_, _, hv₂⟩)
    exact schemeOriginalFlags_eq_of_lexEquivalent f (m + 1) E
      (schemeProjectiveTNKahlerBackground f (m + 1) E)
      (schemeProjectiveTNKahlerBackground f (m + 1) E) Y₁ Y₂ hY₁ hY₂ hequiv
  subst hYM
  have hM := OF2.matrix_eq_of_lexMapValuation_eq
    (surjective_schemeFubiniStudyFunctionFieldValuation f E Y₁ hY₁) _ _ (hv₁.symm.trans hv₂)
  rw [hM]

end SGPT.Okounkov.OF4
