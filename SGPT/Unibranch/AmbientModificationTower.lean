import SGPT.Unibranch.OriginalClosedSubspaceFactorization
import SGPT.Unibranch.OriginalNativeModification
import SGPT.Unibranch.HironakaG11PresUnconditional
import SGPT.GAGA.ChowBlEmbed

set_option autoImplicit false

namespace SGPT.Unibranch.AmbientModificationTower

open CategoryTheory Set
open SourceReducedComplexSpace OriginalNativeModification SmoothCentreModification
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BlowupTowers
open SGPT.GAGA.H0S SGPT.Projective

/-- A closed reduced embedding, recording its actual reduced closed analytic subspace
and its full structure-sheaf identification over the ambient manifold. -/
def IsClosedReducedEmbedding {n : ℕ} {A : CMfd.{0} n}
    {X : SourceReducedComplexSpace} (j : X ⟶ wholeModel (n := n) A) : Prop :=
  ∃ (C : Set A) (hC : IsComplexAnalyticSubset (n := n) C)
    (e : X ≅ ofClosedAnalytic C hC),
    e.hom ≫ OriginalClosedSubspaceFactorization.inclusion hC
      isComplexAnalyticSubset_univ (Set.subset_univ C) = j

/-- One ambient blow-up realises a given intrinsic blow-up, retaining the actual
intrinsic source and the full commuting square. -/
def AmbientStepBridge (n : ℕ) : Prop :=
  ∀ (A : CMfd.{0} n) {X Y : SourceReducedComplexSpace}
    (j : X ⟶ wholeModel (n := n) A), IsClosedReducedEmbedding (A := A) j →
    (p : Y ⟶ X) → IsSmoothCentreStep p →
    ∃ (A' : CMfd.{0} n) (C : Set A) (β : A' → A) (hβ : IsBlowupAlong n C β)
      (j' : Y ⟶ wholeModel (n := n) A'),
      IsClosedReducedEmbedding (A := A') j' ∧
      j' ≫ nativeMorphism (n := n) (m := n) hβ.contMDiff = p ≫ j

/-- An intrinsic finite modification embeds in an ambient finite blow-up tower.
The square uses the given intrinsic projection and the literal ambient tower projection. -/
theorem exists_ambientTower_of_isModification {n : ℕ}
    (step : AmbientStepBridge n) {A : CMfd.{0} n} {X Y : SourceReducedComplexSpace}
    (j : X ⟶ wholeModel (n := n) A) (hj : IsClosedReducedEmbedding (A := A) j)
    {p : Y ⟶ X} (hp : IsModification p) :
    ∃ (A' : CMfd.{0} n) (T : BlowupTower A A') (j' : Y ⟶ wholeModel (n := n) A'),
      IsClosedReducedEmbedding (A := A') j' ∧
      j' ≫ nativeMorphism (n := n) (m := n) T.contMDiff_proj = p ≫ j := by
  induction hp with
  | id =>
    let T : BlowupTower A A := .refl
    have hid : nativeMorphism (n := n) (m := n) T.contMDiff_proj =
        𝟙 (wholeModel (n := n) A) :=
      morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
    exact ⟨A, T, j, hj, by simp only [hid, Category.comp_id, Category.id_comp]⟩
  | cons p₁ p₀ hp₁ _ ih =>
    obtain ⟨A₀, T₀, j₀, hj₀, h₀⟩ := ih
    obtain ⟨A₁, C, β, hβ, j₁, hj₁, h₁⟩ := step A₀ j₀ hj₀ p₁ hp₁
    let T₁ := T₀.step C β hβ
    have hcomp : nativeMorphism hβ.contMDiff ≫ nativeMorphism T₀.contMDiff_proj =
        nativeMorphism T₁.contMDiff_proj :=
      morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
    refine ⟨A₁, T₁, j₁, hj₁, ?_⟩
    calc
      j₁ ≫ nativeMorphism T₁.contMDiff_proj =
          (j₁ ≫ nativeMorphism hβ.contMDiff) ≫ nativeMorphism T₀.contMDiff_proj := by
        rw [hcomp.symm, Category.assoc]
      _ = p₁ ≫ (j₀ ≫ nativeMorphism T₀.contMDiff_proj) := by rw [h₁, Category.assoc]
      _ = (p₁ ≫ p₀) ≫ j := by rw [h₀, Category.assoc]

/-- For a compact projective ambient manifold, the same terminal ambient manifold is
compact and projective by Chow's theorem for smooth-centre blow-up towers. -/
theorem exists_projectiveAmbientTower_of_isModification {n N : ℕ}
    (step : AmbientStepBridge n) {A : CMfd.{0} n} [CompactSpace A]
    {Ψ : A → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {X Y : SourceReducedComplexSpace}
    (j : X ⟶ wholeModel (n := n) A) (hj : IsClosedReducedEmbedding (A := A) j)
    {p : Y ⟶ X} (hp : IsModification p) :
    ∃ (A' : CMfd.{0} n) (T : BlowupTower A A') (j' : Y ⟶ wholeModel (n := n) A'),
      IsClosedReducedEmbedding (A := A') j' ∧
      j' ≫ nativeMorphism (n := n) (m := n) T.contMDiff_proj = p ≫ j ∧
      CompactSpace A' ∧
      ∃ (N' : ℕ) (Ψ' : A' → ComplexProjectiveSpace N'), IsHolomorphicEmbedding (n := n) Ψ' := by
  obtain ⟨A', T, j', hj', hcomm⟩ := exists_ambientTower_of_isModification step (A := A) j hj hp
  exact ⟨A', T, j', hj', hcomm,
    SGPT.GAGA.ChowBl.exists_isHolomorphicEmbedding_of_isBlowupSequence hΨ T.isBlowupSequence⟩

/-- Apply the ambient construction to the unchanged finite resolution supplied by G11. -/
theorem exists_resolution_in_projectiveAmbientTower {n N : ℕ}
    (step : AmbientStepBridge n) {A : CMfd.{0} n} [CompactSpace A]
    {Ψ : A → ComplexProjectiveSpace N} (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (X : SourceReducedComplexSpace) (hX : CompactSpace X.obj.left)
    (j : X ⟶ wholeModel (n := n) A) (hj : IsClosedReducedEmbedding (A := A) j) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X)
      (A' : CMfd.{0} n) (T : BlowupTower A A') (j' : Y ⟶ wholeModel (n := n) A'),
      IsModification p ∧ IsResolution p ∧
      IsClosedReducedEmbedding (A := A') j' ∧
      j' ≫ nativeMorphism (n := n) (m := n) T.contMDiff_proj = p ≫ j ∧
      CompactSpace A' ∧
      ∃ (N' : ℕ) (Ψ' : A' → ComplexProjectiveSpace N'), IsHolomorphicEmbedding (n := n) Ψ' := by
  obtain ⟨Y, p, -, hp, -, hres, -⟩ := HironakaG11PresUnconditional.exists_endpoint X hX
  obtain ⟨A', T, j', hj', hcomm, hprojective⟩ :=
    exists_projectiveAmbientTower_of_isModification step (A := A) hΨ j hj hp
  exact ⟨Y, p, A', T, j', hp, hres, hj', hcomm, hprojective⟩

end SGPT.Unibranch.AmbientModificationTower
