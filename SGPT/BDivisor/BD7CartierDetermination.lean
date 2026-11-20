import SGPT.BDivisor.BD7CanonicalNumericalInverseLimit
import SGPT.BDivisor.ModificationChangeOfVariables

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy CanonicalCurrentFrame
open SGPT.Okounkov.OF13
open scoped Manifold ContDiff

local instance cartierDeterminationPointTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g

local instance cartierDeterminationPointCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] : ChartedSpace (ComplexModel d) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g d

local instance cartierDeterminationPointManifold {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g d

variable {Z : Scheme.{0}} {f : Z ⟶ Spec (.of ℂ)} {m : ℕ}
    [IsIntegral Z] [SmoothOfRelativeDimension (m + 1) f]
    [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    (E : ClosedProjectiveEmbedding f)

local notation "M" => SmoothAlgebraicModel f (m + 1)
local notation "N" => SmoothModelNumericalClasses (f := f) (d := m + 1)
local notation "Book" => BookBlowupModel (f := f) (d := m + 1)

/-- Actual pullback of real Cartier combinations on the original numerical quotient. -/
def smoothModelNumericalCartierPullback {A B : M} (h : A ≤ B) : N A →ₗ[ℝ] N B := by
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := B.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  letI := smoothProjectiveNativeConnected (B.p ≫ f) (m + 1) B.embedding
  exact numericalCartierPullback (B.p ≫ f) (A.p ≫ f) B.embedding A.embedding
    (m := m) normalizationProjectiveForCurves_bd7 (A.homOfLE h)
    (SmoothAlgebraicModel.homOfLE_structure h)

include E in
theorem smoothModelNumericalCartierPullback_trans
    {A B C : M} (h : A ≤ B) (k : B ≤ C) (v : N A) :
    smoothModelNumericalCartierPullback (h.trans k) v =
      smoothModelNumericalCartierPullback k (smoothModelNumericalCartierPullback h v) := by
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  letI := C.embedding.isSeparated
  letI := C.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := B.embedding.analyticCompact
  letI := C.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  letI := smoothProjectiveNativeConnected (B.p ≫ f) (m + 1) B.embedding
  letI := smoothProjectiveNativeConnected (C.p ≫ f) (m + 1) C.embedding
  apply (integralNumericalEquivNS_bd7 (C.p ≫ f) C.embedding m
    normalizationProjectiveForCurves_bd7).injective
  apply Subtype.ext
  simp only [smoothModelNumericalCartierPullback, numericalChern_numericalCartierPullback]
  rw [← classPullback_comp]
  exact classPullback_congr (smoothModelComplexPointMap_homOfLE_trans E h k) _ _ _

theorem smoothModelTransportedAnalyticPushforward_numericalCartierPullback
    {A B : M} (h : A ≤ B) (v : N A) :
    smoothModelTransportedAnalyticPushforward E h (smoothModelNumericalCartierPullback h v) = v := by
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := B.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  letI := smoothProjectiveNativeConnected (B.p ≫ f) (m + 1) B.embedding
  apply (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m
    normalizationProjectiveForCurves_bd7).injective
  apply Subtype.ext
  simp only [smoothModelTransportedAnalyticPushforward, smoothModelNumericalCartierPullback,
    numericalChern_transportedAnalyticPushforward, numericalChern_numericalCartierPullback]
  exact classPushforward_classPullback
    (SmoothAlgebraicModel.homOfLE_analyticModification h E) (Nat.succ_pos m) _

section Diffeo

variable {U V : Type} [TopologicalSpace U] [ChartedSpace (ComplexModel (m + 1)) U]
    [IsComplexManifold (m + 1) U] [CompactSpace U]
    [TopologicalSpace V] [ChartedSpace (ComplexModel (m + 1)) V]
    [IsComplexManifold (m + 1) V] [CompactSpace V]

private theorem classPushforward_diffeo_injective
    (e : U ≃ₘ⟮𝓘(ℂ, ComplexModel (m + 1)), 𝓘(ℂ, ComplexModel (m + 1))⟯ V) :
    Function.Injective
      (classPushforward e.contMDiff (canonicalBasis (m + 1)) (Nat.succ_pos m)) := by
  intro a b h
  have inverse (v : RealBottChern (m + 1) U) :
      classPushforward e.symm.contMDiff (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (classPushforward e.contMDiff (canonicalBasis (m + 1)) (Nat.succ_pos m) v) = v := by
    rw [← classPushforward_comp (canonicalBasis (m + 1)) (Nat.succ_pos m)]
    have H {g : U → U} (hg : g = id)
        (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ g) :
        classPushforward hs (canonicalBasis (m + 1)) (Nat.succ_pos m) v = v := by
      subst g
      exact classPushforward_id (canonicalBasis (m + 1)) (Nat.succ_pos m) v
    exact H (funext e.symm_apply_apply) _
  calc
    a = _ := (inverse a).symm
    _ = _ := congrArg _ h
    _ = b := inverse b

end Diffeo

/-- The actual Cartier pullback along algebraic domination respects the same
Bott--Chern transition as the corresponding domination of the book's towers. -/
theorem bookModelNumericalChern_pullback_square
    (E : ClosedProjectiveEmbedding f)
    (alg : ∀ π : Book, BookModelAlgebraization (f := f) (d := m + 1) π)
    {π τ : Book} (h : π ≤ τ) (v : N (alg π).A) :
    (bookModelNumericalChern alg τ
      (smoothModelNumericalCartierPullback (bookModelAlgebraization_monotone E alg h) v)).val =
      Modification.classPullbackOfLE (show π.1 ≤ τ.1 from h)
        (bookModelNumericalChern alg π v).val := by
  let A := (alg π).A
  let B := (alg τ).A
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI := B.embedding.isSeparated
  letI := B.embedding.quasiCompact
  letI := A.embedding.analyticCompact
  letI := B.embedding.analyticCompact
  letI := smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  letI := smoothProjectiveNativeConnected (B.p ≫ f) (m + 1) B.embedding
  let hA : A ≤ B := bookModelAlgebraization_monotone E alg h
  let hq := SmoothAlgebraicModel.homOfLE_structure hA
  let g := SmoothAlgebraicModel.homOfLE_analyticModification hA E
  let k := Modification.Dominates.isAnalyticModification (show π.1 ≤ τ.1 from h)
  let c := (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m
    normalizationProjectiveForCurves_bd7 v).val
  let α := classPushforward (alg π).e.contMDiff (canonicalBasis (m + 1)) (Nat.succ_pos m) c
  have hinverse : classPullback (alg π).e.contMDiff α = c := by
    apply classPushforward_diffeo_injective (alg π).e
    exact classPushforward_classPullback
      (isAnalyticModification_of_diffeomorph (alg π).e) (Nat.succ_pos m) α
  have hcartier := numericalChern_numericalCartierPullback
    (B.p ≫ f) (A.p ≫ f) B.embedding A.embedding (m := m)
    normalizationProjectiveForCurves_bd7 (A.homOfLE hA) hq v
  have hs := classPullback_transition_square (alg π).e (alg τ).e g.1 k.1
    (bookModelAlgebraization_transition E alg h) α
  change classPushforward (alg τ).e.contMDiff (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (integralNumericalEquivNS_bd7 (B.p ≫ f) B.embedding m normalizationProjectiveForCurves_bd7
        (smoothModelNumericalCartierPullback hA v)).val = classPullback k.1 α
  rw [smoothModelNumericalCartierPullback, hcartier]
  change classPushforward (alg τ).e.contMDiff (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (classPullback g.1 c) = classPullback k.1 α
  rw [← hinverse, hs]
  exact classPushforward_classPullback
    (isAnalyticModification_of_diffeomorph (alg τ).e) (Nat.succ_pos m) _

/-- An ordinary numerical Weil family is Cartier on its determining algebraic model
if all higher traces are related by actual pullback of scheme line bundles. -/
def IsOriginalNumericallyDeterminedOn
    {push : ∀ ⦃A B : M⦄, A ≤ B → N B →ₗ[ℝ] N A}
    (D : compatibleLinearFamilies (R := ℝ) push) (A : M) (v : N A) : Prop :=
  ∀ B (h : A ≤ B), D.val B = smoothModelNumericalCartierPullback h v

include E in
/-- Determination moves from an arbitrary algebraic model to any dominating model
by pulling back its determining Cartier class. -/
theorem IsOriginalNumericallyDeterminedOn.of_le
    {push : ∀ ⦃A B : M⦄, A ≤ B → N B →ₗ[ℝ] N A}
    {D : compatibleLinearFamilies (R := ℝ) push} {A B : M} {v : N A}
    (hD : IsOriginalNumericallyDeterminedOn D A v) (h : A ≤ B) :
    IsOriginalNumericallyDeterminedOn D B (smoothModelNumericalCartierPullback h v) := by
  intro C k
  exact (hD C (h.trans k)).trans (smoothModelNumericalCartierPullback_trans E h k v)

/-- It suffices to check ordinary determination above a given model on the
cofinal chosen book algebraizations. This form isolates the two actual
pullback identities used by descent. -/
theorem isOriginalNumericallyDeterminedOn_iff_cofinal
    (E : ClosedProjectiveEmbedding f)
    (alg : ∀ π : Book, BookModelAlgebraization (f := f) (d := m + 1) π)
    {push : ∀ ⦃A B : M⦄, A ≤ B → N B →ₗ[ℝ] N A}
    (pullTrans : ∀ ⦃A B C : M⦄ (h : A ≤ B) (k : B ≤ C) (v : N A),
      smoothModelNumericalCartierPullback (h.trans k) v =
        smoothModelNumericalCartierPullback k (smoothModelNumericalCartierPullback h v))
    (pushPull : ∀ ⦃B C : M⦄ (h : B ≤ C) (v : N B),
      push h (smoothModelNumericalCartierPullback h v) = v)
    (D : compatibleLinearFamilies (R := ℝ) push) (π : Book) (v : N (alg π).A) :
    IsOriginalNumericallyDeterminedOn D (alg π).A v ↔
      ∀ τ (h : π ≤ τ), D.val (alg τ).A =
        smoothModelNumericalCartierPullback (bookModelAlgebraization_monotone E alg h) v := by
  constructor
  · intro h τ hπτ
    exact h (alg τ).A (bookModelAlgebraization_monotone E alg hπτ)
  · intro h B hAB
    obtain ⟨σ, hBσ⟩ := bookModelAlgebraization_cofinal E alg B
    obtain ⟨τ, hπτ, hστ⟩ := ModelSystem.Model.exists_le_le π σ
    have hBτ : B ≤ (alg τ).A :=
      hBσ.trans (bookModelAlgebraization_monotone E alg hστ)
    calc
      D.val B = push hBτ (D.val (alg τ).A) := (D.property B (alg τ).A hBτ).symm
      _ = push hBτ (smoothModelNumericalCartierPullback (hAB.trans hBτ) v) :=
        congrArg (push hBτ) (h τ hπτ)
      _ = smoothModelNumericalCartierPullback hAB v := by
        rw [pullTrans hAB hBτ v]
        exact pushPull hBτ (smoothModelNumericalCartierPullback hAB v)

open SGPT.Hodge.BDivChain.NativeDraft

/-- Cartier determination on a chosen algebraic model gives realization on its book tower. -/
theorem isRealizationAny_of_originalNumericallyDeterminedOn
    (E : ClosedProjectiveEmbedding f)
    (alg : ∀ π : Book, BookModelAlgebraization (f := f) (d := m + 1) π)
    {push : ∀ ⦃A B : M⦄, A ≤ B → N B →ₗ[ℝ] N A}
    {D : compatibleLinearFamilies (R := ℝ) push}
    {C : WeilFamilyAny (ModelSystem.blowup (m + 1) (SchemeComplexPoint f))}
    (coords : ∀ τ : Book, C.val τ = (bookModelNumericalChern alg τ (D.val (alg τ).A)).val)
    (π : Book) (v : N (alg π).A)
    (hD : IsOriginalNumericallyDeterminedOn D (alg π).A v) :
    IsRealizationAny C π (bookModelNumericalChern alg π v).val := by
  intro τ h
  rw [coords τ, hD (alg τ).A (bookModelAlgebraization_monotone E alg h)]
  exact bookModelNumericalChern_pullback_square E alg h v

/-- Analytic realization reads back the original ordinary determination on
every higher algebraic model, by passing through a cofinal tower. -/
theorem originalNumericallyDeterminedOn_of_isRealizationAny
    (E : ClosedProjectiveEmbedding f)
    (alg : ∀ π : Book, BookModelAlgebraization (f := f) (d := m + 1) π)
    {push : ∀ ⦃A B : M⦄, A ≤ B → N B →ₗ[ℝ] N A}
    {D : compatibleLinearFamilies (R := ℝ) push}
    {C : WeilFamilyAny (ModelSystem.blowup (m + 1) (SchemeComplexPoint f))}
    (coords : ∀ τ : Book, C.val τ = (bookModelNumericalChern alg τ (D.val (alg τ).A)).val)
    (pullTrans : ∀ ⦃A B C : M⦄ (h : A ≤ B) (k : B ≤ C) (v : N A),
      smoothModelNumericalCartierPullback (h.trans k) v =
        smoothModelNumericalCartierPullback k (smoothModelNumericalCartierPullback h v))
    (pushPull : ∀ ⦃B C : M⦄ (h : B ≤ C) (v : N B),
      push h (smoothModelNumericalCartierPullback h v) = v)
    (π : Book) (v : N (alg π).A)
    (hC : IsRealizationAny C π (bookModelNumericalChern alg π v).val) :
    IsOriginalNumericallyDeterminedOn D (alg π).A v := by
  apply (isOriginalNumericallyDeterminedOn_iff_cofinal E alg pullTrans pushPull D π v).2
  intro τ h
  apply (bookModelNumericalChern alg τ).injective
  apply Subtype.ext
  rw [← coords τ, bookModelNumericalChern_pullback_square E alg h v]
  exact hC τ h

section Canonical

variable [ConnectedSpace (SchemeComplexPoint f)]
local notation "chosen" => chooseBookModelAlgebraization (f := f) (d := m + 1)

/-- Ordinary algebraic determining-model data gives the book realization under
the canonical identification with actual algebraic cycle transitions. -/
theorem canonicalBookRealization_of_originalDetermination
    (E : ClosedProjectiveEmbedding f)
    (D : compatibleLinearFamilies (R := ℝ) (I := M) (E := N)
      (smoothModelOriginalCyclePushforward E)) (π : Book)
    (v : N (chosen E π).A)
    (hD : IsOriginalNumericallyDeterminedOn D (chosen E π).A v) :
    IsRealizationAny (canonicalOriginalNumericalWeilEquiv E D).val π
      (bookModelNumericalChern (chosen E) π v).val :=
  isRealizationAny_of_originalNumericallyDeterminedOn E (chosen E) (canonicalOriginalNumericalWeilEquiv_apply E D) π v hD

/-- The book realization on a chosen tower reads back ordinary Cartier data
on its algebraization and every higher smooth projective model. -/
theorem canonicalOriginalDetermination_of_bookRealization
    (E : ClosedProjectiveEmbedding f)
    (D : compatibleLinearFamilies (R := ℝ) (I := M) (E := N)
      (smoothModelOriginalCyclePushforward E)) (π : Book)
    (v : N (chosen E π).A)
    (hC : IsRealizationAny (canonicalOriginalNumericalWeilEquiv E D).val π
      (bookModelNumericalChern (chosen E) π v).val) :
    IsOriginalNumericallyDeterminedOn D (chosen E π).A v := by
  apply originalNumericallyDeterminedOn_of_isRealizationAny E (chosen E) (canonicalOriginalNumericalWeilEquiv_apply E D)
  · exact fun {A B C} h k v =>
      smoothModelNumericalCartierPullback_trans E (A := A) (B := B) (C := C) h k v
  · intro A B h v
    rw [smoothModelOriginalCyclePushforward_eq_transport E h]
    exact smoothModelTransportedAnalyticPushforward_numericalCartierPullback E h v
  · exact hC

/-- Existence of an ordinary determining algebraic model and existence of a book
Cartier realization are equivalent for the same Weil family. -/
theorem canonicalCartierExistence_iff
    (E : ClosedProjectiveEmbedding f)
    (D : compatibleLinearFamilies (R := ℝ) (I := M) (E := N)
      (smoothModelOriginalCyclePushforward E)) :
    (∃ A : M, ∃ v : N A, IsOriginalNumericallyDeterminedOn D A v) ↔
      ∃ π : Book, ∃ c : DFAlg.neronSeveri (m + 1) π.1.carrier,
        IsRealizationAny (canonicalOriginalNumericalWeilEquiv E D).val π c.val := by
  constructor
  · rintro ⟨A, v, hD⟩
    obtain ⟨π, h⟩ := bookModelAlgebraization_cofinal E (chosen E) A
    let w := smoothModelNumericalCartierPullback h v
    exact ⟨π, bookModelNumericalChern (chosen E) π w,
      canonicalBookRealization_of_originalDetermination E D π w
        (IsOriginalNumericallyDeterminedOn.of_le E hD h)⟩
  · rintro ⟨π, c, hC⟩
    let v := (bookModelNumericalChern (chosen E) π).symm c
    have hv : bookModelNumericalChern (chosen E) π v = c :=
      (bookModelNumericalChern (chosen E) π).apply_symm_apply c
    refine ⟨(chosen E π).A, v, canonicalOriginalDetermination_of_bookRealization E D π v ?_⟩
    rw [hv]
    exact hC

end Canonical

end SGPT.BDivisor.BD7
