import SGPT.BDivisor.BD7CanonicalNumericalInverseLimit
import SGPT.BDivisor.BD7InverseLimitApproximation
import SGPT.PSH.BiholomorphicGeometricQPreimage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Okounkov SGPT.Okounkov.OF13 SGPT.Projective.BDivNov16
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy CanonicalCurrentFrame
open SGPT.BDivisor.DFAlg SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open scoped Topology Manifold ContDiff

section PrimeTransport

variable {m : ℕ} {U Y : Type} [TopologicalSpace U] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel (m + 1)) U] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) U] [IsComplexManifold (m + 1) Y]
    [CompactSpace U] [CompactSpace Y]

/-- The pushforward of the geometric preimage prime is the same prime, with coefficient one. -/
theorem neronSeveriDiffeoEquiv_primePreimage
    (e : U ≃ₘ⟮𝓘(ℂ, ComplexModel (m + 1)), 𝓘(ℂ, ComplexModel (m + 1))⟯ Y)
    (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) Y) :
    neronSeveriDiffeoEquiv e
        (primeCycleClassNS (SGPT.PSH.biholomorphic_geometricPrimeCarrier_preimage
          e.toHomeomorph e.contMDiff e.symm.contMDiff P)) = primeCycleClassNS P := by
  let R := SGPT.PSH.biholomorphic_geometricPrimeCarrier_preimage
    e.toHomeomorph e.contMDiff e.symm.contMDiff P
  let he := isAnalyticModification_of_diffeomorph e
  have hR : ¬ R.val ⊆ exceptionalLocus (m + 1) e := by
    rw [exceptionalLocus_diffeomorph]
    obtain ⟨x, hx⟩ := R.nonempty
    exact fun h => h hx
  have hRP : primeImage he R hR = P := by
    apply SGPT.PSH.GeometricPrimeCarrier.ext
    rw [primeImage_val]
    change e '' (e ⁻¹' P.val) = P.val
    exact e.surjective.image_preimage P.val
  have hclass := classPushforward_cycleClass_prime he R
  rw [primePushforward, dif_neg hR, divisorClass_single, one_smul, hRP] at hclass
  exact Subtype.ext hclass

end PrimeTransport

variable {Z : Scheme.{0}} {f : Z ⟶ Spec (.of ℂ)} {m : ℕ}

local instance canonicalApproxPointTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance canonicalApproxPointCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] : ChartedSpace (ComplexModel d) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g d
local instance canonicalApproxPointManifold {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold d (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g d

variable [IsIntegral Z] [SmoothOfRelativeDimension (m + 1) f]
  [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
  (E : ClosedProjectiveEmbedding f)

local notation "Model" => SmoothAlgebraicModel f (m + 1)
local notation "Book" => BookBlowupModel (f := f) (d := m + 1)
local notation "N" => SmoothModelNumericalClasses (f := f) (d := m + 1)
local notation "Alg" => fun π : Book => chooseBookModelAlgebraization E π

/-- Chow's same-prime endpoint on the actual scheme incarnation, transported to the book model. -/
theorem bookModelNumericalChern_surj_on_primes (alg : ∀ π : Book, BookModelAlgebraization π)
    (π : Book) (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.1.carrier) :
    ∃ x : {x : (alg π).A.V // Order.coheight x = 1},
      bookModelNumericalChern alg π (smoothModelOriginalPrimeNumerical (alg π).A x) =
        primeCycleClassNS P := by
  let A := (alg π).A
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI : CompactSpace (SchemeComplexPoint (A.p ≫ f)) :=
    (alg π).e.symm.toHomeomorph.compactSpace
  letI : ConnectedSpace (SchemeComplexPoint (A.p ≫ f)) :=
    smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  let R := SGPT.PSH.biholomorphic_geometricPrimeCarrier_preimage (alg π).e.toHomeomorph
    (alg π).e.contMDiff (alg π).e.symm.contMDiff P
  obtain ⟨z, _, _, hz, _, htrace, _⟩ :=
    exists_originalCartierCodimOnePrime_cycleClass (A.p ≫ f) m A.embedding R
  let x : {x : A.V // Order.coheight x = 1} := ⟨z, hz⟩
  have hx : nativePrimeOfOriginalPoint (A.p ≫ f) A.embedding (m := m) x = R :=
    SGPT.PSH.GeometricPrimeCarrier.ext
      ((nativePrimeOfOriginalPoint_val (A.p ≫ f) A.embedding (m := m) x).trans htrace.symm)
  have hc : integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m normalizationProjectiveForCurves_bd7
        (smoothModelOriginalPrimeNumerical A x) = primeCycleClassNS R := by
    apply Subtype.ext
    exact (numericalChern_originalPrimeNumerical (A.p ≫ f) A.embedding
      normalizationProjectiveForCurves_bd7 x).trans
      (congrArg (fun Q => cycleClass (SGPT.Siu.primeEffectiveDivisor Q)) hx)
  refine ⟨x, ?_⟩
  change neronSeveriDiffeoEquiv (alg π).e
    (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m normalizationProjectiveForCurves_bd7
      (smoothModelOriginalPrimeNumerical A x)) = _
  rw [hc]
  exact neronSeveriDiffeoEquiv_primePreimage (alg π).e P

variable [ConnectedSpace (SchemeComplexPoint f)]

local notation "CPush" => smoothModelOriginalCyclePushforward E
local notation "CE" => canonicalOriginalNumericalWeilEquiv E
local notation "Sys" => ModelSystem.blowup (m + 1) (SchemeComplexPoint f)

/-- The canonical algebraic approximants decrease and dominate on every original smooth model. -/
theorem exists_canonicalInverseLimit_approximation (a : compatibleLinearFamilies (R := ℝ) (I := Model) (E := N) CPush)
    {F : ℕ → WeilFamilyAny Sys}
    (hCartier : ∀ i, IsAlgNefCartierAny (F i))
    (hEff : ∀ i j, i ≤ j → ∀ π : Book, (F i).val π - (F j).val π ∈ effectiveClosure)
    (hConv : ConvergesAny atTop F (CE a).val) :
    ∃ u : ℕ → compatibleLinearFamilies (R := ℝ) (I := Model) (E := N) CPush,
      (∀ i, (CE (u i)).val = F i) ∧
      (∀ i, IsAlgNefCartierAny (CE (u i)).val) ∧
      (∀ i j, i ≤ j → ∀ A, (u i).val A - (u j).val A ∈
        @closure _ (euclideanTopology (N A)) (finiteEffectiveCone (smoothModelOriginalPrimeNumerical A))) ∧
      (∀ A, Tendsto (fun i => (u i).val A) atTop (@nhds _ (euclideanTopology (N A)) (a.val A))) ∧
      (∀ i A, (u i).val A - a.val A ∈
        @closure _ (euclideanTopology (N A)) (finiteEffectiveCone (smoothModelOriginalPrimeNumerical A))) := by
  have hpush ⦃A B : Model⦄ (h : A ≤ B) := smoothModelOriginalCyclePushforward_eq_transport E h
  have hcycle ⦃A B : Model⦄ (h : A ≤ B) (P : {x : B.V // Order.coheight x = 1}) :
      CPush h (smoothModelOriginalPrimeNumerical B P) =
        algebraicPrimeImageClass (A.p ≫ f) A.embedding (A.homOfLE h)
          (smoothModelOriginalPrimeNumerical A) P := by
    rw [hpush]
    exact smoothModelTransportedAnalyticPushforward_originalPrime E h P
  exact exists_inverseLimit_effectively_decreasing E Alg CPush (fun {A B} h => hpush (A := A) (B := B) h)
    smoothModelOriginalPrimeNumerical (bookModelNumericalChern_surj_on_primes Alg)
    (fun {A B} h P => hcycle (A := A) (B := B) h P)
    a hCartier hEff hConv


/-- The forward prime direction for order of arbitrary algebraic majorants. -/
theorem bookModelNumericalChern_maps_prime (alg : ∀ π : Book, BookModelAlgebraization π)
    (π : Book) (x : {x : (alg π).A.V // Order.coheight x = 1}) :
    ∃ P : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.1.carrier,
      bookModelNumericalChern alg π (smoothModelOriginalPrimeNumerical (alg π).A x) =
        primeCycleClassNS P := by
  let A := (alg π).A
  letI := A.embedding.isSeparated
  letI := A.embedding.quasiCompact
  letI : CompactSpace (SchemeComplexPoint (A.p ≫ f)) :=
    (alg π).e.symm.toHomeomorph.compactSpace
  letI : ConnectedSpace (SchemeComplexPoint (A.p ≫ f)) :=
    smoothProjectiveNativeConnected (A.p ≫ f) (m + 1) A.embedding
  let R := nativePrimeOfOriginalPoint (A.p ≫ f) A.embedding (m := m) x
  let K := SGPT.PSH.biholomorphic_geometricPrimeCarrier_equiv (alg π).e.toHomeomorph
    (alg π).e.contMDiff (alg π).e.symm.contMDiff
  let P := K.symm R
  refine ⟨P, ?_⟩
  change neronSeveriDiffeoEquiv (alg π).e
    (integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m normalizationProjectiveForCurves_bd7
      (smoothModelOriginalPrimeNumerical A x)) = _
  have hR : integralNumericalEquivNS_bd7 (A.p ≫ f) A.embedding m normalizationProjectiveForCurves_bd7
      (smoothModelOriginalPrimeNumerical A x) = primeCycleClassNS R :=
    Subtype.ext (numericalChern_originalPrimeNumerical (A.p ≫ f) A.embedding
      normalizationProjectiveForCurves_bd7 x)
  rw [hR, ← K.apply_symm_apply R]
  exact neronSeveriDiffeoEquiv_primePreimage (alg π).e P

open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-- An ordinary algebraic majorant is a majorant for the book's order under the canonical Chern map. -/
theorem canonicalOriginalNumericalWeilEquiv_le_of_majorant
    (κ : ∀ π : Book, KahlerBackground (m + 1) π.1.carrier)
    (a b : compatibleLinearFamilies (R := ℝ) (I := Model) (E := N) CPush)
    (hab : ∀ A, b.val A - a.val A ∈
      @closure _ (euclideanTopology (N A)) (finiteEffectiveCone (smoothModelOriginalPrimeNumerical A))) :
    LEAny (CE a).val (CE b).val := by
  apply leAny_of_modelwise_effectiveClosure _ _ κ
  intro π
  let A := (Alg π).A
  let L : N A →ₗ[ℝ] RealBottChern (m + 1) π.1.carrier :=
    (neronSeveri (m + 1) π.1.carrier).subtype.comp (bookModelNumericalChern Alg π).toLinearMap
  have h := mapsTo_effectiveClosure_of_push_primes (smoothModelOriginalPrimeNumerical A)
    (fun P : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.1.carrier =>
      cycleClass (SGPT.Siu.primeEffectiveDivisor P)) L (fun x => by
        obtain ⟨P, hP⟩ := bookModelNumericalChern_maps_prime Alg π x
        exact Or.inr ⟨P, 1, zero_le_one, by
          rw [one_smul]
          exact congrArg Subtype.val hP⟩) (hab A)
  rw [map_sub] at h
  exact h

end SGPT.BDivisor.BD7
