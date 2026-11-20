import SGPT.BDivisor.BD7NumericalInverseLimit
import SGPT.BDivisor.BD7DecreasingAlgebraicApproximation
import SGPT.BDivisor.BDDangFavreCartier

/-! Decreasing algebraic numerical approximants and their modelwise majorants. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.BDivisor.BD7

open Filter Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open SGPT.BDivisor.DFAlg SGPT.Hodge.BDivChain.NativeDraft
open SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft

private theorem reflect_primeClosure_of_injective
    {P Q V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (p : P → V) (q : Q → W) (L : V →ₗ[ℝ] W)
    (hinj : Function.Injective L) (hprime : ∀ b, ∃ a, L (p a) = q b) {a : V}
    (ha : L a ∈ @closure _ (euclideanTopology W) (finiteEffectiveCone q)) :
    a ∈ @closure _ (euclideanTopology V) (finiteEffectiveCone p) := by
  obtain ⟨R, hR⟩ := L.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hleft (v : V) : R (L v) = v := LinearMap.congr_fun hR v
  rw [← hleft a]
  exact mapsTo_effectiveClosure_of_push_primes q p R (fun b => by
    obtain ⟨c, hc⟩ := hprime b
    exact Or.inr ⟨c, 1, zero_le_one, by rw [one_smul, ← hc, hleft]⟩) ha

private theorem majorant_of_decreasing_effective
    {P V : Type*} [AddCommGroup V] [Module ℝ V] (p : P → V)
    (u : ℕ → V) (v : V)
    (hd : ∀ i j, i ≤ j → u i - u j ∈ @closure _ (euclideanTopology V) (finiteEffectiveCone p))
    (hc : Tendsto u atTop (@nhds _ (euclideanTopology V) v)) (i : ℕ) :
    u i - v ∈ @closure _ (euclideanTopology V) (finiteEffectiveCone p) := by
  letI := euclideanTopology V
  have hdiff : Tendsto (fun j => u i - u j) atTop (𝓝 (u i - v)) := by
    apply tendsto_euclideanTopology_iff.mpr
    intro φ
    simpa only [map_sub] using
      (tendsto_const_nhds (x := φ (u i))).sub ((tendsto_euclideanTopology_iff.mp hc) φ)
  exact isClosed_closure.mem_of_tendsto hdiff
    ((eventually_ge_atTop i).mono (fun j hj => hd i j hj))

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ}

local instance inverseApproxPointTopology {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance inverseApproxPointCharts {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n
local instance inverseApproxPointManifold {S : Scheme.{0}} (g : S ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n

variable [IsIntegral X] [SmoothOfRelativeDimension (m + 1) f]
  [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
  [ConnectedSpace (SchemeComplexPoint f)]
  (E : ClosedProjectiveEmbedding f)

local notation "Book" => BookBlowupModel (f := f) (d := m + 1)
local notation "Model" => SmoothAlgebraicModel f (m + 1)
local notation "N" => SmoothModelNumericalClasses (f := f) (d := m + 1)
local notation "Sys" => ModelSystem.blowup (m + 1) (SchemeComplexPoint f)

variable (alg : ∀ π : (BookBlowupModel (f := f) (d := m + 1)), BookModelAlgebraization π)
  (push : ∀ ⦃A B : (SmoothAlgebraicModel f (m + 1))⦄, A ≤ B → SmoothModelNumericalClasses (f := f) (d := m + 1) B →ₗ[ℝ] SmoothModelNumericalClasses (f := f) (d := m + 1) A)
  (hpush : ∀ ⦃A B : (SmoothAlgebraicModel f (m + 1))⦄ (h : A ≤ B), push h = smoothModelTransportedAnalyticPushforward E h)
  (prime : ∀ A : (SmoothAlgebraicModel f (m + 1)), {x : A.V // Order.coheight x = 1} → SmoothModelNumericalClasses (f := f) (d := m + 1) A)
  (hChow : ∀ (π : (BookBlowupModel (f := f) (d := m + 1))) (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.1.carrier),
    ∃ x : {x : (alg π).A.V // Order.coheight x = 1},
      bookModelNumericalChern alg π (prime (alg π).A x) = primeCycleClassNS P)
  (hcycle : ∀ ⦃A B : (SmoothAlgebraicModel f (m + 1))⦄ (h : A ≤ B) P, push h (prime B P) =
    algebraicPrimeImageClass (A.p ≫ f) A.embedding (A.homOfLE h) (prime A) P)

private theorem originalPrimePush_nonnegative {A B : Model} (h : A ≤ B)
    (P : {x : B.V // Order.coheight x = 1})
    (hr : push h (prime B P) =
      algebraicPrimeImageClass (A.p ≫ f) A.embedding (A.homOfLE h) (prime A) P) :
    push h (prime B P) = 0 ∨ ∃ Q : {x : A.V // Order.coheight x = 1},
      ∃ c : ℝ, 0 ≤ c ∧ push h (prime B P) = c • prime A Q := by
  rw [hr, algebraicPrimeImageClass]
  split
  next hQ => exact Or.inr ⟨⟨A.homOfLE h P.val, hQ⟩, _, Nat.cast_nonneg _, rfl⟩
  next => exact Or.inl rfl

include hChow hcycle

/-- Lift the actual effective Chern sequence to the numerical projective limit.
Antitonicity and majorant inequalities are asserted on every original algebraic model.
The Cartier and nef conclusion is stated for the image under the same Chern equivalence. -/
theorem exists_inverseLimit_effectively_decreasing
    (a : compatibleLinearFamilies (R := ℝ) (I := Model) (E := N) push)
    {F : ℕ → WeilFamilyAny Sys}
    (hCartier : ∀ i, IsAlgNefCartierAny (F i))
    (hEff : ∀ i j, i ≤ j → ∀ π : Book, (F i).val π - (F j).val π ∈ effectiveClosure)
    (hConv : ConvergesAny atTop F (originalNumericalAlgebraicWeilEquiv E alg push hpush a).val) :
    let chern := originalNumericalAlgebraicWeilEquiv E alg push hpush
    ∃ u : ℕ → compatibleLinearFamilies (R := ℝ) (I := Model) (E := N) push,
      (∀ i, (chern (u i)).val = F i) ∧
      (∀ i, IsAlgNefCartierAny (chern (u i)).val) ∧
      (∀ i j, i ≤ j → ∀ A, (u i).val A - (u j).val A ∈
        @closure _ (euclideanTopology (N A)) (finiteEffectiveCone (prime A))) ∧
      (∀ A, Tendsto (fun i => (u i).val A) atTop (@nhds _ (euclideanTopology (N A)) (a.val A))) ∧
      (∀ i A, (u i).val A - a.val A ∈
        @closure _ (euclideanTopology (N A)) (finiteEffectiveCone (prime A))) := by
  classical
  let chern := originalNumericalAlgebraicWeilEquiv E alg push hpush
  let Fs (i : ℕ) : algebraicWeilFamilies m (SchemeComplexPoint f) :=
    ⟨F i, (hCartier i).isAlgebraicAny⟩
  let u (i : ℕ) := chern.symm (Fs i)
  have he (i : ℕ) : chern (u i) = Fs i := chern.apply_symm_apply _
  have hco (i : ℕ) (π : Book) :
      (bookModelNumericalChern alg π ((u i).val (alg π).A)).val = (F i).val π :=
    congrArg (fun w : algebraicWeilFamilies m (SchemeComplexPoint f) => w.val.val π) (he i)
  have hD : ∀ i j, i ≤ j → ∀ A, (u i).val A - (u j).val A ∈
      @closure _ (euclideanTopology (N A)) (finiteEffectiveCone (prime A)) := by
    intro i j hij A
    obtain ⟨π, hA⟩ := bookModelAlgebraization_cofinal E alg A
    let L : N (alg π).A →ₗ[ℝ] RealBottChern (m + 1) π.1.carrier :=
      (neronSeveri (m + 1) π.1.carrier).subtype.comp (bookModelNumericalChern alg π).toLinearMap
    have hpr (P : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.1.carrier) :
        ∃ x, L (prime (alg π).A x) = cycleClass (SGPT.Siu.primeEffectiveDivisor P) := by
      obtain ⟨x, hx⟩ := hChow π P
      exact ⟨x, congrArg Subtype.val hx⟩
    have hd : L ((u i).val (alg π).A - (u j).val (alg π).A) ∈ effectiveClosure := by
      rw [map_sub]
      change (bookModelNumericalChern alg π ((u i).val (alg π).A)).val -
        (bookModelNumericalChern alg π ((u j).val (alg π).A)).val ∈ effectiveClosure
      rw [hco i π, hco j π]
      exact hEff i j hij π
    have hh := reflect_primeClosure_of_injective (prime (alg π).A) _ L
      (Subtype.val_injective.comp (bookModelNumericalChern alg π).injective) hpr hd
    have hL := mapsTo_effectiveClosure_of_push_primes (prime (alg π).A) (prime A) (push hA)
      (fun P => originalPrimePush_nonnegative push prime hA P (hcycle hA P))
    have hs := hL hh
    rw [map_sub, (u i).property A (alg π).A hA, (u j).property A (alg π).A hA] at hs
    exact hs
  have hC := (originalNumericalAlgebraicWeilEquiv_tendsto E alg push hpush u a atTop).mpr (by
    intro π
    exact (hConv π).congr' (Eventually.of_forall fun i =>
      (congrArg (fun w : algebraicWeilFamilies m (SchemeComplexPoint f) => w.val.val π)
        (he i)).symm))
  refine ⟨u, fun i => congrArg Subtype.val (he i), fun i => ?_, hD, hC, ?_⟩
  · rw [he]
    exact hCartier i
  · intro i A
    exact majorant_of_decreasing_effective (prime A) (fun j => (u j).val A) (a.val A)
      (fun j k hjk => hD j k hjk A) (hC A) i

end SGPT.BDivisor.BD7
