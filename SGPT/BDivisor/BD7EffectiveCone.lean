import SGPT.BDivisor.BD2DangFavreNef
import SGPT.Hodge.ConePositive
import SGPT.Okounkov.TranscendentalVolumeConcavityMinkowski
import SGPT.Siu.SiuDecompositionLelong

/-! Effective prime cones, their Euclidean closures, and the book's modelwise order. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD7

open Set AlgebraicGeometry
open scoped BigOperators Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open FirstPass.PositiveClasses FirstPass.HolomorphicIdealSheaves
open CurrentBottChernClass CanonicalCurrentFrame
open SGPT.BDivisor.DFAlg
open SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
open SGPT.Okounkov.TranscendentalVolumeConcavity

/-- The finite nonnegative combinations of the given prime cycle classes. -/
def finiteEffectiveCone {P V : Type*} [AddCommGroup V] [Module ℝ V]
    (prime : P → V) : Set V :=
  {x | ∃ (s : Finset P) (c : P → ℝ), (∀ p ∈ s, 0 ≤ c p) ∧
    x = ∑ p ∈ s, c p • prime p}

private theorem mapsTo_finiteEffectiveCone
    {P Q V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (e : P ≃ Q) (L : V →ₗ[ℝ] W) (p : P → V) (q : Q → W)
    (h : ∀ a, L (p a) = q (e a)) :
    MapsTo L (finiteEffectiveCone p) (finiteEffectiveCone q) := by
  classical
  rintro _ ⟨s, c, hc, rfl⟩
  refine ⟨s.map e.toEmbedding, c ∘ e.symm, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    simpa only [Function.comp_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hc a ha
  · rw [map_sum, Finset.sum_map]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_smul, h, Function.comp_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

private theorem continuous_linear_euclidean
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W) :
    Continuous[euclideanTopology V, euclideanTopology W] L := by
  letI := euclideanTopology V
  letI := euclideanTopology W
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_euclideanTopology_iff.mpr
  intro φ
  exact (continuous_euclideanTopology (φ.comp L)).continuousAt

section Model

variable {m : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] [CompactSpace Y]
local notation "PAn" => SGPT.PSH.GeometricPrimeCarrier (m + 1) Y
local notation "BC" => RealBottChern (m + 1) Y
local notation "NS" => neronSeveri (m + 1) Y

/-- The analytic prime cycle class lies in the book's actual positive-current cone. -/
private theorem primeCycleClass_pseudoeffective (P : PAn) :
    ClassPseudoeffectiveViaPotentials (cycleClass (SGPT.Siu.primeEffectiveDivisor P)) := by
  obtain ⟨E, _, hE⟩ := DivisorMetric.exists_divisorMetric (SGPT.Siu.primeEffectiveDivisor P)
  rw [cycleClass_eq_of_isDivisorMetric _ E hE, classPseudoeffectiveViaPotentials_ofRepresentative]
  exact ⟨E.weight, SGPT.Okounkov.isThetaPshPotential_effectiveDivisorMetric _ E hE⟩

/-- The book's closed positive-current cone contains the Euclidean closure of effective classes. -/
theorem analyticPseudoeffective_of_mem_effectiveClosure [ConnectedSpace Y]
    (κ : KahlerBackground (m + 1) Y) {α : BC}
    (hα : α ∈ @closure _ (euclideanTopology BC)
      (finiteEffectiveCone (fun P : PAn => cycleClass (SGPT.Siu.primeEffectiveDivisor P)))) :
    ClassPseudoeffectiveViaPotentials α := by
  classical
  letI := euclideanTopology BC
  apply closure_minimal _ (SGPT.Hodge.isClosed_setOf_classPseudoeffective κ) hα
  rintro _ ⟨s, c, hc, rfl⟩
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    refine (PseudoeffectiveOriginalCurrentEquivalence.classPseudoeffectiveViaPotentials_iff_exists_original_current
      (0 : BC)).mpr ⟨0, SGPT.Siu.isFullPositive_zero, ?_⟩
    exact (bottChernClassLinearMap (M := Y) (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_zero
  | @insert P s hPs ih =>
    rw [Finset.sum_insert hPs]
    exact classPseudoeffective_add
      (classPseudoeffective_smul (primeCycleClass_pseudoeffective P) (hc P (Finset.mem_insert_self _ _)))
      (ih (fun Q hQ => hc Q (Finset.mem_insert_of_mem hQ)))

/-- The native Néron–Severi class of a prime cycle. -/
def primeCycleClassNS (P : PAn) : NS :=
  ⟨cycleClass (SGPT.Siu.primeEffectiveDivisor P), cycleClass_mem_neronSeveri _⟩

section Numerical

variable [ConnectedSpace Y]

/-- The algebraic and analytic effective cones, and their Euclidean closures in the modelwise
Néron–Severi space, agree under the numerical cycle-class equivalence when scheme primes and
analytic primes correspond with their actual Chern classes. -/
theorem numericalClassEquiv_effective_cones
    {V : Scheme.{0}} (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y)
    (prime : {x : V // Order.coheight x = 1} → NumericalClasses m Y)
    (corr : {x : V // Order.coheight x = 1} ≃ PAn)
    (hprime : ∀ P, numericalClassEquiv hY (prime P) = primeCycleClassNS (corr P)) :
    (numericalClassEquiv hY '' finiteEffectiveCone prime = finiteEffectiveCone primeCycleClassNS) ∧
    (numericalClassEquiv hY '' (@closure _ (euclideanTopology (NumericalClasses m Y))
      (finiteEffectiveCone prime)) =
      @closure _ (euclideanTopology NS) (finiteEffectiveCone primeCycleClassNS)) := by
  let e := numericalClassEquiv hY
  have heff : e '' finiteEffectiveCone prime = finiteEffectiveCone primeCycleClassNS := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact mapsTo_finiteEffectiveCone corr e.toLinearMap prime primeCycleClassNS hprime ha
    · have hback : ∀ P, e.symm (primeCycleClassNS P) = prime (corr.symm P) := by
        intro P
        apply e.injective
        simpa only [LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply] using (hprime (corr.symm P)).symm
      intro b hb
      exact ⟨e.symm b, mapsTo_finiteEffectiveCone corr.symm e.symm.toLinearMap
        primeCycleClassNS prime hback hb, e.apply_symm_apply b⟩
  letI := euclideanTopology (NumericalClasses m Y)
  letI := euclideanTopology NS
  let h : NumericalClasses m Y ≃ₜ NS :=
    { e.toEquiv with
      continuous_toFun := continuous_linear_euclidean e.toLinearMap
      continuous_invFun := continuous_linear_euclidean e.symm.toLinearMap }
  have heff' : h '' finiteEffectiveCone prime = finiteEffectiveCone primeCycleClassNS := heff
  refine ⟨heff, ?_⟩
  change h '' closure (finiteEffectiveCone prime) = closure (finiteEffectiveCone primeCycleClassNS)
  rw [h.image_closure, heff']

/-- The algebraic effective-closure condition implies the analytic effective-closure condition
on the actual Bott–Chern class. -/
theorem numericalClassEquiv_mem_analyticEffectiveClosure
    {V : Scheme.{0}} (hY : SGPT.Trace.Bertini.IsProjectiveManifold (m + 1) Y)
    (prime : {x : V // Order.coheight x = 1} → NumericalClasses m Y)
    (corr : {x : V // Order.coheight x = 1} ≃ PAn)
    (hprime : ∀ P, numericalClassEquiv hY (prime P) = primeCycleClassNS (corr P))
    {a : NumericalClasses m Y}
    (ha : a ∈ @closure _ (euclideanTopology (NumericalClasses m Y)) (finiteEffectiveCone prime)) :
    (numericalClassEquiv hY a : BC) ∈ @closure _ (euclideanTopology BC)
      (finiteEffectiveCone (fun P : PAn => cycleClass (SGPT.Siu.primeEffectiveDivisor P))) := by
  letI := euclideanTopology NS
  letI := euclideanTopology BC
  let incl : NS →ₗ[ℝ] BC := (neronSeveri (m + 1) Y).subtype
  have hα : numericalClassEquiv hY a ∈ closure (finiteEffectiveCone primeCycleClassNS) := by
    rw [← (numericalClassEquiv_effective_cones hY prime corr hprime).2]
    exact ⟨a, ha, rfl⟩
  have hmaps : incl '' finiteEffectiveCone primeCycleClassNS ⊆
      finiteEffectiveCone (fun P : PAn => cycleClass (SGPT.Siu.primeEffectiveDivisor P)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact mapsTo_finiteEffectiveCone (Equiv.refl PAn) incl primeCycleClassNS
      (fun P => cycleClass (SGPT.Siu.primeEffectiveDivisor P)) (fun _ => rfl) hb
  exact closure_mono hmaps
    (image_closure_subset_closure_image (continuous_linear_euclidean incl)
      ⟨numericalClassEquiv hY a, hα, rfl⟩)

end Numerical
end Model

section Order

attribute [local instance] blowup_model_connectedSpace

variable {m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]

/-- The algebraic effective-closure tests on the incarnations of a difference imply the book's
order test. This is the order input for decreasing nef Cartier approximation. -/
theorem leAny_of_modelwise_effectiveClosure
    (D E : WeilFamilyAny (ModelSystem.blowup (m + 1) X))
    (κ : ∀ π : (ModelSystem.blowup (m + 1) X).Model, KahlerBackground (m + 1) π.1.carrier)
    (h : ∀ π, E.val π - D.val π ∈
      @closure _ (euclideanTopology (RealBottChern (m + 1) π.1.carrier))
        (finiteEffectiveCone fun P : SGPT.PSH.GeometricPrimeCarrier (m + 1) π.1.carrier =>
          cycleClass (SGPT.Siu.primeEffectiveDivisor P))) :
    LEAny D E :=
  fun π => analyticPseudoeffective_of_mem_effectiveClosure (κ π) (h π)

end Order

end SGPT.BDivisor.BD7
