import SGPT.Okounkov.SchemeNativeFormalGerm
import SGPT.NAPotential.GAGAMult2Faithful
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Smooth complex schemes are normal; their codimension-one local rings are DVRs


The order comparison along a prime divisor of a smooth complex scheme `X` needs the local ring
`𝒪_{X,z}` of a point `z` of codimension one to be a discrete valuation ring.  Mathlib does not
know that smooth schemes are normal; here this is derived from the analytic theory:

* `isIntegrallyClosed_of_faithfullyFlat`: **faithfully flat descent of normality** — if
  `φ : R → S` is a faithfully flat map of domains and `S` is integrally closed, so is `R`
  (`a/b` integral over `R` lies in `S`, so `a ∈ bS ∩ R = bR`);
* `isIntegrallyClosed_stalk_complexPoint`: at a complex point `p`, `𝒪_{X,p} → 𝒪^an_{X,p}` is
  faithfully flat (`SGPT.Okounkov.schemeNativeStalkGerm_faithfullyFlat`) and the ring of
  holomorphic germs is factorial (TN), hence `𝒪_{X,p}` is integrally closed;
* `isIntegrallyClosed_sections`, `isIntegrallyClosed_stalk`: the ring of every nonempty affine
  open is integrally closed (its maximal ideals are complex points, Nullstellensatz), hence so
  is every local ring `𝒪_{X,x}` (a localization);
* `isDiscreteValuationRing_stalk`: if `Order.coheight z = 1`, `𝒪_{X,z}` is a discrete valuation
  ring.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes2

open AlgebraicGeometry CategoryTheory Topology IsLocalRing
open SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.NAPotential.Berkovich

/-- **Faithfully flat descent of integral closedness.**  If `φ : R → S` is a faithfully flat
ring map of domains and `S` is integrally closed, then `R` is integrally closed. -/
theorem isIntegrallyClosed_of_faithfullyFlat {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [IsIntegrallyClosed S] (φ : R →+* S) (hφ : φ.FaithfullyFlat) :
    IsIntegrallyClosed R := by
  have hinj : Function.Injective φ := hφ.injective
  let K := FractionRing R
  let L := FractionRing S
  have hg : Function.Injective ((algebraMap S L).comp φ) :=
    (IsFractionRing.injective S L).comp hinj
  let ψ : K →+* L := IsFractionRing.lift hg
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hψ : ∀ r : R, ψ (algebraMap R K r) = algebraMap S L (φ r) := fun r =>
    IsFractionRing.lift_algebraMap hg r
  have hint : IsIntegral S (ψ (algebraMap R K a / algebraMap R K b)) :=
    IsIntegral.map_of_comp_eq φ ψ (by ext r; exact (hψ r).symm) hx
  obtain ⟨σ, hσ⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hbS : algebraMap S L (φ b) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective S L), map_eq_zero_iff _ hinj]
    exact hb0
  have hkey : φ a = φ b * σ := by
    apply IsFractionRing.injective S L
    rw [map_mul, hσ, map_div₀, hψ, hψ, mul_div_cancel₀ _ hbS]
  let := φ.toAlgebra
  let : Module.FaithfullyFlat R S := hφ
  have hmem : φ a ∈ (Ideal.span {b}).map φ := by
    rw [Ideal.map_span, Set.image_singleton, hkey]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have ha : a ∈ Ideal.span {b} := by
    have := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (Ideal.span {b})
    rw [← this]
    exact hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp ha
  refine ⟨r, ?_⟩
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  rw [eq_div_iff hbK, ← map_mul, mul_comm r b, ← hr, mul_comm]

/-- The ring of holomorphic germs `𝒪_{ℂⁿ,0}` is integrally closed (it is factorial). -/
theorem isIntegrallyClosed_holGerm (n : ℕ) : IsIntegrallyClosed (HolGerm (ComplexModel n)) := by
  let := ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

section Scheme

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f] [IsIntegral X]

local instance algPrimes2NormalPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algPrimes2NormalPointCharts :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance algPrimes2NormalPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

include n in
/-- **The local ring of a smooth complex scheme at a complex point is integrally closed**:
`𝒪_{X,p} → 𝒪^an_{X,p} ≅ 𝒪_{ℂⁿ,0}` is faithfully flat and `𝒪_{ℂⁿ,0}` is factorial. -/
theorem isIntegrallyClosed_stalk_complexPoint (p : SchemeComplexPoint f) :
    IsIntegrallyClosed (X.presheaf.stalk (schemeComplexPointImage f p)) := by
  have := isIntegrallyClosed_holGerm n
  have hff : ((NativeHolGerm.chartEquiv p).toRingHom.comp
      (schemeNativeStalkGerm f n p)).FaithfullyFlat :=
    RingHom.FaithfullyFlat.stableUnderComposition _ _ (schemeNativeStalkGerm_faithfullyFlat f n p)
      (RingHom.FaithfullyFlat.of_bijective (NativeHolGerm.chartEquiv (n := n) p).bijective)
  exact isIntegrallyClosed_of_faithfullyFlat _ hff

include f n in
/-- The ring of sections of a nonempty affine open of a smooth integral complex scheme is
integrally closed: its maximal ideals are complex points (Nullstellensatz), and normality is
local at the maximal ideals. -/
theorem isIntegrallyClosed_sections {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : LocallyOfFiniteType f := inferInstance
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP => ?_
  obtain ⟨p, hp⟩ := exists_schemeComplexPoint_fromSpec f hU P hP
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf
    ⟨hU.fromSpec ⟨P, hP.isPrime⟩, fromSpec_mem hU _⟩
  have hloc := hU.isLocalization_stalk' ⟨P, hP.isPrime⟩ (fromSpec_mem hU _)
  have hint : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) := by
    have h := isIntegrallyClosed_stalk_complexPoint f n p
    rw [hp] at h
    exact h
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩))
      (Localization.AtPrime P)).toRingEquiv

include f n in
/-- **Smooth integral complex schemes are normal**: every local ring `𝒪_{X,x}` is integrally
closed. -/
theorem isIntegrallyClosed_stalk (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have := isIntegrallyClosed_sections f n hU
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc := hU.isLocalization_stalk ⟨x, hxU⟩
  exact isIntegrallyClosed_of_isLocalization (R := Γ(X, U)) (S := X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

include f n in
/-- **The local ring of a smooth integral complex scheme at a point of codimension one is a
discrete valuation ring.** -/
theorem isDiscreteValuationRing_stalk [IsLocallyNoetherian X] {z : X}
    (hz : Order.coheight z = 1) : IsDiscreteValuationRing (X.presheaf.stalk z) := by
  have hdim : ringKrullDim (X.presheaf.stalk z) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hz]
    rfl
  have hnf : ¬IsField (X.presheaf.stalk z) := by
    intro hF
    rw [ringKrullDim_eq_zero_of_isField hF] at hdim
    exact absurd hdim (by decide)
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le (le_of_eq hz)
  have := isIntegrallyClosed_stalk f n z
  have hm : maximalIdeal (X.presheaf.stalk z) ≠ ⊥ :=
    isField_iff_maximalIdeal_eq.not.mp hnf
  have key := (IsDiscreteValuationRing.TFAE (X.presheaf.stalk z) hnf).out 0 3
  refine key.mpr ⟨inferInstance, maximalIdeal _, ⟨hm, inferInstance⟩, fun P hP => ?_⟩
  exact (IsLocalRing.eq_maximalIdeal (hP.2.isMaximal_of_ne_bot hP.1))

end Scheme

end SGPT.NAPotential.AlgPrimes2

end
