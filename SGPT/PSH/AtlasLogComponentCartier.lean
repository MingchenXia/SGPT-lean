import SGPT.PSH.AtlasLogComponentIdeals
import SGPT.PSH.CanonicalCartierAdditivity

/-! Genuine reduced Cartier restrictions of ORIGINAL primes on every actual
component, retaining the empty restriction and every original coefficient. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending HironakaEffectiveDivisorSum
open scoped Topology Manifold ContDiff Classical
universe u

section NativeAny
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The existing native reduced prime Cartier divisor in every admissible
dimension. The zero-dimensional prime branch is genuinely empty. -/
def nativePrimeCartierAny (Q : GeometricPrimeCarrier n M) : EffectiveDivisor n M := by
  cases n with
  | zero => exact isEmptyElim Q
  | succ m => exact geometricPrimeCarrierEffectiveDivisor Q

/-- The existing actual Cartier reader on every admissible genuine prime.
No scalar is assigned to a nonexistent zero-dimensional prime. -/
def nativeCartierCoefficientAny (H : EffectiveDivisor n M) (Q : GeometricPrimeCarrier n M) : ℕ := by
  cases n with
  | zero => exact isEmptyElim Q
  | succ m => exact cartierGeometricPrimeCoefficient H Q

lemma nativePrimeCartierAny_ideal (Q : GeometricPrimeCarrier n M) :
    (nativePrimeCartierAny Q).ideal=vanishingIdeal (n := n) Q.val := by
  cases n with
  | zero => exact isEmptyElim Q
  | succ m => exact geometricPrimeCarrierEffectiveDivisor_ideal Q

lemma nativeCartierCoefficientAny_reduced (P Q : GeometricPrimeCarrier n M) :
    nativeCartierCoefficientAny (nativePrimeCartierAny P) Q = if Q=P then 1 else 0 := by
  classical
  cases n with
  | zero => exact isEmptyElim Q
  | succ m => exact cartierGeometricPrimeCoefficient_reduced P Q

lemma nativeCartierCoefficientAny_zero (Q : GeometricPrimeCarrier n M) :
    nativeCartierCoefficientAny (0 : EffectiveDivisor n M) Q=0 := by
  cases n with
  | zero => exact isEmptyElim Q
  | succ m => exact cartierGeometricPrimeCoefficient_zero Q

omit [IsComplexManifold n M] in
private lemma empty_vanishing_ideal :
    vanishingIdeal (n := n) (∅ : Set M)=IdealWeightPowers.unitIdeal n M := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun h => h.1,fun h => ?_⟩)
  exact ⟨h,Eventually.of_forall fun _ hfalse => hfalse.elim⟩

end NativeAny

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- ORIGINAL P,x manufacture an actual Cartier divisor with the FULL reduced
ideal of the SAME restricted carrier and its EVERY native coefficient.
Empty component restrictions give the genuine zero Cartier divisor. -/
theorem exists_original_prime_component_cartier (P : AtlasGeometricPrimeCarrier A) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∃ H : EffectiveDivisor (A.pointDimension x) (A.componentOpen x),
      H.ideal=vanishingIdeal (n := A.pointDimension x)
        ((Subtype.val : A.componentOpen x → X) ⁻¹' P.val) ∧
      ∀ Q : GeometricPrimeCarrier (A.pointDimension x) (A.componentOpen x),
        nativeCartierCoefficientAny H Q=if A.nativePrimeOriginalCarrier x Q=P then 1 else 0 := by
  classical
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  rcases original_prime_component_cases P x with ⟨Q,hpre,himage⟩ | hempty
  · have hQ : A.nativePrimeOriginalCarrier x Q=P := AtlasGeometricPrimeCarrier.ext himage
    refine ⟨nativePrimeCartierAny Q,?_,?_⟩
    · rw [hpre]
      exact nativePrimeCartierAny_ideal Q
    · intro R
      rw [nativeCartierCoefficientAny_reduced]
      have hkey : R=Q ↔ A.nativePrimeOriginalCarrier x R=P := by
        constructor
        · rintro rfl
          exact hQ
        · intro hR
          exact (A.nativePrimeOriginalCarrier_injective x) (hR.trans hQ.symm)
      rw [hkey]
  · refine ⟨0,?_,?_⟩
    · rw [hempty,ideal_zero]
      exact empty_vanishing_ideal.symm
    · intro Q
      have hne : A.nativePrimeOriginalCarrier x Q≠P := by
        intro heq
        obtain ⟨q,hq⟩ := Q.nonempty
        have himage : Subtype.val '' Q.val=P.val := congrArg Subtype.val heq
        have hp : q∈(Subtype.val : A.componentOpen x → X) ⁻¹' P.val := by
          change q.val∈P.val
          rw [←himage]
          exact ⟨q,hq,rfl⟩
        rw [hempty] at hp
        exact hp
      rw [nativeCartierCoefficientAny_zero,if_neg hne]

/-- Select ONLY the Cartier divisor genuinely produced from original P,x;
no native divisor/ideal/order certificate is a caller input. -/
def componentPrimeCartier (P : AtlasGeometricPrimeCarrier A) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    EffectiveDivisor (A.pointDimension x) (A.componentOpen x) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  exact Classical.choose (exists_original_prime_component_cartier P x)

lemma componentPrimeCartier_ideal (P : AtlasGeometricPrimeCarrier A) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (componentPrimeCartier P x).ideal=vanishingIdeal (n := A.pointDimension x)
      ((Subtype.val : A.componentOpen x → X) ⁻¹' P.val) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  exact (Classical.choose_spec (exists_original_prime_component_cartier P x)).1

lemma componentPrimeCartier_coefficient (P : AtlasGeometricPrimeCarrier A) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ Q : GeometricPrimeCarrier (A.pointDimension x) (A.componentOpen x),
      nativeCartierCoefficientAny (componentPrimeCartier P x) Q=
        if A.nativePrimeOriginalCarrier x Q=P then 1 else 0 := by
  classical
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  exact (Classical.choose_spec (exists_original_prime_component_cartier P x)).2

/-- The SAME original equation now generates the actual internally produced
component Cartier divisor at EVERY full scalar stalk. -/
theorem original_equation_component_cartier (P : AtlasGeometricPrimeCarrier A)
    (f : X → ℂ)
    (hgen : ∀ y b,(atlasVanishingIdeal A P.val).mem y b ↔ A.AtlasIsInSpanAt (· = f) y b)
    (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ q : A.componentOpen x,∀ g : A.componentOpen x → ℂ,
      (componentPrimeCartier P x).ideal.mem q g ↔
        IsInSpanAt (n := A.pointDimension x) (· = f ∘ Subtype.val) q g := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro q g
  rw [componentPrimeCartier_ideal]
  exact original_generator_component P.val f hgen x q g

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
