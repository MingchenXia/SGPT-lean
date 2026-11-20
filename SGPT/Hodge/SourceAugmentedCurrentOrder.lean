import SGPT.Hodge.SourceAugmentedCurrentObjects
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshPositivePDomain

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceAugmentedDraft
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
  SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- Actual multiplier order preserves actual addition of original currents,
using genuine potentials produced internally. -/
theorem currentIOrderAny_add [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    (ω : KahlerBackground n X) {T S U V : ClosedPositive (n := n) (X := X)}
    (hTS : currentIOrderAny T S) (hUV : currentIOrderAny U V) :
    currentIOrderAny (addCurrentAny T U) (addCurrentAny S V) := by
  cases n with
  | zero =>
    have he : addCurrentAny T U=addCurrentAny S V :=
      (closedPositive_eq_zeroDim _).trans (closedPositive_eq_zeroDim _).symm
    rw [he]
    exact currentIOrderAny_refl _
  | succ m =>
    obtain ⟨θ,σ,u,v,hT,hS,hI⟩ := hTS
    obtain ⟨τ,ρ,w,z,hU,hV,hJ⟩ := hUV
    obtain ⟨hu,hTeq⟩ := (isPresentationAny_iff_book T θ u).mp hT
    obtain ⟨hv,hSeq⟩ := (isPresentationAny_iff_book S σ v).mp hS
    obtain ⟨hw,hUeq⟩ := (isPresentationAny_iff_book U τ w).mp hU
    obtain ⟨hz,hVeq⟩ := (isPresentationAny_iff_book V ρ z).mp hV
    obtain ⟨huw,hcurT⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hu hw
    obtain ⟨hvz,hcurS⟩ := SGPT.Okounkov.exists_thetaPotentialCurrent_add hv hz
    apply (currentIOrderAny_iff_existing _ _).mpr
    refine ⟨θ+τ,σ+ρ,(fun x => u x+w x),(fun x => v x+z x),huw,hvz,?_,?_,?_⟩
    · rw [toBookCurrent_addCurrentAny,hcurT,←hTeq,←hUeq]
    · rw [toBookCurrent_addCurrentAny,hcurS,←hSeq,←hVeq]
    · obtain ⟨C,_,huC,hvC,_,_⟩ := GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background
        ω hu.quasiPshPotential hv.quasiPshPotential
      obtain ⟨B,_,hwB,hzB,_,_⟩ := GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background
        ω hw.quasiPshPotential hz.quasiPshPotential
      exact ActualMultiplierOrderAddition.iOrderOnManifold_add huC hwB hvC hzB hI hJ

/-- Actual multiplier order implies the exact original generic coefficient inequalities. -/
theorem currentCoefficientAny_le_of_IOrder {T S : ClosedPositive (n := n) (X := X)}
    (hTS : currentIOrderAny T S) (D : SGPT.PSH.GeometricPrimeCarrier n X) :
    currentCoefficientAny S D ≤ currentCoefficientAny T D := by
  cases n with
  | zero => exact isEmptyElim D
  | succ m =>
    obtain ⟨θ,σ,u,v,hT,hS,hI⟩ := hTS
    obtain ⟨hu,hTeq⟩ := (isPresentationAny_iff_book T θ u).mp hT
    obtain ⟨hv,hSeq⟩ := (isPresentationAny_iff_book S σ v).mp hS
    let hTp := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)
    let hSp := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent S)
    have hpoint (x : X) : SGPT.Siu.currentLelong (toBookCurrent S).current hSp x ≤
        SGPT.Siu.currentLelong (toBookCurrent T).current hTp x := by
      rw [SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent hSp hSeq,
        SGPT.Siu.currentLelong_eq_of_eq_thetaPotentialCurrent hTp hTeq]
      have h := RawIntegerPointComparison.lelongNumber_le_of_iOrderOnManifold
        hu.1.quasiPlurisubharmonic hI x
      rw [lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m),
        lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)] at h
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h
    change (SGPT.Siu.bookGenericLelong (toBookCurrent S) D).toReal ≤
      (SGPT.Siu.bookGenericLelong (toBookCurrent T) D).toReal
    rw [SGPT.Siu.bookGenericLelong_eq,SGPT.Siu.bookGenericLelong_eq]
    apply ENNReal.toReal_mono (SGPT.Siu.currentGenericLelong_ne_top hTp D)
    exact le_iInf₂ fun x hx => (SGPT.Siu.currentGenericLelong_le hSp D hx).trans (hpoint x)

theorem currentCoefficientAny_eq_of_IEquivalent {T S : ClosedPositive (n := n) (X := X)}
    (hTS : currentIOrderAny T S) (hST : currentIOrderAny S T) :
    currentCoefficientAny T=currentCoefficientAny S := by
  funext D
  exact le_antisymm (currentCoefficientAny_le_of_IOrder hST D)
    (currentCoefficientAny_le_of_IOrder hTS D)

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
