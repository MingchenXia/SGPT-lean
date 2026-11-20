import SGPT.Hodge.SourceAugmentedCurrentObjects

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceAugmentedDraft
open Set Filter
open scoped Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.BDivisor.PrimePushforward
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

theorem actualCurrent_eq_of_book_eq {m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]
    {T S : ClosedPositive (n := m+1) (X := M)} (h : toBookCurrent T=toBookCurrent S) : T=S :=
  (ofBookCurrent_toBookCurrent T).symm.trans
    ((congrArg ofBookCurrent h).trans (ofBookCurrent_toBookCurrent S))

/-- EXACT original class-summability internally realizes an actual purely divisorial
current with every original generic coefficient, in all natural dimensions. -/
theorem exists_divisorial_currentAny_of_class_sum [ConnectedSpace X]
    (ω : KahlerBackground n X) (c : SGPT.PSH.GeometricPrimeCarrier n X → ℝ)
    (hc : ∀ D, 0≤c D) (β : RealBottChern n X) (hclass : HasDivisorClassSumAny c β) :
    ∃ V : ClosedPositive (n := n) (X := X), currentClassAny V=β ∧
      currentCoefficientAny V=c ∧ V=divisorCurrentAny V := by
  cases n with
  | zero =>
    refine ⟨closedPositiveZeroDim,?_,?_,?_⟩
    · exact (realBottChern_eq_zero_of_dim_zero _).trans (realBottChern_eq_zero_of_dim_zero β).symm
    · funext D; exact isEmptyElim D
    · exact (closedPositive_eq_zeroDim _).trans (closedPositive_eq_zeroDim _).symm
  | succ m =>
    obtain ⟨S,hS,hSclass,hcoeff,hpure⟩ := exists_divisorial_current_of_class_sum ω c hc β hclass
    let V := ofBookCurrent (SGPT.Siu.toBookCurrent S hS)
    refine ⟨V,?_,?_,?_⟩
    · change SGPT.PSH.BookCurrent.currentClass (toBookCurrent (ofBookCurrent _))=β
      rw [toBookCurrent_ofBookCurrent]
      exact hSclass
    · funext D
      change (SGPT.Siu.bookGenericLelong (toBookCurrent (ofBookCurrent _)) D).toReal=c D
      rw [toBookCurrent_ofBookCurrent,SGPT.Siu.bookGenericLelong_eq]
      exact hcoeff D
    · apply actualCurrent_eq_of_book_eq
      apply SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
      rw [toBookCurrent_divisorCurrentAny]
      dsimp only [V]
      simp only [toBookCurrent_ofBookCurrent,SGPT.Siu.toBookCurrent_current]
      exact hpure

/-- Adding any actual current to an actual nondivisorial current retains precisely
the added current's generic divisor coefficients. -/
theorem addCurrentAny_coeff_of_regular
    (R V : ClosedPositive (n := n) (X := X)) (hR : R=regularCurrentAny R) :
    currentCoefficientAny (addCurrentAny R V)=currentCoefficientAny V := by
  funext D
  cases n with
  | zero => exact isEmptyElim D
  | succ m =>
    let hRp := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent R)
    let hVp := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent V)
    have hR0 := (SGPT.Siu.isNonDivisorial_iff hRp).mp (nonDivisorial_toBookCurrent R hR) D
    change (SGPT.Siu.bookGenericLelong (toBookCurrent (addCurrentAny R V)) D).toReal =
      (SGPT.Siu.bookGenericLelong (toBookCurrent V) D).toReal
    rw [SGPT.Siu.bookGenericLelong_eq,SGPT.Siu.bookGenericLelong_eq]
    have he : SGPT.Siu.currentGenericLelong (toBookCurrent (addCurrentAny R V)).current
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent (addCurrentAny R V))) D =
        SGPT.Siu.currentGenericLelong ((toBookCurrent R).current+(toBookCurrent V).current)
          (hRp.add hVp) D := by congr 1; exact toBookCurrent_addCurrentAny R V
    rw [he,currentGenericLelong_add hRp hVp (hRp.add hVp) D,hR0,zero_add]

/-- The actual Siu regular part of R+V is R when R is nondivisorial and V divisorial. -/
theorem regularCurrentAny_add_of_divisorial
    (R V : ClosedPositive (n := n) (X := X)) (hR : R=regularCurrentAny R)
    (hV : V=divisorCurrentAny V) : regularCurrentAny (addCurrentAny R V)=R := by
  cases n with
  | zero => exact (closedPositive_eq_zeroDim _).trans (closedPositive_eq_zeroDim _).symm
  | succ m =>
    apply actualCurrent_eq_of_book_eq
    apply SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
    rw [regularCurrentAny_pos]
    let hRp := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent R)
    let hVp := SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent V)
    have hRreg : SGPT.Siu.siuRegularPart (toBookCurrent R).current hRp=(toBookCurrent R).current :=
      (nonDivisorial_toBookCurrent R hR).symm
    have hVdiv : (toBookCurrent V).current=SGPT.Siu.siuDivisorialPart (toBookCurrent V).current hVp :=
      (congrArg (fun T => (toBookCurrent T).current) hV).trans (toBookCurrent_divisorCurrentAny V)
    have hVreg : SGPT.Siu.siuRegularPart (toBookCurrent V).current hVp=0 := by
      unfold SGPT.Siu.siuRegularPart
      rw [←hVdiv]
      abel
    change SGPT.Siu.siuRegularPart (toBookCurrent (addCurrentAny R V)).current _ = _
    calc
      _ = SGPT.Siu.siuRegularPart ((toBookCurrent R).current+(toBookCurrent V).current)
          (hRp.add hVp) := siuRegularPart_congr (toBookCurrent_addCurrentAny R V) _ _
      _ = SGPT.Siu.siuRegularPart (toBookCurrent R).current hRp+
          SGPT.Siu.siuRegularPart (toBookCurrent V).current hVp := siuRegularPart_add hRp hVp _
      _ = (toBookCurrent R).current := by rw [hRreg,hVreg]; abel

/-- Equality of every original coefficient identifies the actual full divisorial currents. -/
theorem divisorCurrentAny_eq_of_coeff_eq {T S : ClosedPositive (n := n) (X := X)}
    (h : currentCoefficientAny T=currentCoefficientAny S) : divisorCurrentAny T=divisorCurrentAny S := by
  cases n with
  | zero => exact (closedPositive_eq_zeroDim _).trans (closedPositive_eq_zeroDim _).symm
  | succ m =>
    apply actualCurrent_eq_of_book_eq
    apply SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
    rw [toBookCurrent_divisorCurrentAny,toBookCurrent_divisorCurrentAny]
    apply SGPT.Foundations.Analysis.FirstPass.GlobalCurrent.ext
    intro e η
    have ht := SGPT.Siu.hasSum_siuDivisorialPart
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)) e η
    have hs := SGPT.Siu.hasSum_siuDivisorialPart
      (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent S)) e η
    have he (D) : (SGPT.Siu.currentGenericLelong (toBookCurrent T).current
        (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent T)) D).toReal =
        (SGPT.Siu.currentGenericLelong (toBookCurrent S).current
          (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (toBookCurrent S)) D).toReal := by
      have hD := congrFun h D
      change (SGPT.Siu.bookGenericLelong (toBookCurrent T) D).toReal =
        (SGPT.Siu.bookGenericLelong (toBookCurrent S) D).toReal at hD
      simpa only [SGPT.Siu.bookGenericLelong_eq] using hD
    simp_rw [he] at ht
    exact ht.unique hs

end SGPT.Hodge.BDivChain.SourceAugmentedDraft
