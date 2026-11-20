import SGPT.Hodge.SourceBigNefIntersection
import SGPT.Hodge.SourceRegFamily

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceRegCone
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor
  SGPT.Hodge.BDivChain.NativeDraft SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceIntersection

/-- Pure finite cancellation, separated from the geometric mixed-volume reader. -/
theorem ennreal_error_zero (r b e s : ENNReal) (hr : r ≠ ⊤)
    (hmono : r ≤ b) (hadd : s=b+e) (hdiag : r=s) : e=0 := by
  have h : r+e ≤ r+0 := by
    calc r+e ≤ b+e := add_le_add hmono le_rfl
      _ = s := hadd.symm
      _ = r+0 := by rw [add_zero]; exact hdiag.symm
  exact le_antisymm ((ENNReal.add_le_add_iff_left (a := r) (b := e) (c := 0) hr).mp h)
    bot_le

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X]
local notation "C" => SGPT.PSH.BookCurrent.ClosedPositiveCurrent m X

/-- Actual zero and sum on the ORIGINAL closed positive current carrier. -/
def coneZero : C := SGPT.Siu.toBookCurrent 0 SGPT.Siu.isClosedPositiveCurrent_zero

def coneAdd (A B : C) : C := SGPT.Siu.toBookCurrent (A.current+B.current)
  ((SGPT.Siu.isClosedPositiveCurrent_bookCurrent A).add
    (SGPT.Siu.isClosedPositiveCurrent_bookCurrent B))

local instance : Zero C := ⟨coneZero⟩
local instance : Add C := ⟨coneAdd⟩

omit [CompactSpace X] in
@[simp] theorem current_zero : (0 : C).current = 0 := rfl
@[simp] theorem current_add (A B : C) : (A+B).current=A.current+B.current := rfl

local instance : AddCommMonoid C where
  zero := coneZero
  add := coneAdd
  add_assoc A B D := SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext (add_assoc _ _ _)
  zero_add A := SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext (zero_add _)
  add_zero A := SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext (add_zero _)
  add_comm A B := SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext (add_comm _ _)
  nsmul := nsmulRec

/-- Current order is given by an ACTUAL other positive current, not b-divisor/class order. -/
def CurrentLE (A B : C) : Prop := ∃ D : C, B=A+D

theorem currentLE_refl (A : C) : CurrentLE A A := ⟨0,(add_zero A).symm⟩

theorem currentLE_trans {A B D : C} (hAB : CurrentLE A B) (hBD : CurrentLE B D) :
    CurrentLE A D := by
  obtain ⟨U,rfl⟩ := hAB
  obtain ⟨V,rfl⟩ := hBD
  exact ⟨U+V,add_assoc A U V⟩

/-- The same actual original mixed value, on this actual current cone. -/
def mixed (ω : KahlerBackground (m+1) X) (T : Fin (m+1) → C)
    [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] : ENNReal :=
  currentMixedIVolumeAny ω (fun i => ofBookCurrent (T i))

variable [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X]

theorem mixed_eq_existing (ω : KahlerBackground (m+1) X) (T : Fin (m+1) → C) :
    mixed ω T = sourceCurrentMixedIVolume ω (fun i => (T i).current)
      (fun i => (T i).isClosed) (fun i => (T i).isTypeOneOne)
      (fun i => (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (T i)).2.2) := by
  unfold mixed
  simpa only [toBookCurrent_ofBookCurrent] using
    currentMixedIVolumeAny_eq_existing ω (fun i => ofBookCurrent (T i))

theorem mixed_lt_top (ω : KahlerBackground (m+1) X) (T : Fin (m+1) → C) :
    mixed ω T < ⊤ := currentMixedIVolumeAny_lt_top ω _

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
theorem current_update (T : Fin (m+1) → C) (a : Fin (m+1)) (A : C) :
    (fun i => (Function.update T a A i).current) =
      Function.update (fun i => (T i).current) a A.current := by
  funext i
  by_cases hi : i=a
  · subst i; simp only [Function.update_self]
  · simp only [Function.update_of_ne hi]

/-- Multiadditivity is the previously accepted law for ARBITRARY original currents. -/
theorem mixed_update_add (ω : KahlerBackground (m+1) X) (T : Fin (m+1) → C)
    (a : Fin (m+1)) (A : C) :
    mixed ω (Function.update T a (T a+A)) = mixed ω T+mixed ω (Function.update T a A) := by
  rw [mixed_eq_existing,mixed_eq_existing,mixed_eq_existing]
  obtain ⟨hc,h11,hp,h⟩ := sourceCurrentMixedIVolume_add_slot ω
    (fun i => (T i).current) (fun i => (T i).isClosed) (fun i => (T i).isTypeOneOne)
    (fun i => (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (T i)).2.2) a A.current
    A.isClosed A.isTypeOneOne (SGPT.Siu.isClosedPositiveCurrent_bookCurrent A).2.2
  simpa only [current_update,current_add] using h

/-- Slotwise monotonicity uses the ACTUAL positive difference. -/
theorem mixed_update_mono (ω : KahlerBackground (m+1) X) (T : Fin (m+1) → C)
    (a : Fin (m+1)) (A : C) (h : CurrentLE (T a) A) :
    mixed ω T ≤ mixed ω (Function.update T a A) := by
  obtain ⟨D,rfl⟩ := h
  rw [mixed_update_add]
  exact le_self_add

/-- Actual current sums, used for finite positive domination. -/
def currentSum {ι : Type*} (s : Finset ι) (T : ι → C) : C := ∑ i ∈ s, T i

/-- Arbitrary simultaneous CURRENT-order monotonicity from actual positive differences. -/
theorem mixed_mono_current (ω : KahlerBackground (m+1) X)
    (T S : Fin (m+1) → C) (hTS : ∀ i, CurrentLE (T i) (S i)) :
    mixed ω T ≤ mixed ω S := by
  classical
  choose D hD using hTS
  let U (s : Finset (Fin (m+1))) : Fin (m+1) → C := fun i => if i ∈ s then S i else T i
  have hmono (s : Finset (Fin (m+1))) : mixed ω T ≤ mixed ω (U s) := by
    induction s using Finset.induction_on with
    | empty => simp only [U,Finset.notMem_empty,if_false]; exact le_rfl
    | @insert a s ha ih =>
      have hU : U (insert a s) = Function.update (U s) a (U s a+D a) := by
        funext i
        by_cases hi : i=a
        · subst i; simp only [U,Finset.mem_insert_self,if_true,Function.update_self,if_neg ha]
          exact hD a
        · simp only [U,Finset.mem_insert,hi,false_or,Function.update_of_ne hi]
      rw [hU]
      exact ih.trans (mixed_update_mono ω (U s) a (U s a+D a) ⟨D a,rfl⟩)
  simpa only [U,Finset.mem_univ,if_true] using hmono Finset.univ

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
theorem currentLE_sum {ι : Type*} (s : Finset ι) (T : ι → C) {a : ι} (ha : a ∈ s) :
    CurrentLE (T a) (currentSum s T) := by
  classical
  refine ⟨currentSum (s.erase a) T,?_⟩
  simpa only [currentSum] using (Finset.add_sum_erase s T ha).symm

def regular (T : C) : C := SGPT.Siu.bookSiuRegularPart T
def divisorial (T : C) : C := SGPT.Siu.bookSiuDivisorialPart T

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
theorem decompose (T : C) : T=regular T+divisorial T :=
  SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext (SGPT.Siu.book_siu_decomposition T).1

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
theorem regular_currentLE (T : C) : CurrentLE (regular T) T := ⟨divisorial T,decompose T⟩

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
theorem divisorial_add (T S : C) : divisorial (T+S)=divisorial T+divisorial S := by
  apply SGPT.PSH.BookCurrent.ClosedPositiveCurrent.ext
  exact PrimePushforward.siuDivisorialPart_add
    (SGPT.Siu.isClosedPositiveCurrent_bookCurrent T)
    (SGPT.Siu.isClosedPositiveCurrent_bookCurrent S)
    (SGPT.Siu.isClosedPositiveCurrent_bookCurrent (T+S))

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] in
theorem divisorial_currentLE {T S : C} (h : CurrentLE T S) :
    CurrentLE (divisorial T) (divisorial S) := by
  obtain ⟨D,rfl⟩ := h
  exact ⟨divisorial D,divisorial_add T D⟩

/-- The source mixed diagonal is the independently defined actual original I-volume. -/
theorem mixed_diagonal (ω : KahlerBackground (m+1) X) (T : C) :
    mixed ω (fun _ => T) = currentIVolumeAny (ofBookCurrent T) :=
  sourceGeneralMixedIVolume_diagonal ω (presentationPSH (ofBookCurrent T))

/-- Diagonal Reg invariance is INTERNALLY produced from the actual complete-family theorem. -/
theorem mixed_diagonal_regular (ω : KahlerBackground (m+1) X) (T : C) :
    mixed ω (fun _ => regular T)=mixed ω (fun _ => T) := by
  rw [mixed_diagonal,mixed_diagonal]
  have hReg : regularCurrentAny (ofBookCurrent T)=ofBookCurrent (regular T) := by
    calc regularCurrentAny (ofBookCurrent T) =
        ofBookCurrent (toBookCurrent (regularCurrentAny (ofBookCurrent T))) :=
          (ofBookCurrent_toBookCurrent _).symm
      _ = ofBookCurrent (regular T) := congrArg ofBookCurrent (by
        rw [regularCurrentAny_pos,toBookCurrent_ofBookCurrent]; rfl)
  rw [←hReg]
  exact SGPT.Hodge.BDivChain.SourceReg.currentIVolumeAny_regular_eq ω (ofBookCurrent T)

/-- Finite diagonal cancellation kills the actual divisorial error in ANY slot.
No infinite-tail estimate or source Reg mixed-volume theorem is an input. -/
theorem mixed_divisorial_diagonal_zero (ω : KahlerBackground (m+1) X) (S : C)
    (a : Fin (m+1)) :
    mixed ω (Function.update (fun _ => S) a (divisorial S))=0 := by
  classical
  let R := regular S
  let D := divisorial S
  let B : Fin (m+1) → C := Function.update (fun _ => S) a R
  have hinput : Function.update B a (B a+D)=(fun _ => S) := by
    funext i
    by_cases hi : i=a
    · subst i; simp only [B,Function.update_self]; exact (decompose S).symm
    · simp only [B,Function.update_of_ne hi]
  have herr : Function.update B a D=Function.update (fun _ => S) a D := by
    funext i
    by_cases hi : i=a
    · subst i; simp only [Function.update_self]
    · simp only [B,Function.update_of_ne hi]
  have hadd := mixed_update_add ω B a D
  rw [hinput,herr] at hadd
  have hmono : mixed ω (fun _ => R) ≤ mixed ω B := by
    apply mixed_mono_current
    intro i
    by_cases hi : i=a
    · subst i; simp only [B,Function.update_self]; exact currentLE_refl R
    · simp only [B,Function.update_of_ne hi]; exact regular_currentLE S
  have hpure : mixed ω (fun _ => R)=mixed ω (fun _ => S) := mixed_diagonal_regular ω S
  exact ennreal_error_zero (mixed ω (fun _ => R)) (mixed ω B)
    (mixed ω (Function.update (fun _ => S) a D)) (mixed ω (fun _ => S))
    (ne_of_lt (mixed_lt_top ω (fun _ => R))) hmono hadd hpure

/-- Every individual source divisorial-slot error is zero, dominated by an
INTERNALLY produced actual positive finite sum of the original currents. -/
theorem mixed_divisorial_slot_zero (ω : KahlerBackground (m+1) X)
    (T : Fin (m+1) → C) (a : Fin (m+1)) :
    mixed ω (Function.update T a (divisorial (T a)))=0 := by
  classical
  let S := currentSum Finset.univ T
  have hTS (i : Fin (m+1)) : CurrentLE (T i) S :=
    currentLE_sum Finset.univ T (Finset.mem_univ i)
  have hmono : mixed ω (Function.update T a (divisorial (T a))) ≤
      mixed ω (Function.update (fun _ => S) a (divisorial S)) := by
    apply mixed_mono_current
    intro i
    by_cases hi : i=a
    · subst i; simp only [Function.update_self]; exact divisorial_currentLE (hTS a)
    · simp only [Function.update_of_ne hi]; exact hTS i
  exact le_antisymm (hmono.trans_eq (mixed_divisorial_diagonal_zero ω S a)) bot_le

/-- Replacing ONE original current by its actual Reg part preserves the mixed value. -/
theorem mixed_update_regular (ω : KahlerBackground (m+1) X)
    (T : Fin (m+1) → C) (a : Fin (m+1)) :
    mixed ω (Function.update T a (regular (T a)))=mixed ω T := by
  classical
  let B := Function.update T a (regular (T a))
  have hinput : Function.update B a (B a+divisorial (T a))=T := by
    funext i
    by_cases hi : i=a
    · subst i; simp only [B,Function.update_self]; exact (decompose (T a)).symm
    · simp only [B,Function.update_of_ne hi]
  have herr : Function.update B a (divisorial (T a))=
      Function.update T a (divisorial (T a)) := by
    funext i
    by_cases hi : i=a
    · subst i; simp only [Function.update_self]
    · simp only [B,Function.update_of_ne hi]
  have hadd := mixed_update_add ω B a (divisorial (T a))
  rw [hinput,herr,mixed_divisorial_slot_zero,add_zero] at hadd
  exact hadd.symm

/-- Original mixed Reg invariance on EVERY actual positive-current tuple.
All finite sums/current differences and the finite diagonal cancellation
were produced internally. No source output certificate or I-good restriction. -/
theorem mixed_regular (ω : KahlerBackground (m+1) X) (T : Fin (m+1) → C) :
    mixed ω (fun i => regular (T i))=mixed ω T := by
  classical
  let U (s : Finset (Fin (m+1))) : Fin (m+1) → C :=
    fun i => if i ∈ s then regular (T i) else T i
  have heq (s : Finset (Fin (m+1))) : mixed ω (U s)=mixed ω T := by
    induction s using Finset.induction_on with
    | empty => simp only [U,Finset.notMem_empty,if_false]
    | @insert a s ha ih =>
      have hU : U (insert a s)=Function.update (U s) a (regular (U s a)) := by
        funext i
        by_cases hi : i=a
        · subst i; simp only [U,Finset.mem_insert_self,if_true,Function.update_self,if_neg ha]
        · simp only [U,Finset.mem_insert,hi,false_or,Function.update_of_ne hi]
      rw [hU]
      exact (mixed_update_regular ω (U s) a).trans ih
  simpa only [U,Finset.mem_univ,if_true] using heq Finset.univ

end SGPT.Hodge.BDivChain.SourceRegCone
