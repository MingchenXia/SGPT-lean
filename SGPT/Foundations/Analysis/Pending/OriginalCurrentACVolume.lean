import SGPT.Foundations.Analysis.Pending.OriginalCurrentClassUniformACTopMass

set_option autoImplicit false

/-! # Volume of an actual smooth Bott--Chern class

Boucksom Definition 1.3 in the original full-current space: supremum of
canonical AC-top masses of ALL original closed positive type-(1,1) currents.
The classwise uniform bound internally gives finiteness, and a strict
threshold internally selects an actual current. Positive dimension includes
empty and disconnected manifolds. No Calabi--Yau or weak-class compactness
is inferred. The full blueprint statements and proofs precede this source. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SGPT.Foundations.Analysis.Pending.OriginalCurrentACVolume
open FirstPass FirstPass.PositiveClasses GlobalCurrents GlobalCurrentPotentials
  CanonicalCurrentFrame CurrentBottChernClass GlobalPositiveCurrentACRestriction
  GlobalPositiveCurrentACTopMeasure OriginalCurrentClassUniformACTopMass

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]

/-- Boucksom's original-current volume. The class constraint uses the
actual smooth Bott--Chern class map of SAME original closed currents. -/
def originalCurrentACVolume (β : RealBottChern (m+1) M) : ℝ≥0∞ :=
  ⨆ (T : ClosedOneOneCurrent (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m))
    (hT : IsFullPositive T.val)
    (_ : bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T = β),
      globalACtopMeasure T.val hT univ

/-- Every genuine original admissible current contributes its actual mass
to the original volume supremum. -/
theorem ac_top_mass_le_volume
    (T : ClosedOneOneCurrent (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m))
    (hT : IsFullPositive T.val) {β : RealBottChern (m+1) M}
    (hclass : bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T = β) :
    globalACtopMeasure T.val hT univ ≤ originalCurrentACVolume β := by
  exact le_iSup_of_le T (le_iSup_of_le hT (le_iSup_of_le hclass le_rfl))

/-- The genuine quotient internally supplies a smooth representative;
the classwise bound is uniform before ALL original admissible currents. -/
theorem originalCurrentACVolume_lt_top
    (omega : KahlerBackground (m+1) M) (β : RealBottChern (m+1) M) :
    originalCurrentACVolume β < ⊤ := by
  refine Quotient.inductionOn β (fun θ => ?_)
  obtain ⟨C,hC,hbound⟩ := exists_uniform_ac_top_mass_of_class omega θ
  apply lt_of_le_of_lt _ hC
  exact iSup_le fun T => iSup_le fun hT => iSup_le fun hclass => hbound T hT hclass

/-- An actual original current is selected internally above ANY strict
volume threshold. No near-maximizing family is an input. -/
theorem exists_current_mass_gt (β : RealBottChern (m+1) M) {r : ℝ≥0∞}
    (hr : r < originalCurrentACVolume β) :
    ∃ (T : ClosedOneOneCurrent (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m))
      (hT : IsFullPositive T.val),
      bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T = β ∧
        r < globalACtopMeasure T.val hT univ := by
  unfold originalCurrentACVolume at hr
  obtain ⟨T,h₁⟩ := lt_iSup_iff.mp hr
  obtain ⟨hT,h₂⟩ := lt_iSup_iff.mp h₁
  obtain ⟨hclass,hlt⟩ := lt_iSup_iff.mp h₂
  exact ⟨T,hT,hclass,hlt⟩

end SGPT.Foundations.Analysis.Pending.OriginalCurrentACVolume
