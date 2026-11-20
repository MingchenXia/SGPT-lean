import SGPT.Toric.LogLogModelEnvelope

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- The literal original V_theta raw supremum over ALL genuine source
theta-PSH functions below zero, including the actual empty-index branch. -/
def sourceMinimalEnvelope (θ : AtlasClosedRealOneOneForm A) : X → EReal :=
  fun x ↦ ⨆ v : {v : X → EReal // A.IsThetaPSH θ v ∧ v ≤ 0}, v.1 x

theorem sourceMinimalEnvelope_le_zero (θ : AtlasClosedRealOneOneForm A) :
    sourceMinimalEnvelope θ ≤ 0 := fun x ↦ iSup_le fun v ↦ v.2.2 x

/-- Every actual source theta minorant below zero is already below the
independent minimal envelope, so the two raw rooftop families agree. -/
theorem thetaRooftop_sourceMinimalEnvelope_eq_zero
    (θ : AtlasClosedRealOneOneForm A) (u : X → EReal) :
    thetaRooftop θ u (sourceMinimalEnvelope θ) = thetaRooftop θ u 0 := by
  apply le_antisymm
  · intro x
    exact iSup_le fun v ↦ le_thetaRooftop v.2.1 v.2.2.1
      (v.2.2.2.trans (sourceMinimalEnvelope_le_zero θ)) x
  · intro x
    apply iSup_le
    intro v
    apply le_thetaRooftop v.2.1 v.2.2.1 _ x
    intro y
    exact le_iSup (fun w : {w : X → EReal // A.IsThetaPSH θ w ∧ w ≤ 0} ↦ w.1 y)
      ⟨v.1, v.2.1, v.2.2.2⟩

/-- Genuine ALL-competitor reindexing, before any claim that an individual
raw rooftop or the regularized output belongs to the source PSH class. -/
theorem sourceSingularityEnvelope_eq_uscSup_thetaRooftop
    (θ : AtlasClosedRealOneOneForm A) (u : X → EReal) :
    sourceSingularityEnvelope θ u =
      uscSup (fun C : ℝ ↦ thetaRooftop θ (fun x ↦ u x + (C : EReal)) 0) := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro v
    obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real _ _).mp v.2.2.2
    exact (le_thetaRooftop v.2.1 hC v.2.2.1 x).trans
      (le_iSup (fun C : ℝ ↦ thetaRooftop θ (fun x ↦ u x + (C : EReal)) 0 x) C)
  · apply iSup_le
    intro C
    apply iSup_le
    intro v
    exact le_iSup (fun w : sourceSingularityCompetitors θ u ↦ w.1 x)
      ⟨v.1, v.2.1, v.2.2.2,
        (singularityLE_iff_exists_real _ _).mpr ⟨C, v.2.2.1⟩⟩

/-- The exact printed positive-integer/V_theta source formula: genuine
Archimedean cofinality retains all original poles and empty families. -/
theorem sourceSingularityEnvelope_eq_uscSup_positiveInt_minimal
    (θ : AtlasClosedRealOneOneForm A) (u : X → EReal) :
    sourceSingularityEnvelope θ u = uscSup (fun j : ℕ ↦
      thetaRooftop θ (fun x ↦ u x + ((j + 1 : ℕ) : EReal))
        (sourceMinimalEnvelope θ)) := by
  rw [sourceSingularityEnvelope_eq_uscSup_thetaRooftop]
  simp_rw [thetaRooftop_sourceMinimalEnvelope_eq_zero]
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro C
    obtain ⟨j, hj⟩ := exists_nat_gt C
    apply le_trans _ (le_iSup
      (fun j : ℕ ↦ thetaRooftop θ (fun x ↦ u x + ((j + 1 : ℕ) : EReal)) 0 x) j)
    apply iSup_le
    intro v
    apply le_thetaRooftop v.2.1 _ v.2.2.2 x
    intro y
    apply (v.2.2.1 y).trans
    change u y + (C : EReal) ≤ u y + ((j + 1 : ℕ) : EReal)
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr
      (by exact hj.le.trans (by norm_num)))
  · apply iSup_le
    intro j
    exact le_iSup (fun C : ℝ ↦ thetaRooftop θ (fun x ↦ u x + (C : EReal)) 0 x)
      (j + 1 : ℕ)

end SGPT.PSH.VariableComplexAtlas
