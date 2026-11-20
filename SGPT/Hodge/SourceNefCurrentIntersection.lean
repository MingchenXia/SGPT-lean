import SGPT.Hodge.SourceMixedLinearity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefCurrentIntersectionDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetRealDraft SGPT.Hodge.BDivChain.SourceIntersection
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft SGPT.Hodge.BDivChain.SourceMixedOrderDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup n X

/-- ALL original current mixed I-volumes have the independently defined
pure-family-volume polarization, with no I-good/nondivisorial/fullness input. -/
theorem source_currentMixed_real_eq_nefIntersectionReal (ω : KahlerBackground n X)
    (T : Fin n → ClosedPositive (n := n) (X := X)) :
    (currentMixedIVolumeAny ω T).toReal=
      nefIntersectionReal (fun i => currentBDivisorAnyOn Sys (T i)) := by
  cases n with
  | zero =>
    rw [nefIntersectionReal_zero]
    change (sourceGeneralMixedIVolume ω _ _ _).toReal=1
    rw [SGPT.IGood.LogVolume.sourceGeneralMixedIVolume_eq_one_of_dim_zero]
    exact ENNReal.toReal_one
  | succ m =>
    have h := factorial_mul_currentMixed_eq_family_polarization ω (fun i => actualCurrentCone (T i))
    simp_rw [coneActualCurrent_actualCurrentCone,coneFamilyHom_actualCurrentCone] at h
    have hn : ((m+1).factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (m+1)
    unfold nefIntersectionReal
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm,familyVolumePolarization,volumeRealAny] using h

/-- Exact fifth original prop:DFlinear clause on ALL actual source currents,
in ALL dimensions. This is I-envelope mixed volume, never original NPP mass. -/
theorem source_nefIntersection_current (ω : KahlerBackground n X)
    (T : Fin n → ClosedPositive (n := n) (X := X)) :
    (∀ i,IsNefAny (currentBDivisorAnyOn Sys (T i))) ∧
      nefIntersection (fun i => currentBDivisorAnyOn Sys (T i))=currentMixedIVolumeAny ω T := by
  refine ⟨fun i => SGPT.Hodge.BDivChain.NativeDraft.DTUniformDraft.currentBDivisorAnyOn_isNef ω (T i),?_⟩
  unfold nefIntersection
  rw [←source_currentMixed_real_eq_nefIntersectionReal ω T]
  exact ENNReal.ofReal_toReal (currentMixedIVolumeAny_lt_top ω T).ne

/-- WHOLE original prop:DFlinear: actual all-nef algebra and original order,
plus the actual mixed I-volume reader on EVERY source positive closed tuple. -/
theorem source_prop_DFlinear_whole (ω : KahlerBackground n X) :
    ((∀ (D : Fin n → WeilFamilyAny Sys), (∀ i,IsNefAny (D i)) →
      ∀ σ : Equiv.Perm (Fin n),nefIntersection (fun i => D (σ i))=nefIntersection D) ∧
    (∀ (D : Fin n → WeilFamilyAny Sys), (∀ i,IsNefAny (D i)) →
      ∀ (j : Fin n) (U V : WeilFamilyAny Sys), IsNefAny U → IsNefAny V →
        nefIntersection (Function.update D j (U+V))=
          nefIntersection (Function.update D j U)+nefIntersection (Function.update D j V)) ∧
    (∀ (D : Fin n → WeilFamilyAny Sys), (∀ i,IsNefAny (D i)) →
      ∀ (j : Fin n) (U : WeilFamilyAny Sys), IsNefAny U → ∀ c : ℝ,0≤c →
        nefIntersection (Function.update D j (c • U))=
          ENNReal.ofReal c * nefIntersection (Function.update D j U)) ∧
    (∀ (D E : Fin n → WeilFamilyAny Sys), (∀ i,IsNefAny (D i)) →
      (∀ i,IsNefAny (E i)) → (∀ i,LEAny (D i) (E i)) → nefIntersection D≤nefIntersection E)) ∧
    (∀ T : Fin n → ClosedPositive (n := n) (X := X),
      (∀ i,IsNefAny (currentBDivisorAnyOn Sys (T i))) ∧
      nefIntersection (fun i => currentBDivisorAnyOn Sys (T i))=currentMixedIVolumeAny ω T) :=
  ⟨source_DFlinear_whole ω,source_nefIntersection_current ω⟩

end SGPT.Hodge.BDivChain.SourceNefCurrentIntersectionDraft
