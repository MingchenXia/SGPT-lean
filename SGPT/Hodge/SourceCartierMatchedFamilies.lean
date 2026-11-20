import SGPT.Hodge.SourceCartierCoherentRows

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
  SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.GlobalDistributionTwo
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Same actual analytic singularity type in the SAME root class gives the
SAME complete original family, even if the currents have divisorial parts. -/
theorem representedFamily_eq_of_sameSingularityType
    (θ η : ClosedRealOneOneForm (m+1) X) (u v : X → EReal)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential η.val v)
    (hc : RealBottChern.ofRepresentative θ = RealBottChern.ofRepresentative η)
    (hSame : SameSingularityTypeOn u v univ) :
    currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent θ u hu) =
      currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent η v hv) := by
  obtain ⟨C,hC⟩ := hSame.1
  obtain ⟨B,hB⟩ := hSame.2
  have hIuv := iOrderOnManifold_of_le_add hv.1.quasiPlurisubharmonic (fun x => hC x (mem_univ x))
  have hIvu := iOrderOnManifold_of_le_add hu.1.quasiPlurisubharmonic (fun x => hB x (mem_univ x))
  have hp := representedCurrent_isPresentation θ u hu
  have hq := representedCurrent_isPresentation η v hv
  exact currentBDivisorAnyOn_eq_of_currentIEquivalent
    ((currentClassAny_eq_of_presentation _ _ _ hp).trans
      (hc.trans (currentClassAny_eq_of_presentation _ _ _ hq).symm))
    ⟨θ,η,u,v,hp,hq,hIuv⟩ ⟨η,θ,v,u,hq,hp,hIvu⟩

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Exact simultaneous QEA family bridge. After removing the actual smooth
reciprocal root shift, every positive same-j row is the SAME original family.
The equality is produced from actual currents/types, never supplied as a
simultaneous-QEA or model/cofinality certificate. -/
theorem matchedRow_family_minus_shift (ω : KahlerBackground (m+1) X)
    (α : RealBottChern (m+1) X) (θ : ℕ → ClosedRealOneOneForm (m+1) X)
    (hclass : ∀ i, RealBottChern.ofRepresentative (θ i) =
      α + reciprocalStep i • RealBottChern.ofRepresentative ω.form)
    (i : ℕ) (v w : X → EReal)
    (hv : IsThetaPshPotential (θ i).val v) (hw : IsThetaPshPotential (θ 0).val w)
    (hSame : SameSingularityTypeOn v w univ) :
    currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent (θ i) v hv) =
      currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent (θ 0) w hw) -
        rootCartierAny (RealBottChern.ofRepresentative ω.form) +
          reciprocalStep i • rootCartierAny (RealBottChern.ofRepresentative ω.form) := by
  let σ : ClosedRealOneOneForm (m+1) X := (1-reciprocalStep i) • ω.form
  have hσ : σ.val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul ω.isSemipositive (sub_nonneg.mpr (reciprocalStep_le_one i))
  have hv' := LocalPotentials.isThetaPshPotential_add_of_semipositive hv hσ
  have hc : RealBottChern.ofRepresentative (θ i+σ) = RealBottChern.ofRepresentative (θ 0) := by
    calc
      _ = RealBottChern.ofRepresentative (θ i) + RealBottChern.ofRepresentative σ :=
        RealBottChern.ofRepresentative_add _ _
      _ = (α + reciprocalStep i • RealBottChern.ofRepresentative ω.form) +
          (1-reciprocalStep i) • RealBottChern.ofRepresentative ω.form := by
        rw [hclass, RealBottChern.ofRepresentative_smul]
      _ = α + RealBottChern.ofRepresentative ω.form := by module
      _ = _ := by
        have hzero : RealBottChern.ofRepresentative (θ 0) =
            α + RealBottChern.ofRepresentative ω.form := by
          simpa only [reciprocalStep,Nat.cast_zero,zero_add,div_one,one_smul] using hclass 0
        exact hzero.symm
  have he := (representedSmoothShift_bdivisor (θ i) v hv σ hσ).symm.trans
    (representedFamily_eq_of_sameSingularityType (θ i+σ) (θ 0) v w hv' hw hc hSame)
  have heσ : rootCartierAny (RealBottChern.ofRepresentative σ) =
      (1-reciprocalStep i) • rootCartierAny (RealBottChern.ofRepresentative ω.form) := by
    rw [RealBottChern.ofRepresentative_smul,rootCartierAny_smul]
  rw [heσ] at he
  calc
    _ = currentBDivisorAnyOn (ModelSystem.blowup (m+1) X) (representedCurrent (θ 0) w hw) -
        (1-reciprocalStep i) • rootCartierAny (RealBottChern.ofRepresentative ω.form) :=
      eq_sub_of_add_eq he
    _ = _ := by module

end SGPT.Hodge.BDivChain.SourceCartierSequenceDraft
