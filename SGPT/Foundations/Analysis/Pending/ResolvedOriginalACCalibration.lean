import SGPT.Foundations.Analysis.Pending.ResolvedNefCalabiYauDescent
import SGPT.Foundations.Analysis.Pending.MeteredDivisorResidualACMeasure
import SGPT.Foundations.Analysis.Pending.ThetaCurrentModificationGlobalACTransport
import SGPT.Foundations.Analysis.Pending.PrescribedBlowupDomination

set_option autoImplicit false

/-!
# Original-space AC calibration from a resolved nef family

An arbitrary original closed fully positive current internally supplies a
single resolution before every positive reference perturbation. Its entire
downstairs AC measure is calibrated to the pushforward reference volume.
The residual potentials may be unbounded and nonanalytic. This is the
transport step in Boucksom 4.6, not the subsequent weak-limit argument.
The complete mathematical statement and ENTIRE proof precede this file.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
universe u
namespace SGPT.Foundations.Analysis.Pending.ResolvedOriginalACCalibration
open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.GlobalAnalyticSingularities FirstPass.BlowupSequences
  FirstPass.HolomorphicIdealSheaves IntegrationCurrent BoundedGlobalProduct
  NefMixedMass ThetaPotentialCurrentBottChernClass
  CurrentBottChernClass CanonicalCurrentFrame GlobalCurrentPotentials
  GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
  AnalyticModificationLocalDiscrepancy
  _root_.SGPT.Foundations.Analysis.LocalCurrents

private theorem isAnalyticModification_id
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] :
    IsAnalyticModification (n := n) (id : X → X) := by
  refine ⟨contMDiff_id, isProperMap_id, ∅, ∅, id,
    isClosed_empty, isComplexAnalyticSubset_empty, ?_,
    isClosed_empty, isComplexAnalyticSubset_empty, ?_, ?_,
    contMDiff_id.contMDiffOn, fun _ _ => rfl, fun _ _ => rfl⟩ <;> simp

private theorem isAnalyticModification_of_isBlowupSequence
    {n : ℕ} {X Y : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : IsBlowupSequence n X Y π) :
    IsAnalyticModification (n := n) π := by
  induction hπ with
  | refl => exact isAnalyticModification_id
  | step f C b _ hb ih =>
      exact AnalyticModificationComposition.isAnalyticModification_comp ih
        (PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong hb)

private theorem thetaPotentialCurrent_congr
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]
    (θ : ClosedRealOneOneForm (m+1) M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (h : u = v) : thetaPotentialCurrent θ.val u hu =
      thetaPotentialCurrent θ.val v hv := by
  subst v
  rfl

private theorem globalACtopMeasure_congr
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    {S R : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m))}
    (hS : IsFullPositive S) (hR : IsFullPositive R) (h : S = R) :
    globalACtopMeasure S hS = globalACtopMeasure R hR := by
  subst R
  rfl

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X]

/-- An arbitrary original positive closed current internally supplies one
resolution and entire original-space AC calibrations for every positive
reference perturbation. No limit or calibration is an input. -/
theorem exists_original_space_calibrations
    (ω : KahlerBackground (m+1) X)
    (T : ClosedOneOneCurrent (M := X) (canonicalBasis (m+1)) (Nat.succ_pos m))
    (hT : IsFullPositive T.val) {ε : ℝ} (hε : 0 < ε) :
    ∃ (θ : ClosedRealOneOneForm (m+1) X),
      RealBottChern.ofRepresentative θ =
        bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T ∧
      ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m+1)) Y)
        (_ : IsComplexManifold (m+1) Y) (π : Y → X)
        (hπ : IsBlowupSequence (m+1) X Y π) (_ : CompactSpace Y)
        (_ : ConnectedSpace Y) (ωY : KahlerBackground (m+1) Y)
        (F : MeteredEffectiveQDivisor (m+1) Y),
        letI : MeasurableSpace Y := borel Y
        haveI : BorelSpace Y := ⟨rfl⟩
        let β := ClosedRealOneOneForm.pullback hπ.contMDiff (θ + ε • ω.form) - F.curvature
        (∀ Ω : KahlerBackground (m+1) Y, NefWithRespectTo Ω β) ∧
        globalACtopMeasure T.val hT univ ≤ ENNReal.ofReal (slotIntegral ωY (fun _ => β)) ∧
        ∀ (δ : ℝ), 0 < δ → ∃ (Ω : KahlerBackground (m+1) Y),
          Ω.form = ClosedRealOneOneForm.pullback hπ.contMDiff ω.form + δ • ωY.form ∧
          ∃ (s : X → EReal) (hs : IsThetaPshPotential (θ + ε • ω.form).val s),
            0 ≤ slotIntegral ωY (fun _ => β) / (kahlerVolume Ω).real univ ∧
            bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m)
              (thetaClosedCurrent (θ + ε • ω.form) s hs) =
              bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T +
                ε • RealBottChern.ofRepresentative ω.form ∧
            globalACtopMeasure
                (thetaPotentialCurrent (θ + ε • ω.form).val s hs)
                (fun e α hα => thetaPotentialCurrent_full_positive
                  (θ + ε • ω.form).val s hs e α hα) =
              ENNReal.ofReal (slotIntegral ωY (fun _ => β) / (kahlerVolume Ω).real univ) •
                (kahlerVolume Ω).map π := by
  classical
  obtain ⟨θ, _v, _hv, hclass, _han, Y, tY, cY, mY, π, hπ, hcpt, hconn, ωY, F,
      hnef, hmajor, hfamily⟩ :=
    ResolvedNefCalabiYauDescent.exists_resolved_calabi_yau_descents ω T hT hε
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  let β := ClosedRealOneOneForm.pullback hπ.contMDiff (θ + ε • ω.form) - F.curvature
  have hπa := isAnalyticModification_of_isBlowupSequence hπ
  refine ⟨θ, hclass, Y, tY, cY, mY, π, hπ, hcpt, hconn, ωY, F, hnef, hmajor, ?_⟩
  intro δ hδ
  obtain ⟨Ω, hΩ, R, hR, ψ, hψ, s, hs, hread, _hRclass, hc, hcal, hsw, hSclass⟩ :=
    hfamily δ hδ
  obtain ⟨huY, hmap⟩ :=
    ThetaCurrentModificationGlobalACTransport.exists_global_original_ac_transport
      hπa (θ + ε • ω.form) hs
  let θY := ClosedRealOneOneForm.pullback hπa.1 (θ + ε • ω.form)
  have hF : LocallyNondegenerate F.weight := by
    intro y U hU hyU
    obtain ⟨q, hqU, hq⟩ := huY.2 y U hU hyU
    refine ⟨q, hqU, fun hbot => hq ?_⟩
    change s (π q) = ⊥
    rw [hsw q, hbot, EReal.bot_add]
  obtain ⟨hw, hS, hR', _hadd, _hforms, hAC⟩ :=
    MeteredDivisorResidualACMeasure.exists_weight_add_current_ac_invariance F hF θY hψ
  have heq : (fun y => s (π y)) = (fun y => F.weight y + ψ y) := funext hsw
  have hcurr := thetaPotentialCurrent_congr θY huY hw heq
  have hY : IsFullPositive
      (thetaPotentialCurrent θY.val (fun y => s (π y)) huY) := fun e α hα =>
    thetaPotentialCurrent_full_positive θY.val _ huY e α hα
  have hACR : globalACtopMeasure
      (thetaPotentialCurrent θY.val (fun y => s (π y)) huY) hY =
      globalACtopMeasure R.val hR :=
    (globalACtopMeasure_congr hY hS hcurr).trans
      (hAC.trans (globalACtopMeasure_congr hR' hR hread.symm))
  refine ⟨Ω, hΩ, s, hs, hc, hSclass, ?_⟩
  calc
    globalACtopMeasure (thetaPotentialCurrent (θ + ε • ω.form).val s hs)
        (fun e α hα => thetaPotentialCurrent_full_positive
          (θ + ε • ω.form).val s hs e α hα) =
        (globalACtopMeasure
          (thetaPotentialCurrent θY.val (fun y => s (π y)) huY) hY).map π := hmap.symm
    _ = (globalACtopMeasure R.val hR).map π := congrArg (fun μ : Measure Y => μ.map π) hACR
    _ = (ENNReal.ofReal (slotIntegral ωY (fun _ => β) / (kahlerVolume Ω).real univ) •
        kahlerVolume Ω).map π := congrArg (fun μ : Measure Y => μ.map π) hcal
    _ = _ := Measure.map_smul _ _ _

end SGPT.Foundations.Analysis.Pending.ResolvedOriginalACCalibration
