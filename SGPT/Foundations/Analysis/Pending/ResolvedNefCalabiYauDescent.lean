import SGPT.Foundations.Analysis.Pending.OriginalCurrentAnalyticACMajorization
import SGPT.Foundations.Analysis.Pending.NefOriginalCurrentCalabiYau
import SGPT.Foundations.Analysis.Pending.DominationResidualMass
import SGPT.Foundations.Analysis.Pending.DivisorialDomination
import SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass

set_option autoImplicit false

/-! The complete mathematical statement and ENTIRE proof precede Lean.
ANY original positive closed current internally supplies one analytic
resolution and ALL positive-delta nef-CY descent currents. Calibration is
upstairs only; no nonanalytic downstairs AC transport or general CY closure.
Source: Boucksom 4.6, with a bounded residual replacing a neat residual. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
universe u
namespace SGPT.Foundations.Analysis.Pending.ResolvedNefCalabiYauDescent
open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.GlobalAnalyticSingularities FirstPass.BlowupSequences
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.HolomorphicIdealSheaves
  DiagonalMass GlobalNonPluripolar ManifoldTubePositivity MixedNonPluripolar
  IntegrationCurrent BoundedGlobalProduct
  MixedMass NefMixedMass CurrentBottChernClass CanonicalCurrentFrame GlobalCurrentPotentials
  GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
  ThetaPotentialCurrentBottChernClass
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X]

/-- ANY original positive closed current internally supplies one resolution
and ALL positive reference-perturbation CY currents together with their
genuine original-space descent. The exact calibration is upstairs only. -/
theorem exists_resolved_calabi_yau_descents
    (ω : KahlerBackground (m+1) X)
    (T : ClosedOneOneCurrent (M := X) (canonicalBasis (m+1)) (Nat.succ_pos m))
    (hT : IsFullPositive T.val) {ε : ℝ} (hε : 0 < ε) :
    ∃ (θ : ClosedRealOneOneForm (m+1) X) (v : X → EReal)
      (_ : IsThetaPshPotential (θ + ε • ω.form).val v),
      RealBottChern.ofRepresentative θ =
        bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T ∧
      HasAnalyticSingularities (n := m+1) v ∧
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
          ∃ (R : ClosedOneOneCurrent (M := Y) (canonicalBasis (m+1)) (Nat.succ_pos m))
            (hR : IsFullPositive R.val) (ψ : Y → EReal)
            (hψ : IsThetaPshPotential β.val ψ) (s : X → EReal)
            (hs : IsThetaPshPotential (θ + ε • ω.form).val s),
            R.val = thetaPotentialCurrent β.val ψ hψ ∧
            bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) R =
              RealBottChern.ofRepresentative β ∧
            0 ≤ slotIntegral ωY (fun _ => β) / (kahlerVolume Ω).real univ ∧
            globalACtopMeasure R.val hR =
              ENNReal.ofReal (slotIntegral ωY (fun _ => β) / (kahlerVolume Ω).real univ) •
                kahlerVolume Ω ∧
            (∀ y, s (π y) = F.weight y + ψ y) ∧
            bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m)
              (thetaClosedCurrent (θ + ε • ω.form) s hs) =
              bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T +
                ε • RealBottChern.ofRepresentative ω.form := by
  classical
  obtain ⟨θ,v,hv,hclass,han,hsmooth,_hSclass,hmajor⟩ :=
    OriginalCurrentAnalyticACMajorization.exists_analytic_positive_current_ac_mass_majorant
      ω T hT hε
  obtain ⟨c,𝔞,htype⟩ := han
  obtain ⟨Y,tY,cY,mY,π,hπ,hcpt,hconn,⟨ωY⟩,hpot,F,L,b,hb,hblow,hbupp,
      _hboff,hnef,hmass⟩ :=
    DominationResidualMass.exists_logResolution_mass (Nat.succ_pos m) ω
      (θ + ε • ω.form) hv htype
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  let β := ClosedRealOneOneForm.pullback hπ.contMDiff (θ + ε • ω.form) - F.curvature
  have hbB : IsBoundedPotential b := ⟨-L.bound,L.bound,fun y => ⟨hblow y,hbupp y⟩⟩
  have hI := NefBoundedMixedMass.globalMixedMass_toReal_eq_slotIntegral (Nat.succ_pos m) ωY
    (θ := fun _ => β) (fun _ => hnef ωY) (u := fun _ => b)
    (fun _ => hb) (fun _ => hbB)
  have hmassI : diagonalPotentialMass β b hb =
      ENNReal.ofReal (slotIntegral ωY (fun _ => β)) := by
    change globalMixedMass (fun _ => β) (fun _ => b) (fun _ => hb.1) = _
    rw [← hI,ENNReal.ofReal_toReal (globalMixedMass_lt_top ωY (fun _ => hb.1)).ne]
  have hAC := congrArg (fun ν : Measure X => ν univ)
    (OriginalCurrentAnalyticACMajorization.globalACtopMeasure_theta_analytic_eq
      (θ + ε • ω.form) hv hsmooth)
  have hmajorI : globalACtopMeasure T.val hT univ ≤
      ENNReal.ofReal (slotIntegral ωY (fun _ => β)) := by
    have hM : globalACtopMeasure
        (thetaPotentialCurrent (θ + ε • ω.form).val v hv)
        (fun e α hα => thetaPotentialCurrent_full_positive
          (θ + ε • ω.form).val v hv e α hα) univ =
        diagonalPotentialMass (θ + ε • ω.form) v hv := hAC
    exact hmajor.trans_eq (hM.trans (hmass.symm.trans hmassI))
  have hF : LocallyNondegenerate F.weight := by
    intro y U hU hyU
    obtain ⟨y',hy'U,hy'⟩ := hpot.2 y U hU hyU
    refine ⟨y',hy'U,fun hbot => hy' ?_⟩
    change v (π y') = ⊥
    rw [L.weight_add y',hbot,EReal.bot_add]
  refine ⟨θ,v,hv,hclass,⟨c,𝔞,htype⟩,Y,tY,cY,mY,π,hπ,hcpt,hconn,ωY,F,hnef,hmajorI,?_⟩
  intro δ hδ
  let Ω : KahlerBackground (m+1) Y :=
    ⟨ClosedRealOneOneForm.pullback hπ.contMDiff ω.form + δ • ωY.form,
      NefCoreKahlerCurrent.isKahler_add_smul_of_isSemipositive ωY
        (ClosedRealOneOneForm.pullback_isSemipositive hπ.contMDiff ω.isSemipositive) hδ⟩
  have hIΩ := NefBoundedMixedMass.globalMixedMass_toReal_eq_slotIntegral (Nat.succ_pos m) Ω
    (θ := fun _ => β) (fun _ => hnef Ω) (u := fun _ => b)
    (fun _ => hb) (fun _ => hbB)
  have hsame : slotIntegral Ω (fun _ => β) = slotIntegral ωY (fun _ => β) :=
    hIΩ.symm.trans hI
  obtain ⟨hc,R,hR,hRclass,hcal⟩ :=
    NefOriginalCurrentCalabiYau.exists_nef_original_current_calabi_yau Ω β (hnef Ω)
  rw [hsame] at hc hcal
  obtain ⟨ψ,hψ,hread,_hchart⟩ :=
    PositiveCurrentPrescribedBottChernRepresentation.exists_theta_representation_of_class_eq
      R β hR hRclass
  have hw : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback hπ.contMDiff (θ + ε • ω.form)).val
        (fun y => F.weight y + ψ y) :=
    DivisorialDomination.isThetaPshPotential_weight_add F hF hψ
  obtain ⟨s,hs,hsw⟩ :=
    BlowupSequencePotentialDescent.exists_descent_of_isBlowupSequence hπ
      (θ + ε • ω.form) hw
  refine ⟨Ω,rfl,R,hR,ψ,hψ,s,hs,hread,hRclass,hc,hcal,hsw,?_⟩
  rw [bottChernClass_thetaClosedCurrent,RealBottChern.ofRepresentative_add,
    RealBottChern.ofRepresentative_smul,hclass]

end SGPT.Foundations.Analysis.Pending.ResolvedNefCalabiYauDescent
