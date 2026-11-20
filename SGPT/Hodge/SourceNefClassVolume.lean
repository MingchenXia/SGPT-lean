import SGPT.Hodge.BDivChainDTVolume
import SGPT.Okounkov.TranscendentalVolumeConcavityContinuity
import SGPT.Okounkov.TranscendentalLiftingApprox
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.DiagonalMass
  SGPT.Foundations.Analysis.Pending.NefMixedMass
  SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
  SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
  SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Actual smooth semipositive class volume equals its genuine smooth top
intersection. No assertion is made about a singular original current. -/
theorem sourceClassVolume_semipositive_eq_slotIntegral
    (κ : KahlerBackground (m+1) X) (θ : ClosedRealOneOneForm (m+1) X)
    (hθ : θ.val.IsSemipositive) :
    (sourceClassVolume (RealBottChern.ofRepresentative θ)).toReal=
      slotIntegral κ (fun _ : Fin (m+1) => θ) := by
  have hp : IsThetaPshPotential θ.val (fun _ : X => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff _).mpr hθ
  have hv := SGPT.Hodge.BDivChain.sourceClassVolume_eq_mass_of_bounded κ θ hp 0
    (fun _ => by simp) (fun _ => le_rfl)
  rw [hv]
  change (SGPT.Foundations.Analysis.Pending.MixedMass.globalMixedMass
    (fun _ : Fin (m+1) => θ) (fun _ _ => (0 : EReal)) (fun _ => hp.1)).toReal= _
  exact globalMixedMass_toReal_eq_slotIntegral (Nat.succ_pos m) κ
    (fun _ => nefWithRespectTo_of_isSemipositive hθ) (fun _ => hp)
    (fun _ => ⟨0,0,fun _ => ⟨le_rfl,le_rfl⟩⟩)

/-- The ORIGINAL volume of EVERY genuine nef class is its actual smooth
cohomological top power, derived through real smooth nef approximations. -/
theorem sourceClassVolume_nef_eq_slotIntegral
    (κ : KahlerBackground (m+1) X) (θ : ClosedRealOneOneForm (m+1) X)
    (hθ : NefWithRespectTo κ θ) :
    (sourceClassVolume (RealBottChern.ofRepresentative θ)).toReal=
      slotIntegral κ (fun _ : Fin (m+1) => θ) := by
  let t : ℕ → ℝ := fun j => 1/((j : ℝ)+1)
  have ht j : 0<t j := by dsimp [t]; positivity
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hstage j : (sourceClassVolume (RealBottChern.ofRepresentative (θ+t j • κ.form))).toReal=
      slotIntegral κ (fun _ : Fin (m+1) => θ+t j • κ.form) := by
    obtain ⟨f,hf,hsemi⟩ := exists_isSemipositive_of_nef hθ (ht j)
    have hv := sourceClassVolume_semipositive_eq_slotIntegral κ
      (θ+t j • κ.form+ddcClosedForm f hf) hsemi
    rw [SGPT.Okounkov.TranscendentalLifting.ofRepresentative_add_ddc] at hv
    exact hv.trans (slotIntegral_add_ddc κ (fun _ : Fin (m+1) => θ+t j • κ.form)
      (fun _ => f) (fun _ => hf))
  have hvol : Tendsto (fun j => sourceClassVolume
      (RealBottChern.ofRepresentative (θ+t j • κ.form))) atTop
      (𝓝 (sourceClassVolume (RealBottChern.ofRepresentative θ))) := by
    have h := (SGPT.Okounkov.TranscendentalVolumeConcavity.continuous_sourceClassVolume_add_smul κ
      (RealBottChern.ofRepresentative θ) (RealBottChern.ofRepresentative κ.form)).continuousAt.tendsto.comp ht0
    simpa only [RealBottChern.ofRepresentative_add,RealBottChern.ofRepresentative_smul,
      zero_smul,add_zero,Function.comp_def] using h
  have hreal := (ENNReal.tendsto_toReal
    (SGPT.Okounkov.TranscendentalVolumeConcavity.sourceClassVolume_lt_top κ _).ne).comp hvol
  have hcoh : Tendsto (fun j => slotIntegral κ (fun _ : Fin (m+1) => θ+t j • κ.form)) atTop
      (𝓝 (slotIntegral κ (fun _ : Fin (m+1) => θ))) := by
    have h := (continuous_slotIntegral_add_smul κ (fun _ : Fin (m+1) => θ)
      (fun _ => κ.form)).continuousAt.tendsto.comp ht0
    simpa only [zero_smul,add_zero,Function.comp_def] using h
  exact tendsto_nhds_unique (hreal.congr' (Eventually.of_forall hstage)) hcoh

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
