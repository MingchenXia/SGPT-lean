import SGPT.Hodge.SourceSmoothMixedCohomology
import SGPT.Hodge.SourceNefIntersection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.NefMixedMass
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetRealDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

/-- The ACTUAL smooth cohomological integral on an actual original model,
with its literal Borel structure; it is independent of b-divisor volumes. -/
def modelSlotIntegral (π : (ModelSystem.blowup (m+1) X).Model)
    (κ : KahlerBackground (m+1) π.1.carrier)
    (θ : Fin (m+1) → ClosedRealOneOneForm (m+1) π.1.carrier) : ℝ := by
  letI : MeasurableSpace π.1.carrier := borel π.1.carrier
  letI : BorelSpace π.1.carrier := ⟨rfl⟩
  exact slotIntegral κ θ

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Actual nef Cartier realization witnesses give the unchanged net-nef predicate. -/
theorem isNefAny_of_nef_realization (D : WeilFamilyAny Sys)
    (π : (ModelSystem.blowup (m+1) X).Model)
    (κ : KahlerBackground (m+1) π.1.carrier)
    (θ : ClosedRealOneOneForm (m+1) π.1.carrier)
    (hr : IsRealizationAny D π (RealBottChern.ofRepresentative θ))
    (hθ : NefWithRespectTo κ θ) : IsNefAny D :=
  isNefAny_of_isNefCartierAny ⟨π,RealBottChern.ofRepresentative θ,hr,κ,hθ⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- The ORIGINAL pure volume of a genuine nef Cartier realization is its
actual smooth cohomological top integral on THAT SAME original model. -/
theorem volumeRealAny_of_nef_realization (ω : KahlerBackground (m+1) X)
    (D : WeilFamilyAny Sys) (π : (ModelSystem.blowup (m+1) X).Model)
    (κ : KahlerBackground (m+1) π.1.carrier)
    (θ : ClosedRealOneOneForm (m+1) π.1.carrier)
    (hr : IsRealizationAny D π (RealBottChern.ofRepresentative θ))
    (hθ : NefWithRespectTo κ θ) :
    volumeRealAny D=modelSlotIntegral π κ (fun _ : Fin (m+1) => θ) := by
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  let : BorelSpace π.1.carrier := ⟨rfl⟩
  let : ConnectedSpace π.1.carrier := Modification.IsBlowupModel.connectedSpace π.2
  have hp := isPseudoeffectiveAny_of_isNef ω D (isNefAny_of_nef_realization D π κ θ hr hθ)
  have hrex := (isRealizationAny_iff_existing (Nat.succ_pos m) D π _).mp hr
  have hmodel : D.val π=RealBottChern.ofRepresentative θ := hrex.onModel_eq
  have hpθ : ClassPseudoeffectiveViaPotentials (RealBottChern.ofRepresentative θ) := by
    rw [←hmodel]
    exact hp π
  obtain ⟨b,hb⟩ := (classPseudoeffectiveViaPotentials_ofRepresentative θ).mp hpθ
  have hv : volumeAny D=Modification.classVolume π.1 (RealBottChern.ofRepresentative θ) := by
    rw [volumeAny_eq_existing (Nat.succ_pos m)]
    exact SGPT.Hodge.BDivChain.vol_eq_classVolume_of_isRealization ⟨ω⟩
      ((isPseudoeffectiveAny_iff_existing (Nat.succ_pos m) D).mp hp) hrex hb
  calc volumeRealAny D=(Modification.classVolume π.1 (RealBottChern.ofRepresentative θ)).toReal :=
        congrArg ENNReal.toReal hv
    _ = modelSlotIntegral π κ (fun _ : Fin (m+1) => θ) :=
        sourceClassVolume_nef_eq_slotIntegral κ θ hθ

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Finite original families sharing a genuine realization retain that
realization under ACTUAL addition of their smooth quotient classes. -/
theorem isRealizationAny_sum {I : Type*} (S : Finset I) (D : I → WeilFamilyAny Sys)
    (π : (ModelSystem.blowup (m+1) X).Model)
    (θ : I → ClosedRealOneOneForm (m+1) π.1.carrier)
    (hr : ∀ i ∈ S,IsRealizationAny (D i) π (RealBottChern.ofRepresentative (θ i))) :
    IsRealizationAny (∑ i ∈ S,D i) π (RealBottChern.ofRepresentative (∑ i ∈ S,θ i)) := by
  intro ρ hπρ
  rw [family_sum_onModel]
  change (∑ i ∈ S,(D i).val ρ)=
    (Modification.classPullbackOfLE (show π.1≤ρ.1 from hπρ))
      (RealBottChern.ofRepresentativeLinearMap (∑ i ∈ S,θ i))
  rw [map_sum,map_sum]
  exact Finset.sum_congr rfl (fun i hi => hr i hi ρ hπρ)

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem nefWithRespectTo_finset_sum
    (π : (ModelSystem.blowup (m+1) X).Model) (κ : KahlerBackground (m+1) π.1.carrier)
    {I : Type*} (S : Finset I) (θ : I → ClosedRealOneOneForm (m+1) π.1.carrier)
    (hθ : ∀ i ∈ S,NefWithRespectTo κ (θ i)) : NefWithRespectTo κ (∑ i ∈ S,θ i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact nefWithRespectTo_zero κ
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact nefWithRespectTo_add κ (hθ a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hθ i (Finset.mem_insert_of_mem hi)))

/-- The genuine original all-nef intersection of EVERY nef Cartier tuple
on ONE actual original realization equals its ordinary smooth cohomology
integral. No target mixed reader or original-NPP-fullness certificate is input. -/
theorem nefIntersection_of_common_nef_realization (ω : KahlerBackground (m+1) X)
    (D : Fin (m+1) → WeilFamilyAny Sys)
    (π : (ModelSystem.blowup (m+1) X).Model) (κ : KahlerBackground (m+1) π.1.carrier)
    (θ : Fin (m+1) → ClosedRealOneOneForm (m+1) π.1.carrier)
    (hr : ∀ i,IsRealizationAny (D i) π (RealBottChern.ofRepresentative (θ i)))
    (hθ : ∀ i,NefWithRespectTo κ (θ i)) :
    (nefIntersection D).toReal=modelSlotIntegral π κ θ := by
  let : MeasurableSpace π.1.carrier := borel π.1.carrier
  let : BorelSpace π.1.carrier := ⟨rfl⟩
  have hD i : IsNefAny (D i) := isNefAny_of_nef_realization (D i) π κ (θ i) (hr i) (hθ i)
  have hv (S : Finset (Fin (m+1))) : volumeRealAny (∑ i ∈ S,D i)=
      modelSlotIntegral π κ (fun _ : Fin (m+1) => ∑ i ∈ S,θ i) :=
    volumeRealAny_of_nef_realization ω _ π κ _
      (isRealizationAny_sum S D π θ (fun i _ => hr i))
      (nefWithRespectTo_finset_sum π κ S θ (fun i _ => hθ i))
  have hpol : familyVolumePolarization D=((m+1).factorial : ℝ)*modelSlotIntegral π κ θ := by
    unfold familyVolumePolarization
    simp_rw [hv]
    exact (factorial_mul_slotIntegral_eq_polarization κ θ).symm
  change (ENNReal.ofReal (nefIntersectionReal D)).toReal=modelSlotIntegral π κ θ
  rw [ENNReal.toReal_ofReal (nefIntersectionReal_nonneg ω D hD)]
  unfold nefIntersectionReal
  rw [hpol]
  have hn : ((m+1).factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (m+1)
  exact mul_div_cancel_left₀ (modelSlotIntegral π κ θ) hn

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
