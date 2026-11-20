import SGPT.Foundations.Analysis.Pending.NefMixedMass
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone
import SGPT.Foundations.Analysis.Pending.ThetaCurrentGlobalACDomination
import SGPT.Foundations.Analysis.Pending.PositiveCurrentPrescribedBottChernRepresentation

set_option autoImplicit false

/-! Full BP statements and ENTIRE proofs saved before Lean. Genuine sharp
nef upper bounds for arbitrary unbounded/nonanalytic potentials and ALL
original full-positive closed currents. No supplied correction, smoothing,
density, mass or convergence certificate. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.NefOriginalCurrentSharpACMass
open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  NefMixedMass GlobalNonPluripolar MixedMass GlobalMixedMassMonotone
  AmbientMassBackgroundMonotone ManifoldTubePositivity GlobalPotentialTransforms
  CurrentBottChernClass CanonicalCurrentFrame GlobalCurrentPotentials
  GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  NaturalThetaPshGeometricCurrent PositiveCurrentPrescribedBottChernRepresentation
  ThetaCurrentGlobalACDomination
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]

private theorem smooth_np_mass_eq_intersection
    (ω : KahlerBackground (m+1) M) (σ : ClosedRealOneOneForm (m+1) M)
    (f : M → ℝ) (hf : ChartSmooth (n := m+1) f)
    (hfpsh : ThetaPlurisubharmonic σ.val (fun x => (f x : EReal))) :
    globalMixedMass (fun _ : Fin (m+1) => σ) (fun _ x => (f x : EReal))
      (fun _ => hfpsh) = ENNReal.ofReal (slotIntegral ω (fun _ => σ)) := by
  let η := σ + ddcClosedForm f hf
  have hη : η.val.IsSemipositive := fun e z hz v => by
    have h := (LocalPotentials.thetaPlurisubharmonic_smooth_iff σ f hf).mp hfpsh e z hz v
    simpa only [η,ClosedRealOneOneForm.coeff_add,ddcClosedForm_coeff,
      ContinuousAlternatingMap.add_apply] using h
  have hη0 : ∀ _ : Fin (m+1), ThetaPlurisubharmonic η.val (fun _ => 0) :=
    fun _ => (LocalPotentials.thetaPlurisubharmonic_zero_iff η).mpr hη
  have hchange := globalMixedMass_changeRepresentative (θ := fun _ : Fin (m+1) => σ)
    (η := fun _ => η) (f := fun _ => f) (fun _ => hf)
    (fun _ e z _ => by simp only [η,ClosedRealOneOneForm.coeff_add,ddcClosedForm_coeff])
    (fun _ => hfpsh)
  have hzero : (fun (_ : Fin (m+1)) x => ((f x : ℝ) : EReal) - ((f x : ℝ) : EReal)) =
      fun (_ : Fin (m+1)) (_ : M) => (0 : EReal) := by
    funext i x
    rw [← EReal.coe_sub,sub_self,EReal.coe_zero]
  have htransformed : ∀ _ : Fin (m+1), ThetaPlurisubharmonic η.val
      (fun x => (f x : EReal) - (f x : EReal)) := by
    simpa only [← EReal.coe_sub,sub_self,EReal.coe_zero] using hη0
  have hsame := congrArg (fun μ : Measure M => μ univ)
    (globalMixedMeasure_congr_tuples rfl hzero htransformed hη0)
  have hsameMass : globalMixedMass (fun _ : Fin (m+1) => η)
      (fun _ x => (f x : EReal) - (f x : EReal)) htransformed =
      globalMixedMass (fun _ => η) (fun _ _ => 0) hη0 := hsame
  have hreal : (globalMixedMass (fun _ : Fin (m+1) => σ)
      (fun _ x => (f x : EReal)) (fun _ => hfpsh)).toReal =
      slotIntegral ω (fun _ => σ) := by
    rw [← hchange,hsameMass]
    have hsm := MixedMassClassInvariance.globalMixedMeasure_real_univ_eq_integral ω
      (fun _ => η) hη0
    change (globalMixedMeasure (fun _ => η) (fun _ _ => 0) hη0).real univ = _
    rw [hsm]
    change slotIntegral ω (fun _ => η) = _
    exact slotIntegral_add_ddc ω (fun _ => σ) (fun _ => f) (fun _ => hf)
  rw [← hreal]
  exact (ENNReal.ofReal_toReal (globalMixedMass_lt_top ω (fun _ => hfpsh)).ne).symm

private theorem perturbed_mass_bound
    (ω : KahlerBackground (m+1) M) (θ : ClosedRealOneOneForm (m+1) M)
    (hnef : NefWithRespectTo ω θ) {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {ε : ℝ} (hε : 0 < ε) :
    globalMixedMass (fun _ : Fin (m+1) => θ) (fun _ => u) (fun _ => hu.1) ≤
      ENNReal.ofReal (slotIntegral ω (fun _ => θ + ε • ω.form)) := by
  obtain ⟨f,hf,hsemi⟩ := exists_isSemipositive_of_nef hnef hε
  have hfpsh : ThetaPlurisubharmonic (θ + ε • ω.form).val (fun x => (f x : EReal)) := by
    apply (LocalPotentials.thetaPlurisubharmonic_smooth_iff _ f hf).mpr
    intro e z hz v
    have h := hsemi e z hz v
    simpa only [ClosedRealOneOneForm.coeff_add,ddcClosedForm_coeff,
      ContinuousAlternatingMap.add_apply] using h
  have hfpot : IsThetaPshPotential (θ + ε • ω.form).val (fun x => (f x : EReal)) :=
    ⟨hfpsh,fun x _ _ hx => ⟨x,hx,EReal.coe_ne_bot _⟩⟩
  have hue : IsThetaPshPotential (θ + ε • ω.form).val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul ω.isSemipositive hε.le)
  have hupper : ∃ B : ℝ, ∀ x, u x ≤ (B : EReal) := by
    cases isEmpty_or_nonempty M with
    | inl h =>
      let := h
      exact ⟨0,fun x => isEmptyElim x⟩
    | inr h =>
      let := h
      exact hu.exists_global_upper_bound
  obtain ⟨B,hB⟩ := hupper
  obtain ⟨L,hL⟩ := (isCompact_univ.image
    (CurrentTraceMeasure.chartSmooth_continuous hf)).bddBelow
  have horder : MoreSingularOn u (fun x => (f x : EReal)) univ := by
    refine ⟨B-L,fun x _ => ?_⟩
    have hc : L ≤ f x := hL ⟨x,mem_univ x,rfl⟩
    calc
      u x ≤ (B : EReal) := hB x
      _ ≤ ((f x + (B-L) : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
      _ = (f x : EReal) + ((B-L : ℝ) : EReal) := EReal.coe_add _ _
  have hbg := globalMixedMeasure_diagonal_le_add_smul ω.isSemipositive hε hu hue.1
  have hmass := globalMixedMass_mono_of_isThetaPshPotential ω
    (fun _ : Fin (m+1) => hue) (fun _ => hfpot) (fun _ => horder)
  exact (Measure.le_iff'.mp hbg univ).trans
    (hmass.trans_eq (smooth_np_mass_eq_intersection ω _ f hf hfpsh))

/-- Arbitrary genuine singular theta-PSH potentials in a nef class have the
sharp top NP mass upper bound, with no bounded/analytic/correction input. -/
theorem diagonal_np_mass_le_intersection_of_nef
    (ω : KahlerBackground (m+1) M) (θ : ClosedRealOneOneForm (m+1) M)
    (hnef : NefWithRespectTo ω θ) {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    globalMixedMass (fun _ : Fin (m+1) => θ) (fun _ => u) (fun _ => hu.1) ≤
      ENNReal.ofReal (slotIntegral ω (fun _ => θ)) := by
  let ε : ℕ → ℝ := fun j => 1 / (j+1 : ℝ)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlim := ((continuous_slotIntegral_add_smul ω (fun _ => θ) (fun _ => ω.form)).tendsto 0).comp hεlim
  have hENN := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  have hENN' : Tendsto (fun j => ENNReal.ofReal (slotIntegral ω (fun _ => θ + ε j • ω.form)))
      atTop (𝓝 (ENNReal.ofReal (slotIntegral ω (fun _ => θ)))) := by
    simpa only [Function.comp_def,zero_smul,add_zero] using hENN
  apply ge_of_tendsto hENN'
  exact Eventually.of_forall fun j => perturbed_mass_bound ω θ hnef hu (hε j)

private theorem global_ac_congr
    {T S : GlobalCurrent (m+1) M (degreeTwo (Nat.succ_pos m))}
    (hT : IsFullPositive T) (hS : IsFullPositive S) (heq : T = S) :
    globalACtopMeasure T hT = globalACtopMeasure S hS := by
  subst S
  rfl

/-- ALL original closed full-positive currents in the actual nef class have
the sharp canonical AC mass upper bound, with representation internal. -/
theorem original_ac_top_mass_le_intersection_of_nef
    (ω : KahlerBackground (m+1) M) (θ : ClosedRealOneOneForm (m+1) M)
    (hnef : NefWithRespectTo ω θ)
    (T : ClosedOneOneCurrent (M := M) (canonicalBasis (m+1)) (Nat.succ_pos m))
    (hT : IsFullPositive T.val)
    (hclass : bottChernClass (canonicalBasis (m+1)) (Nat.succ_pos m) T =
      RealBottChern.ofRepresentative θ) :
    globalACtopMeasure T.val hT univ ≤ ENNReal.ofReal (slotIntegral ω (fun _ => θ)) := by
  obtain ⟨u,hu,hEq,_hreader⟩ := exists_theta_representation_of_class_eq T θ hT hclass
  let hpos : IsFullPositive (thetaPotentialCurrent θ.val u hu) :=
    fun e α hα => thetaPotentialCurrent_full_positive θ.val u hu e α hα
  rw [global_ac_congr hT hpos hEq]
  have hAC := globalACtopMeasure_le_globalMixedMeasure ω θ hu
  exact (Measure.le_iff'.mp hAC univ).trans (diagonal_np_mass_le_intersection_of_nef ω θ hnef hu)

end SGPT.Foundations.Analysis.Pending.NefOriginalCurrentSharpACMass
