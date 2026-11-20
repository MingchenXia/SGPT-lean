import SGPT.BBJ.CantorMultiplierEquivalence
import SGPT.BBJ.CantorZeroMass
import SGPT.PSH.SourceFullMassIGood
import SGPT.PSH.GlobalPComparison
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion

/-! Actual masses, envelopes and global singularity consequences of the Cantor average. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set MeasureTheory SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass
open scoped Topology ENNReal Classical
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "ω" => projectiveNativeFSBackground.form
local notation "Θ" => projectiveNativeFSBackground.form + projectiveNativeFSBackground.form

/-- Genuine native zero FS-PSH from the original Bool-chart producer. -/
theorem isThetaPshPotential_projectiveZero :
    IsThetaPshPotential (ω).val (fun _ : P1 => 0) :=
  isThetaPshPotential_projectiveNativeFS_of_source isThetaPSH_projectiveZero

/-- The same Cantor potential is genuinely PSH in the actual doubled background. -/
theorem isThetaPshPotential_cantorLogPotential_double :
    IsThetaPshPotential (Θ).val cantorLogPotential :=
  SGPT.Foundations.Analysis.Pending.LocalPotentials.isThetaPshPotential_add_of_semipositive
    isThetaPshPotential_cantorLogPotential projectiveNativeFSBackground.isSemipositive

/-- Genuine zero PSH in the same doubled background. -/
theorem isThetaPshPotential_projectiveZero_double :
    IsThetaPshPotential (Θ).val (fun _ : P1 => 0) :=
  SGPT.Foundations.Analysis.Pending.LocalPotentials.isThetaPshPotential_add_of_semipositive
    isThetaPshPotential_projectiveZero projectiveNativeFSBackground.isSemipositive

/-- Actual FS normalization, obtained from the existing log-log measure and envelope. -/
theorem diagonalPotentialMass_projectiveZero :
    diagonalPotentialMass ω (fun _ : P1 => 0) isThetaPshPotential_projectiveZero = 1 := by
  have hℓ := isThetaPshPotential_projectiveLogLogPotential
  have hP := SGPT.Foundations.Analysis.FirstPass.singularityEnvelope_isThetaPshPotential
    (ω).val (ω).property.1 (ω).property.2 hℓ.1.hasSmoothLocalPotentials projectiveLogLogPotential hℓ
  calc
    diagonalPotentialMass ω (fun _ : P1 => 0) isThetaPshPotential_projectiveZero =
        diagonalPotentialMass ω (singularityEnvelope (ω).val projectiveLogLogPotential) hP :=
      (diagonalPotentialMass_congr projectiveLogLog_nativeEnvelope_eq_zero hP
        isThetaPshPotential_projectiveZero).symm
    _ = diagonalPotentialMass ω projectiveLogLogPotential hℓ :=
      singularityEnvelopeMassPreserving projectiveNativeFSBackground ω
        projectiveLogLogPotential hℓ hP
    _ = 1 := projectiveLogLogNonPluripolarMeasure_univ

private theorem update_fin_one {X : Type*} (f : Fin 1 → X) (a : X) :
    Function.update f 0 a = fun _ => a := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact Function.update_self _ _ _

private theorem diagonalPotentialMeasure_double_add_zero {u : P1 → EReal}
    (hu : IsThetaPshPotential (ω).val u) (hd : IsThetaPshPotential (Θ).val u) :
    diagonalPotentialMeasure Θ u hd = diagonalPotentialMeasure ω u hu +
      diagonalPotentialMeasure ω (fun _ : P1 => 0) isThetaPshPotential_projectiveZero := by
  let f : Bool → P1 → EReal := fun i => if i then u else 0
  have hf : ∀ i, IsThetaPshPotential (ω).val (f i) := by
    intro i
    cases i
    · exact isThetaPshPotential_projectiveZero
    · exact hu
  have hp : ∀ k : Fin 1, k ≠ 0 →
      ThetaPlurisubharmonic ((fun _ : Fin 1 => ω) k).val ((fun _ : Fin 1 => u) k) := by
    intro k hk
    exact (hk (Fin.eq_zero k)).elim
  let hT : (Finset.univ : Finset Bool).Nonempty := ⟨false, Finset.mem_univ _⟩
  let hw : ∀ _ : Bool, (0 : ℝ) < 1 := fun _ => zero_lt_one
  have h := GlobalMultilinearExpansion.globalMixedMeasure_update_sum (0 : Fin 1) hp
    (T := Finset.univ) hT (w := fun _ => 1) hw
    (α := fun _ : Bool => ω) (fun i => (hf i).1)
    (fun i => ⟨(hf i).1.quasiPlurisubharmonic, (hf i).2⟩)
  have eform : GlobalMultilinearExpansion.sumForm (Finset.univ : Finset Bool)
      (fun _ => 1) (fun _ => ω) = Θ := by
    simp [GlobalMultilinearExpansion.sumForm, two_nsmul]
  have epot : GlobalMultilinearExpansion.sumPot (Finset.univ : Finset Bool)
      (fun _ => 1) f = u := by
    funext p
    simp [GlobalMultilinearExpansion.sumPot, f]
  have eLeft : GlobalNonPluripolar.globalMixedMeasure
      (Function.update (fun _ : Fin 1 => ω) 0
        (GlobalMultilinearExpansion.sumForm Finset.univ (fun _ => 1) (fun _ : Bool => ω)))
      (Function.update (fun _ : Fin 1 => u) 0
        (GlobalMultilinearExpansion.sumPot Finset.univ (fun _ => 1) f))
      (GlobalMultilinearExpansion.update_thetaPlurisubharmonic hp
        (GlobalMultilinearExpansion.thetaPlurisubharmonic_sumPot hT hw (fun i => (hf i).1))) =
        diagonalPotentialMeasure Θ u hd := by
    exact GlobalDiagonalScaling.globalMixedMeasure_congr
      (by rw [update_fin_one, eform]) (by rw [update_fin_one, epot]) _ _
  have eRight (i : Bool) : GlobalNonPluripolar.globalMixedMeasure
      (Function.update (fun _ : Fin 1 => ω) 0 ω)
      (Function.update (fun _ : Fin 1 => u) 0 (f i))
      (GlobalMultilinearExpansion.update_thetaPlurisubharmonic hp (hf i).1) =
        diagonalPotentialMeasure ω (f i) (hf i) := by
    exact GlobalDiagonalScaling.globalMixedMeasure_congr
      (update_fin_one _ _) (update_fin_one _ _) _ _
  have h' := eLeft.symm.trans h
  simp_rw [eRight] at h'
  simpa [f, Pi.zero_def] using h'


/-- The actual doubled-background Cantor NP measure is the actual zero FS measure. -/
theorem diagonalPotentialMeasure_cantorLogPotential_double :
    diagonalPotentialMeasure Θ cantorLogPotential isThetaPshPotential_cantorLogPotential_double =
      diagonalPotentialMeasure ω (fun _ : P1 => 0) isThetaPshPotential_projectiveZero := by
  rw [diagonalPotentialMeasure_double_add_zero isThetaPshPotential_cantorLogPotential,
    diagonalPotentialMeasure_cantorLogPotential_eq_zero, zero_add]

/-- The same Cantor potential has actual positive doubled-background mass one. -/
theorem diagonalPotentialMass_cantorLogPotential_double :
    diagonalPotentialMass Θ cantorLogPotential isThetaPshPotential_cantorLogPotential_double =
      1 := by
  exact (congrArg (fun μ : Measure P1 => μ univ)
    diagonalPotentialMeasure_cantorLogPotential_double).trans diagonalPotentialMass_projectiveZero

/-- The actual zero potential in the doubled background has mass two. -/
theorem diagonalPotentialMass_projectiveZero_double :
    diagonalPotentialMass Θ (fun _ : P1 => 0) isThetaPshPotential_projectiveZero_double = 2 := by
  have h := congrArg (fun μ : Measure P1 => μ univ)
    (diagonalPotentialMeasure_double_add_zero isThetaPshPotential_projectiveZero
      isThetaPshPotential_projectiveZero_double)
  simpa only [Measure.add_apply, diagonalPotentialMeasure_univ,
    diagonalPotentialMass_projectiveZero, one_add_one_eq_two] using h

/-- The genuine native FS multiplier envelope of the same Cantor average is zero. -/
theorem iSingularityEnvelope_cantorLogPotential_eq_zero :
    IEnvelope.iSingularityEnvelope (ω).val cantorLogPotential = 0 :=
  le_antisymm (IEnvelope.iSingularityEnvelope_le_zero _ _)
    (IEnvelope.le_iSingularityEnvelope isThetaPshPotential_projectiveZero le_rfl
      iEquivalentOnManifold_cantorLogPotential_zero.symm)

/-- The genuine native multiplier envelope remains zero in the doubled background. -/
theorem iSingularityEnvelope_cantorLogPotential_double_eq_zero :
    IEnvelope.iSingularityEnvelope (Θ).val cantorLogPotential = 0 :=
  le_antisymm (IEnvelope.iSingularityEnvelope_le_zero _ _)
    (IEnvelope.le_iSingularityEnvelope isThetaPshPotential_projectiveZero_double le_rfl
      iEquivalentOnManifold_cantorLogPotential_zero.symm)

/-- Genuine original Bool-atlas zero PSH in the literal doubled original FS form. -/
theorem isThetaPSH_projectiveZero_double :
    projectiveLineAtlas.IsThetaPSH (projectiveFSForm.add projectiveFSForm)
      (fun _ : P1 => 0) := by
  simpa only [zero_add] using
    SGPT.PSH.VariableComplexAtlas.IsThetaPSH.add
      isThetaPSH_projectiveZero isThetaPSH_projectiveZero

/-- The same original Cantor potential is PSH in that doubled original background. -/
theorem isThetaPSH_cantorLogPotential_double :
    projectiveLineAtlas.IsThetaPSH (projectiveFSForm.add projectiveFSForm)
      cantorLogPotential := by
  simpa only [add_zero] using
    SGPT.PSH.VariableComplexAtlas.IsThetaPSH.add
      isThetaPSH_cantorLogPotential isThetaPSH_projectiveZero

/-- Literal original Bool-atlas FS I-envelope, using its actual original competitors. -/
theorem sourceIEnvelope_cantorLogPotential_eq_zero :
    SGPT.PSH.VariableComplexAtlas.sourceIEnvelope projectiveFSForm cantorLogPotential = 0 :=
  le_antisymm (SGPT.PSH.VariableComplexAtlas.sourceIEnvelope_le_zero _ _)
    (SGPT.PSH.VariableComplexAtlas.le_sourceIEnvelope isThetaPSH_projectiveZero le_rfl
      (SGPT.PSH.VariableComplexAtlas.sourceIEquivalent_symm
        sourceIEquivalent_cantorLogPotential_zero))

/-- Literal original Bool-atlas doubled I-envelope; no fixed-atlas identification is used. -/
theorem sourceIEnvelope_cantorLogPotential_double_eq_zero :
    SGPT.PSH.VariableComplexAtlas.sourceIEnvelope (projectiveFSForm.add projectiveFSForm)
      cantorLogPotential = 0 :=
  le_antisymm (SGPT.PSH.VariableComplexAtlas.sourceIEnvelope_le_zero _ _)
    (SGPT.PSH.VariableComplexAtlas.le_sourceIEnvelope isThetaPSH_projectiveZero_double le_rfl
      (SGPT.PSH.VariableComplexAtlas.sourceIEquivalent_symm
        sourceIEquivalent_cantorLogPotential_zero))

/-- Actual native I-volume in the doubled positive background equals two. -/
theorem iVolume_cantorLogPotential_double :
    iVolume Θ isThetaPshPotential_cantorLogPotential_double.1.hasSmoothLocalPotentials
      cantorLogPotential isThetaPshPotential_cantorLogPotential_double = 2 := by
  unfold iVolume
  exact (diagonalPotentialMass_congr iSingularityEnvelope_cantorLogPotential_double_eq_zero
    _ isThetaPshPotential_projectiveZero_double).trans diagonalPotentialMass_projectiveZero_double

/-- The actual native ordinary FS envelope cannot equal zero because its mass is zero. -/
theorem singularityEnvelope_cantorLogPotential_ne_zero :
    singularityEnvelope (ω).val cantorLogPotential ≠ 0 := by
  intro he
  have hP := SGPT.Foundations.Analysis.FirstPass.singularityEnvelope_isThetaPshPotential
    (ω).val (ω).property.1 (ω).property.2
    isThetaPshPotential_cantorLogPotential.1.hasSmoothLocalPotentials
    cantorLogPotential isThetaPshPotential_cantorLogPotential
  have hmass := singularityEnvelopeMassPreserving projectiveNativeFSBackground ω
    cantorLogPotential isThetaPshPotential_cantorLogPotential hP
  have hzero := diagonalPotentialMass_congr he hP isThetaPshPotential_projectiveZero
  have h := hzero.symm.trans hmass
  simp only [Pi.zero_def] at h
  rw [diagonalPotentialMass_projectiveZero,
    diagonalPotentialMass_cantorLogPotential_eq_zero] at h
  norm_num at h

private theorem sourceSingularityEnvelope_cantor_le_native :
    SGPT.PSH.VariableComplexAtlas.sourceSingularityEnvelope projectiveFSForm cantorLogPotential ≤
      singularityEnvelope (ω).val cantorLogPotential := by
  change uscRegularization (fun x =>
    ⨆ v : SGPT.PSH.VariableComplexAtlas.sourceSingularityCompetitors
      projectiveFSForm cantorLogPotential, v.1 x) ≤ _
  apply uscRegularization_le (upperSemicontinuous_singularityEnvelope _ _)
  intro x
  apply iSup_le
  intro v
  exact le_singularityEnvelope
    (isThetaPshPotential_projectiveNativeFS_of_source v.2.1) v.2.2.1 v.2.2.2 x

/-- The literal original Bool-atlas ordinary envelope is also nonzero. -/
theorem sourceSingularityEnvelope_cantorLogPotential_ne_zero :
    SGPT.PSH.VariableComplexAtlas.sourceSingularityEnvelope projectiveFSForm cantorLogPotential ≠
      0 := by
  intro he
  have hle := sourceSingularityEnvelope_cantor_le_native
  rw [he] at hle
  exact singularityEnvelope_cantorLogPotential_ne_zero
    (le_antisymm (singularityEnvelope_le_zero _ _) hle)

/-- Global native P-nonequivalence, tested in the genuine positive doubled background. -/
theorem not_nativeSourcePEquivalent_cantorLogPotential_zero :
    ¬ SingularGlobalPOrder.SourcePEquivalent (n := 1) cantorLogPotential (fun _ : P1 => 0) := by
  intro h
  have hv : HasPositivePotentialMass Θ cantorLogPotential
      isThetaPshPotential_cantorLogPotential_double := by
    change 0 < diagonalPotentialMass Θ cantorLogPotential _
    rw [diagonalPotentialMass_cantorLogPotential_double]
    exact zero_lt_one
  have hz : HasPositivePotentialMass Θ (fun _ : P1 => 0)
      isThetaPshPotential_projectiveZero_double := by
    change 0 < diagonalPotentialMass Θ (fun _ : P1 => 0) _
    rw [diagonalPotentialMass_projectiveZero_double]
    norm_num
  have he := (SingularGlobalPOrder.sourcePEquivalent_iff_pEquivalentWith
    projectiveNativeFSBackground Θ isThetaPshPotential_cantorLogPotential_double
    isThetaPshPotential_projectiveZero_double hv hz).mp h
  have hm := SingularPositiveMassPEquivalence.diagonalPotentialMass_eq_of_pEquivalentWith
    projectiveNativeFSBackground Θ isThetaPshPotential_cantorLogPotential_double
    isThetaPshPotential_projectiveZero_double he
  rw [diagonalPotentialMass_cantorLogPotential_double,
    diagonalPotentialMass_projectiveZero_double] at hm
  norm_num at hm

/-- The existing actual SGPT global source P relation is false for the Cantor potential and zero. -/
theorem not_sourcePEquivalent_cantorLogPotential_zero :
    ¬ SGPT.PSH.GlobalPComparison.sourcePEquivalent (n := 1) cantorLogPotential
      (fun _ : P1 => 0) :=
  not_nativeSourcePEquivalent_cantorLogPotential_zero

/-- No arbitrary positive admissible background can witness native global I-goodness. -/
theorem not_iGood_cantorLogPotential : ¬ IGood (n := 1) cantorLogPotential := by
  rintro ⟨σ, hσ, hg⟩
  have hv : HasPositivePotentialMass Θ cantorLogPotential
      isThetaPshPotential_cantorLogPotential_double := by
    change 0 < diagonalPotentialMass Θ cantorLogPotential _
    rw [diagonalPotentialMass_cantorLogPotential_double]
    exact zero_lt_one
  have hd := (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential
    projectiveNativeFSBackground σ Θ hσ isThetaPshPotential_cantorLogPotential_double hg.1 hv).mp hg
  have he := hd.2.trans iSingularityEnvelope_cantorLogPotential_double_eq_zero
  have hP := SGPT.Foundations.Analysis.FirstPass.singularityEnvelope_isThetaPshPotential
    (Θ).val (Θ).property.1 (Θ).property.2
    isThetaPshPotential_cantorLogPotential_double.1.hasSmoothLocalPotentials
    cantorLogPotential isThetaPshPotential_cantorLogPotential_double
  have hm := singularityEnvelopeMassPreserving projectiveNativeFSBackground Θ
    cantorLogPotential isThetaPshPotential_cantorLogPotential_double hP
  have hz := diagonalPotentialMass_congr he hP isThetaPshPotential_projectiveZero_double
  have h := hm.symm.trans hz
  simp only [Pi.zero_def] at h
  rw [diagonalPotentialMass_cantorLogPotential_double,
    diagonalPotentialMass_projectiveZero_double] at h
  norm_num at h

/-- Existing source background-existential I-goodness is false on its stated manifold domain. -/
theorem not_sourceIGood_cantorLogPotential :
    ¬ SGPT.PSH.VariableComplexAtlas.sourceIGood (n := 1) cantorLogPotential := by
  intro h
  exact not_iGood_cantorLogPotential
    ((SGPT.PSH.VariableComplexAtlas.sourceIGood_iff_native _).mp h)

end SGPT.BBJ
