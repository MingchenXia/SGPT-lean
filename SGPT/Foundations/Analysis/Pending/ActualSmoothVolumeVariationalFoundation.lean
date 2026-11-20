import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshVolumeIntegrability
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteRealEnergy
import SGPT.Foundations.Analysis.Pending.RelativePreceqStatements
import SGPT.Foundations.Analysis.Pending.SingularModelUniformModelL1
import SGPT.Foundations.Analysis.Pending.ModelRaySupremum
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCocycle

set_option autoImplicit false

/-! # Actual smooth-volume functional and genuine maximizing sequences

Original positive-model/preceq-E1 variational domain. Actual volume
integrability, finite translation, normalization and uniform bound.
No compactness, energy USC, maximizer or prescribed MA solution is assumed.
Complete mathematical blueprint and proofs preceded SOURCE.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalFoundation

open FirstPass FirstPass.PositiveClasses DiagonalMass RelativeEnergy
  RelativeDarvasDistance RelativePreceqClasses IntegrationCurrent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual prescribed smooth-volume coefficient of the original model. -/
def smoothVolumeCoefficient (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (hφ : IsModelPotential θ φ) : ℝ :=
  modelVolume θ φ hφ / (kahlerVolume omega).real univ

/-- The original finite-energy functional with the actual smooth-volume integral. -/
def smoothVolumeFunctional (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (φ : M → EReal)
    (hφ : IsModelPotential θ φ) (u : M → EReal) : ℝ :=
  (energy θ φ hφ u).toReal - smoothVolumeCoefficient omega θ φ hφ *
    (∫ x, (u x).toReal ∂kahlerVolume omega)

/-- Genuine original potentials internally supply volume integrability and
the actual finite-constant integral translation, including original poles. -/
theorem integrable_and_integral_toReal_add_const (omega : KahlerBackground n M)
    {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (a : ℝ) :
    Integrable (fun x => (u x).toReal) (kahlerVolume omega) ∧
    (∫ x, (u x + (a : EReal)).toReal ∂kahlerVolume omega) =
      (∫ x, (u x).toReal ∂kahlerVolume omega) + a * (kahlerVolume omega).real univ := by
  have hint := GlobalQuasiPshVolumeIntegrability.integrable_toReal_of_genuine_thetaPsh
    (kahlerVolume omega) (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
    θ u hu
  have h0 : IsThetaPshPotential omega.form.val (fun _ : M => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have hpole : ∀ᵐ x ∂kahlerVolume omega, u x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not, kahlerVolume, diagonalPotentialMeasure] using
      GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
        (θ := fun _ : Fin n => omega.form) (u := fun _ => fun _ : M => (0 : EReal))
        (fun _ : Fin n => h0.1) hu
  refine ⟨hint, ?_⟩
  calc
    (∫ x, (u x + (a : EReal)).toReal ∂kahlerVolume omega) =
        ∫ x, (u x).toReal + a ∂kahlerVolume omega := by
      apply integral_congr_ae
      filter_upwards [hpole] with x hx
      have hux : u x = ((u x).toReal : EReal) :=
        (EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hx).symm
      rw [hux, ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]
    _ = _ := by rw [integral_add hint (integrable_const a), integral_const]; simp only [smul_eq_mul]; ring

variable [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u : M → EReal} {hφ : IsModelPotential θ φ}

omit [ConnectedSpace M] in
private theorem volume_real_pos [Nonempty M] (omega : KahlerBackground n M) :
    0 < (kahlerVolume omega).real univ := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos
    (KahlerLaplacianStokes.kahlerVolume_pos_of_isOpen omega isOpen_univ univ_nonempty).ne'
    (measure_ne_top _ _)

omit [ConnectedSpace M] in
/-- The actual original smooth-volume functional is internally invariant
under finite translations on its entire genuine singular E1 domain. -/
theorem functional_add_const (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (a : ℝ) :
    RelativeFiniteEnergyPreceq θ φ (fun x => u x + (a : EReal)) hφ ∧
      smoothVolumeFunctional omega θ φ hφ (fun x => u x + (a : EReal)) =
        smoothVolumeFunctional omega θ φ hφ u := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  refine ⟨RelativeFiniteEnergyPreceq.add_const omega hu a, ?_⟩
  have hI := (integrable_and_integral_toReal_add_const omega hu.1.plurisubharmonic a).2
  have hE := SingularModelFiniteRealEnergy.toReal_energy_add_const omega hu a
  have hV := (volume_real_pos omega).ne'
  unfold smoothVolumeFunctional smoothVolumeCoefficient
  rw [hE, hI]
  field_simp [hV]
  ring

omit [ConnectedSpace M] in
/-- Compact genuine finite maxima and the known original model identity
internally normalize the whole E1 domain without changing its functional. -/
theorem exists_normalized_translate (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) :
    ∃ a : ℝ,
      RelativeFiniteEnergyPreceq θ φ (fun x => u x + (a : EReal)) hφ ∧
      (⨆ x, u x + (a : EReal)) = 0 ∧
      (∀ x, u x + (a : EReal) ≤ φ x) ∧
      smoothVolumeFunctional omega θ φ hφ (fun x => u x + (a : EReal)) =
        smoothVolumeFunctional omega θ φ hφ u ∧
      ∃ x, u x + (a : EReal) = 0 := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  have huP := hu.1.plurisubharmonic
  obtain ⟨x0, _hx0, hmax⟩ :=
    (huP.1.quasiPlurisubharmonic.upperSemicontinuous.upperSemicontinuousOn univ).exists_isMaxOn
      univ_nonempty isCompact_univ
  obtain ⟨y, _hy, hybot, _⟩ := huP.quasiPshPotential.exists_finite
    (Classical.arbitrary M) isOpen_univ (mem_univ _)
  have hxbot : u x0 ≠ ⊥ := ne_bot_of_le_ne_bot hybot (hmax (mem_univ y))
  let S : ℝ := (u x0).toReal
  have hxreal : u x0 = (S : EReal) :=
    (EReal.coe_toReal (huP.1.quasiPlurisubharmonic.ne_top x0) hxbot).symm
  let v : M → EReal := fun x => u x + ((-S : ℝ) : EReal)
  have hv0 : ∀ x, v x ≤ 0 := by
    intro x
    have hb := add_le_add (hmax (mem_univ x)) (le_refl ((-S : ℝ) : EReal))
    simpa only [v, hxreal, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using hb
  have hvx : v x0 = 0 := by
    simp only [v, hxreal, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  obtain ⟨hvF, hFeq⟩ := functional_add_const omega hu (-S)
  have hvφ : ∀ x, v x ≤ φ x := by
    intro x
    have h := RelativePreceqStatements.le_add_const_of_moreSingularOn_of_singularityEnvelope_eq
      hvF.1.plurisubharmonic hφ.envelope_eq.symm hvF.1.relativePSHPreceq.2
      (B := 0) (by simpa only [EReal.coe_zero] using hv0) x
    simpa only [EReal.coe_zero, add_zero] using h
  refine ⟨-S, hvF, ?_, hvφ, hFeq, x0, hvx⟩
  apply le_antisymm (iSup_le hv0)
  exact hvx ▸ le_iSup v x0

private theorem ofReal_neg_toReal_le_neg_toENNReal (a : EReal) :
    ENNReal.ofReal (-a.toReal) ≤ (-a).toENNReal := by
  by_cases ha : -a = ⊤
  · rw [ha, EReal.toENNReal_top]
    exact le_top
  · rw [EReal.toENNReal_of_ne_top ha, EReal.toReal_neg_eq]

omit [ConnectedSpace M] in
private theorem energy_model_eq_zero (omega : KahlerBackground n M) :
    energy θ φ hφ φ = 0 := by
  rw [SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega θ hφ
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
    RelativeEnergy.relativeEnergyOfMinimalType_self, EReal.coe_zero]

/-- The actual uniform volume bound produces a real upper bound on the
whole original functional domain and a genuine model candidate. -/
theorem exists_uniform_integral_energy_functional_bound (omega : KahlerBackground n M) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ v : M → EReal, RelativeFiniteEnergyPreceq θ φ v hφ →
        (⨆ x, v x) = 0 →
        (∀ x, v x ≤ φ x) ∧
        -B ≤ (∫ x, (v x).toReal ∂kahlerVolume omega) ∧
        (∫ x, (v x).toReal ∂kahlerVolume omega) ≤ 0 ∧
        (energy θ φ hφ v).toReal ≤ 0 ∧
        smoothVolumeFunctional omega θ φ hφ v ≤ smoothVolumeCoefficient omega θ φ hφ * B) ∧
      (∀ v : M → EReal, RelativeFiniteEnergyPreceq θ φ v hφ →
        smoothVolumeFunctional omega θ φ hφ v ≤ smoothVolumeCoefficient omega θ φ hφ * B) ∧
      RelativeFiniteEnergyPreceq θ φ φ hφ ∧
      0 ≤ smoothVolumeFunctional omega θ φ hφ φ := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  have hφF : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have hc : 0 ≤ smoothVolumeCoefficient omega θ φ hφ :=
    div_nonneg (measureReal_nonneg : 0 ≤ modelVolume θ φ hφ) (volume_real_pos omega).le
  have hEφ := energy_model_eq_zero (hφ := hφ) omega
  obtain ⟨K, hK, hKv⟩ :=
    SingularModelUniformModelL1.exists_uniform_lintegral_neg_le_kahlerVolume θ omega 0
  have hnorm : ∀ v : M → EReal, RelativeFiniteEnergyPreceq θ φ v hφ →
      (⨆ x, v x) = 0 →
      (∀ x, v x ≤ φ x) ∧
      -K.toReal ≤ (∫ x, (v x).toReal ∂kahlerVolume omega) ∧
      (∫ x, (v x).toReal ∂kahlerVolume omega) ≤ 0 ∧
      (energy θ φ hφ v).toReal ≤ 0 ∧
      smoothVolumeFunctional omega θ φ hφ v ≤ smoothVolumeCoefficient omega θ φ hφ * K.toReal := by
    intro v hv hsup
    have hvP := hv.1.plurisubharmonic
    have hv0 : ∀ x, v x ≤ 0 := fun x => hsup ▸ le_iSup v x
    obtain ⟨x0, _hx0, hmax⟩ :=
      (hvP.1.quasiPlurisubharmonic.upperSemicontinuous.upperSemicontinuousOn univ).exists_isMaxOn
        univ_nonempty isCompact_univ
    have hx0 : v x0 = 0 := by
      apply le_antisymm (hv0 x0)
      rw [← hsup]
      exact iSup_le fun x => hmax (mem_univ x)
    have hlin := hKv v hvP.1 hv0 ⟨x0, by simp [hx0]⟩
    have hI := (integrable_and_integral_toReal_add_const omega hvP 0).1
    have hvR : ∀ x, (v x).toReal ≤ 0 := fun x => EReal.toReal_nonpos (hv0 x)
    have hI0 : (∫ x, (v x).toReal ∂kahlerVolume omega) ≤ 0 :=
      integral_nonpos_of_ae (Eventually.of_forall hvR)
    have hlinR : (∫⁻ x, ENNReal.ofReal (-(v x).toReal) ∂kahlerVolume omega) ≤ K :=
      (lintegral_mono fun x => ofReal_neg_toReal_le_neg_toENNReal (v x)).trans hlin
    have hreal := ENNReal.toReal_mono hK.ne hlinR
    have hformula := integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => neg_nonneg.mpr (hvR x)) hI.neg.aestronglyMeasurable
    rw [← hformula, integral_neg] at hreal
    have hvφ : ∀ x, v x ≤ φ x := by
      intro x
      have hf := RelativePreceqStatements.le_add_const_of_moreSingularOn_of_singularityEnvelope_eq
        hvP hφ.envelope_eq.symm hv.1.relativePSHPreceq.2 (B := 0)
        (by simpa only [EReal.coe_zero] using hv0) x
      simpa only [EReal.coe_zero, add_zero] using hf
    have hE := SingularModelFiniteRealEnergy.toReal_energy_mono omega hv hφF hvφ
    rw [hEφ, EReal.toReal_zero] at hE
    refine ⟨hvφ, by linarith, hI0, hE, ?_⟩
    unfold smoothVolumeFunctional
    have hmul := mul_le_mul_of_nonneg_left hreal hc
    linarith
  refine ⟨K.toReal, ENNReal.toReal_nonneg, hnorm, ?_, hφF, ?_⟩
  · intro v hv
    obtain ⟨a, hva, hs, _hb, hFa, _hx⟩ := exists_normalized_translate omega hv
    have hbound := (hnorm _ hva hs).2.2.2.2
    rwa [hFa] at hbound
  · have hφ0 : ∀ x, φ x ≤ 0 := by
      rw [hφ.envelope_eq]
      exact singularityEnvelope_le_zero θ.val φ
    have hI0 : (∫ x, (φ x).toReal ∂kahlerVolume omega) ≤ 0 :=
      integral_nonpos_of_ae (Eventually.of_forall fun x => EReal.toReal_nonpos (hφ0 x))
    unfold smoothVolumeFunctional
    rw [hEφ, EReal.toReal_zero]
    exact sub_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hc hI0)

/-- Real completeness, genuine model nonemptiness and actual finite
translations internally produce a normalized maximizing sequence with a
uniform original energy lower bound; no maximizer or compactness is input. -/
theorem exists_normalized_maximizing_sequence (omega : KahlerBackground n M) :
    ∃ L B : ℝ, ∃ uj : ℕ → M → EReal,
      0 ≤ L ∧ 0 ≤ B ∧
      (∀ j : ℕ,
        RelativeFiniteEnergyPreceq θ φ (uj j) hφ ∧
        (⨆ x, uj j x) = 0 ∧
        (∀ x, uj j x ≤ φ x) ∧
        L - 1 / ((j : ℝ) + 1) < smoothVolumeFunctional omega θ φ hφ (uj j) ∧
        smoothVolumeFunctional omega θ φ hφ (uj j) ≤ L ∧
        L - 1 - smoothVolumeCoefficient omega θ φ hφ * B ≤ (energy θ φ hφ (uj j)).toReal) ∧
      (∀ v : M → EReal, RelativeFiniteEnergyPreceq θ φ v hφ →
        smoothVolumeFunctional omega θ φ hφ v ≤ L) ∧
      Tendsto (fun j : ℕ => smoothVolumeFunctional omega θ φ hφ (uj j)) atTop (𝓝 L) := by
  classical
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  obtain ⟨B, hB, hnorm, hupper, hφF, hFφ0⟩ :=
    exists_uniform_integral_energy_functional_bound (hφ := hφ) omega
  let values : Set ℝ := {a | ∃ v : M → EReal,
    RelativeFiniteEnergyPreceq θ φ v hφ ∧ smoothVolumeFunctional omega θ φ hφ v = a}
  have hmemφ : smoothVolumeFunctional omega θ φ hφ φ ∈ values := ⟨φ, hφF, rfl⟩
  have hne : values.Nonempty := ⟨_, hmemφ⟩
  have hbd : BddAbove values := by
    refine ⟨smoothVolumeCoefficient omega θ φ hφ * B, ?_⟩
    rintro a ⟨v, hv, rfl⟩
    exact hupper v hv
  let L : ℝ := sSup values
  have hmax : ∀ v : M → EReal, RelativeFiniteEnergyPreceq θ φ v hφ →
      smoothVolumeFunctional omega θ φ hφ v ≤ L := fun v hv =>
    le_csSup hbd ⟨v, hv, rfl⟩
  have hL : 0 ≤ L := hFφ0.trans (hmax φ hφF)
  have happrox : ∀ j : ℕ, ∃ v : M → EReal,
      RelativeFiniteEnergyPreceq θ φ v hφ ∧
        L - 1 / ((j : ℝ) + 1) < smoothVolumeFunctional omega θ φ hφ v := by
    intro j
    have ht : 0 < (1 / ((j : ℝ) + 1) : ℝ) := by positivity
    obtain ⟨a, ⟨v, hv, heq⟩, hlt⟩ :=
      exists_lt_of_lt_csSup hne (sub_lt_self L ht)
    rw [← heq] at hlt
    exact ⟨v, hv, hlt⟩
  choose wj hwj hnear using happrox
  have hnormalized : ∀ j : ℕ, ∃ v : M → EReal,
      RelativeFiniteEnergyPreceq θ φ v hφ ∧ (⨆ x, v x) = 0 ∧
      (∀ x, v x ≤ φ x) ∧
      smoothVolumeFunctional omega θ φ hφ v = smoothVolumeFunctional omega θ φ hφ (wj j) := by
    intro j
    obtain ⟨a, hv, hs, hb, hF, _hx⟩ := exists_normalized_translate omega (hwj j)
    exact ⟨_, hv, hs, hb, hF⟩
  choose uj huj hsup hmodel hF using hnormalized
  have hlo : ∀ j : ℕ, L - 1 / ((j : ℝ) + 1) < smoothVolumeFunctional omega θ φ hφ (uj j) := by
    intro j
    rw [hF j]
    exact hnear j
  have hhi : ∀ j, smoothVolumeFunctional omega θ φ hφ (uj j) ≤ L := fun j => hmax _ (huj j)
  have hc : 0 ≤ smoothVolumeCoefficient omega θ φ hφ :=
    div_nonneg (measureReal_nonneg : 0 ≤ modelVolume θ φ hφ) (volume_real_pos omega).le
  refine ⟨L, B, uj, hL, hB, ?_, hmax, ?_⟩
  · intro j
    refine ⟨huj j, hsup j, hmodel j, hlo j, hhi j, ?_⟩
    have ht1 : (1 / ((j : ℝ) + 1) : ℝ) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).mpr
      simp only [one_mul]
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hIlow := (hnorm (uj j) (huj j) (hsup j)).2.1
    have hm := mul_le_mul_of_nonneg_left hIlow hc
    have hEeq : (energy θ φ hφ (uj j)).toReal =
        smoothVolumeFunctional omega θ φ hφ (uj j) + smoothVolumeCoefficient omega θ φ hφ *
          (∫ x, (uj j x).toReal ∂kahlerVolume omega) := by
      unfold smoothVolumeFunctional
      ring
    have hjlo := hlo j
    rw [hEeq]
    linarith
  · have hlolim : Tendsto (fun j : ℕ => L - 1 / ((j : ℝ) + 1)) atTop (𝓝 L) := by
      have hconst : Tendsto (fun _j : ℕ => L) atTop (𝓝 L) := tendsto_const_nhds
      simpa only [sub_zero] using
        (hconst.sub tendsto_one_div_add_atTop_nhds_zero_nat)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlolim tendsto_const_nhds
      (fun j => (hlo j).le) hhi

end

end SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalFoundation
