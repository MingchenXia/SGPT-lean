import SGPT.Foundations.Analysis.Pending.SingularModelUniformModelL1
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasSupremumLowerBound
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalUpperComparison

set_option autoImplicit false

/-!
# Actual two-sided singular-model Darvas supremum control

Xia SGPT PDF0164 Lemma 4.3.3, equation (4.21). The actual uniform
normalized model integral and the actual endpoint diagonal comparison
produce the opposite supremum estimate. Actual distance boundedness then
produces a uniform all-point real upper bound, without a bound certificate.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasSupremumControl

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses DiagonalMass SingularModelUniformModelL1

noncomputable section

private theorem ofReal_le_abs_add_neg_shift {a S : ℝ} (ha : a ≤ S) :
    ENNReal.ofReal S ≤ ENNReal.ofReal |a| + ENNReal.ofReal (S - a) := by
  rw [← ENNReal.ofReal_add (abs_nonneg a) (sub_nonneg.mpr ha)]
  exact ENNReal.ofReal_le_ofReal (by linarith [le_abs_self a])

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- The complete actual source two-sided distance/supremum estimate for every singular model. -/
theorem exists_pos_constants_supremum_bounds (omega : KahlerBackground n M) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ u : M → EReal,
      RelativeFiniteEnergyPreceq θ φ u hφ →
        -(modelVolume θ φ hφ) * (⨆ x, u x).toReal ≤ relativeD1 θ φ hφ u φ ∧
        modelVolume θ φ hφ * (⨆ x, u x).toReal ≤ A * relativeD1 θ φ hφ u φ + B := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  let μ := diagonalPotentialMeasure θ φ hφ.plurisubharmonic
  let A : ℝ := 3 * (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1)
  have hA : 0 < A := by positivity
  have hm : 0 ≤ modelVolume θ φ hφ := measureReal_nonneg
  have hφfinite : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  obtain ⟨K, hK, hKv⟩ := exists_uniform_lintegral_neg_le_modelMeasure omega θ hφ 1
  refine ⟨A, K.toReal + 1, hA, by positivity, ?_⟩
  intro u hu
  refine ⟨SingularModelDarvasSupremumLowerBound.neg_modelVolume_mul_iSup_le_relativeD1 omega hu, ?_⟩
  let S : ℝ := (⨆ x, u x).toReal
  have hD : 0 ≤ relativeD1 θ φ hφ u φ :=
    SingularModelDarvasBasic.relativeD1_nonneg omega hu hφfinite
  by_cases hs : S ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos hm hs).trans
      (by positivity : 0 ≤ A * relativeD1 θ φ hφ u φ + (K.toReal + 1))
  have hs0 : 0 < S := not_le.mp hs
  have hSf := ModelRaySupremum.iSup_ne_top_ne_bot hu.1.plurisubharmonic
  have hS : (S : EReal) = ⨆ x, u x := EReal.coe_toReal hSf.1 hSf.2
  have huS : ∀ x, u x ≤ (S : EReal) := fun x => hS.symm ▸ le_iSup u x
  let v : M → EReal := fun x => u x - (S : EReal)
  have hv := hu.1.plurisubharmonic.sub_const S
  have hv0 : ∀ x, v x ≤ 0 := sub_const_nonpositive_of_le huS
  have hvnorm : ∃ x0, (((-1 : ℝ) : EReal)) ≤ v x0 := by
    have hlt : ((S - 1 : ℝ) : EReal) < ⨆ x, u x := by
      rw [← hS]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp hlt
    refine ⟨x, ?_⟩
    apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot S))
      (Or.inl (EReal.coe_ne_top S))).mpr
    simpa only [← EReal.coe_add, show (-1 + S : ℝ) = S - 1 by ring] using hx.le
  have hnorm : (∫⁻ x, (-v x).toENNReal ∂μ) ≤ K := hKv v hv.1 hv0 hvnorm
  have hφ0 : φ ≤ 0 := by
    rw [hφ.envelope_eq]
    exact singularityEnvelope_le_zero θ.val φ
  have hP : IsThetaPshPotential θ.val (singularityEnvelope θ.val φ) := by
    rw [← hφ.envelope_eq]
    exact hφ.plurisubharmonic
  have hnull : μ {x | φ x < 0} = 0 := by
    have h := SingularityEnvelopeContact.diagonalPotentialMeasure_singularityEnvelope_lt_zero
      omega θ hφ.plurisubharmonic hP
    simpa only [μ, ← hφ.envelope_eq] using h
  have hφae : ∀ᵐ x ∂μ, φ x = 0 := by
    apply ae_iff.mpr
    apply measure_mono_null ?_ hnull
    intro x hx
    exact lt_of_le_of_ne (hφ0 x) hx
  have hpole : ∀ᵐ x ∂μ, u x ≠ ⊥ := by
    have hz : μ {x | u x = ⊥} = 0 :=
      GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
        (fun _ : Fin n => hφ.plurisubharmonic.1) hu.1.plurisubharmonic
    exact ae_iff.mpr (by simpa only [not_not] using hz)
  have hpoint : ∀ᵐ x ∂μ, ENNReal.ofReal S ≤
      canonicalERealAbsDiff (φ x) (u x) + (-v x).toENNReal := by
    filter_upwards [hφae, hpole] with x hxφ hxu
    have hux : u x = ((u x).toReal : EReal) :=
      (EReal.coe_toReal (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hxu).symm
    have hreal : (u x).toReal ≤ S := by
      simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal (huS x) hxu (EReal.coe_ne_top S)
    dsimp only [v]
    rw [hxφ, hux]
    simpa only [show (0 : EReal) = ((0 : ℝ) : EReal) from rfl,
      canonicalERealAbsDiff_coe_coe, zero_sub, abs_neg, ← EReal.coe_sub,
      ← EReal.coe_neg, EReal.real_coe_toENNReal, neg_sub] using
      ofReal_le_abs_add_neg_shift hreal
  have hgap := SingularModelDarvasDiagonalUpperComparison.lintegral_gap_le_mul_relativeD1
    omega hφfinite hu
  rw [relativeD1_comm θ φ hφ φ u] at hgap
  have hmeasgap : Measurable (fun x => canonicalERealAbsDiff (φ x) (u x)) :=
    hφ.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable.canonicalERealAbsDiff
      hu.1.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hbound : ENNReal.ofReal S * μ univ ≤
      ENNReal.ofReal (A * relativeD1 θ φ hφ u φ) + K := by
    calc
      ENNReal.ofReal S * μ univ = ∫⁻ _x, ENNReal.ofReal S ∂μ := (lintegral_const _).symm
      _ ≤ ∫⁻ x, canonicalERealAbsDiff (φ x) (u x) + (-v x).toENNReal ∂μ :=
        lintegral_mono_ae hpoint
      _ = (∫⁻ x, canonicalERealAbsDiff (φ x) (u x) ∂μ) + ∫⁻ x, (-v x).toENNReal ∂μ :=
        lintegral_add_left hmeasgap _
      _ ≤ _ := add_le_add hgap hnorm
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hK.ne⟩) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs0.le,
    ENNReal.toReal_add ENNReal.ofReal_ne_top hK.ne,
    ENNReal.toReal_ofReal (mul_nonneg hA.le hD)] at hreal
  change S * modelVolume θ φ hφ ≤ A * relativeD1 θ φ hφ u φ + K.toReal at hreal
  change modelVolume θ φ hφ * S ≤ A * relativeD1 θ φ hφ u φ + (K.toReal + 1)
  nlinarith

/-- Actual distance boundedness produces an all-point uniform real upper bound on any E1 family. -/
theorem exists_uniform_upper_bound_of_relativeD1_le {I : Type*}
    (omega : KahlerBackground n M) {ui : I → M → EReal}
    (hui : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ) {R : ℝ}
    (hR : ∀ i, relativeD1 θ φ hφ (ui i) φ ≤ R) :
    ∃ C : ℝ, ∀ i x, ui i x ≤ (C : EReal) := by
  obtain ⟨A, B, hA, _, hbounds⟩ := exists_pos_constants_supremum_bounds (hφ := hφ) omega
  let := DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure
    omega θ hφ.plurisubharmonic
  have hm : 0 < modelVolume θ φ hφ :=
    ENNReal.toReal_pos hφ.positive_mass.ne' (measure_ne_top _ _)
  refine ⟨(A * R + B) / modelVolume θ φ hφ, ?_⟩
  intro i x
  have h := (hbounds (ui i) (hui i)).2.trans
    (add_le_add (mul_le_mul_of_nonneg_left (hR i) hA.le) (le_refl B))
  have hsup : (⨆ y, ui i y).toReal ≤ (A * R + B) / modelVolume θ φ hφ := by
    apply (le_div_iff₀ hm).mpr
    nlinarith
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  have hf := ModelRaySupremum.iSup_ne_top_ne_bot (hui i).1.plurisubharmonic
  calc
    ui i x ≤ ⨆ y, ui i y := le_iSup _ x
    _ = (((⨆ y, ui i y).toReal : ℝ) : EReal) := (EReal.coe_toReal hf.1 hf.2).symm
    _ ≤ _ := EReal.coe_le_coe_iff.mpr hsup

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasSupremumControl
