import SGPT.Envelopes.SourceIncreasingOrdinaryEnvelopes
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import Mathlib.Order.Hom.CompleteLattice

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending GlobalMultilinearExpansion

/-- Positive finite multiplication is an actual complete-order isomorphism,
with the reciprocal inverse at BOTH infinities. -/
def sourcePositiveERealOrderIso (a : ℝ) (ha : 0 < a) : EReal ≃o EReal where
  toFun q := (a : EReal) * q
  invFun q := ((a⁻¹ : ℝ) : EReal) * q
  left_inv q := by
    change ((a⁻¹ : ℝ) : EReal) * ((a : EReal) * q) = q
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ha.ne', EReal.coe_one, one_mul]
  right_inv q := by
    change (a : EReal) * (((a⁻¹ : ℝ) : EReal) * q) = q
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ha.ne', EReal.coe_one, one_mul]
  map_rel_iff' := by
    intro q r
    change (a : EReal) * q ≤ (a : EReal) * r ↔ q ≤ r
    constructor
    · intro h
      have hh := mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr (inv_pos.mpr ha).le)
      simpa only [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ha.ne',
        EReal.coe_one, one_mul] using hh
    · exact fun h => mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr ha.le)

/-- The original neighborhood regularization commutes with the SAME positive
finite multiplier; no boundedness, nonempty family or finite-value premise. -/
theorem sourcePositiveScaling_uscRegularization {X : Type*} [TopologicalSpace X]
    (a : ℝ) (ha : 0 < a) (f : X → EReal) :
    uscRegularization (fun x => (a : EReal) * f x) =
      fun x => (a : EReal) * uscRegularization f x := by
  let e := sourcePositiveERealOrderIso a ha
  have hmap (x : X) :
      uscRegularization (fun y => e (f y)) x = e (uscRegularization f x) := by
    simp only [uscRegularization, _root_.map_iInf, _root_.map_iSup]
  exact funext hmap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Every original chart coefficient is multiplied by the printed REAL a. -/
theorem sourcePositiveScaling_form_coeff (a : ℝ) :
    (nativeClosedFormToAtlas (a • atlasClosedFormToNative θ)).coeff =
      fun e z => a • θ.coeff e z := rfl

/-- Genuine source potentials scale in the actual coefficient-scaled form. -/
theorem sourcePositiveScaling_thetaPSH {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {a : ℝ} (ha : 0 < a) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (a • atlasClosedFormToNative θ))
      (fun x => (a : EReal) * u x) := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact RestrictedApproximantComparison.isThetaPshPotential_smul
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) ha

omit [TopologicalSpace M] in
/-- ONE finite additive comparison constant scales to precisely a*C. -/
theorem sourcePositiveScaling_singularityLE {u v : M → EReal}
    (huv : SGPT.PSH.SingularityLE u v) {a : ℝ} (ha : 0 < a) :
    SGPT.PSH.SingularityLE (fun x => (a : EReal) * u x)
      (fun x => (a : EReal) * v x) := by
  obtain ⟨C, hC⟩ := huv
  refine ⟨a * C, fun x hx => ?_⟩
  exact (mul_le_mul_of_nonneg_left (hC x hx) (EReal.coe_nonneg.mpr ha.le)).trans_eq
    (ThetaPshConvexCombination.coe_mul_add_coe ha _ C)

/-- EVERY actual original competitor scales, including zero-mass references. -/
theorem sourcePositiveScaling_competitor {u : M → EReal}
    (w : sourceSingularityCompetitors θ u) {a : ℝ} (ha : 0 < a) :
    (ofFixedModel n M).IsThetaPSH
        (nativeClosedFormToAtlas (a • atlasClosedFormToNative θ))
        (fun x => (a : EReal) * w.1 x) ∧
      (fun x => (a : EReal) * w.1 x) ≤ 0 ∧
      SGPT.PSH.SingularityLE (fun x => (a : EReal) * w.1 x)
        (fun x => (a : EReal) * u x) :=
  ⟨sourcePositiveScaling_thetaPSH w.2.1 ha,
    fun x => mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr ha.le) (w.2.2.1 x),
    sourcePositiveScaling_singularityLE w.2.2.2 ha⟩

/-- ENTIRE ordinary envelope scaling, through the whole competitor bijection
and the original outer USC; no positive mass or input/output type equivalence. -/
theorem sourceOrdinaryEnvelope_positiveScaling (u : M → EReal)
    {a : ℝ} (ha : 0 < a) :
    sourceSingularityEnvelope (nativeClosedFormToAtlas (a • atlasClosedFormToNative θ))
      (fun x => (a : EReal) * u x) =
      fun x => (a : EReal) * sourceSingularityEnvelope θ u x := by
  let e := sourcePositiveERealOrderIso a ha
  let Θ := nativeClosedFormToAtlas (a • atlasClosedFormToNative θ)
  have hraw : (fun x => ⨆ z : sourceSingularityCompetitors Θ
      (fun x => (a : EReal) * u x), z.1 x) =
      fun x => (a : EReal) * ⨆ w : sourceSingularityCompetitors θ u, w.1 x := by
    funext x
    change _ = e (⨆ w : sourceSingularityCompetitors θ u, w.1 x)
    rw [_root_.map_iSup]
    apply le_antisymm
    · apply iSup_le
      intro z
      let w : M → EReal := fun y => ((a⁻¹ : ℝ) : EReal) * z.1 y
      have hw := sourcePositiveScaling_competitor z (inv_pos.mpr ha)
      have hform : nativeClosedFormToAtlas (a⁻¹ • atlasClosedFormToNative Θ) = θ := by
        simp only [Θ, sourceNativeAtlasForm_roundTrip, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
        cases θ
        rfl
      have href : (fun y => ((a⁻¹ : ℝ) : EReal) * ((a : EReal) * u y)) = u := by
        funext y
        exact e.left_inv (u y)
      rw [hform, href] at hw
      exact le_iSup_of_le (⟨w, hw⟩ : sourceSingularityCompetitors θ u)
        (le_of_eq (e.right_inv (z.1 x)).symm)
    · apply iSup_le
      intro w
      exact le_iSup_of_le
        (⟨_, sourcePositiveScaling_competitor w ha⟩ : sourceSingularityCompetitors Θ
          (fun x => (a : EReal) * u x)) le_rfl
  change uscRegularization _ = fun x => (a : EReal) * uscRegularization _ x
  rw [hraw, sourcePositiveScaling_uscRegularization a ha]

private theorem nativeIndependentSum_genuine
    {T S : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential T.val u) (hv : IsThetaPshPotential S.val v) :
    IsThetaPshPotential (T + S).val (fun x => u x + v x) := by
  classical
  let α : Bool → ClosedRealOneOneForm n M := fun b => if b then T else S
  let f : Bool → M → EReal := fun b => if b then u else v
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hv
    · exact hu
  have h := MixedSummandCapacityDomination.isThetaPshPotential_sumPot
    (T := Finset.univ) (w := fun _ : Bool => (1 : ℝ))
    Finset.univ_nonempty (fun _ => zero_lt_one) hf
  have hQ : GlobalMultilinearExpansion.sumPot Finset.univ
      (fun _ : Bool => (1 : ℝ)) f = fun x => u x + v x := by
    funext x
    simp only [GlobalMultilinearExpansion.sumPot, Fintype.sum_bool, f,
      Bool.false_eq_true, ↓reduceIte, EReal.coe_one, one_mul]
  rw [hQ] at h
  simpa only [GlobalMultilinearExpansion.sumForm, Fintype.sum_bool, α,
    Bool.false_eq_true, ↓reduceIte, one_smul] using h

/-- The literal sum retains all original coefficients in BOTH backgrounds. -/
theorem sourceIndependentSum_form_coeff :
    (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)).coeff =
      fun e z => θ.coeff e z + σ.coeff e z := rfl

/-- GENUINE two-background sum; local nondegeneracy is produced by the actual
finite pole-union mother, rather than supplied as a certificate. -/
theorem sourceIndependentSum_thetaPSH {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
      (fun x => u x + v x) := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact nativeIndependentSum_genuine
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential σ v).mp hv)

variable [CompactSpace M]

/-- WHOLE original addition clause in TWO independent original backgrounds.
Actual truncated competitors and genuine chart-AE recovery produce the link;
no same-singularity-type assertion about either ordinary envelope is assumed. -/
theorem sourceOrdinaryEnvelope_independent_add_le {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH σ v) :
    (fun x => sourceSingularityEnvelope θ u x + sourceSingularityEnvelope σ v x) ≤
      sourceSingularityEnvelope
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
        (fun x => u x + v x) := by
  classical
  by_cases hM : Nonempty M
  swap
  · exact fun x => (hM ⟨x⟩).elim
  let : Nonempty M := hM
  simp only [sourceSingularityEnvelope_eq_native, sourceNativeAtlasForm_roundTrip]
  let T := atlasClosedFormToNative θ
  let S := atlasClosedFormToNative σ
  have hun : IsThetaPshPotential T.val u := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn : IsThetaPshPotential S.val v := (isThetaPSH_iff_nativeThetaPotential σ v).mp hv
  obtain ⟨C, hC⟩ := hun.exists_normalized_sub_const
  obtain ⟨D, hD⟩ := hvn.exists_normalized_sub_const
  let A : ℕ → M → EReal := fun j => truncatedSingularityEnvelope T.val u (-C + j)
  let B : ℕ → M → EReal := fun j => truncatedSingularityEnvelope S.val v (-D + j)
  have hA (j : ℕ) : IsThetaPshPotential T.val (A j) :=
    truncatedSingularityEnvelope_isThetaPshPotential hun.1.hasSmoothLocalPotentials
      ⟨_, sub_const_mem_truncatedSingularityCompetitors hC (le_add_of_nonneg_right j.cast_nonneg)⟩
  have hB (j : ℕ) : IsThetaPshPotential S.val (B j) :=
    truncatedSingularityEnvelope_isThetaPshPotential hvn.1.hasSmoothLocalPotentials
      ⟨_, sub_const_mem_truncatedSingularityCompetitors hD (le_add_of_nonneg_right j.cast_nonneg)⟩
  have hAm : Monotone A := fun j k hjk => truncatedSingularityEnvelope_mono _ _
    (add_le_add le_rfl (by exact_mod_cast hjk : (j : ℝ) ≤ k))
  have hBm : Monotone B := fun j k hjk => truncatedSingularityEnvelope_mono _ _
    (add_le_add le_rfl (by exact_mod_cast hjk : (j : ℝ) ≤ k))
  have hPu : IsThetaPshPotential T.val (singularityEnvelope T.val u) :=
    FirstPass.singularityEnvelope_isThetaPshPotential T.val T.property.1 T.property.2
      hun.1.hasSmoothLocalPotentials u hun
  have hPv : IsThetaPshPotential S.val (singularityEnvelope S.val v) :=
    FirstPass.singularityEnvelope_isThetaPshPotential S.val S.property.1 S.property.2
      hvn.1.hasSmoothLocalPotentials v hvn
  have heqA : uscRegularization (⨆ j, A j) = singularityEnvelope T.val u :=
    (singularityEnvelope_eq_uscRegularization_iSup_truncated T.val u (-C)).symm
  have heqB : uscRegularization (⨆ j, B j) = singularityEnvelope S.val v :=
    (singularityEnvelope_eq_uscRegularization_iSup_truncated S.val v (-D)).symm
  have hstage (j : ℕ) : (fun x => A j x + B j x) ≤
      singularityEnvelope (T + S).val (fun x => u x + v x) := by
    apply le_singularityEnvelope (nativeIndependentSum_genuine (hA j) (hB j))
    · intro x
      exact (add_le_add (truncatedSingularityEnvelope_le_zero T.val u (-C + j) x)
        (truncatedSingularityEnvelope_le_zero S.val v (-D + j) x)).trans_eq (zero_add 0)
    · refine ⟨(-C + j) + (-D + j), fun x _ => ?_⟩
      calc
        _ ≤ (u x + ((-C + j : ℝ) : EReal)) + (v x + ((-D + j : ℝ) : EReal)) :=
          add_le_add
            (truncatedSingularityEnvelope_le_add hun.1.quasiPlurisubharmonic T.val (-C + j) x)
            (truncatedSingularityEnvelope_le_add hvn.1.quasiPlurisubharmonic S.val (-D + j) x)
        _ = _ := by rw [add_add_add_comm, ← EReal.coe_add]
  have hreg : uscRegularization (⨆ j, fun x => A j x + B j x) =
      fun x => singularityEnvelope T.val u x + singularityEnvelope S.val v x := by
    apply SingularModelIncreasingAERegularizedLimit.uscRegularization_iSup_eq_of_monotone_ae_chart_tendsto
      (fun j => nativeIndependentSum_genuine (hA j) (hB j))
      (nativeIndependentSum_genuine hPu hPv)
      (fun x j k hjk => add_le_add (hAm hjk x) (hBm hjk x))
    intro e
    have hAEa := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine
      hA hAm (heqA.symm ▸ hPu) e
    have hAEb := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine
      hB hBm (heqB.symm ▸ hPv) e
    rw [heqA] at hAEa
    rw [heqB] at hAEb
    filter_upwards [hAEa, hAEb] with z ha hb
    have hla : Tendsto (fun j => A j (e.val.symm z)) atTop
        (𝓝 (singularityEnvelope T.val u (e.val.symm z))) := by
      change Tendsto (fun j => chartFunction (A j) e z) atTop
        (𝓝 (chartFunction (singularityEnvelope T.val u) e z))
      rw [← ha]
      exact tendsto_atTop_iSup (fun j k hjk => hAm hjk (e.val.symm z))
    have hlb : Tendsto (fun j => B j (e.val.symm z)) atTop
        (𝓝 (singularityEnvelope S.val v (e.val.symm z))) := by
      change Tendsto (fun j => chartFunction (B j) e z) atTop
        (𝓝 (chartFunction (singularityEnvelope S.val v) e z))
      rw [← hb]
      exact tendsto_atTop_iSup (fun j k hjk => hBm hjk (e.val.symm z))
    have hAtop := ne_of_lt ((singularityEnvelope_le_zero T.val u (e.val.symm z)).trans_lt
      (by simp : (0 : EReal) < ⊤))
    have hBtop := ne_of_lt ((singularityEnvelope_le_zero S.val v (e.val.symm z)).trans_lt
      (by simp : (0 : EReal) < ⊤))
    exact (EReal.continuousAt_add (Or.inl hAtop) (Or.inr hBtop)).tendsto.comp
      (hla.prodMk_nhds hlb)
  rw [← hreg]
  exact uscRegularization_le (upperSemicontinuous_singularityEnvelope (T + S).val _)
    (iSup_le hstage)

end SGPT.PSH.VariableComplexAtlas
