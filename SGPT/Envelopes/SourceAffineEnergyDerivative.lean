import SGPT.Envelopes.SourceFiniteEnergyComparison
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass GlobalNonPluripolar GlobalDiagonalScaling
open GlobalMultilinearExpansion MixedMassProductCalculus

/-- Elementary real calculus turns produced supporting increments into a within derivative. -/
theorem sourceHasDerivWithinAt_of_increment_bounds {F P : ℝ → ℝ} {S : Set ℝ} {t : ℝ}
    (hP : ContinuousAt P t)
    (hb : ∀ s ∈ S, (s - t) * P s ≤ F s - F t ∧ F s - F t ≤ (s - t) * P t) :
    HasDerivWithinAt F (P t) S t := by
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hc : ContinuousAt (fun _ : ℝ => P t) t := continuousAt_const
  have hlo : Tendsto (fun s => min (P s) (P t)) (𝓝[S \ {t}] t) (𝓝 (P t)) := by
    simpa only [min_self] using (hP.min hc).mono_left
      (nhdsWithin_le_nhds : 𝓝[S \ {t}] t ≤ 𝓝 t)
  have hhi : Tendsto (fun s => max (P s) (P t)) (𝓝[S \ {t}] t) (𝓝 (P t)) := by
    simpa only [max_self] using (hP.max hc).mono_left
      (nhdsWithin_le_nhds : 𝓝[S \ {t}] t ≤ 𝓝 t)
  have hbounds : ∀ᶠ s in 𝓝[S \ {t}] t,
      min (P s) (P t) ≤ slope F t s ∧ slope F t s ≤ max (P s) (P t) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : s ≠ t := by simpa only [mem_singleton_iff] using hs.2
    have h := hb s hs.1
    rw [slope_def_field]
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hst) with hneg | hpos
    · exact ⟨(min_le_right _ _).trans ((le_div_iff_of_neg' hneg).mpr h.2),
        ((div_le_iff_of_neg' hneg).mpr h.1).trans (le_max_left _ _)⟩
    · exact ⟨(min_le_left _ _).trans ((le_div_iff₀' hpos).mpr h.1),
        ((div_le_iff₀' hpos).mpr h.2).trans (le_max_right _ _)⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The original affine convention assigns t to the second endpoint. -/
def sourceAffinePath (u v : M → EReal) (t : ℝ) : M → EReal :=
  ThetaPshConvexCombination.convexComb t v u

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The exact original zero endpoint, including poles. -/
theorem sourceAffinePath_zero (u v : M → EReal) : sourceAffinePath u v 0 = u :=
  sourceConvexComb_zero v u

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The exact original one endpoint, including poles. -/
theorem sourceAffinePath_one (u v : M → EReal) : sourceAffinePath u v 1 = v :=
  sourceConvexComb_one v u

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u v : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- The entire original closed affine path belongs to the same actual preceq E1 class. -/
theorem sourceRelativeFiniteEnergy_affinePath (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    SourceRelativeFiniteEnergy θ φ (sourceAffinePath u v t) hφ :=
  sourceRelativeFiniteEnergy_convexComb ω hv hu ht.1 ht.2

/-- The actual original real inf-majorant energy on the unchanged affine path. -/
def sourceAffineEnergy (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (hφ : SourceModelPotential θ φ) (u v : M → EReal) (t : ℝ) : ℝ :=
  (sourceRelativeEnergy θ φ (sourceAffinePath u v t) hφ).toReal

/-- Actual E1 excludes both infinities before the original affine energy is read as real. -/
theorem sourceAffineEnergy_coe (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (sourceAffineEnergy θ φ hφ u v t : EReal) =
      sourceRelativeEnergy θ φ (sourceAffinePath u v t) hφ :=
  sourceRelativeFiniteEnergy_coe_toReal ω (sourceRelativeFiniteEnergy_affinePath ω hu hv ht)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The unchanged binary tuple selecting the original endpoints in each actual slot. -/
def sourceAffineBinaryTuple (u v : M → EReal) (g : Fin n → Bool) : Fin n → M → EReal :=
  fun i => if g i then v else u

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Every selected original affine coefficient has its actual source theta tests. -/
theorem sourceAffineBinaryTuple_thetaPSH
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (g : Fin n → Bool) :
    ∀ i, (ofFixedModel n M).IsThetaPSH θ (sourceAffineBinaryTuple u v g i) := by
  intro i
  cases h : g i <;> simp only [sourceAffineBinaryTuple, h, Bool.false_eq_true, ↓reduceIte] <;>
    first | exact hu | exact hv

/-- Each coefficient is the actual signed integral on its unchanged binary mixed tuple. -/
def sourceAffineMixedMoment (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u v : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (g : Fin n → Bool) : ℝ :=
  ∫ x, (v x).toReal - (u x).toReal
    ∂sourceMixedNonPluripolarMeasure (fun _ => θ) (sourceAffineBinaryTuple u v g)
      (sourceAffineBinaryTuple_thetaPSH hu hv g)

/-- The finite actual-moment polynomial, defined at every real parameter. -/
def sourceAffineSlopePolynomial (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u v : M → EReal) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (t : ℝ) : ℝ :=
  ∑ g : Fin n → Bool, (∏ i, if g i then t else 1 - t) * sourceAffineMixedMoment θ u v hu hv g

omit [BorelSpace M] [ConnectedSpace M] in
/-- The explicit finite polynomial is continuous at every real parameter. -/
theorem sourceAffineSlopePolynomial_continuous
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    Continuous (sourceAffineSlopePolynomial θ u v hu hv) := by
  unfold sourceAffineSlopePolynomial
  apply continuous_finsetSum
  intro g _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro i _
  cases g i
  · exact continuous_const.sub continuous_id
  · exact continuous_id

/-- The whole actual affine diagonal measure expands with unchanged original mixed coefficients. -/
theorem sourceAffinePath_measure_expansion (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sourcePotentialNonPluripolarMeasure θ (sourceAffinePath u v t)
        (sourceRelativeFiniteEnergy_affinePath ω hu hv ht).1.choose =
      ∑ g : Fin n → Bool, ENNReal.ofReal (∏ i, if g i then t else 1 - t) •
        sourceMixedNonPluripolarMeasure (fun _ => θ) (sourceAffineBinaryTuple u v g)
          (sourceAffineBinaryTuple_thetaPSH hu.1.choose hv.1.choose g) := by
  classical
  let c : Bool → ℝ := fun e => if e then t else 1 - t
  let f : Bool → M → EReal := fun e => if e then v else u
  have hc (_ : Fin n) (e : Bool) : 0 ≤ c e := by
    cases e
    · exact sub_nonneg.mpr ht.2
    · exact ht.1
  have hf (e : Bool) : IsThetaPshPotential (atlasClosedFormToNative θ).val (f e) := by
    cases e
    · exact (isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1.choose
    · exact (isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1.choose
  have he := globalMixedMeasure_sumPot_expand ω hc hf
  have hforms : (fun _ : Fin n => sumForm Finset.univ c (fun _ : Bool => atlasClosedFormToNative θ)) =
      fun _ => atlasClosedFormToNative θ := by
    funext i
    simp only [sumForm, Fintype.sum_bool, c, Bool.false_eq_true, ↓reduceIte]
    rw [← add_smul]
    have hc1 : t + (1 - t) = 1 := by ring
    rw [hc1, one_smul]
  have hpots : (fun _ : Fin n => sumPot Finset.univ c f) =
      fun _ => sourceAffinePath u v t := by
    funext i x
    simp [sumPot, c, f, sourceAffinePath, ThetaPshConvexCombination.convexComb]
  erw [globalMixedMeasure_congr hforms hpots _
    (fun _ => ((isThetaPSH_iff_nativeThetaPotential θ _).mp
      (sourceRelativeFiniteEnergy_affinePath ω hu hv ht).1.choose).1)] at he
  exact he

/-- Every actual selected coefficient has a genuinely integrable original signed difference. -/
theorem sourceAffineBinaryTuple_integrable (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    (g : Fin n → Bool) :
    Integrable (fun x => (v x).toReal - (u x).toReal)
      (sourceMixedNonPluripolarMeasure (fun _ => θ) (sourceAffineBinaryTuple u v g)
        (sourceAffineBinaryTuple_thetaPSH hu.1.choose hv.1.choose g)) := by
  apply sourceRelativeFiniteEnergy_integrable_independent_mixed_toReal ω hv hu
  intro i
  cases h : g i <;> simp only [sourceAffineBinaryTuple, h, Bool.false_eq_true, ↓reduceIte] <;>
    first | exact hu | exact hv

/-- Actual mixed integrability produces the entire original affine diagonal signed domain. -/
theorem sourceAffinePath_integrable_slope (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun x => (v x).toReal - (u x).toReal)
      (sourcePotentialNonPluripolarMeasure θ (sourceAffinePath u v t)
        (sourceRelativeFiniteEnergy_affinePath ω hu hv ht).1.choose) := by
  have h := sourceRelativeFiniteEnergy_integrable_independent_mixed_toReal ω hv hu
    (fun _ : Fin n => sourceRelativeFiniteEnergy_affinePath ω hu hv ht)
  rwa [sourceMixedNonPluripolarMeasure_diagonal] at h

/-- The actual whole source slope equals the explicit finite polynomial on the CLOSED interval. -/
theorem sourceAffinePath_integral_eq_polynomial (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, (v x).toReal - (u x).toReal
      ∂sourcePotentialNonPluripolarMeasure θ (sourceAffinePath u v t)
        (sourceRelativeFiniteEnergy_affinePath ω hu hv ht).1.choose) =
      sourceAffineSlopePolynomial θ u v hu.1.choose hv.1.choose t := by
  rw [sourceAffinePath_measure_expansion ω hu hv ht, integral_finsetSum_measure]
  · unfold sourceAffineSlopePolynomial
    refine Finset.sum_congr rfl fun g _ => ?_
    have hc : 0 ≤ ∏ i, if g i then t else 1 - t := by
      apply Finset.prod_nonneg
      intro i _
      cases g i
      · exact sub_nonneg.mpr ht.2
      · exact ht.1
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal hc]
    rfl
  · intro g _
    exact (sourceAffineBinaryTuple_integrable ω hu hv g).smul_measure ENNReal.ofReal_ne_top

omit [ConnectedSpace M] in
/-- Actual pole-nullity gives the original scalar affine increment identity on every genuine diagonal. -/
theorem sourceAffinePath_difference_ae
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    {w : M → EReal} (hw : (ofFixedModel n M).IsThetaPSH θ w) (s t : ℝ) :
    (fun x => (sourceAffinePath u v s x).toReal - (sourceAffinePath u v t x).toReal) =ᵐ[
      sourcePotentialNonPluripolarMeasure θ w hw]
      (fun x => (s - t) * ((v x).toReal - (u x).toReal)) := by
  have hpole (a : M → EReal) (ha : (ofFixedModel n M).IsThetaPSH θ a) :
      ∀ᵐ x ∂sourcePotentialNonPluripolarMeasure θ w hw, a x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not, ← sourceMixedNonPluripolarMeasure_diagonal] using
      sourceMixedNonPluripolarMeasure_pole_null (fun _ : Fin n => hw) ha
  filter_upwards [hpole u hu, hpole v hv] with x hub hvb
  change
    (((s : EReal) * v x + ((1 - s : ℝ) : EReal) * u x).toReal -
      ((t : EReal) * v x + ((1 - t : ℝ) : EReal) * u x).toReal) = _
  rw [← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).1.quasiPlurisubharmonic.ne_top x) hub,
    ← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ v).mp hv).1.quasiPlurisubharmonic.ne_top x) hvb]
  simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.toReal_coe]
  ring

/-- The complete unordered source energy bounds produce both real affine increment inequalities. -/
theorem sourceAffineEnergy_increment_bounds (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (s - t) * sourceAffineSlopePolynomial θ u v hu.1.choose hv.1.choose s ≤
        sourceAffineEnergy θ φ hφ u v s - sourceAffineEnergy θ φ hφ u v t ∧
    sourceAffineEnergy θ φ hφ u v s - sourceAffineEnergy θ φ hφ u v t ≤
      (s - t) * sourceAffineSlopePolynomial θ u v hu.1.choose hv.1.choose t := by
  have hps := sourceRelativeFiniteEnergy_affinePath ω hu hv hs
  have hpt := sourceRelativeFiniteEnergy_affinePath ω hu hv ht
  have h := sourceRelativeFiniteEnergy_endpoint_bounds_toReal ω hps hpt
  rw [integral_congr_ae (sourceAffinePath_difference_ae hu.1.choose hv.1.choose hps.1.choose s t),
    integral_const_mul, sourceAffinePath_integral_eq_polynomial ω hu hv hs,
    integral_congr_ae (sourceAffinePath_difference_ae hu.1.choose hv.1.choose hpt.1.choose s t),
    integral_const_mul, sourceAffinePath_integral_eq_polynomial ω hu hv ht] at h
  exact h

/-- The WHOLE original E1 affine energy derivative, including the actual closed endpoint filters. -/
theorem sourceAffineEnergy_hasDerivWithinAt (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (sourceAffineEnergy θ φ hφ u v)
      (∫ x, (v x).toReal - (u x).toReal
        ∂sourcePotentialNonPluripolarMeasure θ (sourceAffinePath u v t)
          (sourceRelativeFiniteEnergy_affinePath ω hu hv ht).1.choose) (Icc (0 : ℝ) 1) t := by
  rw [sourceAffinePath_integral_eq_polynomial ω hu hv ht]
  exact sourceHasDerivWithinAt_of_increment_bounds
    (sourceAffineSlopePolynomial_continuous hu.1.choose hv.1.choose).continuousAt
    (fun s hs => sourceAffineEnergy_increment_bounds ω hu hv hs ht)

/-- The original interval interior has the actual ordinary two-sided energy derivative. -/
theorem sourceAffineEnergy_hasDerivAt (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (sourceAffineEnergy θ φ hφ u v)
      (∫ x, (v x).toReal - (u x).toReal
        ∂sourcePotentialNonPluripolarMeasure θ (sourceAffinePath u v t)
          (sourceRelativeFiniteEnergy_affinePath ω hu hv ⟨ht.1.le, ht.2.le⟩).1.choose) t :=
  (sourceAffineEnergy_hasDerivWithinAt ω hu hv ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- The genuine original right derivative at zero reads back the unchanged first diagonal. -/
theorem sourceAffineEnergy_hasDerivAt_zero_right (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ) :
    HasDerivWithinAt (sourceAffineEnergy θ φ hφ u v)
      (∫ x, (v x).toReal - (u x).toReal
        ∂sourcePotentialNonPluripolarMeasure θ u hu.1.choose) (Ici (0 : ℝ)) 0 := by
  have hd := sourceAffineEnergy_hasDerivWithinAt ω hu hv (t := 0) ⟨le_rfl, zero_le_one⟩
  have h := hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (show (0 : ℝ) < 1 by norm_num))
  simpa only [sourceAffinePath_zero] using h

/-- The genuine original left derivative at one reads back the unchanged second diagonal. -/
theorem sourceAffineEnergy_hasDerivAt_one_left (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ) :
    HasDerivWithinAt (sourceAffineEnergy θ φ hφ u v)
      (∫ x, (v x).toReal - (u x).toReal
        ∂sourcePotentialNonPluripolarMeasure θ v hv.1.choose) (Iic (1 : ℝ)) 1 := by
  have hd := sourceAffineEnergy_hasDerivWithinAt ω hu hv (t := 1) ⟨zero_le_one, le_rfl⟩
  have h := hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE (show (0 : ℝ) < 1 by norm_num))
  simpa only [sourceAffinePath_one] using h

/-- The entire original closed interval is differentiable, with both one-sided endpoints included. -/
theorem sourceAffineEnergy_differentiableOn (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ) :
    DifferentiableOn ℝ (sourceAffineEnergy θ φ hφ u v) (Icc (0 : ℝ) 1) :=
  fun _ ht => (sourceAffineEnergy_hasDerivWithinAt ω hu hv ht).differentiableWithinAt

end SGPT.PSH.VariableComplexAtlas
