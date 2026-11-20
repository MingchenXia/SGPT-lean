import SGPT.PSH.HermitianProductsSmoothExpansion
import SGPT.PSH.HermitianProductsRadialApproximation
import SGPT.PSH.HermitianProductsPositivity
import SGPT.PSH.HermitianProductsFlat
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothCovariance

/-!
# Holomorphic covariance of the actual nonclosed-background products

The smooth identity is read against every complementary test, in every
degree. The bounded products are approached using the same actual smooth
positive approximants and weak continuity of positive-current pullback.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalBedfordTaylorSmoothDensity LocalBedfordTaylorSmoothProductDensity LocalBedfordTaylorContinuity
  LocalBedfordTaylorLocality LocalBedfordTaylorCollar
  LocalCurrentPullback LocalCurrentPullbackDdc LocalBedfordTaylorSmoothCovariance
  TopDegreeDensity ConstantFormProducts BedfordTaylor
open scoped Topology Distributions ContDiff

variable {n : ℕ} {A B : Opens (ComplexModel n)}
  {τ ι : ComplexModel n → ComplexModel n}

private theorem wedgeProd_comp_map (L : ComplexModel n →L[ℝ] ComplexModel n) :
    ∀ (p : ℕ) (α : Fin p → RealForm n 2),
      (wedgeProd p α).compContinuousLinearMap L =
        wedgeProd p (fun i => (α i).compContinuousLinearMap L)
  | 0, _ => by ext v; rfl
  | p + 1, α => by
    rw [wedgeProd_succ, wedgeProd_succ, coordinateWedge_compContinuousLinearMap,
      wedgeProd_comp_map L p]

/-- Full complementary-test covariance of a smooth positive form in every
degree. The input compatibility is the literal tensor transformation law;
no equality of currents or measures is supplied as a premise. -/
theorem pullback_wedgeForm_of_tensor_compatibility {r p : ℕ} (hdeg : r + p = n)
    (h : IsBiholomorphicPair A B τ ι)
    {αB αA : ComplexModel n → RealForm n (2 * p)}
    (hαB : ContDiffOn ℝ ∞ αB B) (hαA : ContDiffOn ℝ ∞ αA A)
    (hαBp : ∀ y ∈ B, αB y ∈ spCone p)
    (hcompat : ∀ x ∈ A, αA x =
      (αB (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars ℝ)) :
    pullback h (isPositive_wedgeForm hdeg isPositive_oneCurrent hαB hαBp) =
      wedgeForm hdeg (oneCurrent A) hαA := by
  have hAS : ∀ x ∈ A, αA x ∈ formSpan n p := by
    intro x hx
    rw [hcompat x hx]
    exact compContinuousLinearMap_mem_formSpan (fderiv ℂ τ x)
      (mem_formSpan_of_mem_spCone (hαBp (τ x) (h.mapsTo hx)))
  ext γ φ
  rw [pullback_wedgeForm_apply hdeg h hαB hαBp,
    wedgeForm_oneCurrent_apply hdeg hαA hAS]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ A
  · rw [hcompat x hx]
  · simp only [testFunction_eq_zero_of_notMem φ hx, zero_mul]

/-- Products of compatible smooth semipositive two-forms have the actual
holomorphic current covariance, including all lower-degree products. -/
theorem pullback_smooth_wedgeProduct {r p : ℕ} (hdeg : r + p = n)
    (h : IsBiholomorphicPair A B τ ι)
    (αB αA : Fin p → ComplexModel n → RealForm n 2)
    (hαB : ∀ i, ContDiffOn ℝ ∞ (αB i) B)
    (hαA : ∀ i, ContDiffOn ℝ ∞ (αA i) A)
    (hαBp : ∀ i y, y ∈ B → IsSemipositiveOneOne (αB i y))
    (hcompat : ∀ i x, x ∈ A → αA i x =
      (αB i (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars ℝ)) :
    pullback h (isPositive_wedgeForm hdeg isPositive_oneCurrent
      (contDiffOn_wedgeProd p αB hαB)
      (fun y hy => wedgeProd_mem_spCone p _ (fun i => hαBp i y hy))) =
      wedgeForm hdeg (oneCurrent A) (contDiffOn_wedgeProd p αA hαA) := by
  apply pullback_wedgeForm_of_tensor_compatibility hdeg h
    (contDiffOn_wedgeProd p αB hαB) (contDiffOn_wedgeProd p αA hαA)
    (fun y hy => wedgeProd_mem_spCone p _ (fun i => hαBp i y hy))
  intro x hx
  rw [wedgeProd_comp_map]
  congr 1
  funext i
  exact hcompat i x hx

/-- Smooth positive factors give positivity of the literal expansion by
the actual exterior identity. The residual itself may have either sign. -/
theorem isPositive_smooth_backgroundExpansion {U : Opens (ComplexModel n)}
    (p r : ℕ) (T : LocalProductCurrent n U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) U)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) U)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U)
    (hσS : ∀ z ∈ U, σ z ∈ formSpan n 1)
    (hforms : ∀ i z, z ∈ U → IsSemipositiveOneOne (ddcForm (v i) z + σ z)) :
    IsPositive (backgroundExpansion p r v hσ T) := by
  rw [backgroundExpansion_smooth p r v hv hvp hσ hσS T hT hTc]
  exact isPositive_wedgeForm_smooth_product rfl hT _
    (fun i => (contDiffOn_ddcForm (hv i)).add hσ) hforms

private theorem wedgeForm_oneCurrentOf {r p : ℕ} (hdeg : r + p = n)
    {U : Opens (ComplexModel n)} {α : ComplexModel n → RealForm n (2 * p)}
    (hα : ContDiffOn ℝ ∞ α U) :
    wedgeForm rfl (oneCurrentOf (U := U) hdeg) hα =
      wedgeForm hdeg (oneCurrent U) hα := by
  cases hdeg
  rfl

private theorem pullback_congr_current {r : ℕ}
    (h : IsBiholomorphicPair A B τ ι) {S T : LocalProductCurrent n B r}
    (hS : IsPositive S) (hT : IsPositive T) (heq : S = T) :
    pullback h hS = pullback h hT := by
  subst T
  rfl

/-- The actual smooth nonclosed-background expansion is holomorphically
covariant for every `p ≤ n`. The residual compatibility is only the
pointwise tensor law, and target positivity is not an input. -/
theorem pullback_smooth_backgroundExpansion {r p : ℕ} (hdeg : r + p = n)
    (h : IsBiholomorphicPair A B τ ι)
    (v : Fin p → ComplexModel n → ℝ)
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) B)
    (hvp : ∀ i, PlurisubharmonicOn (fun z => (v i z : EReal)) B)
    {σB σA : ComplexModel n → RealForm n 2}
    (hσB : ContDiffOn ℝ ∞ σB B) (hσA : ContDiffOn ℝ ∞ σA A)
    (hσBS : ∀ z ∈ B, σB z ∈ formSpan n 1)
    (hσcomp : ∀ x ∈ A, σA x =
      (σB (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars ℝ))
    (hforms : ∀ i z, z ∈ B → IsSemipositiveOneOne (ddcForm (v i) z + σB z)) :
    pullback h (isPositive_smooth_backgroundExpansion p r (oneCurrentOf hdeg)
      (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)
      v hv hvp hσB hσBS hforms) =
      backgroundExpansion p r (fun i x => v i (τ x)) hσA (oneCurrentOf (U := A) hdeg) := by
  classical
  have hvA (i : Fin p) : ContDiffOn ℝ ∞ (fun x => v i (τ x)) A :=
    (hv i).comp (h.holo.restrict_scalars ℝ) h.mapsTo
  have hvpA (i : Fin p) : PlurisubharmonicOn (fun x => (v i (τ x) : EReal)) A :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic A.isOpen
      (h.holo.differentiableOn (by simp)) h.mapsTo (hvp i)
  have hσAS : ∀ x ∈ A, σA x ∈ formSpan n 1 := by
    intro x hx
    rw [hσcomp x hx]
    exact compContinuousLinearMap_mem_formSpan (fderiv ℂ τ x) (hσBS _ (h.mapsTo hx))
  let αB : Fin p → ComplexModel n → RealForm n 2 := fun i z => ddcForm (v i) z + σB z
  let αA : Fin p → ComplexModel n → RealForm n 2 :=
    fun i z => ddcForm (fun x => v i (τ x)) z + σA z
  have hαB (i : Fin p) : ContDiffOn ℝ ∞ (αB i) B := (contDiffOn_ddcForm (hv i)).add hσB
  have hαA (i : Fin p) : ContDiffOn ℝ ∞ (αA i) A := (contDiffOn_ddcForm (hvA i)).add hσA
  have hcompat : ∀ i x, x ∈ A → αA i x =
      (αB i (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars ℝ) := by
    intro i x hx
    have hd := HolomorphicDDC.smoothDDC_comp A.isOpen B.isOpen h.holo (hv i) h.mapsTo hx
    rw [fderiv_real_eq h hx] at hd
    change smoothDDC (fun y => v i (τ y)) x + σA x =
      (smoothDDC (v i) (τ x) + σB (τ x)).compContinuousLinearMap
        ((fderiv ℂ τ x).restrictScalars ℝ)
    rw [hd, hσcomp x hx]
    ext d
    rfl
  have hposB := isPositive_wedgeForm hdeg isPositive_oneCurrent
    (contDiffOn_wedgeProd p αB hαB) (fun y hy => wedgeProd_mem_spCone p _ (fun i => hforms i y hy))
  have eB : backgroundExpansion p r v hσB (oneCurrentOf (U := B) hdeg) =
      wedgeForm hdeg (oneCurrent B) (contDiffOn_wedgeProd p αB hαB) :=
    (backgroundExpansion_smooth p r v hv hvp hσB hσBS (oneCurrentOf hdeg)
      (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)).trans
      (wedgeForm_oneCurrentOf hdeg _)
  have eA : backgroundExpansion p r (fun i x => v i (τ x)) hσA (oneCurrentOf (U := A) hdeg) =
      wedgeForm hdeg (oneCurrent A) (contDiffOn_wedgeProd p αA hαA) :=
    (backgroundExpansion_smooth p r _ hvA hvpA hσA hσAS (oneCurrentOf hdeg)
      (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)).trans
      (wedgeForm_oneCurrentOf hdeg _)
  rw [pullback_congr_current h _ hposB eB, eA]
  exact pullback_smooth_wedgeProduct hdeg h αB αA hαB hαA hforms hcompat

/-- Passing to the actual decreasing bounded-potential limit preserves
the smooth covariance identity. This support lemma is used only after the
radial producer has manufactured the smooth positive approximants. -/
private theorem locallyBoundedPsh_comp (h : IsBiholomorphicPair A B τ ι)
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn B w) :
    IsLocallyBoundedPshOn A (fun x => w (τ x)) := by
  refine ⟨HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    (u := fun z => (w z : EReal)) A.isOpen
    (h.holo.differentiableOn (by simp)) h.mapsTo hw.1, fun z hz => ?_⟩
  obtain ⟨V, hzV, hVB, C, hC⟩ := hw.2 (τ z) (h.mapsTo hz)
  exact ⟨preOpen h V, ⟨hz, hzV⟩, preOpen_le h V, C, fun x hx => hC (τ x) hx.2⟩

theorem pullback_backgroundExpansion_of_smooth_decreasing
    {r p : ℕ} (hdeg : r + p = n) (h : IsBiholomorphicPair A B τ ι)
    (f : ℕ → Fin p → ComplexModel n → ℝ) (v : Fin p → ComplexModel n → ℝ)
    (hf : ∀ j i, IsSmoothPshOn B (f j i))
    (hv : ∀ i, IsLocallyBoundedPshOn B (v i))
    (hanti : ∀ i z, z ∈ B → Antitone (fun j => f j i z))
    (hlim : ∀ i z, z ∈ B → Tendsto (fun j => f j i z) atTop (𝓝 (v i z)))
    {σB σA : ComplexModel n → RealForm n 2}
    (hσB : ContDiffOn ℝ ∞ σB B) (hσA : ContDiffOn ℝ ∞ σA A)
    (hσBS : ∀ z ∈ B, σB z ∈ formSpan n 1)
    (hσcomp : ∀ x ∈ A, σA x =
      (σB (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars ℝ))
    (hforms : ∀ j i z, z ∈ B → IsSemipositiveOneOne (ddcForm (f j i) z + σB z))
    (hpos : IsPositive (backgroundExpansion p r v hσB (oneCurrentOf hdeg))) :
    pullback h hpos =
      backgroundExpansion p r (fun i x => v i (τ x)) hσA (oneCurrentOf (U := A) hdeg) := by
  have hfj (j : ℕ) (i : Fin p) : IsLocallyBoundedPshOn B (f j i) :=
    isLocallyBoundedPshOn_of_isSmoothPshOn (hf j i)
  have hposj (j : ℕ) := isPositive_smooth_backgroundExpansion p r (oneCurrentOf hdeg)
    (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)
    (f j) (fun i => (hf j i).1) (fun i => (hf j i).2.1) hσB hσBS (hforms j)
  have hB := backgroundExpansion_decreasing p r (oneCurrentOf hdeg)
    (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)
    f v hfj hv hanti hlim hσB
  have hA := backgroundExpansion_decreasing p r (oneCurrentOf (U := A) hdeg)
    (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)
    (fun j i x => f j i (τ x)) (fun i x => v i (τ x))
    (fun j i => locallyBoundedPsh_comp h (hfj j i))
    (fun i => locallyBoundedPsh_comp h (hv i))
    (fun i x hx => hanti i (τ x) (h.mapsTo hx))
    (fun i x hx => hlim i (τ x) (h.mapsTo hx)) hσA
  have heq (j : ℕ) : pullback h (hposj j) =
      backgroundExpansion p r (fun i x => f j i (τ x)) hσA (oneCurrentOf (U := A) hdeg) :=
    pullback_smooth_backgroundExpansion hdeg h (f j)
      (fun i => (hf j i).1) (fun i => (hf j i).2.1)
      hσB hσA hσBS hσcomp (hforms j)
  ext γ φ
  apply tendsto_nhds_unique (weakTendsto_pullback h hposj hpos hB γ φ)
  simpa only [heq] using hA γ φ

/-- A canonical smooth error form on the source of a coordinate change.
It is the actual `ddc` of the pulled-back flat quadratic. -/
def pulledFlatForm (τ : ComplexModel n → ComplexModel n) (x : ComplexModel n) :
    RealForm n 2 := ddcForm (fun z => flatQuadratic (τ z)) x

theorem contDiffOn_pulledFlatForm (h : IsBiholomorphicPair A B τ ι) :
    ContDiffOn ℝ ∞ (pulledFlatForm τ) A :=
  contDiffOn_ddcForm (contDiff_flatQuadratic.contDiffOn.comp
    (h.holo.restrict_scalars ℝ) h.mapsTo)

theorem pulledFlatForm_tensor (h : IsBiholomorphicPair A B τ ι) (x : ComplexModel n)
    (hx : x ∈ A) :
    pulledFlatForm τ x = (kahlerForm n).compContinuousLinearMap
      ((fderiv ℂ τ x).restrictScalars ℝ) := by
  have hd := HolomorphicDDC.smoothDDC_comp A.isOpen B.isOpen h.holo
    contDiff_flatQuadratic.contDiffOn h.mapsTo hx
  rw [fderiv_real_eq h hx, smoothDDC_flatQuadratic] at hd
  exact hd

/-- On a buffered source domain the actual common radial systems prove
bounded-potential covariance. Both the smooth positive-error limit and the
zero-error limit are constructed here; no target positivity or covariance
certificate is an input. -/
theorem pullback_backgroundExpansion_of_radialSystems
    {m : ℕ} {U V A : Opens (ComplexModel (m + 1))}
    {τ ι : ComplexModel (m + 1) → ComplexModel (m + 1)}
    (hVU : V ≤ U) {r p : ℕ} (hdeg : r + p = m + 1)
    (h : IsBiholomorphicPair A V τ ι)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σB σA : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσB : ContDiffOn ℝ ∞ σB U) (hσA : ContDiffOn ℝ ∞ σA A)
    (hσB11 : ∀ z ∈ U, IsOneOne (σB z))
    (hσcomp : ∀ x ∈ A, σA x =
      (σB (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars ℝ))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσB))
    {R : ℝ} {K : Set (ComplexModel (m + 1))}
    (S : (i : Fin p) → RadialConvolutionSystem V K (v i) R)
    (hR : 0 < R) (hK : IsCompact K) (hKU : K ⊆ U)
    (hVK : (V : Set (ComplexModel (m + 1))) ⊆ K) :
    pullback h (isPositive_backgroundExpansion_of_radialSystems hVU p r
      (oneCurrentOf hdeg) (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)
      v hv hσB hσB11 hfactor S hR hK hKU hVK) =
      backgroundExpansion p r (fun i x => v i (τ x)) hσA (oneCurrentOf (U := A) hdeg) := by
  classical
  let f : ℕ → Fin p → ComplexModel (m + 1) → ℝ :=
    fun j i => translationPairing volume (K.indicator (v i)) ((S i).kernel j)
  have hf (i : Fin p) : IsDecreasingApproximation V (v i) (fun j => f j i) :=
    radialSystem_isDecreasingApproximation (hv i) hVU (S i) hK hKU
  have hvV (i : Fin p) : IsLocallyBoundedPshOn V (v i) :=
    isLocallyBoundedPshOn_mono (hv i) hVU
  have hβA := contDiffOn_pulledFlatForm h
  have hσVS : ∀ z ∈ V, σB z ∈ formSpan (m + 1) 1 :=
    fun z hz => oneOne_mem_formSpan (hσB11 z (hVU hz))
  have hBlim (ε : ℝ) := backgroundExpansion_decreasing p r (oneCurrentOf (U := V) hdeg)
    (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg) f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hvV
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz)
    ((hσB.mono hVU).add ((contDiffOn_const (c := kahlerForm (m + 1))).const_smul ε))
  have hevent (ε : ℝ) (hε : 0 < ε) : ∀ᶠ j in atTop, ∀ i z, z ∈ V →
      IsSemipositiveOneOne (ddcForm (f j i) z + (σB z + ε • kahlerForm (m + 1))) := by
    apply Filter.eventually_all.mpr
    intro i
    obtain ⟨N, hN⟩ := radial_correctedForm_eventually_semipositive
      (hv i) hσB hσB11 (hfactor i) (S i) hR hK hKU hVK ε hε
    exact (Filter.eventually_atTop.mpr ⟨N, hN⟩).mono fun j hj z hz => by
      simpa only [ddcForm, add_assoc] using hj z hz
  have hσepsS (ε : ℝ) : ∀ z ∈ V, σB z + ε • kahlerForm (m + 1) ∈ formSpan (m + 1) 1 :=
    fun z hz => (formSpan (m + 1) 1).add_mem (hσVS z hz)
      ((formSpan (m + 1) 1).smul_mem ε (oneOne_mem_formSpan isSemipositiveOneOne_kahlerForm.1))
  have hposε (ε : ℝ) (hε : 0 < ε) : IsPositive (backgroundExpansion p r v
      ((hσB.mono hVU).add ((contDiffOn_const (c := kahlerForm (m + 1))).const_smul ε))
      (oneCurrentOf hdeg)) := by
    apply isPositive_of_eventually_weakTendsto (hevent ε hε |>.mono ?_) (hBlim ε)
    intro j hj
    exact isPositive_smooth_backgroundExpansion p r (oneCurrentOf hdeg)
      (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg) (f j)
      (fun i => ((hf i).1 j).1) (fun i => ((hf i).1 j).2.1)
      _ (hσepsS ε) hj
  have hcovε (ε : ℝ) (hε : 0 < ε) : pullback h (hposε ε hε) =
      backgroundExpansion p r (fun i x => v i (τ x))
        (hσA.add (hβA.const_smul ε)) (oneCurrentOf (U := A) hdeg) := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hevent ε hε)
    apply pullback_backgroundExpansion_of_smooth_decreasing hdeg h
      (fun j => f (j + N)) v (fun j i => (hf i).1 (j + N)) hvV
      (fun i z hz a b hab => (hf i).2.1 z hz (Nat.add_le_add_right hab N))
      (fun i z hz => ((hf i).2.2 z hz).comp (tendsto_add_atTop_nat N))
      _ _ (hσepsS ε) _ (fun j => hN (j + N) (Nat.le_add_left N j)) (hposε ε hε)
    intro x hx
    rw [pulledFlatForm_tensor h x hx, hσcomp x hx]
    ext d
    simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hpos₀ := isPositive_backgroundExpansion_of_radialSystems hVU p r
    (oneCurrentOf hdeg) (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)
    v hv hσB hσB11 hfactor S hR hK hKU hVK
  have hpb := weakTendsto_pullback h (fun j => hposε (ε j) (hε j)) hpos₀
    (backgroundExpansion_affine_residual p r v (oneCurrentOf hdeg)
      (hσB.mono hVU) contDiffOn_const tendsto_one_div_add_atTop_nhds_zero_nat)
  have htarget := backgroundExpansion_affine_residual p r (fun i x => v i (τ x))
    (oneCurrentOf (U := A) hdeg) hσA hβA tendsto_one_div_add_atTop_nhds_zero_nat
  have heq (j : ℕ) : pullback h (hposε (ε j) (hε j)) =
      backgroundExpansion p r (fun i x => v i (τ x))
        (hσA.add (hβA.const_smul (ε j))) (oneCurrentOf (U := A) hdeg) :=
    hcovε (ε j) (hε j)
  ext γ φ
  apply tendsto_nhds_unique (hpb γ φ)
  simpa only [heq] using htarget γ φ

private theorem restrict_unit {U V : Opens (ComplexModel n)} (hVU : V ≤ U)
    {r p : ℕ} (hdeg : r + p = n) :
    restrict hVU (oneCurrentOf (U := U) hdeg) = oneCurrentOf (U := V) hdeg := by
  cases hdeg
  exact restrict_oneCurrent hVU

/-- Holomorphic covariance of the actual locally bounded nonclosed-background
product in every degree. Its inputs are the original bounded PSH factors,
their actual positive one-one currents, and the smooth residual tensor law.
All buffers, radial approximations, positive errors, and both weak limits
are produced internally. -/
theorem pullback_backgroundExpansion
    {m : ℕ} {A B : Opens (ComplexModel (m + 1))}
    {τ ι : ComplexModel (m + 1) → ComplexModel (m + 1)}
    {r p : ℕ} (hdeg : r + p = m + 1) (h : IsBiholomorphicPair A B τ ι)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn B (v i))
    {σB σA : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσB : ContDiffOn ℝ ∞ σB B) (hσA : ContDiffOn ℝ ∞ σA A)
    (hσB11 : ∀ z ∈ B, IsOneOne (σB z))
    (hσcomp : ∀ x ∈ A, σA x =
      (σB (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars ℝ))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent B) (v i) + wedgeForm rfl (oneCurrent B) hσB)) :
    pullback h (isPositive_backgroundExpansion p r (oneCurrentOf hdeg)
      (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)
      v hv hσB hσB11 hfactor) =
      backgroundExpansion p r (fun i x => v i (τ x)) hσA (oneCurrentOf (U := A) hdeg) := by
  classical
  ext γ φ
  have hK : IsCompact (τ '' tsupport φ) :=
    φ.hasCompactSupport.image_of_continuousOn (h.holo.continuousOn.mono φ.tsupport_subset)
  have hKB : τ '' tsupport φ ⊆ B :=
    image_subset_iff.mpr fun x hx => h.mapsTo (φ.tsupport_subset hx)
  obtain ⟨W₀, hWo, hKW, hWcl, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK B.isOpen hKB
  let W : Opens (ComplexModel (m + 1)) := ⟨W₀, hWo⟩
  have hWrc : RelativelyCompactIn W B := ⟨hWc, hWcl⟩
  obtain ⟨R, hR, V, K, hWV, hVB, hK, hKB, hVK, S, _⟩ :=
    exists_common_radial_systems hWrc v hv
  let h' := isBiholomorphicPair_preOpen h hVB
  have hφA' : tsupport φ ⊆ preOpen h V :=
    fun x hx => ⟨φ.tsupport_subset hx, hWV (hKW ⟨x, hx, rfl⟩)⟩
  let φ' : 𝓓(preOpen h V, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφA'⟩
  have hext : extTest (preOpen_le h V) φ' = φ := by
    ext x
    rw [extTest_apply]
    rfl
  have hposB := isPositive_backgroundExpansion p r (oneCurrentOf hdeg)
    (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg) v hv hσB hσB11 hfactor
  have hposV := isPositive_backgroundExpansion_of_radialSystems hVB p r (oneCurrentOf hdeg)
    (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)
    v hv hσB hσB11 hfactor S hR hK hKB hVK
  have eB : restrict hVB (backgroundExpansion p r v hσB (oneCurrentOf hdeg)) =
      backgroundExpansion p r v (hσB.mono hVB) (oneCurrentOf (U := V) hdeg) := by
    rw [backgroundExpansion_restrict hVB p r (oneCurrentOf hdeg)
      (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg) v hv hσB,
      restrict_unit hVB hdeg]
  have e1 : pullback h hposB γ φ = pullback h' hposV γ φ' := by
    rw [← hext, ← LocalBedfordTaylorLocality.restrict_apply, ← pullback_restrict h hposB hVB]
    rw [pullback_congr_current h' _ hposV eB]
  have e2 : pullback h' hposV =
      backgroundExpansion p r (fun i x => v i (τ x))
        (hσA.mono (preOpen_le h V)) (oneCurrentOf (U := preOpen h V) hdeg) :=
    pullback_backgroundExpansion_of_radialSystems hVB hdeg h' v hv hσB
      (hσA.mono (preOpen_le h V)) hσB11 (fun x hx => hσcomp x hx.1)
      hfactor S hR hK hKB hVK
  rw [e1, e2, ← restrict_unit (preOpen_le h V) hdeg,
    ← backgroundExpansion_restrict (preOpen_le h V) p r (oneCurrentOf hdeg)
      (isPositive_oneCurrentOf hdeg) (isClosedAny_oneCurrentOf hdeg)
      (fun i x => v i (τ x)) (fun i => locallyBoundedPsh_comp h (hv i)) hσA,
    LocalBedfordTaylorLocality.restrict_apply, hext]

end SGPT.PSH.HermitianProducts
