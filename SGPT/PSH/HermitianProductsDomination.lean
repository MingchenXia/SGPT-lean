import SGPT.PSH.HermitianProductsPositivity

/-!
# Domination by the corrected ordinary Bedford--Taylor product

When the smooth residual is nonpositive, the actual positive Hermitian
product is dominated by the ordinary product of its corrected PSH factors.
The proof uses smooth exterior-product order and the same two limits as
positivity.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorForms LocalBedfordTaylorSmooth
  LocalBedfordTaylorSmoothProductDensity LocalBedfordTaylorContinuity
  LocalBedfordTaylorLocality LocalBedfordTaylorCalculus LocalBedfordTaylorDecreasing
  LocalBedfordTaylorCollar TopDegreeDensity ConstantFormProducts
open scoped Topology Distributions ContDiff

variable {n : ℕ} {U V : Opens (ComplexModel n)}

/-- Increasing each semipositive factor increases its actual exterior
product in the strongly positive cone. -/
theorem wedgeProd_sub_mem_spCone : ∀ (p : ℕ) (α β : Fin p → RealForm n 2),
    (∀ i, IsSemipositiveOneOne (α i)) →
    (∀ i, IsSemipositiveOneOne (β i - α i)) →
    wedgeProd p β - wedgeProd p α ∈ spCone p
  | 0, _, _, _, _ => by simp only [wedgeProd_zero, sub_self]; exact (spCone 0).zero_mem
  | p + 1, α, β, hα, hdiff => by
    have hβlast : IsSemipositiveOneOne (β (Fin.last p)) := by
      convert (hα (Fin.last p)).add (hdiff (Fin.last p)) using 1; abel
    have h₁ := wedge_mem_spCone
      (wedgeProd_sub_mem_spCone p (Fin.init α) (Fin.init β)
        (fun i => hα i.castSucc) (fun i => hdiff i.castSucc)) hβlast
    have h₂ := wedge_mem_spCone
      (wedgeProd_mem_spCone p (Fin.init α) (fun i => hα i.castSucc)) (hdiff (Fin.last p))
    have heq : wedgeProd (p + 1) β - wedgeProd (p + 1) α =
        coordinateWedge (wedgeProd p (Fin.init β) - wedgeProd p (Fin.init α)) (β (Fin.last p)) +
        coordinateWedge (wedgeProd p (Fin.init α)) (β (Fin.last p) - α (Fin.last p)) := by
      simp only [wedgeProd_succ]
      change wedgeToBilin n rfl _ _ - wedgeToBilin n rfl _ _ =
        wedgeToBilin n rfl (_ - _) _ + wedgeToBilin n rfl _ (_ - _)
      simp only [map_sub, LinearMap.sub_apply]
      abel
    rw [heq]
    exact (spCone (p + 1)).add_mem h₁ h₂

/-- The smooth current represented by an increasing finite product of
semipositive forms increases as an actual positive-current inequality. -/
theorem isPositive_wedgeForm_product_sub {p r : ℕ}
    {T : LocalProductCurrent n U (r + p)} (hT : IsPositive T)
    (α β : Fin p → ComplexModel n → RealForm n 2)
    (hα : ∀ i, ContDiffOn ℝ ∞ (α i) U) (hβ : ∀ i, ContDiffOn ℝ ∞ (β i) U)
    (hpos : ∀ i z, z ∈ U → IsSemipositiveOneOne (α i z))
    (hdiff : ∀ i z, z ∈ U → IsSemipositiveOneOne (β i z - α i z)) :
    IsPositive (wedgeForm rfl T (contDiffOn_wedgeProd p β hβ) -
      wedgeForm rfl T (contDiffOn_wedgeProd p α hα)) := by
  rw [← wedgeForm_sub]
  exact isPositive_wedgeForm rfl hT _ (fun z hz =>
    wedgeProd_sub_mem_spCone p _ _ (fun i => hpos i z hz) (fun i => hdiff i z hz))

/-- A zero residual gives the genuine ordinary product, proved on actual
smooth approximants and then by decreasing continuity. -/
theorem backgroundExpansion_zero_of_approximation (p r : ℕ)
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    (f : ℕ → Fin p → ComplexModel n → ℝ)
    (hf : ∀ i, IsDecreasingApproximation U (v i) (fun j => f j i)) :
    backgroundExpansion p r v (contDiffOn_const (c := (0 : RealForm n 2))) T =
      btProduct p r v T := by
  have heq (j : ℕ) :
      backgroundExpansion p r (f j) (contDiffOn_const (c := (0 : RealForm n 2))) T =
        btProduct p r (f j) T := by
    rw [backgroundExpansion_smooth p r _ (fun i => ((hf i).1 j).1)
      (fun i => ((hf i).1 j).2.1) _ (fun _ _ => (formSpan n 1).zero_mem) T hT hTc,
      btProduct_eq_wedgeForm p r _ (fun i => ((hf i).1 j).1)
        (fun i => ((hf i).1 j).2.1) T hT hTc]
    apply wedgeForm_congr
    intro z _
    change wedgeProd p (fun i => ddcForm (f j i) z + 0) =
      wedgeProd p (fun i => ddcForm (f j i) z)
    simp only [add_zero]
  have hleft := backgroundExpansion_decreasing p r T hT hTc f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hv
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz)
    (contDiffOn_const (c := (0 : RealForm n 2)))
  have hright := weakTendsto_btProduct_of_antitone p r T hT hTc f v
    (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j)) hv
    (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz)
  ext γ φ
  apply tendsto_nhds_unique (hleft γ φ)
  simpa only [heq] using hright γ φ

/-- The corrected ordinary product dominates the actual Hermitian expansion
on a domain with visible shared radial convolution systems. -/
theorem isPositive_btProduct_sub_backgroundExpansion_of_radialSystems
    {m : ℕ} {U V : Opens (ComplexModel (m + 1))} (hVU : V ≤ U)
    (p r : ℕ) (T : LocalProductCurrent (m + 1) V (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    (hnegative : ∀ z ∈ U, IsSemipositiveOneOne (-σ z))
    {R : ℝ} {K : Set (ComplexModel (m + 1))}
    (S : (i : Fin p) → RadialConvolutionSystem V K (v i) R)
    (hR : 0 < R) (hK : IsCompact K) (hKU : K ⊆ U)
    (hVK : (V : Set (ComplexModel (m + 1))) ⊆ K) :
    IsPositive (btProduct p r v T - backgroundExpansion p r v (hσ.mono hVU) T) := by
  classical
  let f : ℕ → Fin p → ComplexModel (m + 1) → ℝ :=
    fun j i => translationPairing volume (K.indicator (v i)) ((S i).kernel j)
  have hf (i : Fin p) : IsDecreasingApproximation V (v i) (fun j => f j i) :=
    radialSystem_isDecreasingApproximation (hv i) hVU (S i) hK hKU
  have hfixed (ε : ℝ) (hε : 0 < ε) : IsPositive
      (backgroundExpansion p r v (contDiffOn_const (c := ε • kahlerForm (m + 1))) T -
        backgroundExpansion p r v
          ((hσ.mono hVU).add ((contDiffOn_const (c := kahlerForm (m + 1))).const_smul ε)) T) := by
    have hevent : ∀ᶠ j in atTop, ∀ i z, z ∈ V → IsSemipositiveOneOne
        (smoothDDC (f j i) z + σ z + ε • kahlerForm (m + 1)) := by
      apply Filter.eventually_all.mpr
      intro i
      obtain ⟨N, hN⟩ := radial_correctedForm_eventually_semipositive
        (hv i) hσ hσ11 (hfactor i) (S i) hR hK hKU hVK ε hε
      exact Filter.eventually_atTop.mpr ⟨N, hN⟩
    apply isPositive_of_eventually_weakTendsto (T := fun j =>
      backgroundExpansion p r (f j) (contDiffOn_const (c := ε • kahlerForm (m + 1))) T -
      backgroundExpansion p r (f j) ((hσ.mono hVU).add ((contDiffOn_const (c := kahlerForm (m + 1))).const_smul ε)) T)
    · apply hevent.mono
      intro j hj
      rw [backgroundExpansion_smooth p r _ (fun i => ((hf i).1 j).1)
        (fun i => ((hf i).1 j).2.1) _ (fun _ _ =>
          (formSpan (m + 1) 1).smul_mem ε
            (oneOne_mem_formSpan isSemipositiveOneOne_kahlerForm.1)) T hT hTc,
        backgroundExpansion_smooth p r _ (fun i => ((hf i).1 j).1)
          (fun i => ((hf i).1 j).2.1) _ (fun z hz =>
            (formSpan (m + 1) 1).add_mem (oneOne_mem_formSpan (hσ11 z (hVU hz)))
              ((formSpan (m + 1) 1).smul_mem ε
                (oneOne_mem_formSpan isSemipositiveOneOne_kahlerForm.1))) T hT hTc]
      refine isPositive_wedgeForm_product_sub hT _ _
        (fun i => (contDiffOn_ddcForm ((hf i).1 j).1).add
          ((hσ.mono hVU).add (contDiffOn_const (c := ε • kahlerForm (m + 1)))))
        (fun i => (contDiffOn_ddcForm ((hf i).1 j).1).add
          (contDiffOn_const (c := ε • kahlerForm (m + 1)))) ?_ ?_
      · intro i z hz
        simpa only [ddcForm, add_assoc] using hj i z hz
      · intro i z hz
        convert hnegative z (hVU hz) using 1; abel
    · intro γ φ
      exact (backgroundExpansion_decreasing p r T hT hTc f v
        (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j))
        (fun i => isLocallyBoundedPshOn_mono (hv i) hVU)
        (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) _ γ φ).sub
          (backgroundExpansion_decreasing p r T hT hTc f v
            (fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf i).1 j))
            (fun i => isLocallyBoundedPshOn_mono (hv i) hVU)
            (fun i z hz => (hf i).2.1 z hz) (fun i z hz => (hf i).2.2 z hz) _ γ φ)
  have hzero := backgroundExpansion_zero_of_approximation p r T hT hTc v
    (fun i => isLocallyBoundedPshOn_mono (hv i) hVU) f hf
  rw [← hzero]
  apply LocalBedfordTaylorContinuity.isPositive_of_weakTendsto
    (T := fun j => backgroundExpansion p r v
      (contDiffOn_const (c := (1 / ((j : ℝ) + 1)) • kahlerForm (m + 1))) T -
      backgroundExpansion p r v
        ((hσ.mono hVU).add ((contDiffOn_const (c := kahlerForm (m + 1))).const_smul (1 / ((j : ℝ) + 1)))) T)
  · intro j
    exact hfixed _ (by positivity)
  · intro γ φ
    have h₁ := backgroundExpansion_affine_residual p r v T
      (contDiffOn_const (c := (0 : RealForm (m + 1) 2)))
      (contDiffOn_const (c := kahlerForm (m + 1)))
      tendsto_one_div_add_atTop_nhds_zero_nat γ φ
    have h₂ := backgroundExpansion_affine_residual p r v T (hσ.mono hVU)
      (contDiffOn_const (c := kahlerForm (m + 1)))
      tendsto_one_div_add_atTop_nhds_zero_nat γ φ
    simpa only [zero_add, LinearMap.sub_apply, _root_.sub_apply] using h₁.sub h₂

/-- An actual local Hermitian product is dominated by the ordinary product
of its corrected bounded PSH factors when the smooth correction dominates
the background. -/
theorem isPositive_btProduct_sub_backgroundExpansion
    {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    (hnegative : ∀ z ∈ U, IsSemipositiveOneOne (-σ z)) :
    IsPositive (btProduct p r v T - backgroundExpansion p r v hσ T) := by
  apply LocalPositiveCurrentGluing.isPositive_of_local_restrict
  intro x hx
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  let A : Opens (ComplexModel (m + 1)) := ⟨ball x (a / 2), isOpen_ball⟩
  have hAU : RelativelyCompactIn A U := relativelyCompactIn_half_ball ha hball
  obtain ⟨R, hR, V, K, hAV, hVU, hK, hKU, hVK, S, _⟩ :=
    exists_common_radial_systems hAU v hv
  refine ⟨V, hVU, hAV (mem_ball_self (half_pos ha)), ?_⟩
  change IsPositive (restrict hVU (btProduct p r v T) -
    restrict hVU (backgroundExpansion p r v hσ T))
  rw [← btProduct_restrict hVU p r v T hT hTc hv,
    backgroundExpansion_restrict hVU p r T hT hTc v hv hσ]
  exact isPositive_btProduct_sub_backgroundExpansion_of_radialSystems hVU p r
    (restrict hVU T) (isPositive_restrict hT hVU) (isClosedAny_restrict hTc hVU)
    v hv hσ hσ11 hfactor hnegative S hR hK hKU hVK

/-- The canonical Riesz trace of the actual Hermitian expansion is
dominated by the trace of its corrected ordinary product. -/
theorem traceMeasure_backgroundExpansion_le_btProduct
    {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (v : Fin p → ComplexModel (m + 1) → ℝ)
    (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    {σ : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (hσ : ContDiffOn ℝ ∞ σ U) (hσ11 : ∀ z ∈ U, IsOneOne (σ z))
    (hfactor : ∀ i, IsPositive
      (ddcMul (oneCurrent U) (v i) + wedgeForm rfl (oneCurrent U) hσ))
    (hnegative : ∀ z ∈ U, IsSemipositiveOneOne (-σ z)) :
    (isPositive_backgroundExpansion p r T hT hTc v hv hσ hσ11 hfactor).traceMeasure ≤
      (isPositive_btProduct p r v T hT hTc hv).1.traceMeasure :=
  traceMeasure_le_of_isPositive_sub
    (isPositive_backgroundExpansion p r T hT hTc v hv hσ hσ11 hfactor)
    (isPositive_btProduct p r v T hT hTc hv).1
    (isPositive_btProduct_sub_backgroundExpansion p r T hT hTc v hv hσ hσ11 hfactor hnegative)

end SGPT.PSH.HermitianProducts
