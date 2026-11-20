import SGPT.PSH.HermitianProductsMeasureScaling

/-!
# Actual product inequality for rescaling a bounded Hermitian potential

A single chosen smooth correction is used for the original and scaled
potentials. Homogeneity, correction independence and smooth-background
monotonicity give the degree-power comparison of the genuine currents.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorForms LocalBedfordTaylorCollar
  LocalCurrentDensityMatrix
open scoped Topology Distributions ContDiff

variable {m : ℕ} {U : Opens (ComplexModel (m + 1))}

/-- The original bounded Hermitian product is dominated by `c^p` times the
product of the potential divided by `c ≥ 1`, using the same genuine smooth
correction on both sides. -/
theorem isPositive_backgroundExpansion_rescale_sub
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (u : Fin p → ComplexModel (m + 1) → ℝ)
    {q : ComplexModel (m + 1) → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    {omega : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (homega : ContDiffOn ℝ ∞ omega U) (homegapos : ∀ z ∈ U, IsSemipositiveOneOne (omega z))
    {c : ℝ} (hc : 1 ≤ c)
    (hv : ∀ i, IsLocallyBoundedPshOn U (fun z => u i z + q z))
    (hw : ∀ i, IsLocallyBoundedPshOn U (fun z => u i z / c + q z))
    (hfactor : ∀ i, IsPositive (ddcMul (oneCurrent U) (fun z => u i z + q z) +
      wedgeForm rfl (oneCurrent U) (homega.sub (contDiffOn_ddcForm hq)))) :
    IsPositive
      (c ^ p • backgroundExpansion p r (fun i z => u i z / c + q z)
        (homega.sub (contDiffOn_ddcForm hq)) T -
      backgroundExpansion p r (fun i z => u i z + q z)
        (homega.sub (contDiffOn_ddcForm hq)) T) := by
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  let v : Fin p → ComplexModel (m + 1) → ℝ := fun i z => u i z + q z
  let w : Fin p → ComplexModel (m + 1) → ℝ := fun i z => u i z / c + q z
  let σ := fun z => omega z - ddcForm q z
  let τ := fun z => (c - 1) • omega z
  let g := fun z => (c - 1) * q z
  have hσ : ContDiffOn ℝ ∞ σ U := homega.sub (contDiffOn_ddcForm hq)
  have hτ : ContDiffOn ℝ ∞ τ U := homega.const_smul (c - 1)
  have hg : ContDiffOn ℝ ∞ g U := hq.const_smul (c - 1)
  have hq11 (z) (hz : z ∈ U) : IsOneOne (ddcForm q z) :=
    smoothDDC_isOneOne ((hq.contDiffAt (U.isOpen.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hσ11 : ∀ z ∈ U, IsOneOne (σ z) :=
    fun z hz => isOneOne_sub (homegapos z hz).1 (hq11 z hz)
  have hσS : ∀ z ∈ U, σ z ∈ formSpan (m + 1) 1 :=
    fun z hz => oneOne_mem_formSpan (hσ11 z hz)
  have hτpos : ∀ z ∈ U, IsSemipositiveOneOne (τ z) :=
    fun z hz => (homegapos z hz).smul (sub_nonneg.mpr hc)
  have hpot (i : Fin p) : (fun z => c * w i z) = (fun z => v i z + g z) := by
    funext z
    dsimp only [v, w, g]
    field_simp [hcpos.ne']
    ring
  have hvg : ∀ i, IsLocallyBoundedPshOn U (fun z => v i z + g z) := by
    intro i
    rw [← hpot i]
    exact isLocallyBoundedPshOn_pos_smul (hw i) hcpos
  have hcorr := backgroundExpansion_add_smooth p r T hT hTc v hv hg hvg
    (hσ.add hτ) (fun z hz => (formSpan (m + 1) 1).add_mem
      (hσS z hz) (oneOne_mem_formSpan (hτpos z hz).1))
  have heq : c ^ p • backgroundExpansion p r w hσ T =
      backgroundExpansion p r v (hσ.add hτ) T := by
    calc
      _ = backgroundExpansion p r (fun i z => c * w i z) (hσ.const_smul c) T :=
        (backgroundExpansion_pos_smul p r T hT hTc w hw hσ hσS hcpos).symm
      _ = backgroundExpansion p r (fun i z => v i z + g z)
          ((hσ.add hτ).sub (contDiffOn_ddcForm hg)) T := by
        apply backgroundExpansion_congr
        · intro i z _
          exact congrFun (hpot i) z
        · intro z hz
          change c • (omega z - smoothDDC q z) =
            (omega z - smoothDDC q z + (c - 1) • omega z) -
              smoothDDC (fun y => (c - 1) • q y) z
          rw [smoothDDC_smul U.isOpen hq (c - 1) hz]
          module
      _ = _ := hcorr
  change IsPositive (c ^ p • backgroundExpansion p r w hσ T - backgroundExpansion p r v hσ T)
  rw [heq]
  exact isPositive_backgroundExpansion_add_sub p r T hT hTc v hv hσ hτ hσ11 hfactor hτpos

theorem isPositive_of_pos_smul {n r : ℕ} {U : Opens (ComplexModel n)}
    {T : LocalProductCurrent n U r} {c : ℝ} (hc : 0 < c)
    (hT : IsPositive (c • T)) : IsPositive T := by
  intro ι _ γ φ hγ
  have h := hT ι γ φ hγ
  simp only [LinearMap.smul_apply, _root_.smul_apply, smul_eq_mul, ← Finset.mul_sum] at h
  exact nonneg_of_mul_nonneg_right h hc

/-- Positivity of the actual product with one chosen smooth correction. -/
theorem isPositive_backgroundExpansion_corrected
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (u : Fin p → ComplexModel (m + 1) → ℝ)
    {q : ComplexModel (m + 1) → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    {omega : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (homega : ContDiffOn ℝ ∞ omega U)
    (homegaPos : ∀ z ∈ U, IsSemipositiveOneOne (omega z))
    (hv : ∀ i, IsLocallyBoundedPshOn U (fun z => u i z + q z))
    (hfactor : ∀ i, IsPositive (ddcMul (oneCurrent U) (fun z => u i z + q z) +
      wedgeForm rfl (oneCurrent U) (homega.sub (contDiffOn_ddcForm hq)))) :
    IsPositive (backgroundExpansion p r (fun i z => u i z + q z)
      (homega.sub (contDiffOn_ddcForm hq)) T) := by
  apply isPositive_backgroundExpansion p r T hT hTc _ hv _ _ hfactor
  intro z hz
  exact isOneOne_sub (homegaPos z hz).1
    (smoothDDC_isOneOne ((hq.contDiffAt (U.isOpen.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)))

/-- Positivity of the rescaled potential's actual product follows from
the proved current comparison, without an extra factor-current premise. -/
theorem isPositive_backgroundExpansion_rescaled
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (u : Fin p → ComplexModel (m + 1) → ℝ)
    {q : ComplexModel (m + 1) → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    {omega : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (homega : ContDiffOn ℝ ∞ omega U)
    (homegaPos : ∀ z ∈ U, IsSemipositiveOneOne (omega z))
    {c : ℝ} (hc : 1 ≤ c)
    (hv : ∀ i, IsLocallyBoundedPshOn U (fun z => u i z + q z))
    (hw : ∀ i, IsLocallyBoundedPshOn U (fun z => u i z / c + q z))
    (hfactor : ∀ i, IsPositive (ddcMul (oneCurrent U) (fun z => u i z + q z) +
      wedgeForm rfl (oneCurrent U) (homega.sub (contDiffOn_ddcForm hq)))) :
    IsPositive (backgroundExpansion p r (fun i z => u i z / c + q z)
      (homega.sub (contDiffOn_ddcForm hq)) T) := by
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hσ11 : ∀ z ∈ U, IsOneOne (omega z - ddcForm q z) := by
    intro z hz
    exact isOneOne_sub (homegaPos z hz).1
      (smoothDDC_isOneOne ((hq.contDiffAt (U.isOpen.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)))
  have hP := isPositive_backgroundExpansion p r T hT hTc _ hv
    (homega.sub (contDiffOn_ddcForm hq)) hσ11 hfactor
  have hD := isPositive_backgroundExpansion_rescale_sub p r T hT hTc u hq homega homegaPos hc
    hv hw hfactor
  apply isPositive_of_pos_smul (pow_pos hcpos p)
  convert hD.add hP using 1; abel

/-- The canonical trace-measure form of the genuine degree-power
rescaling inequality used for bounded Hermitian capacity competitors. -/
theorem traceMeasure_backgroundExpansion_rescale_le
    (p r : ℕ) (T : LocalProductCurrent (m + 1) U (r + p))
    (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (u : Fin p → ComplexModel (m + 1) → ℝ)
    {q : ComplexModel (m + 1) → ℝ} (hq : ContDiffOn ℝ ∞ q U)
    {omega : ComplexModel (m + 1) → RealForm (m + 1) 2}
    (homega : ContDiffOn ℝ ∞ omega U)
    (homegaPos : ∀ z ∈ U, IsSemipositiveOneOne (omega z))
    {c : ℝ} (hc : 1 ≤ c)
    (hv : ∀ i, IsLocallyBoundedPshOn U (fun z => u i z + q z))
    (hw : ∀ i, IsLocallyBoundedPshOn U (fun z => u i z / c + q z))
    (hfactor : ∀ i, IsPositive (ddcMul (oneCurrent U) (fun z => u i z + q z) +
      wedgeForm rfl (oneCurrent U) (homega.sub (contDiffOn_ddcForm hq)))) :
    (isPositive_backgroundExpansion_corrected p r T hT hTc u hq homega homegaPos hv hfactor).traceMeasure ≤
      Real.toNNReal (c ^ p) •
      (isPositive_backgroundExpansion_rescaled p r T hT hTc u hq homega homegaPos hc
        hv hw hfactor).traceMeasure := by
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  let hP := isPositive_backgroundExpansion_corrected p r T hT hTc u hq homega homegaPos hv hfactor
  let hQ := isPositive_backgroundExpansion_rescaled p r T hT hTc u hq homega homegaPos hc
    hv hw hfactor
  have hRight := hQ.smul (pow_nonneg hcpos.le p)
  have hle := LocalBedfordTaylorCalculus.traceMeasure_le_of_isPositive_sub hP hRight
    (isPositive_backgroundExpansion_rescale_sub p r T hT hTc u hq homega homegaPos hc hv hw hfactor)
  have heq : hRight.traceMeasure = Real.toNNReal (c ^ p) • hQ.traceMeasure := by
    apply traceMeasure_eq_smul_of_current_eq _ _ (Real.toNNReal (c ^ p))
    rw [Real.coe_toNNReal _ (pow_nonneg hcpos.le p)]
  rw [heq] at hle
  exact hle

end SGPT.PSH.HermitianProducts
