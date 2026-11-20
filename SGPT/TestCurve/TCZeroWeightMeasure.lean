import SGPT.TestCurve.SrcRevDHMass
import SGPT.Projective.OkounkovOriginalBookVolume
import SGPT.Okounkov.PobDimZeroCore
import Mathlib.MeasureTheory.Measure.DiracProba

/-! Actual zero-dimensional original jumping measures and their genuine weak limit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.ZeroDH
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov
open SGPT.NAPotential.NANS.TestConfig
open scoped Topology ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}

/-- Actual maximal jumping number equals the original first successive minimum. -/
theorem succMin_zero_eq_jump_toReal (F : SectionFiltration f a) {k : ℕ} (hk : 0 < k)
    [FiniteDimensional ℂ (SectionSpace f L k)] [Nontrivial (SectionSpace f L k)] :
    F.succMin k 0 = (F.jump k).toReal := by
  have hpos : 0 < Module.finrank ℂ (SectionSpace f L k) := Module.finrank_pos_iff.mpr inferInstance
  have hp (μ : ℝ) : 0 < F.pieceDim μ k ↔ F.piece μ k ≠ ⊥ := by
    simp only [Nat.pos_iff_ne_zero, SectionFiltration.pieceDim, ne_eq, Submodule.finrank_eq_zero]
  have hiff (μ : ℝ) : μ ≤ F.succMin k 0 ↔ μ ≤ (F.jump k).toReal := by
    rw [← F.lt_pieceDim_iff hk hpos μ, hp, F.piece_ne_bot_iff μ, F.jump_eq_coe hk,
      EReal.coe_le_coe_iff]
    simp only [EReal.toReal_coe]
  exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)

variable [IsIntegral X] [SmoothOfRelativeDimension 0 f] (E : ClosedProjectiveEmbedding f)
include E

/-- The actual original section spaces have dimension one, without a caller-supplied flag. -/
theorem original_h0_eq_one (a : LineBundleAtlas L) (k : ℕ) :
    Module.finrank ℂ (SectionSpace f L k) = 1 := by
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  obtain ⟨Y, hY⟩ := SGPT.Okounkov.OriginalBook.exists_original_smoothFlag_allDimensions f 0 E
  exact PobDimZero.h0_eq_one f E Y hY a k

/-- The actual original jumping measure is literally one Dirac mass in dimension zero. -/
theorem jumpMeasure_eq_dirac (F : SectionFiltration f a) (k : ℕ) :
    F.jumpMeasure k = Measure.dirac (F.succMin k 0 / (k : ℝ)) := by
  simp [SectionFiltration.jumpMeasure, original_h0_eq_one E a k]

/-- The genuine original normalized weights converge to Dirac at the original slope. -/
theorem normalized_weights_tendsto_dirac_slope (F : SectionFiltration f a) :
    Tendsto (fun j : ℕ => (rescaledFiniteMeasure F 0 j).normalize) atTop
      (𝓝 (diracProba F.slope.toReal)) := by
  let (k : ℕ) : FiniteDimensional ℂ (SectionSpace f L k) := SectionSpace.finiteDimensional f E a k
  have hn (k : ℕ) : Nontrivial (SectionSpace f L k) :=
    Module.nontrivial_of_finrank_pos (show 0 < Module.finrank ℂ (SectionSpace f L k) by
      rw [original_h0_eq_one E a k]; omega)
  let : Nontrivial (SectionSpace f L 1) := hn 1
  have hbot : F.slope ≠ ⊥ := F.slope_ne_bot (k := 1) (by omega)
  have hlim := (EReal.tendsto_toReal F.slope_ne_top hbot).comp
    (F.tendsto_jump_div_slope (Eventually.of_forall hn))
  have hshift := hlim.comp (tendsto_add_atTop_nat 1)
  have hreal : Tendsto (fun j : ℕ => F.succMin (j+1) 0 / ((j+1 : ℕ) : ℝ)) atTop
      (𝓝 F.slope.toReal) := by
    apply hshift.congr
    intro j
    let : Nontrivial (SectionSpace f L (j+1)) := hn (j+1)
    change (F.jump (j+1) / (((j+1 : ℕ) : ℝ) : EReal)).toReal =
      F.succMin (j+1) 0 / ((j+1 : ℕ) : ℝ)
    rw [F.jump_eq_coe (k := j+1) (by omega), ← EReal.coe_div, EReal.toReal_coe,
      succMin_zero_eq_jump_toReal F (by omega)]
  have hp (j : ℕ) : (rescaledFiniteMeasure F 0 j).normalize =
      diracProba (F.succMin (j+1) 0 / ((j+1 : ℕ) : ℝ)) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [normalize_rescaledFiniteMeasure F 0 j (by rw [original_h0_eq_one E a]; simp)]
    simp [SectionFiltration.bhjWeightMeasure, original_h0_eq_one E a, jumpMeasure_eq_dirac E F,
      diracProba]
  exact (continuous_diracProba.tendsto F.slope.toReal |>.comp hreal).congr fun j => (hp j).symm

/-- The SAME original ample self-intersection has its correct dimension-zero value. -/
theorem original_selfIntersection_eq_one (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    P.selfIntersection 0 = 1 := by
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  obtain ⟨Y, hY⟩ := SGPT.Okounkov.OriginalBook.exists_original_smoothFlag_allDimensions f 0 E
  have h := P.volume_eq_selfIntersection 0 a
  rw [PobDimZero.lineBundle_volume_eq_one f E Y hY a] at h
  have hreal := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_one, ENNReal.toReal_ofReal (P.selfIntersection_nonneg 0)] using hreal.symm

end SGPT.TestCurve.ZeroDH
