import SGPT.NPP.DN5Regularity
import SGPT.NPP.DN5Interface

/-!
# Assembly of the joint smoothing (`SGPT.NPP.DN2.JointSmoothingStatement`)

Lane DN5, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, lines 12–368).

For gluing data `A` (`SGPT.NPP.DN5.exists_fibreAtlas`) and a uniform radius
(`SGPT.NPP.DN5.exists_isUniformRadius`), the smoothing `Ψ = SGPT.NPP.DN5.smoothing wY A` has the
fields `contDiffOn`, `mono`, `neg`, `add_const` of `SGPT.NPP.DN2.IsJointSmoothing`
(`SGPT.NPP.DN5Regularity`, `SGPT.NPP.DN5Smoothing`).  The two remaining fields are the hypotheses
of the assembly:

* `generator` — `SGPT.NPP.DN5.GeneratorEstimate`;
* `psh` — `SmoothingPshStatement` below: for every uniform radius `r₁` some `r₀ ∈ (0, r₁]`
  carries the `psh` field (`PshField`) for `Ψ`; it is to be derived from the chart-level estimate
  `SGPT.NPP.DN5.LocalJointEstimate` by the uniformity argument of FPT ("all bounds are
  uniform over the centers, because the constructions are made in the charts of a fixed finite
  atlas").

`jointSmoothingStatement_of` proves `SGPT.NPP.DN2.JointSmoothingStatement` from these two.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN5

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open KahlerLaplacianChart IntegrationCurrent
open SGPT.NPP.DN2

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The `psh` field of `SGPT.NPP.DN2.IsJointSmoothing` (verbatim). -/
def PshField (wY : KahlerBackground N Y) (r₀ : ℝ) (Ψ : (Y → ℝ) → Y → ℝ → ℝ) : Prop :=
  ∀ (θ : ClosedRealOneOneForm N Y) (u : Y → EReal), IsThetaPshPotential θ.val u →
    ∃ K A C C₁ : ℝ, 0 ≤ K ∧ 0 ≤ A ∧ 0 ≤ C ∧ 0 < C₁ ∧
      (∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → u x ≤ ((correctedSmoothing Ψ u K x t : ℝ) : EReal)) ∧
      (∀ (x : Y) (s : ℝ), s < Real.log r₀ →
        0 ≤ deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s)) s ∧
        0 < deriv (deriv (fun s => correctedSmoothing Ψ u K x (Real.exp s))) s) ∧
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < r₀ →
          JointLeviLowerBound θ wY (correctedSmoothing Ψ u K) e z w
            (A * logSlope (correctedSmoothing Ψ u K) (e.val.symm z) ‖w‖ + C * ‖w‖) C C) ∧
      (∀ (x : Y) (a : ℝ), u x = (a : EReal) → ∀ L : ℝ, 0 ≤ L → ∀ r : ℝ, 0 < r → C₁ * r < r₀ →
        (∀ t : ℝ, 0 < t → t ≤ C₁ * r → correctedSmoothing Ψ u K x t ≤ a + L * t) →
        ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → e.val.symm z = x →
          ∀ w : ℂ, ‖w‖ = r →
            JointLeviLowerBound θ wY (correctedSmoothing Ψ u K) e z w
              (A * logSlope (correctedSmoothing Ψ u K) x r + C * (1 + L) * r ^ 2)
              (C * (1 + L) * r) (C * (1 + L) * r))

variable [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **`IsJointSmoothing` for the smoothing `Ψ = smoothing wY A`**, given the generator and the
`psh` field at a radius `r₀` below a uniform radius. -/
theorem isJointSmoothing_smoothing {wY : KahlerBackground N Y} {A : FibreAtlas N Y}
    {r₁ r₀ : ℝ} (hr₁ : IsUniformRadius wY A r₁) (hr₀ : 0 < r₀) (hle : r₀ ≤ r₁)
    (hgen : ∃ a : ℝ, 0 < a ∧ ∀ g : Y → ℝ, Integrable g (kahlerVolume wY) →
      ∀ χ : Y → ℝ, ChartSmooth (n := N) χ →
        Tendsto (fun t => ∫ y, (smoothing wY A g y t - g y) / t ^ 2 * χ y ∂(kahlerVolume wY))
          (𝓝[>] 0) (𝓝 (a * ∫ y, g y * laplacian wY.form.val χ y ∂(kahlerVolume wY))))
    (hpsh : PshField wY r₀ (smoothing wY A)) :
    IsJointSmoothing wY r₀ (smoothing wY A) where
  r₀_pos := hr₀
  contDiffOn g hg e := (smoothing_contDiffOn hr₁ hg e).mono
    (prod_mono subset_rfl (Ioo_subset_Ioo_right hle))
  mono g g' hg hg' hle' x t ht htr := smoothing_mono hr₁ hg hg' hle' x ht (htr.trans_le hle)
  neg g x t := smoothing_neg A g x t
  add_const g hg c x t ht htr := smoothing_add_const hr₁ hg c x ht (htr.trans_le hle)
  generator := hgen
  psh := hpsh

universe v

/-- The global `psh` statement for the smoothing of lane DN5: below every uniform radius there is a
radius carrying the `psh` field (to be derived from `SGPT.NPP.DN5.LocalJointEstimate`). -/
def SmoothingPshStatement : Prop :=
  ∀ (N : ℕ) (Y : Type v) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (wY : KahlerBackground N Y) (A : FibreAtlas N Y) (r₁ : ℝ), IsUniformRadius wY A r₁ →
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ r₁ ∧ PshField wY r₀ (smoothing wY A)

/-- **FPT `lem:chern-joint-smoothing` in the form of `SGPT.NPP.DN2.JointSmoothingStatement`**,
from the generator and the `psh` field (lane DN4 + DN5).  The fibre map, the smoothing,
and the fields `contDiffOn`, `mono`, `neg`, `add_const` are constructed and proved here. -/
theorem jointSmoothingStatement_of (hgen : GeneratorEstimate.{v})
    (hpsh : SmoothingPshStatement.{v}) : JointSmoothingStatement.{v} := by
  intro N Y _ _ _ _ _ _ wY
  obtain ⟨A⟩ := exists_fibreAtlas (N := N) (Y := Y)
  obtain ⟨r₁, hr₁⟩ := exists_isUniformRadius wY A
  obtain ⟨r₀, hr₀, hle, hp⟩ := hpsh N Y wY A r₁ hr₁
  exact ⟨r₀, smoothing wY A, isJointSmoothing_smoothing hr₁ hr₀ hle (hgen N Y wY A) hp⟩

end SGPT.NPP.DN5
