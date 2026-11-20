import SGPT.Foundations.Analysis.Pending.ClosedCurrentMassLimitReduction

set_option autoImplicit false

/-!
# Singular-collar error reduction for regular-piece masses

The form-current proof of Stokes has a final analytic step near the singular
locus. After cancellation on the regular part, the two finite regular-piece
masses differ by a real collar error. This module records the exact purely
numerical consequence of that step.

For a fixed exhaustion `H`, a `FormPieceMassCollarError` consists of finiteness
of every left-hand finite-piece mass, a real sequence of collar errors tending
to zero, and an absolute-value bound for the difference of the two masses after
conversion to real numbers. From this data and a finite limit for the right-hand
masses, `commonLimit_of_collarError` constructs the common `ENNReal` limit
expected by `ClosedCurrentMassLimitReduction`. The final theorem combines it
with the proved compact-absorbing exhaustion machinery to identify the two
global regular-piece suprema.

No analytic collar estimate is asserted here. In the intended closed-current
application, the remaining source input has to provide precisely the finite
mass bound and the displayed real error estimate, obtained from cutoffs near
`V_sing`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCollarMassErrorReduction

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open ClosedCurrentMassLimitReduction
open RegularPieceExhaustion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- A real sequence converges to `L` when it is pointwise within an error
sequence tending to zero of another sequence converging to `L`. -/
theorem tendsto_of_abs_sub_le_of_tendsto {x y e : ℕ → ℝ} {L : ℝ}
    (hy : Tendsto y atTop (𝓝 L)) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ m, |x m - y m| ≤ e m) :
    Tendsto x atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hy (eps / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.1 he (eps / 2) (by linarith)
  refine ⟨max N1 N2, fun m hm => ?_⟩
  have hm1 : N1 ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : N2 ≤ m := le_trans (le_max_right _ _) hm
  have hy' : |y m - L| < eps / 2 := by
    simpa only [Real.dist_eq] using hN1 m hm1
  have he' : |e m - 0| < eps / 2 := by
    simpa only [Real.dist_eq] using hN2 m hm2
  have hxy : |x m - y m| ≤ e m := hbound m
  have hnonneg : 0 ≤ e m := le_trans (abs_nonneg _) hxy
  rw [Real.dist_eq]
  calc
    |x m - L| ≤ |x m - y m| + |y m - L| := abs_sub_le _ _ _
    _ ≤ e m + |y m - L| := add_le_add hxy le_rfl
    _ < eps / 2 + eps / 2 :=
      add_lt_add (by simpa [abs_of_nonneg hnonneg] using he') hy'
    _ = eps := by ring

/-- The residual numerical content of the singular-collar step along a fixed
regular-piece exhaustion. The bound is deliberately stated after `toReal`:
the collar calculation is a signed real integral. -/
structure FormPieceMassCollarError (a b : SmoothRealForm n M 2)
    (H : ℕ → RegularPieceFamily V (∅ : Set M)) where
  /-- The left masses are finite, so conversion through `toReal` loses no
  information. -/
  left_ne_top : ∀ m, PatchFormMass.formPieceMass a (H m) ≠ ⊤
  /-- The remaining singular-collar error, measured in signed real mass. -/
  error : ℕ → ℝ
  /-- The collar error vanishes along the exhaustion. -/
  tendsto_error : Tendsto error atTop (𝓝 0)
  /-- After regular-locus Stokes cancellation, the two finite-piece masses are
  controlled by the collar error. -/
  abs_toReal_sub_le : ∀ m,
    |(PatchFormMass.formPieceMass a (H m)).toReal -
        (PatchFormMass.formPieceMass b (H m)).toReal| ≤ error m

namespace FormPieceMassCollarError

/-- A finite right-hand limit plus a vanishing collar error gives a common
`ENNReal` limit of the two mass sequences. -/
noncomputable def commonLimit_of_collarError
    {a b : SmoothRealForm n M 2} {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    (D : FormPieceMassCollarError a b H) {L : ℝ≥0∞}
    (hlimit : Tendsto (fun m : ℕ => PatchFormMass.formPieceMass b (H m)) atTop (𝓝 L))
    (hLfinite : L ≠ ⊤) :
    FormPieceMassCommonLimit a b H := by
  have hBreal : Tendsto (fun m : ℕ => (PatchFormMass.formPieceMass b (H m)).toReal)
      atTop (𝓝 L.toReal) :=
    (ENNReal.tendsto_toReal hLfinite).comp hlimit
  have hAreal : Tendsto (fun m : ℕ => (PatchFormMass.formPieceMass a (H m)).toReal)
      atTop (𝓝 L.toReal) :=
    tendsto_of_abs_sub_le_of_tendsto hBreal D.tendsto_error D.abs_toReal_sub_le
  have hofreal : Tendsto (fun m : ℕ =>
      ENNReal.ofReal (PatchFormMass.formPieceMass a (H m)).toReal) atTop
      (𝓝 (ENNReal.ofReal L.toReal)) :=
    ENNReal.tendsto_ofReal hAreal
  have hleft : (fun m : ℕ =>
      ENNReal.ofReal (PatchFormMass.formPieceMass a (H m)).toReal) =
      fun m : ℕ => PatchFormMass.formPieceMass a (H m) := by
    funext m
    exact ENNReal.ofReal_toReal (D.left_ne_top m)
  rw [hleft, ENNReal.ofReal_toReal hLfinite] at hofreal
  exact ⟨L, hofreal, hlimit⟩

end FormPieceMassCollarError

/-- A vanishing singular-collar error on a monotone compact-absorbing
exhaustion identifies the two global regular-piece masses. This is the largest
consequence of collar convergence alone: the hypotheses retain the finite-mass
and signed-error facts that must be supplied by the analytic current argument. -/
theorem iSup_formPieceMass_eq_of_collarError
    (a b : SmoothRealForm n M 2) {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    (hmono : ∀ m, coveredRegion (H m) ⊆ coveredRegion (H (m + 1)))
    (hexh : ∀ K : Set M, IsCompact K →
      K ⊆ regularLocus (n := n) V.carrier V.dim → ∃ m, K ⊆ coveredRegion (H m))
    (hbright : (⨆ F : RegularPieceFamily V (∅ : Set M),
      PatchFormMass.formPieceMass b F) ≠ ⊤)
    (D : FormPieceMassCollarError a b H) :
    (⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass a F) =
      ⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass b F := by
  apply iSup_formPieceMass_eq_of_commonLimit a b hmono hexh
  exact D.commonLimit_of_collarError
    (tendsto_formPieceMass_of_exhaustion (V := V) isClosed_empty hmono
      (fun K hK hKreg _ => hexh K hK hKreg) b)
    hbright

end

end SGPT.Foundations.Analysis.Pending.SingularCollarMassErrorReduction
