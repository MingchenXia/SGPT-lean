import SGPT.Foundations.Analysis.Pending.GermParametrizationSets
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetNull

set_option autoImplicit false

/-!
# The almost-everywhere sheet bound of an adapted projection

`Pending.GermParametrizationData.SetsData.ncard_fibre` counts the fibre of the adapted
projection `π : ℂⁿ → ℂᵈ` exactly: over a base point `x` of the base disc with `δ(x) ≠ 0`
the fibre of `A ∩ Δ` has `q = P.deg` points.  The generic-projection statement
(`Pending.GenericProjectionSheetBound`) consumes a *uniform bound valid for almost every*
base point instead, over the whole of `ℂᵈ` and with no hypothesis on `x`.

This module makes that passage.  The two points that have to be supplied are

* the discriminant locus is Lebesgue-null — `P.disc` is holomorphic on `ball 0 P.rad` and
  not identically zero there, so `Pending.HolomorphicZeroSetNull` applies once the base
  disc has been shrunk inside that ball (`baseRadius`);
* outside the base disc the fibre is *empty*, because the polydisc is contained in
  `{z | ‖π z‖ < r₁}`; so the bound holds there for the trivial reason.

The output `exists_fibreBound` is already in the shape of one clause of
`GenericProjectionSheetBound.exists_genericProjectionSheetBound`: an open neighbourhood of
the centre, a finite-volume measurable base set containing the image, and one integer
bounding the fibre cardinality almost everywhere.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ParametrizationFibreBound

open FirstPass FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.GermParametrizationData

variable {n : ℕ} {A : Set (ComplexModel n)}

/-- The radius of the base disc, shrunk inside the ball on which the discriminant is
holomorphic.  `SetsData` does not record `r₁ ≤ P.rad`, and nothing below needs it: the
fibre count of `SetsData.ncard_fibre` only improves on a smaller base disc. -/
def baseRadius (P : ParametrizationData A) (S : SetsData P) : ℝ := min S.r₁ P.rad

theorem baseRadius_pos (P : ParametrizationData A) (S : SetsData P) : 0 < baseRadius P S :=
  lt_min S.r₁_pos P.rad_pos

theorem baseRadius_le_r₁ (P : ParametrizationData A) (S : SetsData P) :
    baseRadius P S ≤ S.r₁ := min_le_left _ _

theorem baseRadius_le_rad (P : ParametrizationData A) (S : SetsData P) :
    baseRadius P S ≤ P.rad := min_le_right _ _

/-- The parametrizing polydisc over the shrunk base disc. -/
def basePolydisc (P : ParametrizationData A) (S : SetsData P) : Set (ComplexModel n) :=
  polydisc n P.dim (baseRadius P S) S.r₂

theorem isOpen_basePolydisc (P : ParametrizationData A) (S : SetsData P) :
    IsOpen (basePolydisc P S) := isOpen_polydisc _ _ _ _

theorem zero_mem_basePolydisc (P : ParametrizationData A) (S : SetsData P) :
    (0 : ComplexModel n) ∈ basePolydisc P S :=
  ⟨by simpa using baseRadius_pos P S, fun _ _ => by simpa using S.r₂_pos⟩

theorem basePolydisc_subset (P : ParametrizationData A) (S : SetsData P) :
    basePolydisc P S ⊆ polydisc n P.dim S.r₁ S.r₂ :=
  polydisc_mono (baseRadius_le_r₁ P S)

theorem norm_coordinateProjection_lt (P : ParametrizationData A) (S : SetsData P)
    {z : ComplexModel n} (hz : z ∈ basePolydisc P S) :
    ‖coordinateProjection n P.dim z‖ < baseRadius P S := hz.1

/-- The discriminant does not vanish identically on the ball on which it is holomorphic. -/
theorem exists_disc_ne_zero (P : ParametrizationData A) :
    ∃ x ∈ ball (0 : ComplexModel P.dim) P.rad, P.disc x ≠ 0 := by
  by_contra h
  push Not at h
  exact P.disc_not_eventually_zero
    (Filter.eventually_of_mem (ball_mem_nhds _ P.rad_pos) h)

/-- **The discriminant locus of the base disc is null.** -/
theorem measure_discriminant_eq_zero (P : ParametrizationData A) (S : SetsData P) :
    volume {x : ComplexModel P.dim | ‖x‖ < baseRadius P S ∧ P.disc x = 0} = 0 := by
  obtain ⟨x₁, hx₁, hne⟩ := exists_disc_ne_zero P
  refine measure_mono_null ?_
    (HolomorphicZeroSetNull.measure_ball_inter_preimage_zero_eq_zero volume
      P.differentiableOn_disc hx₁ hne)
  rintro x ⟨hx, hd⟩
  exact ⟨mem_ball_zero_iff.2 (hx.trans_le (baseRadius_le_rad P S)), hd⟩

/-- **The almost-everywhere sheet bound.**  Over almost every base point the fibre of
`A ∩ Δ` has at most `P.deg` points: over the base disc off the discriminant it has exactly
`P.deg`, and outside the base disc it is empty. -/
theorem ae_encard_fibre_le (P : ParametrizationData A) (S : SetsData P) :
    ∀ᵐ x : ComplexModel P.dim,
      (A ∩ basePolydisc P S ∩ coordinateProjection n P.dim ⁻¹' {x}).encard
        ≤ (P.deg : ℕ∞) := by
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_discriminant_eq_zero P S)
  intro x hx
  simp only [Set.mem_ofPred_eq, not_le] at hx
  -- A fibre with more than `P.deg` points is in particular nonempty, and any point of it
  -- witnesses `‖x‖ < baseRadius P S`: that is the whole content of the base disc clause.
  have hne : (A ∩ basePolydisc P S ∩ coordinateProjection n P.dim ⁻¹' {x}).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Set.encard_empty] at hx
    simp at hx
  obtain ⟨z, hz⟩ := hne
  have hnorm : ‖x‖ < baseRadius P S := by
    have hlt := norm_coordinateProjection_lt P S hz.1.2
    rwa [show coordinateProjection n P.dim z = x from hz.2] at hlt
  refine ⟨hnorm, ?_⟩
  -- Off the discriminant the fibre over the shrunk polydisc is contained in the fibre over
  -- the original one, which `SetsData.ncard_fibre` counts as exactly `P.deg`.
  by_contra hd
  have hlt : ‖x‖ < S.r₁ := hnorm.trans_le (baseRadius_le_r₁ P S)
  have hsub : A ∩ basePolydisc P S ∩ coordinateProjection n P.dim ⁻¹' {x} ⊆
      A ∩ polydisc n P.dim S.r₁ S.r₂ ∩ coordinateProjection n P.dim ⁻¹' {x} :=
    fun z hz => ⟨⟨hz.1.1, basePolydisc_subset P S hz.1.2⟩, hz.2⟩
  have hfin := S.finite_fibre x hlt hd
  have hcard := S.ncard_fibre x hlt hd
  refine absurd hx (not_lt.2 ?_)
  calc (A ∩ basePolydisc P S ∩ coordinateProjection n P.dim ⁻¹' {x}).encard
      ≤ (A ∩ polydisc n P.dim S.r₁ S.r₂ ∩
          coordinateProjection n P.dim ⁻¹' {x}).encard := Set.encard_mono hsub
    _ = ((A ∩ polydisc n P.dim S.r₁ S.r₂ ∩
          coordinateProjection n P.dim ⁻¹' {x}).ncard : ℕ∞) := hfin.cast_ncard_eq.symm
    _ = (P.deg : ℕ∞) := by rw [hcard]

/-- **The sheet bound in the shape the generic-projection statement consumes**: an open
neighbourhood of the centre, a measurable base set of finite volume containing the image of
`A` under the adapted projection, and one integer bounding the fibre cardinality almost
everywhere. -/
theorem exists_fibreBound (P : ParametrizationData A) (S : SetsData P) :
    ∃ (U : Set (ComplexModel n)) (Δ : Set (ComplexModel P.dim)) (N : ℕ),
      IsOpen U ∧ (0 : ComplexModel n) ∈ U ∧
        MeasurableSet Δ ∧ volume Δ ≠ ⊤ ∧
        (∀ z ∈ A ∩ U, coordinateProjection n P.dim z ∈ Δ) ∧
        ∀ᵐ x : ComplexModel P.dim,
          (A ∩ U ∩ coordinateProjection n P.dim ⁻¹' {x}).encard ≤ (N : ℕ∞) := by
  refine ⟨basePolydisc P S, ball 0 (baseRadius P S), P.deg, isOpen_basePolydisc P S,
    zero_mem_basePolydisc P S, measurableSet_ball, ?_, ?_, ae_encard_fibre_le P S⟩
  · exact (measure_ball_lt_top).ne
  · exact fun z hz => mem_ball_zero_iff.2 (norm_coordinateProjection_lt P S hz.2)

end SGPT.Foundations.Analysis.Pending.ParametrizationFibreBound
