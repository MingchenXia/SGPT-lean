import SGPT.Foundations.Analysis.FirstPass.RegularLocusDense

set_option autoImplicit false

/-!
# The projections cut out by a change of coordinates are dense in `Hom(ℂⁿ, ℂᵈ)`

A statement about the projection `coordinateProjection n d ∘ L⁻¹` transported by a linear
automorphism `L` of `ℂⁿ` — a Noether position, an adapted projection, a sheet bound — is
naturally produced near the STANDARD projection `coordinateProjection n d`, because that is
where an induction over the coordinates leaves it.  Its consumers prescribe an arbitrary
`B₀ : ℂⁿ → ℂᵈ` instead.  This module is the purely linear-algebraic bridge between the two:
for `d ≤ n`,

  `exists_continuousLinearEquiv_near`: every `B₀` is within `δ` of some
  `coordinateProjection n d ∘ K⁻¹`.

Conjugating a statement produced near `coordinateProjection n d` by such a `K` therefore
restates it near `B₀`.

## Why `B₀` may have rank `< d`

Every `coordinateProjection n d ∘ K⁻¹` is surjective, so `B₀` itself is realized exactly only
when it is.  This is why the conclusion approximates rather than matches: the surjections are
DENSE, which the proof exhibits in two explicit steps rather than by a rank argument.

* `exists_small_injective`.  With `ι = coordinateInclusion n d` and `π = coordinateProjection
  n d` (so `π ∘ ι = 1` for `d ≤ n`), `(B₀ + t·π) ∘ ι = B₀ ∘ ι + t`.  That fails to be
  injective only for `-t` in the spectrum of the endomorphism `B₀ ∘ ι` of `ℂᵈ`, a finite set
  (`Module.End.finite_spectrum`), so some `t` of arbitrarily small modulus works.
* `adaptedEndo B = ι ∘ B + (1 - ι ∘ π)` realizes such a `B` exactly: `π ∘ adaptedEndo B = B`,
  and `adaptedEndo B` is injective — hence, `ℂⁿ` being finite-dimensional, an automorphism —
  as soon as `B ∘ ι` is.  Indeed `adaptedEndo B z = 0` forces `B z = 0` after applying `π`,
  then `z = ι (π z)`, then `π z = 0`.

Degenerate cases.  `d = 0`: the target is the zero space, every map is `0` and `K = 1`
serves.  `d = n`: `ι` and `π` are mutually inverse, `adaptedEndo B = ι ∘ B`, and the
statement is that the automorphisms are dense in `End(ℂⁿ)`.  The hypothesis `d ≤ n` is
needed: `coordinateProjection n d` zero-pads, so for `d > n` no `coordinateProjection n d ∘
K⁻¹` comes near a `B₀` with a nonzero coordinate of index `≥ n`.
-/

open Metric Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.CoordinateProjectionDense

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.RegularLocusDense

noncomputable section

variable {n d : ℕ}

/-- The map `Φ = ι ∘ B + (1 - ι ∘ π)` of the construction below: it agrees with `B` after
`π`, and it is injective as soon as `B ∘ ι` is. -/
def adaptedEndo (B : ComplexModel n →L[ℂ] ComplexModel d) :
    ComplexModel n →L[ℂ] ComplexModel n :=
  (coordinateInclusion n d).comp B +
    (ContinuousLinearMap.id ℂ (ComplexModel n) -
      (coordinateInclusion n d).comp (coordinateProjection n d))

@[simp] theorem adaptedEndo_apply (B : ComplexModel n →L[ℂ] ComplexModel d)
    (z : ComplexModel n) :
    adaptedEndo B z =
      coordinateInclusion n d (B z) + (z - coordinateInclusion n d (coordinateProjection n d z)) :=
  rfl

theorem coordinateProjection_adaptedEndo (hdn : d ≤ n)
    (B : ComplexModel n →L[ℂ] ComplexModel d) (z : ComplexModel n) :
    coordinateProjection n d (adaptedEndo B z) = B z := by
  rw [adaptedEndo_apply, map_add, map_sub, coordinateProjection_coordinateInclusion hdn,
    coordinateProjection_coordinateInclusion hdn, sub_self, add_zero]

theorem injective_adaptedEndo (hdn : d ≤ n) {B : ComplexModel n →L[ℂ] ComplexModel d}
    (hB : Function.Injective fun w => B (coordinateInclusion n d w)) :
    Function.Injective (adaptedEndo B) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hBz : B z = 0 := by
    have := coordinateProjection_adaptedEndo hdn B z
    rw [hz, map_zero] at this
    exact this.symm
  have hzι : z = coordinateInclusion n d (coordinateProjection n d z) := by
    rw [adaptedEndo_apply, hBz, map_zero, zero_add, sub_eq_zero] at hz
    exact hz
  have : coordinateProjection n d z = 0 := by
    refine hB ?_
    show B (coordinateInclusion n d (coordinateProjection n d z)) = B (coordinateInclusion n d 0)
    rw [← hzι, hBz, map_zero, map_zero]
  rw [hzι, this, map_zero]

/-- **A small perturbation of `B` makes `B ∘ ι` injective.**  `(B + t·π) ∘ ι = B ∘ ι + t`,
and `-t` fails to be an eigenvalue of `B ∘ ι` for all but finitely many `t`. -/
theorem exists_small_injective (hdn : d ≤ n) (B : ComplexModel n →L[ℂ] ComplexModel d)
    {η : ℝ} (hη : 0 < η) :
    ∃ t : ℂ, ‖t‖ < η ∧
      Function.Injective fun w : ComplexModel d =>
        (B + t • coordinateProjection n d) (coordinateInclusion n d w) := by
  classical
  set T : Module.End ℂ (ComplexModel d) :=
    (B.comp (coordinateInclusion n d)).toLinearMap with hT
  have hfin : ((fun t : ℂ => -t) ⁻¹' spectrum ℂ T).Finite :=
    (Module.End.finite_spectrum T).preimage neg_injective.injOn
  obtain ⟨t, htc, htb⟩ :=
    (hfin.countable.dense_compl ℂ).exists_mem_open isOpen_ball ⟨0, mem_ball_self hη⟩
  have hspec : -t ∉ spectrum ℂ T := htc
  rw [spectrum.notMem_iff] at hspec
  have hneg : algebraMap ℂ (Module.End ℂ (ComplexModel d)) (-t) - T
      = -(T + t • (1 : Module.End ℂ (ComplexModel d))) := by
    rw [Algebra.algebraMap_eq_smul_one, neg_smul]
    abel
  rw [hneg, IsUnit.neg_iff] at hspec
  obtain ⟨v, hv⟩ := hspec.exists_left_inv
  have hleft : ∀ w, v ((T + t • (1 : Module.End ℂ (ComplexModel d))) w) = w := by
    intro w
    have h := congrArg (fun f : Module.End ℂ (ComplexModel d) => f w) hv
    simpa [Module.End.mul_apply] using h
  have key : ∀ w : ComplexModel d,
      (B + t • coordinateProjection n d) (coordinateInclusion n d w)
        = (T + t • (1 : Module.End ℂ (ComplexModel d))) w := by
    intro w
    simp [hT, coordinateProjection_coordinateInclusion hdn]
  refine ⟨t, by simpa [dist_eq_norm] using htb, fun w₁ w₂ h => ?_⟩
  have h' : (T + t • (1 : Module.End ℂ (ComplexModel d))) w₁
      = (T + t • (1 : Module.End ℂ (ComplexModel d))) w₂ := by
    rw [← key w₁, ← key w₂]; exact h
  rw [← hleft w₁, ← hleft w₂, h']

/-- **The transported projections are dense.**  For `d ≤ n` every continuous linear map
`B₀ : ℂⁿ → ℂᵈ` is approximated, as closely as we like, by `coordinateProjection n d ∘ K⁻¹`
for a linear automorphism `K` of `ℂⁿ`.

The rank of `B₀` is unconstrained: `coordinateProjection n d ∘ K⁻¹` is always surjective, and
a `B₀` of rank `< d` is not a counterexample because it is merely approximated.  This is the
step that lets a genericity statement produced near `coordinateProjection n d` be restated
near an arbitrary prescribed `B₀`. -/
theorem exists_continuousLinearEquiv_near (hdn : d ≤ n)
    (B₀ : ComplexModel n →L[ℂ] ComplexModel d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ComplexModel n ≃L[ℂ] ComplexModel n,
      ‖(coordinateProjection n d).comp (K.symm : ComplexModel n →L[ℂ] ComplexModel n) - B₀‖
        < δ := by
  have hpos : (0 : ℝ) < ‖coordinateProjection n d‖ + 1 := by positivity
  obtain ⟨t, ht, hinj⟩ := exists_small_injective hdn B₀ (div_pos hδ hpos)
  set B₁ := B₀ + t • coordinateProjection n d with hB₁
  have hΦinj : Function.Injective (adaptedEndo B₁) := injective_adaptedEndo hdn hinj
  have hker : LinearMap.ker (adaptedEndo B₁ : ComplexModel n →ₗ[ℂ] ComplexModel n) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hΦinj
  have hrange : LinearMap.range (adaptedEndo B₁ : ComplexModel n →ₗ[ℂ] ComplexModel n) = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hΦinj)
  refine ⟨(ContinuousLinearEquiv.ofBijective (adaptedEndo B₁) hker hrange).symm, ?_⟩
  have hcoe : (((ContinuousLinearEquiv.ofBijective (adaptedEndo B₁) hker hrange).symm.symm :
      ComplexModel n ≃L[ℂ] ComplexModel n) : ComplexModel n →L[ℂ] ComplexModel n)
      = adaptedEndo B₁ := by
    rw [ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.coe_ofBijective]
  rw [hcoe]
  have hcomp : (coordinateProjection n d).comp (adaptedEndo B₁) = B₁ := by
    ext z : 1
    exact coordinateProjection_adaptedEndo hdn B₁ z
  rw [hcomp, hB₁, add_sub_cancel_left, norm_smul]
  have ht' : ‖t‖ * (‖coordinateProjection n d‖ + 1) < δ := (lt_div_iff₀ hpos).mp ht
  nlinarith [norm_nonneg t, norm_nonneg (coordinateProjection n d)]

end

end SGPT.Foundations.Analysis.Pending.CoordinateProjectionDense
