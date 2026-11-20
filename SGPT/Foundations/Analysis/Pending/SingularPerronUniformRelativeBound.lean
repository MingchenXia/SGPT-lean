import SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalTruncationEnergy
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicSingularBarriers

set_option autoImplicit false

/-! # Genuine uniform relative bounds for singular Perron curves -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularPerronUniformRelativeBound

open FirstPass FirstPass.PositiveClasses FiniteGeodesicSingularBarriers
  SingularModelEnergyTruncation SingularPerronCanonicalTruncationEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine endpoint bounds give the same two extended bounds on the actual Perron curve at all interior times, including common poles. -/
theorem finiteGeodesic_extended_bounds {θ : SmoothRealForm n M 2}
    {φ u₀ u₁ : M → EReal} (hφ : IsThetaPshPotential θ φ)
    (hu₀ : IsThetaPshPotential θ u₀) (hu₁ : IsThetaPshPotential θ u₁) {C : ℝ}
    (hl₀ : ∀ x, φ x + ((-C : ℝ) : EReal) ≤ u₀ x)
    (hl₁ : ∀ x, φ x + ((-C : ℝ) : EReal) ≤ u₁ x)
    (hh₀ : ∀ x, u₀ x ≤ φ x + (C : EReal))
    (hh₁ : ∀ x, u₁ x ≤ φ x + (C : EReal))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    φ x + ((-C : ℝ) : EReal) ≤ finiteGeodesic θ u₀ u₁ t x ∧
      finiteGeodesic θ u₀ u₁ t x ≤ φ x + (C : EReal) := by
  refine ⟨le_finiteGeodesic_of_le_endpoints (hφ.add_const (-C)) hl₀ hl₁ t x, ?_⟩
  refine (finiteGeodesic_le_eRealChord hu₀ hu₁ ht x).trans
    ((eRealChord_mono (hh₀ x) (hh₁ x) ht.1.le ht.2.le).trans_eq ?_)
  induction hpx : φ x using EReal.rec with
  | bot =>
      simp only [eRealChord, EReal.bot_add]
      rw [EReal.coe_mul_bot_of_pos (sub_pos.mpr ht.2),
        EReal.coe_mul_bot_of_pos ht.1, EReal.bot_add]
  | coe r =>
      simp only [eRealChord, ← EReal.coe_add, ← EReal.coe_mul]
      norm_cast
      ring
  | top => exact False.elim (hφ.quasiPshPotential.1.ne_top x hpx)

/-- Actual finite-type endpoint comparisons produce one nonnegative extended Perron bound for all interior times and points. -/
theorem exists_uniform_extended_bounds_of_relativeEInfinity
    {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hu₀ : RelativeEInfinity θ φ u₀) (hu₁ : RelativeEInfinity θ φ u₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      φ x + ((-C : ℝ) : EReal) ≤ finiteGeodesic θ.val u₀ u₁ t x ∧
        finiteGeodesic θ.val u₀ u₁ t x ≤ φ x + (C : EReal) := by
  obtain ⟨C₀, hC₀, hl₀, hh₀⟩ :=
    exists_nonneg_le_add_of_sameSingularityType hu₀.sameSingularityType
  obtain ⟨C₁, hC₁, hl₁, hh₁⟩ :=
    exists_nonneg_le_add_of_sameSingularityType hu₁.sameSingularityType
  let C : ℝ := max C₀ C₁
  have hC₀C : (C₀ : EReal) ≤ (C : EReal) :=
    EReal.coe_le_coe_iff.mpr (le_max_left _ _)
  have hC₁C : (C₁ : EReal) ≤ (C : EReal) :=
    EReal.coe_le_coe_iff.mpr (le_max_right _ _)
  have lower₀ (x : M) : φ x + ((-C : ℝ) : EReal) ≤ u₀ x := by
    apply (EReal.addLECancellable_coe C).add_le_add_iff_right.mp
    calc
      (φ x + ((-C : ℝ) : EReal)) + (C : EReal) = φ x := by
        rw [add_assoc, ← EReal.coe_add]
        simp
      _ ≤ u₀ x + (C₀ : EReal) := hl₀ x
      _ ≤ u₀ x + (C : EReal) := add_le_add le_rfl hC₀C
  have lower₁ (x : M) : φ x + ((-C : ℝ) : EReal) ≤ u₁ x := by
    apply (EReal.addLECancellable_coe C).add_le_add_iff_right.mp
    calc
      (φ x + ((-C : ℝ) : EReal)) + (C : EReal) = φ x := by
        rw [add_assoc, ← EReal.coe_add]
        simp
      _ ≤ u₁ x + (C₁ : EReal) := hl₁ x
      _ ≤ u₁ x + (C : EReal) := add_le_add le_rfl hC₁C
  refine ⟨C, hC₀.trans (le_max_left _ _), fun t ht x => ?_⟩
  exact finiteGeodesic_extended_bounds hφ hu₀.1 hu₁.1 lower₀ lower₁
    (fun y => (hh₀ y).trans (add_le_add le_rfl hC₀C))
    (fun y => (hh₁ y).trans (add_le_add le_rfl hC₁C)) ht x

/-- Two genuine finite extended bounds control the canonical real gap, with zero at common poles. -/
theorem canonicalDiff_le_of_extended_bounds {a b : EReal} {C : ℝ}
    (hb : b ≠ ⊤) (hC : 0 ≤ C)
    (hl : b + ((-C : ℝ) : EReal) ≤ a) (hh : a ≤ b + (C : EReal)) :
    |canonicalERealDiffToReal a b| ≤ C := by
  by_cases hbot : b = ⊥
  · have ha : a = ⊥ := by
      simpa only [hbot, EReal.bot_add, le_bot_iff] using hh
    simpa [ha, hbot, canonicalERealDiffToReal, poleModifiedERealDiffToReal] using hC
  · have he := (EReal.coe_toReal hb hbot).symm
    rw [he, ← EReal.coe_add] at hl hh
    obtain ⟨ha, hlow, hhigh⟩ := FiniteGeodesicEnergyEndpoints.eq_coe_toReal_of_coe_le_le hl hh
    rw [ha, he, canonicalERealDiffToReal_coe_coe]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- One genuine canonical real bound controls all times of the actual finite-type Perron curve. -/
theorem exists_uniform_canonicalDiff_bound_of_relativeEInfinity
    {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hu₀ : RelativeEInfinity θ φ u₀) (hu₁ : RelativeEInfinity θ φ u₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      |canonicalERealDiffToReal (finiteGeodesic θ.val u₀ u₁ t x) (φ x)| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_extended_bounds_of_relativeEInfinity hφ hu₀ hu₁
  exact ⟨C, hC, fun t ht x => canonicalDiff_le_of_extended_bounds
    (hφ.quasiPshPotential.1.ne_top x) hC (hbound t ht x).1 (hbound t ht x).2⟩

/-- Actual endpoint truncations internally produce a single relative bound on every interior time of their actual Perron curve. -/
theorem exists_uniform_extended_bounds_truncatedGeodesic
    {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hu₀ : RelativePreceqClasses.RelativePSHPreceq θ φ u₀)
    (hu₁ : RelativePreceqClasses.RelativePSHPreceq θ φ u₁) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      φ x + ((-C : ℝ) : EReal) ≤ truncatedGeodesic θ.val φ u₀ u₁ j t x ∧
        truncatedGeodesic θ.val φ u₀ u₁ j t x ≤ φ x + (C : EReal) :=
  exists_uniform_extended_bounds_of_relativeEInfinity hφ
    (relativeEInfinity_truncation hφ hu₀.1 hu₀.2 j)
    (relativeEInfinity_truncation hφ hu₁.1 hu₁.2 j)

/-- Each genuine canonical stage has one actual canonical real bound uniform over the full interior time interval and space, including poles. -/
theorem exists_uniform_relative_bound_truncatedGeodesic
    {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hu₀ : RelativePreceqClasses.RelativePSHPreceq θ φ u₀)
    (hu₁ : RelativePreceqClasses.RelativePSHPreceq θ φ u₁) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      (φ x + ((-C : ℝ) : EReal) ≤ truncatedGeodesic θ.val φ u₀ u₁ j t x ∧
        truncatedGeodesic θ.val φ u₀ u₁ j t x ≤ φ x + (C : EReal)) ∧
      |canonicalERealDiffToReal (truncatedGeodesic θ.val φ u₀ u₁ j t x) (φ x)| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_extended_bounds_truncatedGeodesic hφ hu₀ hu₁ j
  refine ⟨C, hC, fun t ht x => ⟨hbound t ht x, ?_⟩⟩
  exact canonicalDiff_le_of_extended_bounds (hφ.quasiPshPotential.1.ne_top x)
    hC (hbound t ht x).1 (hbound t ht x).2

end

end SGPT.Foundations.Analysis.Pending.SingularPerronUniformRelativeBound
