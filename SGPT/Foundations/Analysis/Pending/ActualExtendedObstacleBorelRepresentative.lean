import SGPT.Foundations.Analysis.Pending.ActualExtendedObstacleQuasiContinuity
import SGPT.Foundations.Analysis.Pending.ActualQuasiContinuousBorelRepresentative
import SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity

set_option autoImplicit false

/-! # Actual Borel representatives of original extended-real obstacles

Independent measurable input for Xia, PDF 0080--0081. Countably many
finite clamps and true outer-capacity-zero representatives recover the
original obstacle off one measurable outer-capacity-zero set. No
measurability, lower bound, or finite-value assumption is made on it.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualExtendedObstacleBorelRepresentative

open FirstPass FirstPass.PositiveClasses ThetaCapacity CapacityWeightedConvergence
  ActualExtendedObstacleQuasiContinuity PluripolarCapacityZero PluripolarOuterCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The original nonpositive extended-real quasicontinuous obstacle has a
Borel, nonpositive, genuinely extended-real quasicontinuous representative
off one Borel set of actual outer Kähler capacity zero. -/
theorem exists_borel_representative (omega : KahlerBackground n M)
    {f : M → EReal} (hf0 : ∀ x, f x ≤ 0)
    (hf : QuasiContinuousERealFor (thetaCapacity omega.form (fun _ => 0)) f) :
    ∃ g : M → EReal, Measurable g ∧ (∀ x, g x ≤ 0) ∧
      QuasiContinuousERealFor (thetaCapacity omega.form (fun _ => 0)) g ∧
      ∃ E : Set M, MeasurableSet E ∧ OuterCapacityZero omega E ∧ EqOn f g Eᶜ := by
  classical
  let F : ℕ → M → ℝ := fun j x => (max (f x) (((-(j : ℝ)) : ℝ) : EReal)).toReal
  have hfinite : ∀ (j : ℕ) x, max (f x) (((-(j : ℝ)) : ℝ) : EReal) ≠ ⊥ ∧
      max (f x) (((-(j : ℝ)) : ℝ) : EReal) ≠ ⊤ := by
    intro j x
    have h0 : max (f x) (((-(j : ℝ)) : ℝ) : EReal) ≤ 0 :=
      max_le (hf0 x) (EReal.coe_nonpos.mpr (neg_nonpos.mpr (Nat.cast_nonneg j)))
    exact ⟨ne_of_gt ((EReal.bot_lt_coe (-(j : ℝ))).trans_le (le_max_right _ _)),
      ne_of_lt (h0.trans_lt (by norm_num : (0 : EReal) < ⊤))⟩
  have hFb : ∀ (j : ℕ) x, -(j : ℝ) ≤ F j x ∧ F j x ≤ 0 := by
    intro j x
    obtain ⟨hbot, htop⟩ := hfinite j x
    constructor
    · simpa only [F, EReal.toReal_coe] using
        EReal.toReal_le_toReal (le_max_right (f x) (((-(j : ℝ)) : ℝ) : EReal))
          (EReal.coe_ne_bot (-(j : ℝ))) htop
    · simpa only [F, EReal.toReal_zero] using
        EReal.toReal_le_toReal
          (max_le (hf0 x) (EReal.coe_nonpos.mpr (neg_nonpos.mpr (Nat.cast_nonneg j))))
          hbot (by norm_num : (0 : EReal) ≠ ⊤)
  have hFqc : ∀ j, QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) (F j) := by
    intro j
    simpa only [F, EReal.coe_zero, min_eq_left (hf0 _)] using
      quasiContinuousFor_clamp (neg_nonpos.mpr (Nat.cast_nonneg j)) hf
  choose g hgm _hgB _hgQC E hEm hEcap heq using fun j : ℕ =>
    ActualQuasiContinuousBorelRepresentative.exists_borel_representative omega
      (by positivity : 0 ≤ (j : ℝ))
      (fun x => abs_le.mpr ⟨(hFb j x).1, (hFb j x).2.trans (by positivity)⟩) (hFqc j)
  let Z : Set M := ⋃ j : ℕ, E j
  let f' : M → EReal := fun x => ⨅ j : ℕ, ((min (g j x) 0 : ℝ) : EReal)
  have hZm : MeasurableSet Z := MeasurableSet.iUnion hEm
  have hZc : OuterCapacityZero omega Z := OuterCapacityZero.iUnion hEcap
  have hfm : Measurable f' := Measurable.iInf fun j =>
    continuous_coe_real_ereal.measurable.comp ((hgm j).min measurable_const)
  have hfn : ∀ x, f' x ≤ 0 := fun x => iInf_le_of_le 0
    (EReal.coe_nonpos.mpr (min_le_right _ _))
  have hff : EqOn f f' Zᶜ := by
    intro x hx
    have hj : ∀ j, x ∈ (E j)ᶜ := fun j hxj => hx (mem_iUnion.mpr ⟨j, hxj⟩)
    have he : ∀ j, ((min (g j x) 0 : ℝ) : EReal) =
        max (f x) (((-(j : ℝ)) : ℝ) : EReal) := by
      intro j
      rw [← heq j (hj j), min_eq_left (hFb j x).2]
      exact EReal.coe_toReal (hfinite j x).2 (hfinite j x).1
    change f x = ⨅ j : ℕ, ((min (g j x) 0 : ℝ) : EReal)
    simp_rw [he]
    exact (RooftopUscDecreasingLimit.iInf_max_neg_natCast (f x)).symm
  have hfqc : QuasiContinuousERealFor (thetaCapacity omega.form (fun _ => 0)) f' := by
    intro η hη
    have hhalf : 0 < η / 2 := ENNReal.div_pos_iff.mpr ⟨hη.ne', by norm_num⟩
    obtain ⟨G, hGo, hGc, hcont⟩ := hf (η / 2) hhalf
    obtain ⟨O, hOo, hZO, hOc⟩ := hZc (η / 2) hhalf
    refine ⟨G ∪ O, hGo.union hOo, ?_, ?_⟩
    · calc thetaCapacity omega.form (fun _ => 0) (G ∪ O)
          ≤ thetaCapacity omega.form (fun _ => 0) G + thetaCapacity omega.form (fun _ => 0) O :=
            thetaCapacity_union_le _ _ _ _
        _ < η / 2 + η / 2 := ENNReal.add_lt_add hGc hOc
        _ = η := ENNReal.add_halves η
    · apply hcont.congr_mono
      · intro x hx
        exact (hff (fun hxZ => hx (Or.inr (hZO hxZ)))).symm
      · intro x hx hxG
        exact hx (Or.inl hxG)
  exact ⟨f', hfm, hfn, hfqc, Z, hZm, hZc, hff⟩

end
end SGPT.Foundations.Analysis.Pending.ActualExtendedObstacleBorelRepresentative
