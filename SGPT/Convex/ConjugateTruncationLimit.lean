import SGPT.Convex.FamilyOperations
import SGPT.Convex.GrowthClasses
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false

/-!
# Actual lower truncations and extended conjugate-gap convergence

The genuine pointwise infimum of finite lower truncations produces the actual
supremum of their conjugates. Monotone convergence applies to their extended
nonnegative gaps and retains positive infinity.
-/

noncomputable section

namespace SGPT.Convex

open Set Filter MeasureTheory
open scoped Topology ENNReal RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "B" => innerₗ E

/-- The literal finite lower truncation at the actual reference floor. -/
def realLowerTruncation (f g : E → ℝ) (j : ℕ) (x : E) : ℝ :=
  max (f x) (g x - j)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Actual lower floors decrease, so their genuine conjugates increase. -/
theorem conjugate_realLowerTruncation_mono (f g : E → ℝ) :
    Monotone (fun j : ℕ => conjugate B (fun x => (realLowerTruncation f g j x : EReal))) := by
  intro i j hij
  apply conjugate_antitone B
  intro x
  apply EReal.coe_le_coe_iff.mpr
  apply max_le_max le_rfl
  exact sub_le_sub_left (Nat.cast_le.mpr hij) _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The actual pointwise infimum, without a convergence certificate, gives the
whole original extended conjugate supremum, including every top value. -/
theorem conjugate_eq_iSup_realLowerTruncation (f g : E → ℝ) :
    conjugate B (fun x => (f x : EReal)) =
      fun m => ⨆ j : ℕ, conjugate B (fun x => (realLowerTruncation f g j x : EReal)) m := by
  have hinf : (fun x => (f x : EReal)) =
      (fun x => ⨅ j : ℕ, (realLowerTruncation f g j x : EReal)) := by
    funext x
    apply le_antisymm
    · apply le_iInf
      intro j
      exact EReal.coe_le_coe_iff.mpr (le_max_left _ _)
    · obtain ⟨j, hj⟩ := exists_nat_ge (g x - f x)
      apply iInf_le_of_le j
      change ((max (f x) (g x - j) : ℝ) : EReal) ≤ _
      rw [max_eq_left (by linarith)]
  rw [hinf, conjugate_iInf]
  rfl

private theorem continuous_sub_coe (r : ℝ) :
    Continuous (fun z : EReal => z - (r : EReal)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  simp only [sub_eq_add_neg, ← EReal.coe_neg]
  cases z using EReal.rec with
  | bot =>
    exact (EReal.continuousAt_add_bot_coe (-r)).comp
      (f := fun z : EReal => (z, ((-r : ℝ) : EReal)))
      (continuousAt_id.prodMk continuousAt_const)
  | coe a =>
    exact (EReal.continuousAt_add_coe_coe a (-r)).comp
      (f := fun z : EReal => (z, ((-r : ℝ) : EReal)))
      (continuousAt_id.prodMk continuousAt_const)
  | top =>
    exact (EReal.continuousAt_add_top_coe (-r)).comp
      (f := fun z : EReal => (z, ((-r : ℝ) : EReal)))
      (continuousAt_id.prodMk continuousAt_const)

/-- The actual extended nonnegative conjugate gaps satisfy monotone convergence
on the original body. No integrability or finiteness premise is inserted. -/
theorem lintegral_conjugate_gap_eq_iSup_realLowerTruncation
    (μ : Measure E) [μ.IsAddHaarMeasure] {P : Set E}
    (hP : IsCompact P) (hne : P.Nonempty) (hconv : Convex ℝ P)
    (f g : E → ℝ)
    (hg : (fun x => (g x : EReal)) ∈ BoundedGrowthClass B P) :
    (∫⁻ m in P, ((conjugate B (fun x => (f x : EReal)) m) -
      (conjugate B (fun x => (g x : EReal)) m)).toENNReal ∂μ) =
      ⨆ j : ℕ, ∫⁻ m in P,
        ((conjugate B (fun x => (realLowerTruncation f g j x : EReal)) m) -
          (conjugate B (fun x => (g x : EReal)) m)).toENNReal ∂μ := by
  let F : E → EReal := fun x => (f x : EReal)
  let G : E → EReal := fun x => (g x : EReal)
  let T : ℕ → E → EReal := fun j x => (realLowerTruncation f g j x : EReal)
  let q : ℕ → E → ℝ≥0∞ := fun j m =>
    (conjugate B (T j) m - conjugate B G m).toENNReal
  have hmono : Monotone (fun j => conjugate B (T j)) :=
    conjugate_realLowerTruncation_mono f g
  have hqm : ∀ j, Measurable (q j) := fun j =>
    EReal.continuous_toENNReal.measurable.comp
      ((measurable_conjugate B (T j)).sub (measurable_conjugate B G))
  have hqmono : Monotone q := by
    intro i j hij m
    apply EReal.toENNReal_le_toENNReal
    exact add_le_add (hmono hij m) le_rfl
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass B hP hconv hg
  have hgp := isProper_conjugate_of_isContPerfPair B
    (isProper_of_mem_boundedGrowthClass B hP hne hg)
  have hgap : ∀ m ∈ P,
      (conjugate B F m - conjugate B G m).toENNReal = ⨆ j : ℕ, q j m := by
    intro m hm
    have hgfinite : conjugate B G m = ((conjugate B G m).toReal : EReal) :=
      (EReal.coe_toReal
        (ne_top_of_le_ne_top (EReal.coe_ne_top b) (hab m hm).2) (hgp.2.2 m)).symm
    have hlim : Tendsto (fun j => conjugate B (T j) m) atTop
        (𝓝 (conjugate B F m)) := by
      rw [show conjugate B F m = ⨆ j : ℕ, conjugate B (T j) m from
        congrFun (conjugate_eq_iSup_realLowerTruncation f g) m]
      exact tendsto_atTop_iSup (fun i j hij => hmono hij m)
    have hcont : Continuous (fun z : EReal => (z - conjugate B G m).toENNReal) := by
      rw [hgfinite]
      exact EReal.continuous_toENNReal.comp (continuous_sub_coe _)
    have hq := hcont.continuousAt.tendsto.comp hlim
    exact tendsto_nhds_unique hq
      (tendsto_atTop_iSup (fun i j hij => hqmono hij m))
  change (∫⁻ m, (conjugate B F m - conjugate B G m).toENNReal ∂μ.restrict P) = _
  calc
    _ = ∫⁻ m, ⨆ j : ℕ, q j m ∂μ.restrict P := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hP.isClosed.measurableSet] with m hm
      exact hgap m hm
    _ = _ := lintegral_iSup hqm hqmono

end SGPT.Convex
