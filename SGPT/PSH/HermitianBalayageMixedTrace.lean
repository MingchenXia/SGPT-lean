import SGPT.PSH.HermitianBalayageBallTrace
import SGPT.PSH.HermitianProductsFlat
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import Mathlib.GroupTheory.Perm.Fin

/-!
# The nearby-trace recurrence in an arbitrary actual mixed-product slot

The scalar trace estimate is read on the canonical bounded mixed
Bedford--Taylor measures. The remaining current is constructed from the
other slots; no current representation or mass comparison is supplied.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCollar
  LocalBedfordTaylorSmoothTraceMeasure LocalBedfordTaylorCanonicalTraceMeasure
  LocalBedfordTaylorCalculus LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open scoped Topology Distributions

variable {n : ℕ} {Ω : Opens (ComplexModel (n + 1))}

/-- The normalized Euclidean slot is a genuine locally bounded PSH function. -/
theorem locallyBoundedPsh_flatQuadratic {N : ℕ} (D : Opens (ComplexModel N)) :
    IsLocallyBoundedPshOn D (HermitianProducts.flatQuadratic (n := N)) := by
  apply isLocallyBoundedPshOn_of_continuousOn
  · simpa only [HermitianProducts.flatQuadratic, EReal.coe_mul] using
      (isSmoothPshOn_norm_sq D).2.1.const_mul Real.pi_pos
  · exact HermitianProducts.contDiff_flatQuadratic.continuous.continuousOn

/-- Inserting the normalized Euclidean quadratic converts the remaining
current's trace into the exact full Monge--Ampère trace measure. -/
theorem traceMeasure_ddcMul_flatQuadratic {N : ℕ} {D : Opens (ComplexModel N)}
    {R : LocalProductCurrent N D 1} (hR : IsPositive R) (hRc : IsClosedCurrent R) :
    (isPositive_ddcMul hR hRc (locallyBoundedPsh_flatQuadratic D)).1.traceMeasure =
      hR.traceMeasure := by
  let hS := (isPositive_ddcMul hR hRc (locallyBoundedPsh_flatQuadratic D)).1
  exact eq_of_forall_testFunction_integral_eq hS.traceMeasure_compl hR.traceMeasure_compl
    (fun _ hK hKD => hS.traceMeasure_lt_top hK hKD)
    (fun _ hK hKD => hR.traceMeasure_lt_top hK hKD)
    (fun χ => by
      rw [hS.integral_traceMeasure, hR.integral_traceMeasure]
      exact HermitianProducts.ddcMul_flatQuadratic_trace hR hRc χ)

/-- Inserting an actual bounded PSH slot produces the full mixed PSH tuple. -/
theorem locallyBoundedPsh_insertNth
    {f : Fin n → ComplexModel (n + 1) → ℝ}
    (hf : ∀ i, IsLocallyBoundedPshOn Ω (f i)) (j : Fin (n + 1))
    {u : ComplexModel (n + 1) → ℝ} (hu : IsLocallyBoundedPshOn Ω u) :
    ∀ i : Fin (n + 1),
      IsLocallyBoundedPshOn Ω ((j.insertNth u f : Fin (n + 1) → ComplexModel (n + 1) → ℝ) i) := by
  intro i
  refine Fin.succAboveCases j ?_ (fun k => ?_) i
  · simpa only [Fin.insertNth_apply_same] using hu
  · simpa only [Fin.insertNth_apply_succAbove] using hf k

private theorem oneCurrentOf_heq {N a b : ℕ} {D : Opens (ComplexModel N)}
    (ha : a = N) (hb : b = N) :
    HEq (oneCurrentOf (U := D) ha) (oneCurrentOf (U := D) hb) := by
  subst ha
  subst hb
  rfl

private theorem traceMeasure_eq_of_current_eq {N k : ℕ} {D : Opens (ComplexModel N)}
    {A B : LocalProductCurrent N D k} (hA : IsPositive A) (hB : IsPositive B)
    (h : A = B) : hA.traceMeasure = hB.traceMeasure := by
  subst h
  rfl

/-- The residual current of the actual other mixed-product slots. -/
def remainingMixedCurrent (Ω : Opens (ComplexModel (n + 1)))
    (f : Fin n → ComplexModel (n + 1) → ℝ) : LocalProductCurrent (n + 1) Ω 1 :=
  btProduct n 1 f (oneCurrentOf (by omega : 1 + n = n + 1))

theorem remainingMixedCurrent_positive_closed
    {f : Fin n → ComplexModel (n + 1) → ℝ}
    (hf : ∀ i, IsLocallyBoundedPshOn Ω (f i)) :
    IsPositive (remainingMixedCurrent Ω f) ∧ IsClosedCurrent (remainingMixedCurrent Ω f) :=
  isPositive_btProduct n 1 f _ (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hf

/-- The canonical full mixed measure is exactly the trace of the
differentiated residual current, at any slot position. -/
theorem canonicalMixedMeasure_insertNth_eq_trace
    {f : Fin n → ComplexModel (n + 1) → ℝ}
    (hf : ∀ i, IsLocallyBoundedPshOn Ω (f i)) (j : Fin (n + 1))
    {u : ComplexModel (n + 1) → ℝ} (hu : IsLocallyBoundedPshOn Ω u) :
    canonicalMixedBedfordTaylorMeasure Ω (j.insertNth u f) (locallyBoundedPsh_insertNth hf j hu) =
      (isPositive_ddcMul (remainingMixedCurrent_positive_closed hf).1
        (remainingMixedCurrent_positive_closed hf).2 hu).1.traceMeasure := by
  let hfull := locallyBoundedPsh_insertNth hf j hu
  have hperm := canonicalMixedBedfordTaylorMeasure_perm hfull j.cycleRange.symm
    (fun i => hfull (j.cycleRange.symm i))
  have hc : ∀ i : Fin (n + 1),
      IsLocallyBoundedPshOn Ω ((Fin.cons u f : Fin (n + 1) → ComplexModel (n + 1) → ℝ) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using hu
    · simpa using hf k
  have hceq : canonicalMixedBedfordTaylorMeasure Ω (j.insertNth u f) hfull =
      canonicalMixedBedfordTaylorMeasure Ω (Fin.cons u f) hc := by
    change canonicalMixedBedfordTaylorMeasure Ω ((j.insertNth u f) ∘ j.cycleRange.symm) _ =
      canonicalMixedBedfordTaylorMeasure Ω (j.insertNth u f) hfull at hperm
    simpa only [Fin.insertNth_comp_cycleRange_symm] using hperm.symm
  rw [hceq, canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure hc]
  let T := oneCurrentOf (U := Ω) (Nat.zero_add (n + 1))
  have heq : btProduct (n + 1) 0 (Fin.cons u f) T =
      ddcMul (remainingMixedCurrent Ω f) u := by
    rw [btProduct_succ_eq_ddcMul n 0 (Fin.cons u f) T
      (oneCurrentOf (by omega : 0 + 1 + n = n + 1)) (oneCurrentOf_heq _ _)]
    rfl
  exact traceMeasure_eq_of_current_eq
    (isPositive_btProduct (n + 1) 0 (Fin.cons u f) T
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hc).1
    (isPositive_ddcMul (remainingMixedCurrent_positive_closed hf).1
      (remainingMixedCurrent_positive_closed hf).2 hu).1 heq

/-- The residual trace is literally a canonical mixed measure with one
normalized flat slot, in any position chosen by the caller. -/
theorem canonicalMixedMeasure_insertNth_flat_eq_trace
    {f : Fin n → ComplexModel (n + 1) → ℝ}
    (hf : ∀ i, IsLocallyBoundedPshOn Ω (f i)) (j : Fin (n + 1)) :
    canonicalMixedBedfordTaylorMeasure Ω (j.insertNth HermitianProducts.flatQuadratic f)
        (locallyBoundedPsh_insertNth hf j (locallyBoundedPsh_flatQuadratic Ω)) =
      (remainingMixedCurrent_positive_closed hf).1.traceMeasure := by
  rw [canonicalMixedMeasure_insertNth_eq_trace hf j (locallyBoundedPsh_flatQuadratic Ω),
    traceMeasure_ddcMul_flatQuadratic (remainingMixedCurrent_positive_closed hf).1
      (remainingMixedCurrent_positive_closed hf).2]

/-- Nearby bounded potentials give the genuine canonical mixed-measure
recurrence in any independently chosen slot. -/
theorem exists_one_slot_canonicalMixed_ball_mass_le {t₀ t₁ : ℝ}
    (ht₀ : 0 < t₀) (htt : t₀ < t₁) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Opens (ComplexModel (n + 1))) (a : ComplexModel (n + 1)) (r κ : ℝ),
        0 < r → 0 ≤ κ → closedBall a (t₁ * r) ⊆ Ω →
        ∀ (f : Fin n → ComplexModel (n + 1) → ℝ)
          (hf : ∀ i, IsLocallyBoundedPshOn Ω (f i)) (j : Fin (n + 1))
          (u v : ComplexModel (n + 1) → ℝ),
          Measurable u → Measurable v →
          ∀ (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v),
            (∀ x ∈ closedBall a (t₁ * r), |v x - u x| ≤ κ * r ^ 2) →
            (canonicalMixedBedfordTaylorMeasure Ω (j.insertNth v f)
                (locallyBoundedPsh_insertNth hf j hv) (closedBall a (t₀ * r))).toReal ≤
              (canonicalMixedBedfordTaylorMeasure Ω (j.insertNth u f)
                  (locallyBoundedPsh_insertNth hf j hu) (closedBall a (t₁ * r))).toReal +
                C * κ * ((remainingMixedCurrent_positive_closed hf).1.traceMeasure
                  (closedBall a (t₁ * r))).toReal := by
  obtain ⟨C, hC0, hC⟩ := exists_one_slot_ball_trace_mass_le (n := n + 1) 0 ht₀ htt
  refine ⟨C, hC0, ?_⟩
  intro Ω a r κ hr hκ hball f hf j u v hum hvm hu hv hclose
  rw [canonicalMixedMeasure_insertNth_eq_trace hf j hv,
    canonicalMixedMeasure_insertNth_eq_trace hf j hu]
  exact hC Ω a r κ hr hκ hball (remainingMixedCurrent Ω f)
    (remainingMixedCurrent_positive_closed hf).1 (remainingMixedCurrent_positive_closed hf).2
    u v hum hvm hu hv hclose

end SGPT.PSH.HermitianBalayage
