import SGPT.PSH.HermitianProductsIncreasing
import SGPT.PSH.HermitianProductPatches
import SGPT.PSH.HermitianEnvelopeStability
import SGPT.Foundations.Analysis.Pending.IncreasingPshBallSubmean

/-!
# Actual bounded increasing Hermitian potentials and their product limits

The regularized supremum is the literal USC regularization. Common local
PSH corrections and the sharp ball-submean theorem recover its original
pointwise supremum almost everywhere in every native chart. Real bounds
exclude poles, so the corrected real readers converge almost everywhere.
These internally produced inputs feed actual nonclosed product continuity.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere LocalBedfordTaylorContinuity
open Hermitian HermitianProducts
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Original nonclosed Hermitian potentials recover their actual
regularized supremum almost everywhere in every genuine native chart.
The common corrections are manufactured from the actual background. -/
theorem ae_chartFunction_iSup_eq_of_monotone
    (omega : Background (m + 1) M) {g : ℕ → M → EReal} {u : M → EReal}
    (hg : ∀ j, IsHermitianPSH omega (g j)) (C : ℝ)
    (hupper : ∀ j x, g j x ≤ (C : EReal)) (hmono : Monotone g)
    (heq : uscRegularization (fun x => ⨆ j, g j x) = u)
    (e : ComplexChart (m + 1) M) :
    ∀ᵐ z ∂volume.restrict e.val.target, (⨆ j, chartFunction (g j) e z) = chartFunction u e z := by
  refine ae_restrict_of_open_neighborhood_ae ?_
  intro z hz
  obtain ⟨W, q, hzW, hW, hWe, hq, hpsh⟩ := hasCommonLocalCorrections omega e z hz
  let v : ℕ → ComplexModel (m + 1) → EReal := fun j y => chartFunction (g j) e y + (q y : EReal)
  have hqc (y : ComplexModel (m + 1)) (hy : y ∈ W) : ContinuousAt q y :=
    (hq.continuousOn.continuousAt (hW.mem_nhds hy))
  have hsup : (⨆ j, v j) = fun y => chartFunction (fun x => ⨆ j, g j x) e y + (q y : EReal) := by
    funext y
    simpa only [iSup_apply, v, chartFunction] using
      iSup_add_coe (fun j => g j (e.val.symm y)) (q y)
  have hVeq : EqOn (fun y => chartFunction u e y + (q y : EReal))
      (uscRegularization (⨆ j, v j)) W := by
    intro y hy
    rw [hsup, uscRegularization_add_coe_continuousAt_apply _ (hqc y hy),
      uscRegularization_chartFunction_apply _ e (hWe hy), heq]
  obtain ⟨S, hS, hSW⟩ := Metric.isOpen_iff.mp hW z hzW
  have hclosed : closedBall z (S / 2) ⊆ W :=
    (closedBall_subset_ball (by linarith)).trans hSW
  obtain ⟨D, hD⟩ := (isCompact_closedBall z (S / 2)).exists_bound_of_continuousOn
    (hq.continuousOn.mono hclosed)
  refine ⟨ball z (S / 4), isOpen_ball, mem_ball_self (by linarith), ?_⟩
  have hbound : ∀ j, ∀ y ∈ ball z (S / 2), v j y ≤ ((C + D : ℝ) : EReal) := by
    intro j y hy
    rw [EReal.coe_add]
    exact add_le_add (hupper j _) (EReal.coe_le_coe_iff.mpr
      ((le_abs_self _).trans (hD y (ball_subset_closedBall hy))))
  have hae := ae_uscRegularization_iSup_eq_on_ball
    (u := v) (U := W) (fun j => (hpsh (g j) (hg j)).discPshOn)
    (fun y _ j k hjk => add_le_add (hmono hjk _) le_rfl)
    (volume : Measure (ComplexModel (m + 1))) z (S := S / 2) (by linarith)
    ((ball_subset_ball (by linarith)).trans hSW) hbound
  rw [show (S / 2) / 2 = S / 4 by ring] at hae
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_ball] with y hy hymem
  have hyW : y ∈ W := hSW (ball_subset_ball (by linarith) hymem)
  have h1 : uscRegularization (fun t => ⨆ j, v j t) y = ⨆ j, v j y := hy hymem
  have hfn : (fun t => ⨆ j, v j t) = (⨆ j, v j) := funext fun _ => iSup_apply.symm
  rw [hfn] at h1
  have h2 := (hVeq hyW).trans h1
  have h3 : (⨆ j, v j y) = (⨆ j, chartFunction (g j) e y) + (q y : EReal) :=
    iSup_add_coe (fun j => chartFunction (g j) e y) (q y)
  rw [h3] at h2
  have hcanc := EReal.addLECancellable_coe (q y)
  apply Eq.symm
  apply le_antisymm
  · rw [← hcanc.add_le_add_iff_right]
    exact h2.le
  · rw [← hcanc.add_le_add_iff_right]
    exact h2.ge

/-- The original real bounds pass to the literal regularized supremum. -/
theorem uscRegularization_iSup_bounds {X : Type*} [TopologicalSpace X]
    (g : ℕ → X → EReal) (a b : ℝ)
    (hb : ∀ j x, (a : EReal) ≤ g j x ∧ g j x ≤ (b : EReal)) :
    ∀ x, (a : EReal) ≤ uscRegularization (fun y => ⨆ j, g j y) x ∧
      uscRegularization (fun y => ⨆ j, g j y) x ≤ (b : EReal) := by
  intro x
  refine ⟨((hb 0 x).1.trans (le_iSup (fun j => g j x) 0)).trans
    (le_uscRegularization (fun y => ⨆ j, g j y) x), ?_⟩
  apply uscRegularization_le_of_eventually_le upperSemicontinuousAt_const
  exact Eventually.of_forall fun y => iSup_le fun j => (hb j y).2

namespace BackgroundPatch

variable {omega : Background (m + 1) M}

/-- Finite original bounds make the actual corrected real readers
monotone, with no representative convergence input. -/
theorem correctedReal_monotone (P : BackgroundPatch omega)
    {g : ℕ → M → EReal} (a b : ℝ)
    (hb : ∀ j x, (a : EReal) ≤ g j x ∧ g j x ≤ (b : EReal)) (hmono : Monotone g)
    (z : ComplexModel (m + 1)) : Monotone fun j => P.correctedReal (g j) z := by
  intro j k hjk
  have hgbot : g j (P.geometry.chart.val.symm z) ≠ ⊥ :=
    ne_of_gt ((EReal.bot_lt_coe a).trans_le (hb j _).1)
  have hgtop : g k (P.geometry.chart.val.symm z) ≠ ⊤ :=
    ne_of_lt ((hb k _).2.trans_lt (EReal.coe_lt_top b))
  exact add_le_add (EReal.toReal_le_toReal (hmono hjk _) hgbot hgtop) le_rfl

/-- Almost-everywhere real convergence of the corrected readers is
produced from the actual original regularized supremum and its bounds. -/
theorem correctedReal_ae_tendsto_uscSup (P : BackgroundPatch omega)
    {g : ℕ → M → EReal} (hg : ∀ j, IsHermitianPSH omega (g j)) (a b : ℝ)
    (hb : ∀ j x, (a : EReal) ≤ g j x ∧ g j x ≤ (b : EReal)) (hmono : Monotone g) :
    ∀ᵐ z, z ∈ P.geometry.domain → Tendsto (fun j => P.correctedReal (g j) z) atTop
      (𝓝 (P.correctedReal (uscRegularization (fun x => ⨆ j, g j x)) z)) := by
  let u : M → EReal := uscRegularization (fun x => ⨆ j, g j x)
  have huBounds := uscRegularization_iSup_bounds g a b hb
  have hae := ae_chartFunction_iSup_eq_of_monotone omega hg b
    (fun j x => (hb j x).2) hmono rfl P.geometry.chart
  have hae' := (ae_restrict_iff' P.geometry.chart.val.open_target.measurableSet).mp hae
  filter_upwards [hae'] with z hz hzD
  have hzT := P.geometry.domain_le_target hzD
  have hlim : Tendsto (fun j => chartFunction (g j) P.geometry.chart z) atTop
      (𝓝 (chartFunction u P.geometry.chart z)) := by
    rw [← hz hzT]
    exact tendsto_atTop_iSup (fun j k hjk => hmono hjk _)
  have huTop : chartFunction u P.geometry.chart z ≠ ⊤ :=
    ne_of_lt ((huBounds _).2.trans_lt (EReal.coe_lt_top b))
  have huBot : chartFunction u P.geometry.chart z ≠ ⊥ :=
    ne_of_gt ((EReal.bot_lt_coe a).trans_le (huBounds _).1)
  exact ((EReal.tendsto_toReal huTop huBot).comp hlim).add_const (P.correction z)

/-- The genuine native mixed nonclosed-background product converges for
actual bounded increasing Hermitian potentials. The limiting class,
corrected PSH readers and almost-everywhere limits are all produced. -/
theorem mixedCurrent_increasing_uscSup (P : BackgroundPatch omega) (p : ℕ) (hp : p ≤ m + 1)
    (u : ℕ → Fin p → M → EReal) (hu : ∀ j i, IsHermitianPSH omega (u j i))
    (a b : ℝ) (hb : ∀ j i x, (a : EReal) ≤ u j i x ∧ u j i x ≤ (b : EReal))
    (hmono : ∀ i, Monotone fun j => u j i) :
    WeakTendsto (fun j => P.mixedCurrent p hp (u j))
      (P.mixedCurrent p hp (fun i => uscRegularization (fun x => ⨆ j, u j i x))) := by
  let u₀ : Fin p → M → EReal := fun i => uscRegularization (fun x => ⨆ j, u j i x)
  have hu₀ (i : Fin p) : IsHermitianPSH omega (u₀ i) :=
    isHermitianPSH_uscRegularization_iSup_of_uniform_bound omega (fun j => u j i)
      (fun j => hu j i) b (fun j x => (hb j i x).2)
  have hb₀ (i : Fin p) : ∀ x, (a : EReal) ≤ u₀ i x ∧ u₀ i x ≤ (b : EReal) :=
    uscRegularization_iSup_bounds (fun j => u j i) a b (fun j x => hb j i x)
  apply backgroundExpansion_increasing_oneCurrent p (m + 1 - p) (Nat.sub_add_cancel hp)
    (fun j i => P.correctedReal (u j i)) (fun i => P.correctedReal (u₀ i))
    (fun j i => P.correctedReal_isLocallyBoundedPshOn (hu j i) ⟨a, b, hb j i⟩)
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu₀ i) ⟨a, b, hb₀ i⟩)
    (fun i z _ => P.correctedReal_monotone a b (fun j x => hb j i x) (hmono i) z)
    (fun i => P.correctedReal_ae_tendsto_uscSup (fun j => hu j i) a b
      (fun j x => hb j i x) (hmono i)) P.residual_smooth

/-- The top-degree native product is the full-degree specialization of
the same actual increasing-convergence theorem. -/
theorem current_increasing_uscSup (P : BackgroundPatch omega)
    (u : ℕ → Fin (m + 1) → M → EReal) (hu : ∀ j i, IsHermitianPSH omega (u j i))
    (a b : ℝ) (hb : ∀ j i x, (a : EReal) ≤ u j i x ∧ u j i x ≤ (b : EReal))
    (hmono : ∀ i, Monotone fun j => u j i) :
    WeakTendsto (fun j => P.current (u j))
      (P.current (fun i => uscRegularization (fun x => ⨆ j, u j i x))) := by
  let u₀ : Fin (m + 1) → M → EReal := fun i => uscRegularization (fun x => ⨆ j, u j i x)
  have hu₀ (i : Fin (m + 1)) : IsHermitianPSH omega (u₀ i) :=
    isHermitianPSH_uscRegularization_iSup_of_uniform_bound omega (fun j => u j i)
      (fun j => hu j i) b (fun j x => (hb j i x).2)
  have hb₀ (i : Fin (m + 1)) : ∀ x, (a : EReal) ≤ u₀ i x ∧ u₀ i x ≤ (b : EReal) :=
    uscRegularization_iSup_bounds (fun j => u j i) a b (fun j x => hb j i x)
  exact backgroundExpansion_increasing_oneCurrent (m + 1) 0 (Nat.zero_add (m + 1))
    (fun j i => P.correctedReal (u j i)) (fun i => P.correctedReal (u₀ i))
    (fun j i => P.correctedReal_isLocallyBoundedPshOn (hu j i) ⟨a, b, hb j i⟩)
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu₀ i) ⟨a, b, hb₀ i⟩)
    (fun i z _ => P.correctedReal_monotone a b (fun j x => hb j i x) (hmono i) z)
    (fun i => P.correctedReal_ae_tendsto_uscSup (fun j => hu j i) a b
      (fun j x => hb j i x) (hmono i)) P.residual_smooth

end BackgroundPatch

end SGPT.PSH.HermitianGlobalProducts
