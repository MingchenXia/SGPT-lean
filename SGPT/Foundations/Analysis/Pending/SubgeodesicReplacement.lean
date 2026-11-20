import SGPT.Foundations.Analysis.Pending.SubgeodesicBoundaryUpperControl
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicClosedRestriction

/-!
# The actual subgeodesic replacement curve

Replace the open segment `(a,b)` by a normalized subgeodesic with the old
closed endpoint slices. Actual joint endpoint upper control gives USC at
the two interior seams; arbitrary curve values outside `(0,1)` are irrelevant.
This is the boundary part of Xia, SGPT Lemma 4.1.1, PDF pages 0152--0153.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicGluing

open FirstPass SubgeodesicBoundaryUpperControl

noncomputable section

/-- Substitute a normalized curve on the open physical interval `(a,b)`.
At the seams and outside the replacement interval retain the old curve. -/
def replacementCurve {M : Type*} (curve replacement : ℝ → M → EReal)
    (a b : ℝ) : ℝ → M → EReal := by
  classical
  exact fun t => if t ∈ Ioo a b then replacement ((t - a) / (b - a)) else curve t

/-- Positive inverse affine time sends the physical replacement interval
to the normalized interval. -/
theorem replacementTime_mem_Ioo {a b t : ℝ} (hab : a < b) (ht : t ∈ Ioo a b) :
    (t - a) / (b - a) ∈ Ioo (0 : ℝ) 1 :=
  ⟨div_pos (sub_pos.mpr ht.1) (sub_pos.mpr hab),
    (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual joint USC of the piecewise replacement curve on the open strip.
Domination is needed later for PSH, but not for this upper control theorem. -/
theorem upperSemicontinuousAt_replacementCurve
    {theta : SmoothRealForm n M 2} {curve replacement : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom theta curve u₀ u₁)
    {a b : ℝ} (hab : a < b)
    (hr : IsSubgeodesicFrom theta replacement
      (closedSubgeodesicSlice curve u₀ u₁ a) (closedSubgeodesicSlice curve u₀ u₁ b))
    (x : M) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    UpperSemicontinuousAt (fun p : M × ℝ => replacementCurve curve replacement a b p.2 p.1)
      (x, t) := by
  classical
  let A : M × ℝ → M × ℝ := fun p => (p.1, (p.2 - a) / (b - a))
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hOld := upperSemicontinuousAt_of_isSubgeodesicFrom h x ht
  by_cases htab : t ∈ Ioo a b
  · have hNew : UpperSemicontinuousAt
        (fun p : M × ℝ => replacement ((p.2 - a) / (b - a)) p.1) (x, t) :=
      UpperSemicontinuousAt.comp (g := A) (c := (x, t))
        (upperSemicontinuousAt_of_isSubgeodesicFrom hr x (replacementTime_mem_Ioo hab htab))
        hA.continuousAt
    intro c hc
    have hc' : replacement ((t - a) / (b - a)) x < c := by
      simpa [replacementCurve, htab] using hc
    have hNear : ∀ᶠ p : M × ℝ in 𝓝 (x, t), p.2 ∈ Ioo a b :=
      continuous_snd.continuousAt.eventually (isOpen_Ioo.mem_nhds htab)
    filter_upwards [hNew c hc', hNear] with p hp hpI
    simpa [replacementCurve, hpI] using hp
  · intro c hc
    have hcOld : curve t x < c := by simpa [replacementCurve, htab] using hc
    by_cases hta : t = a
    · have haI : a ∈ Ioo (0 : ℝ) 1 := by simpa [hta] using ht
      have hcEnd : closedSubgeodesicSlice curve u₀ u₁ a x < c := by
        rw [closedSubgeodesicSlice_eq_curve haI]
        simpa [hta] using hcOld
      have hleft := eventually_lt_left_endpoint hr hcEnd
      have hAt : Tendsto A (𝓝 (x, t)) (𝓝 (x, 0)) := by
        simpa [A, hta] using hA.continuousAt.tendsto (x := (x, t))
      filter_upwards [hOld c hcOld, hAt.eventually hleft] with p hpOld hpNew
      by_cases hpI : p.2 ∈ Ioo a b
      · simpa [replacementCurve, hpI] using hpNew (replacementTime_mem_Ioo hab hpI)
      · simpa [replacementCurve, hpI] using hpOld
    · by_cases htb : t = b
      · have hbI : b ∈ Ioo (0 : ℝ) 1 := by simpa [htb] using ht
        have hcEnd : closedSubgeodesicSlice curve u₀ u₁ b x < c := by
          rw [closedSubgeodesicSlice_eq_curve hbI]
          simpa [htb] using hcOld
        have hright := eventually_lt_right_endpoint hr hcEnd
        have hAt : Tendsto A (𝓝 (x, t)) (𝓝 (x, 1)) := by
          simpa [A, htb, ne_of_gt (sub_pos.mpr hab)] using
            hA.continuousAt.tendsto (x := (x, t))
        filter_upwards [hOld c hcOld, hAt.eventually hright] with p hpOld hpNew
        by_cases hpI : p.2 ∈ Ioo a b
        · simpa [replacementCurve, hpI] using hpNew (replacementTime_mem_Ioo hab hpI)
        · simpa [replacementCurve, hpI] using hpOld
      · have htout : t < a ∨ b < t := by
          rcases le_total t a with hta' | hat'
          · exact Or.inl (lt_of_le_of_ne hta' hta)
          · have hat : a < t := lt_of_le_of_ne hat' (Ne.symm hta)
            have hbt : b ≤ t := le_of_not_gt (fun htb' => htab ⟨hat, htb'⟩)
            exact Or.inr (lt_of_le_of_ne hbt (Ne.symm htb))
        have hNear : ∀ᶠ p : M × ℝ in 𝓝 (x, t), p.2 ∉ Ioo a b := by
          rcases htout with hta' | hbt
          · filter_upwards [continuous_snd.continuousAt.eventually
              (isOpen_Iio.mem_nhds hta')] with p hp hpI
            exact (not_lt_of_ge hp.le) hpI.1
          · filter_upwards [continuous_snd.continuousAt.eventually
              (isOpen_Ioi.mem_nhds hbt)] with p hp hpI
            exact (not_lt_of_ge hp.le) hpI.2
        filter_upwards [hOld c hcOld, hNear] with p hp hpI
        simpa [replacementCurve, hpI] using hp

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicGluing
