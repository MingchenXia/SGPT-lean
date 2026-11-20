import SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity

set_option autoImplicit false

/-!
# Quasi-continuity of a pair, and of a minimum

Xia's Theorem 2.4.4 needs *one* small-capacity open set outside which several
functions are simultaneously continuous: in the enlargement after (2.27)
(`xia-sgpt:page-0081`) the potential `P_theta(f)` and the obstacle `f` must both
be continuous on the same complement, and the obstacle of Section 3.1 is itself
a minimum `min {phi, psi}` of two potentials.

Both reductions are the same halving argument, recorded here once:
`Cap_theta` is finitely subadditive, so two open sets of capacity `< eps/2` can
be replaced by their union, and continuity survives passage to the smaller
complement.  For the minimum one extra point is needed: on a set where both
functions are finite, `(min p q).toReal = min p.toReal q.toReal`, so
`ContinuousOn.min` applies.

`exists_isOpen_thetaCapacity_lt_continuousOn_min_of_boundedOn` is the form the
rooftop obstacle uses: `phi` and `psi` bounded `theta`-PSH potentials on an open
set (which, away from `nK({theta})`, is what Lemma 2.4.1 provides for their
truncations at `V_theta - C`).
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ThetaCapacityMinQuasiContinuity

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.ThetaCapacityLocalQuasiContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [BorelSpace M] in
/-- **Two quasi-continuous functions are quasi-continuous off one common open
set.**  Halve the tolerance and take the union; `Cap_theta` is subadditive and
continuity passes to the smaller complement. -/
theorem exists_isOpen_thetaCapacity_lt_continuousOn_pair
    {theta : ClosedRealOneOneForm n M} {V p q : M → EReal} {K : Set M}
    (hp : ∀ eps : ℝ, 0 < eps → ∃ G : Set M, IsOpen G ∧
      thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (p y).toReal) (K \ G))
    (hq : ∀ eps : ℝ, 0 < eps → ∃ G : Set M, IsOpen G ∧
      thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (q y).toReal) (K \ G))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (p y).toReal) (K \ G) ∧
      ContinuousOn (fun y => (q y).toReal) (K \ G) := by
  obtain ⟨G₁, hG₁open, hG₁cap, hG₁cont⟩ := hp (eps / 2) (by linarith)
  obtain ⟨G₂, hG₂open, hG₂cap, hG₂cont⟩ := hq (eps / 2) (by linarith)
  refine ⟨G₁ ∪ G₂, hG₁open.union hG₂open, ?_, ?_, ?_⟩
  · have hsum : thetaCapacity theta V (G₁ ∪ G₂) ≤
        thetaCapacity theta V G₁ + thetaCapacity theta V G₂ :=
      thetaCapacity_union_le theta V G₁ G₂
    have hlt : thetaCapacity theta V G₁ + thetaCapacity theta V G₂ <
        ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) :=
      ENNReal.add_lt_add hG₁cap hG₂cap
    have heq : ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) =
        ENNReal.ofReal eps := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      norm_num
    exact lt_of_le_of_lt hsum (heq ▸ hlt)
  · exact hG₁cont.mono (fun x hx => ⟨hx.1, fun h => hx.2 (Or.inl h)⟩)
  · exact hG₂cont.mono (fun x hx => ⟨hx.1, fun h => hx.2 (Or.inr h)⟩)

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- On a set where both values are finite, the real part of the minimum is the
minimum of the real parts. -/
theorem toReal_min_eq {p q : M → EReal} {T : Set M}
    (hpfin : ∀ x ∈ T, p x ≠ ⊥ ∧ p x ≠ ⊤) (hqfin : ∀ x ∈ T, q x ≠ ⊥ ∧ q x ≠ ⊤)
    {x : M} (hx : x ∈ T) :
    (min (p x) (q x)).toReal = min ((p x).toReal) ((q x).toReal) := by
  obtain ⟨hp1, hp2⟩ := hpfin x hx
  obtain ⟨hq1, hq2⟩ := hqfin x hx
  rcases le_total (p x) (q x) with h | h
  · rw [min_eq_left h, min_eq_left (EReal.toReal_le_toReal h hp1 hq2)]
  · rw [min_eq_right h, min_eq_right (EReal.toReal_le_toReal h hq1 hp2)]

omit [BorelSpace M] in
/-- **The minimum of two quasi-continuous finite functions is quasi-continuous.** -/
theorem exists_isOpen_thetaCapacity_lt_continuousOn_min
    {theta : ClosedRealOneOneForm n M} {V p q : M → EReal} {K : Set M}
    (hpfin : ∀ x ∈ K, p x ≠ ⊥ ∧ p x ≠ ⊤) (hqfin : ∀ x ∈ K, q x ≠ ⊥ ∧ q x ≠ ⊤)
    (hp : ∀ eps : ℝ, 0 < eps → ∃ G : Set M, IsOpen G ∧
      thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (p y).toReal) (K \ G))
    (hq : ∀ eps : ℝ, 0 < eps → ∃ G : Set M, IsOpen G ∧
      thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (q y).toReal) (K \ G))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (min (p y) (q y)).toReal) (K \ G) := by
  obtain ⟨G, hGopen, hGcap, hpc, hqc⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_pair hp hq heps
  refine ⟨G, hGopen, hGcap, ?_⟩
  intro x hx
  refine ContinuousWithinAt.congr ((hpc x hx).inf (hqc x hx)) (fun y hy => ?_) ?_
  · rw [toReal_min_eq (fun z hz => hpfin z hz.1) (fun z hz => hqfin z hz.1) hy]
  · rw [toReal_min_eq (fun z hz => hpfin z hz.1) (fun z hz => hqfin z hz.1) hx]

/-- **The rooftop obstacle is quasi-continuous.**  For two `theta`-PSH
potentials bounded on an open `Omega` and a compact `K ⊆ Omega`, the minimum
`min {phi, psi}` is continuous outside an open set of arbitrarily small
`Cap_theta(-, V)`.  This is Xia's Theorem 2.3.2 applied to each of the two
potentials, in the local form of `Pending.ThetaCapacityLocalQuasiContinuity`. -/
theorem exists_isOpen_thetaCapacity_lt_continuousOn_min_of_boundedOn
    {theta : ClosedRealOneOneForm n M} {V p q : M → EReal}
    (hp : IsThetaPshPotential theta.val p) (hq : IsThetaPshPotential theta.val q)
    {Omega : Set M} (hOmega : IsOpen Omega)
    (hpb : IsBoundedPotentialOn p Omega) (hqb : IsBoundedPotentialOn q Omega)
    (hVb : IsBoundedPotentialOn V Omega)
    {K : Set M} (hK : IsCompact K) (hKO : K ⊆ Omega)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ G : Set M, IsOpen G ∧ thetaCapacity theta V G < ENNReal.ofReal eps ∧
      ContinuousOn (fun y => (min (p y) (q y)).toReal) (K \ G) :=
  exists_isOpen_thetaCapacity_lt_continuousOn_min
    (fun _x hx => ⟨hpb.ne_bot (hKO hx), hpb.ne_top (hKO hx)⟩)
    (fun _x hx => ⟨hqb.ne_bot (hKO hx), hqb.ne_top (hKO hx)⟩)
    (fun _ h => exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn hp hOmega hpb hVb hK hKO h)
    (fun _ h => exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn hq hOmega hqb hVb hK hKO h)
    heps

end

end SGPT.Foundations.Analysis.Pending.ThetaCapacityMinQuasiContinuity
