import SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumInterior
import SGPT.Foundations.Analysis.Pending.SubgeodesicEndpointQuasiEverywhere
import SGPT.Foundations.Analysis.Pending.ChoquetRegularization

/-!
# Pointwise endpoints of arbitrary-family subgeodesic suprema

Choquet reduction of the endpoint family, countable pluripolar stability and
actual endpoint limits identify the canonical pointwise limits of the
regularized supremum. These producers precede the endpoint L1 proof.
Source: Xia, SGPT Proposition 4.1.3, PDF page 0151.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumEndpoints

open FirstPass FirstPass.PositiveClasses SubgeodesicEndpointLimits

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The canonical left limit is dominated by a potential upper endpoint when
the curve lies below its chord with a finite upper constant. This does not
assume endpoint L1 convergence. -/
theorem leftLimit_le_of_upper_chord {theta : SmoothRealForm n M 2}
    {curve : ℝ → M → EReal} (h : IsSubgeodesicInterior theta curve)
    {u : M → EReal} {C : ℝ}
    (hupper : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, curve t x ≤ eRealChord (u x) (C : EReal) t)
    (x : M) : leftLimit curve x ≤ u x := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hcoef : Tendsto (fun t : ℝ => ((1 - t : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : EReal)) := by
    have h₁ : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
      tendsto_const_nhds
    simpa using EReal.tendsto_coe.mpr (h₁.sub ht)
  have hA : Tendsto (fun t : ℝ => ((1 - t : ℝ) : EReal) * u x)
      (𝓝[>] (0 : ℝ)) (𝓝 (u x)) := by
    simpa [Function.comp_def] using (EReal.continuousAt_mul (p := ((1 : EReal), u x))
      (Or.inl one_ne_zero) (Or.inl one_ne_zero)
      (Or.inl (by change ((1 : ℝ) : EReal) ≠ ⊥; exact EReal.coe_ne_bot 1))
      (Or.inl (by change ((1 : ℝ) : EReal) ≠ ⊤; exact EReal.coe_ne_top 1))).tendsto.comp
        (hcoef.prodMk_nhds tendsto_const_nhds)
  have hB : Tendsto (fun t : ℝ => (t : EReal) * (C : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : EReal)) := by
    have hreal : Tendsto (fun t : ℝ => t * C) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using ht.mul_const C
    simpa using EReal.tendsto_coe.mpr hreal
  have hchord : Tendsto (fun t => eRealChord (u x) (C : EReal) t)
      (𝓝[>] (0 : ℝ)) (𝓝 (u x)) := by
    simpa [eRealChord, Function.comp_def] using
      (EReal.continuousAt_add (p := (u x, 0)) (Or.inr (by simp))
        (Or.inr (by simp))).tendsto.comp (hA.prodMk_nhds hB)
  apply le_of_tendsto_of_tendsto (tendsto_leftLimit h x) hchord
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  exact hupper t ht x

variable [CompactSpace M] [ConnectedSpace M]

/-- The canonical pointwise left limit of the regularized supremum agrees
quasi-everywhere with the regularized left endpoint supremum. -/
theorem leftLimit_uscRegularization_iSup_quasiEverywhereEq {ι : Type*} [Nonempty ι]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {curve : ι → ℝ → M → EReal} {u₀ u₁ : ι → M → EReal}
    (h : ∀ i, IsSubgeodesicFrom theta.val (curve i) (u₀ i) (u₁ i)) {C : ℝ}
    (h₀ : ∀ i x, u₀ i x ≤ (C : EReal)) (h₁ : ∀ i x, u₁ i x ≤ (C : EReal)) :
    QuasiEverywhereEq (n := n)
      (leftLimit (fun t => uscRegularization (fun x => ⨆ i, curve i t x)))
      (uscRegularization (fun x => ⨆ i, u₀ i x)) := by
  classical
  let U : ℝ → M → EReal := fun t => uscRegularization (fun x => ⨆ i, curve i t x)
  let v₀ : M → EReal := uscRegularization (fun x => ⨆ i, u₀ i x)
  have hC := SubgeodesicSupremumSlices.uniform_upper_bound_of_endpoint_bounds h h₀ h₁
  have hU : IsSubgeodesicInterior theta.val U :=
    SubgeodesicSupremumInterior.isSubgeodesicInterior_uscRegularization_iSup
      (fun i => (h i).interior) hC
  have hv₀ : IsThetaPshPotential theta.val v₀ :=
    SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
      (fun i => (h i).left_endpoint) h₀
  have hiU : ∀ i t x, curve i t x ≤ U t x := fun i t x =>
    (le_iSup (fun i => curve i t x) i).trans
      (le_uscRegularization (fun x => ⨆ i, curve i t x) x)
  have hiv₀ : ∀ i x, u₀ i x ≤ v₀ x := fun i x =>
    (le_iSup (fun i => u₀ i x) i).trans
      (le_uscRegularization (fun x => ⨆ i, u₀ i x) x)
  have hupper : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      U t x ≤ eRealChord (v₀ x) (C : EReal) t := by
    intro t ht
    apply uscRegularization_le (upperSemicontinuous_eRealChord
      hv₀.1.quasiPlurisubharmonic.upperSemicontinuous upperSemicontinuous_const
      (fun x => hv₀.1.quasiPlurisubharmonic.ne_top x)
      (fun _ => EReal.coe_ne_top C) ht.1.le ht.2.le)
    intro x
    exact iSup_le fun i => ((h i).le_eRealChord ht x).trans
      (eRealChord_mono (hiv₀ i x) (h₁ i x) ht.1.le ht.2.le)
  have hle : ∀ x, leftLimit U x ≤ v₀ x := leftLimit_le_of_upper_chord hU hupper
  obtain ⟨s, hs, hseq⟩ := exists_seq_uscRegularization_iSup_eq (F := range u₀)
    (range_nonempty u₀)
  choose idx hidx using hs
  have hsg : ∀ j, IsThetaPshPotential theta.val (s j) := by
    intro j
    rw [← hidx j]
    exact (h (idx j)).left_endpoint
  have hsC : ∀ j x, s j x ≤ (C : EReal) := by
    intro j x
    rw [← hidx j]
    exact h₀ (idx j) x
  have hQlower : QuasiEverywhere (n := n) (fun x => ∀ j, s j x ≤ leftLimit U x) :=
    RooftopObstacleQuasiEverywhere.quasiEverywhere_forall
      (PluripolarOuterCapacity.countablyStablePluripolar omega) (fun j =>
        (SubgeodesicEndpointQuasiEverywhere.leftLimit_quasiEverywhereEq omega theta
          (h (idx j))).mono fun x hx => by
            rw [← hidx j, ← hx]
            exact le_of_tendsto_of_tendsto
              (tendsto_leftLimit (h (idx j)).interior x) (tendsto_leftLimit hU x)
              (Eventually.of_forall fun t => hiU (idx j) t x))
  have hQneg := NegligibleSetsPluripolarProof.negligibleSetsPluripolar omega theta s C hsg hsC
  refine (quasiEverywhere_and hQneg hQlower).mono fun x hx => le_antisymm (hle x) ?_
  have hreg : uscRegularization (⨆ j, s j) = v₀ := by
    rw [sSup_range] at hseq
    have hfun : (⨆ i, u₀ i) = (fun x => ⨆ i, u₀ i x) := by
      funext x
      exact iSup_apply
    rw [hfun] at hseq
    exact hseq
  calc v₀ x = uscRegularization (⨆ j, s j) x := congrFun hreg.symm x
    _ ≤ (⨆ j, s j) x := hx.1
    _ ≤ leftLimit U x := by rw [iSup_apply]; exact iSup_le (hx.2)

/-- Right endpoint identification, by applying left identification to the
actual time-reversed subgeodesic family. -/
theorem rightLimit_uscRegularization_iSup_quasiEverywhereEq {ι : Type*} [Nonempty ι]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {curve : ι → ℝ → M → EReal} {u₀ u₁ : ι → M → EReal}
    (h : ∀ i, IsSubgeodesicFrom theta.val (curve i) (u₀ i) (u₁ i)) {C : ℝ}
    (h₀ : ∀ i x, u₀ i x ≤ (C : EReal)) (h₁ : ∀ i x, u₁ i x ≤ (C : EReal)) :
    QuasiEverywhereEq (n := n)
      (rightLimit (fun t => uscRegularization (fun x => ⨆ i, curve i t x)))
      (uscRegularization (fun x => ⨆ i, u₁ i x)) :=
  leftLimit_uscRegularization_iSup_quasiEverywhereEq omega theta
    (fun i => (h i).timeReversed) h₁ h₀

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumEndpoints
