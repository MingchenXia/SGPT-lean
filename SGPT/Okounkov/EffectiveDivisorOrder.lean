import SGPT.Foundations.Analysis.Pending.DivisorExponent
import SGPT.Foundations.Analysis.Pending.DivisorMetric
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open DivisorExponent

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original Cartier ideal itself produces a genuinely nonzero
holomorphic germ at every point. -/
theorem effectiveDivisor_isNonzeroAt (D : EffectiveDivisor n M) (x : M) :
    IsNonzeroAt D.ideal x := by
  obtain ⟨U, hU, hxU, g, hg, hgnz, hgen⟩ := D.isInvertible x
  have hhol : HolomorphicAt n g x :=
    DivisorExponent.holomorphicAt_of_mdifferentiableOn_open hU hg hxU
  refine ⟨g, (hgen x hxU g).mpr
    (isInSpanAt_of_eq_mul rfl hhol (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp)), ?_⟩
  rw [frequently_nhds_iff]
  intro V hxV hV
  obtain ⟨y, hy, hy0⟩ := hgnz (V ∩ U) (hV.inter hU) inter_subset_right
    ⟨x, hxV, hxU⟩
  exact ⟨y, hy.1, hy0⟩

/-- The actual maximal Cartier divisibility exponent is locally constant
on the genuine smooth carrier; local constancy is reused, not assumed. -/
theorem isLocallyConstant_effectiveDivisor_order {W : Set M} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) (D : EffectiveDivisor n M) :
    IsLocallyConstant (fun p : W => divExp n D.ideal W (p : M)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro p
  have hlocal := eventually_divExp_eq
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)
    (hW.2.2 p p.property)
    (Eventually.of_forall fun y => effectiveDivisor_isNonzeroAt D y)
  have hincl : Tendsto (Subtype.val : W → M) (𝓝 p) (𝓝 (p : M)) :=
    continuous_subtype_val.continuousAt.tendsto
  filter_upwards [hincl.eventually hlocal] with q hq
  exact hq q.property

/-- A genuine connected smooth component produces one actual finite
natural Cartier order, with the exact divisibility characterization
at every original point. -/
theorem exists_effectiveDivisor_order_on_connected_component {W : Set M} {k : ℕ}
    (hW : IsClosedConnectedSubmanifold n W k) (D : EffectiveDivisor n M) :
    ∃ a : ℕ, ∀ x ∈ W, ∀ r : ℕ, IsDivNear n D.ideal W r x ↔ r ≤ a := by
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  obtain ⟨p, hp⟩ := hW.2.1.nonempty
  have hloc := isLocallyConstant_effectiveDivisor_order hW D
  have hhol : ∀ x g, D.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hg
  refine ⟨divExp n D.ideal W p, fun x hx r => ?_⟩
  have hconst := hloc.apply_eq_of_preconnectedSpace (⟨x, hx⟩ : W) (⟨p, hp⟩ : W)
  exact (isDivNear_iff_le_divExp hhol hx (effectiveDivisor_isNonzeroAt D x)).trans
    (by rw [hconst])

end SGPT.Okounkov
