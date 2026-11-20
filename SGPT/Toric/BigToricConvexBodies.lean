import SGPT.Toric.BigToricEnvelope
import SGPT.Toric.BigToricMongeAmpere
import SGPT.PSH.GlobalPComparison

/-!
# `P`-singularity types of toric potentials and convex bodies in `P_D`

Source `chapter_toric_big.tex`:

* `cor:PequivtorD`, equivalence (1) ⇔ (3) for potentials of positive mass:
  `φ ≼_P ψ ⇔ Δ(θ, φ) ⊆ Δ(θ, ψ)` (via `prop:GPenvelopebig`, as in the source);
  more generally, for all toric potentials, `P_θ[φ] ≤ P_θ[ψ] ⇔ Δ(θ, φ) ⊆ Δ(θ, ψ)`;
* `cor:bij_conv_torpsh`, the surjectivity clause: every convex body `K ⊆ P_D` is the Newton
  body of a toric potential (with `G_φ = χ_K`), and the map `φ ↦ Δ(θ, φ)` is injective on
  `P`-equivalence classes of potentials of positive mass.

`≼_P` is the source global `P`-order (`GlobalPComparison.sourcePOrder`); for potentials of
positive mass it is the comparison of the envelopes `P_θ[·]` in the background `θ`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators Classical

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

omit [Fintype K] [Nonempty K] in
/-- The indicator of a closed set is lower semicontinuous. -/
theorem lowerSemicontinuous_indicator_of_isClosed {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E] {A : Set E} (hA : IsClosed A) :
    LowerSemicontinuous (SGPT.Convex.indicator A) := by
  intro x y hy
  by_cases hx : x ∈ A
  · simp only [SGPT.Convex.indicator, if_pos hx] at hy
    refine Eventually.of_forall fun x' => hy.trans_le ?_
    by_cases hx' : x' ∈ A <;> simp [SGPT.Convex.indicator, hx']
  · simp only [SGPT.Convex.indicator, if_neg hx] at hy
    filter_upwards [hA.isOpen_compl.mem_nhds hx] with x' hx'
    simp only [SGPT.Convex.indicator, if_neg (show x' ∉ A from hx')]
    exact hy

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)
variable (hP : (toricDivisorPolytope D).Nonempty)

include hP

/-- `P_θ[φ] ≤ P_θ[ψ] ⇔ Δ(θ, φ) ⊆ Δ(θ, ψ)` for toric potentials (`prop:GPenvelopebig`). -/
theorem sourceSingularityEnvelope_le_iff {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) :
    sourceSingularityEnvelope h.atlasForm u ≤ sourceSingularityEnvelope h.atlasForm v ↔
      h.newtonBody u ⊆ h.newtonBody v := by
  obtain ⟨hPu, hGu⟩ := h.sourceSingularityEnvelope_spec hP hu
  obtain ⟨hPv, hGv⟩ := h.sourceSingularityEnvelope_spec hP hv
  rw [h.le_iff hPu hPv, h.profile_le_iff_legendre hP hPu hPv]
  obtain ⟨a, b, hab⟩ := h.legendre_minimalEnvelope_bounds hP
  have hsub := (h.newtonBody_properties hP hu).2.2.2
  constructor
  · intro hle m hm
    have h1 := hle m
    rw [hGu m, hGv m, if_pos hm] at h1
    by_contra hmv
    rw [if_neg hmv] at h1
    exact (ne_of_lt ((hab m (hsub hm)).2.trans_lt (EReal.coe_lt_top b))) (top_le_iff.mp h1)
  · intro hsubset m
    rw [hGu m, hGv m]
    by_cases hm : m ∈ h.newtonBody u
    · rw [if_pos hm, if_pos (hsubset hm)]
    · rw [if_neg hm]
      exact le_top

/-- Source `cor:PequivtorD`, (1) ⇔ (3) for potentials of positive mass:
`φ ≼_P ψ ⇔ Δ(θ, φ) ⊆ Δ(θ, ψ)`. -/
theorem sourcePOrder_iff_newtonBody_subset {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) (hupos : 0 < h.MA hu univ)
    (hvpos : 0 < h.MA hv univ) :
    GlobalPComparison.sourcePOrder (n := n) u v ↔ h.newtonBody u ⊆ h.newtonBody v := by
  have hun : IsThetaPshPotential h.form.val u :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1
  have hvn : IsThetaPshPotential h.form.val v :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm v).mp hv.1
  rw [GlobalPComparison.sourcePOrder_iff_positive_background
    (polytopeToricKahlerBackground γ hs) h.form hun hvn hupos hvpos]
  rw [← h.sourceSingularityEnvelope_le_iff hP hu hv]
  have e1 : sourceSingularityEnvelope h.atlasForm u = singularityEnvelope h.form.val u :=
    sourceSingularityEnvelope_eq_native h.atlasForm u
  have e2 : sourceSingularityEnvelope h.atlasForm v = singularityEnvelope h.form.val v :=
    sourceSingularityEnvelope_eq_native h.atlasForm v
  rw [e1, e2]
  rfl

/-- Source `cor:PequivtorD` / `cor:bij_conv_torpsh` for potentials of positive mass:
`φ ∼_P ψ ⇔ Δ(θ, φ) = Δ(θ, ψ)`. -/
theorem sourcePEquivalent_iff_newtonBody_eq {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) (hupos : 0 < h.MA hu univ)
    (hvpos : 0 < h.MA hv univ) :
    GlobalPComparison.sourcePEquivalent (n := n) u v ↔ h.newtonBody u = h.newtonBody v := by
  change GlobalPComparison.sourcePOrder (n := n) u v ∧
    GlobalPComparison.sourcePOrder (n := n) v u ↔ _
  rw [h.sourcePOrder_iff_newtonBody_subset hP hu hv hupos hvpos,
    h.sourcePOrder_iff_newtonBody_subset hP hv hu hvpos hupos]
  exact ⟨fun h' => Subset.antisymm h'.1 h'.2, fun h' => ⟨h'.le, h'.ge⟩⟩

/-- Source `cor:bij_conv_torpsh` (surjectivity): every convex body `K ⊆ P_D` (non-empty
compact convex, possibly with empty interior) is the Newton body of a toric potential `φ`,
namely the one with `G_φ = χ_K`. -/
theorem exists_newtonBody_eq {Kb : Set (EuclideanSpace ℝ (Fin n))} (hne : Kb.Nonempty)
    (hcomp : IsCompact Kb) (hconv : Convex ℝ Kb) (hsub : Kb ⊆ toricDivisorPolytope D) :
    ∃ u, u ∈ h.PSHTor ∧ h.legendre u = SGPT.Convex.indicator Kb ∧ h.newtonBody u = Kb := by
  have hG : SGPT.Convex.indicator Kb ∈ ClosedProperOnBody (toricDivisorPolytope D) := by
    refine ⟨(isProper_indicator_iff hconv).mpr hne,
      lowerSemicontinuous_indicator_of_isClosed hcomp.isClosed, fun m hm => ?_⟩
    simp [SGPT.Convex.indicator, show m ∉ Kb from fun h' => hm (hsub h')]
  let u := ((h.equivClosedProper hP).symm ⟨_, hG⟩)
  have hGu : h.legendre u.val = SGPT.Convex.indicator Kb := by
    rw [← h.equivClosedProper_apply hP u, Equiv.apply_symm_apply]
  refine ⟨u.val, u.property, hGu, ?_⟩
  rw [h.newtonBody_eq_closure_effectiveDomain hP u.property, convexNewtonBody, hGu,
    effectiveDomain_indicator]
  exact hcomp.isClosed.closure_eq

/-- The Newton body of a potential of positive mass has positive volume. -/
theorem volume_newtonBody_pos_iff {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    0 < h.MA hu univ ↔ 0 < volume (h.newtonBody u) := by
  rw [h.MA_univ hP hu]
  have hfact : (0 : ENNReal) < (n.factorial : ENNReal) := by
    exact_mod_cast Nat.factorial_pos n
  constructor
  · intro hpos
    exact pos_of_ne_zero fun h0 => by simp [h0] at hpos
  · intro hpos
    exact ENNReal.mul_pos hfact.ne' hpos.ne'

end BigToricMetric

end SGPT.Toric
