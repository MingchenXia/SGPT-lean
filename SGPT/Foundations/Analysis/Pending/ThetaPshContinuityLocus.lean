import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC
import SGPT.Foundations.Analysis.Pending.CollarExhaustionDini

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The continuity locus of a theta-PSH potential, and why it is a locus of FINITENESS

The collar construction of CT22, Lemma 4.3, Step 3 glues on the open set `U`
where `ψ` is finite and continuous.  The clause it must serve, however, is
asserted at parameters where the hypothesis is only that the **`toReal` chart
expression** of `ψ` is `C^∞` near the chart image, together with `ψ ≠ ⊥` at the
one point.  Smoothness of `toReal` does not by itself exclude poles nearby:
`toReal ⊥ = 0`, so a pole is invisible to `toReal`.

It is nevertheless excluded here, by an elementary argument that uses both
halves of `IsThetaPshPotential`:

* `ψ` is upper semicontinuous (it is quasi-plurisubharmonic), so at a pole it
  falls below every level on a whole neighbourhood;
* `toReal ψ` is continuous there, so it stays within `1/2` of `0`;
* the two together force `ψ = ⊥` on a whole OPEN set, which
  `LocallyNondegenerate` — the second half of `IsThetaPshPotential` — forbids.

So `ψ` is finite at every point of its continuity locus, and that locus is open
by construction.  This is the step the blueprint proof compresses into "let `U`
be the set of points at which `ψ` is finite and its chart expression is smooth
near the point; it is open".
-/

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ThetaPshContinuityLocus

open FirstPass FirstPass.NumericalRestrictedVolumeScaffold

noncomputable section

/-! ## The elementary exclusion of a pole -/

section General

variable {X : Type*} [TopologicalSpace X]

/-- **Upper semicontinuity plus continuity of `toReal` plus local nondegeneracy
forbid a pole.**  At a pole, upper semicontinuity puts `u` below `-1` on a
neighbourhood while continuity of `toReal` keeps `|toReal u| < 1/2` there; a
finite value would have to satisfy both, so `u = ⊥` on a whole open set, which
local nondegeneracy excludes. -/
theorem ne_bot_of_upperSemicontinuousAt_of_continuousAt_toReal {u : X → EReal} {x : X}
    (husc : UpperSemicontinuousAt u x)
    (hcont : ContinuousAt (fun y => (u y).toReal) x)
    (hnd : ∀ V : Set X, IsOpen V → x ∈ V → ∃ y ∈ V, u y ≠ ⊥) : u x ≠ ⊥ := by
  intro hbot
  -- below the level `-1` on a neighbourhood
  have hlt : ∀ᶠ y in 𝓝 x, u y < ((-1 : ℝ) : EReal) := by
    refine husc _ ?_
    show u x < ((-1 : ℝ) : EReal)
    rw [hbot]
    exact EReal.bot_lt_coe _
  -- `toReal` stays near `toReal ⊥ = 0`
  have hzero : (u x).toReal = 0 := by rw [hbot]; rfl
  have hnear : ∀ᶠ y in 𝓝 x, |(u y).toReal| < 1 / 2 := by
    have hball := hcont (Metric.ball_mem_nhds ((u x).toReal) (by norm_num : (0:ℝ) < 1 / 2))
    filter_upwards [hball] with y hy
    have : |(u y).toReal - (u x).toReal| < 1 / 2 := by
      simpa [Real.dist_eq] using Metric.mem_ball.mp hy
    rwa [hzero, sub_zero] at this
  -- so `u` is identically `⊥` on an open set
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp (hlt.and hnear)
  obtain ⟨y, hyV, hyne⟩ := hnd V hV hxV
  obtain ⟨hy1, hy2⟩ := hVsub hyV
  have hytop : u y ≠ ⊤ := fun h => by rw [h] at hy1; exact absurd hy1 (by simp)
  have hyreal : ((u y).toReal : EReal) = u y := EReal.coe_toReal hytop hyne
  have : ((u y).toReal : ℝ) < -1 := by
    rw [← EReal.coe_lt_coe_iff, hyreal]; exact hy1
  rw [abs_lt] at hy2
  linarith [hy2.1]

end General

/-! ## The continuity locus -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The open set of points near which `(u ·).toReal` is continuous. -/
def continuityLocus (u : M → EReal) : Set M :=
  {x | ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ContinuousOn (fun y => (u y).toReal) O}

theorem isOpen_continuityLocus (u : M → EReal) : IsOpen (continuityLocus u) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨O, hO, hxO, hcont⟩
  exact ⟨O, fun y hy => ⟨O, hO, hy, hcont⟩, hO, hxO⟩

theorem continuousAt_toReal_of_mem_continuityLocus {u : M → EReal} {x : M}
    (hx : x ∈ continuityLocus u) : ContinuousAt (fun y => (u y).toReal) x := by
  obtain ⟨O, hO, hxO, hcont⟩ := hx
  exact hcont.continuousAt (hO.mem_nhds hxO)

/-- **A theta-PSH potential is finite on its whole continuity locus.** -/
theorem ne_bot_of_mem_continuityLocus {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) {x : M} (hx : x ∈ continuityLocus u) : u x ≠ ⊥ :=
  ne_bot_of_upperSemicontinuousAt_of_continuousAt_toReal
    (hu.1.quasiPlurisubharmonic.upperSemicontinuous x)
    (continuousAt_toReal_of_mem_continuityLocus hx)
    fun V hV hxV => hu.2 x V hV hxV

/-- **The hypothesis of CT22, Lemma 4.3, clause (ii) puts the point in the
continuity locus.**  Smoothness of the `toReal` chart expression near the chart
image transports back to continuity near the point itself. -/
theorem mem_continuityLocus_of_eventually_contDiffAt {u : M → EReal}
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hsm : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ (fun y' => (u (e.val.symm y')).toReal) y) :
    e.val.symm z ∈ continuityLocus u := by
  obtain ⟨V₀, hV₀sub, hV₀, hzV₀⟩ := mem_nhds_iff.mp hsm
  set V : Set (ComplexModel n) := V₀ ∩ e.val.target with hVdef
  have hV : IsOpen V := hV₀.inter e.val.open_target
  have hzV : z ∈ V := ⟨hzV₀, hz⟩
  refine ⟨e.val.source ∩ e.val ⁻¹' V, ?_, ?_, ?_⟩
  · exact e.val.continuousOn.isOpen_inter_preimage e.val.open_source hV
  · refine ⟨e.val.map_target hz, ?_⟩
    show e.val (e.val.symm z) ∈ V
    rw [e.val.right_inv hz]
    exact hzV
  · have hFcont : ContinuousOn (fun y' => (u (e.val.symm y')).toReal) V := by
      intro y hy
      have hy' : ContDiffAt ℝ ∞ (fun y' => (u (e.val.symm y')).toReal) y := hV₀sub hy.1
      exact hy'.continuousAt.continuousWithinAt
    have hecont : ContinuousOn e.val (e.val.source ∩ e.val ⁻¹' V) :=
      e.val.continuousOn.mono inter_subset_left
    refine ContinuousOn.congr (hFcont.comp hecont fun y hy => hy.2) ?_
    intro y hy
    show (u y).toReal = (u (e.val.symm (e.val y))).toReal
    rw [e.val.left_inv hy.1]

end Manifold

end

end SGPT.Foundations.Analysis.Pending.ThetaPshContinuityLocus
