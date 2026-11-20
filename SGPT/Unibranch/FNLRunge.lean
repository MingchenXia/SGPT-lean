import SGPT.Unibranch.FNLRestrict
import SGPT.Unibranch.FNRLocal
import SGPT.Unibranch.FNRPshHull

/-!
# FN80 Lemma 5.2: sublevel sets of weakly strongly psh functions are Runge

Source: `[FN80]` (Fornæss–Narasimhan, Math. Ann. 248 (1980)), Lemma 5.2 (stated there for
`λ = 2` sheets and proved for every `λ` by induction on `λ`), used for SGPT `thm:FN`.

**Lemma 5.2.** Let `X` be a pure `k`-dimensional closed subvariety of `Δⁿ` such that the
projection `π : X → Δᵏ` is a branched covering, and let `φ ∈ WSP(X)`. Then `{φ < 0}` is Runge
in `X`: the polynomially convex hull of every compact `K ⊆ {φ < 0}` lies in `{φ < 0}`.

Formalization (`runge_sublevel`): `Δ = Δ(a, r)` a polydisc of `ℂⁿ`, `π` the projection to the first
`k` coordinates, `X ⊆ Δ` with local holomorphic equations on `Δ`
(`FNR.HasLocalEquationsOn`, i.e. `X` is a closed analytic subset of `Δ`), `X → D` a finite
branched covering (`IsBranchedCovering`, which contains pure dimensionality) over an open
`D ⊇ π(Δ)`, `φ ∈ WSP(X)`.  Hulls are polynomial hulls (`polyHull`, Codex/FNR); by lane FNR they
lie in `X` (`polyHull_subset_of_localEquations_polydisc`), i.e. they are the hulls in `X`.

The proof is `[FN80]`'s: strong induction on the number of sheets; Rossi's local maximum
principle localizes a failure at a point `p₀` of the hull; if the fibre through `p₀`
has other points, a small polydisc around `p₀` carries a covering with fewer sheets
(`exists_restrict_pdisc`), contradiction; the set `Y` of points with one-point fibres is
handled by the plurisubharmonic collapse function (`collapse`, replacing `[FN80]`'s
`log ∑ |f_j|²`); finally at a point of `Y` the trace `tr φ ∘ π` (Lemma 5.1) contradicts the
Runge property of sublevel sets of psh functions on polydiscs.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Unibranch.E2Nov16FNPolynomialPolyhedron SGPT.Unibranch.FNR

variable {n k : ℕ}

theorem hasLocalEquationsOn_inter {X Ω Ω' : Set (ComplexModel n)} (h : HasLocalEquationsOn X Ω)
    (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) : HasLocalEquationsOn (X ∩ Ω') Ω' := by
  intro x hx
  obtain ⟨W, hW, hxW, N, g, hg, hgX⟩ := h x (hsub hx)
  refine ⟨W ∩ Ω', hW.inter hΩ', ⟨hxW, hx⟩, N, g, fun i => (hg i).mono inter_subset_left, ?_⟩
  intro y hy
  rw [← hgX y hy.1]
  exact ⟨fun h => h.1, fun h => ⟨h, hy.2⟩⟩

theorem IsWeaklyPSHOn.add_const {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    (hφ : IsWeaklyPSHOn X φ) (b : ℝ) : IsWeaklyPSHOn X (fun y => φ y + (b : EReal)) :=
  (hφ.add (IsWeaklyPSHOn.of_plurisubharmonicOn (plurisubharmonicOn_quadratic le_rfl 0 b)
    (subset_univ X))).congr fun y _ => by simp

/-- `WSP + WP ⊆ WSP`. -/
theorem IsWeaklyStrictlyPSHOn.add {X : Set (ComplexModel n)} {φ u : ComplexModel n → EReal}
    (hφ : IsWeaklyStrictlyPSHOn X φ) (hu : IsWeaklyPSHOn X u) :
    IsWeaklyStrictlyPSHOn X (fun y => φ y + u y) := by
  intro x hx
  obtain ⟨U, hU, hxU, c, hc, h⟩ := hφ x hx
  refine ⟨U, hU, hxU, c, hc, (h.add (hu.mono inter_subset_left)).congr fun y _ => ?_⟩
  simp only
  rw [add_assoc, add_assoc, add_comm (u y)]

theorem IsWeaklyStrictlyPSHOn.add_const {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    (hφ : IsWeaklyStrictlyPSHOn X φ) (b : ℝ) :
    IsWeaklyStrictlyPSHOn X (fun y => φ y + (b : EReal)) :=
  hφ.add (IsWeaklyPSHOn.of_plurisubharmonicOn (plurisubharmonicOn_quadratic le_rfl 0 b)
    (subset_univ X) |>.congr fun y _ => by simp)

theorem EReal.add_neg_coe_lt {x : EReal} (hb : x ≠ ⊥) (ht : x ≠ ⊤) {t : ℝ} (htp : 0 < t) :
    x + ((-t : ℝ) : EReal) < x := by
  have hx : x = (x.toReal : EReal) := (EReal.coe_toReal ht hb).symm
  rw [hx, ← EReal.coe_add, EReal.coe_lt_coe_iff]
  linarith

theorem EReal.nsmul_le_self {x : EReal} (hx : x ≤ 0) {m : ℕ} (hm : 1 ≤ m) : m • x ≤ x := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · simp
    · rw [succ_nsmul]
      calc m • x + x ≤ 0 + x := add_le_add_left ((ih hm').trans hx) x
        _ = x := zero_add x

theorem EReal.nsmul_neg {x : EReal} (hx : x < 0) {m : ℕ} (hm : 1 ≤ m) : m • x < 0 :=
  lt_of_le_of_lt (EReal.nsmul_le_self hx.le hm) hx

variable {X : Set (ComplexModel n)} {D : Set (ComplexModel k)} {deg : ℕ} {δ : ComplexModel k → ℂ}

namespace IsBranchedCovering

/-- The collapse function is bounded above by `c log (λ² R² + 1)`. -/
theorem collapse_le {π : ComplexModel n →L[ℂ] ComplexModel k}
    (hX : IsBranchedCovering X π D deg δ) {c : ℝ} (hc : 0 < c) {R : ℝ}
    (hR : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ R) {z : ComplexModel k} (hz : z ∈ D) :
    collapse X π δ c z ≤ ((c * Real.log (deg ^ 2 * R ^ 2 + 1) : ℝ) : EReal) := by
  classical
  rw [collapse, PshCodimTwoExtension.extension_eq_uscRegularization]
  refine (uscRegularization_le_localSup _ (hX.isOpen_base.mem_nhds hz)).trans
    (iSup₂_le fun y hy => ?_)
  by_cases hyA : y ∈ {w | δ w = 0}
  · simp only [if_pos hyA]; exact bot_le
  · simp only [if_neg hyA]
    exact hX.log_fibreSpread_le hc hR hy hyA

end IsBranchedCovering

end SGPT.Unibranch.FNL
