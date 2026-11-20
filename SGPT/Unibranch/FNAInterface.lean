import SGPT.Unibranch.FNLBasic
import SGPT.Unibranch.FNRAnalyticHull

/-!
# The local Fornæss--Narasimhan extension theorem: interface

Source: J. E. Fornæss, R. Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), Theorem 5.3.1 (`[FN80]`), cited by SGPT `thm:FN`
(`appendix_unibranch.tex`) for the implication (2) ⇒ (1) on singular complex spaces.

`[FN80]` prove `WP(X) = P(X)`: "the theorem is local, so we may suppose that `X` is a closed
complex subvariety of `Δⁿ`"; for `φ ∈ WP(X)` they produce a plurisubharmonic function `λ` on an
open set `D` with `X ⊆ D ⊆ Δⁿ` and `λ|_X = φ`. `LocalFNExtension` is this local statement, in
the form used by the bridge to complex spaces (`FNABridge.lean`, `FNATheorem.lean`):

* `X ⊆ ℂⁿ` is a closed analytic subset of the open polydisc `Δ(a, r)` centred at a point
  `a ∈ X` (it lies in the polydisc and is cut out near every point of the polydisc by finitely
  many holomorphic functions, `FNR.HasLocalEquationsOn`);
* `φ ∈ WP(X)` (`FNL.IsWeaklyPSHOn`: upper semicontinuous on `X` with values in `[-∞, ∞)`, and
  `φ ∘ f` subharmonic or `≡ -∞` for every holomorphic disc `f : Δ → X`);
* conclusion: on a neighbourhood `W` of `a` there is an ambient function `ψ` satisfying the
  disc criterion (`SGPT.Foundations.Analysis.DiscPshOn`: plurisubharmonic, `≡ -∞` allowed) with
  `ψ = φ` on `X ∩ W`.

This file contains only the statement (a `Prop`); its proof is the work of lane FNS (Siu step
via nested monomial polyhedra and the Hartogs step). The bridge proves `thm:FN` from it.

`LocalFNExtensionOfEquations` is the same statement for `X` the common zero set, in an open
polydisc, of finitely many functions holomorphic near the closed polydisc (the setting of the
Siu step); it implies `LocalFNExtension` (`localFNExtension_of_equations`), by Cartan's
Theorem A on boxes (`FNR.exists_equations_near_box`). Either may be proved.
-/

set_option autoImplicit false

namespace SGPT.Unibranch.FNA

open SGPT.Foundations.Analysis.FirstPass

/-- The open polydisc `Δ(a, r) = {z : ∀ i, |zᵢ - aᵢ| < rᵢ}` of `ℂⁿ` (FNR's spelling). -/
def polydisc {n : ℕ} (a : ComplexModel n) (r : Fin n → ℝ) : Set (ComplexModel n) :=
  {z | ∀ i, ‖z i - a i‖ < r i}

theorem isOpen_polydisc {n : ℕ} (a : ComplexModel n) (r : Fin n → ℝ) : IsOpen (polydisc a r) :=
  FNR.isOpen_polydisc a r

/-- **`[FN80]` Theorem 5.3.1, local form** (to be proved by lane FNS).
Let `X` be a closed analytic subset of an open polydisc `Δ(a, r) ⊆ ℂⁿ` with centre `a ∈ X`
and let `φ ∈ WP(X)`. Then near `a` the function `φ` is the restriction to `X` of an ambient
function satisfying the disc criterion (plurisubharmonic, possibly `≡ -∞`). -/
def LocalFNExtension : Prop :=
  ∀ (n : ℕ) (X : Set (ComplexModel n)) (a : ComplexModel n) (r : Fin n → ℝ)
    (φ : ComplexModel n → EReal),
    (∀ i, 0 < r i) → X ⊆ polydisc a r → FNR.HasLocalEquationsOn X (polydisc a r) → a ∈ X →
    FNL.IsWeaklyPSHOn X φ →
    ∃ W : Set (ComplexModel n), IsOpen W ∧ a ∈ W ∧ ∃ ψ : ComplexModel n → EReal,
      SGPT.Foundations.Analysis.DiscPshOn ψ W ∧ ∀ x ∈ X ∩ W, ψ x = φ x

/-- The closed polydisc `{z : ∀ i, |zᵢ - aᵢ| ≤ rᵢ}`. -/
def closedPolydisc {n : ℕ} (a : ComplexModel n) (r : Fin n → ℝ) : Set (ComplexModel n) :=
  {z | ∀ i, ‖z i - a i‖ ≤ r i}

/-- **`[FN80]` Theorem 5.3.1, local form, for global equations.** Let `h₁, …, h_m` be holomorphic
near the closed polydisc `Δ̄(a, r)`, vanishing at `a`, and let `φ` be weakly plurisubharmonic on
their common zero set `X` in the open polydisc `Δ(a, r)`. Then near `a` the function `φ` is the
restriction to `X` of an ambient function satisfying the disc criterion. -/
def LocalFNExtensionOfEquations : Prop :=
  ∀ (n : ℕ) (a : ComplexModel n) (r : Fin n → ℝ) (V : Set (ComplexModel n)) (m : ℕ)
    (h : Fin m → ComplexModel n → ℂ) (φ : ComplexModel n → EReal),
    (∀ i, 0 < r i) → IsOpen V → closedPolydisc a r ⊆ V → (∀ l, DifferentiableOn ℂ (h l) V) →
    (∀ l, h l a = 0) →
    FNL.IsWeaklyPSHOn {z | z ∈ polydisc a r ∧ ∀ l, h l z = 0} φ →
    ∃ W : Set (ComplexModel n), IsOpen W ∧ a ∈ W ∧ ∃ ψ : ComplexModel n → EReal,
      SGPT.Foundations.Analysis.DiscPshOn ψ W ∧
        ∀ x ∈ W, x ∈ polydisc a r → (∀ l, h l x = 0) → ψ x = φ x

theorem polydisc_subset_closedPolydisc {n : ℕ} (a : ComplexModel n) (r : Fin n → ℝ) :
    polydisc a r ⊆ closedPolydisc a r :=
  fun _ hz i => (hz i).le

/-- **Global equations near a half polydisc** (Cartan's Theorem A on the closed polydisc of half
the radii, `FNR.exists_equations_near_box`): a closed analytic subset `X` of `Δ(a, r)` is, on an
open `V ⊇ Δ̄(a, r/2)`, the common zero set of finitely many functions holomorphic on `V`. -/
theorem exists_equations_half {n : ℕ} {X : Set (ComplexModel n)} {a : ComplexModel n}
    {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hloc : FNR.HasLocalEquationsOn X (polydisc a r)) :
    ∃ V : Set (ComplexModel n), IsOpen V ∧ closedPolydisc a (fun i => r i / 2) ⊆ V ∧
      ∃ (m : ℕ) (h : Fin m → ComplexModel n → ℂ), (∀ l, DifferentiableOn ℂ (h l) V) ∧
        ∀ z ∈ V, (z ∈ X ↔ ∀ l, h l z = 0) := by
  set C : Fin n → Set ℂ := fun i => Metric.closedBall (a i) (r i / 2)
  have hC : SGPT.GAGA.Core.Box.IsBox C :=
    ⟨fun i => isCompact_closedBall _ _, fun i => convex_closedBall _ _⟩
  have hCeq : SGPT.GAGA.Core.Box.boxSet C = closedPolydisc a (fun i => r i / 2) := by
    ext z
    simp only [SGPT.GAGA.Core.Box.mem_boxSet, C, Metric.mem_closedBall, dist_eq_norm,
      closedPolydisc, Set.mem_ofPred_eq]
  have hCΔ : SGPT.GAGA.Core.Box.boxSet C ⊆ polydisc a r := by
    rw [hCeq]
    intro z hz i
    have := hz i
    have := hr i
    simp only at *
    linarith
  obtain ⟨V, hV, hCV, -, μ, hμ, f, hf, hfX⟩ :=
    FNR.exists_equations_near_box hC (isOpen_polydisc a r) hCΔ hloc
  set eqv := Fintype.equivFin μ
  refine ⟨V, hV, hCeq ▸ hCV, Fintype.card μ, fun l => f (eqv.symm l), fun l => hf _, ?_⟩
  intro z hz
  rw [hfX z hz]
  constructor
  · intro hk l
    exact hk _
  · intro hl k
    have := hl (eqv k)
    simpa using this

theorem half_radii_pos {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) : ∀ i, 0 < r i / 2 :=
  fun i => by have := hr i; positivity

theorem center_mem_polydisc {n : ℕ} (a : ComplexModel n) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    a ∈ polydisc a r :=
  fun i => by simpa using hr i

/-- The global-equations form of the local [FN80] theorem implies the form with local
equations (Cartan's Theorem A on a closed polydisc of half the radii). -/
theorem localFNExtension_of_equations (H : LocalFNExtensionOfEquations) : LocalFNExtension := by
  intro n X a r φ hr hXΔ hloc haX hWP
  obtain ⟨V, hV, hCV, m, h, hh, hmemX⟩ := exists_equations_half hr hloc
  have hr' := half_radii_pos hr
  have hsub : polydisc a (fun i => r i / 2) ⊆ V :=
    (polydisc_subset_closedPolydisc a _).trans hCV
  have haV : a ∈ V := hsub (center_mem_polydisc a hr')
  have hX' : {z | z ∈ polydisc a (fun i => r i / 2) ∧ ∀ l, h l z = 0} ⊆ X := by
    rintro z ⟨hz, hz0⟩
    exact (hmemX z (hsub hz)).mpr hz0
  obtain ⟨W, hW, haW, ψ, hψ, hψφ⟩ := H n a (fun i => r i / 2) V m h φ hr' hV hCV hh
    ((hmemX a haV).mp haX) (hWP.mono hX')
  refine ⟨W ∩ polydisc a (fun i => r i / 2), hW.inter (isOpen_polydisc _ _),
    ⟨haW, center_mem_polydisc a hr'⟩, ψ, hψ.mono Set.inter_subset_left, ?_⟩
  rintro x ⟨hxX, hxW, hxΔ⟩
  exact hψφ x hxW hxΔ ((hmemX x (hsub hxΔ)).mp hxX)

end SGPT.Unibranch.FNA
