import SGPT.Unibranch.FNSLocal
import SGPT.Unibranch.FNAInterface

/-!
# From the Runge half of `[FN80, Thm. 5.3.1]` to the local extension theorem

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), Theorem 5.3.1 (`[FN80]`), for `thm:FN` (2) ⇒ (1)
(`appendix_unibranch.tex`).

`HartogsRungeOfEquations` is the first half of the proof of `[FN80, Thm. 5.3.1]` (the Hartogs
domain `Ω_φ = {φ(z) + log |w| < 0}` over `X` is Runge in `X × ℂ`, possibly after shrinking the
polydisc), in the setting of the `FNA.LocalFNExtensionOfEquations`. The second half of the
proof (`FNS.exists_ambient_psh_of_hartogsRunge`: Siu's Stein neighbourhood by nested monomial
polyhedra and the Hartogs step) turns it into the local extension theorem:

* `localFNExtensionOfEquations_of_hartogsRunge : HartogsRungeOfEquations → FNA.LocalFNExtensionOfEquations`;
* `localFNExtension_of_hartogsRunge : HartogsRungeOfEquations → FNA.LocalFNExtension`,

which the bridge turns into `thm:FN` on complex spaces.
-/

set_option autoImplicit false

noncomputable section

open Set
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNS

/-- **`[FN80, Thm. 5.3.1]`, first half (Runge), local form for global equations.** For
`h₁, …, h_m` holomorphic near the closed polydisc `Δ̄(a, r)`, vanishing at `a`, and `φ` weakly
plurisubharmonic on their common zero set `X` in `Δ(a, r)`, the Hartogs domain `Ω_φ` over
`X ∩ Δ(a, r')` is Runge in `(X ∩ Δ(a, r')) × ℂ` for some smaller polydisc `Δ(a, r')`. -/
def HartogsRungeOfEquations : Prop :=
  ∀ (n : ℕ) (a : ComplexModel n) (r : Fin n → ℝ) (V : Set (ComplexModel n)) (m : ℕ)
    (h : Fin m → ComplexModel n → ℂ) (φ : ComplexModel n → EReal),
    (∀ i, 0 < r i) → IsOpen V → FNA.closedPolydisc a r ⊆ V → (∀ l, DifferentiableOn ℂ (h l) V) →
    (∀ l, h l a = 0) →
    FNL.IsWeaklyPSHOn {z | z ∈ FNA.polydisc a r ∧ ∀ l, h l z = 0} φ →
    ∃ r' : Fin n → ℝ, (∀ i, 0 < r' i) ∧ (∀ i, r' i ≤ r i) ∧
      HartogsRunge {z | z ∈ FNA.polydisc a r' ∧ ∀ l, h l z = 0} φ

/-- The Runge half implies the local extension theorem for global equations. -/
theorem localFNExtensionOfEquations_of_hartogsRunge (H : HartogsRungeOfEquations) :
    FNA.LocalFNExtensionOfEquations := by
  intro n a r V m h φ hr hV hrV hh ha hφ
  obtain ⟨r', hr'0, hr'r, hR⟩ := H n a r V m h φ hr hV hrV hh ha hφ
  set X : Set (ComplexModel n) := {z | z ∈ FNA.polydisc a r ∧ ∀ l, h l z = 0} with hXdef
  set O : Set (ComplexModel n) := FNA.polydisc a r' with hOdef
  have hO : IsOpen O := FNA.isOpen_polydisc a r'
  have hOr : O ⊆ FNA.polydisc a r := fun z hz i => (hz i).trans_le (hr'r i)
  have hOV : O ⊆ V := fun z hz =>
    hrV (FNA.polydisc_subset_closedPolydisc a r (hOr hz))
  have hXO : ∀ z ∈ O, z ∈ X ↔ ∀ l, h l z = 0 := fun z hz =>
    ⟨fun hzX => hzX.2, fun h0 => ⟨hOr hz, h0⟩⟩
  have hXOeq : X ∩ O = {z | z ∈ FNA.polydisc a r' ∧ ∀ l, h l z = 0} := by
    ext z
    exact ⟨fun ⟨hzX, hzO⟩ => ⟨hzO, hzX.2⟩, fun ⟨hzO, h0⟩ => ⟨⟨hOr hzO, h0⟩, hzO⟩⟩
  have haO : a ∈ X ∩ O := by
    refine ⟨⟨fun i => by simpa using hr i, ha⟩, fun i => by simpa using hr'0 i⟩
  obtain ⟨D, hD, haD, ψ, hψ, hψφ⟩ := exists_ambient_psh_of_hartogsRunge hO
    (fun l => (hh l).mono hOV) hXO hφ (by rwa [hXOeq]) haO
  exact ⟨D, hD, haD, ψ, hψ, fun x hxD hxr hx0 => hψφ x ⟨⟨hxr, hx0⟩, hxD⟩⟩

/-- The Runge half implies the local extension theorem, hence (`FNA.fornaessNarasimhan`)
`thm:FN` on every complex space. -/
theorem localFNExtension_of_hartogsRunge (H : HartogsRungeOfEquations) : FNA.LocalFNExtension :=
  FNA.localFNExtension_of_equations (localFNExtensionOfEquations_of_hartogsRunge H)

end SGPT.Unibranch.FNS
