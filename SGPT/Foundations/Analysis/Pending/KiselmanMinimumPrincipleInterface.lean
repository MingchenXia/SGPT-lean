import SGPT.Foundations.Analysis.FirstPass.Subgeodesics
import SGPT.Foundations.Analysis.Pending.KiselmanMinimumPrincipleProof

set_option autoImplicit false

/-!
# Kiselman's minimum principle (filed as an interface, now proved)

Xia's Proposition 4.1.2 (`xia-sgpt:page-0149`) derives

  `inf_{t in (0,1)} u_t in PSH(X, theta)`

for a subgeodesic from one classical input, which he states as his
Proposition 1.2.8 (**Kiselman's principle**, `xia-sgpt:page-0029`) and cites
to Demailly, *Complex Analytic and Differential Geometry*, Theorem I.7.5
(`[Dem12b, Theorem 7.5]` in Xia's bibliography):

> Let `Ω ⊆ C^m × C^n` be a pseudoconvex domain such that, for every
> `z ∈ C^m`, the slice `Ω_z = {w : (z,w) ∈ Ω}` has the form `E + i R^n`.  Let
> `φ ∈ PSH(Ω)` be independent of the imaginary part of the `C^n` variable and
> let `Ω₀` be the projection of `Ω` to `C^m`.  Then
> `ψ(z) = inf_{w ∈ Ω_z} φ(z, w)` is either identically `-∞` or lies in
> `PSH(Ω₀)`.

This module records the single instance the subgeodesic argument consumes:
`n = 1`, the tube slice is the normalized time strip
`FirstPass.complexTimeStrip`, and the base is an arbitrary open subset of the
model space.  Two deliberate shape choices:

* The conclusion is the unconditional `PlurisubharmonicOn`, with no
  `ψ ≢ -∞` side condition.  This project's `PlurisubharmonicOn` permits the
  value `⊥` (see `Plurisubharmonic.lean`), so Xia's dichotomy collapses into
  the single conclusion: the `ψ ≡ -∞` branch also satisfies it.
* The base `U` is an arbitrary open set, not a pseudoconvex domain.
  `PlurisubharmonicOn` is a local property, and every point of `U` has a ball
  neighbourhood `B ⊆ U` for which `B ×ˢ complexTimeStrip` is convex, hence
  pseudoconvex; so the open-set form follows from the source statement by
  restriction.  (The proof below does not even need that reduction: the
  disc criterion only tests discs inside `U`.)

**Status.**  Filed in run 0093 as a named classical input with an explicit
`sorry`; since run 0095 it is a theorem.  The proof -- the classical
holomorphic-disc argument, in this project's extended-real disc language -- is
`Pending.KiselmanMinimumPrincipleProof.plurisubharmonicOn_iInf_slices`, whose
statement is identical; the declaration below is kept, with its statement
unchanged, so that its consumer and the audit keep their names.

The consumer is `Pending.SubgeodesicInfimumThetaPsh`.  The other half of Xia's
assertion -- that the slice infimum is finite somewhere, and that it lies below
both prescribed endpoints -- is PROVED, without this interface, in
`Pending.SubgeodesicInfimum`.
-/

open Filter Set

namespace SGPT.Foundations.Analysis.Pending.KiselmanMinimumPrinciple

open FirstPass

noncomputable section

/-- **Kiselman's minimum principle, strip instance** (proved in
`Pending.KiselmanMinimumPrincipleProof`).  If `Φ` is plurisubharmonic on
`U ×ˢ complexTimeStrip` and depends on the time variable only through its real
part, then the pointwise infimum of its real-time slices is plurisubharmonic
on `U`.

Source: Demailly, *Complex Analytic and Differential Geometry*, Theorem I.7.5,
as quoted in Xia, SGPT, Proposition 1.2.8 (`xia-sgpt:page-0029`). -/
theorem plurisubharmonicOn_iInf_slices {m : ℕ} {U : Set (ComplexModel m)}
    (hU : IsOpen U) {Φ : ComplexModel m × ℂ → EReal}
    (hΦ : PlurisubharmonicOn Φ (U ×ˢ complexTimeStrip))
    (hinv : ∀ (y : ComplexModel m) (τ σ : ℂ), τ.re = σ.re → Φ (y, τ) = Φ (y, σ)) :
    PlurisubharmonicOn
      (fun y : ComplexModel m => ⨅ t : ↥(Ioo (0 : ℝ) 1), Φ (y, ((t : ℝ) : ℂ))) U := by
  exact KiselmanMinimumPrincipleProof.plurisubharmonicOn_iInf_slices hU hΦ hinv

end

end SGPT.Foundations.Analysis.Pending.KiselmanMinimumPrinciple
