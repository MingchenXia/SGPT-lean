import SGPT.Hodge.StarGlobal
import SGPT.BDivisor.BlowupModelSystem

/-!
# Finite dimensionality of `H^{1,1}(X, ℝ)`

Blueprint `claude-hodge`, node `claude-hodge:thm-finite-dimensional`; route of
Xia, *Foundations of pluripotential theory*, q07, after `def:real-one-one-cohomology` ("every class
contains exactly one harmonic form, so `H^{1,1}(X, ℝ)` is isomorphic to the space of harmonic real
`(1,1)`-forms; in particular it is finite dimensional").  Used without proof in Xia,
*Singularities in global pluripotential theory*, `chap:bdiv` (`def:nefb`, `prop:dscontbdiv`).

* `SGPT.Hodge.finiteDimensional_realBottChern`: for a compact connected complex manifold `X`
  carrying a Kähler form, the real Bott–Chern space `H^{1,1}(X, ℝ)` is finite dimensional
  (`finiteDimensional_realBottChern_of_coclosed` of `SGPT.Hodge.Finite`, with the coclosedness
  `SGPT.Hodge.constantTraceCoclosed` of `SGPT.Hodge.StarGlobal`).  No measurable structure is
  assumed: the Borel structure is chosen inside the proof.
* `SGPT.Hodge.finiteDimensional_realBottChern_of_nonempty`: the same from
  `Nonempty (KahlerBackground n X)`.
* `SGPT.Hodge.finiteDimensional_realBottChern_blowupModel`: on every model of the book's blow-up
  model system of a compact connected Kähler manifold (blow-up models are compact, connected and
  Kähler), so that the hypotheses `[FiniteDimensional ℝ (RealBottChern (m + 1) π.1.carrier)]` of
  `SGPT.BDivisor` can be discharged.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Hodge

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Finite dimensionality of `H^{1,1}(X, ℝ)`** (`claude-hodge:thm-finite-dimensional`) for a
compact connected Kähler manifold. -/
theorem finiteDimensional_realBottChern [CompactSpace M] [ConnectedSpace M]
    (w : KahlerBackground n M) : FiniteDimensional ℝ (RealBottChern n M) := by
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  exact finiteDimensional_realBottChern_of_coclosed w (constantTraceCoclosed w)

/-- Finite dimensionality of `H^{1,1}(X, ℝ)` for a compact connected manifold admitting a Kähler
form. -/
theorem finiteDimensional_realBottChern_of_nonempty [CompactSpace M] [ConnectedSpace M]
    (hK : Nonempty (KahlerBackground n M)) : FiniteDimensional ℝ (RealBottChern n M) :=
  finiteDimensional_realBottChern hK.some

/-- **Finite dimensionality on the book's models**: for `X` compact connected Kähler, every model
`Y` of the blow-up model system (`def:modif`) has finite-dimensional `H^{1,1}(Y, ℝ)`. -/
theorem finiteDimensional_realBottChern_blowupModel {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X]
    (hK : Nonempty (KahlerBackground n X)) (π : (SGPT.BDivisor.ModelSystem.blowup n X).Model) :
    FiniteDimensional ℝ (RealBottChern n π.1.carrier) := by
  obtain ⟨hc, hKY⟩ := SGPT.BDivisor.Modification.compactSpace_and_kahler_of_isBlowupSequence hK π.2
  have := hc
  have := SGPT.BDivisor.Modification.IsBlowupModel.connectedSpace π.2
  exact finiteDimensional_realBottChern_of_nonempty hKY

end SGPT.Hodge
