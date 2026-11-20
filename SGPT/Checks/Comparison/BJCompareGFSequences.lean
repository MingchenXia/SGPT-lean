import SGPT.Checks.Comparison.BJCanonicalModuleTopology
import Mathlib.Algebra.Module.Rat

/-!
# Decreasing sequences of GF functions in classes `L + ε_k H`

The Boucksom–Jonsson half of `lma:varphian` (`chapter_NApotential.tex`, *The algebraic setting*).
The book's proof shows that `v ↦ -k⁻¹ v(𝓘(kφ))` lies in `H^gf_ℚ((L + (b/k) H)^An)` and that along
`k = 2^j` these functions decrease to `φ^An` (`eq:varphiAnalt`); then `φ^An ∈ PSH(L^An)` "by
definition".  The definitional step is `isModuleTopologyPSH_of_antitone_seq`: the limit of a
decreasing sequence of rational GF functions in classes `L + ε_k H`, `ε_k → 0` in `ℚ`, is a psh
metric on `L^An` as soon as it is not identically `-∞`.  The analytic input (Siu's uniform global
generation and the algebraic models of `𝓘(kφ)`) is not part of this file.

## Main results

* `tendsto_numericalClass_add_smul`: `c₁(L + ε_k H) → c₁(L)` in the module topology.
* `isModuleTopologyPSH_of_antitone_seq`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ.Printed

open AlgebraicGeometry CategoryTheory Filter Topology
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- `c₁(L + ε_k H) → c₁(L)` in the canonical module topology when `ε_k → 0`. -/
theorem tendsto_numericalClass_add_smul {L H : RationalPicardSpace X} {ε : ℕ → ℚ}
    (hε : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k => numericalClass p (L + ε k • H)) atTop
      (@nhds _ (numericalModuleTopology p) (numericalClass p L)) := by
  let : TopologicalSpace (NativeRealNumericalClasses.Space p) := numericalModuleTopology p
  have := ModuleTopology.continuousSMul ℝ (NativeRealNumericalClasses.Space p)
  have := ModuleTopology.continuousAdd ℝ (NativeRealNumericalClasses.Space p)
  have hsmul : Tendsto (fun k => (ε k : ℝ) • numericalClass p H) atTop
      (𝓝 ((0 : ℝ) • numericalClass p H)) := hε.smul_const _
  rw [zero_smul] at hsmul
  have hsum := (tendsto_const_nhds (x := numericalClass p L)).add hsmul
  rw [add_zero] at hsum
  refine hsum.congr fun k => ?_
  rw [map_add, numericalClass_rat_smul, Rat.cast_smul_eq_qsmul ℝ]

/-- **Decreasing sequences of GF functions.**  If `D_k ∈ H^gf_ℚ((L + ε_k H)^An)` with rational
`ε_k → 0`, the functions `D_k` decrease, and their infimum is not identically `-∞`, then the
infimum lies in `PSH(L^An)`. -/
theorem isModuleTopologyPSH_of_antitone_seq {L H : RationalPicardSpace X}
    (D : ℕ → RationalGFPackage X) {ε : ℕ → ℚ}
    (hε : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0))
    (hclass : ∀ k, (D k).picardClass = L + ε k • H)
    (hanti : ∀ v, Antitone (fun k => (D k).eval p v))
    (hne : ∃ v, (⨅ k, (D k).eval p v) ≠ ⊥) :
    IsModuleTopologyPSH.{u} p L (fun v => ⨅ k, (D k).eval p v) := by
  let J : Type u := ULift.{u} ℕ
  let hdir : IsDirectedOrder J :=
    ⟨fun a b => ⟨⟨max a.down b.down⟩, ULift.down_le.mp (le_max_left a.down b.down),
      ULift.down_le.mp (le_max_right a.down b.down)⟩⟩
  have hdown : Tendsto (fun j : J => j.down) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨⟨b⟩, fun a ha => ULift.down_le.mpr ha⟩
  let E : DecreasingGFNet.{u} p :=
    { I := J
      preorder := inferInstance
      nonempty := inferInstance
      directed := hdir
      term := fun j => D j.down
      decreasing := fun v a b hab => hanti v (ULift.down_le.mpr hab) }
  refine ⟨hne, E, ?_, fun v => ?_⟩
  · change Tendsto (fun j : J => (D j.down).numericalClass p) atTop _
    have h := tendsto_numericalClass_add_smul p (L := L) (H := H) hε
    refine (h.comp hdown).congr fun j => ?_
    change numericalClass p (L + ε j.down • H) = numericalClass p (D j.down).picardClass
    rw [hclass]
  · change Tendsto (fun j : J => (D j.down).eval p v) atTop _
    exact (tendsto_atTop_iInf (hanti v)).comp hdown

end SGPT.NAPotential.BJ.Printed
