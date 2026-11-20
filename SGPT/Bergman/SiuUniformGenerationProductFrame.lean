import SGPT.Bergman.SiuUniformGenerationLocalFrame
import SGPT.PSH.SiuL2Correction

/-!
# Product holomorphicity for the actual local frames

The pullback of an actual holomorphic base section is holomorphic on the
product in the original atlas-coefficient sense.  Dividing a product section
by an actual nonzero local frame is holomorphic in every product chart.
These bridges connect the newly constructed frames to the existing scalar
domain-gluing correction theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Bundle Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.PSH.LineBundleMetric
open SGPT.NAPotential.NAGaga

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {E : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- The actual product pullback of a native holomorphic base section. -/
theorem isHolomorphicProdSectionOn_baseSection
    {U : Set X} (hU : IsOpen U) (s : (x : X) → E.Fiber x)
    (hs : IsHolomorphicSectionOn (n := n) E.Fiber s U) :
    IsHolomorphicProdSectionOn E (fun q : X × unitDisc => s q.1) (Prod.fst ⁻¹' U) := by
  intro q hq e he
  let := e.property
  filter_upwards [((hU.inter e.val.open_baseSet).preimage continuous_fst).mem_nhds ⟨hq, he⟩]
    with q' hq'
  have hsm := (hs q'.1 hq'.1).mdifferentiableAt (hU.mem_nhds hq'.1)
  have hcoef := (Trivialization.mdifferentiableAt_section_iff
    (IB := 𝓘(ℂ, ComplexModel n)) e.val s hq'.2).mp hsm
  have hfst := (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)).mdifferentiableAt
    (by simp) (x := q')
  have hcomp := hcoef.comp q' hfst
  refine MDifferentiableAt.congr_of_eventuallyEq hcomp ?_
  filter_upwards [(e.val.open_baseSet.preimage continuous_fst).mem_nhds hq'.2] with q'' hq''
  exact Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hq'' _

/-- Coordinates in an actual nonzero base frame remain holomorphic for a
product section, including product sections that vary with the disc variable. -/
theorem differentiableOn_prodSectionCoordinate
    (d : ComplexChart (n + 1) (X × unitDisc)) {U : Set X} {V : Set (X × unitDisc)}
    (hU : IsOpen U) (_hV : IsOpen V) (s : (x : X) → E.Fiber x)
    (hs : IsHolomorphicSectionOn (n := n) E.Fiber s U) (hs0 : ∀ x ∈ U, s x ≠ 0)
    (S : (q : X × unitDisc) → E.Fiber q.1) (hS : IsHolomorphicProdSectionOn E S V) :
    DifferentiableOn ℂ
      (fun w => sectionCoordinate s ((d.val.symm w).1) (S (d.val.symm w)))
      (d.val.target ∩ d.val.symm ⁻¹' ((Prod.fst ⁻¹' U) ∩ V)) := by
  have hsprod := isHolomorphicProdSectionOn_baseSection hU s hs
  intro z hz
  let e := prefFrame E (d.val.symm z).1
  have he : (d.val.symm z).1 ∈ e.val.baseSet := mem_prefFrame E _
  have hsd : DifferentiableAt ℂ
      (fun w => e.val.continuousLinearMapAt ℂ (d.val.symm w).1 (s (d.val.symm w).1)) z :=
    differentiableAt_comp_symm_of_holomorphicAt d hz.1
      (hsprod _ hz.2.1 e he)
  have hSd : DifferentiableAt ℂ
      (fun w => e.val.continuousLinearMapAt ℂ (d.val.symm w).1 (S (d.val.symm w))) z :=
    differentiableAt_comp_symm_of_holomorphicAt d hz.1 (hS _ hz.2.2 e he)
  have hden := atlasCoefficient_ne_zero_of_section_ne_zero s e he (hs0 _ hz.2.1)
  have hdiff : DifferentiableAt ℂ (fun w =>
      e.val.continuousLinearMapAt ℂ (d.val.symm w).1 (S (d.val.symm w)) /
        e.val.continuousLinearMapAt ℂ (d.val.symm w).1 (s (d.val.symm w).1)) z := by
    simpa only [div_eq_mul_inv] using hSd.fun_mul (hsd.fun_inv hden)
  have hev : (fun w => sectionCoordinate s (d.val.symm w).1 (S (d.val.symm w))) =ᶠ[𝓝 z]
      fun w => e.val.continuousLinearMapAt ℂ (d.val.symm w).1 (S (d.val.symm w)) /
        e.val.continuousLinearMapAt ℂ (d.val.symm w).1 (s (d.val.symm w).1) := by
    filter_upwards [(d.val.isOpen_inter_preimage_symm
      ((hU.inter e.val.open_baseSet).preimage continuous_fst)).mem_nhds
        ⟨hz.1, hz.2.1, he⟩] with w hw
    exact sectionCoordinate_eq_inFrame s e hw.2.2 (hs0 _ hw.2.1) _
  exact (hdiff.congr_of_eventuallyEq hev).differentiableWithinAt

end SGPT.Bergman.SiuUniformGeneration
