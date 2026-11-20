import SGPT.PSH.AnalyticGeneratorAlgebra
import SGPT.Foundations.Analysis.Pending.PshConvexCone

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe v
variable {X : Type v} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- The original whole atlas form, multiplied by the actual real scalar. -/
def AtlasClosedRealOneOneForm.scale (c : ℝ) (θ : AtlasClosedRealOneOneForm A) :
    AtlasClosedRealOneOneForm A where
  coeff := fun i z => c • θ.coeff i z
  smooth := fun i => (θ.smooth i).const_smul c
  compatible := by
    intro i j z hz w
    exact congrArg (c • ·) (θ.compatible i j z hz w)
  closed := by
    intro i z hz
    change extDeriv (c • θ.coeff i) z = 0
    rw [extDeriv_smul, θ.closed i z hz, smul_zero]
  typeOneOne := by
    intro i z hz u w
    exact congrArg (c • ·) (θ.typeOneOne i z hz u w)

/-- Every original potential of the actual scaled form unscales on the SAME set. -/
theorem IsAtlasLocalPotential.unscale {θ : AtlasClosedRealOneOneForm A}
    {U : Set X} {g : X → ℝ} {c : ℝ} (hc : 0 < c)
    (hg : A.IsAtlasLocalPotential (θ.scale c) U g) :
    A.IsAtlasLocalPotential θ U (fun x => c⁻¹ * g x) := by
  refine ⟨hg.1, fun i => (hg.2.1 i).const_smul c⁻¹, ?_⟩
  intro i z hz
  have hD := (A.chart i).isOpen_inter_preimage_symm hg.1
  change smoothDDC (fun y => c⁻¹ • (g ∘ (A.chart i).symm) y) z = θ.coeff i z
  rw [smoothDDC_smul hD (hg.2.1 i) c⁻¹ hz, hg.2.2 i hz]
  change c⁻¹ • (c • θ.coeff i z) = θ.coeff i z
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- Main's genuine disc producer scales the SAME original connected PSH witnesses. -/
theorem IsPSHOn.pos_smul {u : X → EReal} {U : Set X}
    (hu : A.IsPSHOn u U) {c : ℝ} (hc : 0 < c) :
    A.IsPSHOn (fun x => (c : EReal) * u x) U := by
  intro x hx
  obtain ⟨i, hi, V, hV, hconn, hVe, hxV, hpsh⟩ := hu x hx
  refine ⟨i, hi, V, hV, hconn, hVe, hxV, hpsh.disc.const_mul hc, ?_⟩
  obtain ⟨y, hy, hfin⟩ := hpsh.nontrivial
  refine ⟨y, hy, ?_⟩
  exact (EReal.mul_ne_bot _ _).mpr
    ⟨Or.inl (EReal.coe_ne_bot c), Or.inr hfin,
      Or.inl (EReal.coe_ne_top c), Or.inl (EReal.coe_nonneg.mpr hc.le)⟩

/-- Universal testing survives positive real scaling for EVERY original potential. -/
theorem IsThetaPSH.pos_smul {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hu : A.IsThetaPSH θ u) {c : ℝ} (hc : 0 < c) :
    A.IsThetaPSH (θ.scale c) (fun x => (c : EReal) * u x) := by
  refine ⟨fun x => eReal_const_mul_ne_top hc.le (hu.1 x), ?_⟩
  intro U g hg
  have hp := (hu.2 U (fun x => c⁻¹ * g x) (hg.unscale hc)).pos_smul hc
  have heq : (fun x => (c : EReal) * (u x + ((c⁻¹ * g x : ℝ) : EReal))) =
      (fun x => (c : EReal) * u x + (g x : EReal)) := by
    funext x
    rw [EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr hc.le) (EReal.coe_ne_top c), ← EReal.coe_mul]
    congr 1
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [heq] at hp
  exact hp

/-- Manufacture the genuine global background; no local-QPSH certificate is supplied. -/
theorem IsQPSH.pos_smul {u : X → EReal} (hu : A.IsQPSH u)
    {c : ℝ} (hc : 0 < c) : A.IsQPSH (fun x => (c : EReal) * u x) := by
  obtain ⟨θ, hθ⟩ := hu
  exact ⟨θ.scale c, hθ.pos_smul hc⟩

/-- Original global QPSH AND actual rational analytic presentations scale together. -/
theorem IsQPSH.pos_rat_smul_analytic {u : X → EReal} (hu : A.IsQPSH u)
    (han : A.HasRationalAnalyticChartType u) {r : ℚ} (hr : 0 < r) :
    A.IsQPSH (fun x => ((r : ℝ) : EReal) * u x) ∧
      A.HasRationalAnalyticChartType (fun x => ((r : ℝ) : EReal) * u x) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  exact ⟨hu.pos_smul hrR, han.pos_rat_smul hr⟩

end SGPT.PSH.VariableComplexAtlas
