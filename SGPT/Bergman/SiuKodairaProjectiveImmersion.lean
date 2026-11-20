import SGPT.Bergman.SiuKodairaProjectiveMap
import SGPT.Bergman.SiuKodairaChartDerivative
import SGPT.NAPotential.GAGAMultSiuGerms
import Mathlib.Algebra.BigOperators.Fin

/-!
# Actual native immersion of the original full-section map

Every section ratio factors through the literal affine coordinates of the
original projective map. Their true derivatives detect the actual nonzero
chart vectors already separated by the constructed original sections.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:section-map`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.NAPotential.GAGAMult

variable {n N : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The literal affine linear function read from a homogeneous linear form. -/
def affineLinearFunction (a : Fin (N + 1) → ℂ) (i : Fin (N + 1)) (z : ComplexModel N) : ℂ :=
  a i + ∑ k : Fin N, a (i.succAbove k) * z k

theorem differentiable_affineLinearFunction (a : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    Differentiable ℂ (affineLinearFunction a i) := by
  intro z
  have hconst : DifferentiableAt ℂ (fun _ : ComplexModel N => a i) z := differentiableAt_const _
  apply hconst.add
  exact DifferentiableAt.fun_sum fun k _ =>
    (show DifferentiableAt ℂ (fun _ : ComplexModel N => a (i.succAbove k)) z from
      differentiableAt_const _).fun_mul (EuclideanSpace.proj (𝕜 := ℂ) k).differentiableAt

/-- Actual homogeneous division is exactly the corresponding affine linear function. -/
theorem affineLinearFunction_affineRatio (a v : Fin (N + 1) → ℂ)
    (i : Fin (N + 1)) (hi : v i ≠ 0) :
    affineLinearFunction a i (affineRatio i v) = (∑ j, a j * v j) / v i := by
  rw [Fin.sum_univ_succAbove (fun j => a j * v j) i, add_div, Finset.sum_div]
  rw [mul_div_assoc, div_self hi, mul_one]
  simp only [affineLinearFunction, affineRatio_apply]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

variable (E : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- Every actual section ratio factors through the actual affine projective map. -/
theorem sectionRatio_factorization
    (b : Module.Basis (Fin (N + 1)) ℂ (HolomorphicSections (n := n) E.Fiber))
    (hgen : ∀ x : X, ∃ j : Fin (N + 1), b j x ≠ 0)
    (e : AtlasFrame E) (i : Fin (N + 1)) {x : X} (hx : x ∈ e.val.baseSet)
    (hi : sectionVector E b e x i ≠ 0) (s : HolomorphicSections (n := n) E.Fiber) :
    e.val.continuousLinearMapAt ℂ x (s x) / sectionVector E b e x i =
      affineLinearFunction (b.repr s) i
        (affineChart i (sourceNativeFiniteSectionProjectiveMap E b hgen x)) := by
  rw [(nativeSectionMap_affineChart E b hgen e i hx hi).2,
    affineLinearFunction_affineRatio (b.repr s) (sectionVector E b e x) i hi]
  rw [basis_coefficient_expansion E b s e x]
  rfl

/-- Actual first derivatives of section ratios prove injectivity of the
actual affine coordinate derivative. -/
theorem nativeBasisSectionMap_chart_fderiv_injective
    (b : Module.Basis (Fin (N + 1)) ℂ (HolomorphicSections (n := n) E.Fiber))
    (hgen : ∀ x : X, ∃ j : Fin (N + 1), b j x ≠ 0)
    (hsep : ∀ (p : X) (e : AtlasFrame E), p ∈ e.val.baseSet →
      ∀ c : ComplexChart n X, p ∈ c.val.source → ∀ v : ComplexModel n, v ≠ 0 →
        ∃ s : HolomorphicSections (n := n) E.Fiber, s p = 0 ∧
          fderiv ℂ (fun z => e.val.continuousLinearMapAt ℂ (c.val.symm z) (s (c.val.symm z)))
            (c.val p) v ≠ 0)
    (p : X) (e : AtlasFrame E) (he : p ∈ e.val.baseSet)
    (c : ComplexChart n X) (hc : p ∈ c.val.source) (i : Fin (N + 1))
    (hi : sectionVector E b e p i ≠ 0) :
    Function.Injective (fderiv ℂ
      (fun z => affineChart i (sourceNativeFiniteSectionProjectiveMap E b hgen (c.val.symm z)))
      (c.val p)) := by
  let := e.property
  let F := sourceNativeFiniteSectionProjectiveMap E b hgen
  let q := c.val p
  let Q : ComplexModel n → ComplexModel N := fun z => affineChart i (F (c.val.symm z))
  let den : ComplexModel n → ℂ := fun z =>
    e.val.continuousLinearMapAt ℂ (c.val.symm z) (b i (c.val.symm z))
  have hcp : c.val.symm q = p := c.val.left_inv hc
  have hsrc : F p ∈ (affineChart i).source := (nativeSectionMap_affineChart E b hgen e i he hi).1
  have hF : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) F p :=
    (sourceNativeFiniteSectionProjectiveMap_contMDiff E b hgen p).mdifferentiableAt (by simp)
  have hsy : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.val.symm q :=
    mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) c.property (c.val.map_source hc)
  have hFcp : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) F (c.val.symm q) :=
    hcp.symm ▸ hF
  have hdcp : MDifferentiableAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) (affineChart i)
      (F (c.val.symm q)) := by
    simpa only [hcp] using (contMDiffAt_affineChart i hsrc).mdifferentiableAt (by simp)
  have hQd : DifferentiableAt ℂ Q q :=
    mdifferentiableAt_iff_differentiableAt.mp (hdcp.comp q (hFcp.comp q hsy))
  have hdenhol := holomorphicAt_coef_of_contMDiff e.val (b i).contMDiff he
  have hdd : DifferentiableAt ℂ den q := differentiableAt_chart_of_holomorphicAt c hc hdenhol
  have hd0 : den q ≠ 0 := by
    dsimp only [den]
    rw [hcp]
    exact hi
  have hi' : e.val.continuousLinearMapAt ℂ p (b i p) ≠ 0 := hi
  have hne : ∀ᶠ x in 𝓝 p, e.val.continuousLinearMapAt ℂ x (b i x) ≠ 0 :=
    hdenhol.self_of_nhds.continuousAt.eventually (isOpen_ne.mem_nhds hi')
  have hdom : ∀ᶠ z in 𝓝 q, c.val.symm z ∈ e.val.baseSet ∧
      e.val.continuousLinearMapAt ℂ (c.val.symm z) (b i (c.val.symm z)) ≠ 0 := by
    have hloc : ∀ᶠ x in 𝓝 (c.val.symm q), x ∈ e.val.baseSet ∧
        e.val.continuousLinearMapAt ℂ x (b i x) ≠ 0 := by
      simpa only [hcp] using
        ((show ∀ᶠ x in 𝓝 p, x ∈ e.val.baseSet from e.val.open_baseSet.mem_nhds he).and hne)
    exact (c.val.continuousAt_symm (c.val.map_source hc)).eventually hloc
  change Function.Injective (fderiv ℂ Q q)
  have hker : ∀ v : ComplexModel n, fderiv ℂ Q q v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨s, hsp, hsder⟩ := hsep p e he c hc v hv0
    let num : ComplexModel n → ℂ := fun z =>
      e.val.continuousLinearMapAt ℂ (c.val.symm z) (s (c.val.symm z))
    have hnumhol := holomorphicAt_coef_of_contMDiff e.val s.contMDiff he
    have hnd : DifferentiableAt ℂ num q := differentiableAt_chart_of_holomorphicAt c hc hnumhol
    have hn0 : num q = 0 := by dsimp only [num]; rw [hcp, hsp, map_zero]
    have hfactor : (fun z => num z / den z) =ᶠ[𝓝 q]
        fun z => affineLinearFunction (b.repr s) i (Q z) := by
      filter_upwards [hdom] with z hz
      exact sectionRatio_factorization E b hgen e i hz.1 hz.2 s
    have hP := differentiable_affineLinearFunction (b.repr s) i (Q q)
    have hratio0 : fderiv ℂ (fun z => num z / den z) q v = 0 := by
      rw [hfactor.fderiv_eq]
      change fderiv ℂ (affineLinearFunction (b.repr s) i ∘ Q) q v = 0
      rw [fderiv_comp q hP hQd]
      simp only [ContinuousLinearMap.comp_apply, hv, map_zero]
    have hquot : fderiv ℂ (fun z => num z / den z) q v =
        (den q)⁻¹ * fderiv ℂ num q v := by
      simp only [div_eq_mul_inv]
      rw [fderiv_fun_mul hnd (hdd.fun_inv hd0)]
      simp only [add_apply, smul_apply, smul_eq_mul, hn0, zero_mul, zero_add]
    have hmul : (den q)⁻¹ * fderiv ℂ num q v = 0 := hquot.symm.trans hratio0
    exact hsder ((mul_eq_zero.mp hmul).resolve_left (inv_ne_zero hd0))
  intro v w hvw
  have hz : fderiv ℂ Q q (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hker (v - w) hz)

/-- The original section map has injective native manifold differential.
The native preferred projective chart is one of the actual affine charts. -/
theorem nativeBasisSectionMap_mfderiv_injective
    (b : Module.Basis (Fin (N + 1)) ℂ (HolomorphicSections (n := n) E.Fiber))
    (hgen : ∀ x : X, ∃ j : Fin (N + 1), b j x ≠ 0)
    (hsep : ∀ (p : X) (e : AtlasFrame E), p ∈ e.val.baseSet →
      ∀ c : ComplexChart n X, p ∈ c.val.source → ∀ v : ComplexModel n, v ≠ 0 →
        ∃ s : HolomorphicSections (n := n) E.Fiber, s p = 0 ∧
          fderiv ℂ (fun z => e.val.continuousLinearMapAt ℂ (c.val.symm z) (s (c.val.symm z)))
            (c.val p) v ≠ 0)
    (p : X) :
    Function.Injective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      (sourceNativeFiniteSectionProjectiveMap E b hgen) p) := by
  let F := sourceNativeFiniteSectionProjectiveMap E b hgen
  let c := complexChartAt (n := n) p
  let e := prefFrame E p
  let := e.property
  let i := chartIndex (F p)
  have hc : p ∈ c.val.source := mem_complexChartAt_source p
  have he : p ∈ e.val.baseSet := mem_prefFrame E p
  have hsrc : F p ∈ (affineChart i).source := mem_affineChart_chartIndex (F p)
  have hi : sectionVector E b e p i ≠ 0 := by
    have h := hsrc
    change sourceNativeFiniteSectionProjectiveMap E b hgen p ∈ (affineChart i).source at h
    rw [nativeSectionMap_frame E b hgen e p he] at h
    exact (mk_mem_affineChart_source_iff i (sectionVector_ne_zero E b hgen e p he)).mp h
  have hF := (sourceNativeFiniteSectionProjectiveMap_contMDiff E b hgen p).mdifferentiableAt (by simp)
  rw [mfderiv_eq_fderiv_complexChartAt hF]
  change Function.Injective (fderiv ℂ (fun z => affineChart i (F (c.val.symm z))) (c.val p))
  exact nativeBasisSectionMap_chart_fderiv_injective E b hgen hsep p e he c hc i hi

end SGPT.Bergman.SiuKodaira
