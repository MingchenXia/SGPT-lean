import SGPT.Projective.OkounkovOriginalPerturbValueInclusion
import SGPT.Okounkov.ValGen2Hausdorff

/-! SAME original normalized raw points, all sufficiently large degrees, genuine residue absorption.
Blueprint: okounkov-original-perturb-raw-upper.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalPerturbRawUpper
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValGen2
open scoped Topology Pointwise
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance perturbRawUpperTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance perturbRawUpperCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance perturbRawUpperManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- ENTIRE original raw point inclusion, all large ORIGINAL degrees, with literal floor normalization. -/
theorem eventually_rawPoints_subset_scaled_unitPerturbPolytope {L T A : X.Modules}
    (a : LineBundleAtlas L) (aT : LineBundleAtlas T) (aA : LineBundleAtlas A)
    (P : SGPT.LineBundle.AmplePolarization f A) (H : SchemeLineBundleMetric f n E L)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {c : X} (hc : IsNonnegAt v c)
    (q p₀ : ℕ) (hq : 0<q) (hp₀ : 0<p₀)
    (r : ∀ k, LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∀ᶠ k : ℕ in atTop,
      (fun x => (k:ℝ)⁻¹ • euclideanCast n x) ''
        AlgebraicValuation.twistedMultiplierValues f n E v c k (r k) φ ⊆
      (((k/q:ℕ):ℝ)/(k:ℝ)) • poly
        (fun g => AlgebraicValuation.twistedMultiplierValues
          (T:=SheafOfModules.unit X.ringCatSheaf)
          (L:=bundleTensor (bundleTensorPower L q) (bundleTensorPower A (P.power*p₀)))
          f n E v c g (((OkoNS.perturbAtlas a aA q (P.power*p₀)).tensorPower g).tensorPower 1)
          (fun x => (q:EReal)*φ x)) (k/q) := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨B,hB,hvalues⟩ := OriginalPerturbValueInclusion.exists_uniform_perturb_multiplier_value_inclusions
    f n E a aT aA P q hq
  filter_upwards [eventually_ge_atTop (q*B)] with k hk
  let g := k/q
  let residue : Fin q := ⟨k%q,Nat.mod_lt k hq⟩
  have hgB : B≤g := (Nat.le_div_iff_mul_le hq).mpr (by simpa only [Nat.mul_comm] using hk)
  have hg : 0<g := hB.trans_le hgB
  have heq : q*g+residue.val=k := Nat.div_add_mod k q
  have hinc := hvalues p₀ hp₀ g hgB residue H φ hφ v c hc (heq.symm ▸ r k)
  have hraw (j : ℕ) (hj : j=k) :
      AlgebraicValuation.twistedMultiplierValues f n E v c j (hj.symm ▸ r k) φ =
      AlgebraicValuation.twistedMultiplierValues f n E v c k (r k) φ := by
    subst j
    rfl
  rw [hraw _ heq] at hinc
  rintro _ ⟨x,hx,rfl⟩
  have hx' := hinc hx
  apply mem_smul_set.mpr
  refine ⟨(g:ℝ)⁻¹ • euclideanCast n x,subset_convexHull ℝ _ (mem_image_of_mem _ hx'),?_⟩
  rw [smul_smul]
  congr 1
  have hgR : (g:ℝ)≠0 := by exact_mod_cast hg.ne'
  field_simp [hgR]
  rfl
end SGPT.Okounkov.OriginalPerturbRawUpper
