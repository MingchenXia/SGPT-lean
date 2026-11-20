import SGPT.Trace.BertiniFamilyCanonicalModel
import SGPT.Trace.BertiniPencilNormal
import SGPT.Trace.BertiniNativeChartCofactor

/-! Native complex smoothness of ACTUAL moving original family coefficient factors. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal

private theorem actualScalarDifferential_in_chart {m : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    (e : ComplexChart m Y) (q : Y) (hq : q ∈ e.val.source)
    (f : Y → ℂ) (hf : HolomorphicAt m f q)
    (u : TangentSpace 𝓘(ℂ, ComplexModel m) q) :
    nativeScalarDifferential f q u = fderiv ℂ (f ∘ e.val.symm) (e.val q)
      (nativeOriginalChartTangentEquiv e q hq u) := by
  have heq : f =ᶠ[𝓝 q] ((f ∘ e.val.symm) ∘ e.val) := by
    filter_upwards [e.val.open_source.mem_nhds hq] with y hy
    simp only [Function.comp_apply, e.val.left_inv hy]
  have hG : MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ℂ) (f ∘ e.val.symm) (e.val q) :=
    (eventually_differentiableAt_comp_symm e hq hf).self_of_nhds.mdifferentiableAt
  have he := mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel m)) e.property hq
  have hcomp := mfderiv_comp q hG he
  rw [mfderiv_eq_fderiv] at hcomp
  rw [nativeOriginalChartTangentEquiv_apply]
  unfold nativeScalarDifferential
  rw [heq.mfderiv_eq, hcomp]
  rfl

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))

theorem familyScalarDifferential_in_chart :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart n (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (hq : q ∈ e.val.source) (u : TangentSpace 𝓘(ℂ, ComplexModel n) q),
      nativeScalarDifferential (scalarParameter p i a v U) q u =
        fderiv ℂ (scalarParameter p i a v U ∘ e.val.symm) (e.val q)
          (nativeOriginalChartTangentEquiv e q hq u) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq u
  exact actualScalarDifferential_in_chart e q hq _
    (holomorphicAt_scalarParameter p i a v U p.contMDiff hsm q) u

theorem contMDiffAt_familyParameterPartial :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart n (familyIncidence p i a v U)) (k : Fin n)
      (q : familyIncidence p i a v U) (_hq : q ∈ e.val.source),
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
        (chartDeriv e (EuclideanSpace.single k 1) (scalarParameter p i a v U)) q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e k q hq
  exact contMDiffAt_of_eventually_mdifferentiableAt (holomorphicAt_chartDeriv hq
    (holomorphicAt_scalarParameter p i a v U p.contMDiff hsm q))

theorem exists_familyParameterChartPartial_ne_zero :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart n (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (_hq : q ∈ e.val.source),
      ∃ k : Fin n, chartDeriv e (EuclideanSpace.single k 1) (scalarParameter p i a v U) q ≠ 0 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q hq
  obtain ⟨nu, hnu⟩ := surjective_mfderiv_scalarParameter p i a v U p.contMDiff hsm q (1 : ℂ)
  have hnorm : fderiv ℂ (scalarParameter p i a v U ∘ e.val.symm) (e.val q)
      (nativeOriginalChartTangentEquiv e q hq nu) = 1 := by
    exact (actualScalarDifferential_in_chart e q hq _
      (holomorphicAt_scalarParameter p i a v U p.contMDiff hsm q) nu).symm.trans hnu
  by_contra hn
  push Not at hn
  have hD : (fderiv ℂ (scalarParameter p i a v U ∘ e.val.symm) (e.val q)).toLinearMap = 0 := by
    apply (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.ext
    intro k
    have hk := hn k
    change fderiv ℂ (scalarParameter p i a v U ∘ e.val.symm) (e.val q)
      (EuclideanSpace.single k 1) = 0 at hk
    change fderiv ℂ (scalarParameter p i a v U ∘ e.val.symm) (e.val q)
      ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis k) = 0
    change fderiv ℂ (scalarParameter p i a v U ∘ e.val.symm) (e.val q)
      ((EuclideanSpace.basisFun (Fin n) ℂ) k) = 0
    rw [EuclideanSpace.basisFun_apply]
    exact hk
  have hz := DFunLike.congr_fun hD (nativeOriginalChartTangentEquiv e q hq nu)
  change fderiv ℂ (scalarParameter p i a v U ∘ e.val.symm) (e.val q)
    (nativeOriginalChartTangentEquiv e q hq nu) = 0 at hz
  exact one_ne_zero (hnorm.symm.trans hz)

theorem contMDiffAt_familyVerticalPartial (eT : ComplexChart 1 U) (eX : ComplexChart n X)
    (j : Fin (N + 1)) (m : Fin n) (q : familyIncidence p i a v U)
    (ht : q.val.1 ∈ eT.val.source) (hx : q.val.2 ∈ eX.val.source)
    (hpj : p q.val.2 ∈ (affineChart j).source) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun r : familyIncidence p i a v U => chartDeriv eX (EuclideanSpace.single m 1)
        (nativeBertiniLocalEquation p i (a - r.val.1.val 0 • v) j) r.val.2) q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let e := productComplexChart eT eX
  have hqe : q.val ∈ e.val.source := by
    simpa only [e, productComplexChart, prodChart_source] using
      (show q.val ∈ eT.val.source ×ˢ eX.val.source from ⟨ht, hx⟩)
  have hg := holomorphicAt_chartDeriv (v := prodModelEquiv 1 n (0, EuclideanSpace.single m (1 : ℂ))) hqe
    (holomorphicAt_pencilLocalEquation p i a v U p.contMDiff j hpj)
  have hpartial := contMDiffAt_of_eventually_mdifferentiableAt hg
  have hc := hpartial.comp q ((contMDiff_familyInclusion p i a v U p.contMDiff hsm).contMDiffAt)
  apply hc.congr_of_eventuallyEq
  have hnearT := (contMDiff_familyProjection p i a v U p.contMDiff hsm).continuous.continuousAt.eventually
    (eT.val.open_source.mem_nhds ht)
  have hnearX := (familyNativeXMap p i a v U hsm).contMDiff.continuous.continuousAt.eventually
    (eX.val.open_source.mem_nhds hx)
  have hnearj := (p.contMDiff.continuous.comp (familyNativeXMap p i a v U hsm).contMDiff.continuous).continuousAt.eventually
    ((affineChart j).open_source.mem_nhds hpj)
  filter_upwards [hnearT, hnearX, hnearj] with r hrT hrX hrj
  exact (chartDeriv_product_vertical eT eX hrT hrX
    (holomorphicAt_pencilLocalEquation p i a v U p.contMDiff j hrj)
    (EuclideanSpace.single m 1)).symm

theorem contMDiffAt_familyVerticalPartial_inv (eT : ComplexChart 1 U) (eX : ComplexChart n X)
    (j : Fin (N + 1)) (m : Fin n) (q : familyIncidence p i a v U)
    (ht : q.val.1 ∈ eT.val.source) (hx : q.val.2 ∈ eX.val.source)
    (hpj : p q.val.2 ∈ (affineChart j).source)
    (hm : chartDeriv eX (EuclideanSpace.single m 1)
      (nativeBertiniLocalEquation p i (a - q.val.1.val 0 • v) j) q.val.2 ≠ 0) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun r : familyIncidence p i a v U => (chartDeriv eX (EuclideanSpace.single m 1)
        (nativeBertiniLocalEquation p i (a - r.val.1.val 0 • v) j) r.val.2)⁻¹) q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact (contMDiffAt_familyVerticalPartial p i a v U hsm eT eX j m q ht hx hpj).inv₀ hm

theorem contMDiffAt_familyXJacobianEntry :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart n (familyIncidence p i a v U)) (eX : ComplexChart n X)
      (k m : Fin n) (q : familyIncidence p i a v U)
      (_hq : q ∈ e.val.source) (_hx : q.val.2 ∈ eX.val.source),
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
        (fun r => (fderiv ℂ (coordinateMap (familyNativeXMap p i a v U hsm) e eX)
          (e.val r) (EuclideanSpace.single k 1)) m) q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e eX k m q hq hx
  have hD : ContDiffAt ℂ ∞
      (fderiv ℂ (coordinateMap (familyNativeXMap p i a v U hsm) e eX)) (e.val q) :=
    (coordinateMap_contDiffAt (familyNativeXMap p i a v U hsm).contMDiff e eX
      (mem_coordinateDomain hq hx)).fderiv_right (by simp)
  have hentry := (EuclideanSpace.proj (𝕜 := ℂ) m).contDiff.contDiffAt.comp (e.val q)
    (hD.clm_apply (contDiffAt_const (c := EuclideanSpace.single k (1 : ℂ))))
  exact hentry.contMDiffAt.comp q
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property) hq)

end SGPT.Trace.BertiniFamilyCanonical
