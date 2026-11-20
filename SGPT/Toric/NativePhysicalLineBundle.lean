/- Canonical staging of the immutable whole-original toric Bergman proof.
   Exact retained fragments/providers are recorded in fragment-provider-map.json.gz. -/
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import SGPT.Bergman.SourceNativeFirstChernForm
import SGPT.Bergman.SourceSmoothMetricPolynomialBound
import SGPT.Bergman.SourceTensorDictionary
import SGPT.Toric.BigToric2MetricExistence
import SGPT.Toric.BigToric2Orbits
import SGPT.Toric.BigToricMetric
import SGPT.Toric.GeodesicAction
import SGPT.Toric.Toric5Multiplier
import SGPT.Foundations.Analysis.Pending.NaturalHermitianKahlerVolumeCalibration


/- BEGIN SGPT.Bergman.SourceInvariantDensityMeasure; source SHA256 2a75243811f72143d7a8ef12a2e9f0fc597ebd75d3b96d8ed249e9993bf28479 -/
section ToricCanonicalFragment000

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.NativeSingularPhi
open Set MeasureTheory
open scoped ENNReal

/-- Actual change of variables proves preservation of a density measure.
This retains all infinite values and requires no prescribed norm/basis. -/
theorem measurePreserving_withDensity_of_invariant
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {f : Y → Y}
    (hf : MeasurePreserving f μ μ) {ρ : Y → ENNReal} (hρ : Measurable ρ)
    (hinv : ∀ x, ρ (f x) = ρ x) :
    MeasurePreserving f (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  have h := hf.setLIntegral_comp_preimage hs hρ
  simpa only [hinv] using h

end SGPT.Bergman.NativeSingularPhi

end
end ToricCanonicalFragment000
/- END SGPT.Bergman.SourceInvariantDensityMeasure -/

/- BEGIN SGPT.Bergman.SourceNativeRightUnitSections; source SHA256 4cc04058c2ee4d76f945c8a5f6707b5e697b3ac8aea0625b6a23343fd88f6e68 -/
section ToricCanonicalFragment008

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.NativeRightUnit
open Set Bundle Topology Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators Classical ContDiff Manifold TensorProduct
universe u v
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The true right-unit physical fiber isometry, on the actual original
literal tensor fiber, without an incoming compatibility certificate. -/
def nativeRightUnitFiberIsometry (T : HermitianHolomorphicLineBundle.{u,v} n M) (x : M) :
    (tensor T unit).Fiber x ≃ₗᵢ[ℂ] T.Fiber x :=
  TensorProduct.ridIsometry ℂ (T.Fiber x)

/-- The actual product-atlas coefficient is exactly the SAME original
T coefficient of the physical right-unit image, proved on pure tensors. -/
theorem nativeRightUnit_coordinate {T : HermitianHolomorphicLineBundle.{u,v} n M}
    (f : AtlasFrame T) {x : M} (hx : x ∈ f.val.baseSet)
    (t : (tensor T unit).Fiber x) :
    ((tensorAtlasFrame f unitAtlasFrame).val ⟨x, t⟩).2 =
      (f.val ⟨x, nativeRightUnitFiberIsometry T x t⟩).2 := by
  let := f.property
  let : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℂ) := ⟨by rfl⟩
  have h : tensorCoordinate T.Fiber (Bundle.Trivial M ℂ)
      f.val (Bundle.Trivial.trivialization M ℂ) x =
      (f.val.linearMapAt ℂ x).comp (TensorProduct.rid ℂ (T.Fiber x)).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    change tensorCoordinate T.Fiber (Bundle.Trivial M ℂ)
      f.val (Bundle.Trivial.trivialization M ℂ) x (a ⊗ₜ[ℂ] b) =
      f.val.linearMapAt ℂ x (TensorProduct.rid ℂ (T.Fiber x) (a ⊗ₜ[ℂ] b))
    simp [tensorCoordinate_tmul, TensorProduct.rid_tmul, map_smul, smul_eq_mul, mul_comm]
  change tensorCoordinate T.Fiber (Bundle.Trivial M ℂ)
    f.val (Bundle.Trivial.trivialization M ℂ) x t = _
  rw [h]
  exact congrFun (Trivialization.coe_linearMapAt_of_mem f.val hx)
    (nativeRightUnitFiberIsometry T x t)

/-- EVERY actual tensor-unit holomorphic section has a genuine original
holomorphic image; the local coordinate identity proves holomorphy. -/
def nativeRightUnitSection (T : HermitianHolomorphicLineBundle.{u,v} n M)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor T unit).Fiber) :
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) T.Fiber where
  toFun := fun x => nativeRightUnitFiberIsometry T x (s x)
  contMDiff_toFun := by
    intro x
    let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber x, inferInstance⟩
    let := f.property
    let q := tensorAtlasFrame f unitAtlasFrame
    let := q.property
    have hx : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber x
    apply (f.val.contMDiffAt_section_iff hx).mpr
    have hs := (q.val.contMDiffAt_section_iff
      (show x ∈ q.val.baseSet from ⟨hx, mem_univ x⟩)).mp (s.contMDiff x)
    apply hs.congr_of_eventuallyEq
    filter_upwards [f.val.open_baseSet.mem_nhds hx] with y hy
    exact (nativeRightUnit_coordinate f hy (s y)).symm

/-- The actual inverse sends every original section to its tensor with
one; holomorphy is proved in the actual tensor frames. -/
def nativeRightUnitSectionInv (T : HermitianHolomorphicLineBundle.{u,v} n M)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) T.Fiber) :
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor T unit).Fiber where
  toFun := fun x => (nativeRightUnitFiberIsometry T x).symm (s x)
  contMDiff_toFun := by
    intro x
    let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber x, inferInstance⟩
    let := f.property
    let q := tensorAtlasFrame f unitAtlasFrame
    let := q.property
    have hx : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber x
    apply (q.val.contMDiffAt_section_iff
      (show x ∈ q.val.baseSet from ⟨hx, mem_univ x⟩)).mpr
    have hs := (f.val.contMDiffAt_section_iff hx).mp (s.contMDiff x)
    apply hs.congr_of_eventuallyEq
    filter_upwards [f.val.open_baseSet.mem_nhds hx] with y hy
    rw [nativeRightUnit_coordinate f hy, LinearIsometryEquiv.apply_symm_apply]

/-- Genuine BOTH-direction complex linear equivalence of the independent
full original H0 carriers, including empty H0 spaces and base dimension0. -/
def nativeRightUnitSectionsEquiv (T : HermitianHolomorphicLineBundle.{u,v} n M) :
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor T unit).Fiber ≃ₗ[ℂ]
      SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) T.Fiber where
  toFun := nativeRightUnitSection T
  invFun := nativeRightUnitSectionInv T
  left_inv s := by ext x; exact (nativeRightUnitFiberIsometry T x).symm_apply_apply (s x)
  right_inv s := by ext x; exact (nativeRightUnitFiberIsometry T x).apply_symm_apply (s x)
  map_add' s t := by ext x; exact map_add (nativeRightUnitFiberIsometry T x) (s x) (t x)
  map_smul' a s := by ext x; exact map_smul (nativeRightUnitFiberIsometry T x) a (s x)

theorem nativeRightUnitSectionsEquiv_norm (T : HermitianHolomorphicLineBundle.{u,v} n M)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (tensor T unit).Fiber)
    (x : M) : ‖nativeRightUnitSectionsEquiv T s x‖ = ‖s x‖ :=
  (nativeRightUnitFiberIsometry T x).norm_map (s x)

theorem nativeRightUnitSectionsEquiv_symm_norm (T : HermitianHolomorphicLineBundle.{u,v} n M)
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) T.Fiber)
    (x : M) : ‖(nativeRightUnitSectionsEquiv T).symm s x‖ = ‖s x‖ :=
  (nativeRightUnitFiberIsometry T x).symm.norm_map (s x)

end SGPT.Bergman.NativeRightUnit

end
end ToricCanonicalFragment008
/- END SGPT.Bergman.SourceNativeRightUnitSections -/

/- BEGIN SGPT.Toric.ToricCartierTransition; source SHA256 0a639a59628ccac9f9fbad3ee778632680b6092579132c4c91106961ac05d4e0 -/
section ToricCanonicalFragment009

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Literal original Cartier frame-change exponent in the SAME actual
native ray basis. -/
def toricCartierTransitionExponent (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) (j : Fin n) : ℤ :=
  intPairing (toricCartierDatum D v - toricCartierDatum D w)
    (polytopeToricRayGenerator γ hs v j)

def toricCartierLaurentModel (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) (z : ComplexModel n) : ℂ :=
  ∏ j : Fin n, z j ^ toricCartierTransitionExponent D v w j

/-- The actual frame coefficient transformation c_w=g_vw*c_v, read in
the ORIGINAL v chart. Its regularity on ALL actual overlaps is proved
from original prime-divisor incidence and both Cartier equations. -/
def toricCartierTransition (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) (p : PolytopeToricVariety γ hs) : ℂ :=
  toricCartierLaurentModel D v w (originalPolytopeNativeModelChart γ hs v p)

theorem toricCartierTransitionExponent_eq_zero_of_coord_zero
    (D : ToricDivisor γ hs) (v w : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source)
    (j : Fin n) (hz : originalPolytopeNativeModelChart γ hs v p j = 0) :
    toricCartierTransitionExponent D v w j = 0 := by
  let ρ := polytopeToricRay γ hs v j
  have hpρ : p ∈ toricPrimeDivisor ρ := ⟨v, j, rfl, hv, hz⟩
  obtain ⟨k, hk, _⟩ := (mem_toricPrimeDivisor_iff hw ρ).mp hpρ
  have hray : polytopeToricRay γ hs w k = ρ := Subtype.ext hk
  have hmv : intPairing (toricCartierDatum D v) ρ.val = -D ρ :=
    toricCartierDatum_pairing D v j
  have hmw : intPairing (toricCartierDatum D w) ρ.val = -D ρ := by
    calc
      _ = intPairing (toricCartierDatum D w) (polytopeToricRayGenerator γ hs w k) :=
        congrArg (intPairing (toricCartierDatum D w)) hk.symm
      _ = -D (polytopeToricRay γ hs w k) := toricCartierDatum_pairing D w k
      _ = -D ρ := congrArg (fun r : PolytopeToricRays γ hs => -D r) hray
  change intPairing (toricCartierDatum D v - toricCartierDatum D w) ρ.val = 0
  rw [intPairing_sub, hmv, hmw, sub_self]

theorem toricChart_coord_ne_zero_of_transitionExponent_ne_zero
    (D : ToricDivisor γ hs) (v w : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source)
    (j : Fin n) (he : toricCartierTransitionExponent D v w j ≠ 0) :
    originalPolytopeNativeModelChart γ hs v p j ≠ 0 := by
  intro hz
  exact he (toricCartierTransitionExponent_eq_zero_of_coord_zero D v w hv hw j hz)

theorem toricCartierTransition_ne_zero (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    toricCartierTransition D v w p ≠ 0 := by
  unfold toricCartierTransition toricCartierLaurentModel
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases he : toricCartierTransitionExponent D v w j = 0
  · rw [he, zpow_zero]
    exact one_ne_zero
  · exact zpow_ne_zero _ (toricChart_coord_ne_zero_of_transitionExponent_ne_zero D v w hv hw j he)

end SGPT.Toric

end
end ToricCanonicalFragment009
/- END SGPT.Toric.ToricCartierTransition -/

/- BEGIN SGPT.Toric.ToricCartierTransitionRegularity; source SHA256 854a6747b1b4f552e845ade6039abceb6fd21abfbc5fd3ada72b3449e502bc5c -/
section ToricCanonicalFragment010

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

theorem analyticAt_toricCartierLaurentModel_of_overlap (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    AnalyticAt ℂ (toricCartierLaurentModel D v w)
      (originalPolytopeNativeModelChart γ hs v p) := by
  unfold toricCartierLaurentModel
  apply Finset.analyticAt_fun_prod
  intro j _
  by_cases he : toricCartierTransitionExponent D v w j = 0
  · simp only [he, zpow_zero]
    exact analyticAt_const
  · exact ((EuclideanSpace.proj (𝕜 := ℂ) j).analyticAt _).zpow
      (toricChart_coord_ne_zero_of_transitionExponent_ne_zero D v w hv hw j he)

theorem continuousOn_toricCartierTransition (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) :
    ContinuousOn (toricCartierTransition D v w)
      ((originalPolytopeNativeModelChart γ hs v).source ∩
        (originalPolytopeNativeModelChart γ hs w).source) := by
  intro p hp
  exact (analyticAt_toricCartierLaurentModel_of_overlap D v w hp.1 hp.2).continuousAt.comp_continuousWithinAt
    (((originalPolytopeNativeModelChart γ hs v).continuousOn p hp.1).mono inter_subset_left)

/-- The same true transition is holomorphic in EVERY actual original
complex chart, on its entire original overlap. Coordinate zeroes are
allowed, because their exponents were proved zero from Cartier geometry. -/
theorem differentiableOn_toricCartierTransition_comp_symm (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) (e : ComplexChart n (PolytopeToricVariety γ hs)) :
    DifferentiableOn ℂ (fun z => toricCartierTransition D v w (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹'
        ((originalPolytopeNativeModelChart γ hs v).source ∩
          (originalPolytopeNativeModelChart γ hs w).source)) := by
  intro z hz
  have hchart := (differentiableOn_vertexChart_comp_symm (hs := hs) v e).differentiableAt
    ((isOpen_chartOverlap (hs := hs) v e).mem_nhds ⟨hz.1, hz.2.1⟩)
  exact ((analyticAt_toricCartierLaurentModel_of_overlap D v w hz.2.1 hz.2.2).differentiableAt.comp
    z hchart).differentiableWithinAt

theorem contDiffOn_toricCartierTransition_comp_symm (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) (e : ComplexChart n (PolytopeToricVariety γ hs)) :
    ContDiffOn ℂ ∞ (fun z => toricCartierTransition D v w (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹'
        ((originalPolytopeNativeModelChart γ hs v).source ∩
          (originalPolytopeNativeModelChart γ hs w).source)) := by
  exact contDiffOn_of_differentiableOn_complex
    (differentiableOn_toricCartierTransition_comp_symm D v w e)
    (e.val.isOpen_inter_preimage_symm
      ((originalPolytopeNativeModelChart γ hs v).open_source.inter
        (originalPolytopeNativeModelChart γ hs w).open_source))

theorem toricCartierTransition_embedding (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    toricCartierTransition D v w (polytopeToricEmbedding γ hs a) =
      (latticeCharacter (toricCartierDatum D v - toricCartierDatum D w) a : ℂ) := by
  rw [toricCartierTransition, toricCartierLaurentModel, vertexChart_embedding hs v,
    latticeCharacter_eq_prod_basis hs v]
  simp [toricCartierTransitionExponent]


end SGPT.Toric

end
end ToricCanonicalFragment010
/- END SGPT.Toric.ToricCartierTransitionRegularity -/

/- BEGIN SGPT.Toric.ToricCartierCocycle; source SHA256 441fde5bf4c0dcc2475c2c78efb319460656fcf2e4282275d7b8f3e920952709 -/
section ToricCanonicalFragment011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The SAME actual original torus controls EVERY point of an actual open
set, including all its boundary strata. No density certificate is incoming. -/
theorem toricCartier_eqOn_of_denseTorus {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (U : Set (PolytopeToricVariety γ hs)) (hU : IsOpen U)
    (f g : PolytopeToricVariety γ hs → Y) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hT : ∀ a : Fin n → ℂˣ, polytopeToricEmbedding γ hs a ∈ U →
      f (polytopeToricEmbedding γ hs a) = g (polytopeToricEmbedding γ hs a)) : EqOn f g U := by
  have hd : DenseRange (polytopeToricEmbedding γ hs) := denseRange_originalPolytopeNativeOrbitMap γ
  have heq : EqOn f g (polytopeToricEmbedding γ hs '' (polytopeToricEmbedding γ hs ⁻¹' U)) := by
    rintro p ⟨a, ha, rfl⟩
    exact hT a ha
  exact heq.of_subset_closure hf hg (image_preimage_subset _ _)
    (hd.subset_closure_image_preimage_of_isOpen hU)

/-- The literal Cartier monomials give an actual holomorphic triple
cocycle on EVERY original chart overlap, not just on the dense orbit. -/
theorem toricCartierTransition_mul (D : ToricDivisor γ hs)
    (v w t : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source)
    (ht : p ∈ (originalPolytopeNativeModelChart γ hs t).source) :
    toricCartierTransition D v w p * toricCartierTransition D w t p =
      toricCartierTransition D v t p := by
  let U := ((originalPolytopeNativeModelChart γ hs v).source ∩
    (originalPolytopeNativeModelChart γ hs w).source) ∩
      (originalPolytopeNativeModelChart γ hs t).source
  have hU : IsOpen U :=
    ((originalPolytopeNativeModelChart γ hs v).open_source.inter
      (originalPolytopeNativeModelChart γ hs w).open_source).inter
        (originalPolytopeNativeModelChart γ hs t).open_source
  have hf : ContinuousOn (fun q => toricCartierTransition D v w q *
      toricCartierTransition D w t q) U :=
    ((continuousOn_toricCartierTransition D v w).mono (fun _ hq => hq.1)).mul
      ((continuousOn_toricCartierTransition D w t).mono (fun _ hq => ⟨hq.1.2, hq.2⟩))
  have hg : ContinuousOn (toricCartierTransition D v t) U :=
    (continuousOn_toricCartierTransition D v t).mono (fun _ hq => ⟨hq.1.1, hq.2⟩)
  have hall := toricCartier_eqOn_of_denseTorus U hU _ _ hf hg (by
    intro a _
    rw [toricCartierTransition_embedding, toricCartierTransition_embedding,
      toricCartierTransition_embedding]
    have hvec : (toricCartierDatum D v - toricCartierDatum D w) +
        (toricCartierDatum D w - toricCartierDatum D t) =
        toricCartierDatum D v - toricCartierDatum D t := by abel
    have hh := congrArg (fun z : ℂˣ => (z : ℂ))
      (latticeCharacter_add (toricCartierDatum D v - toricCartierDatum D w)
        (toricCartierDatum D w - toricCartierDatum D t) a)
    simpa only [Units.val_mul, hvec] using hh.symm)
  exact hall ⟨⟨hv, hw⟩, ht⟩


end SGPT.Toric

end
end ToricCanonicalFragment011
/- END SGPT.Toric.ToricCartierCocycle -/

/- BEGIN SGPT.Toric.ToricCartierMetricLaw; source SHA256 e8e97853394636425125a64804f3cc460ba45141efc025590c95e3f33dd84735 -/
section ToricCanonicalFragment012

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

theorem toricCartierTransition_norm_sq_embedding {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v w : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    ‖toricCartierTransition D v w (polytopeToricEmbedding γ hs a)‖ ^ 2 =
      Real.exp (h.weight w (originalPolytopeNativeModelChart γ hs w (polytopeToricEmbedding γ hs a)) -
        h.weight v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a))) := by
  rw [toricCartierTransition_embedding]
  have hpos : 0 < ‖(latticeCharacter (toricCartierDatum D v - toricCartierDatum D w) a : ℂ)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (Units.ne_zero _))
  have hlog : Real.log (‖(latticeCharacter (toricCartierDatum D v - toricCartierDatum D w) a : ℂ)‖ ^ 2) =
      latticeFunctional (toricCartierDatum D v - toricCartierDatum D w) (unitTorusLog a) :=
    latticeCharacter_log_norm_sq _ _
  have hsub : latticeFunctional (toricCartierDatum D v - toricCartierDatum D w) (unitTorusLog a) =
      latticeFunctional (toricCartierDatum D v) (unitTorusLog a) -
        latticeFunctional (toricCartierDatum D w) (unitTorusLog a) := by
    simp only [latticeFunctional_apply, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  have ht := h.transition v w a
  have hdiff : latticeFunctional (toricCartierDatum D v - toricCartierDatum D w) (unitTorusLog a) =
      h.weight w (originalPolytopeNativeModelChart γ hs w (polytopeToricEmbedding γ hs a)) -
        h.weight v (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) := by
    rw [hsub]
    linarith
  calc
    _ = Real.exp (Real.log (‖(latticeCharacter (toricCartierDatum D v - toricCartierDatum D w) a : ℂ)‖ ^ 2)) :=
      (Real.exp_log hpos).symm
    _ = Real.exp (latticeFunctional (toricCartierDatum D v - toricCartierDatum D w) (unitTorusLog a)) :=
      congrArg Real.exp hlog
    _ = _ := congrArg Real.exp hdiff

/-- The original smooth metric's actual compatibility law on the ENTIRE
native overlap. It is derived from the given original metric on the torus
and actual boundary density, not assumed for the constructed native bundle. -/
theorem toricCartierTransition_norm_sq {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v w : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    ‖toricCartierTransition D v w p‖ ^ 2 =
      Real.exp (h.weight w (originalPolytopeNativeModelChart γ hs w p) -
        h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
  let U := (originalPolytopeNativeModelChart γ hs v).source ∩
    (originalPolytopeNativeModelChart γ hs w).source
  have hU : IsOpen U := (originalPolytopeNativeModelChart γ hs v).open_source.inter
    (originalPolytopeNativeModelChart γ hs w).open_source
  have hf : ContinuousOn (fun q => ‖toricCartierTransition D v w q‖ ^ 2) U :=
    (continuousOn_toricCartierTransition D v w).norm.pow 2
  have hvcont : ContinuousOn (fun q => h.weight v (originalPolytopeNativeModelChart γ hs v q)) U :=
    (h.smooth v).continuous.comp_continuousOn
      ((originalPolytopeNativeModelChart γ hs v).continuousOn.mono inter_subset_left)
  have hwcont : ContinuousOn (fun q => h.weight w (originalPolytopeNativeModelChart γ hs w q)) U :=
    (h.smooth w).continuous.comp_continuousOn
      ((originalPolytopeNativeModelChart γ hs w).continuousOn.mono inter_subset_right)
  have hg : ContinuousOn (fun q => Real.exp
      (h.weight w (originalPolytopeNativeModelChart γ hs w q) -
        h.weight v (originalPolytopeNativeModelChart γ hs v q))) U :=
    Real.continuous_exp.comp_continuousOn (hwcont.sub hvcont)
  exact (toricCartier_eqOn_of_denseTorus U hU _ _ hf hg
    (fun a _ => toricCartierTransition_norm_sq_embedding h v w a)) ⟨hv, hw⟩

end SGPT.Toric

end
end ToricCanonicalFragment012
/- END SGPT.Toric.ToricCartierMetricLaw -/

/- BEGIN SGPT.Toric.ToricNativeFrameCoefficients; source SHA256 46bb32b1fb83cf02d9bf76f9193bac32533b5626f64c8b983088d05549c4f6eb -/
section ToricCanonicalFragment013

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

theorem contMDiffOn_toricCartierTransition (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) :
    ContMDiffOn (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞ (toricCartierTransition D v w)
      ((originalPolytopeNativeModelChart γ hs v).source ∩
        (originalPolytopeNativeModelChart γ hs w).source) := by
  rw [contMDiffOn_iff]
  refine ⟨continuousOn_toricCartierTransition D v w, ?_⟩
  intro x y
  simpa only [mfld_simps, complexChartAt, Function.comp_def] using
    contDiffOn_toricCartierTransition_comp_symm D v w (complexChartAt (n := n) x)

variable (γ hs) in
/-- A pointwise choice from the SAME actual original chart cover.
No continuity of this raw index choice is asserted or needed. -/
def toricNativePreferredVertex (p : PolytopeToricVariety γ hs) : latticePolytopeVertices γ :=
  (originalPolytopeNativeModelChart_cover γ hs p).choose

theorem toricNativePreferredVertex_mem (p : PolytopeToricVariety γ hs) :
    p ∈ (originalPolytopeNativeModelChart γ hs (toricNativePreferredVertex γ hs p)).source :=
  (originalPolytopeNativeModelChart_cover γ hs p).choose_spec

/-- Coefficient in the genuine original holomorphic frame of a physical
standard complex Hilbert fiber, labelled by the pointwise UNIT vector in
the preferred original frame. The generated bundle topology, not a raw
product topology, will make these original frame charts continuous. -/
def toricNativeFrameCoefficient {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (p : PolytopeToricVariety γ hs) : ℂ :=
  let i := toricNativePreferredVertex γ hs p
  (Real.exp (h.weight i (originalPolytopeNativeModelChart γ hs i p) / 2) : ℂ) *
    toricCartierTransition D i v p

theorem toricNativeFrameCoefficient_ne_zero {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    toricNativeFrameCoefficient h v p ≠ 0 := by
  unfold toricNativeFrameCoefficient
  apply mul_ne_zero
  · exact_mod_cast (Real.exp_pos _).ne'
  · exact toricCartierTransition_ne_zero D _ v (toricNativePreferredVertex_mem p) hv

/-- Actual holomorphic frame changes survive the pointwise unit-fiber
labelling exactly. No normalized unitary chart is asserted holomorphic. -/
theorem toricNativeFrameCoefficient_transition {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v w : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    toricCartierTransition D v w p * toricNativeFrameCoefficient h v p =
      toricNativeFrameCoefficient h w p := by
  let i := toricNativePreferredVertex γ hs p
  let r : ℂ := Real.exp (h.weight i (originalPolytopeNativeModelChart γ hs i p) / 2)
  change toricCartierTransition D v w p * (r * toricCartierTransition D i v p) =
    r * toricCartierTransition D i w p
  calc
    _ = r * (toricCartierTransition D i v p * toricCartierTransition D v w p) := by ring
    _ = _ := by
      rw [toricCartierTransition_mul D i v w (toricNativePreferredVertex_mem p) hv hw]

/-- The original metric law manufactures the actual physical frame norm.
This equality is proved from independent standard fiber norms and actual
Cartier transitions, not stored as a desired norm certificate. -/
theorem toricNativeFrameCoefficient_norm_sq {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ‖toricNativeFrameCoefficient h v p‖ ^ 2 =
      Real.exp (h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
  let i := toricNativePreferredVertex γ hs p
  let wi := h.weight i (originalPolytopeNativeModelChart γ hs i p)
  have hexp : ‖(Real.exp (wi / 2) : ℂ)‖ ^ 2 = Real.exp wi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_two, ← Real.exp_add]
    congr 1
    ring
  change ‖(Real.exp (wi / 2) : ℂ) * toricCartierTransition D i v p‖ ^ 2 = _
  rw [norm_mul, mul_pow, hexp,
    toricCartierTransition_norm_sq h i v (toricNativePreferredVertex_mem p) hv, ← Real.exp_add]
  congr 1
  dsimp only [wi]
  ring

end SGPT.Toric

end
end ToricCanonicalFragment013
/- END SGPT.Toric.ToricNativeFrameCoefficients -/

/- BEGIN SGPT.Toric.ToricNativeLinePretrivialization; source SHA256 2b90901beb2e8b3068874f5ab97d950e452ac501e809754b19c0b4cdcf3c049d -/
section ToricCanonicalFragment014

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Independent standard complex Hilbert fibers, labelled by the original
pointwise UNIT vector. Their actual TOTAL-SPACE topology is constructed
from the genuine original holomorphic frame pretrivializations below. -/
def ToricNativeLineFiber {D : ToricDivisor γ hs} (_h : BigToricMetric D)
    (_p : PolytopeToricVariety γ hs) : Type := ℂ

instance toricNativeLineFiberNormed {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (p : PolytopeToricVariety γ hs) : NormedAddCommGroup (ToricNativeLineFiber h p) :=
  inferInstanceAs (NormedAddCommGroup ℂ)

instance toricNativeLineFiberHermitian {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (p : PolytopeToricVariety γ hs) : InnerProductSpace ℂ (ToricNativeLineFiber h p) :=
  inferInstanceAs (InnerProductSpace ℂ ℂ)

/-- Actual original holomorphic frame charts on the SAME dependent physical
fibers, before assigning total-space topology. No product topology or
holomorphicity of the pointwise unit-vector choices is assumed. -/
def toricNativeLinePretrivialization {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) :
    Pretrivialization ℂ
      (TotalSpace.proj : TotalSpace ℂ (ToricNativeLineFiber h) → PolytopeToricVariety γ hs) where
  toFun p := (p.proj, toricNativeFrameCoefficient h v p.proj * (show ℂ from p.snd))
  invFun p := ⟨p.1, (toricNativeFrameCoefficient h v p.1)⁻¹ * p.2⟩
  source := TotalSpace.proj ⁻¹' (originalPolytopeNativeModelChart γ hs v).source
  target := (originalPolytopeNativeModelChart γ hs v).source ×ˢ Set.univ
  map_source' := fun _ hp => ⟨hp, Set.mem_univ _⟩
  map_target' := fun _ hp => hp.1
  left_inv' := by
    rintro ⟨p, z⟩ hp
    simp only [TotalSpace.mk_inj]
    change (toricNativeFrameCoefficient h v p)⁻¹ *
      (toricNativeFrameCoefficient h v p * (show ℂ from z)) = (show ℂ from z)
    rw [← mul_assoc, inv_mul_cancel₀ (toricNativeFrameCoefficient_ne_zero h v hp), one_mul]
  right_inv' := by
    rintro ⟨p, z⟩ ⟨hp, _⟩
    change (p, toricNativeFrameCoefficient h v p *
      ((toricNativeFrameCoefficient h v p)⁻¹ * z)) = (p, z)
    apply Prod.ext
    · rfl
    rw [← mul_assoc, mul_inv_cancel₀ (toricNativeFrameCoefficient_ne_zero h v hp), one_mul]
  open_target := (originalPolytopeNativeModelChart γ hs v).open_source.prod isOpen_univ
  baseSet := (originalPolytopeNativeModelChart γ hs v).source
  open_baseSet := (originalPolytopeNativeModelChart γ hs v).open_source
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance toricNativeLinePretrivialization_isLinear {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) :
    (toricNativeLinePretrivialization h v).IsLinear ℂ where
  linear p _ := {
    map_add := by
      intro z t
      change toricNativeFrameCoefficient h v p * ((show ℂ from z) + (show ℂ from t)) =
        toricNativeFrameCoefficient h v p * (show ℂ from z) +
          toricNativeFrameCoefficient h v p * (show ℂ from t)
      ring
    map_smul := by
      intro a z
      change toricNativeFrameCoefficient h v p * (a * (show ℂ from z)) =
        a * (toricNativeFrameCoefficient h v p * (show ℂ from z))
      ring }

theorem toricNativeLinePretrivialization_symm {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) (z : ℂ) :
    (toricNativeLinePretrivialization h v).symm p z =
      (toricNativeFrameCoefficient h v p)⁻¹ * z := by
  have hh := (toricNativeLinePretrivialization h v).mk_symm hv z
  change (⟨p, (toricNativeLinePretrivialization h v).symm p z⟩ :
      TotalSpace ℂ (ToricNativeLineFiber h)) =
        ⟨p, (toricNativeFrameCoefficient h v p)⁻¹ * z⟩ at hh
  simpa only [TotalSpace.mk_inj] using hh

end SGPT.Toric

end
end ToricCanonicalFragment014
/- END SGPT.Toric.ToricNativeLinePretrivialization -/

/- BEGIN SGPT.Toric.ToricNativeLinePrebundle; source SHA256 1f074c1ce6a686449fdbe84e6b2d53cdd721b3c924a028301f7986091ec5b12b -/
section ToricCanonicalFragment015

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

def toricNativeLineCoordChange (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) (p : PolytopeToricVariety γ hs) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)
    (toricCartierTransition D v w p)

theorem toricNativeLineCoordChange_apply {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v w : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) (z : ℂ) :
    toricNativeLineCoordChange D v w p z =
      ((toricNativeLinePretrivialization h w)
        ⟨p, (toricNativeLinePretrivialization h v).symm p z⟩).2 := by
  rw [toricNativeLinePretrivialization_symm h v hv z]
  change z * toricCartierTransition D v w p =
    toricNativeFrameCoefficient h w p * ((toricNativeFrameCoefficient h v p)⁻¹ * z)
  rw [← toricNativeFrameCoefficient_transition h v w hv hw]
  field_simp [toricNativeFrameCoefficient_ne_zero h v hv]

theorem continuousOn_toricNativeLineCoordChange (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) :
    ContinuousOn (toricNativeLineCoordChange D v w)
      ((originalPolytopeNativeModelChart γ hs v).source ∩
        (originalPolytopeNativeModelChart γ hs w).source) :=
  (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).continuous.comp_continuousOn
    (continuousOn_toricCartierTransition D v w)

theorem contMDiffOn_toricNativeLineCoordChange (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) :
    ContMDiffOn (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ →L[ℂ] ℂ)) ∞
      (toricNativeLineCoordChange D v w)
      ((originalPolytopeNativeModelChart γ hs v).source ∩
        (originalPolytopeNativeModelChart γ hs w).source) :=
  (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).contMDiff.comp_contMDiffOn
    (contMDiffOn_toricCartierTransition D v w)

/-- The actual native topology and bundle are manufactured from the
ORIGINAL holomorphic frame partial equivalences. Standard physical
Hilbert fibers alone do not assign a product topology to the total space. -/
def toricNativeLineVectorPrebundle {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    VectorPrebundle ℂ ℂ (ToricNativeLineFiber h) where
  pretrivializationAtlas := Set.range (toricNativeLinePretrivialization h)
  pretrivialization_linear' := by
    rintro _ ⟨v, rfl⟩
    infer_instance
  pretrivializationAt p := toricNativeLinePretrivialization h (toricNativePreferredVertex γ hs p)
  mem_base_pretrivializationAt p := toricNativePreferredVertex_mem p
  pretrivialization_mem_atlas p := ⟨toricNativePreferredVertex γ hs p, rfl⟩
  exists_coordChange := by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    exact ⟨toricNativeLineCoordChange D v w, continuousOn_toricNativeLineCoordChange D v w,
      fun p hp z => toricNativeLineCoordChange_apply h v w hp.1 hp.2 z⟩
  totalSpaceMk_isInducing := by
    intro p
    let v := toricNativePreferredVertex γ hs p
    have hne := toricNativeFrameCoefficient_ne_zero h v (toricNativePreferredVertex_mem p)
    change IsInducing (fun z : ℂ => (p, toricNativeFrameCoefficient h v p * z))
    exact isInducing_const_prod.mpr (Homeomorph.mulLeft₀ _ hne).isInducing

instance toricNativeLineTotalSpaceTopology {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    TopologicalSpace (TotalSpace ℂ (ToricNativeLineFiber h)) :=
  (toricNativeLineVectorPrebundle h).totalSpaceTopology

instance toricNativeLineFiberBundle {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    FiberBundle ℂ (ToricNativeLineFiber h) :=
  (toricNativeLineVectorPrebundle h).toFiberBundle

instance toricNativeLineVectorBundle {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    VectorBundle ℂ ℂ (ToricNativeLineFiber h) :=
  (toricNativeLineVectorPrebundle h).toVectorBundle

instance toricNativeLinePrebundleHolomorphic {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    (toricNativeLineVectorPrebundle h).IsContMDiff (𝓘(ℂ, ComplexModel n)) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    exact ⟨toricNativeLineCoordChange D v w, contMDiffOn_toricNativeLineCoordChange D v w,
      fun p hp z => toricNativeLineCoordChange_apply h v w hp.1 hp.2 z⟩

instance toricNativeLineHolomorphicBundle {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    ContMDiffVectorBundle ∞ ℂ (ToricNativeLineFiber h) (𝓘(ℂ, ComplexModel n)) :=
  (toricNativeLineVectorPrebundle h).contMDiffVectorBundle (𝓘(ℂ, ComplexModel n))

def toricNativeLineTrivialization {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) :
    Trivialization ℂ
      (TotalSpace.proj : TotalSpace ℂ (ToricNativeLineFiber h) → PolytopeToricVariety γ hs) :=
  (toricNativeLineVectorPrebundle h).trivializationOfMemPretrivializationAtlas ⟨v, rfl⟩

instance toricNativeLineTrivialization_memAtlas {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) :
    MemTrivializationAtlas (toricNativeLineTrivialization h v) where
  out := ⟨_, ⟨v, rfl⟩, rfl⟩

theorem toricNativeLineTrivialization_symm {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) (z : ℂ) :
    (toricNativeLineTrivialization h v).symm p z =
      (toricNativeFrameCoefficient h v p)⁻¹ * z :=
  toricNativeLinePretrivialization_symm h v hv z

end SGPT.Toric

end
end ToricCanonicalFragment015
/- END SGPT.Toric.ToricNativeLinePrebundle -/

/- BEGIN SGPT.Toric.ToricNativeLineMetric; source SHA256 7f9d19ded0c367bf7d72559cf11c847fb9bf5dda2b40ac67ae0139f8015ba6b8 -/
section ToricCanonicalFragment016

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual independent standard fiber norms, read in the SAME original
holomorphic frame. The desired metric formula is proved, not assigned. -/
theorem toricNativeLineTrivialization_frame_norm_sq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ‖(toricNativeLineTrivialization h v).symm p 1‖ ^ 2 =
      Real.exp (-h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
  rw [toricNativeLineTrivialization_symm h v hv]
  change ‖(toricNativeFrameCoefficient h v p)⁻¹ * (1 : ℂ)‖ ^ 2 = _
  simp only [mul_one, norm_inv, inv_pow]
  rw [toricNativeFrameCoefficient_norm_sq h v hv, Real.exp_neg]

theorem toricNativeLine_norm_sq_eq_coordinates {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) (z : ToricNativeLineFiber h p) :
    ‖z‖ ^ 2 = ‖((toricNativeLineTrivialization h v) ⟨p, z⟩).2‖ ^ 2 *
      Real.exp (-h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
  change ‖(show ℂ from z)‖ ^ 2 =
    ‖toricNativeFrameCoefficient h v p * (show ℂ from z)‖ ^ 2 * _
  rw [norm_mul, mul_pow, toricNativeFrameCoefficient_norm_sq h v hv]
  let W := h.weight v (originalPolytopeNativeModelChart γ hs v p)
  have hcancel : Real.exp W * Real.exp (-W) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  change ‖(show ℂ from z)‖ ^ 2 =
    (Real.exp W * ‖(show ℂ from z)‖ ^ 2) * Real.exp (-W)
  calc
    _ = (Real.exp W * Real.exp (-W)) * ‖(show ℂ from z)‖ ^ 2 := by rw [hcancel, one_mul]
    _ = _ := by ring

/-- Joint physical norm continuity on the ACTUAL constructed total-space
topology follows from original frame weights and actual local charts. -/
theorem continuous_toricNativeLine_norm_sq {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    Continuous (fun q : TotalSpace ℂ (ToricNativeLineFiber h) => ‖q.snd‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro q
  let v := toricNativePreferredVertex γ hs q.proj
  let e := toricNativeLineTrivialization h v
  have hv : q.proj ∈ (originalPolytopeNativeModelChart γ hs v).source :=
    toricNativePreferredVertex_mem q.proj
  have hqe : q ∈ e.source := hv
  have he : ContinuousAt (fun r : TotalSpace ℂ (ToricNativeLineFiber h) => (e r).2) q :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds hqe)).snd
  have hp : ContinuousAt
      (fun r : TotalSpace ℂ (ToricNativeLineFiber h) => r.proj) q :=
    (FiberBundle.continuous_proj ℂ (ToricNativeLineFiber h)).continuousAt
  have hchart : ContinuousAt (originalPolytopeNativeModelChart γ hs v) q.proj :=
    (originalPolytopeNativeModelChart γ hs v).continuousOn.continuousAt
      ((originalPolytopeNativeModelChart γ hs v).open_source.mem_nhds hv)
  have hweight : ContinuousAt
      (fun r : TotalSpace ℂ (ToricNativeLineFiber h) =>
        h.weight v (originalPolytopeNativeModelChart γ hs v r.proj)) q :=
    (h.smooth v).continuous.continuousAt.comp (hchart.comp hp)
  have hexpr := (he.norm.pow 2).mul (Real.continuous_exp.continuousAt.comp hweight.neg)
  apply hexpr.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hqe] with r hr
  exact toricNativeLine_norm_sq_eq_coordinates h v hr r.snd

instance toricNativeLineContinuousFiberNorm {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    ContinuousFiberNorm (ToricNativeLineFiber h) := by
  refine ⟨?_⟩
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm] using
    Real.continuous_sqrt.comp (continuous_toricNativeLine_norm_sq h)

/-- The actual native Hermitian holomorphic line bundle of the SAME
original Cartier data and SAME source metric, with independently built
physical fibers, topology, holomorphic atlas and continuous physical norm.
There is no H0, Chern, frame norm or model certificate input. -/
def toricNativeHermitianLineBundle {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    HermitianHolomorphicLineBundle n (PolytopeToricVariety γ hs) :=
  HermitianHolomorphicLineBundle.ofNative (ToricNativeLineFiber h)

def toricNativeLineAtlasFrame {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) :
    HermitianHolomorphicLineBundle.AtlasFrame (toricNativeHermitianLineBundle h) :=
  ⟨toricNativeLineTrivialization h v, inferInstance⟩

end SGPT.Toric

end
end ToricCanonicalFragment016
/- END SGPT.Toric.ToricNativeLineMetric -/

/- BEGIN SGPT.Toric.ToricNativeSmoothMetric; source SHA256 e158ce5a46a05e73c6f9391d4b213ece5f7abd913605f223b477d56ba6769bd7 -/
section ToricCanonicalFragment017

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- EVERY actual atlas frame of the manufactured original bundle is an
original native frame. This is derived from its actual prebundle atlas. -/
theorem toricNativeLineAtlasFrame_exhaustive {D : ToricDivisor γ hs}
    (h : BigToricMetric D)
    (e : HermitianHolomorphicLineBundle.AtlasFrame (toricNativeHermitianLineBundle h)) :
    ∃ v : latticePolytopeVertices γ, e.val = toricNativeLineTrivialization h v := by
  rcases e.property.out with ⟨f, hf, heq⟩
  rcases hf with ⟨v, rfl⟩
  exact ⟨v, heq⟩

/-- The source smooth physical Hermitian metric condition is an OUTPUT for
the original toric bundle. All actual chart/frame squared norms are smooth
from the SAME original given weights; no smooth-metric certificate is input. -/
theorem isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle
    {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    IsSourceSmoothHermitianMetric (toricNativeHermitianLineBundle h) := by
  intro c e
  obtain ⟨v, hv⟩ := toricNativeLineAtlasFrame_exhaustive h e
  simp only [hv]
  have hweight := contDiffOn_comp_vertexChart_comp_symm (h.smooth v) v c
  have hexp := Real.contDiff_exp.comp_contDiffOn hweight.neg
  apply hexp.congr
  intro z hz
  exact toricNativeLineTrivialization_frame_norm_sq h v hz.2

end SGPT.Toric

end
end ToricCanonicalFragment017
/- END SGPT.Toric.ToricNativeSmoothMetric -/

/- BEGIN SGPT.Toric.ToricNativeFirstChernForm; source SHA256 c3ddd3347cb5c7c7a26e563a054d81177571d0f11acb52b4b0b49693a97c39f3 -/
section ToricCanonicalFragment018

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeHermitianMetric
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual native physical metric has exactly the original given
weight in the SAME original frame on the entire original model chart. -/
theorem toricNativeLine_negative_log_frame_norm_sq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) :
    (fun z : ComplexModel n => -Real.log
      (‖(toricNativeLineTrivialization h v).symm
        ((polytopeToricVertexChart γ hs v).val.symm z) 1‖ ^ 2)) = h.weight v := by
  funext z
  let C : OpenPartialHomeomorph (PolytopeToricVariety γ hs) (ComplexModel n) :=
    (polytopeToricVertexChart γ hs v).val
  have hz : z ∈ C.target := by
    change z ∈ (originalPolytopeNativeModelChart γ hs v).target
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  have hsrc : C.symm z ∈ (originalPolytopeNativeModelChart γ hs v).source :=
    C.map_target hz
  rw [toricNativeLineTrivialization_frame_norm_sq h v hsrc, Real.log_exp]
  change - -h.weight v (C (C.symm z)) = h.weight v z
  rw [C.right_inv hz, neg_neg]

/-- Comparison of the manufactured physical Chern form with the SAME
original curvature, with no Chern comparison hypothesis. -/
theorem toricNativeFirstChernForm_coeff_vertex {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) (z : ComplexModel n) :
    (sourceNativeFirstChernForm (toricNativeHermitianLineBundle h)
      (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle h)).val.coeff
        (polytopeToricVertexChart γ hs v) z =
      h.form.val.coeff (polytopeToricVertexChart γ hs v) z := by
  let c : ComplexChart n (PolytopeToricVariety γ hs) := polytopeToricVertexChart γ hs v
  have hz : z ∈ c.val.target := by
    change z ∈ (originalPolytopeNativeModelChart γ hs v).target
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  have hsrc : c.val.symm z ∈ (toricNativeLineAtlasFrame h v).val.baseSet :=
    c.val.map_target hz
  have hchern := sourceNativeFirstChernForm_isOwn (toricNativeHermitianLineBundle h)
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle h)
    c (toricNativeLineAtlasFrame h v) z hz hsrc
  change _ = smoothDDC (fun w => -Real.log
    (‖(toricNativeLineTrivialization h v).symm (c.val.symm w) 1‖ ^ 2)) z at hchern
  rw [toricNativeLine_negative_log_frame_norm_sq h v] at hchern
  exact hchern.trans (h.coeff v z).symm

theorem toricNativeFirstChernForm_geometricallyEq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) :
    (sourceNativeFirstChernForm (toricNativeHermitianLineBundle h)
      (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle h)).val.GeometricallyEq
        h.form.val := by
  intro c z hz
  obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs c
  exact toricNativeFirstChernForm_coeff_vertex h v z

/-- The original source curvature really is the OWN first Chern form of
the actual original native Hermitian line bundle. This is an output from
the original toric weights and actual constructed geometry. -/
theorem isOwnFirstChernForm_toricNativeHermitianLineBundle {D : ToricDivisor γ hs}
    (h : BigToricMetric D) :
    SGPT.PSH.GlobalL2.IsOwnFirstChernForm (toricNativeHermitianLineBundle h) h.form := by
  intro c e z hz hzU
  rw [← toricNativeFirstChernForm_geometricallyEq h c hz]
  exact sourceNativeFirstChernForm_isOwn (toricNativeHermitianLineBundle h)
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle h) c e z hz hzU

end SGPT.Toric

end
end ToricCanonicalFragment018
/- END SGPT.Toric.ToricNativeFirstChernForm -/

/- BEGIN SGPT.Toric.ToricNativeSectionCoefficients; source SHA256 ae22ee5d07843ca6ac81f734e43d7411afee0748b012686eb7eb8e1244a654ea -/
section ToricCanonicalFragment020

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- ALL genuine native dependent-fiber holomorphic sections. This is the
existing physical ContMDiffSection carrier, independently of toricSections. -/
abbrev ToricNativeHolomorphicSections {D : ToricDivisor γ hs} (h : BigToricMetric D) :=
  HolomorphicSections (n := n) (toricNativeHermitianLineBundle h).Fiber

def toricNativeSectionFrameCoeff {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (s : ToricNativeHolomorphicSections h)
    (p : PolytopeToricVariety γ hs) : ℂ :=
  ((toricNativeLineTrivialization h v) ⟨p, s p⟩).2

def toricNativeSectionChartCoeff {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (s : ToricNativeHolomorphicSections h)
    (z : ComplexModel n) : ℂ :=
  toricNativeSectionFrameCoeff h v s ((originalPolytopeNativeModelChart γ hs v).symm z)

/-- EVERY actual physical section has an entire coefficient on the whole
original native C^n chart. It is not assumed or restricted to characters. -/
theorem differentiable_toricNativeSectionChartCoeff {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ)
    (s : ToricNativeHolomorphicSections h) :
    Differentiable ℂ (toricNativeSectionChartCoeff h v s) := by
  intro z
  let C : OpenPartialHomeomorph (PolytopeToricVariety γ hs) (ComplexModel n) :=
    (polytopeToricVertexChart γ hs v).val
  let e := toricNativeLineTrivialization h v
  have hz : z ∈ C.target := by
    change z ∈ (originalPolytopeNativeModelChart γ hs v).target
    rw [originalPolytopeNativeModelChart_target]
    exact Set.mem_univ z
  have hp : C.symm z ∈ e.baseSet := C.map_target hz
  have hcoeff : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞
      (toricNativeSectionFrameCoeff h v s) (C.symm z) :=
    (e.contMDiffAt_section_iff hp).mp (s.contMDiff (C.symm z))
  have hmem : C ∈ IsManifold.maximalAtlas (𝓘(ℂ, ComplexModel n)) ∞
      (PolytopeToricVariety γ hs) :=
    IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (M := PolytopeToricVariety γ hs) (polytopeToricVertexChart γ hs v).property
  have hchart : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ComplexModel n)) ∞ C.symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (M := PolytopeToricVariety γ hs) hmem hz
  exact (contMDiffAt_iff_contDiffAt.mp (hcoeff.comp z hchart)).differentiableAt (by simp)

theorem toricNativeSectionFrameCoeff_transition {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v w : latticePolytopeVertices γ)
    (s : ToricNativeHolomorphicSections h) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    toricNativeSectionFrameCoeff h w s p =
      toricCartierTransition D v w p * toricNativeSectionFrameCoeff h v s p := by
  change toricNativeFrameCoefficient h w p * (show ℂ from s p) =
    toricCartierTransition D v w p *
      (toricNativeFrameCoefficient h v p * (show ℂ from s p))
  rw [← toricNativeFrameCoefficient_transition h v w hv hw, mul_assoc]

theorem toricNativeSectionChartCoeff_chart_apply {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ)
    (s : ToricNativeHolomorphicSections h) {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    toricNativeSectionChartCoeff h v s (originalPolytopeNativeModelChart γ hs v p) =
      toricNativeSectionFrameCoeff h v s p := by
  unfold toricNativeSectionChartCoeff
  rw [(originalPolytopeNativeModelChart γ hs v).left_inv hp]

end SGPT.Toric

end
end ToricCanonicalFragment020
/- END SGPT.Toric.ToricNativeSectionCoefficients -/

/- BEGIN SGPT.Toric.ToricNativeSectionRestriction; source SHA256 90dc3247a0e2cd9e27e5e2d6bca0f5fc3b47d41e44307d30b102cd2235ec9c29 -/
section ToricCanonicalFragment021

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

theorem toricNativeEmbedding_mem_chartSource (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) :
    polytopeToricEmbedding γ hs a ∈ (originalPolytopeNativeModelChart γ hs v).source := by
  rw [originalPolytopeNativeModelChart_source]
  exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs v a

/-- Restriction of an actual physical section through the ORIGINAL
Cartier rational frame on the SAME dense torus. -/
def toricNativeSectionTorusFunction {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (s : ToricNativeHolomorphicSections h) (a : Fin n → ℂˣ) : ℂ :=
  toricNativeSectionFrameCoeff h (polytopeToricBaseVertex γ) s (polytopeToricEmbedding γ hs a) *
    latticeCharacter (toricCartierDatum D (polytopeToricBaseVertex γ)) a

theorem toricNativeSectionTorusFunction_eq_chartCoeff {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ)
    (s : ToricNativeHolomorphicSections h) (a : Fin n → ℂˣ) :
    toricNativeSectionTorusFunction h s a =
      toricNativeSectionChartCoeff h v s
        (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
          latticeCharacter (toricCartierDatum D v) a := by
  let w := polytopeToricBaseVertex γ
  have hv : polytopeToricEmbedding γ hs a ∈ (originalPolytopeNativeModelChart γ hs v).source :=
    toricNativeEmbedding_mem_chartSource v a
  have hw : polytopeToricEmbedding γ hs a ∈ (originalPolytopeNativeModelChart γ hs w).source :=
    toricNativeEmbedding_mem_chartSource w a
  rw [toricNativeSectionChartCoeff_chart_apply h v s hv]
  have hc := toricNativeSectionFrameCoeff_transition h v w s hv hw
  rw [toricCartierTransition_embedding] at hc
  change toricNativeSectionFrameCoeff h w s (polytopeToricEmbedding γ hs a) *
      (latticeCharacter (toricCartierDatum D w) a : ℂ) = _
  rw [hc]
  have hchar : (latticeCharacter (toricCartierDatum D v - toricCartierDatum D w) a : ℂ) *
      (latticeCharacter (toricCartierDatum D w) a : ℂ) =
      (latticeCharacter (toricCartierDatum D v) a : ℂ) := by
    have hvec : (toricCartierDatum D v - toricCartierDatum D w) +
        toricCartierDatum D w = toricCartierDatum D v := by abel
    have hh := congrArg (fun z : ℂˣ => (z : ℂ))
      (latticeCharacter_add (toricCartierDatum D v - toricCartierDatum D w)
        (toricCartierDatum D w) a)
    simpa only [Units.val_mul, hvec] using hh.symm
  calc
    _ = toricNativeSectionFrameCoeff h v s (polytopeToricEmbedding γ hs a) *
        ((latticeCharacter (toricCartierDatum D v - toricCartierDatum D w) a : ℂ) *
          (latticeCharacter (toricCartierDatum D w) a : ℂ)) := by ring
    _ = _ := by rw [hchar]

/-- EVERY actual native section lands in the independently defined FULL
original toric section space. No finite subseries or H0 dictionary is an input. -/
theorem toricNativeSectionTorusFunction_mem {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (s : ToricNativeHolomorphicSections h) :
    toricNativeSectionTorusFunction h s ∈ toricSections D := by
  intro v
  exact ⟨toricNativeSectionChartCoeff h v s,
    differentiable_toricNativeSectionChartCoeff h v s,
    toricNativeSectionTorusFunction_eq_chartCoeff h v s⟩

def toricNativeSectionRestriction {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    ToricNativeHolomorphicSections h →ₗ[ℂ] toricSections D where
  toFun s := ⟨toricNativeSectionTorusFunction h s, toricNativeSectionTorusFunction_mem h s⟩
  map_add' s t := by
    apply Subtype.ext
    funext a
    change (toricNativeFrameCoefficient h (polytopeToricBaseVertex γ)
        (polytopeToricEmbedding γ hs a) *
          ((show ℂ from s (polytopeToricEmbedding γ hs a)) +
            (show ℂ from t (polytopeToricEmbedding γ hs a)))) *
              (latticeCharacter (toricCartierDatum D (polytopeToricBaseVertex γ)) a : ℂ) =
      (toricNativeFrameCoefficient h (polytopeToricBaseVertex γ) (polytopeToricEmbedding γ hs a) *
        (show ℂ from s (polytopeToricEmbedding γ hs a))) *
          (latticeCharacter (toricCartierDatum D (polytopeToricBaseVertex γ)) a : ℂ) +
      (toricNativeFrameCoefficient h (polytopeToricBaseVertex γ) (polytopeToricEmbedding γ hs a) *
        (show ℂ from t (polytopeToricEmbedding γ hs a))) *
          (latticeCharacter (toricCartierDatum D (polytopeToricBaseVertex γ)) a : ℂ)
    ring
  map_smul' c s := by
    apply Subtype.ext
    funext a
    change (toricNativeFrameCoefficient h (polytopeToricBaseVertex γ)
        (polytopeToricEmbedding γ hs a) *
          (c * (show ℂ from s (polytopeToricEmbedding γ hs a)))) *
            (latticeCharacter (toricCartierDatum D (polytopeToricBaseVertex γ)) a : ℂ) =
      c * ((toricNativeFrameCoefficient h (polytopeToricBaseVertex γ)
        (polytopeToricEmbedding γ hs a) * (show ℂ from s (polytopeToricEmbedding γ hs a))) *
          (latticeCharacter (toricCartierDatum D (polytopeToricBaseVertex γ)) a : ℂ))
    ring

theorem toricNativeSectionRestriction_injective {D : ToricDivisor γ hs}
    (h : BigToricMetric D) : Function.Injective (toricNativeSectionRestriction h) := by
  intro s t hst
  have hg : toricNativeSectionTorusFunction h s = toricNativeSectionTorusFunction h t :=
    congrArg Subtype.val hst
  ext p
  let v := toricNativePreferredVertex γ hs p
  have hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source := toricNativePreferredVertex_mem p
  have hf : toricNativeSectionChartCoeff h v s = toricNativeSectionChartCoeff h v t := by
    apply toricSectionCoeff_unique D v
      (differentiable_toricNativeSectionChartCoeff h v s).continuous
      (differentiable_toricNativeSectionChartCoeff h v t).continuous
      (toricNativeSectionTorusFunction_eq_chartCoeff h v s)
    intro a
    rw [hg]
    exact toricNativeSectionTorusFunction_eq_chartCoeff h v t a
  have hp := congrFun hf (originalPolytopeNativeModelChart γ hs v p)
  rw [toricNativeSectionChartCoeff_chart_apply h v s hv,
    toricNativeSectionChartCoeff_chart_apply h v t hv] at hp
  change toricNativeFrameCoefficient h v p * (show ℂ from s p) =
    toricNativeFrameCoefficient h v p * (show ℂ from t p) at hp
  change (show ℂ from s p) = (show ℂ from t p)
  exact mul_left_cancel₀ (toricNativeFrameCoefficient_ne_zero h v hv) hp

end SGPT.Toric

end
end ToricCanonicalFragment021
/- END SGPT.Toric.ToricNativeSectionRestriction -/

/- BEGIN SGPT.Toric.ToricNativeSectionGluing; source SHA256 ab501883d041357548f81ad55f1fb06a0f352c3b82e19582025c9811471323ee -/
section ToricCanonicalFragment022

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Choose an entire coefficient already present in the independent
original FULL Cartier-section definition. No native H0 certificate enters. -/
def toricOriginalSectionCoeff {D : ToricDivisor γ hs} (g : toricSections D)
    (v : latticePolytopeVertices γ) : ComplexModel n → ℂ :=
  (g.property v).choose

theorem differentiable_toricOriginalSectionCoeff {D : ToricDivisor γ hs}
    (g : toricSections D) (v : latticePolytopeVertices γ) :
    Differentiable ℂ (toricOriginalSectionCoeff g v) :=
  (g.property v).choose_spec.1

theorem toricOriginalSectionCoeff_torus {D : ToricDivisor γ hs}
    (g : toricSections D) (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    g.val a = toricOriginalSectionCoeff g v
      (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
        latticeCharacter (toricCartierDatum D v) a :=
  (g.property v).choose_spec.2 a

/-- The independently given entire coefficients glue on the ENTIRE actual
original overlap. The proof uses the genuine original dense torus and
nowhere-zero holomorphic Cartier transition, including boundary points. -/
theorem toricOriginalSectionCoeff_transition {D : ToricDivisor γ hs}
    (g : toricSections D) (v w : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    toricOriginalSectionCoeff g w (originalPolytopeNativeModelChart γ hs w p) =
      toricCartierTransition D v w p *
        toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v p) := by
  let U := (originalPolytopeNativeModelChart γ hs v).source ∩
    (originalPolytopeNativeModelChart γ hs w).source
  have hU : IsOpen U := (originalPolytopeNativeModelChart γ hs v).open_source.inter
    (originalPolytopeNativeModelChart γ hs w).open_source
  have hf : ContinuousOn
      (fun q => toricOriginalSectionCoeff g w (originalPolytopeNativeModelChart γ hs w q)) U :=
    (differentiable_toricOriginalSectionCoeff g w).continuous.comp_continuousOn
      ((originalPolytopeNativeModelChart γ hs w).continuousOn.mono inter_subset_right)
  have hg : ContinuousOn (fun q => toricCartierTransition D v w q *
      toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v q)) U :=
    (continuousOn_toricCartierTransition D v w).mul
      ((differentiable_toricOriginalSectionCoeff g v).continuous.comp_continuousOn
        ((originalPolytopeNativeModelChart γ hs v).continuousOn.mono inter_subset_left))
  have hall := toricCartier_eqOn_of_denseTorus U hU _ _ hf hg (by
    intro a _
    rw [toricCartierTransition_embedding]
    apply mul_right_cancel₀ (Units.ne_zero (latticeCharacter (toricCartierDatum D w) a))
    have hchar : (latticeCharacter (toricCartierDatum D v - toricCartierDatum D w) a : ℂ) *
        (latticeCharacter (toricCartierDatum D w) a : ℂ) =
        (latticeCharacter (toricCartierDatum D v) a : ℂ) := by
      have hvec : (toricCartierDatum D v - toricCartierDatum D w) + toricCartierDatum D w =
          toricCartierDatum D v := by abel
      have hh := congrArg (fun z : ℂˣ => (z : ℂ))
        (latticeCharacter_add (toricCartierDatum D v - toricCartierDatum D w)
          (toricCartierDatum D w) a)
      simpa only [Units.val_mul, hvec] using hh.symm
    calc
      _ = g.val a := (toricOriginalSectionCoeff_torus g w a).symm
      _ = toricOriginalSectionCoeff g v
          (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
            (latticeCharacter (toricCartierDatum D v) a : ℂ) := toricOriginalSectionCoeff_torus g v a
      _ = toricOriginalSectionCoeff g v
          (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
            ((latticeCharacter (toricCartierDatum D v - toricCartierDatum D w) a : ℂ) *
              (latticeCharacter (toricCartierDatum D w) a : ℂ)) := by rw [hchar]
      _ = _ := by ring)
  exact hall ⟨hv, hw⟩

/-- Actual physical values in the independently constructed native bundle.
The fixed-chart reading is proved below; the raw preferred-index choice
need not be continuous in a product topology. -/
def toricOriginalSectionNativeValue {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (g : toricSections D) (p : PolytopeToricVariety γ hs) : ToricNativeLineFiber h p :=
  let v := toricNativePreferredVertex γ hs p
  (toricNativeFrameCoefficient h v p)⁻¹ *
    toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v p)

/-- EVERY fixed ORIGINAL holomorphic frame reads the SAME given entire
coefficient, even when the pointwise chosen physical unit frame changes. -/
theorem toricOriginalSectionNativeValue_coefficient {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : toricSections D) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((toricNativeLineTrivialization h v) ⟨p, toricOriginalSectionNativeValue h g p⟩).2 =
      toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v p) := by
  let i := toricNativePreferredVertex γ hs p
  have hi : p ∈ (originalPolytopeNativeModelChart γ hs i).source := toricNativePreferredVertex_mem p
  have hsigma := toricNativeFrameCoefficient_transition h i v hi hv
  have hcoeff := toricOriginalSectionCoeff_transition g i v hi hv
  change toricNativeFrameCoefficient h v p *
    ((toricNativeFrameCoefficient h i p)⁻¹ *
      toricOriginalSectionCoeff g i (originalPolytopeNativeModelChart γ hs i p)) = _
  calc
    _ = toricCartierTransition D i v p *
        (toricNativeFrameCoefficient h i p * ((toricNativeFrameCoefficient h i p)⁻¹ *
          toricOriginalSectionCoeff g i (originalPolytopeNativeModelChart γ hs i p))) := by
      rw [← hsigma]
      ring
    _ = toricCartierTransition D i v p *
        toricOriginalSectionCoeff g i (originalPolytopeNativeModelChart γ hs i p) := by
      rw [← mul_assoc (toricNativeFrameCoefficient h i p),
        mul_inv_cancel₀ (toricNativeFrameCoefficient_ne_zero h i hi), one_mul]
    _ = _ := hcoeff.symm

end SGPT.Toric

end
end ToricCanonicalFragment022
/- END SGPT.Toric.ToricNativeSectionGluing -/

/- BEGIN SGPT.Toric.ToricNativeSectionRealization; source SHA256 517dbd830e5f9e9b8ed6e702599213a8277ccba0fb8fb37b4448a3af5d6cacd2 -/
section ToricCanonicalFragment023

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual glued physical values form a genuine global native
holomorphic section, proved in a fixed original frame near every point. -/
theorem contMDiff_toricOriginalSectionNativeValue {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : toricSections D) :
    ContMDiff (𝓘(ℂ, ComplexModel n)) ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun p : PolytopeToricVariety γ hs =>
        (⟨p, toricOriginalSectionNativeValue h g p⟩ : TotalSpace ℂ (ToricNativeLineFiber h))) := by
  intro p
  let v := toricNativePreferredVertex γ hs p
  let e := toricNativeLineTrivialization h v
  let C : OpenPartialHomeomorph (PolytopeToricVariety γ hs) (ComplexModel n) :=
    (polytopeToricVertexChart γ hs v).val
  have hv : p ∈ C.source := toricNativePreferredVertex_mem p
  have hbase : p ∈ e.baseSet := hv
  apply (e.contMDiffAt_section_iff hbase).mpr
  have hf : ContDiff ℂ ∞ (toricOriginalSectionCoeff g v) :=
    contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex
      (differentiable_toricOriginalSectionCoeff g v).differentiableOn isOpen_univ)
  have hmem : C ∈ IsManifold.maximalAtlas (𝓘(ℂ, ComplexModel n)) ∞
      (PolytopeToricVariety γ hs) :=
    IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (M := PolytopeToricVariety γ hs) (polytopeToricVertexChart γ hs v).property
  have hchart := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
    (M := PolytopeToricVariety γ hs) hmem hv
  have hcoeff := (hf.contMDiff (C p)).comp p hchart
  apply hcoeff.congr_of_eventuallyEq
  filter_upwards [C.open_source.mem_nhds hv] with q hq
  exact toricOriginalSectionNativeValue_coefficient h g v hq

def toricNativeSectionOfToric {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (g : toricSections D) : ToricNativeHolomorphicSections h where
  toFun := toricOriginalSectionNativeValue h g
  contMDiff_toFun := contMDiff_toricOriginalSectionNativeValue h g

theorem toricNativeSectionRestriction_ofToric {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : toricSections D) :
    toricNativeSectionRestriction h (toricNativeSectionOfToric h g) = g := by
  apply Subtype.ext
  funext a
  change ((toricNativeLineTrivialization h (polytopeToricBaseVertex γ))
      ⟨polytopeToricEmbedding γ hs a, toricOriginalSectionNativeValue h g
        (polytopeToricEmbedding γ hs a)⟩).2 *
      (latticeCharacter (toricCartierDatum D (polytopeToricBaseVertex γ)) a : ℂ) = g.val a
  rw [toricOriginalSectionNativeValue_coefficient h g (polytopeToricBaseVertex γ)
    (toricNativeEmbedding_mem_chartSource (polytopeToricBaseVertex γ) a)]
  exact (toricOriginalSectionCoeff_torus g (polytopeToricBaseVertex γ) a).symm

/-- The full physical native H0 and the independently defined FULL original
Cartier section space are genuinely linearly equivalent. Neither carrier
was defined as the other side and there is no incoming H0 certificate. -/
def toricNativeFullSectionEquiv {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    ToricNativeHolomorphicSections h ≃ₗ[ℂ] toricSections D :=
  LinearEquiv.ofBijective (toricNativeSectionRestriction h)
    ⟨toricNativeSectionRestriction_injective h,
      fun g => ⟨toricNativeSectionOfToric h g, toricNativeSectionRestriction_ofToric h g⟩⟩

theorem toricNativeFullSectionEquiv_symm_apply {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : toricSections D) :
    (toricNativeFullSectionEquiv h).symm g = toricNativeSectionOfToric h g := by
  apply (toricNativeFullSectionEquiv h).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (toricNativeSectionRestriction_ofToric h g).symm

theorem toricNativeFullSectionEquiv_symm_coefficient {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : toricSections D) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((toricNativeLineTrivialization h v) ⟨p, (toricNativeFullSectionEquiv h).symm g p⟩).2 =
      toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v p) := by
  rw [toricNativeFullSectionEquiv_symm_apply]
  exact toricOriginalSectionNativeValue_coefficient h g v hv

/-- Exact original physical norm of EVERY section, in every original
frame, manufactured from the independent native geometry and dictionary. -/
theorem toricNativeFullSectionEquiv_symm_norm_sq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : toricSections D) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ‖(toricNativeFullSectionEquiv h).symm g p‖ ^ 2 =
      ‖toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v p)‖ ^ 2 *
        Real.exp (-h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
  rw [toricNativeLine_norm_sq_eq_coordinates h v hv,
    toricNativeFullSectionEquiv_symm_coefficient h g v hv]

end SGPT.Toric

end
end ToricCanonicalFragment023
/- END SGPT.Toric.ToricNativeSectionRealization -/

/- BEGIN SGPT.Toric.ToricNativeDegreeGeometry; source SHA256 181a972e6b4073983deda4fed1d7f6f14845ff1b7cd54f81318bb7b619b3c637 -/
section ToricCanonicalFragment024

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The genuine all-degree source tensor power, including its literal
scalar-unit tensor at degree zero, rather than a reassigned H0 carrier. -/
def toricNativeDegreeBundle {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ) :
    HermitianHolomorphicLineBundle n (PolytopeToricVariety γ hs) :=
  twistedPower (toricNativeHermitianLineBundle h) unit q

abbrev ToricNativeDegreeSections {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ) :=
  twistedSections (toricNativeHermitianLineBundle h) unit q

def toricNativeDegreeFrame {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (q : ℕ) : AtlasFrame (toricNativeDegreeBundle h q) :=
  twistedPowerAtlasFrame (toricNativeLineAtlasFrame h v) unitAtlasFrame q

theorem toricNativeDegreeFrame_mem {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (q : ℕ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    p ∈ (toricNativeDegreeFrame h v q).val.baseSet :=
  twistedPowerAtlasFrame_mem (toricNativeLineAtlasFrame h v) unitAtlasFrame hv
    (mem_univ p) q

/-- The actual original native frame coordinate change is the SAME
Cartier transition, derived from the constructed native partial maps. -/
theorem toricNativeLineFrame_transition {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v w : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    ((toricNativeLineAtlasFrame h v).val.coordChangeL ℂ
      (toricNativeLineAtlasFrame h w).val p) 1 = toricCartierTransition D v w p := by
  rw [Trivialization.coordChangeL_apply _ _ ⟨hv, hw⟩]
  change ((toricNativeLineTrivialization h w)
    ⟨p, (toricNativeLineTrivialization h v).symm p 1⟩).2 = _
  rw [toricNativeLineTrivialization_symm h v hv]
  change toricNativeFrameCoefficient h w p *
    ((toricNativeFrameCoefficient h v p)⁻¹ * 1) = _
  rw [← toricNativeFrameCoefficient_transition h v w hv hw]
  field_simp [toricNativeFrameCoefficient_ne_zero h v hv]

theorem toricNativeUnitFrame_transition (p : PolytopeToricVariety γ hs) :
    ((unitAtlasFrame (n := n) (M := PolytopeToricVariety γ hs)).val.coordChangeL ℂ
      unitAtlasFrame.val p) 1 = 1 := by
  change ((Bundle.Trivial.trivialization (PolytopeToricVariety γ hs) ℂ).coordChangeL ℂ
    (Bundle.Trivial.trivialization (PolytopeToricVariety γ hs) ℂ) p) 1 = 1
  rw [Bundle.Trivial.trivialization.coordChangeL]
  rfl

/-- Literal actual tensor frame geometry at EVERY degree. -/
theorem toricNativeDegreeFrame_transition {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v w : latticePolytopeVertices γ) (q : ℕ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    ((toricNativeDegreeFrame h v q).val.coordChangeL ℂ
      (toricNativeDegreeFrame h w q).val p) 1 = toricCartierTransition D v w p ^ q := by
  have ht := twistedPower_frame_transition (toricNativeLineAtlasFrame h v)
    (toricNativeLineAtlasFrame h w) unitAtlasFrame unitAtlasFrame hv hw
      (mem_univ p) (mem_univ p) q
  exact ht.trans ((congrArg₂ (fun a b : ℂ => a ^ q * b)
    (toricNativeLineFrame_transition h v w hv hw) (toricNativeUnitFrame_transition p)).trans
      (mul_one _))

/-- The source integral Cartier datum of qD gives exactly the same degree
q overlap multiplier, on ALL actual original overlaps, including q=0. -/
theorem toricCartierTransition_smul_nat (D : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) (q : ℕ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    toricCartierTransition ((q : ℤ) • D) v w p = toricCartierTransition D v w p ^ q := by
  let U := (originalPolytopeNativeModelChart γ hs v).source ∩
    (originalPolytopeNativeModelChart γ hs w).source
  have hU : IsOpen U := (originalPolytopeNativeModelChart γ hs v).open_source.inter
    (originalPolytopeNativeModelChart γ hs w).open_source
  apply toricCartier_eqOn_of_denseTorus U hU _ _
    (continuousOn_toricCartierTransition ((q : ℤ) • D) v w)
    ((continuousOn_toricCartierTransition D v w).pow q) ?_ ⟨hv, hw⟩
  intro a _
  change toricCartierTransition ((q : ℤ) • D) v w (polytopeToricEmbedding γ hs a) =
    toricCartierTransition D v w (polytopeToricEmbedding γ hs a) ^ q
  rw [toricCartierTransition_embedding, toricCartierTransition_embedding,
    toricCartierDatum_smul, toricCartierDatum_smul, ← smul_sub,
    latticeCharacter_zsmul]
  simp only [zpow_natCast, Units.val_pow_eq_pow_val]

theorem toricNativeDegreeFrame_transition_cartier {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v w : latticePolytopeVertices γ) (q : ℕ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    ((toricNativeDegreeFrame h v q).val.coordChangeL ℂ
      (toricNativeDegreeFrame h w q).val p) 1 =
        toricCartierTransition ((q : ℤ) • D) v w p := by
  rw [toricNativeDegreeFrame_transition h v w q hv hw,
    toricCartierTransition_smul_nat D v w q hv hw]

theorem toricNativeUnitFrame_norm (p : PolytopeToricVariety γ hs) :
    ‖(unitAtlasFrame (n := n) (M := PolytopeToricVariety γ hs)).val.symm p 1‖ = 1 := by
  change ‖(Bundle.Trivial.trivialization (PolytopeToricVariety γ hs) ℂ).symm p 1‖ = 1
  rw [Bundle.Trivial.trivialization_symm_apply, norm_one]


theorem toricNativeDegreeSection_norm_sq {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (q : ℕ) (s : ToricNativeDegreeSections h q)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ‖s p‖ ^ 2 = ‖((toricNativeDegreeFrame h v q).val ⟨p, s p⟩).2‖ ^ 2 *
      Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
  have hn := twistedSection_norm_sq_frame (toricNativeLineAtlasFrame h v) unitAtlasFrame q s hv
    (mem_univ p)
  rw [toricNativeUnitFrame_norm, one_pow, mul_one] at hn
  change ‖s p‖ ^ 2 = ‖((toricNativeDegreeFrame h v q).val ⟨p, s p⟩).2‖ ^ 2 *
    (‖(toricNativeLineTrivialization h v).symm p 1‖ ^ 2) ^ q at hn
  have hexp : (‖(toricNativeLineTrivialization h v).symm p 1‖ ^ 2) ^ q =
      Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
    rw [toricNativeLineTrivialization_frame_norm_sq h v hv, ← Real.exp_nat_mul]
    congr 1
    ring
  exact hn.trans (congrArg
    (fun r : ℝ => ‖((toricNativeDegreeFrame h v q).val ⟨p, s p⟩).2‖ ^ 2 * r) hexp)

end SGPT.Toric

end
end ToricCanonicalFragment024
/- END SGPT.Toric.ToricNativeDegreeGeometry -/

/- BEGIN SGPT.Toric.ToricNativeDegreeSectionCoefficients; source SHA256 4e51f8ff19941ed2dad41c137a799cb83ed22cd23f1bdd64bedb7fe2caf14260 -/
section ToricCanonicalFragment025

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

def toricNativeDegreeSectionFrameCoeff {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) (v : latticePolytopeVertices γ) (s : ToricNativeDegreeSections h q)
    (p : PolytopeToricVariety γ hs) : ℂ :=
  ((toricNativeDegreeFrame h v q).val ⟨p, s p⟩).2

def toricNativeDegreeSectionChartCoeff {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) (v : latticePolytopeVertices γ) (s : ToricNativeDegreeSections h q)
    (z : ComplexModel n) : ℂ :=
  toricNativeDegreeSectionFrameCoeff h q v s
    ((originalPolytopeNativeModelChart γ hs v).symm z)

/-- EVERY section of the actual literal degree-q tensor bundle has an
entire original vertex coefficient, including degree zero. -/
theorem differentiable_toricNativeDegreeSectionChartCoeff {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (v : latticePolytopeVertices γ)
    (s : ToricNativeDegreeSections h q) :
    Differentiable ℂ (toricNativeDegreeSectionChartCoeff h q v s) := by
  intro z
  let C : OpenPartialHomeomorph (PolytopeToricVariety γ hs) (ComplexModel n) :=
    (polytopeToricVertexChart γ hs v).val
  let e := (toricNativeDegreeFrame h v q).val
  have hz : z ∈ C.target := by
    change z ∈ (originalPolytopeNativeModelChart γ hs v).target
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  have hp : C.symm z ∈ e.baseSet := toricNativeDegreeFrame_mem h v q (C.map_target hz)
  have hcoeff : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞
      (toricNativeDegreeSectionFrameCoeff h q v s) (C.symm z) :=
    (e.contMDiffAt_section_iff hp).mp (s.contMDiff (C.symm z))
  have hmem : C ∈ IsManifold.maximalAtlas (𝓘(ℂ, ComplexModel n)) ∞
      (PolytopeToricVariety γ hs) :=
    IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (M := PolytopeToricVariety γ hs) (polytopeToricVertexChart γ hs v).property
  have hchart : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ComplexModel n)) ∞ C.symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (M := PolytopeToricVariety γ hs) hmem hz
  exact (contMDiffAt_iff_contDiffAt.mp (hcoeff.comp z hchart)).differentiableAt (by simp)

theorem toricNativeDegreeSectionChartCoeff_chart_apply {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (v : latticePolytopeVertices γ)
    (s : ToricNativeDegreeSections h q) {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    toricNativeDegreeSectionChartCoeff h q v s (originalPolytopeNativeModelChart γ hs v p) =
      toricNativeDegreeSectionFrameCoeff h q v s p := by
  unfold toricNativeDegreeSectionChartCoeff
  rw [(originalPolytopeNativeModelChart γ hs v).left_inv hp]

/-- The actual linear coordinate change on the literal tensor fiber is
the independently produced original qD Cartier scalar on all overlaps. -/
theorem toricNativeDegreeFrame_change_apply {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (v w : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) (z : ℂ) :
    ((toricNativeDegreeFrame h v q).val.coordChangeL ℂ
      (toricNativeDegreeFrame h w q).val p) z =
        toricCartierTransition ((q : ℤ) • D) v w p * z := by
  let A := (toricNativeDegreeFrame h v q).val.coordChangeL ℂ
    (toricNativeDegreeFrame h w q).val p
  calc
    A z = A (z • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
    _ = z • A 1 := A.map_smul z 1
    _ = _ := by
      rw [toricNativeDegreeFrame_transition_cartier h v w q hv hw, smul_eq_mul]
      exact mul_comm _ _

theorem toricNativeDegreeSectionFrameCoeff_transition {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (v w : latticePolytopeVertices γ)
    (s : ToricNativeDegreeSections h q) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    toricNativeDegreeSectionFrameCoeff h q w s p =
      toricCartierTransition ((q : ℤ) • D) v w p *
        toricNativeDegreeSectionFrameCoeff h q v s p := by
  let e := (toricNativeDegreeFrame h v q).val
  let f := (toricNativeDegreeFrame h w q).val
  have he := toricNativeDegreeFrame_mem h v q hv
  have hf := toricNativeDegreeFrame_mem h w q hw
  have hh := Trivialization.coordChangeL_apply (R := ℂ) e f ⟨he, hf⟩ (e ⟨p, s p⟩).2
  rw [e.symm_apply_apply_mk he] at hh
  rw [toricNativeDegreeFrame_change_apply h q v w hv hw] at hh
  exact hh.symm

end SGPT.Toric

end
end ToricCanonicalFragment025
/- END SGPT.Toric.ToricNativeDegreeSectionCoefficients -/

/- BEGIN SGPT.Toric.ToricNativeDegreeSectionRestriction; source SHA256 b79f4668bc0a3a06cd3f0c496a4488ec8dd558a6e9908431023de6b999ef9da2 -/
section ToricCanonicalFragment026

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

def toricNativeDegreeSectionTorusFunction {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) (s : ToricNativeDegreeSections h q) (a : Fin n → ℂˣ) : ℂ :=
  toricNativeDegreeSectionFrameCoeff h q (polytopeToricBaseVertex γ) s
    (polytopeToricEmbedding γ hs a) *
      latticeCharacter (toricCartierDatum ((q : ℤ) • D) (polytopeToricBaseVertex γ)) a

theorem toricNativeDegreeSectionTorusFunction_eq_chartCoeff {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (v : latticePolytopeVertices γ)
    (s : ToricNativeDegreeSections h q) (a : Fin n → ℂˣ) :
    toricNativeDegreeSectionTorusFunction h q s a =
      toricNativeDegreeSectionChartCoeff h q v s
        (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
          latticeCharacter (toricCartierDatum ((q : ℤ) • D) v) a := by
  let E := (q : ℤ) • D
  let w := polytopeToricBaseVertex γ
  have hv := toricNativeEmbedding_mem_chartSource (hs := hs) v a
  have hw := toricNativeEmbedding_mem_chartSource (hs := hs) w a
  rw [toricNativeDegreeSectionChartCoeff_chart_apply h q v s hv]
  have hc := toricNativeDegreeSectionFrameCoeff_transition h q v w s hv hw
  rw [toricCartierTransition_embedding] at hc
  change toricNativeDegreeSectionFrameCoeff h q w s (polytopeToricEmbedding γ hs a) *
    (latticeCharacter (toricCartierDatum E w) a : ℂ) = _
  rw [hc]
  have hchar : (latticeCharacter (toricCartierDatum E v - toricCartierDatum E w) a : ℂ) *
      (latticeCharacter (toricCartierDatum E w) a : ℂ) =
        (latticeCharacter (toricCartierDatum E v) a : ℂ) := by
    have hvec : (toricCartierDatum E v - toricCartierDatum E w) + toricCartierDatum E w =
      toricCartierDatum E v := by abel
    have hh := congrArg (fun z : ℂˣ => (z : ℂ))
      (latticeCharacter_add (toricCartierDatum E v - toricCartierDatum E w)
        (toricCartierDatum E w) a)
    simpa only [Units.val_mul, hvec] using hh.symm
  calc
    _ = toricNativeDegreeSectionFrameCoeff h q v s (polytopeToricEmbedding γ hs a) *
      ((latticeCharacter (toricCartierDatum E v - toricCartierDatum E w) a : ℂ) *
        (latticeCharacter (toricCartierDatum E w) a : ℂ)) := by ring
    _ = _ := by rw [hchar]

theorem toricNativeDegreeSectionTorusFunction_mem {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (s : ToricNativeDegreeSections h q) :
    toricNativeDegreeSectionTorusFunction h q s ∈ toricSections ((q : ℤ) • D) := by
  intro v
  exact ⟨toricNativeDegreeSectionChartCoeff h q v s,
    differentiable_toricNativeDegreeSectionChartCoeff h q v s,
    toricNativeDegreeSectionTorusFunction_eq_chartCoeff h q v s⟩

theorem toricNativeDegreeFrame_coefficient_add {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (s t : (toricNativeDegreeBundle h q).Fiber p) :
    ((toricNativeDegreeFrame h v q).val ⟨p, s + t⟩).2 =
      ((toricNativeDegreeFrame h v q).val ⟨p, s⟩).2 +
        ((toricNativeDegreeFrame h v q).val ⟨p, t⟩).2 := by
  let e := (toricNativeDegreeFrame h v q).val
  have he := toricNativeDegreeFrame_mem h v q hv
  have hread (z : (toricNativeDegreeBundle h q).Fiber p) :
      (e.linearMapAt ℂ p) z = (e ⟨p, z⟩).2 :=
    congrFun (Trivialization.coe_linearMapAt_of_mem e he) z
  exact (hread (s + t)).symm.trans
    (((e.linearMapAt ℂ p).map_add s t).trans (congrArg₂ (· + ·) (hread s) (hread t)))

theorem toricNativeDegreeFrame_coefficient_smul {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (c : ℂ) (s : (toricNativeDegreeBundle h q).Fiber p) :
    ((toricNativeDegreeFrame h v q).val ⟨p, c • s⟩).2 =
      c • ((toricNativeDegreeFrame h v q).val ⟨p, s⟩).2 := by
  let e := (toricNativeDegreeFrame h v q).val
  have he := toricNativeDegreeFrame_mem h v q hv
  have hread (z : (toricNativeDegreeBundle h q).Fiber p) :
      (e.linearMapAt ℂ p) z = (e ⟨p, z⟩).2 :=
    congrFun (Trivialization.coe_linearMapAt_of_mem e he) z
  exact (hread (c • s)).symm.trans
    (((e.linearMapAt ℂ p).map_smul c s).trans (congrArg (c • ·) (hread s)))

/-- Restriction of ALL actual literal source tensor sections to the
independently defined full degree-q original Cartier section space. -/
def toricNativeDegreeSectionRestriction {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) :
    ToricNativeDegreeSections h q →ₗ[ℂ] toricSections ((q : ℤ) • D) where
  toFun s := ⟨toricNativeDegreeSectionTorusFunction h q s,
    toricNativeDegreeSectionTorusFunction_mem h q s⟩
  map_add' s t := by
    apply Subtype.ext
    funext a
    change ((toricNativeDegreeFrame h (polytopeToricBaseVertex γ) q).val
        ⟨polytopeToricEmbedding γ hs a,
          s (polytopeToricEmbedding γ hs a) + t (polytopeToricEmbedding γ hs a)⟩).2 * _ = _
    rw [toricNativeDegreeFrame_coefficient_add h q (polytopeToricBaseVertex γ)
      (toricNativeEmbedding_mem_chartSource (polytopeToricBaseVertex γ) a), add_mul]
    rfl
  map_smul' c s := by
    apply Subtype.ext
    funext a
    change ((toricNativeDegreeFrame h (polytopeToricBaseVertex γ) q).val
        ⟨polytopeToricEmbedding γ hs a, c • s (polytopeToricEmbedding γ hs a)⟩).2 * _ = _
    rw [toricNativeDegreeFrame_coefficient_smul h q (polytopeToricBaseVertex γ)
      (toricNativeEmbedding_mem_chartSource (polytopeToricBaseVertex γ) a), smul_eq_mul]
    change (c * _) * _ = c * (_ * _)
    exact mul_assoc _ _ _

theorem toricNativeDegreeSectionRestriction_injective {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) : Function.Injective (toricNativeDegreeSectionRestriction h q) := by
  intro s t hst
  have hg : toricNativeDegreeSectionTorusFunction h q s =
      toricNativeDegreeSectionTorusFunction h q t := congrArg Subtype.val hst
  ext p
  let v := toricNativePreferredVertex γ hs p
  have hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source := toricNativePreferredVertex_mem p
  have hf : toricNativeDegreeSectionChartCoeff h q v s =
      toricNativeDegreeSectionChartCoeff h q v t := by
    apply toricSectionCoeff_unique ((q : ℤ) • D) v
      (differentiable_toricNativeDegreeSectionChartCoeff h q v s).continuous
      (differentiable_toricNativeDegreeSectionChartCoeff h q v t).continuous
      (toricNativeDegreeSectionTorusFunction_eq_chartCoeff h q v s)
    intro a
    rw [hg]
    exact toricNativeDegreeSectionTorusFunction_eq_chartCoeff h q v t a
  have hp := congrFun hf (originalPolytopeNativeModelChart γ hs v p)
  rw [toricNativeDegreeSectionChartCoeff_chart_apply h q v s hv,
    toricNativeDegreeSectionChartCoeff_chart_apply h q v t hv] at hp
  have he := toricNativeDegreeFrame_mem h v q hv
  have hh := congrArg ((toricNativeDegreeFrame h v q).val.symm p) hp
  simpa only [toricNativeDegreeSectionFrameCoeff,
    Trivialization.symm_apply_apply_mk _ he] using hh

end SGPT.Toric

end
end ToricCanonicalFragment026
/- END SGPT.Toric.ToricNativeDegreeSectionRestriction -/

/- BEGIN SGPT.Toric.ToricNativeDegreeSectionRealization; source SHA256 c316f7a2171ed723e729b334e12e06f50af05ff5193a4b747c0852fa740b4979 -/
section ToricCanonicalFragment027

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- A value in the actual literal source tensor fiber, using one actual
original tensor frame. No section carrier is reassigned or restricted. -/
def toricOriginalDegreeSectionNativeValue {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (g : toricSections ((q : ℤ) • D))
    (p : PolytopeToricVariety γ hs) : (toricNativeDegreeBundle h q).Fiber p :=
  let i := toricNativePreferredVertex γ hs p
  (toricNativeDegreeFrame h i q).val.symm p
    (toricOriginalSectionCoeff g i (originalPolytopeNativeModelChart γ hs i p))

/-- EVERY fixed original tensor frame reads the independently given
entire qD coefficient on its whole original chart, including boundary. -/
theorem toricOriginalDegreeSectionNativeValue_coefficient {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (g : toricSections ((q : ℤ) • D))
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((toricNativeDegreeFrame h v q).val ⟨p, toricOriginalDegreeSectionNativeValue h q g p⟩).2 =
      toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v p) := by
  let i := toricNativePreferredVertex γ hs p
  have hi : p ∈ (originalPolytopeNativeModelChart γ hs i).source := toricNativePreferredVertex_mem p
  have hchange := Trivialization.coordChangeL_apply (R := ℂ) (toricNativeDegreeFrame h i q).val
    (toricNativeDegreeFrame h v q).val
    ⟨toricNativeDegreeFrame_mem h i q hi, toricNativeDegreeFrame_mem h v q hv⟩
    (toricOriginalSectionCoeff g i (originalPolytopeNativeModelChart γ hs i p))
  rw [toricNativeDegreeFrame_change_apply h q i v hi hv] at hchange
  exact hchange.symm.trans (toricOriginalSectionCoeff_transition g i v hi hv).symm

theorem contMDiff_toricOriginalDegreeSectionNativeValue {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (g : toricSections ((q : ℤ) • D)) :
    ContMDiff (𝓘(ℂ, ComplexModel n)) ((𝓘(ℂ, ComplexModel n)).prod (𝓘(ℂ, ℂ))) ∞
      (fun p : PolytopeToricVariety γ hs =>
        (⟨p, toricOriginalDegreeSectionNativeValue h q g p⟩ :
          TotalSpace ℂ (toricNativeDegreeBundle h q).Fiber)) := by
  intro p
  let v := toricNativePreferredVertex γ hs p
  let e := (toricNativeDegreeFrame h v q).val
  let C : OpenPartialHomeomorph (PolytopeToricVariety γ hs) (ComplexModel n) :=
    (polytopeToricVertexChart γ hs v).val
  have hv : p ∈ C.source := toricNativePreferredVertex_mem p
  have hbase : p ∈ e.baseSet := toricNativeDegreeFrame_mem h v q hv
  apply (e.contMDiffAt_section_iff hbase).mpr
  have hf : ContDiff ℂ ∞ (toricOriginalSectionCoeff g v) :=
    contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex
      (differentiable_toricOriginalSectionCoeff g v).differentiableOn isOpen_univ)
  have hmem : C ∈ IsManifold.maximalAtlas (𝓘(ℂ, ComplexModel n)) ∞
      (PolytopeToricVariety γ hs) :=
    IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (M := PolytopeToricVariety γ hs) (polytopeToricVertexChart γ hs v).property
  have hchart := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
    (M := PolytopeToricVariety γ hs) hmem hv
  have hcoeff := (hf.contMDiff (C p)).comp p hchart
  apply hcoeff.congr_of_eventuallyEq
  filter_upwards [C.open_source.mem_nhds hv] with r hr
  exact toricOriginalDegreeSectionNativeValue_coefficient h q g v hr

def toricNativeDegreeSectionOfToric {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) (g : toricSections ((q : ℤ) • D)) : ToricNativeDegreeSections h q where
  toFun := toricOriginalDegreeSectionNativeValue h q g
  contMDiff_toFun := contMDiff_toricOriginalDegreeSectionNativeValue h q g

theorem toricNativeDegreeSectionRestriction_ofToric {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (g : toricSections ((q : ℤ) • D)) :
    toricNativeDegreeSectionRestriction h q (toricNativeDegreeSectionOfToric h q g) = g := by
  apply Subtype.ext
  funext a
  change ((toricNativeDegreeFrame h (polytopeToricBaseVertex γ) q).val
    ⟨polytopeToricEmbedding γ hs a, toricOriginalDegreeSectionNativeValue h q g
      (polytopeToricEmbedding γ hs a)⟩).2 *
      (latticeCharacter (toricCartierDatum ((q : ℤ) • D) (polytopeToricBaseVertex γ)) a : ℂ) =
        g.val a
  rw [toricOriginalDegreeSectionNativeValue_coefficient h q g (polytopeToricBaseVertex γ)
    (toricNativeEmbedding_mem_chartSource (polytopeToricBaseVertex γ) a)]
  exact (toricOriginalSectionCoeff_torus g (polytopeToricBaseVertex γ) a).symm

/-- ALL actual degree-q source tensor sections are linearly equivalent
to ALL original qD Cartier sections. Both carriers are independent and
q=0 is the actual tensor unit, including when P_D is empty. -/
def toricNativeDegreeFullSectionEquiv {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ) :
    ToricNativeDegreeSections h q ≃ₗ[ℂ] toricSections ((q : ℤ) • D) :=
  LinearEquiv.ofBijective (toricNativeDegreeSectionRestriction h q)
    ⟨toricNativeDegreeSectionRestriction_injective h q,
      fun g => ⟨toricNativeDegreeSectionOfToric h q g,
        toricNativeDegreeSectionRestriction_ofToric h q g⟩⟩

theorem toricNativeDegreeFullSectionEquiv_symm_apply {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (g : toricSections ((q : ℤ) • D)) :
    (toricNativeDegreeFullSectionEquiv h q).symm g = toricNativeDegreeSectionOfToric h q g := by
  apply (toricNativeDegreeFullSectionEquiv h q).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (toricNativeDegreeSectionRestriction_ofToric h q g).symm

theorem toricNativeDegreeFullSectionEquiv_symm_coefficient {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (g : toricSections ((q : ℤ) • D))
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((toricNativeDegreeFrame h v q).val ⟨p, (toricNativeDegreeFullSectionEquiv h q).symm g p⟩).2 =
      toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v p) := by
  rw [toricNativeDegreeFullSectionEquiv_symm_apply]
  exact toricOriginalDegreeSectionNativeValue_coefficient h q g v hv

/-- Exact physical norm for EVERY original Cartier section, on the
actual source tensor bundle and every original native chart. -/
theorem toricNativeDegreeFullSectionEquiv_symm_norm_sq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (g : toricSections ((q : ℤ) • D))
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ‖(toricNativeDegreeFullSectionEquiv h q).symm g p‖ ^ 2 =
      ‖toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v p)‖ ^ 2 *
        Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
  rw [toricNativeDegreeSection_norm_sq h v q _ hv,
    toricNativeDegreeFullSectionEquiv_symm_coefficient h q g v hv]

end SGPT.Toric

end
end ToricCanonicalFragment027
/- END SGPT.Toric.ToricNativeDegreeSectionRealization -/

/- BEGIN SGPT.Toric.ToricNativeDegreeSectionTorusNorm; source SHA256 9f599aaf13971b8aa6eff6c31ac68d8c52a9d80df837aecd07cdbd92d7f28874 -/
section ToricCanonicalFragment031

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}



/-- An actual physical section of the original literal tensor power,
manufactured from the independently proved full Cartier character. -/
def toricNativeDegreeMonomialSection {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints ((q : ℤ) • D)) :
    ToricNativeDegreeSections h q :=
  (toricNativeDegreeFullSectionEquiv h q).symm
    ⟨fun a => (latticeCharacter m a : ℂ), latticeCharacter_mem_toricSections _ hm⟩



end SGPT.Toric

end
end ToricCanonicalFragment031
/- END SGPT.Toric.ToricNativeDegreeSectionTorusNorm -/

/- BEGIN SGPT.Toric.ToricNativePlainPowerSections; source SHA256 a1634b781b92e3548743fddcf06476bc587e3e401991621c660d515a257ecb22 -/
section ToricCanonicalFragment032

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeRightUnit
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The literal plain source powers: the genuine scalar-unit bundle at
zero and the genuine positivePower L k at degree k+1. -/
def toricNativePlainPowerBundle {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    ℕ → HermitianHolomorphicLineBundle n (PolytopeToricVariety γ hs)
  | 0 => unit
  | k + 1 => positivePower (toricNativeHermitianLineBundle h) k

abbrev ToricNativePlainPowerSections {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ) :=
  SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := n) (toricNativePlainPowerBundle h q).Fiber

/-- A genuine actual full-section equivalence, built from the physical
right-unit section maps rather than a supplied fiber compatibility. -/
def toricNativePlainPowerRightUnitEquiv {D : ToricDivisor γ hs} (h : BigToricMetric D) :
    ∀ q : ℕ, ToricNativeDegreeSections h q ≃ₗ[ℂ] ToricNativePlainPowerSections h q
  | 0 => nativeRightUnitSectionsEquiv unit
  | k + 1 => nativeRightUnitSectionsEquiv (positivePower (toricNativeHermitianLineBundle h) k)

theorem toricNativePlainPowerRightUnitEquiv_norm {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (s : ToricNativeDegreeSections h q)
    (p : PolytopeToricVariety γ hs) :
    ‖toricNativePlainPowerRightUnitEquiv h q s p‖ = ‖s p‖ := by
  cases q with
  | zero => exact nativeRightUnitSectionsEquiv_norm unit s p
  | succ k =>
    exact nativeRightUnitSectionsEquiv_norm
      (positivePower (toricNativeHermitianLineBundle h) k) s p

/-- The book's plain actual H0(L^q), including actual unit degree0, is
equivalent to the independent FULL original qD Cartier section space. -/
def toricNativePlainPowerFullSectionEquiv {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ) :
    ToricNativePlainPowerSections h q ≃ₗ[ℂ] toricSections ((q : ℤ) • D) :=
  (toricNativePlainPowerRightUnitEquiv h q).symm.trans (toricNativeDegreeFullSectionEquiv h q)

theorem toricNativePlainPowerFullSectionEquiv_symm_norm_sq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (g : toricSections ((q : ℤ) • D))
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ‖(toricNativePlainPowerFullSectionEquiv h q).symm g p‖ ^ 2 =
      ‖toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v p)‖ ^ 2 *
        Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
  change ‖toricNativePlainPowerRightUnitEquiv h q
    ((toricNativeDegreeFullSectionEquiv h q).symm g) p‖ ^ 2 = _
  rw [toricNativePlainPowerRightUnitEquiv_norm,
    toricNativeDegreeFullSectionEquiv_symm_norm_sq h q g v hv]


def toricNativePlainPowerMonomialSection {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (q : ℕ) {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints ((q : ℤ) • D)) :
    ToricNativePlainPowerSections h q :=
  (toricNativePlainPowerFullSectionEquiv h q).symm
    ⟨fun a => (latticeCharacter m a : ℂ), latticeCharacter_mem_toricSections _ hm⟩



end SGPT.Toric

end
end ToricCanonicalFragment032
/- END SGPT.Toric.ToricNativePlainPowerSections -/

/- BEGIN SGPT.Toric.ToricNativeRawKahlerDensity; source SHA256 3e158549d153d5b2ab010326b003b6ddf02c438fdff56fefd1c86cf80136658e -/
section ToricCanonicalFragment040

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
open scoped Topology ContDiff BigOperators ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The EXACT original raw Kähler-volume chart density, with no normalization. -/
def toricNativeRawKahlerChartDensity (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ComplexModel n → ENNReal :=
  chartDensity (fun _ => (polytopeToricKahlerBackground γ hs).form)
    (polytopeToricVertexChart γ hs v)

/-- The original chart density is the top power of the ACTUAL Guillemin form
in the SAME original entire vertex chart, including all boundary points. -/
theorem toricNativeRawKahlerChartDensity_eq_topPower
    (v : latticePolytopeVertices γ) (z : ComplexModel n) :
    toricNativeRawKahlerChartDensity γ hs v z = ENNReal.ofReal
      (actualTopPowerDensity (smoothDDC (originalGuilleminGeometricNativeWeight γ hs v) z)) := by
  unfold toricNativeRawKahlerChartDensity chartDensity
  rw [actualMixedTopDensity_const]
  exact congrArg (fun F => ENNReal.ofReal (actualTopPowerDensity F))
    (originalGuilleminClosedForm_native_coeff γ hs v z)

/-- Measurability comes from the actual smooth Kähler form on the whole
native chart, not a prescribed invariant-density certificate. -/
theorem measurable_toricNativeRawKahlerChartDensity (v : latticePolytopeVertices γ) :
    Measurable (toricNativeRawKahlerChartDensity γ hs v) := by
  have hc := continuousOn_chartDensity
    (fun _ => (polytopeToricKahlerBackground γ hs).form) (polytopeToricVertexChart γ hs v)
  have ht : (polytopeToricVertexChart γ hs v).val.target = univ :=
    originalPolytopeNativeComplexChart_target γ hs _
  rw [ht] at hc
  exact (continuousOn_univ.mp hc).measurable

/-- The actual compact chart action has real determinant ONE. Isometry
gives absolute determinant one and complex linearity supplies its sign. -/
theorem toricNativeCompactVertexAction_realDet_eq_one
    (v : latticePolytopeVertices γ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a) :
    LinearMap.det ((originalPolytopeNativeModelActionLinear γ hs v a).toLinearMap.restrictScalars ℝ) =
      1 := by
  let A := originalPolytopeNativeModelActionLinear γ hs v a
  have habs := (vertexActionIsometry (hs := hs) v ha).toLinearIsometry.normDet_eq_one
  rw [LinearMap.normDet_eq_abs_det] at habs
  change |LinearMap.det (A.toLinearMap.restrictScalars ℝ)| = 1 at habs
  have hpos : 0 ≤ LinearMap.det (A.toLinearMap.restrictScalars ℝ) := by
    rw [normSq_det_eq_realDet]
    exact Complex.normSq_nonneg _
  rwa [abs_of_nonneg hpos] at habs

/-- The top power of the SAME original Guillemin tensor is invariant under
the actual compact chart action, including coordinate zeros and n=0. -/
theorem toricNativeGuilleminTopPower_compact_action
    (v : latticePolytopeVertices γ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a)
    (z : ComplexModel n) :
    actualTopPowerDensity (smoothDDC (originalGuilleminGeometricNativeWeight γ hs v)
      (originalPolytopeNativeModelActionLinear γ hs v a z)) =
      actualTopPowerDensity (smoothDDC (originalGuilleminGeometricNativeWeight γ hs v) z) := by
  let A := originalPolytopeNativeModelActionLinear γ hs v a
  have hp := smoothDDC_originalGuilleminGeometricNativeWeight_compact_action γ hs v a ha z
  have hder : fderiv ℝ A z = A.restrictScalars ℝ := (A.restrictScalars ℝ).fderiv
  rw [hder] at hp
  have hd := congrArg actualTopPowerDensity hp
  have hdet : LinearMap.det (A.restrictScalars ℝ).toLinearMap = 1 :=
    toricNativeCompactVertexAction_realDet_eq_one (hs := hs) v ha
  rw [actualTopPowerDensity_compContinuousLinearMap, hdet, one_mul] at hd
  exact hd

/-- The literal RAW original Kähler-volume chart density is invariant,
internally derived from the actual geometric form and actual Jacobian. -/
theorem toricNativeRawKahlerChartDensity_compact_action
    (v : latticePolytopeVertices γ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a)
    (z : ComplexModel n) :
    toricNativeRawKahlerChartDensity γ hs v (originalPolytopeNativeModelActionLinear γ hs v a z) =
      toricNativeRawKahlerChartDensity γ hs v z := by
  rw [toricNativeRawKahlerChartDensity_eq_topPower, toricNativeRawKahlerChartDensity_eq_topPower,
    toricNativeGuilleminTopPower_compact_action v ha z]

end SGPT.Toric

end
end ToricCanonicalFragment040
/- END SGPT.Toric.ToricNativeRawKahlerDensity -/

/- BEGIN SGPT.Toric.ToricNativeRawKahlerVolume; source SHA256 85fbaafbad76db26c66d705aabbe9fdaab944517e853a478e2aed4128934088c -/
section ToricCanonicalFragment041

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
open SGPT.Foundations.Analysis.Pending.NaturalHermitianKahlerVolumeCalibration
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open scoped Topology ContDiff BigOperators ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The literal raw Guillemin Kähler volume in every entire actual vertex
chart, retaining the full original space and no probability normalization. -/
theorem toricNativeRawKahlerVolume_restrict_vertex
    (v : latticePolytopeVertices γ) :
    (kahlerVolume (polytopeToricKahlerBackground γ hs)).restrict
        (polytopeToricVertexChart γ hs v).val.source =
      Measure.map (polytopeToricVertexChart γ hs v).val.symm
        (volume.withDensity (toricNativeRawKahlerChartDensity γ hs v)) := by
  have h := kahlerVolume_restrict_chart (polytopeToricKahlerBackground γ hs)
    (polytopeToricVertexChart γ hs v)
  rw [originalPolytopeNativeComplexChart_target, Measure.restrict_univ] at h
  exact h

/-- The SAME actual compact chart action preserves its derived raw-density
measure, by genuine Lebesgue change of variables and actual tensor/Jacobian
invariance, rather than an incoming volume-invariance certificate. -/
theorem toricNativeRawKahlerChart_measurePreserving
    (v : latticePolytopeVertices γ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a) :
    MeasurePreserving (vertexActionIsometry (hs := hs) v ha)
      (volume.withDensity (toricNativeRawKahlerChartDensity γ hs v))
      (volume.withDensity (toricNativeRawKahlerChartDensity γ hs v)) :=
  SGPT.Bergman.NativeSingularPhi.measurePreserving_withDensity_of_invariant
    (measurePreserving_linearIsometryEquiv_addHaar volume (vertexActionIsometry v ha))
    (measurable_toricNativeRawKahlerChartDensity v)
    (toricNativeRawKahlerChartDensity_compact_action v ha)

/-- The actual entire raw Guillemin Kähler volume is invariant under the
actual original compact torus homeomorphism.  All native boundary strata,
dimension zero, and the original unnormalized measure are retained. -/
theorem toricNativeRawKahlerVolume_measurePreserving
    {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a) :
    MeasurePreserving (polytopeToricAction γ hs a)
      (kahlerVolume (polytopeToricKahlerBackground γ hs))
      (kahlerVolume (polytopeToricKahlerBackground γ hs)) := by
  let f := polytopeToricAction γ hs a
  have hf : Measurable f := f.continuous.measurable
  refine ⟨hf, ?_⟩
  have hcover : (⋃ v : latticePolytopeVertices γ,
      (polytopeToricVertexChart γ hs v).val.source) = univ := by
    ext p
    simp only [mem_iUnion, mem_univ, iff_true]
    exact originalPolytopeNativeModelChart_cover γ hs p
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro v
  let e := polytopeToricVertexChart γ hs v
  let A := vertexActionIsometry (hs := hs) v ha
  have he : Measurable e.val.symm := by
    have hc := e.val.continuousOn_symm
    rw [originalPolytopeNativeComplexChart_target] at hc
    exact (continuousOn_univ.mp hc).measurable
  have hsource : f ⁻¹' e.val.source = e.val.source := by
    ext p
    change originalPolytopeNativeAction γ a p ∈
        (originalPolytopeNativeModelChart γ hs v).source ↔
      p ∈ (originalPolytopeNativeModelChart γ hs v).source
    rw [originalPolytopeNativeModelChart_source]
    exact originalPolytopeNativeAction_mem_chart_source_iff γ hs v a p
  have hcomm : (f : PolytopeToricVariety γ hs → PolytopeToricVariety γ hs) ∘
      e.val.symm = e.val.symm ∘ A := by
    funext z
    exact action_vertexChart_symm v a z
  change (Measure.map f (kahlerVolume (polytopeToricKahlerBackground γ hs))).restrict
      e.val.source = (kahlerVolume (polytopeToricKahlerBackground γ hs)).restrict e.val.source
  rw [Measure.restrict_map hf e.val.open_source.measurableSet, hsource,
    toricNativeRawKahlerVolume_restrict_vertex,
    Measure.map_map hf he, hcomm,
    ← Measure.map_map he A.continuous.measurable,
    (toricNativeRawKahlerChart_measurePreserving v ha).map_eq]

end SGPT.Toric

end
end ToricCanonicalFragment041
/- END SGPT.Toric.ToricNativeRawKahlerVolume -/
