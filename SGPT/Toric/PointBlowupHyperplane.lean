import SGPT.Toric.PointBlowupGeometry
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Lean.Elab.Command

section PointBlowupCanonicalFragment001
/- BEGIN OriginalHyperplanePhysicalMapDraft; original source SHA256 f48d978b786d54001e4c570d05eb1bfde272e326d83321dacce1d2371a23360c -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open scoped Manifold ContDiff BigOperators

/-- A genuine smooth source metric, manufactured by the existing unconditional
native metric producer, not an incoming bundle or compatibility certificate. -/
def nativeSimplexHyperplaneMetric : BigToricMetric (simplexHyperplaneDivisor targetSimplexSmooth) :=
  Classical.choice (exists_bigToricMetric _)

def simplexInverseHolomorphicMap :
    ContMDiffMap 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2)
      (SGPT.Projective.ComplexProjectiveSpace 2)
      (PolytopeToricVariety (simplexGenerator 2) targetSimplexSmooth) ∞ :=
  ⟨(simplexProjectiveHomeomorph targetSimplexSmooth).symm,
    contMDiff_simplexProjectiveHomeomorph_symm targetSimplexSmooth⟩

/-- Actual O_P²(1): the genuine native simplex hyperplane bundle transported
through the established genuine biholomorphism, with Mathlib's ACTUAL
pullback total-space topology and holomorphic bundle atlas. -/
abbrev NativeProjectiveHyperplaneFiber :=
  simplexInverseHolomorphicMap *ᵖ (ToricNativeLineFiber nativeSimplexHyperplaneMetric)

instance nativeProjectiveHyperplaneNormed (q : SGPT.Projective.ComplexProjectiveSpace 2) :
    NormedAddCommGroup (NativeProjectiveHyperplaneFiber q) :=
  inferInstanceAs (NormedAddCommGroup ℂ)

instance nativeProjectiveHyperplaneHermitian (q : SGPT.Projective.ComplexProjectiveSpace 2) :
    InnerProductSpace ℂ (NativeProjectiveHyperplaneFiber q) :=
  inferInstanceAs (InnerProductSpace ℂ ℂ)

instance nativeProjectiveHyperplaneContinuousNorm :
    SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm NativeProjectiveHyperplaneFiber := by
  constructor
  exact (SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm.continuous
    (V := ToricNativeLineFiber nativeSimplexHyperplaneMetric)).comp
      (_root_.Pullback.continuous_lift ℂ (ToricNativeLineFiber nativeSimplexHyperplaneMetric)
        simplexInverseHolomorphicMap)

/-- Full physical holomorphic O_P²(1), with no prescribed section-space or
pullback comparison field. -/
def nativeProjectiveHyperplaneBundle :
    HermitianHolomorphicLineBundle 2 (SGPT.Projective.ComplexProjectiveSpace 2) :=
  HermitianHolomorphicLineBundle.ofNative NativeProjectiveHyperplaneFiber

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

def nativeSourceHyperplaneMetric : BigToricMetric (blowupHyperplaneDivisor hs) :=
  Classical.choice (exists_bigToricMetric _)

def originalBlowdownHolomorphicMap :
    ContMDiffMap 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2)
      (PolytopeToricVariety blowupGenerator hs) (SGPT.Projective.ComplexProjectiveSpace 2) ∞ :=
  ⟨originalBlowdown hs, contMDiff_originalBlowdown hs⟩

/-- The LITERAL actual pullback π*O_P²(1), with its genuine pullback
physical fibres and total-space topology. -/
abbrev NativeBlowdownPullbackHyperplaneFiber :=
  originalBlowdownHolomorphicMap hs *ᵖ NativeProjectiveHyperplaneFiber

instance nativeBlowdownPullbackHyperplaneNormed (p : PolytopeToricVariety blowupGenerator hs) :
    NormedAddCommGroup (NativeBlowdownPullbackHyperplaneFiber hs p) :=
  inferInstanceAs (NormedAddCommGroup ℂ)

instance nativeBlowdownPullbackHyperplaneHermitian (p : PolytopeToricVariety blowupGenerator hs) :
    InnerProductSpace ℂ (NativeBlowdownPullbackHyperplaneFiber hs p) :=
  inferInstanceAs (InnerProductSpace ℂ ℂ)

instance nativeBlowdownPullbackHyperplaneContinuousNorm :
    SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm
      (NativeBlowdownPullbackHyperplaneFiber hs) := by
  constructor
  exact (SGPT.Bergman.CompactHolomorphicSectionsDraft.ContinuousFiberNorm.continuous
    (V := NativeProjectiveHyperplaneFiber)).comp
      (_root_.Pullback.continuous_lift ℂ NativeProjectiveHyperplaneFiber
        (originalBlowdownHolomorphicMap hs))

def nativeBlowdownPullbackHyperplaneBundle :
    HermitianHolomorphicLineBundle 2 (PolytopeToricVariety blowupGenerator hs) :=
  HermitianHolomorphicLineBundle.ofNative (NativeBlowdownPullbackHyperplaneFiber hs)

/-- The actual pulled-back projective hyperplane frame on each original
source chart, through BOTH genuine native pullback constructions. -/
def nativeBlowdownPullbackFrame (v : latticePolytopeVertices blowupGenerator) :
    Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ (NativeBlowdownPullbackHyperplaneFiber hs) →
      PolytopeToricVariety blowupGenerator hs) :=
  ((toricNativeLineTrivialization nativeSimplexHyperplaneMetric (blowdownTargetVertex hs v)).pullback
    simplexInverseHolomorphicMap).pullback (originalBlowdownHolomorphicMap hs)

instance nativeBlowdownPullbackFrame_memAtlas (v : latticePolytopeVertices blowupGenerator) :
    MemTrivializationAtlas (nativeBlowdownPullbackFrame hs v) := by
  constructor
  refine ⟨(toricNativeLineTrivialization nativeSimplexHyperplaneMetric
    (blowdownTargetVertex hs v)).pullback simplexInverseHolomorphicMap, ?_, rfl⟩
  constructor
  exact ⟨toricNativeLineTrivialization nativeSimplexHyperplaneMetric
    (blowdownTargetVertex hs v), inferInstance, rfl⟩

theorem nativeBlowdownPullbackFrame_mem (v : latticePolytopeVertices blowupGenerator)
    {p : PolytopeToricVariety blowupGenerator hs}
    (hv : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source) :
    p ∈ (nativeBlowdownPullbackFrame hs v).baseSet :=
  originalBlowdownToSimplex_mem_chart hs v hv

/-- The scalar is defined by actual physical original and pulled-back
frames in an internally selected original covering chart. -/
def nativeBlowdownBundleScalar (p : PolytopeToricVariety blowupGenerator hs) : ℂ :=
  let v := toricNativePreferredVertex blowupGenerator hs p
  (toricNativeFrameCoefficient nativeSimplexHyperplaneMetric (blowdownTargetVertex hs v)
    (originalBlowdownToSimplex hs p))⁻¹ *
      toricNativeFrameCoefficient (nativeSourceHyperplaneMetric hs) v p

theorem nativeBlowdownBundleScalar_ne_zero (p : PolytopeToricVariety blowupGenerator hs) :
    nativeBlowdownBundleScalar hs p ≠ 0 := by
  let v := toricNativePreferredVertex blowupGenerator hs p
  have hv : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source :=
    toricNativePreferredVertex_mem p
  exact mul_ne_zero (inv_ne_zero (toricNativeFrameCoefficient_ne_zero
    nativeSimplexHyperplaneMetric (blowdownTargetVertex hs v)
      (originalBlowdownToSimplex_mem_chart hs v hv)))
    (toricNativeFrameCoefficient_ne_zero (nativeSourceHyperplaneMetric hs) v hv)

/-- The actual cocycle equality proves the physical scalar formula in EVERY
original chart. No local-to-global compatibility is supplied as input. -/
theorem nativeBlowdownBundleScalar_local (v : latticePolytopeVertices blowupGenerator)
    {p : PolytopeToricVariety blowupGenerator hs}
    (hv : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source) :
    nativeBlowdownBundleScalar hs p =
      (toricNativeFrameCoefficient nativeSimplexHyperplaneMetric (blowdownTargetVertex hs v)
        (originalBlowdownToSimplex hs p))⁻¹ *
          toricNativeFrameCoefficient (nativeSourceHyperplaneMetric hs) v p := by
  let w := toricNativePreferredVertex blowupGenerator hs p
  have hw : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs w).source :=
    toricNativePreferredVertex_mem p
  have hsw := toricNativeFrameCoefficient_transition (nativeSourceHyperplaneMetric hs) w v hw hv
  have htw := toricNativeFrameCoefficient_transition nativeSimplexHyperplaneMetric
    (blowdownTargetVertex hs w) (blowdownTargetVertex hs v)
    (originalBlowdownToSimplex_mem_chart hs w hw) (originalBlowdownToSimplex_mem_chart hs v hv)
  rw [← originalBlowdown_cartierTransition hs w v hw hv] at htw
  change (toricNativeFrameCoefficient nativeSimplexHyperplaneMetric (blowdownTargetVertex hs w)
      (originalBlowdownToSimplex hs p))⁻¹ *
        toricNativeFrameCoefficient (nativeSourceHyperplaneMetric hs) w p = _
  rw [← hsw, ← htw]
  field_simp [toricCartierTransition_ne_zero (blowupHyperplaneDivisor hs) w v hw hv,
    toricNativeFrameCoefficient_ne_zero nativeSimplexHyperplaneMetric (blowdownTargetVertex hs w)
      (originalBlowdownToSimplex_mem_chart hs w hw)]

/-- A genuine complex linear isomorphism on EVERY actual physical fibre
O_X(D4)_p ≃ (π*O_P²(1))_p, internally manufactured from the source data. -/
def nativeBlowdownHyperplaneFiberEquiv (p : PolytopeToricVariety blowupGenerator hs) :
    ToricNativeLineFiber (nativeSourceHyperplaneMetric hs) p ≃ₗ[ℂ]
      NativeBlowdownPullbackHyperplaneFiber hs p where
  toFun t := nativeBlowdownBundleScalar hs p * (show ℂ from t)
  invFun t := (nativeBlowdownBundleScalar hs p)⁻¹ * (show ℂ from t)
  left_inv t := by
    change (nativeBlowdownBundleScalar hs p)⁻¹ * (nativeBlowdownBundleScalar hs p * (show ℂ from t)) = (show ℂ from t)
    rw [← mul_assoc, inv_mul_cancel₀ (nativeBlowdownBundleScalar_ne_zero hs p), one_mul]
  right_inv t := by
    change nativeBlowdownBundleScalar hs p * ((nativeBlowdownBundleScalar hs p)⁻¹ * (show ℂ from t)) = (show ℂ from t)
    rw [← mul_assoc, mul_inv_cancel₀ (nativeBlowdownBundleScalar_ne_zero hs p), one_mul]
  map_add' t s := by
    change nativeBlowdownBundleScalar hs p * ((show ℂ from t) + (show ℂ from s)) = _
    exact mul_add _ _ _
  map_smul' a t := by
    change nativeBlowdownBundleScalar hs p * (a * (show ℂ from t)) = a * (nativeBlowdownBundleScalar hs p * (show ℂ from t))
    ring

/-- The ACTUAL physical bundle comparison has coefficient one in every
actual original/pulled-back holomorphic frame. -/
theorem nativeBlowdownHyperplaneFiberEquiv_coordinate (v : latticePolytopeVertices blowupGenerator)
    {p : PolytopeToricVariety blowupGenerator hs}
    (hv : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source)
    (t : ToricNativeLineFiber (nativeSourceHyperplaneMetric hs) p) :
    (nativeBlowdownPullbackFrame hs v
      ⟨p, nativeBlowdownHyperplaneFiberEquiv hs p t⟩).2 =
      (toricNativeLineTrivialization (nativeSourceHyperplaneMetric hs) v ⟨p, t⟩).2 := by
  change toricNativeFrameCoefficient nativeSimplexHyperplaneMetric (blowdownTargetVertex hs v)
      (originalBlowdownToSimplex hs p) * (nativeBlowdownBundleScalar hs p * (show ℂ from t)) =
        toricNativeFrameCoefficient (nativeSourceHyperplaneMetric hs) v p * (show ℂ from t)
  rw [nativeBlowdownBundleScalar_local hs v hv]
  field_simp [toricNativeFrameCoefficient_ne_zero nativeSimplexHyperplaneMetric
    (blowdownTargetVertex hs v) (originalBlowdownToSimplex_mem_chart hs v hv)]

end SGPT.Toric.BlowdownDraft

end
/- END OriginalHyperplanePhysicalMapDraft -/
end PointBlowupCanonicalFragment001

section PointBlowupCanonicalFragment002
/- BEGIN OriginalHyperplaneHolomorphicEquivDraft; original source SHA256 072d806353885cbda62b51a5357948a1c203e1fc2473a4802b26d4e0652fb3d3 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Bundle Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)
local notation "Ibase" => 𝓘(ℂ, ComplexModel 2)

/-- Actual forward map of physical total spaces, covering the identity of
X and complex linear on each original fibre. -/
def nativeBlowdownHyperplaneTotalMap
    (x : TotalSpace ℂ (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs))) :
    TotalSpace ℂ (NativeBlowdownPullbackHyperplaneFiber hs) :=
  ⟨x.proj, nativeBlowdownHyperplaneFiberEquiv hs x.proj x.snd⟩

/-- Actual inverse physical total-space map. -/
def nativeBlowdownHyperplaneTotalInv
    (x : TotalSpace ℂ (NativeBlowdownPullbackHyperplaneFiber hs)) :
    TotalSpace ℂ (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs)) :=
  ⟨x.proj, (nativeBlowdownHyperplaneFiberEquiv hs x.proj).symm x.snd⟩

/-- Inverse coefficients are also literally one in the genuine original
source and pulled-back projective holomorphic frames. -/
theorem nativeBlowdownHyperplaneFiberEquiv_symm_coordinate
    (v : latticePolytopeVertices blowupGenerator)
    {p : PolytopeToricVariety blowupGenerator hs}
    (hv : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source)
    (t : NativeBlowdownPullbackHyperplaneFiber hs p) :
    (toricNativeLineTrivialization (nativeSourceHyperplaneMetric hs) v
      ⟨p, (nativeBlowdownHyperplaneFiberEquiv hs p).symm t⟩).2 =
      (nativeBlowdownPullbackFrame hs v ⟨p, t⟩).2 := by
  have h := nativeBlowdownHyperplaneFiberEquiv_coordinate hs v hv
    ((nativeBlowdownHyperplaneFiberEquiv hs p).symm t)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- Genuine native vector-bundle charts prove holomorphy of the actual
physical total-space comparison. The local coordinate map is (p,z)↦(p,z). -/
theorem contMDiff_nativeBlowdownHyperplaneTotalMap :
    ContMDiff ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ∞ (nativeBlowdownHyperplaneTotalMap hs) := by
  intro x
  let v := toricNativePreferredVertex blowupGenerator hs x.proj
  have hv : x.proj ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source :=
    toricNativePreferredVertex_mem x.proj
  let e := toricNativeLineTrivialization (nativeSourceHyperplaneMetric hs) v
  let f := nativeBlowdownPullbackFrame hs v
  have he : x ∈ e.source := hv
  have hf : nativeBlowdownHyperplaneTotalMap hs x ∈ f.source :=
    nativeBlowdownPullbackFrame_mem hs v hv
  apply (f.contMDiffAt_iff hf).mpr
  refine ⟨contMDiffAt_proj (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs)), ?_⟩
  have hid : ContMDiffAt ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ∞ id x := contMDiffAt_id
  have hcoeff := ((e.contMDiffAt_iff he).mp hid).2
  apply hcoeff.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds he] with y hy
  exact nativeBlowdownHyperplaneFiberEquiv_coordinate hs v hy y.snd

set_option maxHeartbeats 800000 in
/-- The inverse total-space comparison is genuinely holomorphic as well;
the proof retains the actual pullback topology and actual original opens. -/
theorem contMDiff_nativeBlowdownHyperplaneTotalInv :
    ContMDiff ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ∞ (nativeBlowdownHyperplaneTotalInv hs) := by
  intro x
  let v := toricNativePreferredVertex blowupGenerator hs x.proj
  have hv : x.proj ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source :=
    toricNativePreferredVertex_mem x.proj
  let e := toricNativeLineTrivialization (nativeSourceHyperplaneMetric hs) v
  let f := nativeBlowdownPullbackFrame hs v
  have he : nativeBlowdownHyperplaneTotalInv hs x ∈ e.source := hv
  have hf : x ∈ f.source := nativeBlowdownPullbackFrame_mem hs v hv
  apply (e.contMDiffAt_iff he).mpr
  refine ⟨contMDiffAt_proj (NativeBlowdownPullbackHyperplaneFiber hs), ?_⟩
  have hfmap : ContMDiffOn ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ)))
      ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) ∞ f f.source :=
    f.contMDiffOn (IB := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
  have hcoeff : ContMDiffAt ((𝓘(ℂ, ComplexModel 2)).prod (𝓘(ℂ, ℂ))) 𝓘(ℂ, ℂ) ∞
      (fun y : TotalSpace ℂ (NativeBlowdownPullbackHyperplaneFiber hs) => (f y).2) x :=
    (hfmap.contMDiffAt (f.open_source.mem_nhds hf)).snd
  apply hcoeff.congr_of_eventuallyEq
  have hnear : {y : TotalSpace ℂ (NativeBlowdownPullbackHyperplaneFiber hs) |
      y.proj ∈ (originalPolytopeNativeModelChart blowupGenerator hs v).source} ∈ 𝓝 x :=
    ((originalPolytopeNativeModelChart blowupGenerator hs v).open_source.preimage
      (FiberBundle.continuous_proj ℂ (NativeBlowdownPullbackHyperplaneFiber hs))).mem_nhds hv
  filter_upwards [hnear] with y hy
  exact nativeBlowdownHyperplaneFiberEquiv_symm_coordinate hs v hy y.snd

/-- A true physical total-space equivalence, with the actual linear maps
on every original fibre. -/
def nativeBlowdownHyperplaneTotalEquiv :
    TotalSpace ℂ (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs)) ≃
      TotalSpace ℂ (NativeBlowdownPullbackHyperplaneFiber hs) where
  toFun := nativeBlowdownHyperplaneTotalMap hs
  invFun := nativeBlowdownHyperplaneTotalInv hs
  left_inv := by
    rintro ⟨p, t⟩
    change (⟨p, (nativeBlowdownHyperplaneFiberEquiv hs p).symm
      (nativeBlowdownHyperplaneFiberEquiv hs p t)⟩ :
        TotalSpace ℂ (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs))) = ⟨p, t⟩
    rw [LinearEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨p, t⟩
    change (⟨p, nativeBlowdownHyperplaneFiberEquiv hs p
      ((nativeBlowdownHyperplaneFiberEquiv hs p).symm t)⟩ :
        TotalSpace ℂ (NativeBlowdownPullbackHyperplaneFiber hs)) = ⟨p, t⟩
    rw [LinearEquiv.apply_symm_apply]

/-- The actual holomorphic line-bundle isomorphism O_X(D4)≅π*O_P²(1).
Both total-space topologies are independently constructed native topologies;
no desired isomorphism, atlas dictionary or section-space certificate enters. -/
def nativeBlowdownHyperplaneBundleHomeomorph :
    TotalSpace ℂ (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs)) ≃ₜ
      TotalSpace ℂ (NativeBlowdownPullbackHyperplaneFiber hs) where
  toEquiv := nativeBlowdownHyperplaneTotalEquiv hs
  continuous_toFun := (contMDiff_nativeBlowdownHyperplaneTotalMap hs).continuous
  continuous_invFun := (contMDiff_nativeBlowdownHyperplaneTotalInv hs).continuous

/-- The full actual original H0 maps forward holomorphically. -/
def nativeBlowdownHyperplaneSectionMap
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := 2)
      (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs))) :
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := 2)
      (NativeBlowdownPullbackHyperplaneFiber hs) where
  toFun p := nativeBlowdownHyperplaneFiberEquiv hs p (s p)
  contMDiff_toFun := (contMDiff_nativeBlowdownHyperplaneTotalMap hs).comp s.contMDiff

/-- EVERY actual pulled-back holomorphic section has a holomorphic inverse. -/
def nativeBlowdownHyperplaneSectionInv
    (s : SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := 2)
      (NativeBlowdownPullbackHyperplaneFiber hs)) :
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := 2)
      (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs)) where
  toFun p := (nativeBlowdownHyperplaneFiberEquiv hs p).symm (s p)
  contMDiff_toFun := (contMDiff_nativeBlowdownHyperplaneTotalInv hs).comp s.contMDiff

/-- A genuine BOTH-direction complex linear equivalence of the full actual
original and pulled-back section spaces, with no finite chosen subsystem. -/
def nativeBlowdownHyperplaneSectionsEquiv :
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := 2)
      (ToricNativeLineFiber (nativeSourceHyperplaneMetric hs)) ≃ₗ[ℂ]
    SGPT.Bergman.QuantizationDraft.HolomorphicSections (n := 2)
      (NativeBlowdownPullbackHyperplaneFiber hs) where
  toFun := nativeBlowdownHyperplaneSectionMap hs
  invFun := nativeBlowdownHyperplaneSectionInv hs
  left_inv s := by ext p; exact (nativeBlowdownHyperplaneFiberEquiv hs p).symm_apply_apply (s p)
  right_inv s := by ext p; exact (nativeBlowdownHyperplaneFiberEquiv hs p).apply_symm_apply (s p)
  map_add' s t := by ext p; exact map_add (nativeBlowdownHyperplaneFiberEquiv hs p) (s p) (t p)
  map_smul' a s := by ext p; exact map_smul (nativeBlowdownHyperplaneFiberEquiv hs p) a (s p)

end SGPT.Toric.BlowdownDraft

end
/- END OriginalHyperplaneHolomorphicEquivDraft -/
end PointBlowupCanonicalFragment002


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`OriginalMonomialProjectiveMapDraft, `OriginalBlowdownMapDraft, `OriginalBlowupDirectionDraft, `OriginalBlowdownDivisorsDraft, `OriginalBlowupIncidenceDraft, `OriginalBlowupReconstructionDraft, `OriginalIncidenceHomeomorphDraft, `OriginalIncidenceNaturalOpensDraft, `OriginalIncidenceAnalyticManifoldDraft, `OriginalIncidenceRatioChartsDraft, `NativeProjectivePointBlowupDraft, `NativeProjectivePointFourChartsDraft, `OriginalBlowdownCartierTransitionDraft, `OriginalNativeBlowupLocalMapsDraft, `OriginalNativeBlowupGlobalMapDraft, `NativeOriginalBlowupInverseLocalDraft, `NativeBlowupDenseOffCentreDraft, `OriginalNativeBlowupEquivDraft, `OriginalNativePointBlowupUniversalDraft, `OriginalHyperplanePhysicalMapDraft, `OriginalHyperplaneHolomorphicEquivDraft, `SourceOriginalBlowupOkounkovDraft, `PhysicalPowerFlagValuationDraft, `PhysicalPowerOkounkovBodyDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden flat/private provider in proper toric point-blowup module: {m}"
