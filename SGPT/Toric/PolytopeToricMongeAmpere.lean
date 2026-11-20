import SGPT.Toric.PolytopeToricEnergyClasses
import SGPT.Toric.AlexandrovLinearChange
import SGPT.Toric.GlobalTropicalChartMass
import SGPT.Toric.TropicalBedfordTaylor
import SGPT.Foundations.Analysis.Pending.BergmanSupWeight

/-!
# The complex and the real Monge–Ampère measures of a toric potential

Source `chapter_toric_ample.tex`, `prop:toricMAandrealMA`: for `φ ∈ PSH_tor(X, ω)`,
`Trop_*((ω + ddᶜφ)|_T)^n = MA_ℝ(F_φ)` (`eq:tropMAmea`), hence
`∫_X ω_φ^n = ∫ MA_ℝ(F_φ) = n! vol Δ(ω, φ)` and `∫_X ω^n = n! vol P`.

The measure `(ω + ddᶜφ)^n` on `T` is the non-pluripolar product restricted to the open
torus (on `T` the potential is locally bounded, so this is the Bedford–Taylor product).
The identity is proved in the base vertex chart, where the existing tropical
Bedford–Taylor computation applies to the chart convex function, and transported to the
standard coordinates of `N_ℝ` by the unimodular change of variables of the edge basis.
The boundary carries no mass, being the polar set of `log |z_1 ⋯ z_n|^2` in every chart.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-! ### The edge-basis change of variables is unimodular -/

/-- The transpose of the inverse basis change, with coefficients `b.repr e_k`. -/
def latticeBasisLogInverseTranspose (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun q := (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun j => latticeFunctional (fun k => b.repr (Pi.single k 1) j) q)
  map_add' x y := by
    ext j
    simp only [map_add]
    rfl
  map_smul' c x := by
    ext j
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    rfl

/-- The transpose of the basis change, with coefficients `b j i`. -/
def latticeBasisLogMapTranspose (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun q := (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => latticeFunctional (fun j => b j i) q)
  map_add' x y := by
    ext j
    simp only [map_add]
    rfl
  map_smul' c x := by
    ext j
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    rfl

theorem inner_latticeBasisLogInverse (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (y q : EuclideanSpace ℝ (Fin n)) :
    ⟪latticeBasisLogInverse b y, q⟫ = ⟪y, latticeBasisLogInverseTranspose b q⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change ∑ k, q k * (∑ j, (b.repr (Pi.single k 1) j : ℝ) * y j) =
    ∑ j, (∑ k, (b.repr (Pi.single k 1) j : ℝ) * q k) * y j
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem inner_latticeBasisLogMap (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (x q : EuclideanSpace ℝ (Fin n)) :
    ⟪latticeBasisLogMap b x, q⟫ = ⟪x, latticeBasisLogMapTranspose b q⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change ∑ j, q j * (∑ i, (b j i : ℝ) * x i) = ∑ i, (∑ j, (b j i : ℝ) * q j) * x i
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem latticeBasisLogMap_logInverse (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (y : EuclideanSpace ℝ (Fin n)) :
    latticeBasisLogMap b (latticeBasisLogInverse b y) = y := by
  have hsurj : Function.Surjective (latticeBasisLogInverse b) :=
    fun x => ⟨latticeBasisLogMap b x, latticeBasisLogInverse_logMap b x⟩
  have hinj := LinearMap.injective_iff_surjective.mpr hsurj
  exact hinj (latticeBasisLogInverse_logMap b _)

/-- The determinant of a linear map with integer matrix is an integer. -/
theorem det_eq_intCast_of_entries (f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (N : Matrix (Fin n) (Fin n) ℤ) (hf : ∀ q j, f q j = ∑ k, (N j k : ℝ) * q k) :
    LinearMap.det f = ((N.det : ℤ) : ℝ) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis f = (Int.castRingHom ℝ).mapMatrix N := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, hf]
    simp
  rw [hM, ← RingHom.map_det]
  rfl

/-- The transposed inverse basis change as a continuous linear automorphism. -/
def latticeBasisLogInverseTransposeEquiv (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (LinearEquiv.ofLinearMap (latticeBasisLogInverseTranspose b) (latticeBasisLogMapTranspose b)
    (by
      ext1 q
      apply ext_inner_left ℝ
      intro y
      change ⟪y, latticeBasisLogInverseTranspose b (latticeBasisLogMapTranspose b q)⟫ = ⟪y, q⟫
      rw [← inner_latticeBasisLogInverse, ← inner_latticeBasisLogMap,
        latticeBasisLogMap_logInverse])
    (by
      ext1 q
      apply ext_inner_left ℝ
      intro y
      change ⟪y, latticeBasisLogMapTranspose b (latticeBasisLogInverseTranspose b q)⟫ = ⟪y, q⟫
      rw [← inner_latticeBasisLogMap, ← inner_latticeBasisLogInverse,
        latticeBasisLogInverse_logMap])).toContinuousLinearEquiv

/-- The unimodular change of variables of a lattice basis. -/
def latticeBasisUnimodularChange (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    UnimodularChange n where
  B := latticeBasisLogMap b
  C := latticeBasisLogInverse b
  A := latticeBasisLogInverseTransposeEquiv b
  C_B := latticeBasisLogInverse_logMap b
  B_C := latticeBasisLogMap_logInverse b
  inner_C := inner_latticeBasisLogInverse b
  abs_det_A := by
    let N : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun j k => b.repr (Pi.single k 1) j
    let N' : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => b j i
    have hA : LinearMap.det (latticeBasisLogInverseTranspose b) = ((N.det : ℤ) : ℝ) :=
      det_eq_intCast_of_entries _ N (fun q j => rfl)
    have hA' : LinearMap.det (latticeBasisLogMapTranspose b) = ((N'.det : ℤ) : ℝ) :=
      det_eq_intCast_of_entries _ N' (fun q j => rfl)
    have hcomp : latticeBasisLogInverseTranspose b ∘ₗ latticeBasisLogMapTranspose b =
        LinearMap.id := by
      ext1 q
      exact (latticeBasisLogInverseTransposeEquiv b).apply_symm_apply q
    have hdet := congrArg LinearMap.det hcomp
    rw [LinearMap.det_comp, LinearMap.det_id, hA, hA'] at hdet
    have hint : N.det * N'.det = 1 := by exact_mod_cast hdet
    change |LinearMap.det (latticeBasisLogInverseTranspose b)| = 1
    rw [hA]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hint with h | h <;> simp [h]

/-! ### The boundary is pluripolar -/

theorem manifoldLocallyPluripolar_polytopeToricBoundary
    (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ) :
    ManifoldLocallyPluripolar (n := n) (polytopeToricBoundary γ hs) := by
  intro e x _
  refine ⟨univ, fun z => logNormSq (originalPolytopeNativeBoundaryPolynomial n z), isOpen_univ,
    mem_univ x, isPreconnected_univ, ?_, ?_, ?_⟩
  · exact Pending.BergmanSupWeight.plurisubharmonicOn_logNormSq_comp isOpen_univ
      (differentiable_originalPolytopeNativeBoundaryPolynomial n).differentiableOn
  · refine ⟨(originalPolytopeNativeModelEquiv n).symm (fun _ => 1), mem_univ _, ?_⟩
    show logNormSq (originalPolytopeNativeBoundaryPolynomial n
      ((originalPolytopeNativeModelEquiv n).symm fun _ => 1)) ≠ ⊥
    rw [originalPolytopeNativeBoundaryPolynomial_one]
    simp [logNormSq]
  · intro y _ hy
    have hb : originalPolytopeNativeBoundaryPolynomial n y = 0 :=
      (originalPolytopeNativeBoundary_all_chart_iff γ hs e y).mp hy.2
    show logNormSq (originalPolytopeNativeBoundaryPolynomial n y) = ⊥
    rw [hb]
    exact logNormSq_zero

/-! ### The chart identity -/

variable (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)

/-- The vertex functional `⟨v, ·⟩` as an inner product. -/
def polytopeToricVertexVector (v : latticePolytopeVertices γ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => (v.val i : ℝ))

omit [Fintype K] [Nonempty K] in
theorem latticeFunctional_eq_inner (v : latticePolytopeVertices γ) (x : EuclideanSpace ℝ (Fin n)) :
    latticeFunctional v.val x = ⟪polytopeToricVertexVector γ v, x⟫ := by
  simp only [latticeFunctional_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The convex function representing a toric potential in the base vertex chart. -/
def polytopeToricChartProfile (u : PolytopeToricVariety γ hs → EReal)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  polytopeToricRealProfile γ hs u
      (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ)) y) -
    latticeFunctional (polytopeToricBaseVertex γ).val
      (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ)) y)

theorem convexOn_polytopeToricChartProfile {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) : ConvexOn ℝ univ (polytopeToricChartProfile γ hs u) := by
  have hf := (polytopeToricRealProfile_mem γ hs hu).1.1
  let C := latticeBasisLogInverse (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ))
  have h1 : ConvexOn ℝ univ (polytopeToricRealProfile γ hs u ∘ C) := by
    simpa only [preimage_univ] using hf.comp_linearMap C
  have h2 : ConvexOn ℝ univ
      (-(latticeFunctional (polytopeToricBaseVertex γ).val ∘ₗ C)) :=
    LinearMap.convexOn _ convex_univ
  exact h1.add h2

/-- The toric profile in terms of the chart profile and the unimodular change. -/
theorem polytopeToricRealProfile_eq_chartProfile (u : PolytopeToricVariety γ hs → EReal)
    (x : EuclideanSpace ℝ (Fin n)) :
    polytopeToricRealProfile γ hs u x =
      polytopeToricChartProfile γ hs u
          ((latticeBasisUnimodularChange
            (originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ))).B x) +
        ⟪polytopeToricVertexVector γ (polytopeToricBaseVertex γ), x⟫ := by
  change _ = polytopeToricRealProfile γ hs u (latticeBasisLogInverse _ (latticeBasisLogMap _ x)) -
    latticeFunctional _ (latticeBasisLogInverse _ (latticeBasisLogMap _ x)) + _
  rw [latticeBasisLogInverse_logMap, latticeFunctional_eq_inner]
  ring

/-- The base vertex chart as a source atlas chart. -/
def polytopeToricBaseChart : ComplexChart n (PolytopeToricVariety γ hs) :=
  originalPolytopeNativeComplexChart γ hs (polytopeToricBaseVertex γ)

theorem polytopeToricBaseChart_localPotential :
    IsSmoothLocalPotential (polytopeToricKahlerForm γ hs).val (polytopeToricBaseChart γ hs)
      (tropicalSmoothDomain n) (originalGuilleminGeometricNativeWeight γ hs
        (polytopeToricBaseVertex γ)) := by
  refine ⟨(tropicalSmoothDomain n).isOpen, ?_, ?_, ?_⟩
  · intro z _
    change z ∈ (originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).target
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  · exact (contDiff_originalGuilleminGeometricNativeWeight γ hs _).contDiffOn
  · intro z _
    exact (originalGuilleminClosedForm_native_coeff γ hs _ z).symm

theorem polytopeToricBaseChart_corrected {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    EqOn (fun z => chartFunction u (polytopeToricBaseChart γ hs) z +
        (originalGuilleminGeometricNativeWeight γ hs (polytopeToricBaseVertex γ) z : EReal))
      (fun z => (polytopeToricChartProfile γ hs u (tropicalization z) : EReal))
      (tropicalSmoothDomain n) := by
  intro z hz
  have h := polytopeToric_vertexChart_corrected_eq γ hs (fun a => hu.2.embedding_eq γ hs a)
    (polytopeToricBaseVertex γ) hz
  change u ((originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).symm z) + _ = _
  rw [h, (polytopeToricRealProfile_mem γ hs hu).2]
  simp only [tropicalPullback, polytopeToricChartProfile, EReal.coe_add, sub_eq_add_neg]

/-- The non-pluripolar measure `ω_φ^n` of a toric potential (source `def:npp`), in the
source interface. -/
abbrev polytopeToricMA {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ PolytopeToricPSH γ hs) :
    Measure (PolytopeToricVariety γ hs) :=
  sourcePotentialNonPluripolarMeasure (polytopeToricOmega γ hs) u hu.1

theorem polytopeToric_patchSource_eq {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    ((tropicalPotentialPatch (polytopeToricBaseChart γ hs)
      (polytopeToricBaseChart_localPotential γ hs) (convexOn_polytopeToricChartProfile γ hs hu)
        (polytopeToricBaseChart_corrected γ hs hu)).source : Set (PolytopeToricVariety γ hs)) =
      (polytopeToricBoundary γ hs)ᶜ := by
  ext p
  change p ∈ (originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).source ∧
      originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ) p ∈ complexTorus n ↔ _
  constructor
  · rintro ⟨hp, hz⟩
    have h :=
      (polytopeToricVertexChart_symm_mem_compl_iff γ hs (polytopeToricBaseVertex γ) _).mpr hz
    rwa [(originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).left_inv hp] at h
  · intro hp
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
    have hsrc : polytopeToricEmbedding γ hs a ∈
        (originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).source := by
      rw [originalPolytopeNativeModelChart_source]
      exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs _ a
    refine ⟨hsrc, ?_⟩
    apply (polytopeToricVertexChart_symm_mem_compl_iff γ hs (polytopeToricBaseVertex γ) _).mp
    rw [(originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).left_inv hsrc]
    exact polytopeToricEmbedding_mem_compl γ hs a

theorem continuousOn_polytopeToricLog :
    ContinuousOn (polytopeToricLog γ hs) (polytopeToricBoundary γ hs)ᶜ := by
  let c := originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)
  have hsrc : (polytopeToricBoundary γ hs)ᶜ ⊆ c.source := by
    intro p hp
    obtain ⟨a, rfl⟩ := (mem_polytopeToricBoundary_compl_iff γ hs p).mp hp
    change polytopeToricEmbedding γ hs a ∈ (originalPolytopeNativeModelChart γ hs _).source
    rw [originalPolytopeNativeModelChart_source]
    exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs _ a
  have htor : ∀ p ∈ (polytopeToricBoundary γ hs)ᶜ, c p ∈ complexTorus n := by
    intro p hp
    apply (polytopeToricVertexChart_symm_mem_compl_iff γ hs (polytopeToricBaseVertex γ) _).mp
    rw [c.left_inv (hsrc hp)]
    exact hp
  have htrop : ContinuousOn (@tropicalization n) (complexTorus n) := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    apply (PiLp.continuous_toLp 2 _).continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    have hnorm : ContinuousAt (fun z : ComplexModel n => ‖z i‖) z :=
      (PiLp.continuous_apply 2 _ i).continuousAt.norm
    exact continuousAt_const.mul
      ((Real.continuousAt_log (norm_ne_zero_iff.mpr (hz i))).comp
        (f := fun z : ComplexModel n => ‖z i‖) hnorm)
  have hC := (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs
    (polytopeToricBaseVertex γ))).continuous_of_finiteDimensional
  exact hC.comp_continuousOn ((htrop.comp (c.continuousOn.mono hsrc) htor))

theorem aemeasurable_polytopeToricLog (μ : Measure (PolytopeToricVariety γ hs)) :
    AEMeasurable (polytopeToricLog γ hs) (μ.restrict (polytopeToricBoundary γ hs)ᶜ) :=
  (continuousOn_polytopeToricLog γ hs).aemeasurable
    (isOpen_originalPolytopeNativeTorus γ hs).measurableSet

/-- Source `prop:toricMAandrealMA`, `eq:tropMAmea`: `Trop_*((ω + ddᶜφ)|_T)^n = MA_ℝ(F_φ)`. -/
theorem polytopeToric_map_tropicalization_MA {u : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ PolytopeToricPSH γ hs) :
    Measure.map (polytopeToricLog γ hs)
        ((polytopeToricMA γ hs hu).restrict (polytopeToricBoundary γ hs)ᶜ) =
      alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume
        (polytopeToricProfile γ hs u) := by
  let b := originalPolytopeNativeBasis γ hs (polytopeToricBaseVertex γ)
  let T := latticeBasisUnimodularChange b
  let hc := convexOn_polytopeToricChartProfile γ hs hu
  let P := tropicalPotentialPatch (polytopeToricBaseChart γ hs)
    (polytopeToricBaseChart_localPotential γ hs) hc (polytopeToricBaseChart_corrected γ hs hu)
  have hn : IsThetaPshPotential (polytopeToricKahlerForm γ hs).val u :=
    (isThetaPSH_iff_nativeThetaPotential (polytopeToricOmega γ hs) u).mp hu.1
  have hrestr := globalMixedMeasure_restrict_tropical_chart hn (polytopeToricBaseChart γ hs)
    (polytopeToricBaseChart_localPotential γ hs) hc (polytopeToricBaseChart_corrected γ hs hu)
  have hmeasure : (polytopeToricMA γ hs hu).restrict (polytopeToricBoundary γ hs)ᶜ =
      P.pushMeasure (tropicalCanonicalBTMeasure hc) := by
    rw [← polytopeToric_patchSource_eq γ hs hu]
    exact hrestr
  have hprof : polytopeToricProfile γ hs u = fun x =>
      ((polytopeToricChartProfile γ hs u (T.B x) +
        ⟪polytopeToricVertexVector γ (polytopeToricBaseVertex γ), x⟫ : ℝ) : EReal) := by
    rw [(polytopeToricRealProfile_mem γ hs hu).2]
    funext x
    rw [polytopeToricRealProfile_eq_chartProfile]
  have hT : Measurable (@tropicalization n) :=
    (exists_compact_tropical_torus_lift (n := n) isCompact_empty).1
  have hCm : Measurable (T.C : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
    T.C.continuous_of_finiteDimensional.measurable
  have hsupp : tropicalCanonicalBTMeasure hc (complexTorus n)ᶜ = 0 :=
    Pending.MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_compl (tropicalSmoothDomain n)
      (fun _ : Fin n => fun z => polytopeToricChartProfile γ hs u (tropicalization z))
      (fun _ => isLocallyBoundedPshOn_tropicalConvexProfile hc)
  have hae := aemeasurable_polytopeToricLog γ hs (polytopeToricMA γ hs hu)
  rw [hprof, T.alexandrovMeasure_comp, ← tropicalization_canonicalBTMeasure_eq_alexandrov hc,
    Measure.map_map hCm hT]
  ext s hs'
  rw [Measure.map_apply_of_aemeasurable hae hs', Measure.map_apply (hCm.comp hT) hs',
    hmeasure, Patch.pushMeasure_apply]
  have hlog : ∀ z, polytopeToricLog γ hs
      ((originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).symm z) =
        T.C (tropicalization z) := by
    intro z
    have ht : z ∈ (originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).target := by
      rw [originalPolytopeNativeModelChart_target]; exact mem_univ z
    change latticeBasisLogInverse b (tropicalization
      ((originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ))
        ((originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).symm z))) = _
    rw [(originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).right_inv ht]
    rfl
  have hset : (P.domain : Set (ComplexModel n)) ∩
      P.chart.val.symm ⁻¹' (polytopeToricLog γ hs ⁻¹' s) =
      complexTorus n ∩ (T.C ∘ tropicalization) ⁻¹' s := by
    ext z
    change z ∈ complexTorus n ∧ polytopeToricLog γ hs
      ((originalPolytopeNativeModelChart γ hs (polytopeToricBaseVertex γ)).symm z) ∈ s ↔
        z ∈ complexTorus n ∧ T.C (tropicalization z) ∈ s
    rw [hlog]
  rw [hset, inter_comm, measure_inter_conull hsupp]

end SGPT.Toric
