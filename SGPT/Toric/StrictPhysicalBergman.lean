/- Canonical staging of the immutable whole-original toric Bergman proof.
   Exact retained fragments/providers are recorded in fragment-provider-map.json.gz. -/
import SGPT.PSH.AnalyticGeneratorAlgebra
import SGPT.PSH.AtlasQPSHScaling
import SGPT.PSH.GlobalL2BergmanUpper
import SGPT.PSH.MultiplierIdealInfSkoda
import SGPT.Projective.FubiniStudy
import SGPT.Toric.BigToricCorrespondence
import SGPT.Toric.MetricFiniteSums
import SGPT.Toric.NativePhysicalLineBundle
import SGPT.Toric.NativeSingularPhiBergman
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
import SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
import SGPT.Foundations.Analysis.Pending.AnalyticSingularities
import SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
import SGPT.Foundations.Analysis.Pending.BoundedMultiplierGeneratorWeight
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier
import SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationBergmanInstanceTransport
import SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationBergmanLogGenerators
import SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationChartBranch
import SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationChartGermTransfer
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularComparison
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison


/- BEGIN SGPT.Toric.ToricNativePhiAnalyticBergman; source SHA256 8ed171f8529eab757d9df0080a83ece34eba7e1a94df856ae8395ee0a7a7e41f -/
section ToricCanonicalFragment046

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft HermitianHolomorphicLineBundle
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Genuine entire Cartier coefficients of a finite physical original H0 family. -/
def toricNativeFiniteSectionGenerators {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) (v : latticePolytopeVertices γ) :
    Fin d → ComplexModel n → ℂ := fun j =>
  toricOriginalSectionCoeff (toricNativePlainPowerFullSectionEquiv h q (s j)) v

theorem differentiable_toricNativeFiniteSectionGenerators {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) (v : latticePolytopeVertices γ) (j : Fin d) :
    Differentiable ℂ (toricNativeFiniteSectionGenerators h q s v j) :=
  differentiable_toricOriginalSectionCoeff _ _

/-- Literal finite physical section sum. Empty families and q=0 are retained. -/
def toricNativeFiniteSectionDensity {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) (p : PolytopeToricVariety γ hs) : ENNReal :=
  ∑ j, ENNReal.ofReal (‖s j p‖ ^ 2)

def toricNativeFiniteSectionPotential {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) (p : PolytopeToricVariety γ hs) : EReal :=
  ((q : ℝ)⁻¹ : EReal) * ENNReal.log (toricNativeFiniteSectionDensity h q s p)

/-- The actual physical metric factors out of the full finite sum in every
original holomorphic vertex chart, including the common zero set. -/
theorem toricNativeFiniteSectionDensity_eq_generator {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    toricNativeFiniteSectionDensity h q s p =
      ENNReal.ofReal (∑ j, ‖toricNativeFiniteSectionGenerators h q s v j
        (originalPolytopeNativeModelChart γ hs v p)‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-(q : ℝ) * h.weight v
        (originalPolytopeNativeModelChart γ hs v p))) := by
  unfold toricNativeFiniteSectionDensity
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  simpa only [LinearEquiv.symm_apply_apply, toricNativeFiniteSectionGenerators] using
    (toricNativePlainPowerFullSectionEquiv_symm_norm_sq h q
      (toricNativePlainPowerFullSectionEquiv h q (s j)) v hp)

/-- Exact local smooth-remainder logarithmic formula for the SAME physical
metric. No clipping, bounded-equivalence substitute or supplied kernel formula. -/
theorem toricNativeFiniteSectionPotential_eq_generator {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    toricNativeFiniteSectionPotential h q s p =
      ((q : ℝ)⁻¹ : EReal) * generatorLog (toricNativeFiniteSectionGenerators h q s v)
        (originalPolytopeNativeModelChart γ hs v p) -
      (h.weight v (originalPolytopeNativeModelChart γ hs v p) : EReal) := by
  unfold toricNativeFiniteSectionPotential
  rw [toricNativeFiniteSectionDensity_eq_generator h q s v hp, ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp,
    EReal.left_distrib_of_nonneg_of_ne_top
      (show 0 ≤ ((q : ℝ)⁻¹ : EReal) from EReal.coe_nonneg.mpr (by positivity))
      (EReal.coe_ne_top _), ← generatorLog_eq_log_sum]
  congr 1
  rw [← EReal.coe_inv, ← EReal.coe_mul]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← EReal.coe_neg, EReal.coe_eq_coe_iff]
  field_simp


/-- The actual original weight is a potential for the SAME full native Chern
form, throughout the original vertex chart. -/
theorem toricNativeVertexWeight_localPotential {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) :
    IsSmoothLocalPotential h.form.val (polytopeToricVertexChart γ hs v) univ (h.weight v) := by
  refine ⟨isOpen_univ, ?_, (h.smooth v).contDiffOn, fun z _ => (h.coeff v z).symm⟩
  intro z _
  change z ∈ (originalPolytopeNativeModelChart γ hs v).target
  rw [originalPolytopeNativeModelChart_target]
  exact mem_univ z

/-- Genuine holomorphic generators and an EXACT smooth remainder in EVERY
requested actual chart. Coefficient positivity is proved from positive degree. -/
theorem toricNativeFiniteSectionPotential_smoothTypeAt {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q)
    (e : ComplexChart n (PolytopeToricVariety γ hs))
    (z : ComplexModel n) (hz : z ∈ e.val.target) :
    ∃ f : Fin d → ComplexModel n → ℂ,
      SmoothLogarithmicTypeAt (chartFunction (toricNativeFiniteSectionPotential h q s) e)
        ((q : ℝ)⁻¹) f z := by
  let v := toricNativePreferredVertex γ hs (e.val.symm z)
  let c := polytopeToricVertexChart γ hs v
  let hid : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (id : PolytopeToricVariety γ hs → PolytopeToricVariety γ hs) := contMDiff_id
  let F : ComplexModel n → ComplexModel n := coordinateMap id e c
  let W : Set (ComplexModel n) := potentialDomain id e c univ
  have hW : IsOpen W := potentialDomain_isOpen hid e c isOpen_univ
  have hzW : z ∈ W := ⟨⟨hz, toricNativePreferredVertex_mem (e.val.symm z)⟩, mem_univ _⟩
  have hF : DifferentiableOn ℂ F W :=
    ((coordinateMap_contDiffOn hid e c).differentiableOn (by simp)).mono inter_subset_left
  let G := toricNativeFiniteSectionGenerators h q s v
  let f : Fin d → ComplexModel n → ℂ := fun j => G j ∘ F
  have hf : HolomorphicGeneratorsAt f z := by
    refine ⟨W, hW, hzW, fun j => ?_⟩
    exact (differentiable_toricNativeFiniteSectionGenerators h q s v j).comp_differentiableOn hF
  have hρpull := isSmoothLocalPotential_pullback hid e (toricNativeVertexWeight_localPotential h v)
  have hρ : ContDiffOn ℝ ∞ (h.weight v ∘ F) W := hρpull.2.2.1
  refine ⟨f, inv_pos.mpr (by exact_mod_cast hq), hf,
    (fun y => -(h.weight v (F y))), ?_, ?_⟩
  · filter_upwards [hW.mem_nhds hzW] with y hy
    exact (hρ.neg).contDiffAt (hW.mem_nhds hy)
  · filter_upwards [hW.mem_nhds hzW] with y hy
    change toricNativeFiniteSectionPotential h q s (e.val.symm y) =
      ((q : ℝ)⁻¹ : EReal) * generatorLog f y + (-(h.weight v (F y)) : ℝ)
    rw [toricNativeFiniteSectionPotential_eq_generator h q hq s v hy.1.2]
    change ((q : ℝ)⁻¹ : EReal) * generatorLog G (F y) - (h.weight v (F y) : EReal) =
      ((q : ℝ)⁻¹ : EReal) * generatorLog G (F y) + (-(h.weight v (F y)) : ℝ)
    rw [EReal.coe_neg, sub_eq_add_neg]



end SGPT.Toric

end
end ToricCanonicalFragment046
/- END SGPT.Toric.ToricNativePhiAnalyticBergman -/

/- BEGIN SGPT.Toric.ToricNativePhiPshBergman; source SHA256 313104f7961e588a05e8c4538d0f84b7353c527606e90a8acde40c3a82d2fc49 -/
section ToricCanonicalFragment047

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft HermitianHolomorphicLineBundle
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual rational logarithmic coefficient; smoothness across the base locus
is already produced by the genuine entire coefficients/physical metric. -/
theorem toricNativeFiniteSectionPotential_rationalAnalytic {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).HasRationalAnalyticChartType
      (toricNativeFiniteSectionPotential h q s) := by
  intro e z hz
  obtain ⟨f, hf⟩ := toricNativeFiniteSectionPotential_smoothTypeAt h q hq s e z hz
  have hrat : SmoothLogarithmicTypeAt (chartFunction (toricNativeFiniteSectionPotential h q s) e)
      (((q : ℚ)⁻¹ : ℚ) : ℝ) f z := by simpa using hf
  exact hrat.hasAnalyticSingularityTypeAt

/-- A literal finite enumeration of the ACTUAL produced full ON eigensections,
retaining the empty case rather than adding a nonzero-Hilbert-space assumption. -/
def toricNativePhiFiniteSections {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    Fin (Fintype.card (ToricNativeMultiplierCharacterIndex h q hq hφ)) →
      ToricNativePlainPowerSections h q := fun j =>
  toricNativePhiOrthonormalPlainSection h q hq hφ hinv ((Fintype.equivFin _).symm j)

/-- Exact full finite sum equality, proved by finite bijective reindexing. -/
theorem toricNativePhiFiniteSections_density {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (p : PolytopeToricVariety γ hs) :
    toricNativeFiniteSectionDensity h q (toricNativePhiFiniteSections h q hq hφ hinv) p =
      toricNativePhiBergmanDensity h q hq hφ hinv p := by
  exact (Fintype.equivFin (ToricNativeMultiplierCharacterIndex h q hq hφ)).symm.sum_comp
    (fun m => ENNReal.ofReal (‖toricNativePhiOrthonormalPlainSection h q hq hφ hinv m p‖ ^ 2))








end SGPT.Toric

end
end ToricCanonicalFragment047
/- END SGPT.Toric.ToricNativePhiPshBergman -/

/- BEGIN SGPT.Toric.ToricNativeSectionProducts; source SHA256 b620eb558dffdb5a64e86eee107a59406883cdd52e9bc16933615a6a8b31c5ca -/
section ToricCanonicalFragment048

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual original Cartier multiplication; entire coefficient products
manufacture the membership in the independent full section space. -/
def toricOriginalSectionProduct {D E : ToricDivisor γ hs}
    (s : toricSections D) (t : toricSections E) : toricSections (D + E) :=
  ⟨fun a => s.val a * t.val a, by
    intro v
    refine ⟨fun z => toricOriginalSectionCoeff s v z * toricOriginalSectionCoeff t v z,
      (differentiable_toricOriginalSectionCoeff s v).mul
        (differentiable_toricOriginalSectionCoeff t v), ?_⟩
    intro a
    dsimp only
    rw [toricOriginalSectionCoeff_torus s v a, toricOriginalSectionCoeff_torus t v a,
      toricCartierDatum_add, latticeCharacter_add, Units.val_mul]
    ring⟩

/-- Equality on every entire vertex chart, proved by dense-torus uniqueness. -/
theorem toricOriginalSectionCoeff_product {D E : ToricDivisor γ hs}
    (s : toricSections D) (t : toricSections E) (v : latticePolytopeVertices γ) :
    toricOriginalSectionCoeff (toricOriginalSectionProduct s t) v =
      fun z => toricOriginalSectionCoeff s v z * toricOriginalSectionCoeff t v z := by
  apply toricSectionCoeff_unique (D := D + E) v
    (differentiable_toricOriginalSectionCoeff _ v).continuous
    ((differentiable_toricOriginalSectionCoeff s v).continuous.mul
      (differentiable_toricOriginalSectionCoeff t v).continuous)
    (toricOriginalSectionCoeff_torus _ v)
  intro a
  change s.val a * t.val a = _
  rw [toricOriginalSectionCoeff_torus s v a, toricOriginalSectionCoeff_torus t v a,
    toricCartierDatum_add, latticeCharacter_add, Units.val_mul]
  simp only [Pi.mul_apply]
  ring

/-- Actual physical H0 multiplication for the internally constructed tensor
metric. Both inputs and output are genuine native holomorphic sections. -/
def toricNativeSectionProduct {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E)
    (s : ToricNativeHolomorphicSections h) (t : ToricNativeHolomorphicSections g) :
    ToricNativeHolomorphicSections (h.addMetric g) :=
  (toricNativeFullSectionEquiv (h.addMetric g)).symm
    (toricOriginalSectionProduct (toricNativeFullSectionEquiv h s)
      (toricNativeFullSectionEquiv g t))





end SGPT.Toric

end
end ToricCanonicalFragment048
/- END SGPT.Toric.ToricNativeSectionProducts -/

/- BEGIN SGPT.Toric.ToricFullLatticeFubiniStudy; source SHA256 98c80b6aaea9fab583f4e9a11bd41d8222ff6b04dc4134a44df6fab895b8a14e -/
section ToricCanonicalFragment049

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective.ComplexProjectiveSpace
open scoped Topology BigOperators ContDiff Manifold
variable {n d : ℕ} {M : Type*} [AddCommGroup M]

/-- Literal whole-chart monomial coordinates in the Euclidean projective
ratio model; no choice of an analytic extension occurs. -/
def monomialVertexModelRatio (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) : ComplexModel n → ComplexModel d :=
  fun z => modelPoint (monomialVertexRatioVector b β v (fun j => z j))

theorem differentiable_monomialVertexModelRatio (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) :
    Differentiable ℂ (monomialVertexModelRatio b β v) := by
  apply differentiable_modelPoint.comp
  apply differentiable_pi.mpr
  intro i
  change Differentiable ℂ (fun z : ComplexModel n =>
    ∏ j, z j ^ monomialVertexExponent b β v (v.succAbove i) j)
  intro z
  apply AnalyticAt.differentiableAt
  exact Finset.analyticAt_fun_prod _ (fun j _ =>
    ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).analyticAt z).pow _)

/-- Actual primitive basis neighbors give coordinate readback inside the
full affine projective polynomial map. -/
theorem monomialVertexModelRatio_readback (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hν : ∀ j, β (ν j) - β v = b j) (j : Fin n) :
    ∃ k : Fin d, ∀ z : ComplexModel n, monomialVertexModelRatio b β v z k = z j := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq
    (monomialVertexNeighbor_ne_vertex b β v ν hν j)
  refine ⟨k, fun z => ?_⟩
  change monomialVertexVector b β v (fun i => z i) (v.succAbove k) = z j
  rw [hk, monomialVertexVector_neighbor b β v ν hν]

/-- Differential injectivity is DERIVED by differentiating the actual
primitive-coordinate readbacks, throughout the whole original chart. -/
theorem monomialVertexModelRatio_fderiv_injective (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hν : ∀ j, β (ν j) - β v = b j) (z : ComplexModel n) :
    Function.Injective (fderiv ℝ (monomialVertexModelRatio b β v) z) := by
  let F := monomialVertexModelRatio b β v
  have hF : Differentiable ℂ F := differentiable_monomialVertexModelRatio b β v
  intro w w' hww'
  ext j
  obtain ⟨k, hk⟩ := monomialVertexModelRatio_readback b β v ν hν j
  have hcoord : (fun x : ComplexModel n => F x k) =
      (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ) := funext hk
  have hD := ((EuclideanSpace.proj k : ComplexModel d →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp z
    ((hF z).restrictScalars ℝ).hasFDerivAt
  change HasFDerivAt (fun x : ComplexModel n => F x k) _ z at hD
  rw [hcoord] at hD
  have hread := hD.unique
    ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt
  have hw := congrArg (fun L => L w) hread
  have hw' := congrArg (fun L => L w') hread
  change fderiv ℝ F z w k = w j at hw
  change fderiv ℝ F z w' k = w' j at hw'
  rw [← hw, ← hw']
  exact congrArg (fun u : ComplexModel d => u k) hww'

/-- Full ddC pullback and internally proved immersion give strict local
positivity even on the toric boundary; vertex-only sums are not substituted. -/
theorem monomialVertexModelRatio_fs_strictlyPositive (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (ν : Fin n → Fin (d + 1))
    (hν : ∀ j, β (ν j) - β v = b j) (z : ComplexModel n)
    {w : ComplexModel n} (hw : w ≠ 0) :
    0 < smoothDDC (fun y => fsPotential (monomialVertexModelRatio b β v y)) z
      ![w, Complex.I • w] := by
  let F := monomialVertexModelRatio b β v
  have hF : Differentiable ℂ F := differentiable_monomialVertexModelRatio b β v
  have hFs : ContDiffOn ℂ ∞ F univ :=
    contDiffOn_of_differentiableOn_complex hF.differentiableOn isOpen_univ
  rw [HolomorphicDDC.smoothDDC_comp isOpen_univ isOpen_univ hFs
    contDiff_fsPotential.contDiffOn (mapsTo_univ _ _) (mem_univ z)]
  let L := fderiv ℝ F z
  have hLw : L w ≠ 0 := by
    intro h0
    exact hw ((monomialVertexModelRatio_fderiv_injective b β v ν hν z)
      (h0.trans L.map_zero.symm))
  have hvec : L ∘ ![w, Complex.I • w] = ![L w, Complex.I • L w] := by
    funext i
    fin_cases i
    · rfl
    · change fderiv ℝ F z (Complex.I • w) = Complex.I • fderiv ℝ F z w
      rw [(hF z).fderiv_restrictScalars ℝ]
      exact (fderiv ℂ F z).map_smul Complex.I w
  change 0 < smoothDDC fsPotential (F z) (L ∘ ![w, Complex.I • w])
  rw [hvec]
  exact fsPotential_strictlyPositive (F z) hLw

/-- Exact literal logarithm of the FULL monomial coefficient sum. -/
theorem monomialVertexModelRatio_fs_eq_log_sum (b : Module.Basis (Fin n) ℤ M)
    (β : Fin (d + 1) → M) (v : Fin (d + 1)) (z : ComplexModel n) :
    fsPotential (monomialVertexModelRatio b β v z) =
      Real.log (∑ i, ‖monomialVertexVector b β v (fun j => z j) i‖ ^ 2) := by
  rw [fsPotential_eq_log_homNormSq v]
  have hvec : affineLift v (monomialVertexModelRatio b β v z) =
      monomialVertexVector b β v (fun j => z j) := by
    exact insertNth_monomialVertexRatioVector b β v (fun j => z j)
  rw [hvec]
  rfl

variable {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual full-lattice local FS weight for the ORIGINAL polytope. -/
def toricFullLatticeFsWeight (v : latticePolytopeVertices γ) (z : ComplexModel n) : ℝ :=
  fsPotential (monomialVertexModelRatio (originalPolytopeNativeBasis γ hs v)
    (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v) z)

theorem toricFullLatticeFsWeight_eq_log_sum (v : latticePolytopeVertices γ)
    (z : ComplexModel n) :
    toricFullLatticeFsWeight (hs := hs) v z =
      Real.log (∑ i, ‖originalPolytopeNativeVector γ hs v (fun j => z j) i‖ ^ 2) :=
  monomialVertexModelRatio_fs_eq_log_sum _ _ _ _

/-- Whole-chart strict positivity is internally manufactured from ORIGINAL
edge smoothness and the full original lattice enumeration. -/
theorem toricFullLatticeFsWeight_strictlyPositive (v : latticePolytopeVertices γ)
    (z : ComplexModel n) {w : ComplexModel n} (hw : w ≠ 0) :
    0 < smoothDDC (toricFullLatticeFsWeight (hs := hs) v) z ![w, Complex.I • w] := by
  apply monomialVertexModelRatio_fs_strictlyPositive
    (originalPolytopeNativeBasis γ hs v) (originalPolytopeFullExponents γ)
    (originalPolytopeNativeVertexIndex γ v) (originalPolytopeNativeNeighborIndex γ hs v) ?_ z hw
  intro j
  have hv : originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ v) = v.val :=
    latticePolytopeExponentFamily_vertexIndex γ (originalPolytopeFullEnumeration γ) v
  simpa only [hv] using (originalPolytopeNativePiChart_spec γ hs v).1 j

end SGPT.Toric

end
end ToricCanonicalFragment049
/- END SGPT.Toric.ToricFullLatticeFubiniStudy -/

/- BEGIN SGPT.Toric.ToricFullLatticeSections; source SHA256 7dc043bf64b513029945d665e3bbcdfbcb766fa1a9ec318cc1d5c54da9171764 -/
section ToricCanonicalFragment050

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective.ComplexProjectiveSpace
open scoped Topology BigOperators ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual FULL original lattice enumeration lies in the independently
defined ample divisor polytope. -/
theorem toricFullLatticeExponent_mem
    (i : Fin (originalPolytopeFullIndexSize γ + 1)) :
    originalPolytopeFullExponents γ i ∈ toricLatticePoints (polytopeToricAmpleDivisor γ hs) := by
  change latticeVector _ ∈ toricDivisorPolytope _
  rw [toricDivisorPolytope_ampleDivisor]
  change (EuclideanSpace.equiv (Fin n) ℝ) (latticeVector _) ∈ latticePolytope γ
  have hi := (originalPolytopeFullEnumeration γ i).property
  change AlmostSemigroup.Counting.integerCast (originalPolytopeFullExponents γ i) ∈ latticePolytope γ at hi
  simpa only [latticeVector, ContinuousLinearEquiv.apply_symm_apply] using hi

/-- Genuine full original Cartier eigen-sections, with no H0 presentation
or generation certificate supplied. -/
def toricFullLatticeSection (i : Fin (originalPolytopeFullIndexSize γ + 1)) :
    toricSections (polytopeToricAmpleDivisor γ hs) :=
  ⟨fun a => (latticeCharacter (originalPolytopeFullExponents γ i) a : ℂ),
    latticeCharacter_mem_toricSections _ (toricFullLatticeExponent_mem (hs := hs) i)⟩

/-- Chosen entire coefficients are the actual full-lattice polynomials on
EVERY original vertex chart, including all boundary points. -/
theorem toricFullLatticeSection_coeff (i : Fin (originalPolytopeFullIndexSize γ + 1))
    (v : latticePolytopeVertices γ) :
    toricOriginalSectionCoeff (toricFullLatticeSection (hs := hs) i) v =
      fun z => originalPolytopeNativeVector γ hs v (fun j => z j) i := by
  have hmono : toricOriginalSectionCoeff (toricFullLatticeSection (hs := hs) i) v =
      toricMonomial (polytopeToricAmpleDivisor γ hs) v (originalPolytopeFullExponents γ i) := by
    apply toricSectionCoeff_unique (D := polytopeToricAmpleDivisor γ hs) v
      (differentiable_toricOriginalSectionCoeff _ v).continuous
      (differentiable_toricMonomial _ v _).continuous (toricOriginalSectionCoeff_torus _ v)
    exact latticeCharacter_eq_toricMonomial _ (toricFullLatticeExponent_mem (hs := hs) i) v
  rw [hmono]
  funext z
  have hv : originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ v) = v.val :=
    latticePolytopeExponentFamily_vertexIndex γ (originalPolytopeFullEnumeration γ) v
  simp only [toricMonomial, toricCartierDatum_ampleDivisor, originalPolytopeNativeVector,
    monomialVertexVector, monomialVertexExponent, hv, map_sub, Finsupp.sub_apply,
    basis_repr_eq_intPairing]

/-- Exact coefficient-sum readback of the local full-lattice FS weight. -/
theorem toricFullLatticeFsWeight_eq_log_coeff_sum (v : latticePolytopeVertices γ)
    (z : ComplexModel n) :
    toricFullLatticeFsWeight (hs := hs) v z =
      Real.log (∑ i, ‖toricOriginalSectionCoeff (toricFullLatticeSection (hs := hs) i) v z‖ ^ 2) := by
  simp only [toricFullLatticeSection_coeff, toricFullLatticeFsWeight_eq_log_sum]

/-- The chosen original vertex coefficient proves genuine positive density. -/
theorem toricFullLatticeCoeffSum_pos (v : latticePolytopeVertices γ) (z : ComplexModel n) :
    0 < ∑ i, ‖toricOriginalSectionCoeff (toricFullLatticeSection (hs := hs) i) v z‖ ^ 2 := by
  have hterm : ‖toricOriginalSectionCoeff
      (toricFullLatticeSection (hs := hs) (originalPolytopeNativeVertexIndex γ v)) v z‖ ^ 2 = 1 := by
    rw [toricFullLatticeSection_coeff]
    change ‖monomialVertexVector _ _ _ _ (originalPolytopeNativeVertexIndex γ v)‖ ^ 2 = 1
    rw [monomialVertexVector_vertex, norm_one, one_pow]
  have hle := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin (originalPolytopeFullIndexSize γ + 1)))) =>
      sq_nonneg ‖toricOriginalSectionCoeff (toricFullLatticeSection (hs := hs) i) v z‖)
    (Finset.mem_univ (originalPolytopeNativeVertexIndex γ v))
  rw [hterm] at hle
  exact lt_of_lt_of_le zero_lt_one hle

/-- The actual full lattice FS weights are smooth on the WHOLE charts. -/
theorem contDiff_toricFullLatticeFsWeight (v : latticePolytopeVertices γ) :
    ContDiff ℝ ∞ (toricFullLatticeFsWeight (hs := hs) v) := by
  have hF := contDiffOn_univ.mp (contDiffOn_of_differentiableOn_complex
    (differentiable_monomialVertexModelRatio (originalPolytopeNativeBasis γ hs v)
      (originalPolytopeFullExponents γ) (originalPolytopeNativeVertexIndex γ v)).differentiableOn
    isOpen_univ)
  exact contDiff_fsPotential.comp (hF.restrict_scalars ℝ)

/-- True full-overlap difference of weights, derived from the genuine
Cartier coefficient transition and nonvanishing, including boundary zeros. -/
theorem toricFullLatticeFsWeight_sub (v w : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    toricFullLatticeFsWeight (hs := hs) v (originalPolytopeNativeModelChart γ hs v p) -
      toricFullLatticeFsWeight (hs := hs) w (originalPolytopeNativeModelChart γ hs w p) =
      Real.log (Complex.normSq (toricCartierTransition (polytopeToricAmpleDivisor γ hs) w v p)) := by
  rw [toricFullLatticeFsWeight_eq_log_coeff_sum, toricFullLatticeFsWeight_eq_log_coeff_sum]
  have hsum : (∑ i, ‖toricOriginalSectionCoeff (toricFullLatticeSection (hs := hs) i) v
      (originalPolytopeNativeModelChart γ hs v p)‖ ^ 2) =
      ‖toricCartierTransition (polytopeToricAmpleDivisor γ hs) w v p‖ ^ 2 *
        ∑ i, ‖toricOriginalSectionCoeff (toricFullLatticeSection (hs := hs) i) w
          (originalPolytopeNativeModelChart γ hs w p)‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [toricOriginalSectionCoeff_transition _ w v hw hv, norm_mul, mul_pow]
  rw [hsum, Real.log_mul
    (pow_pos (norm_pos_iff.mpr (toricCartierTransition_ne_zero _ w v hw hv)) 2).ne'
    (toricFullLatticeCoeffSum_pos w _).ne', add_sub_cancel_right]
  rw [Complex.normSq_eq_norm_sq]

end SGPT.Toric

end
end ToricCanonicalFragment050
/- END SGPT.Toric.ToricFullLatticeSections -/

/- BEGIN SGPT.Toric.ToricFullLatticeMetric; source SHA256 8fd478f754aabf76fc14dec37a03466103e2a967e1ff56a0cd78b381188f36f1 -/
section ToricCanonicalFragment051

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology BigOperators ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Invariance of the actual full lattice weight follows from actual
coordinate norms and original character norms on the compact torus. -/
theorem toricFullLatticeFsWeight_action (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (ha : IsCompactTorusElement a) (z : ComplexModel n) :
    toricFullLatticeFsWeight (hs := hs) v (originalPolytopeNativeModelActionLinear γ hs v a z) =
      toricFullLatticeFsWeight (hs := hs) v z := by
  have hnorm : ∀ i, ‖(originalPolytopeNativeModelActionLinear γ hs v a z) i‖ = ‖z i‖ := by
    intro i
    change ‖(latticeCharacter (originalPolytopeNativeBasis γ hs v i) a : ℂ) * z i‖ = _
    rw [norm_mul]
    have h1 : ‖(latticeCharacter (originalPolytopeNativeBasis γ hs v i) a : ℂ)‖ = 1 := by
      simp only [latticeCharacter, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod,
        Units.val_zpow_eq_zpow_val, norm_prod, norm_zpow]
      exact Finset.prod_eq_one fun j _ => by rw [ha j, one_zpow]
    rw [h1, one_mul]
  simp only [toricFullLatticeFsWeight_eq_log_sum, originalPolytopeNativeVector,
    monomialVertexVector, norm_prod, norm_pow, hnorm]

/-- The actual ample Cartier transition law is produced from the genuine
full-overlap coefficient identity on the dense torus. -/
theorem toricFullLatticeFsWeight_transition (v w : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) :
    toricFullLatticeFsWeight (hs := hs) v
        (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) +
        latticeFunctional (toricCartierDatum (polytopeToricAmpleDivisor γ hs) v) (unitTorusLog a) =
      toricFullLatticeFsWeight (hs := hs) w
        (originalPolytopeNativeModelChart γ hs w (polytopeToricEmbedding γ hs a)) +
        latticeFunctional (toricCartierDatum (polytopeToricAmpleDivisor γ hs) w) (unitTorusLog a) := by
  have hdiff := toricFullLatticeFsWeight_sub (hs := hs) v w
    (toricNativeEmbedding_mem_chartSource v a) (toricNativeEmbedding_mem_chartSource w a)
  rw [toricCartierTransition_embedding, Complex.normSq_eq_norm_sq,
    latticeCharacter_log_norm_sq] at hdiff
  change _ = latticeFunctional
    (toricCartierDatum (polytopeToricAmpleDivisor γ hs) w -
      toricCartierDatum (polytopeToricAmpleDivisor γ hs) v) (unitTorusLog a) at hdiff
  have hpair : latticeFunctional
      (toricCartierDatum (polytopeToricAmpleDivisor γ hs) w -
        toricCartierDatum (polytopeToricAmpleDivisor γ hs) v) (unitTorusLog a) =
      latticeFunctional (toricCartierDatum (polytopeToricAmpleDivisor γ hs) w) (unitTorusLog a) -
        latticeFunctional (toricCartierDatum (polytopeToricAmpleDivisor γ hs) v) (unitTorusLog a) := by
    simp only [latticeFunctional_apply, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  rw [hpair] at hdiff
  linarith

/-- Full normalized ddC of the actual full-lattice weight difference is zero
on the ENTIRE overlap, because the true transition is a holomorphic unit. -/
theorem smoothDDC_toricFullLatticeFsWeight_sub (v w : latticePolytopeVertices γ)
    (e : ComplexChart n (PolytopeToricVariety γ hs)) (z : ComplexModel n)
    (hz : z ∈ e.val.target)
    (hv : e.val.symm z ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : e.val.symm z ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    smoothDDC (fun u =>
      toricFullLatticeFsWeight (hs := hs) v (originalPolytopeNativeModelChart γ hs v (e.val.symm u)) -
        toricFullLatticeFsWeight (hs := hs) w (originalPolytopeNativeModelChart γ hs w (e.val.symm u))) z = 0 := by
  let O := e.val.target ∩ e.val.symm ⁻¹'
    ((originalPolytopeNativeModelChart γ hs w).source ∩
      (originalPolytopeNativeModelChart γ hs v).source)
  have hO : IsOpen O := e.val.isOpen_inter_preimage_symm
    ((originalPolytopeNativeModelChart γ hs w).open_source.inter
      (originalPolytopeNativeModelChart γ hs v).open_source)
  have hzO : z ∈ O := ⟨hz, hw, hv⟩
  let f := fun u => toricCartierTransition (polytopeToricAmpleDivisor γ hs) w v (e.val.symm u)
  have heq : (fun u =>
      toricFullLatticeFsWeight (hs := hs) v (originalPolytopeNativeModelChart γ hs v (e.val.symm u)) -
        toricFullLatticeFsWeight (hs := hs) w (originalPolytopeNativeModelChart γ hs w (e.val.symm u))) =ᶠ[𝓝 z]
      fun u => Real.log (Complex.normSq (f u)) := by
    filter_upwards [hO.mem_nhds hzO] with u hu
    exact toricFullLatticeFsWeight_sub v w hu.2.2 hu.2.1
  rw [smoothDDC_congr heq]
  apply PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
  · filter_upwards [hO.mem_nhds hzO] with u hu
    exact (differentiableOn_toricCartierTransition_comp_symm
      (polytopeToricAmpleDivisor γ hs) w v e).differentiableAt (hO.mem_nhds hu)
  · exact toricCartierTransition_ne_zero _ w v hw hv

/-- The genuine full lattice weights satisfy ALL original global metric
gluing data; no incoming metric or positivity certificate is used. -/
def toricFullLatticeWeightFamily : ToricWeightFamily (polytopeToricAmpleDivisor γ hs) where
  weight := toricFullLatticeFsWeight
  smooth := contDiff_toricFullLatticeFsWeight
  invariant := toricFullLatticeFsWeight_action
  transition := toricFullLatticeFsWeight_transition
  pluriharmonic := smoothDDC_toricFullLatticeFsWeight_sub

/-- The actual invariant ample full-lattice Fubini--Study metric. -/
def toricFullLatticeMetric : BigToricMetric (polytopeToricAmpleDivisor γ hs) :=
  (toricFullLatticeWeightFamily (hs := hs)).toBigToricMetric

/-- Strict global positivity follows in EVERY chart from the genuine
original atlas and the internally proved full-lattice local immersion. -/
theorem toricFullLatticeMetric_isKahler :
    (toricFullLatticeMetric (hs := hs)).form.val.IsKahler := by
  refine ⟨?_, (toricFullLatticeMetric (hs := hs)).form.property.1⟩
  intro e z hz
  refine ⟨(toricFullLatticeMetric (hs := hs)).form.property.2 e z hz, ?_⟩
  obtain ⟨v, hv⟩ := e.property
  have he : e = polytopeToricVertexChart γ hs v := Subtype.ext hv.symm
  subst e
  rw [(toricFullLatticeMetric (hs := hs)).coeff v z]
  exact fun w hw => toricFullLatticeFsWeight_strictlyPositive (hs := hs) v z hw

/-- Actual native H0 sections, transported through the already proved FULL
physical dictionary from the original Cartier characters. -/
def toricFullLatticeNativeSection (i : Fin (originalPolytopeFullIndexSize γ + 1)) :
    ToricNativeHolomorphicSections (toricFullLatticeMetric (hs := hs)) :=
  (toricNativeFullSectionEquiv (toricFullLatticeMetric (hs := hs))).symm
    (toricFullLatticeSection (hs := hs) i)

/-- The internally produced full auxiliary family has EXACT physical
unit density on the entire original variety, including the boundary. -/
theorem toricFullLatticeNativeSection_sum_norm_sq (p : PolytopeToricVariety γ hs) :
    ∑ i, ‖toricFullLatticeNativeSection (hs := hs) i p‖ ^ 2 = 1 := by
  let v := toricNativePreferredVertex γ hs p
  have hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source := toricNativePreferredVertex_mem p
  simp only [toricFullLatticeNativeSection, toricNativeFullSectionEquiv_symm_norm_sq _ _ v hv]
  rw [← Finset.sum_mul]
  change _ * Real.exp (-toricFullLatticeFsWeight (hs := hs) v
    (originalPolytopeNativeModelChart γ hs v p)) = 1
  rw [toricFullLatticeFsWeight_eq_log_coeff_sum, Real.exp_neg,
    Real.exp_log (toricFullLatticeCoeffSum_pos v _), mul_inv_cancel₀
      (toricFullLatticeCoeffSum_pos v _).ne']

end SGPT.Toric

end
end ToricCanonicalFragment051
/- END SGPT.Toric.ToricFullLatticeMetric -/

/- BEGIN SGPT.Toric.ToricNativeNegativeTwistProducts; source SHA256 7aeabe0ae2c569a3518ba66f67d45ff9b167210fe428b7d472597db1756ef94a -/
section ToricCanonicalFragment052

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology BigOperators ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

private theorem latticeFunctional_zsmul_apply (c : ℤ) (m : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) :
    latticeFunctional (c • m) x = (c : ℝ) * latticeFunctional m x := by
  simp only [latticeFunctional_apply, Pi.smul_apply, smul_eq_mul, Int.cast_mul,
    Finset.mul_sum, mul_assoc]

private theorem latticeFunctional_sub_apply (m m' : Fin n → ℤ)
    (x : EuclideanSpace ℝ (Fin n)) :
    latticeFunctional (m - m') x = latticeFunctional m x - latticeFunctional m' x := by
  simp only [latticeFunctional_apply, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]

namespace BigToricMetric

/-- Actual signed tensor powers, retaining the literal full curvature form. -/
def zsmulMetric {D : ToricDivisor γ hs} (h : BigToricMetric D) (c : ℤ) :
    BigToricMetric (c • D) where
  form := (c : ℝ) • h.form
  weight v z := (c : ℝ) * h.weight v z
  smooth v := contDiff_const.mul (h.smooth v)
  coeff v z := by
    change (c : ℝ) • h.form.val.coeff (polytopeToricVertexChart γ hs v) z = _
    rw [h.coeff v z]
    exact (smoothDDC_smul isOpen_univ (h.smooth v).contDiffOn (c : ℝ) (mem_univ z)).symm
  invariant v a ha z := by rw [h.invariant v a ha z]
  transition v w a := by
    rw [toricCartierDatum_smul, toricCartierDatum_smul,
      latticeFunctional_zsmul_apply, latticeFunctional_zsmul_apply,
      ← mul_add, ← mul_add, h.transition v w a]

/-- Actual dual tensor twist, with literal difference curvature and weights. -/
def subMetric {D E : ToricDivisor γ hs} (h : BigToricMetric D) (g : BigToricMetric E) :
    BigToricMetric (D - E) where
  form := h.form - g.form
  weight v z := h.weight v z - g.weight v z
  smooth v := (h.smooth v).sub (g.smooth v)
  coeff v z := by
    rw [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      ← sub_eq_add_neg, h.coeff v z, g.coeff v z]
    exact (smoothDDC_sub isOpen_univ (h.smooth v).contDiffOn
      (g.smooth v).contDiffOn (mem_univ z)).symm
  invariant v a ha z := by rw [h.invariant v a ha z, g.invariant v a ha z]
  transition v w a := by
    rw [toricCartierDatum_sub, toricCartierDatum_sub,
      latticeFunctional_sub_apply, latticeFunctional_sub_apply]
    linarith [h.transition v w a, g.transition v w a]

end BigToricMetric

/-- Transport only the Cartier divisor equality. -/
def toricOriginalSectionCast {D E : ToricDivisor γ hs}
    (hDE : D = E) (s : toricSections D) : toricSections E := hDE ▸ s

theorem toricOriginalSectionCoeff_cast {D E : ToricDivisor γ hs}
    (hDE : D = E) (s : toricSections D) (v : latticePolytopeVertices γ) :
    toricOriginalSectionCoeff (toricOriginalSectionCast hDE s) v =
      toricOriginalSectionCoeff s v := by
  subst E
  rfl

/-- Actual negative-twist section times auxiliary section, returning to
H0 of the original plain power with its original physical metric. -/
def toricNativeNegativeTwistProduct {D A : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric A) (q : ℕ)
    (s : ToricNativeHolomorphicSections ((h.zsmulMetric (q : ℤ)).subMetric g))
    (t : ToricNativeHolomorphicSections g) : ToricNativePlainPowerSections h q :=
  (toricNativePlainPowerFullSectionEquiv h q).symm
    (toricOriginalSectionCast (sub_add_cancel ((q : ℤ) • D) A)
      (toricOriginalSectionProduct
        (toricNativeFullSectionEquiv ((h.zsmulMetric (q : ℤ)).subMetric g) s)
        (toricNativeFullSectionEquiv g t)))

/-- Exact physical product in the SAME original h^q, for every q including
zero and for all boundary points. -/
theorem toricNativeNegativeTwistProduct_norm_sq {D A : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric A) (q : ℕ)
    (s : ToricNativeHolomorphicSections ((h.zsmulMetric (q : ℤ)).subMetric g))
    (t : ToricNativeHolomorphicSections g) (p : PolytopeToricVariety γ hs) :
    ‖toricNativeNegativeTwistProduct h g q s t p‖ ^ 2 = ‖s p‖ ^ 2 * ‖t p‖ ^ 2 := by
  let v := toricNativePreferredVertex γ hs p
  have hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source :=
    toricNativePreferredVertex_mem p
  have hsnorm := toricNativeFullSectionEquiv_symm_norm_sq
    ((h.zsmulMetric (q : ℤ)).subMetric g)
    (toricNativeFullSectionEquiv ((h.zsmulMetric (q : ℤ)).subMetric g) s) v hv
  have ht := toricNativeFullSectionEquiv_symm_norm_sq g (toricNativeFullSectionEquiv g t) v hv
  simp only [LinearEquiv.symm_apply_apply] at hsnorm ht
  rw [hsnorm, ht]
  unfold toricNativeNegativeTwistProduct
  rw [toricNativePlainPowerFullSectionEquiv_symm_norm_sq _ _ _ v hv,
    toricOriginalSectionCoeff_cast, toricOriginalSectionCoeff_product, norm_mul, mul_pow]
  dsimp only [BigToricMetric.subMetric, BigToricMetric.zsmulMetric]
  simp only [Int.cast_natCast]
  have hexp : Real.exp (-((q : ℝ) * h.weight v
      (originalPolytopeNativeModelChart γ hs v p) - g.weight v
      (originalPolytopeNativeModelChart γ hs v p))) *
      Real.exp (-g.weight v (originalPolytopeNativeModelChart γ hs v p)) =
      Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  conv_rhs => rw [mul_mul_mul_comm]
  rw [hexp]

end SGPT.Toric

end
end ToricCanonicalFragment052
/- END SGPT.Toric.ToricNativeNegativeTwistProducts -/

/- BEGIN SGPT.Toric.ToricNativeStrictProductMargin; source SHA256 1efe0040d1f89c1d4a3c416f73aff0101bcefb32bced30ddc8c893ff0794570f -/
section ToricCanonicalFragment053

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual fixed ample negative twist of the original qh. -/
def toricNativeNegativeTwistMetric {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ) :=
  (h.zsmulMetric (q : ℤ)).subMetric (toricFullLatticeMetric (hs := hs))

/-- Genuine finite products in the ORIGINAL physical plain power L^q. -/
def toricNativeStrictProductSections {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {a : ℕ}
    (s : Fin a → ToricNativeHolomorphicSections (toricNativeNegativeTwistMetric h q)) :
    Fin (a * (originalPolytopeFullIndexSize γ + 1)) → ToricNativePlainPowerSections h q :=
  fun k => toricNativeNegativeTwistProduct h (toricFullLatticeMetric (hs := hs)) q
    (s (finProdFinEquiv.symm k).1)
    (toricFullLatticeNativeSection (hs := hs) (finProdFinEquiv.symm k).2)

/-- Exact physical sum identity proved by actual product norms and the
internally produced unit-density auxiliary family. -/
theorem toricNativeStrictProductSections_sum_norm_sq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {a : ℕ}
    (s : Fin a → ToricNativeHolomorphicSections (toricNativeNegativeTwistMetric h q))
    (p : PolytopeToricVariety γ hs) :
    ∑ k, ‖toricNativeStrictProductSections h q s k p‖ ^ 2 = ∑ i, ‖s i p‖ ^ 2 := by
  calc
    _ = ∑ k : Fin a × Fin (originalPolytopeFullIndexSize γ + 1),
        ‖toricNativeNegativeTwistProduct h (toricFullLatticeMetric (hs := hs)) q (s k.1)
          (toricFullLatticeNativeSection (hs := hs) k.2) p‖ ^ 2 :=
      finProdFinEquiv.symm.sum_comp (fun k : Fin a × Fin (originalPolytopeFullIndexSize γ + 1) =>
        ‖toricNativeNegativeTwistProduct h (toricFullLatticeMetric (hs := hs)) q (s k.1)
          (toricFullLatticeNativeSection (hs := hs) k.2) p‖ ^ 2)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [toricNativeNegativeTwistProduct_norm_sq]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, toricFullLatticeNativeSection_sum_norm_sq, mul_one]
      rfl

theorem toricNativeStrictProductSections_density {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {a : ℕ}
    (s : Fin a → ToricNativeHolomorphicSections (toricNativeNegativeTwistMetric h q))
    (p : PolytopeToricVariety γ hs) :
    toricNativeFiniteSectionDensity h q (toricNativeStrictProductSections h q s) p =
      ENNReal.ofReal (∑ i, ‖s i p‖ ^ 2) := by
  unfold toricNativeFiniteSectionDensity
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    toricNativeStrictProductSections_sum_norm_sq]

/-- Entire original Cartier coefficients of the actual negative-twist family. -/
def toricNativeStrictProductGenerators {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {a : ℕ}
    (s : Fin a → ToricNativeHolomorphicSections (toricNativeNegativeTwistMetric h q))
    (v : latticePolytopeVertices γ) : Fin a → ComplexModel n → ℂ :=
  fun i => toricOriginalSectionCoeff
    (toricNativeFullSectionEquiv (toricNativeNegativeTwistMetric h q) (s i)) v

theorem toricNativeStrictProductSections_density_generator {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {a : ℕ}
    (s : Fin a → ToricNativeHolomorphicSections (toricNativeNegativeTwistMetric h q))
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    toricNativeFiniteSectionDensity h q (toricNativeStrictProductSections h q s) p =
      ENNReal.ofReal (∑ i, ‖toricNativeStrictProductGenerators h q s v i
        (originalPolytopeNativeModelChart γ hs v p)‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-(toricNativeNegativeTwistMetric h q).weight v
        (originalPolytopeNativeModelChart γ hs v p))) := by
  rw [toricNativeStrictProductSections_density, ← ENNReal.ofReal_mul
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [toricNativeStrictProductGenerators, LinearEquiv.symm_apply_apply] using
    toricNativeFullSectionEquiv_symm_norm_sq (toricNativeNegativeTwistMetric h q)
      (toricNativeFullSectionEquiv (toricNativeNegativeTwistMetric h q) (s i)) v hv

/-- Exact SAME-theta strict-margin local potential formula; poles and
empty families are retained as extended-real values. -/
theorem toricNativeStrictProductPotential_eq_generator {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q) {a : ℕ}
    (s : Fin a → ToricNativeHolomorphicSections (toricNativeNegativeTwistMetric h q))
    (v : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    toricNativeFiniteSectionPotential h q (toricNativeStrictProductSections h q s) p =
      ((q : ℝ)⁻¹ : EReal) * generatorLog (toricNativeStrictProductGenerators h q s v)
        (originalPolytopeNativeModelChart γ hs v p) -
      ((h.weight v (originalPolytopeNativeModelChart γ hs v p) -
        (q : ℝ)⁻¹ * (toricFullLatticeMetric (hs := hs)).weight v
          (originalPolytopeNativeModelChart γ hs v p) : ℝ) : EReal) := by
  unfold toricNativeFiniteSectionPotential
  rw [toricNativeStrictProductSections_density_generator h q s v hv, ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp,
    EReal.left_distrib_of_nonneg_of_ne_top
      (show 0 ≤ ((q : ℝ)⁻¹ : EReal) from EReal.coe_nonneg.mpr (by positivity))
      (EReal.coe_ne_top _), ← generatorLog_eq_log_sum]
  rw [← EReal.coe_inv, ← EReal.coe_mul]
  have hreal : (q : ℝ)⁻¹ * (-(toricNativeNegativeTwistMetric h q).weight v
      (originalPolytopeNativeModelChart γ hs v p)) =
      -(h.weight v (originalPolytopeNativeModelChart γ hs v p) -
        (q : ℝ)⁻¹ * (toricFullLatticeMetric (hs := hs)).weight v
          (originalPolytopeNativeModelChart γ hs v p)) := by
    dsimp only [toricNativeNegativeTwistMetric, BigToricMetric.subMetric, BigToricMetric.zsmulMetric]
    simp only [Int.cast_natCast]
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
  rw [hreal, EReal.coe_neg, ← sub_eq_add_neg]

/-- Actual global raw margin theta-q^-1 omega_A for the original plain
finite product potential, produced without an incoming current bound. -/
theorem toricNativeStrictProductPotential_thetaPlurisubharmonic {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q) {a : ℕ}
    (s : Fin a → ToricNativeHolomorphicSections (toricNativeNegativeTwistMetric h q)) :
    ThetaPlurisubharmonic
      (h.form - (q : ℝ)⁻¹ • (toricFullLatticeMetric (hs := hs)).form).val
      (toricNativeFiniteSectionPotential h q (toricNativeStrictProductSections h q s)) := by
  intro e z hz
  obtain ⟨v, hv⟩ := e.property
  have he : e = polytopeToricVertexChart γ hs v := Subtype.ext hv.symm
  subst e
  let H := toricFullLatticeMetric (hs := hs)
  let ρ : ComplexModel n → ℝ := fun y => h.weight v y - (q : ℝ)⁻¹ * H.weight v y
  have htarget : (originalPolytopeNativeModelChart γ hs v).target = univ :=
    originalPolytopeNativeModelChart_target γ hs v
  have hρ : IsSmoothLocalPotential (h.form - (q : ℝ)⁻¹ • H.form).val
      (polytopeToricVertexChart γ hs v) univ ρ := by
    refine ⟨isOpen_univ, ?_, ((h.smooth v).sub (contDiff_const.mul (H.smooth v))).contDiffOn, ?_⟩
    · intro y _
      change y ∈ (originalPolytopeNativeModelChart γ hs v).target
      rw [htarget]
      exact mem_univ y
    · intro y hy
      change smoothDDC (fun y => h.weight v y - (q : ℝ)⁻¹ * H.weight v y) y = _
      rw [smoothDDC_sub isOpen_univ (h.smooth v).contDiffOn
        (contDiff_const.mul (H.smooth v)).contDiffOn hy]
      change smoothDDC (h.weight v) y -
        smoothDDC (fun x => (q : ℝ)⁻¹ • H.weight v x) y = _
      rw [smoothDDC_smul isOpen_univ (H.smooth v).contDiffOn (q : ℝ)⁻¹ hy,
        sub_eq_add_neg h.form ((q : ℝ)⁻¹ • H.form),
        ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
        ClosedRealOneOneForm.coeff_smul, h.coeff v y, H.coeff v y]
      rfl
  refine ⟨univ, ρ, mem_univ z, hρ, ?_⟩
  intro y _
  have hgen : HolomorphicGeneratorsAt (toricNativeStrictProductGenerators h q s v) y :=
    ⟨univ, isOpen_univ, mem_univ y, fun i =>
      (differentiable_toricOriginalSectionCoeff _ v).differentiableOn⟩
  have hlog := plurisubharmonicAt_scaled_generatorLog hgen
    (inv_pos.mpr (show (0 : ℝ) < q by exact_mod_cast hq))
  apply hlog.congr
  filter_upwards with u
  change ((q : ℝ)⁻¹ : EReal) * generatorLog (toricNativeStrictProductGenerators h q s v) u =
    toricNativeFiniteSectionPotential h q (toricNativeStrictProductSections h q s)
      ((originalPolytopeNativeModelChart γ hs v).symm u) + (ρ u : EReal)
  have hu : u ∈ (originalPolytopeNativeModelChart γ hs v).target := by
    rw [htarget]
    exact mem_univ u
  rw [toricNativeStrictProductPotential_eq_generator h q hq s v
    ((originalPolytopeNativeModelChart γ hs v).map_target hu),
    (originalPolytopeNativeModelChart γ hs v).right_inv hu]
  exact EReal.sub_add_cancel.symm

end SGPT.Toric

end
end ToricCanonicalFragment053
/- END SGPT.Toric.ToricNativeStrictProductMargin -/

/- BEGIN SGPT.Toric.ToricNativeTwistedGeometry; source SHA256 ada838f6d7792b7db8cb7a82fe97465009022389180a325c8bf1a23ab8571f5c -/
section ToricCanonicalFragment054

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual metric qh+g on the original divisor qD+E. -/
def toricNativeTwistedMetric {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) :=
  (h.zsmulMetric (q : ℤ)).addMetric g

/-- Actual native source tensor bundle L^q tensor T, at every degree. -/
def toricNativeTwistedBundle {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) :=
  twistedPower (toricNativeHermitianLineBundle h) (toricNativeHermitianLineBundle g) q

abbrev ToricNativeTwistedSections {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) :=
  twistedSections (toricNativeHermitianLineBundle h) (toricNativeHermitianLineBundle g) q

def toricNativeTwistedFrame {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (v : latticePolytopeVertices γ) (q : ℕ) :
    AtlasFrame (toricNativeTwistedBundle h g q) :=
  twistedPowerAtlasFrame (toricNativeLineAtlasFrame h v) (toricNativeLineAtlasFrame g v) q

theorem toricNativeTwistedFrame_mem {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (v : latticePolytopeVertices γ) (q : ℕ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    p ∈ (toricNativeTwistedFrame h g v q).val.baseSet :=
  twistedPowerAtlasFrame_mem (toricNativeLineAtlasFrame h v) (toricNativeLineAtlasFrame g v) hv hv q

/-- Original Cartier addition holds on every ENTIRE overlap, proved on
the dense torus then extended through genuine continuous transition units. -/
theorem toricCartierTransition_add (D E : ToricDivisor γ hs)
    (v w : latticePolytopeVertices γ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    toricCartierTransition (D + E) v w p =
      toricCartierTransition D v w p * toricCartierTransition E v w p := by
  let U := (originalPolytopeNativeModelChart γ hs v).source ∩
    (originalPolytopeNativeModelChart γ hs w).source
  have hU : IsOpen U := (originalPolytopeNativeModelChart γ hs v).open_source.inter
    (originalPolytopeNativeModelChart γ hs w).open_source
  apply toricCartier_eqOn_of_denseTorus U hU _ _
    (continuousOn_toricCartierTransition (D + E) v w)
    ((continuousOn_toricCartierTransition D v w).mul
      (continuousOn_toricCartierTransition E v w)) ?_ ⟨hv, hw⟩
  intro a _
  change toricCartierTransition (D + E) v w (polytopeToricEmbedding γ hs a) =
    toricCartierTransition D v w (polytopeToricEmbedding γ hs a) *
      toricCartierTransition E v w (polytopeToricEmbedding γ hs a)
  rw [toricCartierTransition_embedding, toricCartierTransition_embedding,
    toricCartierTransition_embedding, toricCartierDatum_add, toricCartierDatum_add]
  have heq : toricCartierDatum D v + toricCartierDatum E v -
      (toricCartierDatum D w + toricCartierDatum E w) =
      (toricCartierDatum D v - toricCartierDatum D w) +
        (toricCartierDatum E v - toricCartierDatum E w) := by abel
  rw [heq, latticeCharacter_add, Units.val_mul]

/-- The true actual tensor coordinate change is the full original qD+E
Cartier unit, without a supplied compatibility certificate. -/
theorem toricNativeTwistedFrame_transition_cartier {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E)
    (v w : latticePolytopeVertices γ) (q : ℕ) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    ((toricNativeTwistedFrame h g v q).val.coordChangeL ℂ
      (toricNativeTwistedFrame h g w q).val p) 1 =
      toricCartierTransition ((q : ℤ) • D + E) v w p := by
  have ht := twistedPower_frame_transition (toricNativeLineAtlasFrame h v)
    (toricNativeLineAtlasFrame h w) (toricNativeLineAtlasFrame g v) (toricNativeLineAtlasFrame g w)
    hv hw hv hw q
  rw [toricNativeLineFrame_transition h v w hv hw, toricNativeLineFrame_transition g v w hv hw] at ht
  rw [toricCartierTransition_add _ _ v w hv hw, toricCartierTransition_smul_nat D v w q hv hw]
  exact ht

/-- EVERY actual tensor section has the exact original qh+g physical norm
in every original vertex frame, including degree zero and boundary points. -/
theorem toricNativeTwistedSection_norm_sq {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (v : latticePolytopeVertices γ) (q : ℕ)
    (s : ToricNativeTwistedSections h g q) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ‖s p‖ ^ 2 = ‖((toricNativeTwistedFrame h g v q).val ⟨p, s p⟩).2‖ ^ 2 *
      Real.exp (-(toricNativeTwistedMetric h g q).weight v
        (originalPolytopeNativeModelChart γ hs v p)) := by
  have hn := twistedSection_norm_sq_frame (toricNativeLineAtlasFrame h v)
    (toricNativeLineAtlasFrame g v) q s hv hv
  change ‖s p‖ ^ 2 = ‖((toricNativeTwistedFrame h g v q).val ⟨p, s p⟩).2‖ ^ 2 *
    (‖(toricNativeLineTrivialization h v).symm p 1‖ ^ 2) ^ q *
      ‖(toricNativeLineTrivialization g v).symm p 1‖ ^ 2 at hn
  rw [toricNativeLineTrivialization_frame_norm_sq h v hv,
    toricNativeLineTrivialization_frame_norm_sq g v hv] at hn
  have hexp : Real.exp (-h.weight v (originalPolytopeNativeModelChart γ hs v p)) ^ q *
      Real.exp (-g.weight v (originalPolytopeNativeModelChart γ hs v p)) =
      Real.exp (-(toricNativeTwistedMetric h g q).weight v
        (originalPolytopeNativeModelChart γ hs v p)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp only [toricNativeTwistedMetric, BigToricMetric.addMetric, BigToricMetric.zsmulMetric]
    simp only [Int.cast_natCast]
    ring
  rw [mul_assoc, hexp] at hn
  exact hn

end SGPT.Toric

end
end ToricCanonicalFragment054
/- END SGPT.Toric.ToricNativeTwistedGeometry -/

/- BEGIN SGPT.Toric.ToricNativeTwistedSectionCoefficients; source SHA256 45e7fdf6ed6beb72b532b5368bbe5552994955f6725ac4d000c41ea3d3afa60f -/
section ToricCanonicalFragment055

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

def toricNativeTwistedSectionFrameCoeff {D E : ToricDivisor γ hs} (h : BigToricMetric D) (g : BigToricMetric E)
    (q : ℕ) (v : latticePolytopeVertices γ) (s : ToricNativeTwistedSections h g q)
    (p : PolytopeToricVariety γ hs) : ℂ :=
  ((toricNativeTwistedFrame h g v q).val ⟨p, s p⟩).2

def toricNativeTwistedSectionChartCoeff {D E : ToricDivisor γ hs} (h : BigToricMetric D) (g : BigToricMetric E)
    (q : ℕ) (v : latticePolytopeVertices γ) (s : ToricNativeTwistedSections h g q)
    (z : ComplexModel n) : ℂ :=
  toricNativeTwistedSectionFrameCoeff h g q v s
    ((originalPolytopeNativeModelChart γ hs v).symm z)

/-- EVERY section of the actual arbitrary auxiliary-twisted tensor bundle has an
entire original vertex coefficient, including degree zero. -/
theorem differentiable_toricNativeTwistedSectionChartCoeff {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) (v : latticePolytopeVertices γ)
    (s : ToricNativeTwistedSections h g q) :
    Differentiable ℂ (toricNativeTwistedSectionChartCoeff h g q v s) := by
  intro z
  let C : OpenPartialHomeomorph (PolytopeToricVariety γ hs) (ComplexModel n) :=
    (polytopeToricVertexChart γ hs v).val
  let e := (toricNativeTwistedFrame h g v q).val
  have hz : z ∈ C.target := by
    change z ∈ (originalPolytopeNativeModelChart γ hs v).target
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  have hp : C.symm z ∈ e.baseSet := toricNativeTwistedFrame_mem h g v q (C.map_target hz)
  have hcoeff : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ℂ)) ∞
      (toricNativeTwistedSectionFrameCoeff h g q v s) (C.symm z) :=
    (e.contMDiffAt_section_iff hp).mp (s.contMDiff (C.symm z))
  have hmem : C ∈ IsManifold.maximalAtlas (𝓘(ℂ, ComplexModel n)) ∞
      (PolytopeToricVariety γ hs) :=
    IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (M := PolytopeToricVariety γ hs) (polytopeToricVertexChart γ hs v).property
  have hchart : ContMDiffAt (𝓘(ℂ, ComplexModel n)) (𝓘(ℂ, ComplexModel n)) ∞ C.symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (M := PolytopeToricVariety γ hs) hmem hz
  exact (contMDiffAt_iff_contDiffAt.mp (hcoeff.comp z hchart)).differentiableAt (by simp)

theorem toricNativeTwistedSectionChartCoeff_chart_apply {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) (v : latticePolytopeVertices γ)
    (s : ToricNativeTwistedSections h g q) {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    toricNativeTwistedSectionChartCoeff h g q v s (originalPolytopeNativeModelChart γ hs v p) =
      toricNativeTwistedSectionFrameCoeff h g q v s p := by
  unfold toricNativeTwistedSectionChartCoeff
  rw [(originalPolytopeNativeModelChart γ hs v).left_inv hp]

/-- The actual linear coordinate change on the literal tensor fiber is
the independently produced original qD Cartier scalar on all overlaps. -/
theorem toricNativeTwistedFrame_change_apply {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) (v w : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) (z : ℂ) :
    ((toricNativeTwistedFrame h g v q).val.coordChangeL ℂ
      (toricNativeTwistedFrame h g w q).val p) z =
        toricCartierTransition ((q : ℤ) • D + E) v w p * z := by
  let A := (toricNativeTwistedFrame h g v q).val.coordChangeL ℂ
    (toricNativeTwistedFrame h g w q).val p
  calc
    A z = A (z • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
    _ = z • A 1 := A.map_smul z 1
    _ = _ := by
      rw [toricNativeTwistedFrame_transition_cartier h g v w q hv hw, smul_eq_mul]
      exact mul_comm _ _

theorem toricNativeTwistedSectionFrameCoeff_transition {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) (v w : latticePolytopeVertices γ)
    (s : ToricNativeTwistedSections h g q) {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hw : p ∈ (originalPolytopeNativeModelChart γ hs w).source) :
    toricNativeTwistedSectionFrameCoeff h g q w s p =
      toricCartierTransition ((q : ℤ) • D + E) v w p *
        toricNativeTwistedSectionFrameCoeff h g q v s p := by
  let e := (toricNativeTwistedFrame h g v q).val
  let f := (toricNativeTwistedFrame h g w q).val
  have he := toricNativeTwistedFrame_mem h g v q hv
  have hf := toricNativeTwistedFrame_mem h g w q hw
  have hh := Trivialization.coordChangeL_apply (R := ℂ) e f ⟨he, hf⟩ (e ⟨p, s p⟩).2
  rw [e.symm_apply_apply_mk he] at hh
  rw [toricNativeTwistedFrame_change_apply h g q v w hv hw] at hh
  exact hh.symm

end SGPT.Toric

end
end ToricCanonicalFragment055
/- END SGPT.Toric.ToricNativeTwistedSectionCoefficients -/

/- BEGIN SGPT.Toric.ToricNativeTwistedSectionRestriction; source SHA256 ece7d9333d99931b50bf71d62afb27534eb8cb7f1f1d30bf54f813aee3c7b632 -/
section ToricCanonicalFragment056

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

def toricNativeTwistedSectionTorusFunction {D E : ToricDivisor γ hs} (h : BigToricMetric D) (g : BigToricMetric E)
    (q : ℕ) (s : ToricNativeTwistedSections h g q) (a : Fin n → ℂˣ) : ℂ :=
  toricNativeTwistedSectionFrameCoeff h g q (polytopeToricBaseVertex γ) s
    (polytopeToricEmbedding γ hs a) *
      latticeCharacter (toricCartierDatum ((q : ℤ) • D + E) (polytopeToricBaseVertex γ)) a

theorem toricNativeTwistedSectionTorusFunction_eq_chartCoeff {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) (v : latticePolytopeVertices γ)
    (s : ToricNativeTwistedSections h g q) (a : Fin n → ℂˣ) :
    toricNativeTwistedSectionTorusFunction h g q s a =
      toricNativeTwistedSectionChartCoeff h g q v s
        (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) *
          latticeCharacter (toricCartierDatum ((q : ℤ) • D + E) v) a := by
  let F := (q : ℤ) • D + E
  let w := polytopeToricBaseVertex γ
  have hv := toricNativeEmbedding_mem_chartSource (hs := hs) v a
  have hw := toricNativeEmbedding_mem_chartSource (hs := hs) w a
  rw [toricNativeTwistedSectionChartCoeff_chart_apply h g q v s hv]
  have hc := toricNativeTwistedSectionFrameCoeff_transition h g q v w s hv hw
  rw [toricCartierTransition_embedding] at hc
  change toricNativeTwistedSectionFrameCoeff h g q w s (polytopeToricEmbedding γ hs a) *
    (latticeCharacter (toricCartierDatum F w) a : ℂ) = _
  rw [hc]
  have hchar : (latticeCharacter (toricCartierDatum F v - toricCartierDatum F w) a : ℂ) *
      (latticeCharacter (toricCartierDatum F w) a : ℂ) =
        (latticeCharacter (toricCartierDatum F v) a : ℂ) := by
    have hvec : (toricCartierDatum F v - toricCartierDatum F w) + toricCartierDatum F w =
      toricCartierDatum F v := by abel
    have hh := congrArg (fun z : ℂˣ => (z : ℂ))
      (latticeCharacter_add (toricCartierDatum F v - toricCartierDatum F w)
        (toricCartierDatum F w) a)
    simpa only [Units.val_mul, hvec] using hh.symm
  calc
    _ = toricNativeTwistedSectionFrameCoeff h g q v s (polytopeToricEmbedding γ hs a) *
      ((latticeCharacter (toricCartierDatum F v - toricCartierDatum F w) a : ℂ) *
        (latticeCharacter (toricCartierDatum F w) a : ℂ)) := by ring
    _ = _ := by rw [hchar]

theorem toricNativeTwistedSectionTorusFunction_mem {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) (s : ToricNativeTwistedSections h g q) :
    toricNativeTwistedSectionTorusFunction h g q s ∈ toricSections ((q : ℤ) • D + E) := by
  intro v
  exact ⟨toricNativeTwistedSectionChartCoeff h g q v s,
    differentiable_toricNativeTwistedSectionChartCoeff h g q v s,
    toricNativeTwistedSectionTorusFunction_eq_chartCoeff h g q v s⟩

theorem toricNativeTwistedFrame_coefficient_add {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (s t : (toricNativeTwistedBundle h g q).Fiber p) :
    ((toricNativeTwistedFrame h g v q).val ⟨p, s + t⟩).2 =
      ((toricNativeTwistedFrame h g v q).val ⟨p, s⟩).2 +
        ((toricNativeTwistedFrame h g v q).val ⟨p, t⟩).2 := by
  let e := (toricNativeTwistedFrame h g v q).val
  have he := toricNativeTwistedFrame_mem h g v q hv
  have hread (z : (toricNativeTwistedBundle h g q).Fiber p) :
      (e.linearMapAt ℂ p) z = (e ⟨p, z⟩).2 :=
    congrFun (Trivialization.coe_linearMapAt_of_mem e he) z
  exact (hread (s + t)).symm.trans
    (((e.linearMapAt ℂ p).map_add s t).trans (congrArg₂ (· + ·) (hread s) (hread t)))

theorem toricNativeTwistedFrame_coefficient_smul {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (c : ℂ) (s : (toricNativeTwistedBundle h g q).Fiber p) :
    ((toricNativeTwistedFrame h g v q).val ⟨p, c • s⟩).2 =
      c • ((toricNativeTwistedFrame h g v q).val ⟨p, s⟩).2 := by
  let e := (toricNativeTwistedFrame h g v q).val
  have he := toricNativeTwistedFrame_mem h g v q hv
  have hread (z : (toricNativeTwistedBundle h g q).Fiber p) :
      (e.linearMapAt ℂ p) z = (e ⟨p, z⟩).2 :=
    congrFun (Trivialization.coe_linearMapAt_of_mem e he) z
  exact (hread (c • s)).symm.trans
    (((e.linearMapAt ℂ p).map_smul c s).trans (congrArg (c • ·) (hread s)))

/-- Restriction of ALL actual arbitrary auxiliary-twisted source tensor sections to the
independently defined full original qD+E Cartier section space. -/
def toricNativeTwistedSectionRestriction {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) :
    ToricNativeTwistedSections h g q →ₗ[ℂ] toricSections ((q : ℤ) • D + E) where
  toFun s := ⟨toricNativeTwistedSectionTorusFunction h g q s,
    toricNativeTwistedSectionTorusFunction_mem h g q s⟩
  map_add' s t := by
    apply Subtype.ext
    funext a
    change ((toricNativeTwistedFrame h g (polytopeToricBaseVertex γ) q).val
        ⟨polytopeToricEmbedding γ hs a,
          s (polytopeToricEmbedding γ hs a) + t (polytopeToricEmbedding γ hs a)⟩).2 * _ = _
    rw [toricNativeTwistedFrame_coefficient_add h g q (polytopeToricBaseVertex γ)
      (toricNativeEmbedding_mem_chartSource (polytopeToricBaseVertex γ) a), add_mul]
    rfl
  map_smul' c s := by
    apply Subtype.ext
    funext a
    change ((toricNativeTwistedFrame h g (polytopeToricBaseVertex γ) q).val
        ⟨polytopeToricEmbedding γ hs a, c • s (polytopeToricEmbedding γ hs a)⟩).2 * _ = _
    rw [toricNativeTwistedFrame_coefficient_smul h g q (polytopeToricBaseVertex γ)
      (toricNativeEmbedding_mem_chartSource (polytopeToricBaseVertex γ) a), smul_eq_mul]
    change (c * _) * _ = c * (_ * _)
    exact mul_assoc _ _ _


/-- Every chosen coefficient of the full original Cartier reading is the
actual entire tensor-frame coefficient, including the boundary. -/
theorem toricNativeTwistedSectionRestriction_coeff {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ)
    (s : ToricNativeTwistedSections h g q) (v : latticePolytopeVertices γ) :
    toricOriginalSectionCoeff (toricNativeTwistedSectionRestriction h g q s) v =
      toricNativeTwistedSectionChartCoeff h g q v s := by
  apply toricSectionCoeff_unique (D := (q : ℤ) • D + E) v
    (differentiable_toricOriginalSectionCoeff _ v).continuous
    (differentiable_toricNativeTwistedSectionChartCoeff h g q v s).continuous
    (toricOriginalSectionCoeff_torus _ v)
  exact toricNativeTwistedSectionTorusFunction_eq_chartCoeff h g q v s

/-- Actual linear passage from ALL original tensor H0 to the independent
native qh+g geometry; no desired H0 map/evaluation compatibility is assumed. -/
def toricNativeTwistedSectionToNative {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) :
    ToricNativeTwistedSections h g q →ₗ[ℂ]
      ToricNativeHolomorphicSections (toricNativeTwistedMetric h g q) :=
  (toricNativeFullSectionEquiv (toricNativeTwistedMetric h g q)).symm.toLinearMap.comp
    (toricNativeTwistedSectionRestriction h g q)


end SGPT.Toric

end
end ToricCanonicalFragment056
/- END SGPT.Toric.ToricNativeTwistedSectionRestriction -/

/- BEGIN SGPT.Toric.ToricNativeTwistedBergmanLower; source SHA256 13e3e8691934dbfba7edc219584c2f591192e8439426acd61dd8c4fb883a0f42 -/
section ToricCanonicalFragment057

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeRightUnit SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff Manifold ENNReal BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual source tensor sections, read as degree-one right-unit sections
of the independently produced original qh+g metric. -/
def toricNativeTwistedDegreeOneSection {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ)
    (s : ToricNativeTwistedSections h g q) :
    twistedSections (toricNativeHermitianLineBundle (toricNativeTwistedMetric h g q)) unit 1 :=
  (nativeRightUnitSectionsEquiv
    (toricNativeHermitianLineBundle (toricNativeTwistedMetric h g q))).symm
      (toricNativeTwistedSectionToNative h g q s)


/-- Exact singular weight at all finite values and poles. -/
theorem toricNativeMultiplierWeight_one_scaled (q : ℕ) (u : EReal) :
    multiplierWeight 1 (((q : ℝ) : EReal) * u) = multiplierWeight (q : ℝ) u := by
  simp only [multiplierWeight, EReal.coe_one, one_mul]


/-- Positive scaling of the actual original global QPSH input. -/
theorem toricNativeScaledPhi_qpsh (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH
      (fun x => ((q : ℝ) : EReal) * φ x) :=
  hφ.pos_smul (by exact_mod_cast hq)

theorem toricNativeScaledPhi_invariant (q : ℕ)
    {φ : PolytopeToricVariety γ hs → EReal} (hinv : PolytopeToricInvariant γ hs φ) :
    PolytopeToricInvariant γ hs (fun x => ((q : ℝ) : EReal) * φ x) := by
  intro a ha p
  dsimp only
  rw [hinv a ha p]

/-- The full internally produced physical ON eigensection sum for qD+E,
with original weight q phi and scale 1/q. -/
def toricNativeTwistedPhiBergmanPotential {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (p : PolytopeToricVariety γ hs) : EReal :=
  ((q : ℝ)⁻¹ : EReal) * toricNativePhiBergmanPotential (toricNativeTwistedMetric h g q) 1
    Nat.zero_lt_one (toricNativeScaledPhi_qpsh q hq hφ) (toricNativeScaledPhi_invariant q hinv) p



end SGPT.Toric

end
end ToricCanonicalFragment057
/- END SGPT.Toric.ToricNativeTwistedBergmanLower -/

/- BEGIN SGPT.Toric.ToricNativeNegativeTwistLower; source SHA256 a98d5385052b50e9976b6008a73ddc376c4ade644193ae4487c1481301cf41a6 -/
section ToricCanonicalFragment058

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeRightUnit SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff Manifold ENNReal BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual fixed negative ample auxiliary metric, independent of q. -/
def toricNativeNegativeAuxiliaryMetric :=
  (BigToricMetric.zeroMetric (γ := γ) (hs := hs)).subMetric (toricFullLatticeMetric (hs := hs))

theorem toricNativeNegativeTwistDivisor_eq (D : ToricDivisor γ hs) (q : ℕ) :
    (q : ℤ) • D + (0 - polytopeToricAmpleDivisor γ hs) = (q : ℤ) • D - polytopeToricAmpleDivisor γ hs := by abel

/-- Actual original fixed-negative-twist tensor H0, read through the
independent original Cartier restriction and its true divisor equality. -/
def toricNativeTwistedSectionToNegative {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ)
    (s : ToricNativeTwistedSections h (toricNativeNegativeAuxiliaryMetric (hs := hs)) q) :
    ToricNativeHolomorphicSections (toricNativeNegativeTwistMetric h q) :=
  (toricNativeFullSectionEquiv (toricNativeNegativeTwistMetric h q)).symm
    (toricOriginalSectionCast (toricNativeNegativeTwistDivisor_eq D q)
      (toricNativeTwistedSectionRestriction h (toricNativeNegativeAuxiliaryMetric (hs := hs)) q s))

/-- The same original physical norm at every point; no metric or norm
compatibility certificate is assumed. -/
theorem toricNativeTwistedSectionToNegative_norm_sq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ)
    (s : ToricNativeTwistedSections h (toricNativeNegativeAuxiliaryMetric (hs := hs)) q)
    (p : PolytopeToricVariety γ hs) :
    ‖toricNativeTwistedSectionToNegative h q s p‖ ^ 2 = ‖s p‖ ^ 2 := by
  let v := toricNativePreferredVertex γ hs p
  have hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source := toricNativePreferredVertex_mem p
  rw [toricNativeTwistedSectionToNegative, toricNativeFullSectionEquiv_symm_norm_sq _ _ v hv,
    toricOriginalSectionCoeff_cast, toricNativeTwistedSectionRestriction_coeff,
    toricNativeTwistedSectionChartCoeff_chart_apply h _ q v s hv,
    toricNativeTwistedSection_norm_sq h (toricNativeNegativeAuxiliaryMetric (hs := hs)) v q s hv]
  congr 2
  dsimp only [toricNativeNegativeTwistMetric, toricNativeTwistedMetric,
    toricNativeNegativeAuxiliaryMetric, BigToricMetric.addMetric, BigToricMetric.subMetric,
    BigToricMetric.zsmulMetric, BigToricMetric.zeroMetric]
  ring

def toricNativeTwistedSectionToNegativeOne {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ)
    (s : ToricNativeTwistedSections h (toricNativeNegativeAuxiliaryMetric (hs := hs)) q) :
    twistedSections (toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q)) unit 1 :=
  (nativeRightUnitSectionsEquiv
    (toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q))).symm
      (toricNativeTwistedSectionToNegative h q s)

theorem toricNativeTwistedSectionToNegativeOne_norm_sq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ)
    (s : ToricNativeTwistedSections h (toricNativeNegativeAuxiliaryMetric (hs := hs)) q)
    (p : PolytopeToricVariety γ hs) :
    ‖toricNativeTwistedSectionToNegativeOne h q s p‖ ^ 2 = ‖s p‖ ^ 2 := by
  have hn := nativeRightUnitSectionsEquiv_symm_norm
    (toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q))
    (toricNativeTwistedSectionToNegative h q s) p
  exact (congrArg (fun x : ℝ => x ^ 2) hn).trans
    (toricNativeTwistedSectionToNegative_norm_sq h q s p)

/-- The actual full negative-twist ON family, enumerated in Fin, with the
original q phi singular weight and raw Guillemin Hilbert measure. -/
def toricNativeNegativeTwistPhiFiniteSections {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :=
  toricNativePhiFiniteSections (toricNativeNegativeTwistMetric h q) 1 Nat.zero_lt_one
    (toricNativeScaledPhi_qpsh q hq hφ) (toricNativeScaledPhi_invariant q hinv)

/-- Genuine product sections in original H0(L^q), using the internally
produced full negative-twist ON family and actual auxiliary sections. -/
def toricNativeStrictPhiProductSections {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :=
  toricNativeStrictProductSections h q (toricNativeNegativeTwistPhiFiniteSections h q hq hφ hinv)

def toricNativeStrictPhiProductPotential {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) : PolytopeToricVariety γ hs → EReal :=
  toricNativeFiniteSectionPotential h q (toricNativeStrictPhiProductSections h q hq hφ hinv)

/-- Exact SAME physical logarithmic sum, including zeros and empty Gamma. -/
theorem toricNativeStrictPhiProductPotential_eq_scaled {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (p : PolytopeToricVariety γ hs) :
    toricNativeStrictPhiProductPotential h q hq hφ hinv p =
      ((q : ℝ)⁻¹ : EReal) * toricNativePhiBergmanPotential (toricNativeNegativeTwistMetric h q) 1
        Nat.zero_lt_one (toricNativeScaledPhi_qpsh q hq hφ)
        (toricNativeScaledPhi_invariant q hinv) p := by
  unfold toricNativeStrictPhiProductPotential toricNativeFiniteSectionPotential
    toricNativeStrictPhiProductSections
  rw [toricNativeStrictProductSections_density,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  change ((q : ℝ)⁻¹ : EReal) * ENNReal.log (toricNativeFiniteSectionDensity
    (toricNativeNegativeTwistMetric h q) 1
    (toricNativeNegativeTwistPhiFiniteSections h q hq hφ hinv) p) = _
  rw [toricNativeNegativeTwistPhiFiniteSections, toricNativePhiFiniteSections_density]
  simp only [toricNativePhiBergmanPotential, Nat.cast_one, inv_one, EReal.coe_one, one_mul]

/-- Direct actual integral-unit-ball injection, preserving the original
fixed-L/fixed-negative-T estimate with a threshold uniform in q. -/
theorem toricNativeNegativeTwistOriginalDensity_le {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (φ : PolytopeToricVariety γ hs → EReal)
    (μ : Measure (PolytopeToricVariety γ hs)) (p : PolytopeToricVariety γ hs) :
    nativePhiOriginalBergmanDensity (toricNativeHermitianLineBundle h)
      (toricNativeHermitianLineBundle (toricNativeNegativeAuxiliaryMetric (hs := hs))) q
      (φ := φ) μ p ≤
    nativePhiOriginalBergmanDensity (toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q))
      unit 1 (φ := fun x => ((q : ℝ) : EReal) * φ x) μ p := by
  apply iSup_le
  intro s
  apply iSup_le
  intro hnorm
  have hnorm' : (∫⁻ y, originalSectionDensity
      (twistedPower (toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q)) unit 1).Fiber
      (fun x => ((q : ℝ) : EReal) * φ x) 1
      (toricNativeTwistedSectionToNegativeOne h q s) y ∂μ) ≤ 1 := by
    convert hnorm using 1
    apply lintegral_congr
    intro y
    simp only [originalSectionDensity, toricNativeTwistedSectionToNegativeOne_norm_sq,
      toricNativeMultiplierWeight_one_scaled]
  rw [← toricNativeTwistedSectionToNegativeOne_norm_sq h q s p]
  simpa only [nativePhiOriginalBergmanDensity, Nat.cast_one] using
    (le_iSup₂ (f := fun (t : twistedSections
      (toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q)) unit 1)
      (_ : (∫⁻ y, originalSectionDensity
        (twistedPower (toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q)) unit 1).Fiber
        (fun x => ((q : ℝ) : EReal) * φ x) 1 t y ∂μ) ≤ 1) =>
        ENNReal.ofReal (‖t p‖ ^ 2)) (toricNativeTwistedSectionToNegativeOne h q s) hnorm')

/-- Actual full ON products dominate the original fixed-negative-twist
Bergman sequence, with the literal 1/q scale. -/
theorem toricNativeStrictPhiProductPotential_ge_bergmanSeq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (p : PolytopeToricVariety γ hs) :
    GlobalL2.bergmanSeq (polytopeToricKahlerBackground γ hs) (toricNativeHermitianLineBundle h)
      (toricNativeHermitianLineBundle (toricNativeNegativeAuxiliaryMetric (hs := hs))) φ q p ≤
      toricNativeStrictPhiProductPotential h q hq hφ hinv p := by
  have hlog := ENNReal.log_monotone (toricNativeNegativeTwistOriginalDensity_le h q φ
    (kahlerVolume (polytopeToricKahlerBackground γ hs)) p)
  rw [toricNativePhiOriginalBergmanDensity_eq_eigenbasis (toricNativeNegativeTwistMetric h q)
    1 Nat.zero_lt_one (toricNativeScaledPhi_qpsh q hq hφ)
    (toricNativeScaledPhi_invariant q hinv) p] at hlog
  have hm := monotone_eReal_const_mul (c := (q : ℝ)⁻¹) (by positivity) hlog
  rw [toricNativeStrictPhiProductPotential_eq_scaled]
  simpa only [GlobalL2.bergmanSeq, toricNativePhiBergmanPotential,
    Nat.cast_one, inv_one, EReal.coe_one, one_mul, one_div, EReal.coe_inv,
    nativePhiOriginalBergmanDensity, originalSectionDensity] using hm

/-- Genuine uniform lower estimate on actual strict products in original
L^q, from actual original Chern strictness and arbitrary original phi. -/
theorem toricNativeStrictPhiProductPotential_lower {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (hpositive : IsKahlerCurrentPotential h.form φ) :
    ∃ (q₀ : ℕ) (C : ℝ), 0 < q₀ ∧ 0 < C ∧ ∀ q : ℕ, q₀ ≤ q →
      ∀ (hq : 0 < q) (p : PolytopeToricVariety γ hs),
        φ p - ((Real.log C / q : ℝ) : EReal) ≤
          toricNativeStrictPhiProductPotential h q hq hφ hinv p := by
  obtain ⟨q₀, C, hC, hlower⟩ := GlobalL2.bergmanSeq_lower
    (polytopeToricKahlerBackground γ hs) (toricNativeHermitianLineBundle h)
    (toricNativeHermitianLineBundle (toricNativeNegativeAuxiliaryMetric (hs := hs)))
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle h)
    (isSourceSmoothHermitianMetric_toricNativeHermitianLineBundle
      (toricNativeNegativeAuxiliaryMetric (hs := hs))) h.form
    (isOwnFirstChernForm_toricNativeHermitianLineBundle h) hpositive
  refine ⟨max q₀ 1, C, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), hC, ?_⟩
  intro q hq hqpos p
  exact (hlower q (le_of_max_le_left hq) p).trans
    (toricNativeStrictPhiProductPotential_ge_bergmanSeq h q hqpos hφ hinv p)

end SGPT.Toric

end
end ToricCanonicalFragment058
/- END SGPT.Toric.ToricNativeNegativeTwistLower -/

/- BEGIN SGPT.Toric.ToricNativeStrictPhiApproximation; source SHA256 49cba9f52918c6ba811a9541e107ce02c661acb86612e266a8e35ea3924082f5 -/
section ToricCanonicalFragment059

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The internally produced positive background omega_A/q, on the actual
original manifold and with its full curvature form. -/
def toricNativeStrictPhiBackground (q : ℕ) (hq : 0 < q) :
    KahlerBackground n (PolytopeToricVariety γ hs) where
  form := (q : ℝ)⁻¹ • (toricFullLatticeMetric (hs := hs)).form
  isKahler := by
    refine ⟨?_, ((q : ℝ)⁻¹ • (toricFullLatticeMetric (hs := hs)).form).property.1⟩
    intro e z hz
    refine ⟨((q : ℝ)⁻¹ • (toricFullLatticeMetric (hs := hs)).form).property.2 e z hz, ?_⟩
    intro w hw
    rw [ClosedRealOneOneForm.coeff_smul]
    change (q : ℝ)⁻¹ * (toricFullLatticeMetric (hs := hs)).form.val.coeff e z ![w, Complex.I • w] > 0
    exact mul_pos (by positivity) (((toricFullLatticeMetric_isKahler (hs := hs)).1 e z hz).2 w hw)

/-- Pointwise toric invariance of the ACTUAL full physical product sum,
from the independently produced negative-twist eigenbasis kernel. -/
theorem toricNativeStrictPhiProductPotential_invariant {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    PolytopeToricInvariant γ hs (toricNativeStrictPhiProductPotential h q hq hφ hinv) := by
  intro a ha p
  rw [toricNativeStrictPhiProductPotential_eq_scaled,
    toricNativeStrictPhiProductPotential_eq_scaled,
    toricNativePhiBergmanPotential_invariant _ _ _ _ _ a ha p]



/-- The exact raw strict margin of the literal actual finite product family. -/
theorem toricNativeStrictPhiProductPotential_margin {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    ThetaPlurisubharmonic
      (h.form - (toricNativeStrictPhiBackground (hs := hs) q hq).form).val
      (toricNativeStrictPhiProductPotential h q hq hφ hinv) :=
  toricNativeStrictProductPotential_thetaPlurisubharmonic h q hq _

/-- Local nondegeneracy is produced from the genuine fixed-negative-twist
lower estimate and the original phi finite-locus density. -/
theorem toricNativeStrictPhiProductPotential_margin_eventually {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (hpositive : IsKahlerCurrentPotential h.form φ) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ q : ℕ, q₀ ≤ q → ∀ hq : 0 < q,
      IsThetaPshPotential (h.form - (toricNativeStrictPhiBackground (hs := hs) q hq).form).val
        (toricNativeStrictPhiProductPotential h q hq hφ hinv) := by
  obtain ⟨q₀, C, hq₀, _, hlower⟩ := toricNativeStrictPhiProductPotential_lower h hφ hinv hpositive
  refine ⟨q₀, hq₀, fun q hq hqpos =>
    ⟨toricNativeStrictPhiProductPotential_margin h q hqpos hφ hinv, ?_⟩⟩
  intro x U hU hx
  obtain ⟨y, hyU, hybot⟩ := (toricNativePhi_globalQpsh hφ).2 x U hU hx
  refine ⟨y, hyU, ?_⟩
  have hr : φ y = ((φ y).toReal : EReal) := (EReal.coe_toReal (hφ.ne_top y) hybot).symm
  have hbound := hlower q hq hqpos y
  rw [hr, ← EReal.coe_sub] at hbound
  intro hbot
  rw [hbot] at hbound
  exact (EReal.bot_lt_coe _).not_ge hbound

/-- Actual SAME-theta Kähler current at every sufficiently large original
degree, with internally constructed positive omega_A/q and nondegeneracy. -/
theorem toricNativeStrictPhiProductPotential_isKahlerCurrent_eventually {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (hpositive : IsKahlerCurrentPotential h.form φ) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ q : ℕ, q₀ ≤ q → ∀ hq : 0 < q,
      IsKahlerCurrentPotential h.form (toricNativeStrictPhiProductPotential h q hq hφ hinv) := by
  obtain ⟨q₀, hq₀, hmargin⟩ := toricNativeStrictPhiProductPotential_margin_eventually h hφ hinv hpositive
  exact ⟨q₀, hq₀, fun q hq hqpos =>
    ⟨toricNativeStrictPhiBackground (hs := hs) q hqpos, hmargin q hq hqpos⟩⟩

/-- Actual same-theta toric PSH membership of the actual strict approximants. -/
theorem toricNativeStrictPhiProductPotential_mem_PSHTor_eventually {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (hpositive : IsKahlerCurrentPotential h.form φ) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ q : ℕ, q₀ ≤ q → ∀ hq : 0 < q,
      toricNativeStrictPhiProductPotential h q hq hφ hinv ∈ h.PSHTor := by
  obtain ⟨q₀, hq₀, hmargin⟩ := toricNativeStrictPhiProductPotential_margin_eventually h hφ hinv hpositive
  refine ⟨q₀, hq₀, fun q hq hqpos =>
    ⟨?_, toricNativeStrictPhiProductPotential_invariant h q hqpos hφ hinv⟩⟩
  apply (isThetaPSH_iff_nativeThetaPotential h.atlasForm _).mpr
  have hp := LocalPotentials.isThetaPshPotential_add_of_semipositive (hmargin q hq hqpos)
    (toricNativeStrictPhiBackground (hs := hs) q hqpos).isSemipositive
  have heq : h.form - (toricNativeStrictPhiBackground (hs := hs) q hqpos).form +
      (toricNativeStrictPhiBackground (hs := hs) q hqpos).form = h.form := sub_add_cancel _ _
  rwa [heq] at hp

end SGPT.Toric

end
end ToricCanonicalFragment059
/- END SGPT.Toric.ToricNativeStrictPhiApproximation -/

/- BEGIN SGPT.Toric.ToricNativeStrictPhiEigenproducts; source SHA256 a9f0ef033b4deadc833a5d2e753742cee0af6c3da8989c49c0a2a3c77ab8478d -/
section ToricCanonicalFragment060

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeRightUnit
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Cartier index transport leaves the SAME original dense-torus function. -/
theorem toricOriginalSectionCast_val {D E : ToricDivisor γ hs}
    (hDE : D = E) (s : toricSections D) (a : Fin n → ℂˣ) :
    (toricOriginalSectionCast hDE s).val a = s.val a := by
  subst E
  rfl

/-- Plain degree one and the native full Cartier reading coincide through
the actual tensor right-unit coefficient, rather than an assumed action map. -/
theorem toricNativePlainPowerFullSectionEquiv_one_val {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (s : ToricNativeHolomorphicSections h) (a : Fin n → ℂˣ) :
    (toricNativePlainPowerFullSectionEquiv h 1 s).val a =
      (toricNativeFullSectionEquiv h s).val a := by
  let v := polytopeToricBaseVertex γ
  let p := polytopeToricEmbedding γ hs a
  have hv : p ∈ (originalPolytopeNativeModelChart γ hs v).source :=
    toricNativeEmbedding_mem_chartSource v a
  have hc := nativeRightUnit_coordinate (toricNativeLineAtlasFrame h v) hv
    ((nativeRightUnitSectionsEquiv (toricNativeHermitianLineBundle h)).symm s p)
  have hc' : ((toricNativeDegreeFrame h v 1).val
      ⟨p, (toricNativePlainPowerRightUnitEquiv h 1).symm s p⟩).2 =
      ((toricNativeLineTrivialization h v) ⟨p, s p⟩).2 := by
    calc
      _ = ((toricNativeLineTrivialization h v)
          ⟨p, nativeRightUnitSectionsEquiv (toricNativeHermitianLineBundle h)
            ((nativeRightUnitSectionsEquiv (toricNativeHermitianLineBundle h)).symm s) p⟩).2 := hc
      _ = _ := congrArg (fun t : ToricNativeHolomorphicSections h =>
        ((toricNativeLineTrivialization h v) ⟨p, t p⟩).2)
          ((nativeRightUnitSectionsEquiv (toricNativeHermitianLineBundle h)).apply_symm_apply s)
  change toricNativeDegreeSectionFrameCoeff h 1 v
    ((toricNativePlainPowerRightUnitEquiv h 1).symm s) p *
      (latticeCharacter (toricCartierDatum ((1 : ℤ) • D) v) a : ℂ) =
    toricNativeSectionFrameCoeff h v s p * (latticeCharacter (toricCartierDatum D v) a : ℂ)
  rw [one_smul]
  exact congrArg (fun z : ℂ => z * (latticeCharacter (toricCartierDatum D v) a : ℂ)) hc'

/-- The actual negative-twist finite ON sections retain their whole
complex-torus character in the independent native full Cartier reading. -/
theorem toricNativePhiFiniteSections_one_cartier_eigen {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (a : Fin n → ℂˣ)
    (i : Fin (Fintype.card (ToricNativeMultiplierCharacterIndex h 1 Nat.zero_lt_one hφ))) :
    toricCartierSectionTranslation D a
        (toricNativeFullSectionEquiv h (toricNativePhiFiniteSections h 1 Nat.zero_lt_one hφ hinv i)) =
      (latticeCharacter ((Fintype.equivFin _).symm i).val a : ℂ) •
        toricNativeFullSectionEquiv h (toricNativePhiFiniteSections h 1 Nat.zero_lt_one hφ hinv i) := by
  apply Subtype.ext
  funext b
  have he := congrArg (fun t => (toricNativePlainPowerFullSectionEquiv h 1 t).val b)
    (toricNativePhiOrthonormalPlainSection_complexTorus_eigen h 1 Nat.zero_lt_one hφ hinv a
      ((Fintype.equivFin _).symm i))
  rw [toricNativePlainSectionTranslation_restriction, map_smul] at he
  change (toricNativePlainPowerFullSectionEquiv h 1
    (toricNativePhiFiniteSections h 1 Nat.zero_lt_one hφ hinv i)).val (a * b) =
      (latticeCharacter ((Fintype.equivFin _).symm i).val a : ℂ) *
        (toricNativePlainPowerFullSectionEquiv h 1
          (toricNativePhiFiniteSections h 1 Nat.zero_lt_one hφ hinv i)).val b at he
  rw [toricNativePlainPowerFullSectionEquiv_one_val, toricNativePlainPowerFullSectionEquiv_one_val] at he
  exact he

/-- Exact original Cartier function of the actual native negative product. -/
theorem toricNativeNegativeTwistProduct_restriction_val {D A : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric A) (q : ℕ)
    (s : ToricNativeHolomorphicSections ((h.zsmulMetric (q : ℤ)).subMetric g))
    (t : ToricNativeHolomorphicSections g) (a : Fin n → ℂˣ) :
    (toricNativePlainPowerFullSectionEquiv h q (toricNativeNegativeTwistProduct h g q s t)).val a =
      (toricNativeFullSectionEquiv ((h.zsmulMetric (q : ℤ)).subMetric g) s).val a *
        (toricNativeFullSectionEquiv g t).val a := by
  rw [toricNativeNegativeTwistProduct, LinearEquiv.apply_symm_apply, toricOriginalSectionCast_val]
  rfl

/-- EVERY actual strict product in original H0(L^q) is a genuine toric
eigensection for the ENTIRE complex torus, with internally produced weight. -/
theorem toricNativeStrictPhiProductSections_complexTorus_eigen {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (k : Fin (Fintype.card (ToricNativeMultiplierCharacterIndex
      (toricNativeNegativeTwistMetric h q) 1 Nat.zero_lt_one (toricNativeScaledPhi_qpsh q hq hφ)) *
        (originalPolytopeFullIndexSize γ + 1))) :
    ∃ m : Fin n → ℤ, ∀ a : Fin n → ℂˣ,
      toricNativePlainSectionTranslation h q a (toricNativeStrictPhiProductSections h q hq hφ hinv k) =
        (latticeCharacter m a : ℂ) • toricNativeStrictPhiProductSections h q hq hφ hinv k := by
  let i := (finProdFinEquiv.symm k).1
  let j := (finProdFinEquiv.symm k).2
  let m := ((Fintype.equivFin (ToricNativeMultiplierCharacterIndex
    (toricNativeNegativeTwistMetric h q) 1 Nat.zero_lt_one (toricNativeScaledPhi_qpsh q hq hφ))).symm i).val
  refine ⟨m + originalPolytopeFullExponents γ j, fun a => ?_⟩
  apply (toricNativePlainPowerFullSectionEquiv h q).injective
  rw [toricNativePlainSectionTranslation_restriction, map_smul]
  apply Subtype.ext
  funext b
  change (toricNativePlainPowerFullSectionEquiv h q
      (toricNativeNegativeTwistProduct h (toricFullLatticeMetric (hs := hs)) q
        (toricNativeNegativeTwistPhiFiniteSections h q hq hφ hinv i)
        (toricFullLatticeNativeSection (hs := hs) j))).val (a * b) =
    (latticeCharacter (m + originalPolytopeFullExponents γ j) a : ℂ) *
      (toricNativePlainPowerFullSectionEquiv h q
        (toricNativeNegativeTwistProduct h (toricFullLatticeMetric (hs := hs)) q
          (toricNativeNegativeTwistPhiFiniteSections h q hq hφ hinv i)
          (toricFullLatticeNativeSection (hs := hs) j))).val b
  rw [toricNativeNegativeTwistProduct_restriction_val, toricNativeNegativeTwistProduct_restriction_val]
  have he := congrArg (fun t : toricSections
      ((q : ℤ) • D - polytopeToricAmpleDivisor γ hs) => t.val b)
    (toricNativePhiFiniteSections_one_cartier_eigen (toricNativeNegativeTwistMetric h q)
      (toricNativeScaledPhi_qpsh q hq hφ) (toricNativeScaledPhi_invariant q hinv) a i)
  change (toricNativeFullSectionEquiv (toricNativeNegativeTwistMetric h q)
      (toricNativeNegativeTwistPhiFiniteSections h q hq hφ hinv i)).val (a * b) =
    (latticeCharacter m a : ℂ) * (toricNativeFullSectionEquiv (toricNativeNegativeTwistMetric h q)
      (toricNativeNegativeTwistPhiFiniteSections h q hq hφ hinv i)).val b at he
  dsimp only [toricNativeNegativeTwistMetric] at he
  rw [he]
  have haux (u : Fin n → ℂˣ) :
      (toricNativeFullSectionEquiv (toricFullLatticeMetric (hs := hs))
        (toricFullLatticeNativeSection (hs := hs) j)).val u =
      (latticeCharacter (originalPolytopeFullExponents γ j) u : ℂ) := by
    rw [toricFullLatticeNativeSection, LinearEquiv.apply_symm_apply]
    rfl
  rw [haux, haux, latticeCharacter_add, Units.val_mul, map_mul, Units.val_mul]
  ring

end SGPT.Toric

end
end ToricCanonicalFragment060
/- END SGPT.Toric.ToricNativeStrictPhiEigenproducts -/

/- BEGIN SGPT.Toric.ToricNativeStrictLocalBudget; source SHA256 1a49a9f993142b3658ef838f2b807c578dc4e0decb35a7ade6cdc7dbe25cfad3 -/
section ToricCanonicalFragment061

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Exact entire original negative-twist physical density in corrected
local weight phi+weight_h, preserving poles and zero times infinity. -/
theorem toricNativeNegativeTwist_weightedDensity_chart {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    (φ : PolytopeToricVariety γ hs → EReal)
    (s : ToricNativeHolomorphicSections (toricNativeNegativeTwistMetric h q))
    (v : latticePolytopeVertices γ) (z : ComplexModel n) :
    ENNReal.ofReal (‖s ((originalPolytopeNativeModelChart γ hs v).symm z)‖ ^ 2) *
        multiplierWeight (q : ℝ) (φ ((originalPolytopeNativeModelChart γ hs v).symm z)) =
      ENNReal.ofReal (Real.exp ((toricFullLatticeMetric (hs := hs)).weight v z)) *
        multiplierDensity
          (fun y => φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal))
          (q : ℝ) (toricOriginalSectionCoeff
            (toricNativeFullSectionEquiv (toricNativeNegativeTwistMetric h q) s) v) z := by
  have hz : z ∈ (originalPolytopeNativeModelChart γ hs v).target := by
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  have hn := toricNativeFullSectionEquiv_symm_norm_sq (toricNativeNegativeTwistMetric h q)
    (toricNativeFullSectionEquiv (toricNativeNegativeTwistMetric h q) s) v
    ((originalPolytopeNativeModelChart γ hs v).map_target hz)
  simp only [LinearEquiv.symm_apply_apply,
    (originalPolytopeNativeModelChart γ hs v).right_inv hz] at hn
  rw [hn, multiplierDensity,
    Pending.QuantitativeRegularizationChartBranch.multiplierWeight_add_coe (by exact_mod_cast hq)]
  have he : Real.exp (-(toricNativeNegativeTwistMetric h q).weight v z) =
      Real.exp ((toricFullLatticeMetric (hs := hs)).weight v z) *
        Real.exp (-(q : ℝ) * h.weight v z) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [toricNativeNegativeTwistMetric, BigToricMetric.subMetric, BigToricMetric.zsmulMetric]
    simp only [Int.cast_natCast]
    ring
  rw [he, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp only [neg_mul]
  ac_rfl

/-- A genuine fixed chart-volume minimum gives a uniform local budget for
ALL actual negative-twist sections and arbitrary measurable original phi. -/
theorem exists_toricNativeNegativeTwist_local_budget {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) {B : Set (ComplexModel n)}
    (hB : IsCompact B) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ _hq : 0 < q,
      ∀ φ : PolytopeToricVariety γ hs → EReal, Measurable φ →
      ∀ s : ToricNativeHolomorphicSections (toricNativeNegativeTwistMetric h q),
      (∫⁻ z in B, multiplierDensity
        (fun y => φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal))
        (q : ℝ) (toricOriginalSectionCoeff
          (toricNativeFullSectionEquiv (toricNativeNegativeTwistMetric h q) s) v) z) ≤
      ENNReal.ofReal C * ∫⁻ p, ENNReal.ofReal (‖s p‖ ^ 2) * multiplierWeight (q : ℝ) (φ p)
        ∂(Pending.IntegrationCurrent.kahlerVolume (polytopeToricKahlerBackground γ hs)) := by
  let μ := Pending.IntegrationCurrent.kahlerVolume (polytopeToricKahlerBackground γ hs)
  have hμ := Pending.KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume
    (polytopeToricKahlerBackground γ hs)
  let e := polytopeToricVertexChart γ hs v
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ e
  have hBt : B ⊆ e.val.target := by
    intro z _
    change z ∈ (originalPolytopeNativeModelChart γ hs v).target
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  rcases B.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun q hq φ hφ s => by simp⟩
  let d : ComplexModel n → ℝ := fun z => ρ z * Real.exp ((toricFullLatticeMetric (hs := hs)).weight v z)
  have hdc : ContinuousOn d B := (hρs.continuousOn.mono hBt).mul
    (Real.continuous_exp.comp ((toricFullLatticeMetric (hs := hs)).smooth v).continuous).continuousOn
  have hdp : ∀ z ∈ B, 0 < d z := fun z hz => mul_pos (hρpos z (hBt hz)) (Real.exp_pos _)
  obtain ⟨z₀, hz₀, hmin⟩ := hB.exists_isMinOn hne hdc
  have hd₀ : 0 < d z₀ := hdp z₀ hz₀
  refine ⟨(d z₀)⁻¹, inv_pos.mpr hd₀, fun q hq φ hφ s => ?_⟩
  let f : PolytopeToricVariety γ hs → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (‖s p‖ ^ 2) * multiplierWeight (q : ℝ) (φ p)
  have hf : Measurable f := measurable_originalSectionDensity
    (toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q)).Fiber hφ (q : ℝ) s
  let F : ComplexModel n → ℝ≥0∞ := multiplierDensity
    (fun y => φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal))
    (q : ℝ) (toricOriginalSectionCoeff
      (toricNativeFullSectionEquiv (toricNativeNegativeTwistMetric h q) s) v)
  have hchart : (∫⁻ p in e.val.source ∩ e.val ⁻¹' B, f p ∂μ) =
      ∫⁻ z in B, ENNReal.ofReal (d z) * F z := by
    rw [setLIntegral_source_inter_preimage e hρs.continuousOn hmap hB hBt hf]
    apply lintegral_congr
    intro z
    change ENNReal.ofReal (ρ z) *
      (ENNReal.ofReal (‖s ((originalPolytopeNativeModelChart γ hs v).symm z)‖ ^ 2) *
        multiplierWeight (q : ℝ) (φ ((originalPolytopeNativeModelChart γ hs v).symm z))) = _
    rw [toricNativeNegativeTwist_weightedDensity_chart h q hq φ s v z]
    have hρz : 0 ≤ ρ z := (hρpos z (by
      change z ∈ (originalPolytopeNativeModelChart γ hs v).target
      rw [originalPolytopeNativeModelChart_target]
      exact mem_univ z)).le
    rw [← mul_assoc, ← ENNReal.ofReal_mul hρz]
  calc
    ∫⁻ z in B, F z ≤ ∫⁻ z in B,
        ENNReal.ofReal (d z₀)⁻¹ * (ENNReal.ofReal (d z) * F z) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB.isClosed.measurableSet] with z hz
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hd₀.le)]
      apply le_mul_of_one_le_left zero_le
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_mul_eq_div, le_div_iff₀ hd₀, one_mul]
      exact hmin hz
    _ = ENNReal.ofReal (d z₀)⁻¹ * ∫⁻ z in B, ENNReal.ofReal (d z) * F z :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (d z₀)⁻¹ * ∫⁻ p in e.val.source ∩ e.val ⁻¹' B, f p ∂μ := by rw [hchart]
    _ ≤ ENNReal.ofReal (d z₀)⁻¹ * ∫⁻ p, f p ∂μ :=
      mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le

end SGPT.Toric

end
end ToricCanonicalFragment061
/- END SGPT.Toric.ToricNativeStrictLocalBudget -/

/- BEGIN SGPT.Toric.ToricNativeStrictWeightedMass; source SHA256 dcb14da22bcf862fb37c7bd6b0bc801445b1eaaf9e5df7856346caef0972440c -/
section ToricCanonicalFragment062

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Exact physical exponential of the literal original finite potential,
with the genuine zero-density convention and every original degree q>0. -/
theorem toricNativeFiniteSectionPotential_exp {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q) {a : ℕ}
    (s : Fin a → ToricNativePlainPowerSections h q) (p : PolytopeToricVariety γ hs) :
    EReal.exp (((q : ℝ) : EReal) * toricNativeFiniteSectionPotential h q s p) =
      toricNativeFiniteSectionDensity h q s p := by
  unfold toricNativeFiniteSectionPotential
  have hi : ((q : ℝ) : EReal) * ((q : ℝ)⁻¹ : EReal) = 1 := by
    rw [← EReal.coe_inv, ← EReal.coe_mul,
      mul_inv_cancel₀ (show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne'), EReal.coe_one]
  rw [← mul_assoc, hi, one_mul, ENNReal.exp_log]

/-- Every internally produced full negative-twist ON section has finite
SAME original q-phi weighted physical integral against raw Guillemin volume. -/
theorem toricNativeNegativeTwistPhiFiniteSections_weighted_mass {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (i : Fin (Fintype.card (ToricNativeMultiplierCharacterIndex
      (toricNativeNegativeTwistMetric h q) 1 Nat.zero_lt_one (toricNativeScaledPhi_qpsh q hq hφ)))) :
    (∫⁻ p, ENNReal.ofReal (‖toricNativeNegativeTwistPhiFiniteSections h q hq hφ hinv i p‖ ^ 2) *
      multiplierWeight (q : ℝ) (φ p)
      ∂(kahlerVolume (polytopeToricKahlerBackground γ hs))) < ⊤ := by
  let B := toricNativeNegativeTwistMetric h q
  let hψ := toricNativeScaledPhi_qpsh q hq hφ
  let hψinv := toricNativeScaledPhi_invariant q hinv
  let m := (Fintype.equivFin (ToricNativeMultiplierCharacterIndex B 1 Nat.zero_lt_one hψ)).symm i
  have hn := toricNativePhiOrthonormalPlainSection_original_norm B 1 Nat.zero_lt_one hψ hψinv m
  have hfin : (∫⁻ p, originalSectionDensity (toricNativePlainPowerBundle B 1).Fiber
      (fun x => ((q : ℝ) : EReal) * φ x) 1
      (toricNativePhiOrthonormalPlainSection B 1 Nat.zero_lt_one hψ hψinv m) p
      ∂(kahlerVolume (polytopeToricKahlerBackground γ hs))) < ⊤ := by
    have hnormfin : nativePhiExtendedSectionNorm (toricNativePlainPowerBundle B 1)
        (fun x => ((q : ℝ) : EReal) * φ x) 1
        (kahlerVolume (polytopeToricKahlerBackground γ hs))
        (toricNativePhiOrthonormalPlainSection B 1 Nat.zero_lt_one hψ hψinv m) < ⊤ := by
      rw [hn]
      exact ENNReal.one_lt_top
    apply (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp
    simpa only [nativePhiExtendedSectionNorm, Nat.cast_one] using hnormfin
  simpa only [originalSectionDensity, Nat.cast_one, toricNativeMultiplierWeight_one_scaled,
    toricNativeNegativeTwistPhiFiniteSections, toricNativePhiFiniteSections, B, hψ, hψinv, m] using hfin

/-- The actual entire physical strict product sum has finite ORIGINAL
mixed exponential mass. No local Bergman, ideal-generation or extraction
certificate is input; the full singular-phi ON space produces finiteness. -/
theorem toricNativeStrictPhiProductPotential_weighted_mass {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    (∫⁻ p, EReal.exp (((q : ℝ) : EReal) * toricNativeStrictPhiProductPotential h q hq hφ hinv p) *
      multiplierWeight (q : ℝ) (φ p)
      ∂(kahlerVolume (polytopeToricKahlerBackground γ hs))) < ⊤ := by
  let μ := kahlerVolume (polytopeToricKahlerBackground γ hs)
  let s := toricNativeNegativeTwistPhiFiniteSections h q hq hφ hinv
  have heq : (∫⁻ p, EReal.exp (((q : ℝ) : EReal) *
      toricNativeStrictPhiProductPotential h q hq hφ hinv p) * multiplierWeight (q : ℝ) (φ p) ∂μ) =
      ∑ i, ∫⁻ p, ENNReal.ofReal (‖s i p‖ ^ 2) * multiplierWeight (q : ℝ) (φ p) ∂μ := by
    calc
      _ = ∫⁻ p, ∑ i, ENNReal.ofReal (‖s i p‖ ^ 2) * multiplierWeight (q : ℝ) (φ p) ∂μ := by
        apply lintegral_congr
        intro p
        rw [toricNativeStrictPhiProductPotential, toricNativeFiniteSectionPotential_exp h q hq,
          toricNativeStrictPhiProductSections, toricNativeStrictProductSections_density,
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), Finset.sum_mul]
        rfl
      _ = _ := lintegral_finsetSum _ (fun i _ =>
        (measurable_originalSectionDensity
          (toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q)).Fiber
          (toricNativePhi_globalQpsh hφ).1.upperSemicontinuous.measurable (q : ℝ) (s i)))
  rw [heq]
  exact ENNReal.sum_lt_top.mpr (fun i _ =>
    toricNativeNegativeTwistPhiFiniteSections_weighted_mass h q hq hφ hinv i)

end SGPT.Toric

end
end ToricCanonicalFragment062
/- END SGPT.Toric.ToricNativeStrictWeightedMass -/

/- BEGIN SGPT.Toric.ToricNativeStrictGlobalLocalKernel; source SHA256 a81270b64ce37a118cde876434205df75540246b63d841c024bf690918f31fa2 -/
section ToricCanonicalFragment063

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.BergmanSupWeight
open SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeRightUnit SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Exact full original unit-ball readback of the literal physical product
density, proved through actual full ON enumeration and true product norms. -/
theorem toricNativeStrictPhiProductDensity_eq_original_kernel {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (p : PolytopeToricVariety γ hs) :
    toricNativeFiniteSectionDensity h q (toricNativeStrictPhiProductSections h q hq hφ hinv) p =
      nativePhiOriginalBergmanDensity (toricNativeHermitianLineBundle (toricNativeNegativeTwistMetric h q))
        unit 1 (φ := fun x => ((q : ℝ) : EReal) * φ x)
        (kahlerVolume (polytopeToricKahlerBackground γ hs)) p := by
  rw [toricNativeStrictPhiProductSections, toricNativeStrictProductSections_density,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  change toricNativeFiniteSectionDensity (toricNativeNegativeTwistMetric h q) 1
    (toricNativeNegativeTwistPhiFiniteSections h q hq hφ hinv) p = _
  rw [toricNativeNegativeTwistPhiFiniteSections, toricNativePhiFiniteSections_density,
    toricNativePhiOriginalBergmanDensity_eq_eigenbasis]

/-- The actual full global integral unit ball restricts to the true local
corrected-weight Bergman ball with one INTERNALLY produced finite budget.
The measure, physical bundle and original singular phi are all retained. -/
theorem exists_toricNativeStrictPhi_global_le_local {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) (z : ComplexModel n)
    (R : ℝ) (_hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ hq : 0 < q,
      ∀ φ : PolytopeToricVariety γ hs → EReal,
      ∀ hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ,
      ∀ hinv : PolytopeToricInvariant γ hs φ,
      toricNativeFiniteSectionDensity h q (toricNativeStrictPhiProductSections h q hq hφ hinv)
          ((originalPolytopeNativeModelChart γ hs v).symm z) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal (Real.exp (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z)) *
          bergmanSup (ball z R)
            (fun y => multiplierWeight (q : ℝ)
              (φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal))) z := by
  obtain ⟨C, hC, hbudget⟩ := exists_toricNativeNegativeTwist_local_budget h v (isCompact_closedBall z R)
  refine ⟨C, hC, fun q hq φ hφ hinv => ?_⟩
  rw [toricNativeStrictPhiProductDensity_eq_original_kernel]
  apply iSup_le
  intro s
  apply iSup_le
  intro hnorm
  let B := toricNativeNegativeTwistMetric h q
  let μ := kahlerVolume (polytopeToricKahlerBackground γ hs)
  let t : ToricNativeHolomorphicSections B :=
    nativeRightUnitSectionsEquiv (toricNativeHermitianLineBundle B) s
  let f := toricOriginalSectionCoeff (toricNativeFullSectionEquiv B t) v
  have htnorm (p : PolytopeToricVariety γ hs) : ‖t p‖ = ‖s p‖ :=
    nativeRightUnitSectionsEquiv_norm (toricNativeHermitianLineBundle B) s p
  have hglobal : (∫⁻ p, ENNReal.ofReal (‖t p‖ ^ 2) * multiplierWeight (q : ℝ) (φ p) ∂μ) ≤ 1 := by
    convert hnorm using 1
    apply lintegral_congr
    intro p
    simp only [originalSectionDensity, Nat.cast_one, toricNativeMultiplierWeight_one_scaled, htnorm]
  have hlocal : (∫⁻ y in ball z R, ENNReal.ofReal (‖f y‖ ^ 2) *
      multiplierWeight (q : ℝ)
        (φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal))) ≤
        ENNReal.ofReal C := by
    exact (lintegral_mono_set ball_subset_closedBall).trans
      ((hbudget q hq φ (toricNativePhi_globalQpsh hφ).1.upperSemicontinuous.measurable t).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hglobal zero_le))
  have hf : DifferentiableOn ℂ f (ball z R) := (differentiable_toricOriginalSectionCoeff _ v).differentiableOn
  have hpoint := bergmanSup_extremal hf (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top hlocal z
  have hz : z ∈ (originalPolytopeNativeModelChart γ hs v).target := by
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  have hphysical := toricNativeFullSectionEquiv_symm_norm_sq B (toricNativeFullSectionEquiv B t) v
    ((originalPolytopeNativeModelChart γ hs v).map_target hz)
  simp only [LinearEquiv.symm_apply_apply, (originalPolytopeNativeModelChart γ hs v).right_inv hz] at hphysical
  have hexp : Real.exp (-B.weight v z) =
      Real.exp (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z) := by
    congr 1
    dsimp only [B, toricNativeNegativeTwistMetric, BigToricMetric.subMetric, BigToricMetric.zsmulMetric]
    simp only [Int.cast_natCast]
    ring
  calc
    ENNReal.ofReal (‖s ((originalPolytopeNativeModelChart γ hs v).symm z)‖ ^ 2) =
        ENNReal.ofReal (‖t ((originalPolytopeNativeModelChart γ hs v).symm z)‖ ^ 2) :=
      congrArg (fun x : ℝ => ENNReal.ofReal (x ^ 2)) (htnorm _).symm
    _ = ENNReal.ofReal (‖f z‖ ^ 2) * ENNReal.ofReal (Real.exp
        (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z)) := by
      rw [hphysical, hexp, ENNReal.ofReal_mul (sq_nonneg _)]
    _ ≤ _ := by
      calc
        _ ≤ (ENNReal.ofReal C * bergmanSup (ball z R)
          (fun y => multiplierWeight (q : ℝ)
            (φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal))) z) *
          ENNReal.ofReal (Real.exp
            (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z)) :=
          mul_le_mul_of_nonneg_right hpoint zero_le
        _ = _ := by ac_rfl

/-- Genuine arbitrary-phi local-mean-value upper estimate for the SAME
actual global physical product potential. Every error is O(1/q), with
its constant internally produced from the original raw-volume budget. -/
theorem exists_toricNativeStrictPhi_local_upper {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) (z : ComplexModel n)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ hq : 0 < q,
      ∀ φ : PolytopeToricVariety γ hs → EReal,
      ∀ hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ,
      ∀ hinv : PolytopeToricInvariant γ hs φ,
      ∀ b : ℝ, (∀ y ∈ ball z R,
        φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal) ≤ (b : EReal)) →
      toricNativeStrictPhiProductPotential h q hq hφ hinv
          ((originalPolytopeNativeModelChart γ hs v).symm z) ≤
        ((b - h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C -
          Real.log (volume (ball z (R / 2))).toReal) / q : ℝ) : EReal) := by
  obtain ⟨C, hC, hkernel⟩ := exists_toricNativeStrictPhi_global_le_local h v z R hR
  refine ⟨C, hC, fun q hq φ hφ hinv b hb => ?_⟩
  let P : ComplexModel n → EReal := fun y =>
    φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal)
  have hlog := ENNReal.log_monotone (hkernel q hq φ hφ hinv)
  have hl : ENNReal.log (toricNativeFiniteSectionDensity h q
      (toricNativeStrictPhiProductSections h q hq hφ hinv)
      ((originalPolytopeNativeModelChart γ hs v).symm z)) ≤
      ((Real.log C + (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z) : ℝ) : EReal) +
        bergmanLog (ball z R) (fun y => multiplierWeight (q : ℝ) (P y)) z := by
    simpa only [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hC,
      ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp, ← EReal.coe_add, bergmanLog] using hlog
  have hm := monotone_eReal_const_mul (c := (q : ℝ)⁻¹) (by positivity) hl
  dsimp only at hm
  rw [EReal.left_distrib_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr (show (0 : ℝ) ≤ (q : ℝ)⁻¹ by positivity)) (EReal.coe_ne_top _),
    ← EReal.coe_mul] at hm
  have hreal : (q : ℝ)⁻¹ * (Real.log C + (-(q : ℝ) * h.weight v z +
      (toricFullLatticeMetric (hs := hs)).weight v z)) =
      -h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q := by
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    ring
  rw [hreal] at hm
  have hscaled : toricNativeStrictPhiProductPotential h q hq hφ hinv
      ((originalPolytopeNativeModelChart γ hs v).symm z) ≤
      bergmanWeight (ball z R) P q z +
        ((-h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q : ℝ) : EReal) := by
    simpa only [toricNativeStrictPhiProductPotential, toricNativeFiniteSectionPotential,
      bergmanWeight, EReal.coe_inv, add_comm] using hm
  have hlocal := bergmanWeight_le isOpen_ball (show 1 ≤ q by omega) (half_pos hR)
    (closedBall_subset_ball (half_lt_self hR))
    (fun y hy => hb y (ball_subset_ball (half_le_self hR.le) hy))
  calc
    _ ≤ bergmanWeight (ball z R) P q z +
        ((-h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q : ℝ) : EReal) := hscaled
    _ ≤ ((b - (q : ℝ)⁻¹ * Real.log (volume (ball z (R / 2))).toReal : ℝ) : EReal) +
        ((-h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q : ℝ) : EReal) :=
      add_le_add hlocal le_rfl
    _ = _ := by
      rw [← EReal.coe_add]
      congr 1
      simp only [div_eq_mul_inv]
      ring

end SGPT.Toric

end
end ToricCanonicalFragment063
/- END SGPT.Toric.ToricNativeStrictGlobalLocalKernel -/

/- BEGIN SGPT.Toric.ToricNativeStrictPointwiseConvergence; source SHA256 ae625c4bde456e89c7bc67e8f0023bbc1a18f1fc2f3ed43ea4e8de037e8b4055 -/
section ToricCanonicalFragment064

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open scoped Topology BigOperators ContDiff Manifold ENNReal
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Genuine arbitrary-phi upper approximation at EVERY original point,
including original poles, from actual raw-volume/entire-section mean value. -/
theorem toricNativeStrictPhiProductPotential_eventually_lt_real {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (p : PolytopeToricVariety γ hs)
    (b : ℝ) (hb : φ p < (b : EReal)) :
    ∃ N : ℕ, 0 < N ∧ ∀ q : ℕ, N ≤ q → ∀ hq : 0 < q,
      toricNativeStrictPhiProductPotential h q hq hφ hinv p < (b : EReal) := by
  obtain ⟨m, hmφ, hmb⟩ := EReal.exists_between_coe_real hb
  have hmbR : m < b := EReal.coe_lt_coe_iff.mp hmb
  let v := toricNativePreferredVertex γ hs p
  let c := originalPolytopeNativeModelChart γ hs v
  let z := c p
  have hp : p ∈ c.source := toricNativePreferredVertex_mem p
  have hzp : c.symm z = p := c.left_inv hp
  have hct : c.target = univ := originalPolytopeNativeModelChart_target γ hs v
  have hsymm : Continuous c.symm := continuousOn_univ.mp (by
    rw [← hct]
    exact c.continuousOn_symm)
  let P : ComplexModel n → EReal := fun y => φ (c.symm y) + (h.weight v y : EReal)
  have hPusc : UpperSemicontinuous P := upperSemicontinuous_eReal_add
    ((toricNativePhi_globalQpsh hφ).1.upperSemicontinuous.comp hsymm)
    (continuous_coe_real_ereal.comp (h.smooth v).continuous).upperSemicontinuous
    (fun y => hφ.ne_top (c.symm y)) (fun y => EReal.coe_ne_top (h.weight v y))
  have hPz : P z < ((m + h.weight v z : ℝ) : EReal) := by
    dsimp only [P]
    rw [hzp, EReal.coe_add]
    exact EReal.add_lt_add_right_coe hmφ _
  obtain ⟨R, hR, hRb⟩ := Metric.mem_nhds_iff.mp (hPusc z _ hPz)
  obtain ⟨C, _, hupper⟩ := exists_toricNativeStrictPhi_local_upper h v z R hR
  let A : ℝ := (toricFullLatticeMetric (hs := hs)).weight v z + Real.log C -
    Real.log (volume (ball z (R / 2))).toReal
  have hbound (q : ℕ) (hq : 0 < q) :
      toricNativeStrictPhiProductPotential h q hq hφ hinv p ≤ ((m + A / q : ℝ) : EReal) := by
    have hh := hupper q hq φ hφ hinv (m + h.weight v z) (fun y hy => (hRb hy).le)
    simp only [add_sub_cancel_right] at hh
    change toricNativeStrictPhiProductPotential h q hq hφ hinv (c.symm z) ≤ ((m + A / q : ℝ) : EReal) at hh
    rwa [hzp] at hh
  have hAzero : Tendsto (fun q : ℕ => A / (q : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun q : ℕ => m + A / (q : ℝ)) atTop (𝓝 m) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hAzero)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hmbR))
  refine ⟨max N 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), fun q hq hqpos => ?_⟩
  exact (hbound q hqpos).trans_lt (EReal.coe_lt_coe_iff.mpr (hN q (le_of_max_le_left hq)))

/-- Genuine lower approximation from the fixed ORIGINAL L and negative
auxiliary point-extension estimate, with all constants internally produced. -/
theorem toricNativeStrictPhiProductPotential_eventually_gt_real {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (hpositive : IsKahlerCurrentPotential h.form φ) (p : PolytopeToricVariety γ hs)
    (a : ℝ) (ha : (a : EReal) < φ p) :
    ∃ N : ℕ, 0 < N ∧ ∀ q : ℕ, N ≤ q → ∀ hq : 0 < q,
      (a : EReal) < toricNativeStrictPhiProductPotential h q hq hφ hinv p := by
  have hbot : φ p ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe a).trans ha)
  have hr : φ p = ((φ p).toReal : EReal) := (EReal.coe_toReal (hφ.ne_top p) hbot).symm
  have haR : a < (φ p).toReal := by
    rw [hr] at ha
    exact EReal.coe_lt_coe_iff.mp ha
  obtain ⟨q₀, C, hq₀, _, hlower⟩ := toricNativeStrictPhiProductPotential_lower h hφ hinv hpositive
  have hCzero : Tendsto (fun q : ℕ => Real.log C / (q : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun q : ℕ => (φ p).toReal - Real.log C / (q : ℝ)) atTop (𝓝 (φ p).toReal) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hCzero)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds haR))
  refine ⟨max q₀ N, lt_of_lt_of_le hq₀ (le_max_left _ _), fun q hq hqpos => ?_⟩
  have hb := hlower q (le_of_max_le_left hq) hqpos p
  rw [hr, ← EReal.coe_sub] at hb
  exact (EReal.coe_lt_coe_iff.mpr (hN q (le_of_max_le_right hq))).trans_le hb


end SGPT.Toric

end
end ToricCanonicalFragment064
/- END SGPT.Toric.ToricNativeStrictPointwiseConvergence -/

/- BEGIN SGPT.Toric.ToricWeightedMassSeparatedIdeals; source SHA256 a0ffc8eb61111ec46039e944683ae5777f0ae58d7ecac45d1358f38b4a36d6f9 -/
section ToricCanonicalFragment065

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open QuasiEquisingularApproximationDemailly
open scoped Topology ENNReal ContDiff Manifold
variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X]

omit [IsComplexManifold n X] in
/-- Finite mass against an ACTUAL smooth positive volume gives genuine
local coordinate mass, by the internally chosen positive chart minimum. -/
theorem chart_local_mass_of_global_finite {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {F : X → ℝ≥0∞}
    (hF : Measurable F) (hfin : (∫⁻ x, F x ∂μ) < ⊤)
    (e : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ e.val.target ∧
      (∫⁻ y in ball z r, F (e.val.symm y)) < ⊤ := by
  obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp e.val.open_target z hz
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hKt : closedBall z r ⊆ e.val.target := (closedBall_subset_ball (half_lt_self hR)).trans hRt
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ e
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall z r).exists_isMinOn
    ⟨z, mem_closedBall_self hr.le⟩ (hρs.continuousOn.mono hKt)
  have hc : 0 < ρ z₀ := hρpos z₀ (hKt hz₀)
  refine ⟨r, hr, hKt, ?_⟩
  have hbound : (∫⁻ y in closedBall z r, F (e.val.symm y)) ≤
      ENNReal.ofReal (ρ z₀)⁻¹ * ∫⁻ x, F x ∂μ := by
    calc
      _ ≤ ∫⁻ y in closedBall z r,
          ENNReal.ofReal (ρ z₀)⁻¹ * (ENNReal.ofReal (ρ y) * F (e.val.symm y)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with y hy
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
        apply le_mul_of_one_le_left zero_le
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]
        exact hmin hy
      _ = ENNReal.ofReal (ρ z₀)⁻¹ *
          ∫⁻ y in closedBall z r, ENNReal.ofReal (ρ y) * F (e.val.symm y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (ρ z₀)⁻¹ *
          ∫⁻ x in e.val.source ∩ e.val ⁻¹' closedBall z r, F x ∂μ := by
        rw [setLIntegral_source_inter_preimage e hρs.continuousOn hmap (isCompact_closedBall z r) hKt hF]
      _ ≤ _ := mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le
  exact ((lintegral_mono_set ball_subset_closedBall).trans hbound).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

/-- Actual finite mixed exponential mass and a pointwise lower comparison
produce the literal separated multiplier inclusion in EVERY original chart.
No analytic type, ideal-generation, or multiplier-inclusion certificate is input. -/
theorem multiplierIdealIncluded_of_finite_mixed_mass {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ)
    {u v : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u) (hv : Measurable v)
    (hle : ∀ x, u x ≤ v x) (q : ℕ) (hq : 0 < q)
    (hmass : (∫⁻ x, EReal.exp (((q : ℝ) : EReal) * v x) * multiplierWeight (q : ℝ) (u x) ∂μ) < ⊤)
    {c d : ℝ} (hc : 0 < c) (hcd : c < d) (hsep : c * d ≤ (q : ℝ) * (d - c)) :
    MultiplierIdealIncluded (n := n) v d u c := by
  intro e z hz f hfz hmem'
  have hmem : MultiplierIntegrableAt (chartFunction v e) d f z volume :=
    (multiplierIntegrableAt_ambient_iff_borel _ _ _ _).mpr hmem'
  apply (multiplierIntegrableAt_ambient_iff_borel _ _ _ _).mp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let F : X → ℝ≥0∞ := fun x => EReal.exp (((q : ℝ) : EReal) * v x) * multiplierWeight (q : ℝ) (u x)
  have hF : Measurable F := (EReal.measurable_exp.comp
      ((FirstPass.continuous_eReal_const_mul hqR.ne').measurable.comp hv)).mul
    (EReal.measurable_exp.comp (continuous_neg.measurable.comp
      ((FirstPass.continuous_eReal_const_mul hqR.ne').measurable.comp
        hu.1.upperSemicontinuous.measurable)))
  obtain ⟨r, hr, hrt, hlocal⟩ := chart_local_mass_of_global_finite hμ hF hmass e hz
  obtain ⟨_, U, hU, hzU, hfdiff, hfint⟩ := hmem
  obtain ⟨B, hBsub, hB, hzB⟩ := _root_.mem_nhds_iff.mp
    (hfz.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖f z‖)))
  let W := (U ∩ B) ∩ ball z r
  have hW : IsOpen W := (hU.inter hB).inter isOpen_ball
  have hzW : z ∈ W := ⟨⟨hzU, hzB⟩, mem_ball_self hr⟩
  have hWU : W ⊆ U := fun _ hw => hw.1.1
  have hWB : W ⊆ ball z r := fun _ hw => hw.2
  let A : ℝ := (‖f z‖ + 1) ^ 2
  have hpoint : ∀ y ∈ W, multiplierDensity (chartFunction u e) c f y ≤
      multiplierDensity (chartFunction v e) d f y + ENNReal.ofReal A * F (e.val.symm y) := by
    intro y hy
    have hfbound : ‖f y‖ ^ 2 ≤ A := pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (hBsub hy.1.2)) 2
    have hweight := multiplierWeight_le_add hc hcd hsep (hle (e.val.symm y))
    calc
      _ ≤ ENNReal.ofReal (‖f y‖ ^ 2) *
          (multiplierWeight d (v (e.val.symm y)) +
            EReal.exp (((q : ℝ) : EReal) * v (e.val.symm y)) * multiplierWeight (q : ℝ) (u (e.val.symm y))) :=
        mul_le_mul_right hweight _
      _ = multiplierDensity (chartFunction v e) d f y +
          ENNReal.ofReal (‖f y‖ ^ 2) * F (e.val.symm y) := by
        simp only [multiplierDensity, chartFunction, F, mul_add]
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hfbound) zero_le)
  have hmeasu : AEMeasurable (multiplierDensity (chartFunction u e) c f) (volume.restrict W) :=
    aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn hW
      (fun y hy => hu.1 e y (hrt (ball_subset_closedBall hy.2))) hc.ne'
      (hfdiff.mono hWU).continuousOn
  have hmeasv : AEMeasurable (multiplierDensity (chartFunction v e) d f) (volume.restrict W) :=
    hfint.1.mono_measure (Measure.restrict_mono hWU le_rfl)
  refine ⟨hc, W, hW, hzW, hfdiff.mono hWU, hmeasu, ?_⟩
  calc
    _ ≤ ∫⁻ y in W, multiplierDensity (chartFunction v e) d f y +
        ENNReal.ofReal A * F (e.val.symm y) :=
      setLIntegral_mono_ae' hW.measurableSet (Eventually.of_forall hpoint)
    _ = (∫⁻ y in W, multiplierDensity (chartFunction v e) d f y) +
        ENNReal.ofReal A * ∫⁻ y in W, F (e.val.symm y) := by
      rw [lintegral_add_left' hmeasv, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.add_lt_top.mpr
      ⟨(lintegral_mono_set hWU).trans_lt hfint.2,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((lintegral_mono_set hWB).trans_lt hlocal)⟩

end SGPT.Toric

end
end ToricCanonicalFragment065
/- END SGPT.Toric.ToricWeightedMassSeparatedIdeals -/

/- BEGIN SGPT.Toric.ToricNativeStrictSeparatedApproximation; source SHA256 9b05ea014a2e72e42eb673b5221aece1e7ef943f0d3b431f699e08837d4a38b7 -/
section ToricCanonicalFragment066

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Finite real shifts of the ACTUAL original physical product sum retain
finite original q-phi mixed mass, including every pole and common zero. -/
theorem toricNativeStrictPhiProductPotential_shifted_mass {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (a : ℝ) :
    (∫⁻ p, EReal.exp (((q : ℝ) : EReal) *
        (toricNativeStrictPhiProductPotential h q hq hφ hinv p + (a : EReal))) *
      multiplierWeight (q : ℝ) (φ p)
      ∂(kahlerVolume (polytopeToricKahlerBackground γ hs))) < ⊤ := by
  have he (p : PolytopeToricVariety γ hs) :
      EReal.exp (((q : ℝ) : EReal) *
        (toricNativeStrictPhiProductPotential h q hq hφ hinv p + (a : EReal))) =
      ENNReal.ofReal (Real.exp ((q : ℝ) * a)) *
        EReal.exp (((q : ℝ) : EReal) * toricNativeStrictPhiProductPotential h q hq hφ hinv p) := by
    rw [EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr (Nat.cast_nonneg q)) (EReal.coe_ne_top _),
      ← EReal.coe_mul, EReal.exp_add, EReal.exp_coe, mul_comm]
  calc
    _ = ENNReal.ofReal (Real.exp ((q : ℝ) * a)) *
        ∫⁻ p, EReal.exp (((q : ℝ) : EReal) * toricNativeStrictPhiProductPotential h q hq hφ hinv p) *
          multiplierWeight (q : ℝ) (φ p)
          ∂(kahlerVolume (polytopeToricKahlerBackground γ hs)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro p
      rw [he, mul_assoc]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (toricNativeStrictPhiProductPotential_weighted_mass h q hq hφ hinv)



end SGPT.Toric

end
end ToricCanonicalFragment066
/- END SGPT.Toric.ToricNativeStrictSeparatedApproximation -/

/- BEGIN SGPT.Toric.ToricNativeStrictPhysicalFamily; source SHA256 e21f8171d992e54a57eea906a8ad01bcfa337b586a8bc54b5f4e206a5187c64b -/
section ToricCanonicalFragment067

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual pointwise convergence along EVERY cofinal positive degree
choice, with no supplied convergence or extraction statement. -/
theorem toricNativeStrictPhiProductPotential_tendsto_cofinal {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (hpositive : IsKahlerCurrentPotential h.form φ)
    (Q : ℕ → ℕ) (hQpos : ∀ j, 0 < Q j) (hQ : Tendsto Q atTop atTop)
    (p : PolytopeToricVariety γ hs) :
    Tendsto (fun j => toricNativeStrictPhiProductPotential h (Q j) (hQpos j) hφ hinv p)
      atTop (𝓝 (φ p)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r, har, hrφ⟩ := EReal.exists_between_coe_real ha
    obtain ⟨N, _, hN⟩ := toricNativeStrictPhiProductPotential_eventually_gt_real h hφ hinv hpositive p r hrφ
    filter_upwards [hQ.eventually (eventually_ge_atTop N)] with j hj
    exact har.trans (hN (Q j) hj (hQpos j))
  · intro b hb
    obtain ⟨r, hφr, hrb⟩ := EReal.exists_between_coe_real hb
    obtain ⟨N, _, hN⟩ := toricNativeStrictPhiProductPotential_eventually_lt_real h hφ hinv p r hφr
    filter_upwards [hQ.eventually (eventually_ge_atTop N)] with j hj
    exact (hN (Q j) hj (hQpos j)).trans hrb


end SGPT.Toric

end
end ToricCanonicalFragment067
/- END SGPT.Toric.ToricNativeStrictPhysicalFamily -/

/- BEGIN SGPT.Toric.ToricNativeStrictScalingInterval; source SHA256 5d40f16c6498aa81b5a63fbdfe18549016275b9f02787329b504460ad5aa414d -/
section ToricCanonicalFragment068

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open scoped Topology BigOperators ContDiff Manifold ENNReal

/-- Original strictness INTERNALLY produces a whole same-theta positive
scaling interval and ONE genuine positive background for every scaled input. -/
theorem exists_sameTheta_strict_scaling_interval {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    {θ : ClosedRealOneOneForm n X} {φ : X → EReal}
    (hpositive : IsKahlerCurrentPotential θ φ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ omega : KahlerBackground n X,
      ∀ c : ℝ, 1 - ε ≤ c → c ≤ 1 →
        IsThetaPshPotential (θ - omega.form).val (fun x => (c : EReal) * φ x) := by
  obtain ⟨omega, hφomega⟩ := hpositive
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega θ
  let ε : ℝ := 1 / (4 * (A + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε < 1 := by
    dsimp only [ε]
    rw [div_lt_one (by positivity)]
    linarith
  refine ⟨ε, hε, hε1, KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 2) omega, ?_⟩
  intro c hc hc1
  have hcpos : 0 < c := by linarith
  have hk : 0 ≤ c - 1 / 2 - (1 - c) * A := by
    have hbound : (1 - c) * (A + 1) ≤ ε * (A + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have heps : ε * (A + 1) = 1 / 4 := by
      dsimp only [ε]
      field_simp
    nlinarith
  have hscaled := RestrictedApproximantComparison.isThetaPshPotential_smul hφomega hcpos
  have h₁ := LocalPotentials.isThetaPshPotential_add_of_semipositive hscaled
    (KahlerDomination.isSemipositive_smul hsemi (sub_nonneg.mpr hc1))
  have h₂ := LocalPotentials.isThetaPshPotential_add_of_semipositive h₁
    (KahlerDomination.isSemipositive_smul omega.isSemipositive hk)
  have heq : c • (θ - omega.form) + (1 - c) • (θ + A • omega.form) +
      (c - 1 / 2 - (1 - c) * A) • omega.form = θ - (1 / 2 : ℝ) • omega.form := by module
  change IsThetaPshPotential (θ - (1 / 2 : ℝ) • omega.form).val _
  rwa [heq] at h₂

open SGPT.PSH SGPT.PSH.VariableComplexAtlas
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Original toric membership and original strict current alone produce
an actual same-theta toric strict interval of scaled original inputs. -/
theorem exists_toricNative_sameTheta_strict_scaling_interval {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hmem : φ ∈ h.PSHTor) (hpositive : IsKahlerCurrentPotential h.form φ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ c : ℝ, 1 - ε ≤ c → c ≤ 1 →
      (fun p => (c : EReal) * φ p) ∈ h.PSHTor ∧
      IsKahlerCurrentPotential h.form (fun p => (c : EReal) * φ p) := by
  obtain ⟨ε, hε, hε1, omega, hscaled⟩ := exists_sameTheta_strict_scaling_interval hpositive
  refine ⟨ε, hε, hε1, fun c hc hc1 => ?_⟩
  have hp := hscaled c hc hc1
  refine ⟨⟨?_, ?_⟩, ⟨omega, hp⟩⟩
  · apply (isThetaPSH_iff_nativeThetaPotential h.atlasForm _).mpr
    have h' := LocalPotentials.isThetaPshPotential_add_of_semipositive hp omega.isSemipositive
    rwa [sub_add_cancel] at h'
  · intro a ha p
    dsimp only
    rw [hmem.2 a ha p]

end SGPT.Toric

end
end ToricCanonicalFragment068
/- END SGPT.Toric.ToricNativeStrictScalingInterval -/

/- BEGIN SGPT.Toric.ToricNativeStrictUniformLocalKernel; source SHA256 722a1ec078edbc95a6b9929e7d2f0b918e80016bab5de644200958b294675d09 -/
section ToricCanonicalFragment069

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.BergmanSupWeight
open SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeRightUnit SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual full global integral unit ball restricts to the true local
corrected-weight Bergman ball with one INTERNALLY produced finite budget.
The measure, physical bundle and original singular phi are all retained. -/
theorem exists_toricNativeStrictPhi_uniform_global_le_local {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) (z₀ : ComplexModel n)
    (R : ℝ) (_hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ hq : 0 < q,
      ∀ φ : PolytopeToricVariety γ hs → EReal,
      ∀ hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ,
      ∀ hinv : PolytopeToricInvariant γ hs φ, ∀ z : ComplexModel n,
      toricNativeFiniteSectionDensity h q (toricNativeStrictPhiProductSections h q hq hφ hinv)
          ((originalPolytopeNativeModelChart γ hs v).symm z) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal (Real.exp (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z)) *
          bergmanSup (ball z₀ R)
            (fun y => multiplierWeight (q : ℝ)
              (φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal))) z := by
  obtain ⟨C, hC, hbudget⟩ := exists_toricNativeNegativeTwist_local_budget h v (isCompact_closedBall z₀ R)
  refine ⟨C, hC, fun q hq φ hφ hinv z => ?_⟩
  rw [toricNativeStrictPhiProductDensity_eq_original_kernel]
  apply iSup_le
  intro s
  apply iSup_le
  intro hnorm
  let B := toricNativeNegativeTwistMetric h q
  let μ := kahlerVolume (polytopeToricKahlerBackground γ hs)
  let t : ToricNativeHolomorphicSections B :=
    nativeRightUnitSectionsEquiv (toricNativeHermitianLineBundle B) s
  let f := toricOriginalSectionCoeff (toricNativeFullSectionEquiv B t) v
  have htnorm (p : PolytopeToricVariety γ hs) : ‖t p‖ = ‖s p‖ :=
    nativeRightUnitSectionsEquiv_norm (toricNativeHermitianLineBundle B) s p
  have hglobal : (∫⁻ p, ENNReal.ofReal (‖t p‖ ^ 2) * multiplierWeight (q : ℝ) (φ p) ∂μ) ≤ 1 := by
    convert hnorm using 1
    apply lintegral_congr
    intro p
    simp only [originalSectionDensity, Nat.cast_one, toricNativeMultiplierWeight_one_scaled, htnorm]
  have hlocal : (∫⁻ y in ball z₀ R, ENNReal.ofReal (‖f y‖ ^ 2) *
      multiplierWeight (q : ℝ)
        (φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal))) ≤
        ENNReal.ofReal C := by
    exact (lintegral_mono_set ball_subset_closedBall).trans
      ((hbudget q hq φ (toricNativePhi_globalQpsh hφ).1.upperSemicontinuous.measurable t).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hglobal zero_le))
  have hf : DifferentiableOn ℂ f (ball z₀ R) := (differentiable_toricOriginalSectionCoeff _ v).differentiableOn
  have hpoint := bergmanSup_extremal hf (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top hlocal z
  have hz : z ∈ (originalPolytopeNativeModelChart γ hs v).target := by
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ z
  have hphysical := toricNativeFullSectionEquiv_symm_norm_sq B (toricNativeFullSectionEquiv B t) v
    ((originalPolytopeNativeModelChart γ hs v).map_target hz)
  simp only [LinearEquiv.symm_apply_apply, (originalPolytopeNativeModelChart γ hs v).right_inv hz] at hphysical
  have hexp : Real.exp (-B.weight v z) =
      Real.exp (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z) := by
    congr 1
    dsimp only [B, toricNativeNegativeTwistMetric, BigToricMetric.subMetric, BigToricMetric.zsmulMetric]
    simp only [Int.cast_natCast]
    ring
  calc
    ENNReal.ofReal (‖s ((originalPolytopeNativeModelChart γ hs v).symm z)‖ ^ 2) =
        ENNReal.ofReal (‖t ((originalPolytopeNativeModelChart γ hs v).symm z)‖ ^ 2) :=
      congrArg (fun x : ℝ => ENNReal.ofReal (x ^ 2)) (htnorm _).symm
    _ = ENNReal.ofReal (‖f z‖ ^ 2) * ENNReal.ofReal (Real.exp
        (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z)) := by
      rw [hphysical, hexp, ENNReal.ofReal_mul (sq_nonneg _)]
    _ ≤ _ := by
      calc
        _ ≤ (ENNReal.ofReal C * bergmanSup (ball z₀ R)
          (fun y => multiplierWeight (q : ℝ)
            (φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal))) z) *
          ENNReal.ofReal (Real.exp
            (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z)) :=
          mul_le_mul_of_nonneg_right hpoint zero_le
        _ = _ := by ac_rfl


end SGPT.Toric

end
end ToricCanonicalFragment069
/- END SGPT.Toric.ToricNativeStrictUniformLocalKernel -/

/- BEGIN SGPT.Toric.ToricNativeStrictUniformMeanUpper; source SHA256 da48be66359580c295e7dc1dbadb9d85e3e81c2c6b8c11448f2ec2c601fef2c5 -/
section ToricCanonicalFragment070

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.BergmanSupWeight
open SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeRightUnit SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Genuine arbitrary-phi local-mean-value upper estimate for the SAME
actual global physical product potential. Every error is O(1/q), with
its constant internally produced from the original raw-volume budget. -/
theorem exists_toricNativeStrictPhi_uniform_local_upper {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) (z₀ : ComplexModel n)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ hq : 0 < q,
      ∀ φ : PolytopeToricVariety γ hs → EReal,
      ∀ hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ,
      ∀ hinv : PolytopeToricInvariant γ hs φ,
      ∀ b : ℝ, (∀ y ∈ ball z₀ R,
        φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal) ≤ (b : EReal)) →
      ∀ z ∈ ball z₀ (R / 2), toricNativeStrictPhiProductPotential h q hq hφ hinv
          ((originalPolytopeNativeModelChart γ hs v).symm z) ≤
        ((b - h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C -
          Real.log (volume (ball (0 : ComplexModel n) (R / 4))).toReal) / q : ℝ) : EReal) := by
  obtain ⟨C, hC, hkernel⟩ := exists_toricNativeStrictPhi_uniform_global_le_local h v z₀ R hR
  refine ⟨C, hC, fun q hq φ hφ hinv b hb z hz => ?_⟩
  let P : ComplexModel n → EReal := fun y =>
    φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal)
  have hlog := ENNReal.log_monotone (hkernel q hq φ hφ hinv z)
  have hl : ENNReal.log (toricNativeFiniteSectionDensity h q
      (toricNativeStrictPhiProductSections h q hq hφ hinv)
      ((originalPolytopeNativeModelChart γ hs v).symm z)) ≤
      ((Real.log C + (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z) : ℝ) : EReal) +
        bergmanLog (ball z₀ R) (fun y => multiplierWeight (q : ℝ) (P y)) z := by
    simpa only [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hC,
      ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp, ← EReal.coe_add, bergmanLog] using hlog
  have hm := monotone_eReal_const_mul (c := (q : ℝ)⁻¹) (by positivity) hl
  dsimp only at hm
  rw [EReal.left_distrib_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr (show (0 : ℝ) ≤ (q : ℝ)⁻¹ by positivity)) (EReal.coe_ne_top _),
    ← EReal.coe_mul] at hm
  have hreal : (q : ℝ)⁻¹ * (Real.log C + (-(q : ℝ) * h.weight v z +
      (toricFullLatticeMetric (hs := hs)).weight v z)) =
      -h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q := by
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    ring
  rw [hreal] at hm
  have hscaled : toricNativeStrictPhiProductPotential h q hq hφ hinv
      ((originalPolytopeNativeModelChart γ hs v).symm z) ≤
      bergmanWeight (ball z₀ R) P q z +
        ((-h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q : ℝ) : EReal) := by
    simpa only [toricNativeStrictPhiProductPotential, toricNativeFiniteSectionPotential,
      bergmanWeight, EReal.coe_inv, add_comm] using hm
  have hsub : closedBall z (R / 4) ⊆ ball z₀ R := by
    intro y hy
    have hzy : dist z z₀ < R / 2 := hz
    have hyz : dist y z ≤ R / 4 := hy
    have htri := dist_triangle y z z₀
    rw [mem_ball]
    linarith
  have hlocal := bergmanWeight_le isOpen_ball (show 1 ≤ q by omega)
    (by positivity : 0 < R / 4) hsub
    (fun y hy => hb y (hsub (ball_subset_closedBall hy)))
  rw [Measure.addHaar_ball_center volume z (R / 4)] at hlocal
  calc
    _ ≤ bergmanWeight (ball z₀ R) P q z +
        ((-h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q : ℝ) : EReal) := hscaled
    _ ≤ ((b - (q : ℝ)⁻¹ * Real.log (volume (ball (0 : ComplexModel n) (R / 4))).toReal : ℝ) : EReal) +
        ((-h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q : ℝ) : EReal) :=
      add_le_add hlocal le_rfl
    _ = _ := by
      rw [← EReal.coe_add]
      congr 1
      simp only [div_eq_mul_inv]
      ring

end SGPT.Toric

end
end ToricCanonicalFragment070
/- END SGPT.Toric.ToricNativeStrictUniformMeanUpper -/

/- BEGIN SGPT.Toric.ToricNativeStrictLocalUpperEvents; source SHA256 5af23c405dae68b81d481babd860b6062c698b169c468bb57bcfebb74febee57 -/
section ToricCanonicalFragment071

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators ContDiff Manifold ENNReal
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual local Hartogs upper event for the ORIGINAL physical kernels,
produced directly from true raw-volume budgets and mean value. One real
neighborhood and threshold work for ALL sufficiently large degrees and
ALL points of that neighborhood. No L1/Hartogs/output certificate is input. -/
theorem toricNativeStrictPhiProductPotential_local_upper_event {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (p : PolytopeToricVariety γ hs)
    (b : ℝ) (hb : φ p < (b : EReal)) :
    ∃ V : Set (PolytopeToricVariety γ hs), IsOpen V ∧ p ∈ V ∧
      ∃ N : ℕ, 0 < N ∧ ∀ q : ℕ, N ≤ q → ∀ hq : 0 < q, ∀ x ∈ V,
        toricNativeStrictPhiProductPotential h q hq hφ hinv x < (b : EReal) := by
  obtain ⟨m, hmφ, hmb⟩ := EReal.exists_between_coe_real hb
  have hmbR : m < b := EReal.coe_lt_coe_iff.mp hmb
  let ε : ℝ := (b - m) / 4
  have hε : 0 < ε := div_pos (sub_pos.mpr hmbR) (by norm_num)
  let v := toricNativePreferredVertex γ hs p
  let c := originalPolytopeNativeModelChart γ hs v
  let z := c p
  have hp : p ∈ c.source := toricNativePreferredVertex_mem p
  have hzp : c.symm z = p := c.left_inv hp
  have hct : c.target = univ := originalPolytopeNativeModelChart_target γ hs v
  have hsymm : Continuous c.symm := continuousOn_univ.mp (by
    rw [← hct]
    exact c.continuousOn_symm)
  let P : ComplexModel n → EReal := fun y => φ (c.symm y) + (h.weight v y : EReal)
  have hPusc : UpperSemicontinuous P := upperSemicontinuous_eReal_add
    ((toricNativePhi_globalQpsh hφ).1.upperSemicontinuous.comp hsymm)
    (continuous_coe_real_ereal.comp (h.smooth v).continuous).upperSemicontinuous
    (fun y => hφ.ne_top (c.symm y)) (fun y => EReal.coe_ne_top (h.weight v y))
  have hPz : P z < ((m + h.weight v z : ℝ) : EReal) := by
    dsimp only [P]
    rw [hzp, EReal.coe_add]
    exact EReal.add_lt_add_right_coe hmφ _
  have hmetric : ∀ᶠ y in 𝓝 z, h.weight v z - ε < h.weight v y :=
    (h.smooth v).continuous.continuousAt.eventually (lt_mem_nhds (by linarith : h.weight v z - ε < h.weight v z))
  obtain ⟨R, hR, hRb⟩ := Metric.mem_nhds_iff.mp ((hPusc z _ hPz).and hmetric)
  obtain ⟨C, _, hupper⟩ := exists_toricNativeStrictPhi_uniform_local_upper h v z R hR
  obtain ⟨B, hB⟩ := (isCompact_closedBall z (R / 2)).exists_bound_of_continuousOn
    ((toricFullLatticeMetric (hs := hs)).smooth v).continuous.continuousOn
  let A : ℝ := B + Real.log C - Real.log (volume (ball (0 : ComplexModel n) (R / 4))).toReal
  have hbound (q : ℕ) (hq : 0 < q) {y : ComplexModel n} (hy : y ∈ ball z (R / 2)) :
      toricNativeStrictPhiProductPotential h q hq hφ hinv (c.symm y) ≤ ((m + ε + A / q : ℝ) : EReal) := by
    have hymetric := (hRb (ball_subset_ball (half_le_self hR.le) hy)).2
    have haux : (toricFullLatticeMetric (hs := hs)).weight v y ≤ B :=
      (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB y (ball_subset_closedBall hy)))
    have hh := hupper q hq φ hφ hinv (m + h.weight v z) (fun t ht => (hRb ht).1.le) y hy
    apply hh.trans
    apply EReal.coe_le_coe_iff.mpr
    apply add_le_add
    · linarith
    · apply div_le_div_of_nonneg_right
      · dsimp only [A]
        linarith
      · exact Nat.cast_nonneg q
  have hAzero : Tendsto (fun q : ℕ => A / (q : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun q : ℕ => m + ε + A / (q : ℝ)) atTop (𝓝 (m + ε)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hAzero)
  have htarget : m + ε < b := by dsimp only [ε]; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds htarget))
  let V := c.source ∩ c ⁻¹' ball z (R / 2)
  refine ⟨V, c.isOpen_inter_preimage isOpen_ball, ⟨hp, mem_ball_self (half_pos hR)⟩,
    max N 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), fun q hq hqpos x hx => ?_⟩
  have hxbound := hbound q hqpos hx.2
  rw [c.left_inv hx.1] at hxbound
  exact hxbound.trans_lt (EReal.coe_lt_coe_iff.mpr (hN q (le_of_max_le_left hq)))

end SGPT.Toric

end
end ToricCanonicalFragment071
/- END SGPT.Toric.ToricNativeStrictLocalUpperEvents -/

/- BEGIN SGPT.Toric.ToricNativeStrictCompactUpper; source SHA256 feeb3b7c3b1ab2d59813d9399646262f4e47f2514c67cbdc541f75be97718daa -/
section ToricCanonicalFragment072

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Manifold
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- True compactness and the actual original local kernel upper events
produce ONE uniform degree threshold below EVERY strict continuous real
barrier on a compact region. No uniformity/convergence certificate is input. -/
theorem toricNativeStrictPhiProductPotential_compact_upper {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    {S : Set (PolytopeToricVariety γ hs)} (hS : IsCompact S)
    (f : PolytopeToricVariety γ hs → ℝ) (hf : ContinuousOn f S)
    (hgap : ∀ p ∈ S, φ p < (f p : EReal)) :
    ∃ N : ℕ, 0 < N ∧ ∀ q : ℕ, N ≤ q → ∀ hq : 0 < q, ∀ p ∈ S,
      toricNativeStrictPhiProductPotential h q hq hφ hinv p < (f p : EReal) := by
  classical
  have hloc (p : PolytopeToricVariety γ hs) (hp : p ∈ S) :
      ∃ V : Set (PolytopeToricVariety γ hs), V ∈ 𝓝[S] p ∧
        ∃ N : ℕ, 0 < N ∧ ∀ q : ℕ, N ≤ q → ∀ hq : 0 < q, ∀ x ∈ V,
          toricNativeStrictPhiProductPotential h q hq hφ hinv x < (f x : EReal) := by
    obtain ⟨m, hφm, hmf⟩ := EReal.exists_between_coe_real (hgap p hp)
    have hmfR : m < f p := EReal.coe_lt_coe_iff.mp hmf
    obtain ⟨V, hV, hpV, N, hN, hevent⟩ :=
      toricNativeStrictPhiProductPotential_local_upper_event h hφ hinv p m hφm
    refine ⟨V ∩ {x | m < f x}, ?_, N, hN, fun q hq hqpos x hx => ?_⟩
    · have heventV : ∀ᶠ x in 𝓝[S] p, x ∈ V :=
        (show ∀ᶠ x in 𝓝 p, x ∈ V from hV.mem_nhds hpV).filter_mono nhdsWithin_le_nhds
      exact heventV.and ((hf p hp).eventually (lt_mem_nhds hmfR))
    · exact (hevent q hq hqpos x hx.1).trans (EReal.coe_lt_coe_iff.mpr hx.2)
  choose V hV N hN hbound using hloc
  obtain ⟨t, ht⟩ := hS.elim_nhdsWithin_subcover' V hV
  let M : ℕ := (∑ p ∈ t, N p.val p.property) + 1
  have hNM (p : S) (hp : p ∈ t) : N p.val p.property ≤ M := by
    have hh : N p.val p.property ≤ ∑ x ∈ t, N x.val x.property :=
      Finset.single_le_sum (f := fun x : S => N x.val x.property) (fun _ _ => Nat.zero_le _) hp
    dsimp only [M]
    omega
  refine ⟨M, by dsimp only [M]; omega, fun q hq hqpos p hp => ?_⟩
  obtain ⟨x, hxt, hpx⟩ := mem_iUnion₂.mp (ht hp)
  exact hbound x.val x.property q ((hNM x hxt).trans hq) hqpos p hpx

end SGPT.Toric

end
end ToricCanonicalFragment072
/- END SGPT.Toric.ToricNativeStrictCompactUpper -/

/- BEGIN SGPT.Toric.ToricLocalDyadicUniformBound; source SHA256 d65b4a55fd2fae5e5389ff4da04d77ed303904395830fd708ea47360d74b3942 -/
section ToricCanonicalFragment073

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
open scoped Topology ENNReal

/-- True LOCAL doubling yields one fixed-level bound for EVERY later
dyadic level. The additive constant is internally produced from the ball
and is UNIFORM in the whole input PSH weight and the dyadic exponent. -/
theorem exists_localDyadicBergman_uniform_bound {d : ℕ}
    (z : ComplexModel d) (R : ℝ) (hR : 0 < R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ P : ComplexModel d → EReal,
      PlurisubharmonicOn P (ball z R) → ∀ M : ℕ, 1 ≤ M → ∀ k : ℕ,
      ∀ y ∈ ball z R, bergmanWeight (ball z R) P (2 ^ k * M) y ≤
        bergmanWeight (ball z R) P M y + ((D / M : ℝ) : EReal) := by
  have hrad : 0 < ‖z‖ + R := by positivity
  obtain ⟨C, _, hdouble⟩ := bergmanWeight_two_mul_le d (‖z‖ + R) hrad
  let D : ℝ := max (Real.log C) 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨D, hD, fun P hP M hM k y hy => ?_⟩
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hind (j : ℕ) : bergmanWeight (ball z R) P (2 ^ j * M) y ≤
      bergmanWeight (ball z R) P M y +
        ((D / M * (1 - ((2 : ℝ) ^ j)⁻¹) : ℝ) : EReal) := by
    induction j with
    | zero => simp only [pow_zero, one_mul, inv_one, sub_self, mul_zero, EReal.coe_zero, add_zero, le_refl]
    | succ j ih =>
      have hqpos : 0 < 2 ^ j * M := Nat.mul_pos (pow_pos (by norm_num) j) hMpos
      have hqR : (0 : ℝ) < (2 ^ j * M : ℕ) := by exact_mod_cast hqpos
      have hbd : ∀ w ∈ ball z R, ‖w‖ < ‖z‖ + R := by
        intro w hw
        have hh := norm_le_norm_add_norm_sub' w z
        have hw' : ‖w - z‖ < R := by simpa only [mem_ball, dist_eq_norm] using hw
        linarith
      have hd := hdouble (ball z R) isOpen_ball (convex_ball z R) hbd P hP (2 ^ j * M) (by omega) y hy
      have he : (2 * ((2 ^ j * M : ℕ) : ℝ))⁻¹ * Real.log C ≤
          D / (2 * ((2 ^ j * M : ℕ) : ℝ)) := by
        rw [div_eq_mul_inv, mul_comm D]
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      have hnat : 2 ^ (j + 1) * M = 2 * (2 ^ j * M) := by rw [pow_succ]; ring
      have hcalc : D / M * (1 - ((2 : ℝ) ^ j)⁻¹) + D / (2 * ((2 ^ j * M : ℕ) : ℝ)) =
          D / M * (1 - ((2 : ℝ) ^ (j + 1))⁻¹) := by
        push_cast
        rw [pow_succ]
        have hMne : (M : ℝ) ≠ 0 := hMR.ne'
        have h2ne : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
        field_simp
        ring
      rw [hnat]
      calc
        _ ≤ (((2 * ((2 ^ j * M : ℕ) : ℝ))⁻¹ * Real.log C : ℝ) : EReal) +
            bergmanWeight (ball z R) P (2 ^ j * M) y := by
          simpa only [bergmanWeight,
            Pending.QuantitativeRegularizationBergmanInstanceTransport.bergmanLog_ambient_eq_borel] using hd
        _ ≤ ((D / (2 * ((2 ^ j * M : ℕ) : ℝ)) : ℝ) : EReal) +
            bergmanWeight (ball z R) P (2 ^ j * M) y := add_le_add (EReal.coe_le_coe_iff.mpr he) le_rfl
        _ = bergmanWeight (ball z R) P (2 ^ j * M) y +
            ((D / (2 * ((2 ^ j * M : ℕ) : ℝ)) : ℝ) : EReal) := add_comm _ _
        _ ≤ (bergmanWeight (ball z R) P M y + ((D / M * (1 - ((2 : ℝ) ^ j)⁻¹) : ℝ) : EReal)) +
            ((D / (2 * ((2 ^ j * M : ℕ) : ℝ)) : ℝ) : EReal) := add_le_add ih le_rfl
        _ = _ := by rw [add_assoc, ← EReal.coe_add, hcalc]
  apply (hind k).trans
  apply add_le_add le_rfl
  apply EReal.coe_le_coe_iff.mpr
  have hn : 0 ≤ ((2 : ℝ) ^ k)⁻¹ := by positivity
  have hDdiv : 0 ≤ D / (M : ℝ) := div_nonneg hD hMR.le
  nlinarith

end SGPT.Toric

end
end ToricCanonicalFragment073
/- END SGPT.Toric.ToricLocalDyadicUniformBound -/

/- BEGIN SGPT.Toric.ToricPreviousAnalyticVanishing; source SHA256 9ecc89359e1cf0f8a9241896958cc9e0ee41d7d02d998d6da0e052e0c11c8f88 -/
section ToricCanonicalFragment074

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The PREVIOUS produced analytic weight and a strict scalar comparison
internally force genuine original I-infinity vanishing of ALL new degree-M
multiplier germs. New w is arbitrary; no desired ideal inclusion is input. -/
theorem exists_toricPreviousAnalytic_degree_vanishing
    {v w : PolytopeToricVariety γ hs → EReal}
    (hv : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH v)
    (hvan : (ofFixedModel n (PolytopeToricVariety γ hs)).HasRationalAnalyticChartType v)
    {r B : ℝ} (hr : 1 < r) (hcomp : ∀ p, w p ≤ (r : EReal) * v p + (B : EReal)) :
    ∃ s : ℝ, 1 < s ∧ s < r ∧ ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      (sourceDegreeMultiplierIdeal (n := n) M w).Le
        (SGPT.PSH.inftyIdeal (n := n) (fun p => (((M : ℝ) * s : ℝ) : EReal) * v p)) := by
  let s : ℝ := (r + 1) / 2
  have hs : 1 < s := by dsimp only [s]; linarith
  have hsr : s < r := by dsimp only [s]; linarith
  have hspos : 0 < s := lt_trans zero_lt_one hs
  let η : ℝ := r / s - 1
  have hη : 0 < η := by
    dsimp only [η]
    have hh : 1 < r / s := (lt_div_iff₀ hspos).mpr (by simpa only [one_mul] using hsr)
    linarith
  obtain ⟨t₀, _, hIInf⟩ := SGPT.PSH.MultiplierIdealInf.exists_multiplierIdeal_le_inftyIdeal hvan hη
  let M₀ : ℕ := ⌈t₀ / s⌉₊ + 1
  refine ⟨s, hs, hsr, M₀, by dsimp only [M₀]; omega, fun M hM => ?_⟩
  have hMpos : 0 < M := by dsimp only [M₀] at hM; omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have ht : t₀ ≤ (M : ℝ) * s := by
    apply (div_le_iff₀ hspos).mp
    exact (Nat.le_ceil _).trans (by dsimp only [M₀] at hM; exact_mod_cast (show ⌈t₀ / s⌉₊ ≤ M by omega))
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hscaledV := toricNativePhi_globalQpsh (hv.pos_smul (mul_pos hMR hrpos))
  have hscaled : ∀ p, ((M : ℝ) : EReal) * w p ≤
      (((M : ℝ) * r : ℝ) : EReal) * v p + (((M : ℝ) * B : ℝ) : EReal) := by
    intro p
    have hh := monotone_eReal_const_mul hMR.le (hcomp p)
    dsimp only at hh
    rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hMR.le) (EReal.coe_ne_top _),
      ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul] at hh
    exact hh
  have horder := iOrderOnManifold_of_le_add hscaledV.1 hscaled
  have hI := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold horder one_pos
  have hlast := hIInf ((M : ℝ) * s) ht
  have heq : (M : ℝ) * s * (1 + η) = (M : ℝ) * r := by
    dsimp only [η]
    field_simp [hspos.ne']
    ring
  rw [heq] at hlast
  intro p f hf
  exact hlast p f (hI p f hf)

end SGPT.Toric

end
end ToricCanonicalFragment074
/- END SGPT.Toric.ToricPreviousAnalyticVanishing -/

/- BEGIN SGPT.Toric.ToricLocalMultiplierGerms; source SHA256 1af77f58b8ce6802beb1ab8a8f036b90d0db7e6e1ba027f7225170307aaefac2 -/
section ToricCanonicalFragment075

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Genuine holomorphic pullback of any local model coefficient through
an ACTUAL original vertex chart, derived from its maximal atlas geometry. -/
theorem toricLocalChartCoefficient_holomorphicAt
    (v : latticePolytopeVertices γ) {z : ComplexModel n} {R : ℝ}
    {g : ComplexModel n → ℂ} (hg : DifferentiableOn ℂ g (ball z R))
    {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hpB : originalPolytopeNativeModelChart γ hs v p ∈ ball z R) :
    HolomorphicAt n (fun x : PolytopeToricVariety γ hs => g (originalPolytopeNativeModelChart γ hs v x)) p := by
  let e := polytopeToricVertexChart γ hs v
  let U := e.val.source ∩ e.val ⁻¹' ball z R
  have hU : IsOpen U := e.val.isOpen_inter_preimage isOpen_ball
  have hmem : e.val ∈ IsManifold.maximalAtlas (𝓘(ℂ, ComplexModel n)) ∞
      (PolytopeToricVariety γ hs) :=
    IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (M := PolytopeToricVariety γ hs) e.property
  filter_upwards [hU.mem_nhds ⟨hp, hpB⟩] with x hx
  have hchart := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
    (M := PolytopeToricVariety γ hs) hmem hx.1
  have hgx : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g (e.val x) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hg.differentiableAt (isOpen_ball.mem_nhds hx.2)
  exact hgx.comp x (hchart.mdifferentiableAt (by simp))

/-- Actual corrected-weight local L2 data produce literal ORIGINAL degree
multiplier-ideal membership in the preferred stalk, through genuine
holomorphic chart and smooth-weight integral transport. -/
theorem toricLocalChartCoefficient_mem_sourceDegreeMultiplierIdeal {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (M : ℕ) (hM : 0 < M) {z : ComplexModel n} {R : ℝ}
    {g : ComplexModel n → ℂ} (hg : DifferentiableOn ℂ g (ball z R))
    (hL2 : WeightedL2On
      (fun y => φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal))
      (M : ℝ) g (ball z R) volume)
    {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source)
    (hpB : originalPolytopeNativeModelChart γ hs v p ∈ ball z R) :
    (sourceDegreeMultiplierIdeal (n := n) M φ).mem p
      (fun x => g (originalPolytopeNativeModelChart γ hs v x)) := by
  let e := polytopeToricVertexChart γ hs v
  let x := e.val p
  let P : ComplexModel n → EReal := fun y => chartFunction φ e y + (h.weight v y : EReal)
  let F : PolytopeToricVariety γ hs → ℂ := fun y => g (e.val y)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hP : MultiplierIntegrableAt P (M : ℝ) g x volume :=
    ⟨hMR, ball z R, isOpen_ball, hpB, hg, hL2⟩
  have hcomp := QuantitativeRegularizationChartGermTransfer.moreSingularAt_add_continuous
    (u := P) isOpen_univ ((h.smooth v).continuous.neg.continuousOn) (mem_univ x)
  have heq : (fun y => P y + ((-h.weight v y : ℝ) : EReal)) = chartFunction φ e := by
    funext y
    dsimp only [P]
    rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.add_sub_cancel_right]
  dsimp only [Pi.neg_apply] at hcomp
  rw [heq] at hcomp
  have hraw : MultiplierIntegrableAt (chartFunction φ e) (M : ℝ) g x volume :=
    multiplierIntegrableAt_of_moreSingularAt
      ((toricNativePhi_globalQpsh hφ).1 e x (e.val.map_source hp)) hcomp hP
  have hF : (fun y => F (e.val.symm y)) = g := by
    funext y
    have hyt : y ∈ e.val.target := by
      change y ∈ (originalPolytopeNativeModelChart γ hs v).target
      rw [originalPolytopeNativeModelChart_target]
      exact mem_univ y
    dsimp only [F]
    rw [e.val.right_inv hyt]
  have hrawF : MultiplierIntegrableAt (chartFunction φ e) (M : ℝ)
      (fun y => F (e.val.symm y)) x volume := by rwa [hF]
  let a := complexChartAt (n := n) p
  have husc : UpperSemicontinuousOn (chartFunction φ a) (ChartWeightedL2.overlapDomain a e) :=
    ((toricNativePhi_globalQpsh hφ).1 a).upperSemicontinuousOn.mono (fun _ hy => hy.1)
  have hpreferred := ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume) (g := F)
    a e (mem_complexChartAt_source p) hp husc hMR.ne' hrawF
  rw [sourceDegreeMultiplierIdeal_pos M hM]
  exact ⟨toricLocalChartCoefficient_holomorphicAt v hg hp hpB, hpreferred⟩

end SGPT.Toric

end
end ToricCanonicalFragment075
/- END SGPT.Toric.ToricLocalMultiplierGerms -/

/- BEGIN SGPT.Toric.ToricFixedLocalAnalyticBound; source SHA256 46b8713a9adf971ebee43a04612771f3a617ed7af6d42dcd965181c2c93df491 -/
section ToricCanonicalFragment076

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BergmanSupWeight
open SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology ContDiff Manifold ENNReal BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

private theorem fixedLocalBound_of_originalDegreeInfinity {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {u w : PolytopeToricVariety γ hs → EReal}
    (hw : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w)
    (M : ℕ) (hM : 0 < M) (s : ℝ)
    (hI : (sourceDegreeMultiplierIdeal (n := n) M w).Le
      (SGPT.PSH.inftyIdeal (n := n) (fun p => (((M : ℝ) * s : ℝ) : EReal) * u p)))
    (a : latticePolytopeVertices γ) (z : ComplexModel n) (R : ℝ) (hR : 0 < R) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∀ y ∈ ball z ρ,
      bergmanWeight (ball z (2 * R))
        (fun y => w ((originalPolytopeNativeModelChart γ hs a).symm y) + (h.weight a y : EReal)) M y ≤
      (s : EReal) * u ((originalPolytopeNativeModelChart γ hs a).symm y) + (C : EReal) := by
  let c := originalPolytopeNativeModelChart γ hs a
  let P : ComplexModel n → EReal := fun y => w (c.symm y) + (h.weight a y : EReal)
  have hct : c.target = univ := originalPolytopeNativeModelChart_target γ hs a
  have hsymm : Continuous c.symm := continuousOn_univ.mp (by rw [← hct]; exact c.continuousOn_symm)
  have hPusc : UpperSemicontinuous P := upperSemicontinuous_eReal_add
    ((toricNativePhi_globalQpsh hw).1.upperSemicontinuous.comp hsymm)
    (continuous_coe_real_ereal.comp (h.smooth a).continuous).upperSemicontinuous
    (fun y => hw.ne_top (c.symm y)) (fun y => EReal.coe_ne_top (h.weight a y))
  obtain ⟨B₀, _, hB₀⟩ := SGPT.PSH.GlobalL2.exists_nonneg_upper_bound (toricNativePhi_globalQpsh hw)
  obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall z (2 * R)).exists_bound_of_continuousOn (h.smooth a).continuous.continuousOn
  have hPupper (y : ComplexModel n) (hy : y ∈ ball z (2 * R)) : P y ≤ ((B₀ + B₁ : ℝ) : EReal) := by
    have hh : h.weight a y ≤ B₁ := (le_abs_self _).trans
      ((Real.norm_eq_abs _).symm.le.trans (hB₁ y (ball_subset_closedBall hy)))
    dsimp only [P]
    rw [EReal.coe_add]
    exact add_le_add (hB₀ _) (EReal.coe_le_coe_iff.mpr hh)
  let δ : ℝ := Real.exp (-((M : ℝ) * (B₀ + B₁)))
  have hδ : 0 < δ := Real.exp_pos _
  have hlow : ∀ y ∈ ball z (2 * R), ENNReal.ofReal δ ≤ multiplierWeight (M : ℝ) (P y) := by
    intro y hy
    change ENNReal.ofReal (Real.exp (-((M : ℝ) * (B₀ + B₁)))) ≤ _
    rw [← multiplierWeight_coe]
    exact multiplierWeight_antitone (Nat.cast_nonneg M) (hPupper y hy)
  have hweight : Measurable (fun y => multiplierWeight (M : ℝ) (P y)) :=
    measurable_originalMultiplierWeight hPusc.measurable (M : ℝ)
  obtain ⟨N, g, r₀, C₀, hr₀, hg, hdom⟩ :=
    QuantitativeRegularizationBergmanLogGenerators.exists_bergmanLog_le_generatorLog_add
      hR hweight.aemeasurable hδ hlow
  let p₀ : PolytopeToricVariety γ hs := c.symm z
  have hzt : z ∈ c.target := by rw [hct]; exact mem_univ z
  have hp₀ : p₀ ∈ c.source := c.map_target hzt
  have hp₀B : c p₀ ∈ ball z (2 * R) := by
    change c (c.symm z) ∈ ball z (2 * R)
    rw [c.right_inv hzt]
    exact mem_ball_self (by positivity)
  let F : Fin N → PolytopeToricVariety γ hs → ℂ := fun i p => g i (c p)
  have hFmem (i : Fin N) : (sourceDegreeMultiplierIdeal (n := n) M w).mem p₀ (F i) := by
    have hL2 : WeightedL2On P (M : ℝ) (g i) (ball z (2 * R)) volume :=
      ⟨(((hg i).1.continuousOn.aemeasurable isOpen_ball.measurableSet).norm.pow_const 2).ennreal_ofReal.mul
          hweight.aemeasurable, ((hg i).2).trans_lt ENNReal.one_lt_top⟩
    exact toricLocalChartCoefficient_mem_sourceDegreeMultiplierIdeal h a hw M hM (hg i).1 hL2 hp₀ hp₀B
  have hFInf : ∀ i, (SGPT.PSH.inftyIdeal (n := n)
      (fun p => (((M : ℝ) * s : ℝ) : EReal) * u p)).mem p₀ (F i) :=
    fun i => hI p₀ (F i) (hFmem i)
  obtain ⟨C₁, hC₁⟩ := BoundedMultiplierGeneratorWeight.exists_generatorLog_le_weight_add hFInf
  have hlogEq (y : ComplexModel n) : generatorLog F (c.symm y) = generatorLog g y := by
    have hyt : y ∈ c.target := by rw [hct]; exact mem_univ y
    simp only [generatorLog_eq_log_sum, F, c.right_inv hyt]
  have hmodel : ∀ᶠ y in 𝓝 z, generatorLog g y ≤
      (((M : ℝ) * s : ℝ) : EReal) * u (c.symm y) + (C₁ : EReal) := by
    have ht := (c.continuousAt_symm hzt).tendsto.eventually hC₁
    filter_upwards [ht] with y hy
    rwa [hlogEq] at hy
  obtain ⟨r₁, hr₁, hball⟩ := Metric.mem_nhds_iff.mp hmodel
  let ρ : ℝ := min R (min r₀ r₁)
  have hρ : 0 < ρ := lt_min hR (lt_min hr₀ hr₁)
  have hρ₀ : ρ ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hρ₁ : ρ ≤ r₁ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, (C₁ + C₀) / M, hρ, min_le_left _ _, fun y hy => ?_⟩
  have hl : bergmanLog (ball z (2 * R)) (fun y => multiplierWeight (M : ℝ) (P y)) y ≤
      (((M : ℝ) * s : ℝ) : EReal) * u (c.symm y) + ((C₁ + C₀ : ℝ) : EReal) := by
    have hh := (hdom y (ball_subset_ball hρ₀ hy)).trans
      (add_le_add (hball (ball_subset_ball hρ₁ hy)) le_rfl)
    rwa [add_assoc, ← EReal.coe_add] at hh
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hm := monotone_eReal_const_mul (c := (M : ℝ)⁻¹) (by positivity) hl
  dsimp only at hm
  rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (show (0 : ℝ) ≤ (M : ℝ)⁻¹ by positivity))
      (EReal.coe_ne_top _), ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul] at hm
  have hcoef : (M : ℝ)⁻¹ * ((M : ℝ) * s) = s := by rw [← mul_assoc, inv_mul_cancel₀ hMR.ne', one_mul]
  rw [hcoef] at hm
  simpa only [bergmanWeight, div_eq_mul_inv, mul_comm] using hm

/-- Actual previous analytic data INTERNALLY bound one genuine fixed
local Bergman degree by a STRICT multiple of the previous stage. The
finite local generators, their original ideal stalks, and the finite
additive pole bound are all produced. The new weight w is arbitrary QPSH. -/
theorem exists_toricPreviousAnalytic_localBergman_bound {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {u w : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH u)
    (huan : (ofFixedModel n (PolytopeToricVariety γ hs)).HasRationalAnalyticChartType u)
    (hw : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w)
    {r B : ℝ} (hr : 1 < r) (hcomp : ∀ p, w p ≤ (r : EReal) * u p + (B : EReal)) :
    ∃ s : ℝ, 1 < s ∧ s < r ∧ ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∀ a : latticePolytopeVertices γ, ∀ z : ComplexModel n, ∀ R : ℝ, 0 < R →
      ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∀ y ∈ ball z ρ,
        bergmanWeight (ball z (2 * R))
          (fun y => w ((originalPolytopeNativeModelChart γ hs a).symm y) + (h.weight a y : EReal)) M y ≤
        (s : EReal) * u ((originalPolytopeNativeModelChart γ hs a).symm y) + (C : EReal) := by
  obtain ⟨s, hs, hsr, M₀, hM₀, hI⟩ := exists_toricPreviousAnalytic_degree_vanishing hu huan hr hcomp
  exact ⟨s, hs, hsr, M₀, hM₀, fun M hM a z R hR =>
    fixedLocalBound_of_originalDegreeInfinity h hw M (lt_of_lt_of_le hM₀ hM) s (hI M hM) a z R hR⟩

end SGPT.Toric

end
end ToricCanonicalFragment076
/- END SGPT.Toric.ToricFixedLocalAnalyticBound -/

/- BEGIN SGPT.Toric.ToricNativeStrictLocalWeightBound; source SHA256 1628341d9d3e1912143d2e117f7644e2d71b2d4eb363f032bafdcfe02eae30cf -/
section ToricCanonicalFragment077

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.BergmanSupWeight
open SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeRightUnit SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Derived actual physical global-to-local weight inequality at EVERY
point, including poles, with one genuine fixed raw-volume norm budget.
No local comparison or replacement norm is an input. -/
theorem exists_toricNativeStrictPhi_uniform_local_weight_bound {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) (z₀ : ComplexModel n)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ hq : 0 < q,
      ∀ φ : PolytopeToricVariety γ hs → EReal,
      ∀ hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ,
      ∀ hinv : PolytopeToricInvariant γ hs φ, ∀ z : ComplexModel n,
      toricNativeStrictPhiProductPotential h q hq hφ hinv
        ((originalPolytopeNativeModelChart γ hs v).symm z) ≤
      bergmanWeight (ball z₀ R)
        (fun y => φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal)) q z +
        ((-h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q : ℝ) : EReal) := by
  obtain ⟨C, hC, hkernel⟩ := exists_toricNativeStrictPhi_uniform_global_le_local h v z₀ R hR
  refine ⟨C, hC, fun q hq φ hφ hinv z => ?_⟩
  let P : ComplexModel n → EReal := fun y =>
    φ ((originalPolytopeNativeModelChart γ hs v).symm y) + (h.weight v y : EReal)
  have hlog := ENNReal.log_monotone (hkernel q hq φ hφ hinv z)
  have hl : ENNReal.log (toricNativeFiniteSectionDensity h q
      (toricNativeStrictPhiProductSections h q hq hφ hinv)
      ((originalPolytopeNativeModelChart γ hs v).symm z)) ≤
      ((Real.log C + (-(q : ℝ) * h.weight v z + (toricFullLatticeMetric (hs := hs)).weight v z) : ℝ) : EReal) +
        bergmanLog (ball z₀ R) (fun y => multiplierWeight (q : ℝ) (P y)) z := by
    simpa only [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hC,
      ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp, ← EReal.coe_add, bergmanLog] using hlog
  have hm := monotone_eReal_const_mul (c := (q : ℝ)⁻¹) (by positivity) hl
  dsimp only at hm
  rw [EReal.left_distrib_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr (show (0 : ℝ) ≤ (q : ℝ)⁻¹ by positivity)) (EReal.coe_ne_top _),
    ← EReal.coe_mul] at hm
  have hreal : (q : ℝ)⁻¹ * (Real.log C + (-(q : ℝ) * h.weight v z +
      (toricFullLatticeMetric (hs := hs)).weight v z)) =
      -h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q := by
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp
    ring
  rw [hreal] at hm
  have hscaled : toricNativeStrictPhiProductPotential h q hq hφ hinv
      ((originalPolytopeNativeModelChart γ hs v).symm z) ≤
      bergmanWeight (ball z₀ R) P q z +
        ((-h.weight v z + ((toricFullLatticeMetric (hs := hs)).weight v z + Real.log C) / q : ℝ) : EReal) := by
    simpa only [toricNativeStrictPhiProductPotential, toricNativeFiniteSectionPotential,
      bergmanWeight, EReal.coe_inv, add_comm] using hm
  exact hscaled

end SGPT.Toric

end
end ToricCanonicalFragment077
/- END SGPT.Toric.ToricNativeStrictLocalWeightBound -/

/- BEGIN SGPT.Toric.ToricUniformPreviousAnalyticPole; source SHA256 0eb2ea311085365cb775fdcb0b87ebb64f6a6e904605221d084c436c7c1ebf56 -/
section ToricCanonicalFragment078

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BergmanWeightConvergence
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology ContDiff Manifold ENNReal BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Genuine actual global previous-analytic pole domination with ONE
constant uniform in the ENTIRE later dyadic degree sequence and all
original points. The previous analytic bound, actual local generators,
local doubling, physical norm comparisons and compact cover are produced;
no degree-uniform or global subadditivity certificate is input. -/
theorem exists_toricNativeStrict_uniform_previousAnalytic_pole_bound {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {u w : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH u)
    (huan : (ofFixedModel n (PolytopeToricVariety γ hs)).HasRationalAnalyticChartType u)
    (hwmem : w ∈ h.PSHTor) {r B : ℝ} (hr : 1 < r)
    (hcomp : ∀ p, w p ≤ (r : EReal) * u p + (B : EReal)) :
    ∃ s : ℝ, 1 < s ∧ s < r ∧ ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∃ C : ℝ, ∀ k : ℕ, ∀ hq : 0 < 2 ^ k * M, ∀ p : PolytopeToricVariety γ hs,
        toricNativeStrictPhiProductPotential h (2 ^ k * M) hq
          (show (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w from ⟨h.atlasForm, hwmem.1⟩) hwmem.2 p ≤
          (s : EReal) * u p + (C : EReal) := by
  classical
  have hw : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w := ⟨h.atlasForm, hwmem.1⟩
  have hwn := (isThetaPSH_iff_nativeThetaPotential h.atlasForm w).mp hwmem.1
  obtain ⟨s, hspos, hsr, M₀, hM₀, hfixed⟩ := exists_toricPreviousAnalytic_localBergman_bound h hu huan hw hr hcomp
  refine ⟨s, hspos, hsr, M₀, hM₀, fun M hM => ?_⟩
  have hMpos : 0 < M := lt_of_lt_of_le hM₀ hM
  have hlocal (p : PolytopeToricVariety γ hs) :
      ∃ V : Set (PolytopeToricVariety γ hs), IsOpen V ∧ p ∈ V ∧
        ∃ C : ℝ, ∀ k : ℕ, ∀ hq : 0 < 2 ^ k * M, ∀ x ∈ V,
          toricNativeStrictPhiProductPotential h (2 ^ k * M) hq hw hwmem.2 x ≤
            (s : EReal) * u x + (C : EReal) := by
    let a := toricNativePreferredVertex γ hs p
    let c := originalPolytopeNativeModelChart γ hs a
    let z := c p
    have hp : p ∈ c.source := toricNativePreferredVertex_mem p
    have hzt : z ∈ c.target := c.map_source hp
    let P : ComplexModel n → EReal := fun y => w (c.symm y) + (h.weight a y : EReal)
    obtain ⟨ρ, C₀, hρ, hρ1, hstage⟩ := hfixed M hM a z 1 one_pos
    obtain ⟨D, _, hdyadic⟩ := exists_localDyadicBergman_uniform_bound z 2 (by norm_num)
    obtain ⟨C₁, _, hglobal⟩ := exists_toricNativeStrictPhi_uniform_local_weight_bound h a z 2 (by norm_num)
    obtain ⟨Bh, hBh⟩ := (isCompact_closedBall z 1).exists_bound_of_continuousOn (h.smooth a).continuous.continuousOn
    obtain ⟨BA, hBA⟩ := (isCompact_closedBall z 1).exists_bound_of_continuousOn
      ((toricFullLatticeMetric (hs := hs)).smooth a).continuous.continuousOn
    let A : ℝ := max (BA + Real.log C₁) 0
    let C : ℝ := C₀ + D / M + Bh + A
    let V := c.source ∩ c ⁻¹' ball z ρ
    refine ⟨V, c.isOpen_inter_preimage isOpen_ball, ⟨hp, mem_ball_self hρ⟩, C, ?_⟩
    intro k hq x hx
    let y := c x
    have hy : y ∈ ball z ρ := hx.2
    have hy1 : y ∈ closedBall z 1 := ball_subset_closedBall (ball_subset_ball hρ1 hy)
    have hP : PlurisubharmonicOn P (ball z 2) :=
      (QuantitativeRegularizationChartBranch.plurisubharmonicOn_correctedWeight hwn.1
        (toricNativeVertexWeight_localPotential h a)).mono (subset_univ _)
    have hdy := hdyadic P hP M (by omega) k y (ball_subset_ball (by linarith) hy)
    have hgl := hglobal (2 ^ k * M) hq w hw hwmem.2 y
    have hst := hstage y hy
    simp only [mul_one] at hst
    have hqR : (0 : ℝ) < (2 ^ k * M : ℕ) := by exact_mod_cast hq
    have hq1 : (1 : ℝ) ≤ (2 ^ k * M : ℕ) := by exact_mod_cast (show 1 ≤ 2 ^ k * M by omega)
    have hH : -h.weight a y ≤ Bh := by
      exact (neg_le_abs _).trans ((Real.norm_eq_abs _).symm.le.trans (hBh y hy1))
    have hAux : (toricFullLatticeMetric (hs := hs)).weight a y + Real.log C₁ ≤ A := by
      have hh := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hBA y hy1))
      have hmax : BA + Real.log C₁ ≤ A := le_max_left _ _
      linarith
    have hA : 0 ≤ A := le_max_right _ _
    have hquot : ((toricFullLatticeMetric (hs := hs)).weight a y + Real.log C₁) / (2 ^ k * M : ℕ) ≤ A := by
      apply (div_le_iff₀ hqR).mpr
      exact hAux.trans (by nlinarith)
    have herr : -h.weight a y +
        ((toricFullLatticeMetric (hs := hs)).weight a y + Real.log C₁) / (2 ^ k * M : ℕ) ≤ Bh + A :=
      add_le_add hH hquot
    have hbound := hgl.trans (add_le_add hdy (EReal.coe_le_coe_iff.mpr herr))
    have hbound' := hbound.trans (add_le_add (add_le_add hst le_rfl) le_rfl)
    change toricNativeStrictPhiProductPotential h (2 ^ k * M) hq hw hwmem.2 (c.symm (c x)) ≤ _ at hbound'
    rw [c.left_inv hx.1] at hbound'
    have hconst : ((s : EReal) * u x + (C₀ : EReal) + ((D / M : ℝ) : EReal)) + ((Bh + A : ℝ) : EReal) =
        (s : EReal) * u x + (C : EReal) := by
      simp only [C, EReal.coe_add, add_assoc]
    rwa [hconst] at hbound'
  choose V hV hpV C hC using hlocal
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover V (fun p => (hV p).mem_nhds (hpV p))
  refine ⟨∑ p ∈ t, |C p|, fun k hq p => ?_⟩
  have hpCover : p ∈ ⋃ x ∈ t, V x := by rw [ht]; trivial
  obtain ⟨x, hxt, hpx⟩ := mem_iUnion₂.mp hpCover
  apply (hC x k hq p hpx).trans
  apply add_le_add le_rfl
  apply EReal.coe_le_coe_iff.mpr
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun p => |C p|) (fun _ _ => abs_nonneg _) hxt)

end SGPT.Toric

end
end ToricCanonicalFragment078
/- END SGPT.Toric.ToricUniformPreviousAnalyticPole -/

/- BEGIN SGPT.Toric.ToricPhysicalPotentialContinuity; source SHA256 c875820013ce3acccde751642f9c66eeecc6cc77b6c86959669b845bf6cb8f04 -/
section ToricCanonicalFragment079

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open scoped Topology BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual physical finite density is continuous for the original native
Hermitian topology, including the common zero set and empty family. -/
theorem continuous_toricNativeFiniteSectionDensity {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) :
    Continuous (toricNativeFiniteSectionDensity h q s) := by
  unfold toricNativeFiniteSectionDensity
  apply continuous_finsetSum
  intro j _
  exact ENNReal.continuous_ofReal.comp
    ((sectionNormMap (toricNativePlainPowerBundle h q).Fiber (s j)).continuous.pow 2)

/-- Genuine global continuity of the literal finite physical logarithm as
an EReal function. The minus-infinity locus is retained. -/
theorem continuous_toricNativeFiniteSectionPotential {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) :
    Continuous (toricNativeFiniteSectionPotential h q s) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  exact (continuous_eReal_const_mul (inv_ne_zero hqR)).comp
    (ENNReal.continuous_log.comp (continuous_toricNativeFiniteSectionDensity h q s))


end SGPT.Toric

end
end ToricCanonicalFragment079
/- END SGPT.Toric.ToricPhysicalPotentialContinuity -/

/- BEGIN SGPT.Toric.ToricGlobalPreviousStageOrder; source SHA256 0ef7f541d2106b534f2d64c146bc3174e42a88d75d2c429281b141b6dcd0ca05 -/
section ToricCanonicalFragment080

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Genuine global eventual order. Actual dyadic pole domination handles
the deep pole region; true compact local upper events handle its finite
complement. The continuity hypothesis applies to a previous physical
stage and is produced by `continuous_toricNativeFiniteSectionPotential`.
No global order or degree choice certificate is input. -/
theorem exists_toricNativeStrict_global_previousStage_order {D : ToricDivisor γ hs}
    (h : BigToricMetric D) {u w : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH u)
    (huan : (ofFixedModel n (PolytopeToricVariety γ hs)).HasRationalAnalyticChartType u)
    (hucont : Continuous u) (hwmem : w ∈ h.PSHTor)
    {r B δ : ℝ} (hr : 1 < r) (hδ : 0 < δ)
    (hcomp : ∀ p, w p ≤ (r : EReal) * u p + (B : EReal))
    (hgap : ∀ p, w p ≤ u p - (δ : EReal)) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∃ N : ℕ, 0 < N ∧ ∀ k : ℕ, N ≤ 2 ^ k * M →
      ∀ hq : 0 < 2 ^ k * M, ∀ p : PolytopeToricVariety γ hs,
        toricNativeStrictPhiProductPotential h (2 ^ k * M) hq
          (show (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w from ⟨h.atlasForm, hwmem.1⟩) hwmem.2 p ≤
          u p - ((δ / 2 : ℝ) : EReal) := by
  obtain ⟨s, hspos, _, M₀, hM₀, hpole⟩ :=
    exists_toricNativeStrict_uniform_previousAnalytic_pole_bound h hu huan hwmem hr hcomp
  refine ⟨M₀, hM₀, fun M hM => ?_⟩
  obtain ⟨C, hC⟩ := hpole M hM
  let T : ℝ := (-C - δ) / (s - 1)
  have hs1 : 0 < s - 1 := sub_pos.mpr hspos
  have hTC : (s - 1) * T + C = -δ := by
    dsimp only [T]
    field_simp
    ring
  let S : Set (PolytopeToricVariety γ hs) := {p | (T : EReal) ≤ u p}
  have hS : IsCompact S := (isClosed_Ici.preimage hucont).isCompact
  have hnotbot (p : PolytopeToricVariety γ hs) (hp : p ∈ S) : u p ≠ ⊥ :=
    ne_of_gt ((EReal.bot_lt_coe T).trans_le hp)
  let f : PolytopeToricVariety γ hs → ℝ := fun p => (u p).toReal - δ / 2
  have hf : ContinuousOn f S := by
    intro p hp
    have hc : ContinuousAt (fun x => (u x).toReal) p :=
      (EReal.tendsto_toReal (hu.ne_top p) (hnotbot p hp)).comp hucont.continuousAt
    exact (hc.sub continuousAt_const).continuousWithinAt
  have hfgap : ∀ p ∈ S, w p < (f p : EReal) := by
    intro p hp
    have heq : u p = ((u p).toReal : EReal) := (EReal.coe_toReal (hu.ne_top p) (hnotbot p hp)).symm
    apply (hgap p).trans_lt
    rw [heq, ← EReal.coe_sub]
    exact EReal.coe_lt_coe_iff.mpr (by dsimp only [f]; linarith)
  obtain ⟨N, hN, hfinite⟩ := toricNativeStrictPhiProductPotential_compact_upper h
    (show (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w from ⟨h.atlasForm, hwmem.1⟩)
    hwmem.2 hS f hf hfgap
  refine ⟨N, hN, fun k hk hq p => ?_⟩
  by_cases hp : p ∈ S
  · have hh := (hfinite (2 ^ k * M) hk hq p hp).le
    have heq : (f p : EReal) = u p - ((δ / 2 : ℝ) : EReal) := by
      dsimp only [f]
      rw [EReal.coe_sub, EReal.coe_toReal (hu.ne_top p) (hnotbot p hp)]
    rwa [heq] at hh
  · apply (hC k hq p).trans
    by_cases hubot : u p = ⊥
    · simp only [hubot, EReal.coe_mul_bot_of_pos (lt_trans zero_lt_one hspos),
        EReal.bot_add, EReal.bot_sub, le_refl]
    · have hfin : u p = ((u p).toReal : EReal) := (EReal.coe_toReal (hu.ne_top p) hubot).symm
      have hbelow : (u p).toReal < T := by
        have hh : u p < (T : EReal) := lt_of_not_ge hp
        rwa [hfin, EReal.coe_lt_coe_iff] at hh
      rw [hfin, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub]
      apply EReal.coe_le_coe_iff.mpr
      nlinarith

end SGPT.Toric

end
end ToricCanonicalFragment080
/- END SGPT.Toric.ToricGlobalPreviousStageOrder -/

/- BEGIN SGPT.Toric.ToricPhysicalPreviousStageOrder; source SHA256 d561ee79b53c72f4b12d58551cd69cf9a8ee3e525cf9193b1d7e447241ddb2bb -/
section ToricCanonicalFragment081

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open scoped Topology
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Literal physical previous-stage consumer: actual sections INTERNALLY
produce all analytic and continuity data used in the global degree choice. -/
theorem exists_toricNativeStrict_below_previousPhysical {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q₀ : ℕ) (hq₀ : 0 < q₀) {d : ℕ}
    (a : Fin d → ToricNativePlainPowerSections h q₀)
    (humem : toricNativeFiniteSectionPotential h q₀ a ∈ h.PSHTor)
    {w : PolytopeToricVariety γ hs → EReal} (hwmem : w ∈ h.PSHTor)
    {r B δ : ℝ} (hr : 1 < r) (hδ : 0 < δ)
    (hcomp : ∀ p, w p ≤ (r : EReal) * toricNativeFiniteSectionPotential h q₀ a p + (B : EReal))
    (hgap : ∀ p, w p ≤ toricNativeFiniteSectionPotential h q₀ a p - (δ : EReal)) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∃ N : ℕ, 0 < N ∧ ∀ k : ℕ, N ≤ 2 ^ k * M →
      ∀ hq : 0 < 2 ^ k * M, ∀ p : PolytopeToricVariety γ hs,
        toricNativeStrictPhiProductPotential h (2 ^ k * M) hq
          (show (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH w from ⟨h.atlasForm, hwmem.1⟩) hwmem.2 p ≤
          toricNativeFiniteSectionPotential h q₀ a p - ((δ / 2 : ℝ) : EReal) := by
  exact exists_toricNativeStrict_global_previousStage_order h
    (show (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH _ from ⟨h.atlasForm, humem.1⟩)
    (toricNativeFiniteSectionPotential_rationalAnalytic h q₀ hq₀ a)
    (continuous_toricNativeFiniteSectionPotential h q₀ hq₀ a) hwmem hr hδ hcomp hgap

end SGPT.Toric

end
end ToricCanonicalFragment081
/- END SGPT.Toric.ToricPhysicalPreviousStageOrder -/

/- BEGIN SGPT.Toric.ToricPhysicalScalarShift; source SHA256 8632090d8d4efbbd6ed451c6475163b4aca4a4781f0479951396829dd4d7ab4c -/
section ToricCanonicalFragment082

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Actual scalar multiplication in the ORIGINAL physical H0(L^q). -/
def toricNativeFiniteSectionShift {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) (b : ℝ) :
    Fin d → ToricNativePlainPowerSections h q :=
  fun j => (Real.exp ((q : ℝ) * b / 2) : ℂ) • s j

/-- Exact actual norm-square scaling; no norm is reassigned. -/
theorem toricNativeFiniteSectionShift_density {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) (b : ℝ)
    (p : PolytopeToricVariety γ hs) :
    toricNativeFiniteSectionDensity h q (toricNativeFiniteSectionShift h q s b) p =
      ENNReal.ofReal (Real.exp ((q : ℝ) * b)) * toricNativeFiniteSectionDensity h q s p := by
  have hexp : Real.exp ((q : ℝ) * b / 2) ^ 2 = Real.exp ((q : ℝ) * b) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  unfold toricNativeFiniteSectionDensity toricNativeFiniteSectionShift
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ENNReal.ofReal (‖(Real.exp ((q : ℝ) * b / 2) : ℂ) • s j p‖ ^ 2) = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), hexp, ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- Literal physical logarithmic shift equality on the WHOLE original
manifold, including common zeros. -/
theorem toricNativeFiniteSectionShift_potential {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) (b : ℝ) :
    toricNativeFiniteSectionPotential h q (toricNativeFiniteSectionShift h q s b) =
      fun p => toricNativeFiniteSectionPotential h q s p + (b : EReal) := by
  funext p
  unfold toricNativeFiniteSectionPotential
  rw [toricNativeFiniteSectionShift_density, ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  simp only [← EReal.coe_inv]
  rw [EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr (show (0 : ℝ) ≤ (q : ℝ)⁻¹ by positivity)) (EReal.coe_ne_top _),
    ← EReal.coe_mul]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [inv_mul_cancel_left₀ hqR, add_comm]

/-- Actual whole complex-torus eigenproperty survives a physical shift,
by the ORIGINAL section translation's complex linearity. -/
theorem toricNativeFiniteSectionShift_eigen {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {d : ℕ}
    (s : Fin d → ToricNativePlainPowerSections h q) (b : ℝ)
    (heigen : ∀ i : Fin d, ∃ m : Fin n → ℤ, ∀ t : Fin n → ℂˣ,
      toricNativePlainSectionTranslation h q t (s i) = (latticeCharacter m t : ℂ) • s i) :
    ∀ i : Fin d, ∃ m : Fin n → ℤ, ∀ t : Fin n → ℂˣ,
      toricNativePlainSectionTranslation h q t (toricNativeFiniteSectionShift h q s b i) =
        (latticeCharacter m t : ℂ) • toricNativeFiniteSectionShift h q s b i := by
  intro i
  obtain ⟨m, hm⟩ := heigen i
  refine ⟨m, fun t => ?_⟩
  rw [toricNativeFiniteSectionShift, map_smul, hm t, smul_comm]

end SGPT.Toric

end
end ToricCanonicalFragment082
/- END SGPT.Toric.ToricPhysicalScalarShift -/
