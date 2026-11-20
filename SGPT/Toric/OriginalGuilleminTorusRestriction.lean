import SGPT.Toric.OriginalGuilleminGlobalForm
import SGPT.Toric.NativeOriginalEdgeOrbit
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm

/-!
# The literal F0 torus restriction of the original Guillemin form

The original nonzero coordinate domain parametrizes the same original orbit.
Its actual vertex-chart representative is the literal integer Laurent map.
Full holomorphic ddC naturality identifies the native global two-form pullback
with ddC of the original finite Legendre reference composed with the original
squared logarithmic coordinates. No algebraic Chern-class claim is made.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.Convex SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators
attribute [local instance] monomialProjectiveTopology

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The true original torus domain: every original model coordinate is nonzero. -/
def originalGuilleminTorusDomain (n : ℕ) : Set (ComplexModel n) :=
  {z | originalPolytopeNativeBoundaryPolynomial n z ≠ 0}

theorem mem_originalGuilleminTorusDomain_iff (z : ComplexModel n) :
    z ∈ originalGuilleminTorusDomain n ↔
      ∀ j, originalPolytopeNativeModelEquiv n z j ≠ 0 := by
  simp [originalGuilleminTorusDomain, originalPolytopeNativeBoundaryPolynomial,
    Finset.prod_ne_zero_iff]

theorem isOpen_originalGuilleminTorusDomain (n : ℕ) :
    IsOpen (originalGuilleminTorusDomain n) :=
  (differentiable_originalPolytopeNativeBoundaryPolynomial n).continuous.isOpen_preimage _
    isOpen_compl_singleton

/-- Literal integer Laurent character of the original complex coordinates. -/
def originalGuilleminTorusCharacter (m : Fin n → ℤ) (z : ComplexModel n) : ℂ :=
  ∏ j, originalPolytopeNativeModelEquiv n z j ^ m j

/-- Every integer power, including negative powers, is analytic on the true
nonzero-coordinate domain; no positive-exponent surrogate is used. -/
theorem analyticOnNhd_originalGuilleminTorusCharacter (m : Fin n → ℤ) :
    AnalyticOnNhd ℂ (originalGuilleminTorusCharacter m) (originalGuilleminTorusDomain n) := by
  intro z hz
  apply Finset.analyticAt_fun_prod Finset.univ
  intro j _
  exact (((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt _).comp
    ((originalPolytopeNativeModelEquiv n).toContinuousLinearMap.analyticAt z)).zpow
      ((mem_originalGuilleminTorusDomain_iff z).mp hz j)

theorem originalGuilleminTorusCharacter_ne_zero (m : Fin n → ℤ)
    {z : ComplexModel n} (hz : z ∈ originalGuilleminTorusDomain n) :
    originalGuilleminTorusCharacter m z ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _
    ((mem_originalGuilleminTorusDomain_iff z).mp hz j)

/-- The actual original complex-unit coordinates, retaining their original order. -/
def originalGuilleminTorusUnits (z : originalGuilleminTorusDomain n) : Fin n → ℂˣ :=
  fun j => Units.mk0 (originalPolytopeNativeModelEquiv n z.val j)
    ((mem_originalGuilleminTorusDomain_iff z.val).mp z.property j)

theorem originalGuilleminTorusCharacter_eq_character (m : Fin n → ℤ)
    (z : originalGuilleminTorusDomain n) :
    originalGuilleminTorusCharacter m z.val =
      (latticeCharacter m (originalGuilleminTorusUnits z) : ℂ) := by
  simp [originalGuilleminTorusCharacter, latticeCharacter, originalGuilleminTorusUnits]

/-- The SAME original orbit point, in the SAME monomial projective closure. -/
def originalGuilleminTorusPoint (γ : K → Fin n → ℤ)
    (z : originalGuilleminTorusDomain n) : originalPolytopeNativeSpace γ :=
  originalPolytopeNativeOrbitMap γ (originalGuilleminTorusUnits z)

/-- The genuine original orbit is contained in EVERY genuine original vertex open. -/
theorem originalGuilleminTorusPoint_mem_chart (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : originalGuilleminTorusDomain n) :
    originalGuilleminTorusPoint γ z ∈ (originalPolytopeNativeModelChart γ hs v).source := by
  rw [originalPolytopeNativeModelChart_source]
  exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs v (originalGuilleminTorusUnits z)

/-- Actual original native vertex coordinates of the original orbit, as an
ambient Laurent function whose analytic assertions use only the true domain. -/
def originalGuilleminTorusChartMap (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : ComplexModel n) : ComplexModel n :=
  (originalPolytopeNativeModelEquiv n).symm
    (fun j => originalGuilleminTorusCharacter (originalPolytopeNativeBasis γ hs v j) z)

/-- Literal actual-chart readback, rather than a separately supplied map. -/
theorem originalGuilleminTorusPoint_chart (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : originalGuilleminTorusDomain n) :
    originalPolytopeNativeModelChart γ hs v (originalGuilleminTorusPoint γ z) =
      originalGuilleminTorusChartMap γ hs v z.val := by
  apply (originalPolytopeNativeModelEquiv n).injective
  ext j
  change originalPolytopeNativeModelEquiv n ((originalPolytopeNativeModelEquiv n).symm
      (originalPolytopeNativePiChart γ hs v (originalGuilleminTorusPoint γ z))) j = _
  rw [(originalPolytopeNativeModelEquiv n).apply_symm_apply]
  change originalPolytopeNativePiChart γ hs v
    (originalPolytopeNativeOrbitMap γ (originalGuilleminTorusUnits z)) j =
      originalGuilleminTorusCharacter (originalPolytopeNativeBasis γ hs v j) z.val
  rw [originalPolytopeNativePiChart_orbit]
  exact (originalGuilleminTorusCharacter_eq_character _ z).symm

theorem analyticOnNhd_originalGuilleminTorusChartMap (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    AnalyticOnNhd ℂ (originalGuilleminTorusChartMap γ hs v) (originalGuilleminTorusDomain n) := by
  intro z hz
  apply ((originalPolytopeNativeModelEquiv n).symm.toContinuousLinearMap.analyticAt _).comp
  apply AnalyticAt.pi
  intro j
  exact analyticOnNhd_originalGuilleminTorusCharacter (originalPolytopeNativeBasis γ hs v j) z hz

theorem originalGuilleminTorusChartMap_mem_domain (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {z : ComplexModel n} (hz : z ∈ originalGuilleminTorusDomain n) :
    originalGuilleminTorusChartMap γ hs v z ∈ originalGuilleminTorusDomain n := by
  apply (mem_originalGuilleminTorusDomain_iff _).mpr
  intro j
  change originalPolytopeNativeModelEquiv n ((originalPolytopeNativeModelEquiv n).symm _) j ≠ 0
  rw [(originalPolytopeNativeModelEquiv n).apply_symm_apply]
  exact originalGuilleminTorusCharacter_ne_zero _ hz

/-- The literal original finite Legendre reference composed with the ORIGINAL
squared logarithmic coordinate convention. Only its true torus domain is used. -/
def originalGuilleminTorusReference (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (z : ComplexModel n) : ℝ :=
  (originalCanonicalReference γ hs
    (fun j => 2 * Real.log ‖originalPolytopeNativeModelEquiv n z j‖)).toReal

/-- Finiteness is PRODUCED before realification; no infinite source value is lost. -/
theorem originalGuilleminTorusReference_coe (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (z : ComplexModel n) :
    (originalGuilleminTorusReference γ hs z : EReal) =
      originalCanonicalReference γ hs
        (fun j => 2 * Real.log ‖originalPolytopeNativeModelEquiv n z j‖) := by
  obtain ⟨v, hv⟩ := nonempty_latticePolytopeVertices γ
  have hf := originalCanonicalReference_finite γ hs ⟨v, hv⟩
    (fun j => 2 * Real.log ‖originalPolytopeNativeModelEquiv n z j‖)
  exact EReal.coe_toReal hf.2 hf.1

/-- The actual vertex correction is the genuine original integer character,
not an assumed local pluriharmonic remainder. -/
theorem originalGuilleminTorusReference_eq_weight_add_log (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {z : ComplexModel n} (hz : z ∈ originalGuilleminTorusDomain n) :
    originalGuilleminTorusReference γ hs z =
      originalGuilleminGeometricNativeWeight γ hs v (originalGuilleminTorusChartMap γ hs v z) +
        Real.log (Complex.normSq (originalGuilleminTorusCharacter v.val z)) := by
  let t : originalGuilleminTorusDomain n := ⟨z, hz⟩
  have hp := originalGuilleminTorusPoint_mem_chart γ hs v t
  have hweight : originalGuilleminGeometricNativeWeight γ hs v
      (originalGuilleminTorusChartMap γ hs v z) =
      originalGuilleminVertexPotential γ hs v (originalGuilleminTorusPoint γ t) := by
    change originalGuilleminVertexPotential γ hs v ((originalPolytopeNativeModelChart γ hs v).symm
      (originalGuilleminTorusChartMap γ hs v z)) = _
    rw [← originalGuilleminTorusPoint_chart γ hs v t,
      (originalPolytopeNativeModelChart γ hs v).left_inv hp]
  rw [hweight]
  have hval := originalGuilleminVertexPotential_orbit_eq_reference γ hs v
    (originalGuilleminTorusUnits t)
  change originalGuilleminVertexPotential γ hs v (originalGuilleminTorusPoint γ t) = _ at hval
  have hlog := latticeCharacter_log_norm_sq v.val (originalGuilleminTorusUnits t)
  rw [← Complex.sq_norm, originalGuilleminTorusCharacter_eq_character v.val t]
  rw [hval]
  rw [hlog]
  have hcoords : torusLogCoordinates (latticeTorusPoint (originalGuilleminTorusUnits t)) =
      (fun j => 2 * Real.log ‖originalPolytopeNativeModelEquiv n z j‖) := rfl
  rw [hcoords]
  simp only [originalGuilleminTorusReference, originalCanonicalPairing_apply, integerCast]
  ring

private theorem torusChartMap_contDiffOn (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContDiffOn ℂ ∞ (originalGuilleminTorusChartMap γ hs v) (originalGuilleminTorusDomain n) :=
  contDiffOn_of_differentiableOn_complex
    (fun z hz => (analyticOnNhd_originalGuilleminTorusChartMap γ hs v z hz).differentiableAt.differentiableWithinAt)
    (isOpen_originalGuilleminTorusDomain n)

private theorem torusCharacterLog_contDiffOn (m : Fin n → ℤ) :
    ContDiffOn ℝ ∞ (fun z => Real.log (Complex.normSq (originalGuilleminTorusCharacter m z)))
      (originalGuilleminTorusDomain n) := by
  have hχ : ContDiffOn ℝ ∞ (originalGuilleminTorusCharacter m) (originalGuilleminTorusDomain n) :=
    (contDiffOn_of_differentiableOn_complex
      (fun z hz => (analyticOnNhd_originalGuilleminTorusCharacter m z hz).differentiableAt.differentiableWithinAt)
      (isOpen_originalGuilleminTorusDomain n)).restrict_scalars ℝ
  have hnorm : ContDiffOn ℝ ∞ (fun z => Complex.normSq (originalGuilleminTorusCharacter m z))
      (originalGuilleminTorusDomain n) := by
    simp only [← Complex.sq_norm]
    exact (contDiff_norm_sq ℝ).comp_contDiffOn hχ
  exact hnorm.log (fun z hz => (Complex.normSq_pos.mpr
    (originalGuilleminTorusCharacter_ne_zero m hz)).ne')

/-- The actual holomorphic character has zero COMPLETE normalized ddC on its
whole true nonzero coordinate domain. -/
theorem smoothDDC_log_originalGuilleminTorusCharacter (m : Fin n → ℤ)
    {z : ComplexModel n} (hz : z ∈ originalGuilleminTorusDomain n) :
    smoothDDC (fun y => Real.log (Complex.normSq (originalGuilleminTorusCharacter m y))) z = 0 := by
  apply Pending.PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero
  · filter_upwards [(isOpen_originalGuilleminTorusDomain n).mem_nhds hz] with y hy
    exact (analyticOnNhd_originalGuilleminTorusCharacter m y hy).differentiableAt
  · exact originalGuilleminTorusCharacter_ne_zero m hz

/-- Smoothness of the LITERAL original F0 profile is produced on its complete
true torus domain by the exact geometric-weight and genuine unit-log identity. -/
theorem contDiffOn_originalGuilleminTorusReference (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContDiffOn ℝ ∞ (originalGuilleminTorusReference γ hs) (originalGuilleminTorusDomain n) := by
  have hρ : ContDiffOn ℝ ∞
      (fun y => originalGuilleminGeometricNativeWeight γ hs v (originalGuilleminTorusChartMap γ hs v y))
      (originalGuilleminTorusDomain n) :=
    (contDiff_originalGuilleminGeometricNativeWeight γ hs v).contDiffOn.comp
      ((torusChartMap_contDiffOn γ hs v).restrict_scalars ℝ) (mapsTo_univ _ _)
  exact (hρ.add (torusCharacterLog_contDiffOn v.val)).congr
    (fun z hz => originalGuilleminTorusReference_eq_weight_add_log γ hs v hz)

/-- The LITERAL original ddC(Trop*F0) is the COMPLETE actual original global
Guillemin-form pullback under its genuine Laurent orbit-chart representative. -/
theorem smoothDDC_originalGuilleminTorusReference (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    {z : ComplexModel n} (hz : z ∈ originalGuilleminTorusDomain n) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    smoothDDC (originalGuilleminTorusReference γ hs) z =
      ((originalGuilleminClosedForm γ hs).val.coeff (originalPolytopeNativeComplexChart γ hs v)
        (originalGuilleminTorusChartMap γ hs v z)).compContinuousLinearMap
          (fderiv ℝ (originalGuilleminTorusChartMap γ hs v) z) := by
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  have heq : originalGuilleminTorusReference γ hs =ᶠ[𝓝 z]
      (fun y => originalGuilleminGeometricNativeWeight γ hs v (originalGuilleminTorusChartMap γ hs v y) +
        Real.log (Complex.normSq (originalGuilleminTorusCharacter v.val y))) := by
    filter_upwards [(isOpen_originalGuilleminTorusDomain n).mem_nhds hz] with y hy
    exact originalGuilleminTorusReference_eq_weight_add_log γ hs v hy
  rw [smoothDDC_congr heq]
  have hρ : ContDiffOn ℝ ∞
      (fun y => originalGuilleminGeometricNativeWeight γ hs v (originalGuilleminTorusChartMap γ hs v y))
      (originalGuilleminTorusDomain n) :=
    (contDiff_originalGuilleminGeometricNativeWeight γ hs v).contDiffOn.comp
      ((torusChartMap_contDiffOn γ hs v).restrict_scalars ℝ) (mapsTo_univ _ _)
  rw [smoothDDC_add (isOpen_originalGuilleminTorusDomain n) hρ
    (torusCharacterLog_contDiffOn v.val) hz, smoothDDC_log_originalGuilleminTorusCharacter v.val hz,
    add_zero, originalGuilleminClosedForm_native_coeff]
  exact HolomorphicDDC.smoothDDC_comp (isOpen_originalGuilleminTorusDomain n) isOpen_univ
    (torusChartMap_contDiffOn γ hs v)
    (contDiff_originalGuilleminGeometricNativeWeight γ hs v).contDiffOn (mapsTo_univ _ _) hz

/-- The full two-tensor restriction reads the SAME original orbit point in the
SAME actual native chart, for every true original torus parameter. -/
theorem originalGuilleminClosedForm_torus_restriction (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (z : originalGuilleminTorusDomain n) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    smoothDDC (originalGuilleminTorusReference γ hs) z.val =
      ((originalGuilleminClosedForm γ hs).val.coeff (originalPolytopeNativeComplexChart γ hs v)
        (originalPolytopeNativeModelChart γ hs v (originalGuilleminTorusPoint γ z))).compContinuousLinearMap
          (fderiv ℝ (originalGuilleminTorusChartMap γ hs v) z.val) := by
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  rw [originalGuilleminTorusPoint_chart]
  exact smoothDDC_originalGuilleminTorusReference γ hs v z.property

end SGPT.Toric
