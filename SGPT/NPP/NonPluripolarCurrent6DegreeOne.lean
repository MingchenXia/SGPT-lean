import SGPT.NPP.RieszPlanar

/-!
# The degree-one non-pluripolar product in every dimension

Source: `chapter_npp.tex`, `ex:1Dnpp`: for `φ ∈ PSH(X)`,
`(dd^c φ)^1 = 1_{φ > -∞} dd^c φ` (`eq:1dimnpp`), the left-hand side the non-pluripolar product
(`def:npp:L69`) and the right-hand side the restriction of the distributional current `dd^c φ`.
The inequality `≤` is S29's (`NonPluripolarCurrent3DegreeOne`), the dimension-one case is S45's
(`RieszPlanar`); here the identity is proved **in every dimension**
(`DegreeOne.nonPluripolarProduct_eq_indicator_ddcL1`, and in every chart of a complex manifold
`nonPluripolarProduct_inChart_eq_indicator_ddcCurrent`).

## Route (blueprint `claude-npp-cur6:fibre-disintegration`, `claude-npp-cur6:degree-one`)

The source reduces to the planar case "by the dominated convergence theorem"; we follow Xia,
*Foundations of pluripotential theory*, `prop:nonpluripolar-degree-one-restriction`
("Several variables", the fibre disintegration `eq:hessian-fibre-disintegration`), organised so
that no general monotone class argument and no Bedford–Taylor fibre product is needed:

* **Lines.**  For each coordinate direction `j`, `lineChart j : ℂᵐ × ℂ¹ ≃ ℂ^{m+1}` (the product
  splitting followed by the swap of the coordinates `j` and `m+1`) preserves Lebesgue measure; the
  lines `ι_z = lineChart j (z, ·)` have direction `e_j`, and `L(φ ∘ ι_z)(e₀) = L(φ)(e_j) ∘ ι_z` for
  the Levi form `L` (`leviForm_comp_lineMap`).
* **Trace formula.**  `∫ φ dσ_{dd^c w} = (m!/π) ∑_j ∫ L φ(e_j) w dλ` for the trace measure of
  `dd^c w`, `w` psh in `L¹_loc` (`integral_traceMeasure_ddcL1`, TN's Kähler trace pairing).
* **Fubini for test functions.**  Almost every fibre `w ∘ ι_z` is psh in `L¹_loc`
  (`ae_isL1PshOn_fibre`); with `μ^j_z` the trace measure of its planar current `dd^c(w ∘ ι_z)`
  (`fibreMeasure`), `∫ L φ(e_j) w dλ = π ∫ (∫ φ ∘ ι_z dμ^j_z) dz` (`fubini_testFunction`).
* **Bounded Borel weights.**  The identity `∫ g dσ_{dd^c w} = m! ∑_j ∫∫ g ∘ ι_z dμ^j_z dz`
  (`FibreIdentity`) passes to dominated pointwise limits (`FibreIdentity.of_tendsto`), hence from
  test functions to `φ 1_A`, `A` closed (smooth functions equal to `1` exactly on `A`, raised to
  powers), and to `φ 1_{⋃ A_i}` for increasing closed `A_i`; the strict locus `O_k = {u > -k}` is
  such a union (`levelSet`).
* **Comparison.**  On every good fibre the planar identity gives
  `1_{O_k} dd^c(u ∘ ι_z) = 1_{O_k} dd^c max(u ∘ ι_z, -k)`
  (`traceMeasure_restrict_strictLocus_planar`),
  so `1_{O_k} σ_{dd^c u} = 1_{O_k} σ_{dd^c max(u,-k)}` (`integral_mul_indicator_strictLocus_eq`).
  Since `dd^c u - 1_{O_k} dd^c max(u,-k)` is positive (S29), `1_{O_k}(dd^c u - dd^c max(u,-k))` is
  a positive current with vanishing trace, hence zero: `1_{O_k} dd^c u = 1_{O_k} dd^c max(u,-k)`
  (`mulBorel_ddcL1_strictLocus`), and the uniqueness of the non-pluripolar product
  (`eq_nonPluripolarProduct_of_mulBorel`) gives `(dd^c u)^1 = 1_{u > -∞} dd^c u`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions ContDiff Manifold

namespace SGPT.NPP.DegreeOne

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending

variable {m : ℕ}

/-! ### Lines in the coordinate directions -/

/-- The swap of the coordinates `j` and `m + 1` of `ℂ^{m+1}`, a unitary map. -/
def swapIso (j : Fin (m + 1)) : ComplexModel (m + 1) ≃ₗᵢ[ℂ] ComplexModel (m + 1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap j (Fin.last m))

/-- **The line chart in direction `j`**: `ℂᵐ × ℂ¹ ≃ ℂ^{m+1}`, `(z, x) ↦` the point with coordinate
`x₀` in slot `j` and the coordinates of `z` in the other slots. -/
def lineChart (j : Fin (m + 1)) : (ComplexModel m × ComplexModel 1) ≃L[ℂ] ComplexModel (m + 1) :=
  (ProductComplexManifold.prodModelEquiv m 1).trans (swapIso j).toContinuousLinearEquiv

/-- The fibre coordinate of `ℂᵐ × ℂ¹ ≃ ℂ^{m+1}` is the last coordinate. -/
theorem prodModelEquiv_zero_left (x : ComplexModel 1) :
    ProductComplexManifold.prodModelEquiv m 1 (0, x) = x 0 • coordinateVector (Fin.last m) := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [ProductComplexManifold.prodModelEquiv, coordinateVector]
  · simp [ProductComplexManifold.prodModelEquiv, coordinateVector]

/-- The swap sends `e_{m+1}` to `e_j`. -/
theorem swapIso_coordinateVector_last (j : Fin (m + 1)) :
    swapIso j (coordinateVector (Fin.last m)) = coordinateVector j := by
  simp [swapIso, coordinateVector]

/-- The lines of `lineChart j` have direction `e_j`. -/
theorem lineChart_zero_left (j : Fin (m + 1)) (x : ComplexModel 1) :
    lineChart j (0, x) = x 0 • coordinateVector j := by
  simp [lineChart, prodModelEquiv_zero_left, swapIso_coordinateVector_last]

/-- `lineChart j (z, x) = lineChart j (z, 0) + x₀ e_j`. -/
theorem lineChart_apply_eq_add (j : Fin (m + 1)) (z : ComplexModel m) (x : ComplexModel 1) :
    lineChart j (z, x) = lineChart j (z, 0) + x 0 • coordinateVector j := by
  rw [← lineChart_zero_left, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

/-- The line chart preserves Lebesgue measure. -/
theorem measurePreserving_lineChart (j : Fin (m + 1)) :
    MeasurePreserving (lineChart j) (volume.prod volume) volume :=
  ((swapIso j).toIsometryEquiv.toRealLinearIsometryEquivOfMapZero
    (map_zero (swapIso j))).measurePreserving.comp
    (ProductMixedMeasure.measurePreserving_prodModelEquiv m 1)

/-- The real-linear direction map `x ↦ x₀ e_j` of the lines of the chart `lineChart j`. -/
def lineDir (j : Fin (m + 1)) : ComplexModel 1 →L[ℝ] ComplexModel (m + 1) :=
  (((lineChart j : (ComplexModel m × ComplexModel 1) →L[ℂ] ComplexModel (m + 1)).comp
    (ContinuousLinearMap.inr ℂ (ComplexModel m) (ComplexModel 1)))).restrictScalars ℝ

/-- `lineDir j x = x₀ e_j`. -/
theorem lineDir_apply (j : Fin (m + 1)) (x : ComplexModel 1) :
    lineDir j x = x 0 • coordinateVector j := by
  simp [lineDir, lineChart_zero_left]

/-- `lineDir j` is complex linear. -/
theorem lineDir_smul_I (j : Fin (m + 1)) (x : ComplexModel 1) :
    lineDir j (Complex.I • x) = Complex.I • lineDir j x := by
  simp [lineDir]

/-- `lineDir j e₀ = e_j`. -/
theorem lineDir_coordinateVector (j : Fin (m + 1)) :
    lineDir j (coordinateVector 0) = coordinateVector j := by
  rw [lineDir_apply]
  simp [coordinateVector]

/-- The complex line `x ↦ Φ_j(z, x)` through the base point `z`. -/
def lineMap (j : Fin (m + 1)) (z : ComplexModel m) (x : ComplexModel 1) : ComplexModel (m + 1) :=
  lineChart j (z, x)

/-- The line through `z` is affine. -/
theorem lineMap_eq (j : Fin (m + 1)) (z : ComplexModel m) (x : ComplexModel 1) :
    lineMap j z x = lineChart j (z, 0) + lineDir j x := by
  rw [lineMap, lineChart_apply_eq_add, lineDir_apply]

/-- The lines are continuous. -/
theorem continuous_lineMap (j : Fin (m + 1)) (z : ComplexModel m) : Continuous (lineMap j z) :=
  (lineChart j).continuous.comp (continuous_const.prodMk continuous_id)

/-- The lines are smooth. -/
theorem contDiff_lineMap (j : Fin (m + 1)) (z : ComplexModel m) :
    ContDiff ℝ ∞ (lineMap j z) := by
  have e : lineMap j z = fun x => lineChart j (z, 0) + lineDir j x := funext (lineMap_eq j z)
  rw [e]
  exact contDiff_const.add (lineDir j).contDiff

/-- The lines are holomorphic. -/
theorem differentiableOn_lineMap (j : Fin (m + 1)) (z : ComplexModel m) (s : Set (ComplexModel 1)) :
    DifferentiableOn ℂ (lineMap j z) s :=
  (((lineChart j : (ComplexModel m × ComplexModel 1) →L[ℂ] ComplexModel (m + 1)).differentiable.comp
    ((differentiable_const z).prodMk differentiable_id))).differentiableOn

/-- `lineDir j` is an isometry. -/
theorem norm_lineDir (j : Fin (m + 1)) (x : ComplexModel 1) : ‖lineDir j x‖ = ‖x‖ := by
  rw [lineDir_apply, norm_smul]
  simp [coordinateVector, EuclideanSpace.norm_eq]

/-- **Levi form along a line**: `L_x(φ ∘ ι_z)(e₀) = L(φ)(ι_z x)(e_j)`. -/
theorem leviForm_comp_lineMap {φ : ComplexModel (m + 1) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (j : Fin (m + 1)) (z : ComplexModel m) (x : ComplexModel 1) :
    leviForm (fun y => φ (lineMap j z y)) x (coordinateVector 0) =
      leviForm φ (lineMap j z x) (coordinateVector j) := by
  have e : (fun y => φ (lineMap j z y)) = fun y => φ (lineChart j (z, 0) + lineDir j y) :=
    funext fun y => by rw [lineMap_eq]
  rw [e, leviForm, realHessian_comp_affine hφ, realHessian_comp_affine hφ, ← lineMap_eq,
    lineDir_smul_I, lineDir_coordinateVector, leviForm]

variable (U : Opens (ComplexModel (m + 1)))

/-- The fibre `{x : ι_z x ∈ U}` of `U` over `z` along the direction `j`. -/
def fibreOpens (j : Fin (m + 1)) (z : ComplexModel m) : Opens (ComplexModel 1) :=
  ⟨lineMap j z ⁻¹' U, U.isOpen.preimage (continuous_lineMap j z)⟩

/-- Membership in a fibre. -/
theorem mem_fibreOpens {j : Fin (m + 1)} {z : ComplexModel m} {x : ComplexModel 1} :
    x ∈ fibreOpens U j z ↔ lineMap j z x ∈ U := Iff.rfl

variable {U}

/-- The fibres of a compact set are compact. -/
theorem isCompact_preimage_lineMap {K : Set (ComplexModel (m + 1))} (hK : IsCompact K)
    (j : Fin (m + 1)) (z : ComplexModel m) : IsCompact (lineMap j z ⁻¹' K) := by
  refine Metric.isCompact_of_isClosed_isBounded (hK.isClosed.preimage (continuous_lineMap j z)) ?_
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine (Metric.isBounded_closedBall (x := (0 : ComplexModel 1))
    (r := R + ‖lineChart j (z, 0)‖)).subset
    fun x hx => ?_
  have h1 := hR hx
  rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
  rw [lineMap_eq] at h1
  rw [← norm_lineDir j x]
  have h3 := norm_sub_le (lineChart j (z, 0) + lineDir j x) (lineChart j (z, 0))
  rw [add_sub_cancel_left] at h3
  linarith

/-- The restriction of a test function to a fibre. -/
def fibreTest (φ : 𝓓(U, ℝ)) (j : Fin (m + 1)) (z : ComplexModel m) : 𝓓(fibreOpens U j z, ℝ) where
  toFun x := φ (lineMap j z x)
  contDiff' := φ.contDiff.comp (contDiff_lineMap j z)
  hasCompactSupport' := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_preimage_lineMap φ.hasCompactSupport j z) fun x hx => ?_
    exact subset_tsupport _ hx
  tsupport_subset' := by
    refine (closure_minimal (fun x hx => ?_) ((isClosed_tsupport φ).preimage
      (continuous_lineMap j z))).trans fun x hx => ?_
    · exact subset_tsupport _ hx
    · exact φ.tsupport_subset hx

@[simp] theorem fibreTest_apply (φ : 𝓓(U, ℝ)) (j : Fin (m + 1)) (z : ComplexModel m)
    (x : ComplexModel 1) : fibreTest φ j z x = φ (lineMap j z x) := rfl


open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc
open SGPT.Foundations.Analysis.Pending.XiaoPoissonLeviPositivity

/-! ### The trace formula and the fibre measures -/

/-- **The trace formula**: `∫ φ dσ_{dd^c w} = (m!/π) ∑_j ∫ L φ(e_j) w dλ`, `L` the Levi form. -/
theorem integral_traceMeasure_ddcL1 {U : Opens (ComplexModel (m + 1))}
    {w : ComplexModel (m + 1) → EReal} (hw : IsL1PshOn U w) (φ : 𝓓(U, ℝ)) :
    ∫ y, φ y ∂hw.isPositive_ddcL1.traceMeasure =
      (m.factorial : ℝ) / Real.pi *
        ∑ j, ∫ y, leviForm φ y (coordinateVector j) * (w y).toReal := by
  rw [hw.isPositive_ddcL1.integral_traceMeasure, ddcL1,
    SGPT.Currents.l1Current_eq_scalarTopCurrent hw.locallyIntegrableOn,
    ActualScalarCurrentKahlerTracePairing.ddc_scalarTopCurrent_kahlerPower_eq_sum_levi]
  simp only [distributionalLeviCLM_eq_testLevi, regularDistribution_apply, testLeviCLM_apply]


/-- The fibre `x ↦ w(ι_z x)` of a function along the line through `z` in direction `j`. -/
def fibreFun (w : ComplexModel (m + 1) → EReal) (j : Fin (m + 1)) (z : ComplexModel m) :
    ComplexModel 1 → EReal := fun x => w (lineMap j z x)

variable (U) in
/-- **The fibre measures** `μ_z = dd^c_x w(ι_z x)` (the trace measure of the planar current
`dd^c` of the fibre), for the fibres on which `w` is a psh function in `L¹_loc`; `0` otherwise. -/
def fibreMeasure (w : ComplexModel (m + 1) → EReal) (j : Fin (m + 1)) (z : ComplexModel m) :
    Measure (ComplexModel 1) :=
  by classical exact if h : IsL1PshOn (fibreOpens U j z) (fibreFun w j z) then
    h.isPositive_ddcL1.traceMeasure else 0

/-- The fibre measure on a good fibre. -/
theorem fibreMeasure_of_isL1PshOn {w : ComplexModel (m + 1) → EReal} {j : Fin (m + 1)}
    {z : ComplexModel m} (h : IsL1PshOn (fibreOpens U j z) (fibreFun w j z)) :
    fibreMeasure U w j z = h.isPositive_ddcL1.traceMeasure := by
  classical
  unfold fibreMeasure
  rw [dif_pos h]

/-- The fibre measure on a bad fibre. -/
theorem fibreMeasure_of_not {w : ComplexModel (m + 1) → EReal} {j : Fin (m + 1)}
    {z : ComplexModel m} (h : ¬ IsL1PshOn (fibreOpens U j z) (fibreFun w j z)) :
    fibreMeasure U w j z = 0 := by
  classical
  unfold fibreMeasure
  rw [dif_neg h]

/-- The planar trace formula: `∫ ψ dμ = (1/π) ∫ L ψ(e₀) v dλ`. -/
theorem integral_traceMeasure_ddcL1_planar {V : Opens (ComplexModel 1)}
    {v : ComplexModel 1 → EReal} (hv : IsL1PshOn V v) (ψ : 𝓓(V, ℝ)) :
    ∫ x, ψ x ∂hv.isPositive_ddcL1.traceMeasure =
      Real.pi⁻¹ * ∫ x, leviForm ψ x (coordinateVector 0) * (v x).toReal := by
  rw [integral_traceMeasure_ddcL1 (m := 0) hv ψ]
  simp

/-- The fibres of a psh function are psh. -/
theorem plurisubharmonicOn_fibreFun {w : ComplexModel (m + 1) → EReal}
    (hw : PlurisubharmonicOn w U) (j : Fin (m + 1)) (z : ComplexModel m) :
    PlurisubharmonicOn (fibreFun w j z) (fibreOpens U j z) :=
  HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (F := lineMap j z)
    (fibreOpens U j z).isOpen
    (differentiableOn_lineMap j z _) (fun _ hx => hx) hw

/-- **Almost every fibre of a psh function in `L¹_loc` is a psh function in `L¹_loc`.** -/
theorem ae_isL1PshOn_fibre {w : ComplexModel (m + 1) → EReal} (hw : IsL1PshOn U w)
    (j : Fin (m + 1)) :
    ∀ᵐ z ∂(volume : Measure (ComplexModel m)), IsL1PshOn (fibreOpens U j z) (fibreFun w j z) := by
  have h1 : ∀ᵐ y ∂(volume : Measure (ComplexModel (m + 1))), y ∈ U → w y ≠ ⊥ :=
    (ae_restrict_iff' U.isOpen.measurableSet).mp hw.ae_ne_bot
  have h2 := (measurePreserving_lineChart j).quasiMeasurePreserving.ae h1
  have h3 := Measure.ae_ae_of_ae_prod h2
  filter_upwards [h3] with z hz
  refine ⟨plurisubharmonicOn_fibreFun hw.psh j z, fun x hx => ?_⟩
  rw [Filter.frequently_iff]
  intro N hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hN
    ((fibreOpens U j z).isOpen.mem_nhds hx))
  have hae : ∀ᵐ y ∂(volume.restrict (Metric.ball x ε)), fibreFun w j z y ≠ ⊥ := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hz] with y hy hyb
    exact hy (hball hyb).2
  obtain ⟨y, hy, hyne⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (Metric.measure_ball_pos volume x hε).ne' hae
  exact ⟨y, (hball hy).1, hyne⟩


/-- **Fubini along the lines of direction `j` for test functions**: for `w` psh in `L¹_loc(U)`
and a test function `φ`, `z ↦ ∫ φ(ι_z x) dμ_z(x)` is integrable and
`∫ L φ(e_j) w dλ = π ∫ (∫ φ(ι_z x) dμ_z(x)) dz`. -/
theorem fubini_testFunction {w : ComplexModel (m + 1) → EReal} (hw : IsL1PshOn U w)
    (j : Fin (m + 1)) (φ : 𝓓(U, ℝ)) :
    Integrable (fun z => ∫ x, φ (lineMap j z x) ∂fibreMeasure U w j z) ∧
      ∫ y, leviForm φ y (coordinateVector j) * (w y).toReal =
        Real.pi * ∫ z, ∫ x, φ (lineMap j z x) ∂fibreMeasure U w j z := by
  set F : ComplexModel (m + 1) → ℝ := fun y => leviForm φ y (coordinateVector j) * (w y).toReal
    with hFdef
  have hF : Integrable F := by
    have h := integrable_testFunction_mul hw.locallyIntegrableOn
      (testLeviCLM (coordinateVector j) φ)
    simpa only [testLeviCLM_apply] using h
  have hmp := measurePreserving_lineChart j
  have hemb : MeasurableEmbedding (lineChart j) := (lineChart j).toHomeomorph.measurableEmbedding
  have hint : Integrable (F ∘ lineChart j) (volume.prod volume) :=
    (hmp.integrable_comp_emb hemb).2 hF
  have hI : ∫ y, F y = ∫ z, ∫ x, F (lineChart j (z, x)) := by
    rw [← hmp.integral_comp hemb F]
    exact integral_prod _ hint
  have hfib : ∀ᵐ z ∂(volume : Measure (ComplexModel m)), ∫ x, F (lineChart j (z, x)) =
      Real.pi * ∫ x, φ (lineMap j z x) ∂fibreMeasure U w j z := by
    filter_upwards [ae_isL1PshOn_fibre hw j] with z hz
    rw [fibreMeasure_of_isL1PshOn hz]
    have h := integral_traceMeasure_ddcL1_planar hz (fibreTest φ j z)
    simp only [fibreTest_apply] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hFdef, fibreFun]
    have e := leviForm_comp_lineMap (φ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) j z x
    rw [lineMap] at e
    rw [← e]
    rfl
  refine ⟨?_, ?_⟩
  · refine (hint.integral_prod_left.const_mul Real.pi⁻¹).congr ?_
    filter_upwards [hfib] with z hz
    simp only [Function.comp_apply]
    rw [hz, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  · rw [hI, integral_congr_ae hfib, integral_const_mul]


/-! ### The fibre identity for bounded Borel weights -/

/-- **The fibre identity** for a weight `g`: for every direction `j`, `z ↦ ∫ g(ι_z x) dμ^j_z(x)` is
integrable, and `∫ g dσ_{dd^c w} = m! ∑_j ∫ (∫ g(ι_z x) dμ^j_z(x)) dz`, `σ_{dd^c w}` the trace
measure of `dd^c w`. -/
def FibreIdentity {w : ComplexModel (m + 1) → EReal} (hw : IsL1PshOn U w)
    (g : ComplexModel (m + 1) → ℝ) : Prop :=
  (∀ j, Integrable (fun z => ∫ x, g (lineMap j z x) ∂fibreMeasure U w j z)) ∧
    ∫ y, g y ∂hw.isPositive_ddcL1.traceMeasure =
      (m.factorial : ℝ) * ∑ j, ∫ z, ∫ x, g (lineMap j z x) ∂fibreMeasure U w j z

variable {w : ComplexModel (m + 1) → EReal}

/-- The fibre identity for test functions. -/
theorem fibreIdentity_testFunction (hw : IsL1PshOn U w) (φ : 𝓓(U, ℝ)) : FibreIdentity hw φ := by
  refine ⟨fun j => (fubini_testFunction hw j φ).1, ?_⟩
  rw [integral_traceMeasure_ddcL1 hw φ, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(fubini_testFunction hw j φ).2]
  field_simp

/-- Test functions are integrable for the fibre measures. -/
theorem integrable_fibreMeasure_testFunction (j : Fin (m + 1)) (z : ComplexModel m)
    (φ : 𝓓(U, ℝ)) : Integrable (fun x => φ (lineMap j z x)) (fibreMeasure U w j z) := by
  classical
  by_cases hz : IsL1PshOn (fibreOpens U j z) (fibreFun w j z)
  · rw [fibreMeasure_of_isL1PshOn hz]
    have h := hz.isPositive_ddcL1.integrable_mul_of_bounded (fibreTest φ j z).continuous
      (fibreTest φ j z).hasCompactSupport (fibreTest φ j z).tsupport_subset
      (w := fun _ => (1 : ℝ)) aestronglyMeasurable_const ⟨1, fun _ _ => by simp⟩
    simpa using h
  · rw [fibreMeasure_of_not hz]
    exact integrable_zero_measure

/-- **Closure of the fibre identity under dominated pointwise limits.** -/
theorem FibreIdentity.of_tendsto (hw : IsL1PshOn U w) {g : ℕ → ComplexModel (m + 1) → ℝ}
    {G : ComplexModel (m + 1) → ℝ} (hg : ∀ l, FibreIdentity hw (g l))
    (hgm : ∀ l, Measurable (g l)) (χ : 𝓓(U, ℝ)) {C : ℝ}
    (hbd : ∀ l y, |g l y| ≤ C * χ y) (hlim : ∀ y, Tendsto (fun l => g l y) atTop (𝓝 (G y))) :
    FibreIdentity hw G := by
  set σ := hw.isPositive_ddcL1.traceMeasure
  have hGm : Measurable G := measurable_of_tendsto_metrizable hgm (tendsto_pi_nhds.mpr hlim)
  -- the ambient side
  have hχσ : Integrable (fun y => C * χ y) σ := by
    have h := hw.isPositive_ddcL1.integrable_mul_of_bounded χ.continuous χ.hasCompactSupport
      χ.tsupport_subset (w := fun _ => C) aestronglyMeasurable_const ⟨|C|, fun _ _ => le_rfl⟩
    simpa only [mul_comm] using h
  have hamb : Tendsto (fun l => ∫ y, g l y ∂σ) atTop (𝓝 (∫ y, G y ∂σ)) :=
    tendsto_integral_of_dominated_convergence (fun y => C * χ y)
      (fun l => (hgm l).aestronglyMeasurable) hχσ
      (fun l => Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hbd l y)
      (Eventually.of_forall hlim)
  -- the fibre side, direction by direction
  have hfib : ∀ j, Integrable (fun z => ∫ x, G (lineMap j z x) ∂fibreMeasure U w j z) ∧
      Tendsto (fun l => ∫ z, ∫ x, g l (lineMap j z x) ∂fibreMeasure U w j z) atTop
        (𝓝 (∫ z, ∫ x, G (lineMap j z x) ∂fibreMeasure U w j z)) := by
    intro j
    set B : ComplexModel m → ℝ := fun z => C * ∫ x, χ (lineMap j z x) ∂fibreMeasure U w j z
    have hB : Integrable B := ((fubini_testFunction hw j χ).1).const_mul C
    have hle : ∀ l z, ‖∫ x, g l (lineMap j z x) ∂fibreMeasure U w j z‖ ≤ B z := by
      intro l z
      refine (norm_integral_le_of_norm_le ((integrable_fibreMeasure_testFunction j z χ).const_mul C)
        (Eventually.of_forall fun x => ?_)).trans_eq (integral_const_mul C _)
      rw [Real.norm_eq_abs]
      exact hbd l _
    have hconv : ∀ z, Tendsto (fun l => ∫ x, g l (lineMap j z x) ∂fibreMeasure U w j z) atTop
        (𝓝 (∫ x, G (lineMap j z x) ∂fibreMeasure U w j z)) := fun z =>
      tendsto_integral_of_dominated_convergence (fun x => C * χ (lineMap j z x))
        (fun l => ((hgm l).comp (continuous_lineMap j z).measurable).aestronglyMeasurable)
        ((integrable_fibreMeasure_testFunction j z χ).const_mul C)
        (fun l => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbd l _)
        (Eventually.of_forall fun x => hlim _)
    have hmeas : AEStronglyMeasurable (fun z => ∫ x, G (lineMap j z x) ∂fibreMeasure U w j z)
        volume :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun l => ((hg l).1 j).aestronglyMeasurable)
        (Eventually.of_forall hconv)
    refine ⟨hB.mono' hmeas (Eventually.of_forall fun z =>
      le_of_tendsto (hconv z).norm (Eventually.of_forall fun l => hle l z)), ?_⟩
    exact tendsto_integral_of_dominated_convergence B (fun l => ((hg l).1 j).aestronglyMeasurable)
      hB (fun l => Eventually.of_forall (hle l)) (Eventually.of_forall hconv)
  refine ⟨fun j => (hfib j).1, ?_⟩
  have hsum : Tendsto (fun l => (m.factorial : ℝ) *
      ∑ j, ∫ z, ∫ x, g l (lineMap j z x) ∂fibreMeasure U w j z) atTop
      (𝓝 ((m.factorial : ℝ) * ∑ j, ∫ z, ∫ x, G (lineMap j z x) ∂fibreMeasure U w j z)) :=
    (tendsto_finsetSum _ fun j _ => (hfib j).2).const_mul _
  refine tendsto_nhds_unique hamb ?_
  exact hsum.congr fun l => ((hg l).2).symm


/-- A smooth `f : ℂ^{m+1} → [0,1]` equal to `1` exactly on a given closed set. -/
theorem exists_contDiff_eq_one_iff {A : Set (ComplexModel (m + 1))} (hA : IsClosed A) :
    ∃ f : ComplexModel (m + 1) → ℝ, ContDiff ℝ ∞ f ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
      ∀ y, y ∈ A ↔ f y = 1 := by
  obtain ⟨f, hf, hr, -, h1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (𝓘(ℝ, ComplexModel (m + 1))) (n := ⊤) isClosed_empty hA (empty_disjoint _)
  exact ⟨f, contMDiff_iff_contDiff.mp hf, fun y => hr ⟨y, rfl⟩, h1⟩

/-- A test function is bounded by a multiple of a nonnegative test function. -/
theorem exists_abs_le_mul_testFunction (φ : 𝓓(U, ℝ)) :
    ∃ χ : 𝓓(U, ℝ), ∃ C : ℝ, ∀ y, |φ y| ≤ C * χ y := by
  obtain ⟨χ, hχ1, hχ01⟩ := exists_testFunction_eq_one_nhds_compact (Ω := U)
    φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  refine ⟨χ, C, fun y => ?_⟩
  by_cases hy : y ∈ tsupport φ
  · rw [hχ1.self_of_nhdsSet y hy, mul_one, ← Real.norm_eq_abs]
    exact hC y
  · rw [image_eq_zero_of_notMem_tsupport hy, abs_zero]
    exact mul_nonneg ((norm_nonneg _).trans (hC y)) (hχ01 y).1

/-- The fibre identity for `φ 1_A`, `A` closed. -/
theorem fibreIdentity_mul_indicator_of_isClosed (hw : IsL1PshOn U w) (φ : 𝓓(U, ℝ))
    {A : Set (ComplexModel (m + 1))} (hA : IsClosed A) :
    FibreIdentity hw (fun y => φ y * A.indicator (fun _ => (1 : ℝ)) y) := by
  obtain ⟨f, hf, hf01, hfA⟩ := exists_contDiff_eq_one_iff hA
  obtain ⟨χ, C, hC⟩ := exists_abs_le_mul_testFunction φ
  have hpow : ∀ l : ℕ, ContDiff ℝ ∞ (fun y => f y ^ l) := fun l => hf.pow l
  refine FibreIdentity.of_tendsto hw (g := fun l => ⇑(mulTest (hpow l) φ))
    (fun l => fibreIdentity_testFunction hw _) (fun l => (mulTest (hpow l) φ).continuous.measurable)
    χ (C := C) (fun l y => ?_) (fun y => ?_)
  · rw [mulTest_apply, abs_mul]
    refine le_trans (mul_le_of_le_one_right (abs_nonneg _) ?_) (hC y)
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (by rw [abs_of_nonneg (hf01 y).1]; exact (hf01 y).2)
  · simp only [mulTest_apply]
    refine tendsto_const_nhds.mul ?_
    by_cases hy : y ∈ A
    · rw [(hfA y).mp hy, indicator_of_mem hy]
      exact tendsto_const_nhds.congr fun l => (one_pow l).symm
    · rw [indicator_of_notMem hy]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (hf01 y).1
        (lt_of_le_of_ne (hf01 y).2 fun h => hy ((hfA y).mpr h))

/-- The fibre identity for `φ 1_{⋃ A_i}`, `A_i` closed and increasing. -/
theorem fibreIdentity_mul_indicator_iUnion (hw : IsL1PshOn U w) (φ : 𝓓(U, ℝ))
    {A : ℕ → Set (ComplexModel (m + 1))} (hA : ∀ i, IsClosed (A i)) (hmono : Monotone A) :
    FibreIdentity hw (fun y => φ y * (⋃ i, A i).indicator (fun _ => (1 : ℝ)) y) := by
  obtain ⟨χ, C, hC⟩ := exists_abs_le_mul_testFunction φ
  refine FibreIdentity.of_tendsto hw (g := fun i y => φ y * (A i).indicator (fun _ => (1 : ℝ)) y)
    (fun i => fibreIdentity_mul_indicator_of_isClosed hw φ (hA i))
    (fun i => φ.continuous.measurable.mul (measurable_const.indicator (hA i).measurableSet))
    χ (C := C) (fun i y => ?_) (fun y => ?_)
  · rw [abs_mul]
    refine le_trans (mul_le_of_le_one_right (abs_nonneg _) ?_) (hC y)
    by_cases h : y ∈ A i <;> simp [h]
  · refine tendsto_const_nhds.mul ?_
    by_cases hy : y ∈ ⋃ i, A i
    · obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp hy
      rw [indicator_of_mem hy]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop i₀] with i hi
      rw [indicator_of_mem (hmono hi hi₀)]
    · have h0 : ∀ i, y ∉ A i := fun i h => hy (mem_iUnion.mpr ⟨i, h⟩)
      simp only [indicator_of_notMem hy, indicator_of_notMem (h0 _)]
      exact tendsto_const_nhds

/-! ### The strict loci as increasing unions of closed sets -/

variable (U) in
/-- The closed sets `{y ∈ U → u y ≥ -k + 1/(i+1)}`. -/
def levelSet (u : ComplexModel (m + 1) → EReal) (k i : ℕ) : Set (ComplexModel (m + 1)) :=
  {y | y ∈ U → (((-(k : ℝ) + 1 / ((i : ℝ) + 1) : ℝ)) : EReal) ≤ u y}

/-- The level sets are closed (upper semicontinuity of `u`). -/
theorem isClosed_levelSet {u : ComplexModel (m + 1) → EReal} (hu : PlurisubharmonicOn u U)
    (k i : ℕ) : IsClosed (levelSet U u k i) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  simp only [levelSet, mem_compl_iff, mem_ofPred_eq, Classical.not_imp, not_le] at hy
  have h := (hu y hy.1).upperSemicontinuousAt _ hy.2
  filter_upwards [U.isOpen.mem_nhds hy.1, h] with x hx hxc
  simp only [levelSet, mem_compl_iff, mem_ofPred_eq, Classical.not_imp, not_le]
  exact ⟨hx, hxc⟩

/-- The level sets increase with `i`. -/
theorem levelSet_mono (u : ComplexModel (m + 1) → EReal) (k : ℕ) :
    Monotone (levelSet U u k) := by
  intro i i' hii' y hy hyU
  refine le_trans ?_ (hy hyU)
  rw [EReal.coe_le_coe_iff]
  have : 1 / ((i' : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hii' 1)
  linarith

/-- `φ 1_{O_k} = φ 1_{⋃ᵢ levelSet U u k i}` (the test function vanishes off `U`). -/
theorem mul_indicator_strictLocus_eq (φ : 𝓓(U, ℝ)) (u : ComplexModel (m + 1) → EReal) (k : ℕ) :
    (fun y => φ y * (BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k).indicator
      (fun _ => (1 : ℝ)) y) =
      fun y => φ y * (⋃ i, levelSet U u k i).indicator (fun _ => (1 : ℝ)) y := by
  funext y
  by_cases hyU : y ∈ U
  · have e : y ∈ BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k ↔
        y ∈ ⋃ i, levelSet U u k i := by
      simp only [BedfordTaylorTopDegree.strictLocus, mem_ofPred_eq, forall_const, mem_iUnion,
        levelSet]
      constructor
      · rintro ⟨-, hk⟩
        obtain ⟨r, hkr, hru⟩ := EReal.lt_iff_exists_real_btwn.mp hk
        rw [EReal.coe_lt_coe_iff] at hkr
        obtain ⟨i, hi⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < r + k)
        refine ⟨i, fun _ => le_trans ?_ hru.le⟩
        rw [EReal.coe_le_coe_iff]
        linarith
      · rintro ⟨i, hi⟩
        refine ⟨hyU, lt_of_lt_of_le ?_ (hi hyU)⟩
        rw [EReal.coe_lt_coe_iff]
        have : 0 < 1 / ((i : ℝ) + 1) := by positivity
        linarith
    by_cases h : y ∈ BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k
    · rw [indicator_of_mem h, indicator_of_mem (e.mp h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (e.mpr h'))]
  · have : φ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hyU (φ.tsupport_subset h)
    rw [this, zero_mul, zero_mul]

/-- The fibre identity for `φ 1_{O_k}`, `O_k = {u > -k}` the strict locus. -/
theorem fibreIdentity_mul_indicator_strictLocus (hw : IsL1PshOn U w) (φ : 𝓓(U, ℝ))
    {u : ComplexModel (m + 1) → EReal} (hu : PlurisubharmonicOn u U) (k : ℕ) :
    FibreIdentity hw (fun y => φ y *
      (BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k).indicator
        (fun _ => (1 : ℝ)) y) := by
  rw [mul_indicator_strictLocus_eq]
  exact fibreIdentity_mul_indicator_iUnion hw φ (isClosed_levelSet hu k) (levelSet_mono u k)


/-! ### The planar input and the comparison on the fibres -/

open SGPT.NPP.NonPluripolarCurrent in
/-- The truncation `max(v, -k)` of a psh function is a psh function in `L¹_loc`. -/
theorem isL1PshOn_truncation {N : ℕ} {V : Opens (ComplexModel N)} {v : ComplexModel N → EReal}
    (hv : PlurisubharmonicOn v V) (k : ℕ) :
    IsL1PshOn V (fun x => (truncationReal v k x : EReal)) :=
  ⟨(truncationReal_isLocallyBoundedPshOn hv k).1, fun _ _ =>
    Filter.Frequently.of_forall fun _ => EReal.coe_ne_bot _⟩

open SGPT.NPP.NonPluripolarCurrent in
/-- **The planar input** (S45's identity `(dd^c v)^1 = 1_{v>-∞} dd^c v` in one variable, read on
the strict loci): `1_{O_k} dd^c v = 1_{O_k} dd^c max(v, -k)`, as trace measures. -/
theorem traceMeasure_restrict_strictLocus_planar {V : Opens (ComplexModel 1)}
    {v : ComplexModel 1 → EReal} (hv : IsL1PshOn V v) (k : ℕ) :
    hv.isPositive_ddcL1.traceMeasure.restrict
        (BedfordTaylorTopDegree.strictLocus V (fun _ : Fin 1 => v) k) =
      (isL1PshOn_truncation hv.psh k).isPositive_ddcL1.traceMeasure.restrict
        (BedfordTaylorTopDegree.strictLocus V (fun _ : Fin 1 => v) k) := by
  have hqp : 0 + 1 = 1 := rfl
  set O := BedfordTaylorTopDegree.strictLocus V (fun _ : Fin 1 => v) k with hOdef
  have hψ : ∀ _ : Fin 1, PlurisubharmonicOn v V := fun _ => hv.psh
  have hO : MeasurableSet O := BedfordTaylorTopDegree.measurableSet_strictLocus hψ k
  set A : Set (ComplexModel 1) := {z | z ∈ V ∧ v z ≠ ⊥} with hAdef
  have hA : MeasurableSet A := by
    rw [hAdef, ← iUnion_strictLocus_one (m := 0)]
    exact MeasurableSet.iUnion (BedfordTaylorTopDegree.measurableSet_strictLocus hψ)
  have h1 := SGPT.NPP.Riesz.nonPluripolarProduct_eq_indicator_ddcL1_of_dim_one hv hqp
  have h2 := mulBorel_nonPluripolarProduct_strictLocus hqp hψ (isWellDefinedOn_one hv hqp) k
  rw [h1, mulBorel_mulBorel hv.isPositive_ddcL1 (measurable_const.indicator hA)
    (isLocallyBoundedOn_indicator_one _) (fun x => by by_cases h : x ∈ A <;> simp [h])
    (measurable_const.indicator hO) (isLocallyBoundedOn_indicator_one _)] at h2
  have e : (fun x => A.indicator (fun _ => (1 : ℝ)) x * O.indicator (fun _ => (1 : ℝ)) x) =
      O.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ O
    · have hxA : x ∈ A := ⟨hx.1, ne_bot_of_gt (hx.2 0)⟩
      simp [hx, hxA]
    · simp [hx]
  rw [e] at h2
  have h3 : BedfordTaylorTopDegree.truncatedProduct hqp V (fun _ : Fin 1 => v) k =
      mulBorel (ddcL1 (m := 0) V (fun x => (truncationReal v k x : EReal)))
        (O.indicator fun _ => (1 : ℝ)) := by
    rw [ddcL1_coe_eq_ddcMul (truncationReal_isLocallyBoundedPshOn hv.psh k)]
    rfl
  rw [h3] at h2
  have h4 := SGPT.NPP.Riesz.traceMeasure_eq_of_eq h2
    (isPositive_mulBorel_indicator hv.isPositive_ddcL1 hO)
    (isPositive_mulBorel_indicator (isL1PshOn_truncation hv.psh k).isPositive_ddcL1 hO)
  rw [traceMeasure_mulBorel_indicator hv.isPositive_ddcL1 hO,
    traceMeasure_mulBorel_indicator (isL1PshOn_truncation hv.psh k).isPositive_ddcL1 hO] at h4
  exact h4

/-- The truncation commutes with the restriction to a fibre. -/
theorem fibreFun_truncation (u : ComplexModel (m + 1) → EReal) (k : ℕ) (j : Fin (m + 1))
    (z : ComplexModel m) :
    fibreFun (fun y => (truncationReal u k y : EReal)) j z =
      fun x => (truncationReal (fibreFun u j z) k x : EReal) := rfl

/-- The strict locus of a fibre is the fibre of the strict locus. -/
theorem preimage_strictLocus (u : ComplexModel (m + 1) → EReal) (k : ℕ) (j : Fin (m + 1))
    (z : ComplexModel m) :
    lineMap j z ⁻¹' BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k =
      BedfordTaylorTopDegree.strictLocus (fibreOpens U j z) (fun _ : Fin 1 => fibreFun u j z) k :=
  rfl

/-- **The comparison on a good fibre**: for `g = φ 1_{O_k}`, the fibre integrals against
`dd^c_x u_z` and against `dd^c_x max(u_z, -k)` agree. -/
theorem integral_fibre_strictLocus_eq {u : ComplexModel (m + 1) → EReal}
    (hu : PlurisubharmonicOn u U)
    (j : Fin (m + 1)) {z : ComplexModel m} (hz : IsL1PshOn (fibreOpens U j z) (fibreFun u j z))
    (φ : 𝓓(U, ℝ)) (k : ℕ) :
    ∫ x, φ (lineMap j z x) * (BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k).indicator
        (fun _ => (1 : ℝ)) (lineMap j z x) ∂fibreMeasure U u j z =
      ∫ x, φ (lineMap j z x) *
        (BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k).indicator
          (fun _ => (1 : ℝ)) (lineMap j z x)
        ∂fibreMeasure U (fun y => (truncationReal u k y : EReal)) j z := by
  have hz' : IsL1PshOn (fibreOpens U j z)
      (fibreFun (fun y => (truncationReal u k y : EReal)) j z) :=
    isL1PshOn_truncation (plurisubharmonicOn_fibreFun hu j z) k
  rw [fibreMeasure_of_isL1PshOn hz, fibreMeasure_of_isL1PshOn hz']
  set O' := BedfordTaylorTopDegree.strictLocus (fibreOpens U j z)
    (fun _ : Fin 1 => fibreFun u j z) k
  have hO' : MeasurableSet O' := BedfordTaylorTopDegree.measurableSet_strictLocus
    (fun _ => plurisubharmonicOn_fibreFun hu j z) k
  have e : (fun x => φ (lineMap j z x) *
      (BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k).indicator
        (fun _ => (1 : ℝ)) (lineMap j z x)) = O'.indicator fun x => φ (lineMap j z x) := by
    funext x
    by_cases hx : lineMap j z x ∈ BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k
    · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ O' from hx), mul_one]
    · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ O' from hx), mul_zero]
  rw [e, integral_indicator hO', integral_indicator hO']
  have h := traceMeasure_restrict_strictLocus_planar hz k
  rw [h]
  rfl

/-- **The key identity**: `∫ φ 1_{O_k} dσ_{dd^c u} = ∫ φ 1_{O_k} dσ_{dd^c max(u,-k)}`. -/
theorem integral_mul_indicator_strictLocus_eq {u : ComplexModel (m + 1) → EReal}
    (hu : IsL1PshOn U u) (φ : 𝓓(U, ℝ)) (k : ℕ) :
    ∫ y, φ y * (BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k).indicator
        (fun _ => (1 : ℝ)) y ∂hu.isPositive_ddcL1.traceMeasure =
      ∫ y, φ y * (BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k).indicator
        (fun _ => (1 : ℝ)) y ∂(isL1PshOn_truncation hu.psh k).isPositive_ddcL1.traceMeasure := by
  rw [(fibreIdentity_mul_indicator_strictLocus hu φ hu.psh k).2,
    (fibreIdentity_mul_indicator_strictLocus (isL1PshOn_truncation hu.psh k) φ hu.psh k).2]
  congr 1
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae ?_
  filter_upwards [ae_isL1PshOn_fibre hu j] with z hz
  exact integral_fibre_strictLocus_eq hu.psh j hz φ k


/-! ### The identity `(dd^c u)^1 = 1_{u > -∞} dd^c u` -/

open SGPT.NPP.NonPluripolarCurrent in
/-- **`1_{O_k} dd^c u = 1_{O_k} dd^c max(u, -k)`** as currents, for every `k`. -/
theorem mulBorel_ddcL1_strictLocus {u : ComplexModel (m + 1) → EReal} (hu : IsL1PshOn U u)
    (hqp : m + 1 = m + 1) (k : ℕ) :
    mulBorel (ddcL1 U u)
        ((BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k).indicator fun _ => (1 : ℝ)) =
      BedfordTaylorTopDegree.truncatedProduct hqp U (fun _ : Fin 1 => u) k := by
  set O := BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k with hOdef
  have hψ : ∀ _ : Fin 1, PlurisubharmonicOn u U := fun _ => hu.psh
  have hO : MeasurableSet O := BedfordTaylorTopDegree.measurableSet_strictLocus hψ k
  have hOm : Measurable (O.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hO
  have hOb := isLocallyBoundedOn_indicator_one (U := U) O
  have hO0 : ∀ x, 0 ≤ O.indicator (fun _ => (1 : ℝ)) x := fun x => by
    by_cases h : x ∈ O <;> simp [h]
  set T := ddcL1 U u with hTdef
  have hT : IsPositive T := hu.isPositive_ddcL1
  set Tk := ddcL1 U (fun x => (truncationReal u k x : EReal)) with hTkdef
  have hTk : IsPositive Tk := (isL1PshOn_truncation hu.psh k).isPositive_ddcL1
  set B := BedfordTaylorTopDegree.truncatedProduct hqp U (fun _ : Fin 1 => u) k with hBdef
  have hB : B = mulBorel Tk (O.indicator fun _ => (1 : ℝ)) := by
    rw [hBdef, hTkdef, ddcL1_coe_eq_ddcMul (truncationReal_isLocallyBoundedPshOn hu.psh k)]
    rfl
  have hBpos : IsPositive B := by rw [hB]; exact isPositive_mulBorel_indicator hTk hO
  have hD : IsPositive (T - B) := isPositive_ddcL1_sub_truncatedProduct_one hu hqp k
  have hBB : mulBorel B (O.indicator fun _ => (1 : ℝ)) = B := by
    conv_lhs => rw [hB]
    rw [mulBorel_mulBorel hTk hOm hOb hO0 hOm hOb, hB]
    congr 1
    funext x
    by_cases h : x ∈ O <;> simp [h]
  set E := mulBorel (T - B) (O.indicator fun _ => (1 : ℝ)) with hEdef
  have hE : IsPositive E := isPositive_mulBorel_indicator hD hO
  have hTO : mulBorel T (O.indicator fun _ => (1 : ℝ)) = E + B := by
    have hsplit : T = (1 : ℝ) • (T - B) + (1 : ℝ) • B := by
      rw [one_smul, one_smul, sub_add_cancel]
    conv_lhs => rw [hsplit]
    rw [mulBorel_smul_add_smul hD hBpos zero_le_one zero_le_one hOm hOb, one_smul, one_smul, hBB]
  -- `E` has vanishing trace
  have hdens : ∀ {S : LocalProductCurrent (m + 1) U m} (hS : IsPositive S) (φ : 𝓓(U, ℝ)),
      mulBorel S (O.indicator fun _ => (1 : ℝ)) (kahlerPower (m + 1) m) φ =
        ∫ y, φ y * O.indicator (fun _ => (1 : ℝ)) y ∂hS.traceMeasure := by
    intro S hS φ
    rw [mulBorel_apply hS hOm hOb]
    refine integral_congr_ae ?_
    filter_upwards [density_kahlerPower_ae hS] with x hx
    rw [hx, mul_one]
  have hEtrace : ∀ φ : 𝓓(U, ℝ), E (kahlerPower (m + 1) m) φ = 0 := by
    intro φ
    have h1 : E = mulBorel T (O.indicator fun _ => (1 : ℝ)) - B := by
      rw [hTO, add_sub_cancel_right]
    rw [h1, LinearMap.sub_apply, sub_apply, hdens hT φ]
    conv_lhs => rw [hB]
    rw [hdens hTk φ, sub_eq_zero]
    exact integral_mul_indicator_strictLocus_eq hu φ k
  have hσ : hE.traceMeasure = 0 :=
    LocalBedfordTaylorLocality.eq_of_forall_testFunction_integral_eq (U := U)
      hE.traceMeasure_compl (by simp) (fun K hK hKU => hE.traceMeasure_lt_top hK hKU)
      (fun K _ _ => by simp) fun φ => by
        rw [hE.integral_traceMeasure, hEtrace, integral_zero_measure]
  have hE0 : E = 0 := by
    ext γ φ
    rw [hE.apply_eq_integral_density, hσ, integral_zero_measure]
    rfl
  rw [hTO, hE0, zero_add]

open SGPT.NPP.NonPluripolarCurrent in
/-- **Source `ex:1Dnpp`, `eq:1dimnpp`, in every dimension**: for `u` psh and locally integrable on
an open set `U ⊆ ℂ^{m+1}`, the degree-one non-pluripolar product is
`(dd^c u)^1 = 1_{u > -∞} dd^c u` (`dd^c u` the distributional current `ddcL1`). -/
theorem nonPluripolarProduct_eq_indicator_ddcL1 {u : ComplexModel (m + 1) → EReal}
    (hu : IsL1PshOn U u) (hqp : m + 1 = m + 1) :
    NonPluripolarCurrent.nonPluripolarProduct hqp U (fun _ : Fin 1 => u) =
      mulBorel (ddcL1 U u) ({z | z ∈ U ∧ u z ≠ ⊥}.indicator fun _ => (1 : ℝ)) := by
  have hψ : ∀ _ : Fin 1, PlurisubharmonicOn u U := fun _ => hu.psh
  set A : Set (ComplexModel (m + 1)) := {z | z ∈ U ∧ u z ≠ ⊥} with hAdef
  have hA : MeasurableSet A := by
    rw [hAdef, ← iUnion_strictLocus_one]
    exact MeasurableSet.iUnion (BedfordTaylorTopDegree.measurableSet_strictLocus hψ)
  have hT := hu.isPositive_ddcL1
  have hAm : Measurable (A.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hA
  have hA0 : ∀ x, 0 ≤ A.indicator (fun _ => (1 : ℝ)) x := fun x => by
    by_cases h : x ∈ A <;> simp [h]
  refine (eq_nonPluripolarProduct_of_mulBorel hqp hψ (isWellDefinedOn_one hu hqp)
    (isPositive_mulBorel_indicator hT hA) (fun k => ?_) ?_).symm
  · have hO := BedfordTaylorTopDegree.measurableSet_strictLocus hψ k
    rw [mulBorel_mulBorel hT hAm (isLocallyBoundedOn_indicator_one _) hA0
      (measurable_const.indicator hO) (isLocallyBoundedOn_indicator_one _),
      ← mulBorel_ddcL1_strictLocus hu hqp k]
    congr 1
    funext x
    by_cases hx : x ∈ BedfordTaylorTopDegree.strictLocus U (fun _ : Fin 1 => u) k
    · have hxA : x ∈ A := ⟨hx.1, ne_bot_of_gt (hx.2 0)⟩
      simp [hx, hxA]
    · simp [hx]
  · rw [iUnion_strictLocus_one, ← hAdef, mulBorel_mulBorel hT hAm
      (isLocallyBoundedOn_indicator_one _) hA0 (measurable_const.indicator hA.compl)
      (isLocallyBoundedOn_indicator_one _)]
    have e : (fun x => A.indicator (fun _ => (1 : ℝ)) x * Aᶜ.indicator (fun _ => (1 : ℝ)) x) =
        fun _ => (0 : ℝ) := by
      funext x
      by_cases hx : x ∈ A <;> simp [hx]
    rw [e, mulBorel_const hT 0, zero_smul]

/-- **Source `ex:1Dnpp`, the reverse inequality, in every dimension**:
`1_{u > -∞} dd^c u ≤ (dd^c u)^1`. -/
theorem isPositive_nonPluripolarProduct_sub_indicator_ddcL1 {u : ComplexModel (m + 1) → EReal}
    (hu : IsL1PshOn U u) (hqp : m + 1 = m + 1) :
    IsPositive (NonPluripolarCurrent.nonPluripolarProduct hqp U (fun _ : Fin 1 => u) -
      mulBorel (ddcL1 U u) ({z | z ∈ U ∧ u z ≠ ⊥}.indicator fun _ => (1 : ℝ))) := by
  rw [nonPluripolarProduct_eq_indicator_ddcL1 hu hqp, sub_self]
  exact isPositive_zero

end SGPT.NPP.DegreeOne

namespace SGPT.NPP

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc
open SGPT.NPP.NonPluripolarCurrent

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

/-- **Source `ex:1Dnpp` on a complex manifold of any dimension**: for `φ ∈ PSH(M)`, in every
chart, `(dd^c φ)^1 = 1_{φ > -∞} dd^c φ`, where `(dd^c φ)^1` is the non-pluripolar product
(`def:npp:L69`) and `dd^c φ` the current `SGPT.NPP.ddcCurrent`. -/
theorem nonPluripolarProduct_inChart_eq_indicator_ddcCurrent {φ : M → EReal}
    (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ) (hqp : m + 1 = m + 1)
    (e : ComplexChart (m + 1) M) :
    (nonPluripolarProduct hqp (fun _ : Fin 1 => φ) (fun _ => hφ)
        (isNonPluripolarWellDefined_one hφ hqp)).inChart e =
      mulBorel ((ddcCurrent m φ hφ).inChart e)
        ({z | z ∈ chartTarget e ∧ φ (e.val.symm z) ≠ ⊥}.indicator fun _ => (1 : ℝ)) :=
  SGPT.NPP.DegreeOne.nonPluripolarProduct_eq_indicator_ddcL1 (isL1PshOn_chart hφ e) hqp

/-- **Source `ex:1Dnpp`, the reverse inequality, on a complex manifold of any dimension**: in
every chart, `1_{φ > -∞} dd^c φ ≤ (dd^c φ)^1`. -/
theorem isPositive_nonPluripolarProduct_sub_indicator_ddcCurrent {φ : M → EReal}
    (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ) (hqp : m + 1 = m + 1)
    (e : ComplexChart (m + 1) M) :
    IsPositive ((nonPluripolarProduct hqp (fun _ : Fin 1 => φ) (fun _ => hφ)
        (isNonPluripolarWellDefined_one hφ hqp)).inChart e -
      mulBorel ((ddcCurrent m φ hφ).inChart e)
        ({z | z ∈ chartTarget e ∧ φ (e.val.symm z) ≠ ⊥}.indicator fun _ => (1 : ℝ))) :=
  SGPT.NPP.DegreeOne.isPositive_nonPluripolarProduct_sub_indicator_ddcL1
    (isL1PshOn_chart hφ e) hqp

end SGPT.NPP
