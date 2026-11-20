import SGPT.Okounkov.SchemeLineBundleStructuralMetric
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization
import SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
import SGPT.Foundations.Analysis.FirstPass.AnalyticSingularities

/-!
# The fixed original line metric on actual native fibres

All fibre coordinates are constructed from the original regular frame units.
The existing structural partition metric is fixed before any tensor degree
or section. Smoothness is stated in actual original base/fibre coordinates;
the native core retains its existing continuous bundle structure.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff ComplexConjugate

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance geometryPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance geometryPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance geometryPointManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Auxiliary projective embeddings change only proof instances in the
canonical realization of the SAME original transition unit. -/
theorem schemeFrameTransition_embedding_independent (E' : ClosedProjectiveEmbedding f)
    {L : X.Modules} {U V : X.Opens} (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) :
    schemeFrameTransition f n E α β = schemeFrameTransition f n E' α β := by
  rfl

/-- The coordinate in ANY original frame of the SAME actual native fibre.
The original nonzero transition unit supplies the linear inverse. -/
def schemeLineBundleFibreFrame {L : X.Modules} (a : LineBundleAtlas L)
    {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    (schemeLineBundleCore f n E a).Fiber p ≃ₗ[ℂ] ℂ := by
  let Z := schemeLineBundleCore f n E a
  let g := schemeFrameTransition f n E (a.frame (Z.indexAt p)) α p
  have hg : g ≠ 0 := schemeFrameTransition_ne_zero f n E _ _ p
    (Z.mem_baseSet_at p) hp
  change ℂ ≃ₗ[ℂ] ℂ
  exact
    { toFun := fun v => g * v
      invFun := fun v => g⁻¹ * v
      left_inv := fun v => by
        change g⁻¹ * (g * v) = v
        rw [← mul_assoc, inv_mul_cancel₀ hg, one_mul]
      right_inv := fun v => by
        change g * (g⁻¹ * v) = v
        rw [← mul_assoc, mul_inv_cancel₀ hg, one_mul]
      map_add' := fun v w => mul_add g v w
      map_smul' := fun c v => by simp only [smul_eq_mul, RingHom.id_apply]; ring }

/-- The canonical actual-fibre identification between two ORIGINAL atlases. -/
def schemeLineBundleCore_fibreEquiv {L : X.Modules} (a b : LineBundleAtlas L)
    (p : SchemeComplexPoint f) :
    (schemeLineBundleCore f n E a).Fiber p ≃ₗ[ℂ]
      (schemeLineBundleCore f n E b).Fiber p :=
  schemeLineBundleFibreFrame f n E a
    (b.frame ((schemeLineBundleCore f n E b).indexAt p)) p
    ((schemeLineBundleCore f n E b).mem_baseSet_at p)

namespace SchemeLineBundleMetric

variable {f n E} {L : X.Modules} (H : SchemeLineBundleMetric f n E L)

/-- The genuine Hermitian pairing on the SAME native fibre, using the fixed
original structural metric and its preferred original frame. -/
def nativeHermitian (a : LineBundleAtlas L) (p : SchemeComplexPoint f) :
    (schemeLineBundleCore f n E a).Fiber p →ₗ⋆[ℂ]
      (schemeLineBundleCore f n E a).Fiber p →ₗ[ℂ] ℂ := by
  let h : ℝ := H.frameNormSq (a.frame ((schemeLineBundleCore f n E a).indexAt p)) p
  change ℂ →ₗ⋆[ℂ] ℂ →ₗ[ℂ] ℂ
  exact LinearMap.mk₂'ₛₗ _ _ (fun v w : ℂ => (h : ℂ) * conj v * w)
    (fun v₁ v₂ w => by simp only [map_add]; ring)
    (fun c v w => by simp only [smul_eq_mul, map_mul]; ring)
    (fun v w₁ w₂ => by ring)
    (fun c v w => by simp only [smul_eq_mul, RingHom.id_apply]; ring)

/-- The native pairing has the exact coefficient in EVERY original frame,
not only in the chosen atlas. -/
theorem nativeHermitian_frame (a : LineBundleAtlas L) {U : X.Opens}
    (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U)
    (v w : (schemeLineBundleCore f n E a).Fiber p) :
    H.nativeHermitian a p v w = (H.frameNormSq α p : ℂ) *
      conj (schemeLineBundleFibreFrame f n E a α p hp v) *
        schemeLineBundleFibreFrame f n E a α p hp w := by
  change ℂ at v w
  let Z := schemeLineBundleCore f n E a
  let g := schemeFrameTransition f n E (a.frame (Z.indexAt p)) α p
  have hH := H.transition (a.frame (Z.indexAt p)) α p (Z.mem_baseSet_at p) hp
  change (H.frameNormSq (a.frame (Z.indexAt p)) p : ℂ) * conj (v : ℂ) * (w : ℂ) =
    (H.frameNormSq α p : ℂ) * conj (g * (v : ℂ)) * (g * (w : ℂ))
  rw [hH]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_mul]
  ring

/-- Conjugate symmetry of the actual native-fibre Hermitian pairing. -/
theorem nativeHermitian_conj_symm (a : LineBundleAtlas L) (p : SchemeComplexPoint f)
    (v w : (schemeLineBundleCore f n E a).Fiber p) :
    conj (H.nativeHermitian a p v w) = H.nativeHermitian a p w v := by
  change ℂ at v w
  change conj ((H.frameNormSq
    (a.frame ((schemeLineBundleCore f n E a).indexAt p)) p : ℂ) * conj v * w) =
      (H.frameNormSq (a.frame ((schemeLineBundleCore f n E a).indexAt p)) p : ℂ) * conj w * v
  simp [map_mul, mul_comm, mul_assoc]

/-- Strict positivity of the ACTUAL native-fibre diagonal. -/
theorem nativeHermitian_positive (a : LineBundleAtlas L) (p : SchemeComplexPoint f)
    (v : (schemeLineBundleCore f n E a).Fiber p) (hv : v ≠ 0) :
    0 < (H.nativeHermitian a p v v).re := by
  change ℂ at v
  change 0 < (((H.frameNormSq
    (a.frame ((schemeLineBundleCore f n E a).indexAt p)) p : ℝ) : ℂ) * conj (v : ℂ) * (v : ℂ)).re
  rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_pos (H.positive _ p ((schemeLineBundleCore f n E a).mem_baseSet_at p))
    (Complex.normSq_pos.mpr hv)

/-- The canonical original-atlas fibre identification preserves the SAME
fixed Hermitian metric. -/
theorem nativeHermitian_fibreEquiv (a b : LineBundleAtlas L) (p : SchemeComplexPoint f)
    (v w : (schemeLineBundleCore f n E a).Fiber p) :
    H.nativeHermitian b p (schemeLineBundleCore_fibreEquiv f n E a b p v)
      (schemeLineBundleCore_fibreEquiv f n E a b p w) = H.nativeHermitian a p v w := by
  exact (H.nativeHermitian_frame a
    (b.frame ((schemeLineBundleCore f n E b).indexAt p)) p
    ((schemeLineBundleCore f n E b).mem_baseSet_at p) v w).symm

/-- The exact local squared norm is smooth for EVERY holomorphic scalar
section coefficient, including all its zeros. -/
theorem nativeHermitian_local_smooth {U : X.Opens} (α : LocalBundleFrame L U)
    (b : SchemeComplexPoint f → ℂ)
    (hb : ∀ p, schemeComplexPointImage f p ∈ U → HolomorphicAt n b p)
    (e : ComplexChart n (SchemeComplexPoint f)) :
    ContDiffOn ℝ ∞ (fun z => H.frameNormSq α (e.val.symm z) *
      Complex.normSq (b (e.val.symm z)))
      (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  intro z hz
  have hnorm : ContDiffAt ℝ ∞ (fun z => Complex.normSq (b (e.val.symm z))) z := by
    apply BlanchardWeight.BlanchardData.contDiffAt_normSq_comp
    filter_upwards [hD.mem_nhds hz] with y hy
    exact FactorizedWeightForm.differentiableAt_comp_chart_symm e hy.1
      (hb _ hy.2).mdifferentiableAt
  exact ((H.smooth α e).contDiffAt (hD.mem_nhds hz) |>.mul hnorm).contDiffWithinAt

/-- The actual all-frame positive metric gives smooth real log weights. -/
private theorem frame_log_smooth {U : X.Opens} (α : LocalBundleFrame L U)
    (e : ComplexChart n (SchemeComplexPoint f)) :
    ContDiffOn ℝ ∞ (fun z => Real.log (H.frameNormSq α (e.val.symm z)))
      (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
  (H.smooth α e).log fun _ hz => (H.positive α _ hz.2).ne'

/-- Original unit factorization, with constant-one first generator, reuses
actual logarithmic pluriharmonicity without any supplied curvature identity. -/
private theorem log_frame_ddc_eq {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V)
    (e : ComplexChart n (SchemeComplexPoint f)) {u : ComplexModel n}
    (hu : u ∈ e.val.target) (hU : schemeComplexPointImage f (e.val.symm u) ∈ U)
    (hV : schemeComplexPointImage f (e.val.symm u) ∈ V) :
    smoothDDC (fun z => Real.log (H.frameNormSq α (e.val.symm z))) u =
      smoothDDC (fun z => Real.log (H.frameNormSq β (e.val.symm z))) u := by
  let := E.isSeparated
  let := E.quasiCompact
  let S := e.val.target ∩ e.val.symm ⁻¹'
    ((schemeComplexPointImage f ⁻¹' U) ∩ (schemeComplexPointImage f ⁻¹' V))
  have hS : IsOpen S := e.val.isOpen_inter_preimage_symm
    ((U.isOpen.preimage (schemeComplexPointImage_continuous f)).inter
      (V.isOpen.preimage (schemeComplexPointImage_continuous f)))
  have hα : ContDiffOn ℝ ∞ (fun z => H.frameNormSq α (e.val.symm z)) S :=
    (H.smooth α e).mono fun _ hz => ⟨hz.1, hz.2.1⟩
  have hβ : ContDiffOn ℝ ∞ (fun z => H.frameNormSq β (e.val.symm z)) S :=
    (H.smooth β e).mono fun _ hz => ⟨hz.1, hz.2.2⟩
  let g := fun z : ComplexModel n => schemeFrameTransition f n E α β (e.val.symm z)
  have hg : DifferentiableOn ℂ g S := by
    intro z hz
    exact (FactorizedWeightForm.differentiableAt_comp_chart_symm e hz.1
      (schemeFrameTransition_holomorphicAt f n E α β _ hz.2.1 hz.2.2).mdifferentiableAt).differentiableWithinAt
  exact LogWeightFactorization.smoothDDC_log_eq_of_normSq_mul_eq hS hα hβ
    (fun z hz => H.positive α _ hz.2.1) (fun z hz => H.positive β _ hz.2.2)
    (h₁ := fun _ => (1 : ℂ)) (h₂ := g)
    (fun _ _ => (differentiableAt_const (1 : ℂ)).differentiableWithinAt) hg
    (fun z hz => by
      simpa only [Complex.normSq_one, one_mul] using
        (H.transition α β (e.val.symm z) hz.2.1 hz.2.2))
    (fun z hz => subset_closure ⟨hz, one_ne_zero⟩) ⟨hu, hU, hV⟩

private theorem neg_log_frame_ddc_eq {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V)
    (e : ComplexChart n (SchemeComplexPoint f)) {u : ComplexModel n}
    (hu : u ∈ e.val.target) (hU : schemeComplexPointImage f (e.val.symm u) ∈ U)
    (hV : schemeComplexPointImage f (e.val.symm u) ∈ V) :
    smoothDDC (fun z => -Real.log (H.frameNormSq α (e.val.symm z))) u =
      smoothDDC (fun z => -Real.log (H.frameNormSq β (e.val.symm z))) u := by
  rw [smoothDDC_neg
      (e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f)))
      (H.frame_log_smooth α e) ⟨hu, hU⟩,
    smoothDDC_neg
      (e.val.isOpen_inter_preimage_symm (V.isOpen.preimage (schemeComplexPointImage_continuous f)))
      (H.frame_log_smooth β e) ⟨hu, hV⟩,
    H.log_frame_ddc_eq α β e hu hU hV]

/-- Every local-potential field, including overlap pluriharmonicity, is
manufactured from the SAME original positive smooth frame weights. -/
private def curvatureData (a : LineBundleAtlas L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    LocalPotentialForm.LocalDDCData n (SchemeComplexPoint f) := by
  let := E.isSeparated
  let := E.quasiCompact
  let Z := schemeLineBundleCore f n E a
  exact
    { domain := fun p => schemeComplexPointImage f ⁻¹' a.opens (Z.indexAt p)
      isOpen_domain := fun p =>
        (a.opens (Z.indexAt p)).isOpen.preimage (schemeComplexPointImage_continuous f)
      mem_domain := fun p => Z.mem_baseSet_at p
      potential := fun p q => -Real.log (H.frameNormSq (a.frame (Z.indexAt p)) q)
      smooth := fun p e => (H.frame_log_smooth (a.frame (Z.indexAt p)) e).neg
      pluriharmonic := by
        intro p q e u hu hp hq
        let S := e.val.target ∩ e.val.symm ⁻¹'
          ((schemeComplexPointImage f ⁻¹' a.opens (Z.indexAt p)) ∩
            (schemeComplexPointImage f ⁻¹' a.opens (Z.indexAt q)))
        have hS : IsOpen S := e.val.isOpen_inter_preimage_symm
          (((a.opens (Z.indexAt p)).isOpen.preimage (schemeComplexPointImage_continuous f)).inter
            ((a.opens (Z.indexAt q)).isOpen.preimage (schemeComplexPointImage_continuous f)))
        have hα : ContDiffOn ℝ ∞
            (fun z => -Real.log (H.frameNormSq (a.frame (Z.indexAt p)) (e.val.symm z))) S :=
          ((H.frame_log_smooth (a.frame (Z.indexAt p)) e).neg).mono fun _ hz =>
            ⟨hz.1, hz.2.1⟩
        have hβ : ContDiffOn ℝ ∞
            (fun z => -Real.log (H.frameNormSq (a.frame (Z.indexAt q)) (e.val.symm z))) S :=
          ((H.frame_log_smooth (a.frame (Z.indexAt q)) e).neg).mono fun _ hz =>
            ⟨hz.1, hz.2.2⟩
        rw [PositiveClasses.smoothDDC_sub hS hα hβ ⟨hu, hp, hq⟩,
          H.neg_log_frame_ddc_eq (a.frame (Z.indexAt p)) (a.frame (Z.indexAt q)) e hu hp hq,
          sub_self] }

/-- The actual structural Chern form, constructed by native local-dd-c
gluing. The supplied original embedding internally supplies manifold geometry. -/
def curvature (a : LineBundleAtlas L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ClosedRealOneOneForm n (SchemeComplexPoint f) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact (H.curvatureData a).closedForm

/-- WHOLE local curvature readback in EVERY original frame, on every actual
chart target. Arbitrary off-target coefficient extensions are not compared. -/
theorem curvature_coeff_frame (a : LineBundleAtlas L) {U : X.Opens}
    (α : LocalBundleFrame L U) (e : ComplexChart n (SchemeComplexPoint f))
    {u : ComplexModel n} (hu : u ∈ e.val.target)
    (hU : schemeComplexPointImage f (e.val.symm u) ∈ U) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (H.curvature a).val.coeff e u =
      smoothDDC (fun z => -Real.log (H.frameNormSq α (e.val.symm z))) u := by
  let := E.isSeparated
  let := E.quasiCompact
  let Z := schemeLineBundleCore f n E a
  let D := H.curvatureData a
  change D.form.coeff e u = _
  exact ((D.form_coeff_eventuallyEq (e.val.symm u) e hu (D.mem_domain _)).self_of_nhds).trans
    (H.neg_log_frame_ddc_eq (a.frame (Z.indexAt (e.val.symm u))) α e hu
      (Z.mem_baseSet_at _) hU)

/-- Every choice of original frames gives the SAME geometric Chern form. -/
theorem curvature_atlas_geometricallyEq (a b : LineBundleAtlas L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (H.curvature a).val.GeometricallyEq (H.curvature b).val := by
  let := E.isSeparated
  let := E.quasiCompact
  intro e u hu
  let Z := schemeLineBundleCore f n E a
  let α := a.frame (Z.indexAt (e.val.symm u))
  rw [H.curvature_coeff_frame a α e hu (Z.mem_baseSet_at _),
    H.curvature_coeff_frame b α e hu (Z.mem_baseSet_at _)]

variable {E' : ClosedProjectiveEmbedding f}

/-- The actual global log ratio uses original frame norms, not a supplied
curvature correction. The second metric may use another auxiliary embedding. -/
def logRatio (K : SchemeLineBundleMetric f n E' L) (a : LineBundleAtlas L)
    (p : SchemeComplexPoint f) : ℝ :=
  let α := a.frame ((schemeLineBundleCore f n E a).indexAt p)
  Real.log (H.frameNormSq α p / K.frameNormSq α p)

/-- The actual ratio has the SAME value in EVERY original frame. -/
theorem logRatio_frame (K : SchemeLineBundleMetric f n E' L) (a : LineBundleAtlas L)
    {U : X.Opens} (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    H.logRatio K a p = Real.log (H.frameNormSq α p / K.frameNormSq α p) := by
  let Z := schemeLineBundleCore f n E a
  change Real.log (H.frameNormSq (a.frame (Z.indexAt p)) p /
    K.frameNormSq (a.frame (Z.indexAt p)) p) = _
  congr 1
  rw [H.transition (a.frame (Z.indexAt p)) α p (Z.mem_baseSet_at p) hp,
    K.transition (a.frame (Z.indexAt p)) α p (Z.mem_baseSet_at p) hp,
    ← schemeFrameTransition_embedding_independent f n E E' (a.frame (Z.indexAt p)) α]
  exact mul_div_mul_left _ _ (Complex.normSq_pos.mpr
    (schemeFrameTransition_ne_zero f n E _ α p (Z.mem_baseSet_at p) hp)).ne'

/-- Every original frame gives a positive smooth quotient; the internally
manufactured global log ratio is therefore genuinely chart-smooth. -/
theorem logRatio_chartSmooth (K : SchemeLineBundleMetric f n E' L) (a : LineBundleAtlas L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ChartSmooth (n := n) (H.logRatio K a) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro e z hz
  let Z := schemeLineBundleCore f n E a
  let U := a.opens (Z.indexAt (e.val.symm z))
  let α := a.frame (Z.indexAt (e.val.symm z))
  have hp : schemeComplexPointImage f (e.val.symm z) ∈ U := Z.mem_baseSet_at _
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hsm : ContDiffOn ℝ ∞ (fun y =>
      Real.log (H.frameNormSq α (e.val.symm y) / K.frameNormSq α (e.val.symm y)))
      (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    ((H.smooth α e).div (K.smooth α e) fun _ hy => (K.positive α _ hy.2).ne').log
      fun _ hy => (div_pos (H.positive α _ hy.2) (K.positive α _ hy.2)).ne'
  have heq : (fun y => H.logRatio K a (e.val.symm y)) =ᶠ[𝓝 z]
      fun y => Real.log (H.frameNormSq α (e.val.symm y) / K.frameNormSq α (e.val.symm y)) := by
    filter_upwards [hD.mem_nhds ⟨hz, hp⟩] with y hy
    exact H.logRatio_frame K a α _ hy.2
  exact ((hsm.contDiffAt (hD.mem_nhds ⟨hz, hp⟩)).congr_of_eventuallyEq heq).contDiffWithinAt

/-- The actual ratio has the ORIGINAL Chern sign: Θ_K = Θ_H + dd-c log(H/K).
The equality compares every actual chart target, not off-target extensions. -/
theorem curvature_change (K : SchemeLineBundleMetric f n E' L) (a b : LineBundleAtlas L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (K.curvature b).val.GeometricallyEq
      (H.curvature a + ManifoldTubePositivity.ddcClosedForm
        (H.logRatio K a) (H.logRatio_chartSmooth K a)).val := by
  let := E.isSeparated
  let := E.quasiCompact
  intro e u hu
  let Z := schemeLineBundleCore f n E a
  let U := a.opens (Z.indexAt (e.val.symm u))
  let α := a.frame (Z.indexAt (e.val.symm u))
  have hp : schemeComplexPointImage f (e.val.symm u) ∈ U := Z.mem_baseSet_at _
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  change (K.curvature b).val.coeff e u = (H.curvature a).val.coeff e u +
    smoothDDC (fun y => H.logRatio K a (e.val.symm y)) u
  rw [K.curvature_coeff_frame b α e hu hp, H.curvature_coeff_frame a α e hu hp]
  have heq : (fun y => -Real.log (K.frameNormSq α (e.val.symm y))) =ᶠ[𝓝 u]
      fun y => -Real.log (H.frameNormSq α (e.val.symm y)) + H.logRatio K a (e.val.symm y) := by
    filter_upwards [hD.mem_nhds ⟨hu, hp⟩] with y hy
    rw [H.logRatio_frame K a α _ hy.2,
      Real.log_div (H.positive α _ hy.2).ne' (K.positive α _ hy.2).ne']
    ring
  exact (smoothDDC_congr heq).trans (smoothDDC_add hD (H.frame_log_smooth α e).neg
    ((H.logRatio_chartSmooth K a e).mono inter_subset_left) ⟨hu, hp⟩)

/-- The structural real Bott-Chern class is the class of the SAME actual
manufactured curvature form. No Chern identity is supplied by the caller. -/
def chernClass (a : LineBundleAtlas L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    RealBottChern n (SchemeComplexPoint f) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact RealBottChern.ofRepresentative (H.curvature a)

/-- All genuine metrics, partitions, original atlases and auxiliary projective
embeddings give the SAME actual structural real Bott-Chern class. -/
theorem chernClass_independent (K : SchemeLineBundleMetric f n E' L)
    (a b : LineBundleAtlas L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    H.chernClass a = K.chernClass b := by
  let := E.isSeparated
  let := E.quasiCompact
  change RealBottChern.ofRepresentative (H.curvature a) =
    RealBottChern.ofRepresentative (K.curvature b)
  apply (RealBottChern.ofRepresentative_eq_iff _ _).mpr
  refine ⟨H.logRatio K a, H.logRatio_chartSmooth K a, ?_⟩
  intro e z hz
  exact H.curvature_change K a b e hz

/-- The SAME fixed metric supplies weights on arbitrary original frames of
an actual tensor power. The reference frame is chosen from the original cover. -/
private def tensorFrameNormSq (a : LineBundleAtlas L) (k : ℕ) {U : X.Opens}
    (α : LocalBundleFrame (bundleTensorPower L k) U) (p : SchemeComplexPoint f) : ℝ :=
  let β := a.frame ((schemeLineBundleCore f n E a).indexAt p)
  Complex.normSq (schemeFrameTransition f n E α (β.tensorPower k) p) * H.frameNormSq β p ^ k

/-- Actual unit cocycles and power-frame transitions internally prove choice
independence of the tensor weight in EVERY original L-frame through the point. -/
private theorem tensorFrameNormSq_eq (a : LineBundleAtlas L) (k : ℕ) {U V : X.Opens}
    (α : LocalBundleFrame (bundleTensorPower L k) U) (β : LocalBundleFrame L V)
    (p : SchemeComplexPoint f) (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V) :
    H.tensorFrameNormSq a k α p =
      Complex.normSq (schemeFrameTransition f n E α (β.tensorPower k) p) * H.frameNormSq β p ^ k := by
  let Z := schemeLineBundleCore f n E a
  let γ := a.frame (Z.indexAt p)
  change Complex.normSq (schemeFrameTransition f n E α (γ.tensorPower k) p) *
    H.frameNormSq γ p ^ k = _
  rw [H.transition γ β p (Z.mem_baseSet_at p) hpV,
    schemeFrameTransition_cocycle f n E α (γ.tensorPower k) (β.tensorPower k) p
      hpU (Z.mem_baseSet_at p) hpV,
    schemeFrameTransition_tensorPower f n E γ β k p (Z.mem_baseSet_at p) hpV,
    Complex.normSq_mul, map_pow, mul_pow]
  ring

/-- ONE original metric induces positive smooth metrics on ALL actual original
tensor powers, including all original local frames and degree zero. -/
def tensorPower (a : LineBundleAtlas L) (k : ℕ) :
    SchemeLineBundleMetric f n E (bundleTensorPower L k) where
  frameNormSq := H.tensorFrameNormSq a k
  positive := by
    intro U α p hp
    let Z := schemeLineBundleCore f n E a
    let β := a.frame (Z.indexAt p)
    change 0 < Complex.normSq (schemeFrameTransition f n E α (β.tensorPower k) p) *
      H.frameNormSq β p ^ k
    exact mul_pos (Complex.normSq_pos.mpr
      (schemeFrameTransition_ne_zero f n E α (β.tensorPower k) p hp (Z.mem_baseSet_at p)))
      (pow_pos (H.positive β p (Z.mem_baseSet_at p)) k)
  transition := by
    intro U V α β p hpU hpV
    let Z := schemeLineBundleCore f n E a
    let γ := (a.frame (Z.indexAt p)).tensorPower k
    change Complex.normSq (schemeFrameTransition f n E α γ p) * _ =
      Complex.normSq (schemeFrameTransition f n E α β p) *
        (Complex.normSq (schemeFrameTransition f n E β γ p) * _)
    rw [schemeFrameTransition_cocycle f n E α β γ p hpU hpV (Z.mem_baseSet_at p),
      Complex.normSq_mul]
    ring
  smooth := by
    intro U α e u hu
    let := E.isSeparated
    let := E.quasiCompact
    let Z := schemeLineBundleCore f n E a
    let V := a.opens (Z.indexAt (e.val.symm u))
    let β := a.frame (Z.indexAt (e.val.symm u))
    have hpV : schemeComplexPointImage f (e.val.symm u) ∈ V := Z.mem_baseSet_at _
    let D := e.val.target ∩ e.val.symm ⁻¹'
      ((schemeComplexPointImage f ⁻¹' U) ∩ (schemeComplexPointImage f ⁻¹' V))
    have hD : IsOpen D := e.val.isOpen_inter_preimage_symm
      ((U.isOpen.preimage (schemeComplexPointImage_continuous f)).inter
        (V.isOpen.preimage (schemeComplexPointImage_continuous f)))
    have huD : u ∈ D := ⟨hu.1, hu.2, hpV⟩
    have hnorm : ContDiffAt ℝ ∞ (fun z => Complex.normSq
        (schemeFrameTransition f n E α (β.tensorPower k) (e.val.symm z))) u := by
      apply BlanchardWeight.BlanchardData.contDiffAt_normSq_comp
      filter_upwards [hD.mem_nhds huD] with z hz
      exact FactorizedWeightForm.differentiableAt_comp_chart_symm e hz.1
        (schemeFrameTransition_holomorphicAt f n E α (β.tensorPower k) _
          hz.2.1 hz.2.2).mdifferentiableAt
    have hpow : ContDiffAt ℝ ∞ (fun z => H.frameNormSq β (e.val.symm z) ^ k) u :=
      ((H.smooth β e).pow k).contDiffAt
        ((e.val.isOpen_inter_preimage_symm
          (V.isOpen.preimage (schemeComplexPointImage_continuous f))).mem_nhds ⟨hu.1, hpV⟩)
    have heq : (fun z => H.tensorFrameNormSq a k α (e.val.symm z)) =ᶠ[𝓝 u]
        fun z => Complex.normSq (schemeFrameTransition f n E α (β.tensorPower k) (e.val.symm z)) *
          H.frameNormSq β (e.val.symm z) ^ k := by
      filter_upwards [hD.mem_nhds huD] with z hz
      exact H.tensorFrameNormSq_eq a k α β _ hz.2.1 hz.2.2
    exact ((hnorm.mul hpow).congr_of_eventuallyEq heq).contDiffWithinAt

/-- The induced metric has the exact kth power of the SAME original metric
in EVERY original power frame, including k=0. -/
theorem tensorPower_frame (a : LineBundleAtlas L) {U : X.Opens}
    (α : LocalBundleFrame L U) (k : ℕ) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    (H.tensorPower a k).frameNormSq (α.tensorPower k) p = H.frameNormSq α p ^ k := by
  change H.tensorFrameNormSq a k (α.tensorPower k) p = _
  rw [H.tensorFrameNormSq_eq a k (α.tensorPower k) α p hp hp,
    schemeFrameTransition_self f n E (α.tensorPower k) p hp,
    Complex.normSq_one, one_mul]

/-- The WHOLE actual induced tensor curvature equals k times the fixed
original curvature on every actual chart target, also in degree zero. -/
theorem curvature_tensorPower (a : LineBundleAtlas L) (k : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ((H.tensorPower a k).curvature (a.tensorPower k)).val.GeometricallyEq
      ((k : ℝ) • H.curvature a).val := by
  let := E.isSeparated
  let := E.quasiCompact
  intro e u hu
  let Z := schemeLineBundleCore f n E a
  let U := a.opens (Z.indexAt (e.val.symm u))
  let α := a.frame (Z.indexAt (e.val.symm u))
  have hp : schemeComplexPointImage f (e.val.symm u) ∈ U := Z.mem_baseSet_at _
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  change ((H.tensorPower a k).curvature (a.tensorPower k)).val.coeff e u =
    (k : ℝ) • (H.curvature a).val.coeff e u
  rw [(H.tensorPower a k).curvature_coeff_frame (a.tensorPower k) (α.tensorPower k) e hu hp,
    H.curvature_coeff_frame a α e hu hp]
  have heq : (fun z => -Real.log ((H.tensorPower a k).frameNormSq
      (α.tensorPower k) (e.val.symm z))) =ᶠ[𝓝 u]
      fun z => (k : ℝ) • (-Real.log (H.frameNormSq α (e.val.symm z))) := by
    filter_upwards [hD.mem_nhds ⟨hu, hp⟩] with z hz
    rw [H.tensorPower_frame a α k _ hz.2, Real.log_pow]
    simp only [smul_eq_mul]
    ring
  exact (smoothDDC_congr heq).trans
    (smoothDDC_smul hD (H.frame_log_smooth α e).neg (k : ℝ) ⟨hu, hp⟩)

/-- The actual induced tensor metric has the kth scalar multiple of the SAME
original real Bott-Chern class, including its zero-degree identity. -/
theorem chernClass_tensorPower (a : LineBundleAtlas L) (k : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (H.tensorPower a k).chernClass (a.tensorPower k) = (k : ℝ) • H.chernClass a := by
  let := E.isSeparated
  let := E.quasiCompact
  change RealBottChern.ofRepresentative ((H.tensorPower a k).curvature (a.tensorPower k)) =
    (k : ℝ) • RealBottChern.ofRepresentative (H.curvature a)
  rw [← RealBottChern.ofRepresentative_smul]
  exact RealBottChern.ofRepresentative_eq_of_geometricallyEq (H.curvature_tensorPower a k)

end SchemeLineBundleMetric

/-- The coefficient of the SAME actual global section in an original frame. -/
private def originalFrameCoefficient {L : X.Modules} {U : X.Opens}
    (α : LocalBundleFrame L U) (s : bundleSections L ⊤) : Γ(X, U) :=
  α.coefficients (𝟙 U) (L.val.map (homOfLE le_top).op s)

private theorem originalFrameCoefficient_restrict {L : X.Modules} {U W : X.Opens}
    (α : LocalBundleFrame L U) (i : W ⟶ U) (s : bundleSections L ⊤) :
    α.coefficients i (L.val.map (homOfLE le_top).op s) =
      X.sheaf.obj.map i.op (originalFrameCoefficient α s) := by
  have h := α.coefficients_restrict (𝟙 U) i (L.val.map (homOfLE le_top).op s)
  have hi : (homOfLE (le_top : U ≤ ⊤)).op ≫ i.op =
      (homOfLE (le_top : W ≤ ⊤)).op := Subsingleton.elim _ _
  rw [← PresheafOfModules.map_comp_apply, hi] at h
  simpa only [Category.comp_id, originalFrameCoefficient] using h

/-- Canonical analytic realization of the literal original frame coefficient. -/
private def originalFrameFunction {L : X.Modules} {U : X.Opens}
    (α : LocalBundleFrame L U) (s : bundleSections L ⊤) : SchemeComplexPoint f → ℂ :=
  schemeOpenRegularFunction f n E U (originalFrameCoefficient α s)

private theorem originalFrameFunction_restrict {L : X.Modules} {U W : X.Opens}
    (α : LocalBundleFrame L U) (hWU : W ≤ U) (s : bundleSections L ⊤) :
    EqOn (schemeOpenRegularFunction f n E W
      (α.coefficients (homOfLE hWU) (L.val.map (homOfLE le_top).op s)))
      (originalFrameFunction f n E α s) (schemeComplexPointImage f ⁻¹' W) := by
  rw [originalFrameCoefficient_restrict α (homOfLE hWU) s]
  exact schemeOpenRegularFunction_restrict f n E W U hWU _

/-- The original coefficient theorem is transported by the SAME actual
regular-function maps; no analytic section-gluing certificate is assumed. -/
private theorem originalFrameFunction_transition {L : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (s : bundleSections L ⊤)
    (p : SchemeComplexPoint f) (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V) :
    originalFrameFunction f n E β s p =
      schemeFrameTransition f n E α β p * originalFrameFunction f n E α s p := by
  let W : X.Opens := U ⊓ V
  let i : W ⟶ U := homOfLE inf_le_left
  let j : W ⟶ V := homOfLE inf_le_right
  let t := L.val.map (homOfLE (le_top : W ≤ ⊤)).op s
  have hpW : schemeComplexPointImage f p ∈ W := ⟨hpU, hpV⟩
  calc
    _ = schemeOpenRegularFunction f n E W (β.coefficients j t) p :=
      (originalFrameFunction_restrict f n E β inf_le_right s hpW).symm
    _ = schemeOpenRegularFunction f n E W
        ((localBundleFrameTransition α β i j : Γ(X, W)ˣ).val * α.coefficients i t) p :=
      congrArg (fun r : Γ(X, W) => schemeOpenRegularFunction f n E W r p)
        (localBundleFrameTransition_coefficients α β i j t)
    _ = schemeOpenRegularFunction f n E W (localBundleFrameTransition α β i j).val p *
        schemeOpenRegularFunction f n E W (α.coefficients i t) p :=
      schemeOpenRegularFunction_mul f n E W _ _ hpW
    _ = _ := congrArg₂ (· * ·) rfl
      (originalFrameFunction_restrict f n E α inf_le_left s hpW)

/-- The SAME actual original global section is realized in the SAME native
power bundle. This construction is independent of every Hermitian metric. -/
def schemeAnalyticPowerSection {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (p : SchemeComplexPoint f) :
    (schemeLineBundleCore f n E (a.tensorPower k)).Fiber p := by
  let Z := schemeLineBundleCore f n E (a.tensorPower k)
  change ℂ
  exact originalFrameFunction f n E ((a.frame (Z.indexAt p)).tensorPower k) s p

/-- In EVERY actual original frame of L^k the native fibre coordinate is the
canonical realization of the SAME original restricted algebraic coefficient. -/
theorem schemeAnalyticPowerSection_frame {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) {U : X.Opens}
    (α : LocalBundleFrame (bundleTensorPower L k) U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    schemeLineBundleFibreFrame f n E (a.tensorPower k) α p hp
      (schemeAnalyticPowerSection f n E a k s p) =
        schemeOpenRegularFunction f n E U
          (α.coefficients (𝟙 U) ((bundleTensorPower L k).val.map (homOfLE le_top).op s)) p := by
  let Z := schemeLineBundleCore f n E (a.tensorPower k)
  let β := (a.frame (Z.indexAt p)).tensorPower k
  change schemeFrameTransition f n E β α p * originalFrameFunction f n E β s p =
    originalFrameFunction f n E α s p
  exact (originalFrameFunction_transition f n E β α s p (Z.mem_baseSet_at p) hp).symm

/-- Original holomorphic coefficients internally give global continuity of
the actual native total-space section map. No smooth bundle structure is assumed. -/
theorem schemeAnalyticPowerSection_continuous {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) :
    Continuous (fun p => Bundle.TotalSpace.mk' ℂ p (schemeAnalyticPowerSection f n E a k s p)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let Z := schemeLineBundleCore f n E (a.tensorPower k)
  refine continuous_iff_continuousAt.mpr fun p => ?_
  apply (FiberBundle.continuousAt_section (E := Z.Fiber)
    (s := schemeAnalyticPowerSection f n E a k s) ℂ p).mpr
  let U := a.opens (Z.indexAt p)
  let α := (a.frame (Z.indexAt p)).tensorPower k
  have hp : schemeComplexPointImage f p ∈ U := Z.mem_baseSet_at p
  have hU : IsOpen (schemeComplexPointImage f ⁻¹' U) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  have hC : ContinuousAt (originalFrameFunction f n E α s) p :=
    (schemeOpenRegularFunction_holomorphicAt f n E U (originalFrameCoefficient α s) p hp).mdifferentiableAt.continuousAt
  have heq : (fun q => (FiberBundle.trivializationAt ℂ Z.Fiber p
      ⟨q, schemeAnalyticPowerSection f n E a k s q⟩).2) =ᶠ[𝓝 p]
      originalFrameFunction f n E α s := by
    filter_upwards [hU.mem_nhds hp] with q hq
    change schemeLineBundleFibreFrame f n E (a.tensorPower k) α q hq
      (schemeAnalyticPowerSection f n E a k s q) = originalFrameFunction f n E α s q
    exact schemeAnalyticPowerSection_frame f n E a k s α q hq
  exact hC.congr_of_eventuallyEq heq

namespace SchemeLineBundleMetric

variable {f n E} {L : X.Modules} (H : SchemeLineBundleMetric f n E L)

private theorem nativeHermitian_re_self_frame (a : LineBundleAtlas L) {U : X.Opens}
    (α : LocalBundleFrame L U) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U)
    (v : (schemeLineBundleCore f n E a).Fiber p) :
    (H.nativeHermitian a p v v).re =
      Complex.normSq (schemeLineBundleFibreFrame f n E a α p hp v) * H.frameNormSq α p := by
  rw [H.nativeHermitian_frame a α p hp v v, mul_assoc, ← Complex.normSq_eq_conj_mul_self]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_comm _ _

/-- The fixed original H measures the SAME original algebraic section in the
actual native power bundle, without choosing any fresh section/divisor metric. -/
def sectionNormSq (a : LineBundleAtlas L) (k : ℕ) (s : bundlePowerGlobalSections L k)
    (p : SchemeComplexPoint f) : ℝ :=
  ((H.tensorPower a k).nativeHermitian (a.tensorPower k) p
    (schemeAnalyticPowerSection f n E a k s p) (schemeAnalyticPowerSection f n E a k s p)).re

/-- The literal original section coefficient and the SAME original frame
weight give the exact squared norm in every original frame, for all degrees. -/
theorem sectionNormSq_frame (a : LineBundleAtlas L) {U : X.Opens}
    (α : LocalBundleFrame L U) (k : ℕ) (s : bundlePowerGlobalSections L k)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ U) :
    H.sectionNormSq a k s p = Complex.normSq (schemeOpenRegularFunction f n E U
      ((α.tensorPower k).coefficients (𝟙 U)
        ((bundleTensorPower L k).val.map (homOfLE le_top).op s)) p) * H.frameNormSq α p ^ k := by
  rw [sectionNormSq,
    (H.tensorPower a k).nativeHermitian_re_self_frame (a.tensorPower k) (α.tensorPower k) p hp,
    schemeAnalyticPowerSection_frame f n E a k s (α.tensorPower k) p hp,
    H.tensorPower_frame a α k p hp]

/-- Actual local holomorphic coefficients make the SAME original section's
norm smooth on the whole original manifold, including every section zero. -/
theorem sectionNormSq_chartSmooth (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ChartSmooth (n := n) (H.sectionNormSq a k s) := by
  let := E.isSeparated
  let := E.quasiCompact
  intro e u hu
  let Z := schemeLineBundleCore f n E a
  let U := a.opens (Z.indexAt (e.val.symm u))
  let α := a.frame (Z.indexAt (e.val.symm u))
  have hp : schemeComplexPointImage f (e.val.symm u) ∈ U := Z.mem_baseSet_at _
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) :=
    e.val.isOpen_inter_preimage_symm (U.isOpen.preimage (schemeComplexPointImage_continuous f))
  have hsm := (H.tensorPower a k).nativeHermitian_local_smooth (α.tensorPower k)
    (originalFrameFunction f n E (α.tensorPower k) s)
    (fun p hp => schemeOpenRegularFunction_holomorphicAt f n E U
      (originalFrameCoefficient (α.tensorPower k) s) p hp) e
  have heq : (fun z => H.sectionNormSq a k s (e.val.symm z)) =ᶠ[𝓝 u]
      fun z => (H.tensorPower a k).frameNormSq (α.tensorPower k) (e.val.symm z) *
        Complex.normSq (originalFrameFunction f n E (α.tensorPower k) s (e.val.symm z)) := by
    filter_upwards [hD.mem_nhds ⟨hu, hp⟩] with z hz
    rw [H.sectionNormSq_frame a α k s _ hz.2, H.tensorPower_frame a α k _ hz.2]
    change Complex.normSq (originalFrameFunction f n E (α.tensorPower k) s (e.val.symm z)) *
      H.frameNormSq α (e.val.symm z) ^ k =
        H.frameNormSq α (e.val.symm z) ^ k *
          Complex.normSq (originalFrameFunction f n E (α.tensorPower k) s (e.val.symm z))
    exact mul_comm _ _
  exact ((hsm.contDiffAt (hD.mem_nhds ⟨hu, hp⟩)).congr_of_eventuallyEq heq).contDiffWithinAt

/-- The actual original degree-zero unit has squared norm one. -/
theorem sectionNormSq_one (a : LineBundleAtlas L) (p : SchemeComplexPoint f) :
    H.sectionNormSq a 0 (bundlePowerGlobalOne L) p = 1 := by
  let Z := schemeLineBundleCore f n E a
  let i := Z.indexAt p
  have hp : schemeComplexPointImage f p ∈ a.opens i := Z.mem_baseSet_at p
  rw [H.sectionNormSq_frame a (a.frame i) 0 (bundlePowerGlobalOne L) p hp]
  change Complex.normSq (schemeOpenRegularFunction f n E (a.opens i)
    (atlasPowerGlobalCoefficients a 0 i (bundlePowerGlobalOne L)) p) *
      H.frameNormSq (a.frame i) p ^ 0 = 1
  rw [atlasPowerGlobalCoefficients_one]
  erw [schemeOpenRegularFunction_one f n E (a.opens i) hp]
  simp only [Complex.normSq_one, pow_zero, mul_one]

/-- The actual original sheaf-glued homogeneous product obeys the whole
squared-norm product identity under the SAME fixed H in every degree. -/
theorem sectionNormSq_mul (a : LineBundleAtlas L) (k l : ℕ)
    (s : bundlePowerGlobalSections L k) (t : bundlePowerGlobalSections L l)
    (p : SchemeComplexPoint f) :
    H.sectionNormSq a (k + l) (atlasPowerGlobalMul a k l s t) p =
      H.sectionNormSq a k s p * H.sectionNormSq a l t p := by
  let Z := schemeLineBundleCore f n E a
  let i := Z.indexAt p
  have hp : schemeComplexPointImage f p ∈ a.opens i := Z.mem_baseSet_at p
  rw [H.sectionNormSq_frame a (a.frame i) (k + l) (atlasPowerGlobalMul a k l s t) p hp,
    H.sectionNormSq_frame a (a.frame i) k s p hp,
    H.sectionNormSq_frame a (a.frame i) l t p hp]
  change Complex.normSq (schemeOpenRegularFunction f n E (a.opens i)
    (atlasPowerGlobalCoefficients a (k + l) i (atlasPowerGlobalMul a k l s t)) p) * _ =
      (Complex.normSq (schemeOpenRegularFunction f n E (a.opens i)
        (atlasPowerGlobalCoefficients a k i s) p) * _) *
      (Complex.normSq (schemeOpenRegularFunction f n E (a.opens i)
        (atlasPowerGlobalCoefficients a l i t) p) * _)
  rw [atlasPowerGlobalMul_coefficients]
  erw [schemeOpenRegularFunction_mul f n E (a.opens i) _ _ hp]
  rw [Complex.normSq_mul, pow_add]
  ring

/-- Vanishing of the genuine squared norm is exactly vanishing of the SAME
actual fibre value, not vanishing of the entire original section or germ. -/
theorem sectionNormSq_eq_zero_iff (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (p : SchemeComplexPoint f) :
    H.sectionNormSq a k s p = 0 ↔ schemeAnalyticPowerSection f n E a k s p = 0 := by
  constructor
  · intro h
    by_contra hv
    have hpos : 0 < H.sectionNormSq a k s p :=
      (H.tensorPower a k).nativeHermitian_positive (a.tensorPower k) p _ hv
    exact (ne_of_gt hpos) h
  · intro hv
    simp only [sectionNormSq, hv, map_zero, Complex.zero_re]

/-- The SAME actual original section norm is nonnegative in all dimensions
and all degrees, including the zero section. -/
theorem sectionNormSq_nonneg (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (p : SchemeComplexPoint f) :
    0 ≤ H.sectionNormSq a k s p := by
  by_cases hv : schemeAnalyticPowerSection f n E a k s p = 0
  · rw [(H.sectionNormSq_eq_zero_iff a k s p).mpr hv]
  · exact ((H.tensorPower a k).nativeHermitian_positive (a.tensorPower k) p _ hv).le

/-- The original squared-log convention applied to the SAME fixed-metric
section norm, preserving zero as bottom rather than real log zero. -/
def sectionLogNormSq (a : LineBundleAtlas L) (k : ℕ) (s : bundlePowerGlobalSections L k)
    (p : SchemeComplexPoint f) : EReal :=
  ENNReal.log (ENNReal.ofReal (H.sectionNormSq a k s p))

/-- Exact extended-valued original coefficient formula with the SAME frame
weight, including every actual zero and degree zero. -/
theorem sectionLogNormSq_frame (a : LineBundleAtlas L) {U : X.Opens}
    (α : LocalBundleFrame L U) (k : ℕ) (s : bundlePowerGlobalSections L k)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ U) :
    H.sectionLogNormSq a k s p = SGPT.Foundations.Analysis.logNormSq (schemeOpenRegularFunction f n E U
      ((α.tensorPower k).coefficients (𝟙 U)
        ((bundleTensorPower L k).val.map (homOfLE le_top).op s)) p) +
      (((k : ℝ) * Real.log (H.frameNormSq α p) : ℝ) : EReal) := by
  rw [sectionLogNormSq, H.sectionNormSq_frame a α k s p hp,
    ENNReal.ofReal_mul (Complex.normSq_nonneg _), ENNReal.log_mul_add,
    ENNReal.log_ofReal_of_pos (pow_pos (H.positive α p hp) k), Real.log_pow]
  congr 1
  simp only [SGPT.Foundations.Analysis.logNormSq, Complex.normSq_eq_norm_sq]

/-- The pole set is EXACTLY the actual original section's fibre zero set.
No nonzero-germ or theta-PSH nondegeneracy premise is hidden here. -/
theorem sectionLogNormSq_eq_bot_iff (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (p : SchemeComplexPoint f) :
    H.sectionLogNormSq a k s p = ⊥ ↔ schemeAnalyticPowerSection f n E a k s p = 0 := by
  rw [sectionLogNormSq, ENNReal.log_eq_bot_iff, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    exact (H.sectionNormSq_eq_zero_iff a k s p).mp
      (le_antisymm h (H.sectionNormSq_nonneg a k s p))
  · intro h
    exact le_of_eq ((H.sectionNormSq_eq_zero_iff a k s p).mpr h)

end SchemeLineBundleMetric

end SGPT.Okounkov
