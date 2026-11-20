import SGPT.Okounkov.TranscendentalWNVolumeGlobalLegendre
import SGPT.Okounkov.TranscendentalWNVolumeLine
import SGPT.Toric.ProjectiveTorusAction
import SGPT.Siu.LocalDivisorBound
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
import SGPT.Foundations.Analysis.FirstPass.LocalPotentials

/-!
# Potentials on `Y × ℙ¹` and their partial Legendre transforms (package WN-VF2)

Blueprint `claude-tok-wn-vf2` (sub-lemmas of `tok-wn-vf:punctured`); WN21 §4.

On the product `Y × ℙ¹` (TN's product atlas `prodChart e e'`, `open scoped
ProductComplexManifold`) of a complex manifold `Y` of dimension `N` with `ℙ¹`, let
`Θ = p₁^*θ + b p₂^*ω_FS` (`productLineForm`).  In the affine coordinate `τ` of `ℙ¹ \ {∞}`
(`projectiveModelChart false`), `ω_FS = dd^c log (1 + |τ|²)`, so for a `Θ`-psh `w` on `Y × ℙ¹`

  `u(y, τ) = w(y, [τ : 1]) + b log (1 + |τ|²)`   (`affineTwist`)

is `π_Y^*θ`-psh on `Y × ℂ` (`isPullbackThetaPshPunctured_affineTwist`); it is circle-invariant
when `w` is invariant under the rotations of `ℙ¹` (`isCircleInvariant_affineTwist`); a `Θ`-psh
`w` stays `Θ`-psh after a rotation (`thetaPlurisubharmonic_comp_rotation`).  The global
non-pluripolar measure of `w`, pulled back to `Y × ℂ` along `(y, τ) ↦ (y, [τ : 1])`, is the
measure `ν` of `GlobalLegendreMAStatement` for `u` (`isPuncturedProductMAMeasure_comap`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Toric

/-! ### Generalities -/

theorem IsSmoothLocalPotential.congr_eqOn {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {θ : SmoothRealForm n M 2} {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ σ : ComplexModel n → ℝ} (h : IsSmoothLocalPotential θ e W ρ)
    (heq : EqOn ρ σ W) : IsSmoothLocalPotential θ e W σ := by
  refine ⟨h.1, h.2.1, h.2.2.1.congr fun z hz => (heq hz).symm, fun z hz => ?_⟩
  rw [← smoothDDC_congr (heq.eventuallyEq_of_mem (h.1.mem_nhds hz))]
  exact h.2.2.2 hz

/-- `projectiveModelEquiv (x 0) = x` on `ℂ¹`. -/
theorem projectiveModelEquiv_apply_coord (x : ComplexModel 1) : projectiveModelEquiv (x 0) = x := by
  ext i
  fin_cases i
  exact projectiveModelEquiv_apply_zero _

theorem projectiveModelChart_target_eq (β : Bool) : (projectiveModelChart β).target = univ := by
  ext z; simp [projectiveModelChart, projectiveQuotientScalarChart_target]

/-- The local potential `log (1 + |τ|²)` of `ω_FS` in a native chart. -/
theorem isSmoothLocalPotential_projectiveFS (e : ComplexChart 1 ProjectiveLine) :
    IsSmoothLocalPotential projectiveNativeFSClosedForm.val e e.val.target projectiveFSPotential :=
  ⟨e.val.open_target, subset_rfl, contDiff_projectiveFSPotential.contDiffOn, fun _ _ => rfl⟩

/-! ### The product form and product charts -/

section Product

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- `Θ = p₁^*θ + b p₂^*ω_FS` on `Y × ℙ¹`. -/
def productLineForm (θ : ClosedRealOneOneForm N Y) (b : ℝ) :
    ClosedRealOneOneForm (N + 1) (Y × ProjectiveLine) :=
  ClosedRealOneOneForm.pullback (contMDiff_fst (n := N) (m := 1)) θ +
    b • ClosedRealOneOneForm.pullback (contMDiff_snd (n := N) (m := 1))
      projectiveNativeFSClosedForm

/-- The product chart `e × (affine chart β)`. -/
def productLineChart (e : ComplexChart N Y) (β : Bool) :
    ComplexChart (N + 1) (Y × ProjectiveLine) :=
  ⟨prodChart e.val (projectiveModelChart β), mem_image2_of_mem e.property ⟨β, rfl⟩⟩

omit [IsComplexManifold N Y] in
/-- Every chart of `Y × ℙ¹` is a product chart. -/
theorem exists_eq_productLineChart (E : ComplexChart (N + 1) (Y × ProjectiveLine)) :
    ∃ (e : ComplexChart N Y) (β : Bool), E = productLineChart e β := by
  obtain ⟨a, ha, f, hf, hE⟩ := E.property
  obtain ⟨β, rfl⟩ := (mem_projectiveNativeAtlas_iff f).mp hf
  exact ⟨⟨a, ha⟩, β, Subtype.ext hE.symm⟩

/-- The coordinate domain `W × ℂ` of the product chart. -/
def productLineDomain (W : Set (ComplexModel N)) : Set (ComplexModel (N + 1)) :=
  (prodModelEquiv N 1).symm ⁻¹' (W ×ˢ univ)

theorem isOpen_productLineDomain {W : Set (ComplexModel N)} (hW : IsOpen W) :
    IsOpen (productLineDomain W) :=
  (hW.prod isOpen_univ).preimage (prodModelEquiv N 1).symm.continuous

omit [IsComplexManifold N Y] in
theorem productLineDomain_subset_target {e : ComplexChart N Y} {W : Set (ComplexModel N)}
    (hW : W ⊆ e.val.target) (β : Bool) :
    productLineDomain W ⊆ (productLineChart e β).val.target := by
  intro v hv
  change v ∈ (prodChart e.val (projectiveModelChart β)).target
  rw [prodChart_target, projectiveModelChart_target_eq]
  exact ⟨hW hv.1, mem_univ _⟩

omit [IsComplexManifold N Y] in
@[simp] theorem productLineChart_symm_apply (e : ComplexChart N Y) (β : Bool)
    (v : ComplexModel (N + 1)) :
    (productLineChart e β).val.symm v =
      (e.val.symm ((prodModelEquiv N 1).symm v).1,
        (projectiveModelChart β).symm ((prodModelEquiv N 1).symm v).2) := rfl

/-- The local potential `ρ(z) + b log (1 + |τ|²)` of `Θ` in a product chart. -/
def productLinePotential (ρ : ComplexModel N → ℝ) (b : ℝ) (v : ComplexModel (N + 1)) : ℝ :=
  ρ ((prodModelEquiv N 1).symm v).1 + b * projectiveFSPotential ((prodModelEquiv N 1).symm v).2

/-- **The local potential of `Θ` in a product chart.** -/
theorem isSmoothLocalPotential_productLineForm {θ : ClosedRealOneOneForm N Y}
    {e : ComplexChart N Y} {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e W ρ) (b : ℝ) (β : Bool) :
    IsSmoothLocalPotential (productLineForm θ b).val (productLineChart e β)
      (productLineDomain W) (productLinePotential ρ b) := by
  set E := productLineChart e β
  set c : ComplexChart 1 ProjectiveLine := projectiveNativeChart β
  have hDt := productLineDomain_subset_target (Y := Y) hρ.2.1 β
  have hDo := isOpen_productLineDomain (N := N) hρ.1
  have hfst : productLineDomain W ⊆ potentialDomain (Prod.fst : Y × ProjectiveLine → Y) E e W := by
    intro v hv
    have h1 : ((prodModelEquiv N 1).symm v).1 ∈ e.val.target := hρ.2.1 hv.1
    refine ⟨⟨hDt hv, ?_⟩, ?_⟩
    · change e.val.symm ((prodModelEquiv N 1).symm v).1 ∈ e.val.source
      exact e.val.map_target h1
    · change e.val (e.val.symm ((prodModelEquiv N 1).symm v).1) ∈ W
      rw [e.val.right_inv h1]; exact hv.1
  have hsnd : productLineDomain W ⊆
      potentialDomain (Prod.snd : Y × ProjectiveLine → ProjectiveLine) E c c.val.target := by
    intro v hv
    have h2 : ((prodModelEquiv N 1).symm v).2 ∈ (projectiveModelChart β).target := by
      rw [projectiveModelChart_target_eq]; exact mem_univ _
    refine ⟨⟨hDt hv, ?_⟩, ?_⟩
    · change (projectiveModelChart β).symm ((prodModelEquiv N 1).symm v).2 ∈
        (projectiveModelChart β).source
      exact (projectiveModelChart β).map_target h2
    · change _ ∈ (projectiveModelChart β).target
      rw [projectiveModelChart_target_eq]; exact mem_univ _
  have hp1 := (isSmoothLocalPotential_pullback (contMDiff_fst (n := N) (m := 1)) E hρ).mono hDo hfst
  have hp2 := (isSmoothLocalPotential_pullback (contMDiff_snd (n := N) (m := 1)) E
    (isSmoothLocalPotential_projectiveFS c)).mono hDo hsnd
  have hsum := FirstPass.LocalPotentials.localPotential_add
    (a := ClosedRealOneOneForm.pullback (contMDiff_fst (n := N) (m := 1)) θ)
    (b := b • ClosedRealOneOneForm.pullback (contMDiff_snd (n := N) (m := 1))
      projectiveNativeFSClosedForm) hp1
    (FirstPass.LocalPotentials.localPotential_smul
      (a := ClosedRealOneOneForm.pullback (contMDiff_snd (n := N) (m := 1))
        projectiveNativeFSClosedForm) hp2 b)
  refine IsSmoothLocalPotential.congr_eqOn hsum fun v hv => ?_
  have h1 : ((prodModelEquiv N 1).symm v).1 ∈ e.val.target := hρ.2.1 hv.1
  have h2 : ((prodModelEquiv N 1).symm v).2 ∈ (projectiveModelChart β).target := by
    rw [projectiveModelChart_target_eq]; exact mem_univ _
  simp only [Function.comp_apply, coordinateMap, productLinePotential, smul_eq_mul]
  change ρ (e.val (e.val.symm ((prodModelEquiv N 1).symm v).1)) + b * projectiveFSPotential
      ((projectiveModelChart β) ((projectiveModelChart β).symm ((prodModelEquiv N 1).symm v).2)) =
    _
  rw [e.val.right_inv h1, (projectiveModelChart β).right_inv h2]

/-- **The corrected function of a `Θ`-psh potential in a product chart is psh.** -/
theorem plurisubharmonicOn_productLine_corrected {θ : ClosedRealOneOneForm N Y} {b : ℝ}
    {w : Y × ProjectiveLine → EReal} (hw : ThetaPlurisubharmonic (productLineForm θ b).val w)
    {e : ComplexChart N Y} {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e W ρ) (β : Bool) :
    PlurisubharmonicOn (fun v => w ((productLineChart e β).val.symm v) +
      (productLinePotential ρ b v : EReal)) (productLineDomain W) :=
  ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hw _
    (isSmoothLocalPotential_productLineForm hρ b β)

end Product

/-! ### The affine twist -/

section Twist

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- The point `[τ : 1]` of `ℙ¹`. -/
def affinePoint (τ : ℂ) : ProjectiveLine := (projectiveModelChart false).symm (projectiveModelEquiv τ)

/-- `u(y, τ) = w(y, [τ : 1]) + b log (1 + |τ|²)` (WN21 §4: `u = ũ + b log (1 + |τ|²) + c log W`
when `w = ũ + c log W` is read on `Y × ℙ¹`). -/
def affineTwist (w : Y × ProjectiveLine → EReal) (b : ℝ) (y : Y) (τ : ℂ) : EReal :=
  w (y, affinePoint τ) + ((b * Real.log (1 + ‖τ‖ ^ 2) : ℝ) : EReal)

/-- The linear map `(z, τ) ↦ (z, τ)` from `ℂᴺ × ℂ` to the product model. -/
def twistLinear (N : ℕ) : ComplexModel N × ℂ →L[ℂ] ComplexModel (N + 1) :=
  ((prodModelEquiv N 1 : ComplexModel N × ComplexModel 1 →L[ℂ] ComplexModel (N + 1))).comp
    ((ContinuousLinearMap.id ℂ (ComplexModel N)).prodMap
      (projectiveModelEquiv : ℂ →L[ℂ] ComplexModel 1))

@[simp] theorem prodModelEquiv_symm_twistLinear (p : ComplexModel N × ℂ) :
    (prodModelEquiv N 1).symm (twistLinear N p) = (p.1, projectiveModelEquiv p.2) := by
  simp [twistLinear]; rfl

theorem projectiveFSPotential_projectiveModelEquiv (τ : ℂ) :
    projectiveFSPotential (projectiveModelEquiv τ) = Real.log (1 + ‖τ‖ ^ 2) := by
  rw [projectiveFSPotential_eq, projectiveModelEquiv_apply_zero, Complex.sq_norm]

omit [IsComplexManifold N Y] in
theorem stripChartFunction_affineTwist (w : Y × ProjectiveLine → EReal) (b : ℝ)
    (e : ComplexChart N Y) (ρ : ComplexModel N → ℝ) (p : ComplexModel N × ℂ) :
    stripChartFunction (affineTwist w b) e ρ p =
      w ((productLineChart e false).val.symm (twistLinear N p)) +
        (productLinePotential ρ b (twistLinear N p) : EReal) := by
  simp only [stripChartFunction, affineTwist, productLineChart_symm_apply,
    prodModelEquiv_symm_twistLinear, productLinePotential, projectiveFSPotential_projectiveModelEquiv,
    affinePoint]
  rw [add_assoc, ← EReal.coe_add, add_comm (b * _)]

/-- **`u ∈ PSH(Y × ℂ, π_Y^*θ)`** (`tok-wn-vf:punctured`): the affine twist of a `Θ`-psh
potential is `π_Y^*θ`-psh on `Y × ℂ*`, with any local potential of `θ`. -/
theorem plurisubharmonicOn_stripChartFunction_affineTwist {θ : ClosedRealOneOneForm N Y} {b : ℝ}
    {w : Y × ProjectiveLine → EReal} (hw : ThetaPlurisubharmonic (productLineForm θ b).val w)
    {e : ComplexChart N Y} {W : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e W ρ) :
    PlurisubharmonicOn (stripChartFunction (affineTwist w b) e ρ) (W ×ˢ univ) := by
  have h := (plurisubharmonicOn_productLine_corrected hw hρ false).comp_continuousLinearMap
    (twistLinear N)
  have hpre : twistLinear N ⁻¹' productLineDomain W = W ×ˢ univ := by
    ext p; simp [productLineDomain]
  rw [hpre] at h
  convert h using 1
  funext p
  exact stripChartFunction_affineTwist w b e ρ p

theorem isPullbackThetaPshPunctured_affineTwist {θ : ClosedRealOneOneForm N Y} {b : ℝ}
    {w : Y × ProjectiveLine → EReal} (hw : ThetaPlurisubharmonic (productLineForm θ b).val w) :
    IsPullbackThetaPshPunctured θ.val (affineTwist w b) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ⟩ := Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e z hz
  exact ⟨W, ρ, hzW, hρ, (plurisubharmonicOn_stripChartFunction_affineTwist hw hρ).mono
    (prod_mono subset_rfl (subset_univ _))⟩

/-! ### Rotations -/

/-- The rotation `(y, [v₀ : v₁]) ↦ (y, [a v₀ : v₁])`. -/
def lineRotation (a : ℂˣ) (q : Y × ProjectiveLine) : Y × ProjectiveLine :=
  (q.1, projectiveTorusAction a q.2)

theorem affinePoint_mul (a : ℂˣ) (τ : ℂ) :
    affinePoint ((a : ℂ) * τ) = projectiveTorusAction a (affinePoint τ) := by
  rw [affinePoint, affinePoint, projectiveTorusAction_chart_symm]
  congr 1
  simp only [projectiveTorusChartFactor, Bool.false_eq_true, if_false]
  rw [show (a : ℂ) * τ = (a : ℂ) • τ from rfl, map_smul]

omit [TopologicalSpace Y] in
/-- **Circle invariance of the twist** from rotation invariance of `w`. -/
theorem isCircleInvariant_affineTwist {w : Y × ProjectiveLine → EReal} (b : ℝ)
    (hrot : ∀ a : ℂˣ, ‖(a : ℂ)‖ = 1 → ∀ q, w (lineRotation a q) = w q) :
    IsCircleInvariant (affineTwist w b) := by
  intro y τ σ hτσ
  by_cases hτ : τ = 0
  · have hσ : σ = 0 := by
      rw [hτ, norm_zero] at hτσ; exact norm_eq_zero.mp hτσ.symm
    rw [hτ, hσ]
  have hτn : ‖τ‖ ≠ 0 := norm_ne_zero_iff.mpr hτ
  set a : ℂ := σ / τ
  have ha0 : a ≠ 0 := div_ne_zero (norm_ne_zero_iff.mp (hτσ ▸ hτn)) hτ
  have ha : ‖a‖ = 1 := by rw [norm_div, ← hτσ, div_self hτn]
  have hσa : σ = (Units.mk0 a ha0 : ℂ) * τ := by
    simp [a, div_mul_cancel₀ σ hτ]
  simp only [affineTwist]
  rw [← hτσ, hσa, affinePoint_mul]
  have := hrot (Units.mk0 a ha0) (by simpa using ha) (y, affinePoint τ)
  rw [show (y, projectiveTorusAction (Units.mk0 a ha0) (affinePoint τ)) =
    lineRotation (Units.mk0 a ha0) (y, affinePoint τ) from rfl, this]

/-- **A rotated `Θ`-psh potential is `Θ`-psh** (rotation invariance of `ω_FS`). -/
theorem thetaPlurisubharmonic_comp_rotation {θ : ClosedRealOneOneForm N Y} {b : ℝ}
    {w : Y × ProjectiveLine → EReal} (hw : ThetaPlurisubharmonic (productLineForm θ b).val w)
    {a : ℂˣ} (ha : ‖(a : ℂ)‖ = 1) :
    ThetaPlurisubharmonic (productLineForm θ b).val (fun q => w (lineRotation a q)) := by
  intro E v hv
  obtain ⟨e, β, rfl⟩ := exists_eq_productLineChart E
  have hv1 : ((prodModelEquiv N 1).symm v).1 ∈ e.val.target := by
    have h : v ∈ (prodChart e.val (projectiveModelChart β)).target := hv
    rw [prodChart_target] at h; exact h.1
  obtain ⟨W, ρ, hzW, hρ⟩ := Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e _ hv1
  set c := projectiveTorusChartFactor a β
  have hc : ‖c‖ = 1 := norm_projectiveTorusChartFactor ha β
  let M : ComplexModel (N + 1) →L[ℂ] ComplexModel (N + 1) :=
    ((prodModelEquiv N 1 : ComplexModel N × ComplexModel 1 →L[ℂ] ComplexModel (N + 1))).comp
      (((ContinuousLinearMap.id ℂ (ComplexModel N)).prodMap
        (c • ContinuousLinearMap.id ℂ (ComplexModel 1))).comp
        ((prodModelEquiv N 1).symm : ComplexModel (N + 1) →L[ℂ] ComplexModel N × ComplexModel 1))
  have hM : ∀ v', (prodModelEquiv N 1).symm (M v') =
      (((prodModelEquiv N 1).symm v').1, c • ((prodModelEquiv N 1).symm v').2) := by
    intro v'; simp [M]; rfl
  refine ⟨productLineDomain W, productLinePotential ρ b, ⟨hzW, mem_univ _⟩,
    isSmoothLocalPotential_productLineForm hρ b β, ?_⟩
  have h := (plurisubharmonicOn_productLine_corrected hw hρ β).comp_continuousLinearMap M
  have hpre : M ⁻¹' productLineDomain W = productLineDomain W := by
    ext v'; simp [productLineDomain, hM]
  rw [hpre] at h
  refine SGPT.Siu.plurisubharmonicOn_congr_of_isOpen (isOpen_productLineDomain hρ.1) h ?_
  intro v' _
  simp only [chartFunction, productLineChart_symm_apply, lineRotation, hM, productLinePotential]
  rw [projectiveFSPotential_smul hc, projectiveTorusAction_chart_symm]

end Twist

/-! ### The measure `ν` on `Y × ℂ` -/

section Measure

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

omit [IsComplexManifold N Y] in
theorem stripModelEquiv_apply (v : ComplexModel (N + 1)) :
    stripModelEquiv N v = (((prodModelEquiv N 1).symm v).1, ((prodModelEquiv N 1).symm v).2 0) :=
  rfl

omit [IsComplexManifold N Y] in
theorem twistLinear_stripModelEquiv (v : ComplexModel (N + 1)) :
    twistLinear N (stripModelEquiv N v) = v := by
  apply (prodModelEquiv N 1).symm.injective
  rw [prodModelEquiv_symm_twistLinear, stripModelEquiv_apply, projectiveModelEquiv_apply_coord]

omit [IsComplexManifold N Y] in
theorem stripModelEquiv_twistLinear (p : ComplexModel N × ℂ) :
    stripModelEquiv N (twistLinear N p) = p := by
  rw [stripModelEquiv_apply, prodModelEquiv_symm_twistLinear, projectiveModelEquiv_apply_zero]

/-- `(y, τ) ↦ (y, [τ : 1])`. -/
def affineEmbedding (p : Y × ℂ) : Y × ProjectiveLine := (p.1, affinePoint p.2)

omit [ChartedSpace (ComplexModel N) Y] [IsComplexManifold N Y] in
theorem isOpenEmbedding_affineEmbedding : Topology.IsOpenEmbedding (affineEmbedding (Y := Y)) := by
  have h1 : Topology.IsOpenEmbedding (projectiveModelChart false).symm :=
    (projectiveModelChart false).symm.isOpenEmbedding (by
      rw [OpenPartialHomeomorph.symm_source, projectiveModelChart_target_eq])
  have h2 : Topology.IsOpenEmbedding affinePoint :=
    h1.comp projectiveModelEquiv.toHomeomorph.isOpenEmbedding
  exact Topology.IsOpenEmbedding.id.prodMap h2

omit [IsComplexManifold N Y] in
/-- The inverse product chart followed by `affineEmbedding` is the inverse of the product chart
`e × (affine chart)`. -/
theorem affineEmbedding_productChartInverse (e : ComplexChart N Y) (v : ComplexModel (N + 1)) :
    affineEmbedding (productChartInverse e v) = (productLineChart e false).val.symm v := by
  rw [productLineChart_symm_apply]
  simp only [affineEmbedding, productChartInverse, affinePoint, stripModelEquiv_apply,
    projectiveModelEquiv_apply_coord]

theorem puncturedProductOpens_subset_productLineDomain (W : Opens (ComplexModel N)) :
    (puncturedProductOpens W : Set (ComplexModel (N + 1))) ⊆ productLineDomain W := by
  intro v hv
  exact ⟨by simpa [puncturedProductOpens, stripModelEquiv_apply] using hv.1, mem_univ _⟩

/-- The common patch of `w` in the product chart `e × (affine chart)` over `W × ℂ*`. -/
def productLinePatch (θ : ClosedRealOneOneForm N Y) (b : ℝ) {w : Y × ProjectiveLine → EReal}
    (e : ComplexChart N Y) (W : Opens (ComplexModel N)) (ρ : ComplexModel N → ℝ)
    (hρ : IsSmoothLocalPotential θ.val e (W : Set (ComplexModel N)) ρ)
    (hpsh : PlurisubharmonicOn
      (productModelFunction (chartLegendreFunction (affineTwist w b) e ρ))
      (puncturedProductOpens W)) :
    Patch (fun _ : Fin (N + 1) => productLineForm θ b) (fun _ => w) where
  chart := productLineChart e false
  domain := puncturedProductOpens W
  domain_le_target := (puncturedProductOpens_subset_productLineDomain W).trans
    (productLineDomain_subset_target hρ.2.1 false)
  potential := fun _ => productLinePotential ρ b
  localPotential := fun _ => (isSmoothLocalPotential_productLineForm hρ b false).mono
    (puncturedProductOpens W).isOpen (puncturedProductOpens_subset_productLineDomain W)
  plurisubharmonic := fun _ => by
    convert hpsh using 1
    funext v
    change w ((productLineChart e false).val.symm v) + _ =
      stripChartFunction (affineTwist w b) e ρ (stripModelEquiv N v)
    rw [stripChartFunction_affineTwist, twistLinear_stripModelEquiv]

variable [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace (Y × ProjectiveLine)] [BorelSpace (Y × ProjectiveLine)]

/-- **The measure `ν`** (`tok-wn-vf:punctured`): the global non-pluripolar measure of a `Θ`-psh
`w` on `Y × ℙ¹`, pulled back to `Y × ℂ` along `(y, τ) ↦ (y, [τ : 1])`, is the non-pluripolar
measure of the affine twist `u` on `Y × ℂ*` in the sense of `IsPuncturedProductMAMeasure`. -/
theorem isPuncturedProductMAMeasure_comap {θ : ClosedRealOneOneForm N Y} {b : ℝ}
    {w : Y × ProjectiveLine → EReal}
    (hw : ThetaPlurisubharmonic (productLineForm θ b).val w) :
    IsPuncturedProductMAMeasure θ.val (affineTwist w b)
      ((globalMixedMeasure (fun _ : Fin (N + 1) => productLineForm θ b) (fun _ => w)
        (fun _ => hw)).comap affineEmbedding) := by
  intro e W ρ hρ hpsh T hT hTsub
  have hemb : MeasurableEmbedding (affineEmbedding (Y := Y)) :=
    isOpenEmbedding_affineEmbedding.measurableEmbedding
  rw [hemb.comap_apply]
  set Q := productLinePatch θ b e W ρ hρ hpsh
  have hsub : affineEmbedding '' T ⊆ (Q.source : Set (Y × ProjectiveLine)) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hTsub hp
    have hval : (productLineChart e false).val (affineEmbedding p) = twistLinear N (e.val p.1, p.2) := by
      apply (prodModelEquiv N 1).symm.injective
      rw [prodModelEquiv_symm_twistLinear]
      change (prodModelEquiv N 1).symm ((prodModelEquiv N 1) (e.val p.1,
        projectiveModelChart false (affinePoint p.2))) = _
      rw [ContinuousLinearEquiv.symm_apply_apply, affinePoint,
        (projectiveModelChart false).right_inv (by rw [projectiveModelChart_target_eq]; exact mem_univ _)]
    refine ⟨?_, ?_⟩
    · change (affineEmbedding p) ∈ (prodChart e.val (projectiveModelChart false)).source
      rw [prodChart_source]
      exact ⟨h1, (projectiveModelChart false).map_target
        (by rw [projectiveModelChart_target_eq]; exact mem_univ _)⟩
    · change (productLineChart e false).val (affineEmbedding p) ∈ puncturedProductOpens W
      rw [hval]
      show stripModelEquiv N (twistLinear N (e.val p.1, p.2)) ∈
        (W : Set (ComplexModel N)) ×ˢ puncturedPlane
      rw [stripModelEquiv_twistLinear]
      exact ⟨h2, h3⟩
  rw [← Measure.restrict_eq_self _ hsub, globalMixedMeasure_restrict_patch, patchMeasure,
    Patch.pushMeasure_apply]
  have hv : PlurisubharmonicOn (productModelFunction (chartLegendreFunction (affineTwist w b) e ρ))
      (puncturedProductOpens W) := hpsh
  have hcorr : ∀ i, EqOn (Q.corrected i)
      (productModelFunction (chartLegendreFunction (affineTwist w b) e ρ))
      (puncturedProductOpens W) := by
    intro i v _
    change w ((productLineChart e false).val.symm v) + _ =
      stripChartFunction (affineTwist w b) e ρ (stripModelEquiv N v)
    rw [stripChartFunction_affineTwist, twistLinear_stripModelEquiv]
    rfl
  have hcong : MixedNonPluripolar.mixedTruncationLimitMeasure Q.domain Q.corrected
      Q.plurisubharmonic = MixedNonPluripolar.mixedTruncationLimitMeasure
        (puncturedProductOpens W) (fun _ : Fin (N + 1) =>
          productModelFunction (chartLegendreFunction (affineTwist w b) e ρ)) (fun _ => hv) :=
    MixedNonPluripolar.mixedTruncationLimitMeasure_congr _ _ hcorr
  rw [hcong, MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal (Nat.succ_pos N) hv]
  congr 1
  ext v
  simp only [mem_inter_iff, mem_preimage]
  refine and_congr_right fun _ => ?_
  change (productLineChart e false).val.symm v ∈ _ ↔ _
  rw [← affineEmbedding_productChartInverse]
  exact hemb.injective.mem_set_image

end Measure

end SGPT.Okounkov.TranscendentalWN
