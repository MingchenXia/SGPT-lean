import SGPT.Unibranch.ComplexSpaceFormDomainPullback
import SGPT.Unibranch.ComplexSpaceFormPullbackClosed
import SGPT.Unibranch.ComplexSpaceThetaBimeromorphicPullback
import SGPT.Unibranch.OriginalNativeModification
import SGPT.Foundations.Analysis.FirstPass.FormPullback
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentials
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback

/-!
# smooth forms and `θ`-psh functions of a singular space, pulled back to a manifold

Source `def:modelvalcurr` (`chapter_Okounkov.tex`) pulls a closed positive `(1,1)`-current `S` on
a normal compact Kähler space `Z` back along a proper bimeromorphic morphism `h : Ẑ → Z` from a
compact Kähler manifold. Following `def:unibranch:L105` and `cor:PSH` (Appendix B), a closed
positive `(1,1)`-current on `Z` is `S = θ + ddᶜφ` with `θ` a smooth closed real `(1,1)`-form on
`Z` (`SGPT.Unibranch.SpaceForm`: locally the restriction of ambient forms under local embeddings)
and `φ` a `θ`-psh function (`SourceReducedComplexSpace.IsThetaPSH`); its pull-back is
`h^*S = h^*θ + ddᶜ(φ ∘ h)`.

This file turns the singular-space data into the native manifold data used by the currents of
the smooth chapters, for an arbitrary morphism `h : (W, 𝒪_W) ⟶ Z` from a complex manifold `W`:

* `nativePullback θ h`: the pulled-back form as a native `SmoothRealForm` on `W`; its coefficient
  in the chart `e` is the existing domain pull-back `SpaceForm.pullbackToDomain` along the chart
  inverse composed with `h`;
* `nativePullback_coeff_eq_of_restrictsTo`: in every chart it is computed by every local
  holomorphic lift of `h` into every local embedding on which `θ` restricts;
* `nativePullback_isClosed`, `nativePullback_isTypeOneOne`: closedness and type `(1,1)` are
  inherited from `θ`;
* `isThetaPshPotential_nativePullback`: if `φ` is `θ`-psh on the unibranch space `Z` and `h` is
  proper bimeromorphic, then `φ ∘ h` is a native `h^*θ`-psh potential (local potentials, local
  psh germs and local nondegeneracy are all produced);
* `nativePullback_comp_geometricallyEq`: functoriality along holomorphic maps of manifolds.

Blueprint: `blueprint/src/oc.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OCSpaceFormNative

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification

variable {n : ℕ} {W : Type} [TopologicalSpace W] [ChartedSpace (ComplexModel n) W]
  [IsComplexManifold n W]

/-! ### Chart domains as complex spaces -/

/-- The open target of a chart. -/
def chartDomain (e : ComplexChart n W) : Opens (ComplexModel n) :=
  ⟨e.val.target, e.val.open_target⟩

theorem contMDiff_chartInverse (e : ComplexChart n W) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : chartDomain e => e.val.symm z.val) :=
  (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property)).comp_contMDiff
    contMDiff_subtype_val (fun z => z.property)

/-- The inverse of a chart, as a morphism of complex spaces from its target domain. -/
def chartInverseMorphism (e : ComplexChart n W) :
    domainSpace (chartDomain e) ⟶ wholeModel (n := n) W :=
  nativeMorphism (contMDiff_chartInverse e)

variable {Z : SourceReducedComplexSpace} (h : wholeModel (n := n) W ⟶ Z)

/-- The morphism `h ∘ e⁻¹` from the chart target of `e` to `Z`. -/
def chartMorphism (e : ComplexChart n W) : domainSpace (chartDomain e) ⟶ Z :=
  chartInverseMorphism e ≫ h

theorem chartMorphism_base (e : ComplexChart n W) (y : (univ : Set (chartDomain e))) :
    (chartMorphism h e).hom.left.base y =
      h.hom.left.base ⟨e.val.symm y.val.val, mem_univ _⟩ := rfl

/-! ### The native pull-back form -/

variable {k : ℕ} (θ : SpaceForm Z k)

/-- A local lift of `chartMorphism h e` along the chart transition `T = e' ∘ e⁻¹`. -/
private def transitionLift (e e' : ComplexChart n W) {z : ComplexModel n}
    (hz : z ∈ (chartTransition e e').source)
    (A : SpaceForm.DomainLift θ (chartMorphism h e')
      ⟨chartTransition e e' z, ((chartTransition e e').map_source hz).1⟩) :
    SpaceForm.DomainLift θ (chartMorphism h e) ⟨z, hz.1⟩ where
  chart := A.chart
  window := (chartTransition e e').source ∩ chartTransition e e' ⁻¹' A.window
  isOpen := (chartTransition e e').continuousOn.isOpen_inter_preimage
    (chartTransition e e').open_source A.isOpen
  mem := ⟨hz, A.mem⟩
  subset := fun w hw => hw.1.1
  lift := A.lift ∘ chartTransition e e'
  holomorphic := A.holomorphic.comp
    (fun w hw => (chartTransition_contDiffAt e e' hw.1).contDiffWithinAt) (fun w hw => hw.2)
  maps := fun w hw => A.maps hw.2
  factor := by
    intro y hy
    have hT : chartTransition e e' y.val.val ∈ chartDomain e' :=
      ((chartTransition e e').map_source hy.1).1
    obtain ⟨c, hc, hpc⟩ := A.factor ⟨⟨chartTransition e e' y.val.val, hT⟩, trivial⟩ hy.2
    refine ⟨c, hc, hpc.trans ?_⟩
    rw [chartMorphism_base, chartMorphism_base]
    exact congrArg (fun p => h.hom.left.base p)
      (Subtype.ext (e'.val.left_inv hy.1.2))

private theorem pullbackToDomain_transition (e e' : ComplexChart n W) {z : ComplexModel n}
    (hz : z ∈ (chartTransition e e').source) (v : Fin k → ComplexModel n) :
    SpaceForm.pullbackToDomain θ (chartMorphism h e) z v =
      SpaceForm.pullbackToDomain θ (chartMorphism h e') (chartTransition e e' z)
        (fun i => chartTransitionDerivative e e' z (v i)) := by
  let A := Classical.choice (SpaceForm.domainLift_nonempty θ (chartMorphism h e')
    ⟨chartTransition e e' z, ((chartTransition e e').map_source hz).1⟩)
  let B := transitionLift h θ e e' hz A
  rw [SpaceForm.pullbackToDomain_eq θ _ B B.mem, SpaceForm.pullbackToDomain_eq θ _ A A.mem]
  have hT : DifferentiableAt ℝ (chartTransition e e') z :=
    (chartTransition_contDiffAt_real e e' hz).differentiableAt (by simp)
  have hA : DifferentiableAt ℝ A.lift (chartTransition e e' z) :=
    ((A.holomorphic.differentiableOn (by simp)).differentiableAt
      (A.isOpen.mem_nhds A.mem)).restrictScalars ℝ
  have hcomp := pullbackForm_comp hT hA (θ.rep A.chart)
  change pullbackForm (A.lift ∘ chartTransition e e') (θ.rep A.chart) z v = _
  rw [← hcomp]
  rfl

/-- **The pull-back `h^*θ` as a native smooth form on the manifold `W`.** In the chart `e` its
coefficient is the domain pull-back of `θ` along `h ∘ e⁻¹`. -/
def nativePullback : SmoothRealForm n W k where
  coeff e := SpaceForm.pullbackToDomain θ (chartMorphism h e)
  smooth e := SpaceForm.pullbackToDomain_smooth θ (chartMorphism h e)
  compatible e e' _ hz v := pullbackToDomain_transition h θ e e' hz v

/-- **Computation in charts.** If `θ` restricts to `v` on a local embedding `e'` of `Z` and
`G` is a holomorphic lift of `h ∘ e⁻¹` into `e'` on an open set `D`, then the native coefficient
is `G^*v` on `D`. -/
theorem nativePullback_coeff_eq_of_restrictsTo {e' : LocalEmbedding Z}
    {v : AmbientForm e'.dim k} (hv : θ.RestrictsTo e' v) (e : ComplexChart n W)
    {D : Set (ComplexModel n)} (hD : IsOpen D) (hDe : D ⊆ e.val.target)
    {G : ComplexModel n → ComplexModel e'.dim} (hG : DifferentiableOn ℂ G D)
    (hfac : ∀ w ∈ D, ∃ c : e'.carrier, c.val.val = G w ∧
      e'.toPoint c = h.hom.left.base ⟨e.val.symm w, mem_univ _⟩)
    {z : ComplexModel n} (hz : z ∈ D) :
    (nativePullback h θ).coeff e z = pullbackForm G v z := by
  let A := Classical.choice (SpaceForm.domainLift_nonempty θ (chartMorphism h e)
    ⟨z, hDe hz⟩)
  change SpaceForm.pullbackToDomain θ (chartMorphism h e) z = _
  rw [SpaceForm.pullbackToDomain_eq θ _ A A.mem]
  have hpoints : ∀ w ∈ D ∩ A.window, ∃ (a : e'.carrier) (b : (θ.chart A.chart).carrier),
      a.val.val = G w ∧ b.val.val = A.lift w ∧ e'.toPoint a = (θ.chart A.chart).toPoint b := by
    intro w hw
    obtain ⟨a, ha, hpa⟩ := hfac w hw.1
    obtain ⟨b, hb, hpb⟩ := A.factor ⟨⟨w, hDe hw.1⟩, trivial⟩ hw.2
    exact ⟨a, b, ha, hb, hpa.trans hpb.symm⟩
  exact (SpaceForm.pullback_eq_of_restrictsTo θ hv A.chart (hD.inter A.isOpen)
    (hG.mono inter_subset_left)
    ((A.holomorphic.differentiableOn (by simp)).mono inter_subset_right) hpoints
    ⟨hz, A.mem⟩).symm

/-- Every point of a chart target has a holomorphic lift of `h ∘ e⁻¹` into every local
embedding of `Z` through its image. -/
theorem exists_chart_lift (e : ComplexChart n W) (e' : LocalEmbedding Z) {z : ComplexModel n}
    (hz : z ∈ e.val.target)
    (hz' : h.hom.left.base ⟨e.val.symm z, mem_univ _⟩ ∈ range e'.toPoint) :
    ∃ D : Set (ComplexModel n), IsOpen D ∧ z ∈ D ∧ D ⊆ e.val.target ∧
      ∃ G : ComplexModel n → ComplexModel e'.dim, ContDiffOn ℂ ∞ G D ∧ MapsTo G D e'.ambient ∧
        ∀ w ∈ D, ∃ c : e'.carrier, c.val.val = G w ∧
          e'.toPoint c = h.hom.left.base ⟨e.val.symm w, mem_univ _⟩ := by
  obtain ⟨D, hD, hzD, hDU, G, hG, hmaps, hfac⟩ :=
    LocalEmbedding.exists_contDiffOn_factor (chartMorphism h e).hom.left
      (Over.w (chartMorphism h e).hom) e' (⟨⟨z, hz⟩, trivial⟩ : (univ : Set (chartDomain e))) hz'
  refine ⟨D, hD, hzD, hDU, G, hG, hmaps, ?_⟩
  intro w hw
  exact hfac ⟨⟨w, hDU hw⟩, trivial⟩ hw

/-- Closedness of `θ` gives closedness of the native pull-back. -/
theorem nativePullback_isClosed (hθ : θ.IsClosed) : (nativePullback h θ).IsClosed := by
  intro e z hz
  obtain ⟨e', he', v, hv, hclosed, hres⟩ := hθ (h.hom.left.base ⟨e.val.symm z, mem_univ _⟩)
  obtain ⟨D, hD, hzD, hDe, G, hG, hmaps, hfac⟩ := exists_chart_lift h e e' hz he'
  have heq : (nativePullback h θ).coeff e =ᶠ[𝓝 z] pullbackForm G v := by
    filter_upwards [hD.mem_nhds hzD] with w hw
    exact nativePullback_coeff_eq_of_restrictsTo h θ hres e hD hDe
      (hG.differentiableOn (by simp)) hfac hw
  rw [heq.extDeriv_eq]
  have hdiff := (hv.contDiffAt (e'.ambient.isOpen.mem_nhds (hmaps hzD))).differentiableAt
    (by simp)
  have hnat := extDeriv_pullback hdiff
    ((hG.restrict_scalars ℝ).contDiffAt (hD.mem_nhds hzD))
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change extDeriv (fun w => (v (G w)).compContinuousLinearMap (fderiv ℝ G w)) z = 0
  rw [hnat, hclosed _ (hmaps hzD)]
  ext w
  rfl

/-- Type `(1,1)` of `θ` gives type `(1,1)` of the native pull-back. -/
theorem nativePullback_isTypeOneOne (θ : SpaceForm Z 2) (hθ : θ.IsOneOne) :
    (nativePullback h θ).IsTypeOneOne := by
  intro e z hz
  obtain ⟨e', he', v, _hv, htype, hres⟩ := hθ (h.hom.left.base ⟨e.val.symm z, mem_univ _⟩)
  obtain ⟨D, hD, hzD, hDe, G, hG, hmaps, hfac⟩ := exists_chart_lift h e e' hz he'
  rw [nativePullback_coeff_eq_of_restrictsTo h θ hres e hD hDe
    (hG.differentiableOn (by simp)) hfac hzD]
  intro a b
  have hd := (hG.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hzD)
  have hlin (w : ComplexModel n) :
      fderiv ℝ G z (Complex.I • w) = Complex.I • fderiv ℝ G z w := by
    rw [hd.fderiv_restrictScalars ℝ]
    exact (fderiv ℂ G z).map_smul Complex.I w
  change v (G z) ((fderiv ℝ G z) ∘ ![Complex.I • a, Complex.I • b]) =
    v (G z) ((fderiv ℝ G z) ∘ ![a, b])
  have hvec : ((fderiv ℝ G z) ∘ ![Complex.I • a, Complex.I • b]) =
      ![Complex.I • fderiv ℝ G z a, Complex.I • fderiv ℝ G z b] := by
    funext i
    fin_cases i <;> simp [hlin]
  have hvec' : ((fderiv ℝ G z) ∘ ![a, b]) = ![fderiv ℝ G z a, fderiv ℝ G z b] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, hvec']
  exact htype (G z) (hmaps hzD) (fderiv ℝ G z a) (fderiv ℝ G z b)

/-! ### `θ`-psh functions -/

/-- The pull-back `φ ∘ h` of a function on `Z`, as a function on `W`. -/
def nativePotential (φ : Z.obj.left → EReal) : W → EReal :=
  fun w => φ (h.hom.left.base ⟨w, mem_univ w⟩)

/-- **Local potentials and psh germs.** If `φ` is `θ`-psh on `Z`, then `φ ∘ h` is
`h^*θ`-psh in every chart of `W`, in the native sense: near every point there is a smooth local
potential `ρ` of the native pull-back with `φ ∘ h ∘ e⁻¹ + ρ` plurisubharmonic. -/
theorem thetaPlurisubharmonic_nativePullback (θ : SpaceForm Z 2) {φ : Z.obj.left → EReal}
    (hφ : Z.IsThetaPSH θ φ) :
    ThetaPlurisubharmonic (nativePullback h θ) (nativePotential h φ) := by
  intro e z hz
  obtain ⟨e', he', -, g, hg, hres, hpsh⟩ := hφ (h.hom.left.base ⟨e.val.symm z, mem_univ _⟩)
  obtain ⟨D, hD, hzD, hDe, G, hG, hmaps, hfac⟩ := exists_chart_lift h e e' hz he'
  obtain ⟨c0, hc0, hpc0⟩ := hfac z hzD
  obtain ⟨W₃, hW₃, hcW₃, -, ψ, hψ, hψeq⟩ :=
    SourceReducedComplexSpace.exists_ambient hpsh.2
      (LocalEmbedding.model e'.ambient e'.carrier e'.analytic) c0
  let D' : Set (ComplexModel n) := D ∩ G ⁻¹' W₃
  have hD' : IsOpen D' := hG.continuousOn.isOpen_inter_preimage hD hW₃
  have hzD' : z ∈ D' := ⟨hzD, by change G z ∈ W₃; rw [← hc0]; exact hcW₃⟩
  refine ⟨D', fun w => g (G w), hzD', ⟨hD', fun w hw => hDe hw.1,
    hg.comp ((hG.restrict_scalars ℝ).mono inter_subset_left) (fun w hw => hmaps hw.1), ?_⟩, ?_⟩
  · intro w hw
    rw [HolomorphicDDC.smoothDDC_comp hD e'.ambient.isOpen hG hg hmaps hw.1]
    exact (nativePullback_coeff_eq_of_restrictsTo h θ hres e hD hDe
      (hG.differentiableOn (by simp)) hfac hw.1).symm
  · have hcomp : PlurisubharmonicOn (fun w => ψ (G w)) D' :=
      Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hD'
        ((hG.differentiableOn (by simp)).mono inter_subset_left) (fun w hw => hw.2)
        (fun x hx => ⟨W₃, hW₃, hx, hψ⟩)
    intro x hx
    obtain ⟨V, hV, hxV, hVpsh⟩ := hcomp x hx
    refine ⟨V ∩ D', hV.inter hD', ⟨hxV, hx⟩, (hVpsh.mono inter_subset_left).congr ?_⟩
    intro w hw
    obtain ⟨c, hc, hpc⟩ := hfac w hw.2.1
    have hcW : c.val.val ∈ W₃ := by rw [hc]; exact hw.2.2
    have h1 := hψeq c hcW
    rw [LocalEmbedding.model_toPoint] at h1
    change ψ (G w) = chartFunction (nativePotential h φ) e w + ((g (G w) : ℝ) : EReal)
    rw [← hc, ← h1]
    change ((g c.val.val : ℝ) : EReal) + φ (e'.toPoint c) =
      φ (h.hom.left.base ⟨e.val.symm w, mem_univ _⟩) + ((g c.val.val : ℝ) : EReal)
    rw [hpc, add_comm]

/-- **Native `θ`-psh potential.** If `Z` is unibranch, `φ` is `θ`-psh on `Z` and `h` is proper
bimeromorphic, then `φ ∘ h` is a native `h^*θ`-psh potential on `W`. -/
theorem isThetaPshPotential_nativePullback (θ : SpaceForm Z 2) {φ : Z.obj.left → EReal}
    (hφ : Z.IsThetaPSH θ φ) (hZ : Z.IsUnibranch) (hh : IsProperBimeromorphic h) :
    IsThetaPshPotential (nativePullback h θ) (nativePotential h φ) := by
  refine ⟨thetaPlurisubharmonic_nativePullback h θ hφ, ?_⟩
  have hdense := hφ.dense_finite_pullback_of_isProperBimeromorphic hZ hh
  intro x U hU hxU
  have hU' : IsOpen ((Subtype.val : ↥(univ : Set W) → W) ⁻¹' U) :=
    hU.preimage continuous_subtype_val
  obtain ⟨y, hyU, hy⟩ := hdense.inter_open_nonempty _ hU' ⟨⟨x, mem_univ x⟩, hxU⟩
  exact ⟨y.val, hyU, hy⟩

/-! ### Functoriality -/

variable {W' : Type} [TopologicalSpace W'] [ChartedSpace (ComplexModel n) W']
  [IsComplexManifold n W']

/-- **Functoriality along holomorphic maps.** For a holomorphic `q : W' → W`, the native
pull-back along `q ≫ h` is the native form pull-back along `q` of the native pull-back along
`h`. -/
theorem nativePullback_comp_geometricallyEq {q : W' → W}
    (hq : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ q) :
    (nativePullback (nativeMorphism hq ≫ h) θ).GeometricallyEq
      (SmoothRealForm.pullback hq (nativePullback h θ)) := by
  intro e z hz
  let d := complexChartAt (n := n) (q (e.val.symm z))
  have hzd : z ∈ coordinateDomain q e d := ⟨hz, mem_complexChartAt_source _⟩
  have hcm : coordinateMap q e d z ∈ d.val.target := coordinateMap_mem_target hzd
  let A := Classical.choice (SpaceForm.domainLift_nonempty θ (chartMorphism h d)
    ⟨coordinateMap q e d z, hcm⟩)
  let D : Set (ComplexModel n) := coordinateDomain q e d ∩ coordinateMap q e d ⁻¹' A.window
  have hD : IsOpen D := (coordinateMap_contDiffOn hq e d).continuousOn.isOpen_inter_preimage
    (coordinateDomain_isOpen hq e d) A.isOpen
  have hzD : z ∈ D := ⟨hzd, A.mem⟩
  have hDe : D ⊆ e.val.target := fun w hw => hw.1.1
  have hlift : ContDiffOn ℂ ∞ (A.lift ∘ coordinateMap q e d) D :=
    A.holomorphic.comp ((coordinateMap_contDiffOn hq e d).mono inter_subset_left)
      (fun w hw => hw.2)
  have hres : θ.RestrictsTo (θ.chart A.chart) (θ.rep A.chart) :=
    fun i W G hG => θ.compatible A.chart i W G hG
  have hfac : ∀ w ∈ D, ∃ c : (θ.chart A.chart).carrier,
      c.val.val = (A.lift ∘ coordinateMap q e d) w ∧
      (θ.chart A.chart).toPoint c =
        (nativeMorphism hq ≫ h).hom.left.base ⟨e.val.symm w, mem_univ _⟩ := by
    intro w hw
    have hcw : coordinateMap q e d w ∈ chartDomain d := coordinateMap_mem_target hw.1
    obtain ⟨c, hc, hpc⟩ := A.factor ⟨⟨coordinateMap q e d w, hcw⟩, trivial⟩ hw.2
    refine ⟨c, hc, hpc.trans ?_⟩
    rw [chartMorphism_base]
    exact congrArg (fun p => h.hom.left.base p) (Subtype.ext (d.val.left_inv hw.1.2))
  have hleft := nativePullback_coeff_eq_of_restrictsTo (nativeMorphism hq ≫ h) θ hres e hD hDe
    (hlift.differentiableOn (by simp)) hfac hzD
  rw [hleft, SmoothRealForm.pullback_coeff hq _ e d hzd]
  have hright : (nativePullback h θ).coeff d (coordinateMap q e d z) =
      pullbackForm A.lift (θ.rep A.chart) (coordinateMap q e d z) :=
    SpaceForm.pullbackToDomain_eq θ _ A A.mem
  rw [hright]
  have hcmd : DifferentiableAt ℝ (coordinateMap q e d) z :=
    (coordinateMap_contDiffAt_real hq e d hzd).differentiableAt (by simp)
  have hAd : DifferentiableAt ℝ A.lift (coordinateMap q e d z) :=
    ((A.holomorphic.differentiableOn (by simp)).differentiableAt
      (A.isOpen.mem_nhds A.mem)).restrictScalars ℝ
  exact (pullbackForm_comp hcmd hAd (θ.rep A.chart)).symm

/-- **Functoriality along morphisms of spaces.** For `p : Z' ⟶ Z` and `h' : (W, 𝒪) ⟶ Z'`, the
native pull-back along `h'` of the singular-space pull-back `p^*θ` is the native pull-back of `θ`
along `h' ≫ p`. -/
theorem nativePullback_spacePullback_geometricallyEq {Z' : SourceReducedComplexSpace}
    (p : Z' ⟶ Z) (h' : wholeModel (n := n) W ⟶ Z') :
    (nativePullback h' (SpaceForm.pullback θ p)).GeometricallyEq (nativePullback (h' ≫ p) θ) := by
  intro e z hz
  obtain ⟨i, hi⟩ := θ.covers ((h' ≫ p).hom.left.base ⟨e.val.symm z, mem_univ _⟩)
  obtain ⟨B, hB⟩ := SpaceForm.morphismChartLift_cover p (θ.chart i)
    (h'.hom.left.base ⟨e.val.symm z, mem_univ _⟩) hi
  have hself : θ.RestrictsTo (θ.chart i) (θ.rep i) := fun j W G hG => θ.compatible i j W G hG
  have hresB : (SpaceForm.pullback θ p).RestrictsTo B.source (pullbackForm B.lift (θ.rep i)) :=
    SpaceForm.pullback_restrictsTo_of_lift θ p hself B.source B.holomorphic B.maps B.factor
  obtain ⟨D, hD, hzD, hDe, G, hG, hmaps, hfac⟩ := exists_chart_lift h' e B.source hz hB
  have hfac2 : ∀ w ∈ D, ∃ c : (θ.chart i).carrier, c.val.val = (B.lift ∘ G) w ∧
      (θ.chart i).toPoint c = (h' ≫ p).hom.left.base ⟨e.val.symm w, mem_univ _⟩ := by
    intro w hw
    obtain ⟨c, hc, hpc⟩ := hfac w hw
    obtain ⟨b, hb, hpb⟩ := B.factor c
    refine ⟨b, ?_, hpb.trans ?_⟩
    · rw [hb, hc]
      rfl
    · exact congrArg (fun y => p.hom.left.base y) hpc
  have hBG : ContDiffOn ℂ ∞ (B.lift ∘ G) D := B.holomorphic.comp hG hmaps
  rw [nativePullback_coeff_eq_of_restrictsTo h' (SpaceForm.pullback θ p) hresB e hD hDe
      (hG.differentiableOn (by simp)) hfac hzD,
    nativePullback_coeff_eq_of_restrictsTo (h' ≫ p) θ hself e hD hDe
      (hBG.differentiableOn (by simp)) hfac2 hzD]
  have hGd : DifferentiableAt ℝ G z :=
    ((hG.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hzD)).restrictScalars ℝ
  have hBd : DifferentiableAt ℝ B.lift (G z) :=
    ((B.holomorphic.differentiableOn (by simp)).differentiableAt
      (B.source.ambient.isOpen.mem_nhds (hmaps hzD))).restrictScalars ℝ
  exact pullbackForm_comp hGd hBd (θ.rep i)

end SGPT.Okounkov.OCSpaceFormNative
