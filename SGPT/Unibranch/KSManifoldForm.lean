import SGPT.Unibranch.ComplexSpaceFormConstantFiber
import SGPT.Unibranch.ComplexSpaceFormPullbackClosed
import SGPT.Unibranch.OriginalNativeModification
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Forms and `θ`-psh functions on a complex manifold viewed as a complex space

Appendix B of the book (`appendix_unibranch.tex`, `def:unibranch:L105`,
`cor:PSH`, `def:unibranch:L212`) compares the pluripotential theory of a complex space `X`
with that of compact Kähler manifolds `Y` mapping to `X`: for `π : Y → X` and a smooth form `θ`
on `X`, `π^*θ` is a smooth form on the *manifold* `Y`, and `PSH(Y, π^*θ)` is the manifold notion
used in the body of the book.  The project has two parallel languages for these objects:

* on complex spaces: `SpaceForm` (smooth forms through local embeddings) and
  `SourceReducedComplexSpace.IsThetaPSH` (`def:unibranch:L105`);
* on manifolds: `SmoothRealForm` (atlas coefficients) and `IsThetaPshPotential`.

This file identifies them on a complex manifold `V`, viewed as the complex space
`wholeModel V = (V, 𝒪_V)`.

* `chartInverse e`: the inverse of an atlas chart `e` of `V`, as a morphism of complex spaces
  from the chart target to `wholeModel V`.
* `toManifoldForm θ`: the manifold form of a `SpaceForm` `θ` on `wholeModel V`; its coefficient
  in the chart `e` is the pull-back of `θ` along `chartInverse e`
  (`SpaceForm.pullbackToDomain`).  Closed and type `(1,1)` forms give closed real `(1,1)`-forms
  (`toManifoldForm_isClosed`, `toManifoldForm_isTypeOneOne`).
* `manifoldPullback θ F`: the manifold form `F^*θ` for a morphism `F : wholeModel V ⟶ X` to an
  arbitrary complex space and a `SpaceForm` `θ` on `X`, with its coefficient formula
  `manifoldPullback_coeff`; functoriality along holomorphic maps of manifolds
  (`manifoldPullback_nativeMorphism`).
* `PSH` bridge: `thetaPlurisubharmonic_of_isThetaPSH`,
  `isThetaPshPotential_of_isThetaPSH_of_dense`, `isThetaPSH_of_isThetaPshPotential`.

No new notion of form or of `θ`-psh function is introduced (both sides are the existing ones).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces

namespace SGPT.Unibranch.KSManifoldForm

open SourceReducedComplexSpace OriginalNativeModification

/-! ### Chart inverses as morphisms of complex spaces -/

section Charts

variable {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]
  [IsComplexManifold m V]

/-- The target of an atlas chart, as an open subset of `ℂ^m`. -/
def chartTarget (e : ComplexChart m V) : Opens (ComplexModel m) :=
  ⟨e.val.target, e.val.open_target⟩

theorem contMDiff_chartSymm (e : ComplexChart m V) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞
      (fun z : chartTarget e => e.val.symm z.val) :=
  (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property)).comp_contMDiff
    contMDiff_subtype_val (fun z => z.property)

/-- The inverse of an atlas chart `e` of `V`, as a morphism of complex spaces from the chart
target (a domain of `ℂ^m`) to `V`. -/
def chartInverse (e : ComplexChart m V) : domainSpace (chartTarget e) ⟶ wholeModel (n := m) V :=
  nativeMorphism (n := m) (m := m) (contMDiff_chartSymm e)

theorem chartInverse_base (e : ComplexChart m V) (z : (univ : Set (chartTarget e))) :
    ((chartInverse e).hom.left.base z).val = e.val.symm z.val.val := rfl

end Charts

/-! ### The core change-of-domain formula -/

section Core

variable {X : SourceReducedComplexSpace} {k l m : ℕ}

/-- If two domain morphisms `F : U → X` and `F' : U' → X` are related on an open set `D ⊆ U` by
a holomorphic map `φ : D → U'` (`F = F' ∘ φ` on points), then the pull-back of a smooth form
along `F` is the pull-back along `φ` of its pull-back along `F'`. -/
theorem pullbackToDomain_eq_pullbackForm (θ : SpaceForm X k)
    {U : Opens (ComplexModel l)} {U' : Opens (ComplexModel m)}
    (F : domainSpace U ⟶ X) (F' : domainSpace U' ⟶ X)
    {D : Set (ComplexModel l)} (hD : IsOpen D) (hDU : D ⊆ U)
    {φ : ComplexModel l → ComplexModel m} (hφ : ContDiffOn ℂ ∞ φ D) (hmaps : MapsTo φ D U')
    (hpts : ∀ (y : (univ : Set U)) (hy : y.val.val ∈ D),
      F.hom.left.base y = F'.hom.left.base ⟨⟨φ y.val.val, hmaps hy⟩, trivial⟩)
    {z : ComplexModel l} (hz : z ∈ D) :
    SpaceForm.pullbackToDomain θ F z = pullbackForm φ (SpaceForm.pullbackToDomain θ F') z := by
  let A := Classical.choice (SpaceForm.domainLift_nonempty θ F' ⟨φ z, hmaps hz⟩)
  let W : Set (ComplexModel l) := D ∩ φ ⁻¹' A.window
  have hW : IsOpen W := hφ.continuousOn.isOpen_inter_preimage hD A.isOpen
  have hzW : z ∈ W := ⟨hz, A.mem⟩
  let B : SpaceForm.DomainLift θ F ⟨z, hDU hz⟩ :=
    { chart := A.chart
      window := W
      isOpen := hW
      mem := hzW
      subset := fun w hw => hDU hw.1
      lift := A.lift ∘ φ
      holomorphic := A.holomorphic.comp (hφ.mono inter_subset_left) (fun w hw => hw.2)
      maps := fun w hw => A.maps hw.2
      factor := by
        intro y hy
        obtain ⟨c, hc, hpc⟩ := A.factor ⟨⟨φ y.val.val, hmaps hy.1⟩, trivial⟩ hy.2
        exact ⟨c, hc, hpc.trans (hpts y hy.1).symm⟩ }
  have hφd : DifferentiableAt ℝ φ z :=
    ((hφ.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hz)).restrictScalars ℝ
  have hAd : DifferentiableAt ℝ A.lift (φ z) :=
    ((A.holomorphic.differentiableOn (by simp)).differentiableAt
      (A.isOpen.mem_nhds A.mem)).restrictScalars ℝ
  have hA : SpaceForm.pullbackToDomain θ F' (φ z) = pullbackForm A.lift (θ.rep A.chart) (φ z) :=
    SpaceForm.pullbackToDomain_eq θ F' A A.mem
  have hcomp := pullbackForm_comp hφd hAd (θ.rep A.chart)
  rw [SpaceForm.pullbackToDomain_eq θ F B hzW]
  calc pullbackForm B.lift (θ.rep B.chart) z = pullbackForm (A.lift ∘ φ) (θ.rep A.chart) z := rfl
    _ = pullbackForm φ (pullbackForm A.lift (θ.rep A.chart)) z := hcomp.symm
    _ = pullbackForm φ (SpaceForm.pullbackToDomain θ F') z := by
      show (pullbackForm A.lift (θ.rep A.chart) (φ z)).compContinuousLinearMap (fderiv ℝ φ z) =
        (SpaceForm.pullbackToDomain θ F' (φ z)).compContinuousLinearMap (fderiv ℝ φ z)
      rw [hA]

end Core

/-! ### The manifold form of a smooth form on `wholeModel V` -/

section ManifoldForm

variable {m k : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]
  [IsComplexManifold m V]

theorem chartTransition_contDiffOn (e f : ComplexChart m V) :
    ContDiffOn ℂ ∞ (chartTransition e f) (chartTransition e f).source :=
  fun _ hz => (HolomorphicMaps.chartTransition_contDiffAt e f hz).contDiffWithinAt

theorem toManifoldForm_compatible (θ : SpaceForm (wholeModel (n := m) V) k)
    (e f : ComplexChart m V) (z : ComplexModel m) (hz : z ∈ (chartTransition e f).source)
    (v : Fin k → ComplexModel m) :
    SpaceForm.pullbackToDomain θ (chartInverse e) z v =
      SpaceForm.pullbackToDomain θ (chartInverse f) (chartTransition e f z)
        (fun i => chartTransitionDerivative e f z (v i)) := by
  have hsrc : (chartTransition e f).source = e.val.target ∩ e.val.symm ⁻¹' f.val.source := rfl
  have hmaps : MapsTo (chartTransition e f) (chartTransition e f).source
      (chartTarget f : Set (ComplexModel m)) := by
    intro w hw
    exact ((chartTransition e f).map_source hw).1
  have hDU : (chartTransition e f).source ⊆ (chartTarget e : Set (ComplexModel m)) := by
    intro w hw
    rw [hsrc] at hw
    exact hw.1
  have hpts : ∀ (y : (univ : Set (chartTarget e))) (hy : y.val.val ∈ (chartTransition e f).source),
      (chartInverse e).hom.left.base y =
        (chartInverse f).hom.left.base ⟨⟨chartTransition e f y.val.val, hmaps hy⟩, trivial⟩ := by
    intro y hy
    rw [hsrc] at hy
    apply Subtype.ext
    rw [chartInverse_base, chartInverse_base]
    change e.val.symm y.val.val = f.val.symm (f.val (e.val.symm y.val.val))
    rw [f.val.left_inv hy.2]
  have h := pullbackToDomain_eq_pullbackForm θ (chartInverse e) (chartInverse f)
    (chartTransition e f).open_source hDU (chartTransition_contDiffOn e f) hmaps hpts hz
  rw [h]
  rfl

/-- **The manifold form underlying a smooth form on `V` viewed as a complex space.** Its
coefficient in an atlas chart `e` is the pull-back of `θ` along the chart inverse. -/
def toManifoldForm (θ : SpaceForm (wholeModel (n := m) V) k) : SmoothRealForm m V k where
  coeff e := SpaceForm.pullbackToDomain θ (chartInverse e)
  smooth e := SpaceForm.pullbackToDomain_smooth θ (chartInverse e)
  compatible e f z hz v := toManifoldForm_compatible θ e f z hz v

theorem toManifoldForm_coeff (θ : SpaceForm (wholeModel (n := m) V) k) (e : ComplexChart m V) :
    (toManifoldForm θ).coeff e = SpaceForm.pullbackToDomain θ (chartInverse e) := rfl

/-- Local readback: wherever `θ` restricts to an ambient form `v` on a local embedding `E`, and
`G` is a holomorphic lift of the chart inverse into `E`, the manifold coefficient is the
pull-back of `v` by `G`. -/
theorem toManifoldForm_coeff_eq_of_restrictsTo (θ : SpaceForm (wholeModel (n := m) V) k)
    (e : ComplexChart m V) {E : LocalEmbedding (wholeModel (n := m) V)} {v : AmbientForm E.dim k}
    (hv : θ.RestrictsTo E v) {D : Set (ComplexModel m)} (hD : IsOpen D)
    (hDU : D ⊆ (chartTarget e : Set (ComplexModel m)))
    {G : ComplexModel m → ComplexModel E.dim} (hG : DifferentiableOn ℂ G D)
    (hfac : ∀ c : (univ : Set (chartTarget e)), c.val.val ∈ D →
      ∃ b : E.carrier, b.val.val = G c.val.val ∧ E.toPoint b = (chartInverse e).hom.left.base c)
    {z : ComplexModel m} (hz : z ∈ D) :
    (toManifoldForm θ).coeff e z = pullbackForm G v z :=
  SpaceForm.pullbackToDomain_eq_of_restrictsTo θ (chartInverse e) hv hD hDU hG hfac hz

/-- Every point of a chart target admits a holomorphic lift of the chart inverse into a local
embedding on which `θ` restricts to a prescribed ambient form (the factorization of morphisms
of complex spaces through local embeddings). -/
theorem exists_chartInverse_factor (e : ComplexChart m V)
    (E : LocalEmbedding (wholeModel (n := m) V)) {z : ComplexModel m} (hz : z ∈ e.val.target)
    (hE : (⟨e.val.symm z, mem_univ _⟩ : (wholeModel (n := m) V).obj.left) ∈ range E.toPoint) :
    ∃ W : Set (ComplexModel m), IsOpen W ∧ z ∈ W ∧ W ⊆ (chartTarget e : Set (ComplexModel m)) ∧
      ∃ G : ComplexModel m → ComplexModel E.dim, ContDiffOn ℂ ∞ G W ∧ MapsTo G W E.ambient ∧
        ∀ y : (univ : Set (chartTarget e)), y.val.val ∈ W → ∃ b : E.carrier,
          b.val.val = G y.val.val ∧ E.toPoint b = (chartInverse e).hom.left.base y := by
  let c : (univ : Set (chartTarget e)) := ⟨⟨z, hz⟩, trivial⟩
  have hc : (chartInverse e).hom.left.base c ∈ range E.toPoint := hE
  exact LocalEmbedding.exists_contDiffOn_factor (chartInverse e).hom.left
    (Over.w (chartInverse e).hom) E c hc

/-- Closed smooth forms on `wholeModel V` give closed manifold forms. -/
theorem toManifoldForm_isClosed {θ : SpaceForm (wholeModel (n := m) V) k}
    (hθ : θ.IsClosed) : (toManifoldForm θ).IsClosed := by
  intro e z hz
  obtain ⟨E, hE, v, hv, hclosed, hres⟩ := hθ ⟨e.val.symm z, mem_univ _⟩
  obtain ⟨W, hW, hzW, hWU, G, hG, hGmaps, hfac⟩ := exists_chartInverse_factor e E hz hE
  have heq : (toManifoldForm θ).coeff e =ᶠ[𝓝 z]
      (fun w => (v (G w)).compContinuousLinearMap (fderiv ℝ G w)) := by
    filter_upwards [hW.mem_nhds hzW] with w hw
    exact toManifoldForm_coeff_eq_of_restrictsTo θ e hres hW hWU
      (hG.differentiableOn (by simp)) hfac hw
  rw [heq.extDeriv_eq]
  have hdiff := (hv.contDiffAt (E.ambient.isOpen.mem_nhds (hGmaps hzW))).differentiableAt
    (by simp)
  have hnat := extDeriv_pullback hdiff
    ((hG.restrict_scalars ℝ).contDiffAt (hW.mem_nhds hzW))
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [hnat, hclosed _ (hGmaps hzW)]
  ext w
  rfl

/-- Smooth forms of type `(1,1)` on `wholeModel V` give manifold forms of type `(1,1)`. -/
theorem toManifoldForm_isTypeOneOne {θ : SpaceForm (wholeModel (n := m) V) 2}
    (hθ : θ.IsOneOne) : (toManifoldForm θ).IsTypeOneOne := by
  intro e z hz
  obtain ⟨E, hE, v, hv, htype, hres⟩ := hθ ⟨e.val.symm z, mem_univ _⟩
  obtain ⟨W, hW, hzW, hWU, G, hG, hGmaps, hfac⟩ := exists_chartInverse_factor e E hz hE
  rw [toManifoldForm_coeff_eq_of_restrictsTo θ e hres hW hWU (hG.differentiableOn (by simp))
    hfac hzW]
  intro a b
  have hd := (hG.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hzW)
  have hlin (w : ComplexModel m) :
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
  exact htype (G z) (hGmaps hzW) (fderiv ℝ G z a) (fderiv ℝ G z b)

/-- The closed real `(1,1)`-form on the manifold `V` underlying a closed `(1,1)` `SpaceForm`. -/
def toClosedRealOneOneForm (θ : SpaceForm (wholeModel (n := m) V) 2) (hc : θ.IsClosed)
    (h11 : θ.IsOneOne) : ClosedRealOneOneForm m V :=
  ⟨toManifoldForm θ, toManifoldForm_isClosed hc, toManifoldForm_isTypeOneOne h11⟩

end ManifoldForm

/-! ### Pull-back of a form on a complex space to a manifold -/

section Pullback

variable {X : SourceReducedComplexSpace} {m k : ℕ} {V : Type} [TopologicalSpace V]
  [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V]

/-- **The manifold form `F^*θ`** on a complex manifold `V`, for a morphism of complex spaces
`F : V → X` and a smooth form `θ` on the complex space `X`. -/
def manifoldPullback (θ : SpaceForm X k) (F : wholeModel (n := m) V ⟶ X) : SmoothRealForm m V k :=
  toManifoldForm (SpaceForm.pullback θ F)

/-- Coefficients of `F^*θ`: pull-back of `θ` along the chart inverse composed with `F`. -/
theorem manifoldPullback_coeff (θ : SpaceForm X k) (F : wholeModel (n := m) V ⟶ X)
    (e : ComplexChart m V) {z : ComplexModel m} (hz : z ∈ e.val.target) :
    (manifoldPullback θ F).coeff e z = SpaceForm.pullbackToDomain θ (chartInverse e ≫ F) z :=
  SpaceForm.pullbackToDomain_pullback θ F (chartInverse e) hz

/-- `F^*θ` as a closed real `(1,1)`-form, for `θ` closed of type `(1,1)`. -/
def manifoldPullbackClosed (θ : SpaceForm X 2) (hc : θ.IsClosed) (h11 : θ.IsOneOne)
    (F : wholeModel (n := m) V ⟶ X) : ClosedRealOneOneForm m V :=
  toClosedRealOneOneForm (SpaceForm.pullback θ F) (hc.pullback F) (h11.pullback F)

@[simp] theorem manifoldPullbackClosed_val (θ : SpaceForm X 2) (hc : θ.IsClosed)
    (h11 : θ.IsOneOne) (F : wholeModel (n := m) V ⟶ X) :
    (manifoldPullbackClosed θ hc h11 F).val = manifoldPullback θ F := rfl

/-- `F^*(q^*θ) = (q ∘ F)^*θ` for a further morphism of complex spaces `q : X → X'`. -/
theorem manifoldPullback_pullback {X' : SourceReducedComplexSpace} (θ : SpaceForm X' k)
    (q : X ⟶ X') (F : wholeModel (n := m) V ⟶ X) :
    (manifoldPullback (SpaceForm.pullback θ q) F).GeometricallyEq (manifoldPullback θ (F ≫ q)) := by
  intro e z hz
  rw [manifoldPullback_coeff _ F e hz, manifoldPullback_coeff θ (F ≫ q) e hz,
    SpaceForm.pullbackToDomain_pullback θ q (chartInverse e ≫ F) hz, Category.assoc]

/-- Two morphisms with the same points give the same manifold form. -/
theorem manifoldPullback_congr (θ : SpaceForm X k) {F G : wholeModel (n := m) V ⟶ X}
    (h : ∀ y : V, F.hom.left.base ⟨y, mem_univ y⟩ = G.hom.left.base ⟨y, mem_univ y⟩) :
    manifoldPullback θ F = manifoldPullback θ G := by
  have : F = G := morphism_eq_of_pointwise_eq F G (fun p => h p.val)
  rw [this]

/-- **Functoriality of `F^*θ`** along holomorphic maps of manifolds:
`g^*(F^*θ) = (F ∘ g)^*θ` (as geometric forms, i.e. coefficientwise on chart targets). -/
theorem manifoldPullback_nativeMorphism {l : ℕ} {W : Type} [TopologicalSpace W]
    [ChartedSpace (ComplexModel l) W] [IsComplexManifold l W] (θ : SpaceForm X k)
    (F : wholeModel (n := m) V ⟶ X) {g : W → V}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel l) 𝓘(ℂ, ComplexModel m) ∞ g) :
    (SmoothRealForm.pullback hg (manifoldPullback θ F)).GeometricallyEq
      (manifoldPullback θ (nativeMorphism hg ≫ F)) := by
  intro e z hz
  let d := complexChartAt (n := m) (g (e.val.symm z))
  have hzd : z ∈ coordinateDomain g e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [SmoothRealForm.pullback_coeff hg _ e d hzd,
    manifoldPullback_coeff θ (nativeMorphism hg ≫ F) e hz]
  have hcd : ContDiffOn ℂ ∞ (coordinateMap g e d) (coordinateDomain g e d) :=
    coordinateMap_contDiffOn hg e d
  have hmaps : MapsTo (coordinateMap g e d) (coordinateDomain g e d)
      (chartTarget d : Set (ComplexModel m)) :=
    fun w hw => coordinateMap_mem_target hw
  have hDU : coordinateDomain g e d ⊆ (chartTarget e : Set (ComplexModel l)) := fun w hw => hw.1
  have hpts : ∀ (y : (univ : Set (chartTarget e))) (hy : y.val.val ∈ coordinateDomain g e d),
      (chartInverse e ≫ nativeMorphism hg ≫ F).hom.left.base y =
        (chartInverse d ≫ F).hom.left.base ⟨⟨coordinateMap g e d y.val.val, hmaps hy⟩, trivial⟩ := by
    intro y hy
    have hpt : (nativeMorphism hg).hom.left.base ((chartInverse e).hom.left.base y) =
        (chartInverse d).hom.left.base ⟨⟨coordinateMap g e d y.val.val, hmaps hy⟩, trivial⟩ := by
      apply Subtype.ext
      rw [chartInverse_base]
      change g (e.val.symm y.val.val) = d.val.symm (d.val (g (e.val.symm y.val.val)))
      rw [d.val.left_inv hy.2]
    change F.hom.left.base ((nativeMorphism hg).hom.left.base ((chartInverse e).hom.left.base y)) =
      F.hom.left.base ((chartInverse d).hom.left.base _)
    rw [hpt]
  have h := pullbackToDomain_eq_pullbackForm θ (chartInverse e ≫ nativeMorphism hg ≫ F)
    (chartInverse d ≫ F) (coordinateDomain_isOpen hg e d) hDU hcd hmaps hpts hzd
  rw [h, manifoldPullback_coeff θ F d (coordinateMap_mem_target hzd)]
  rfl

end Pullback

/-! ### `θ`-psh functions -/

section PSH

variable {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]
  [IsComplexManifold m V]

/-- A function on `V` read on the complex space `wholeModel V`. -/
def ofManifold (u : V → EReal) : (wholeModel (n := m) V).obj.left → EReal :=
  fun p => u p.val

/-- **`θ`-psh on the complex space ⇒ `θ`-psh in charts.** A `θ`-psh function on
`wholeModel V` (`def:unibranch:L105`) satisfies the chart criterion of `θ`-plurisubharmonicity
for the manifold form `toManifoldForm θ`. -/
theorem thetaPlurisubharmonic_of_isThetaPSH {θ : SpaceForm (wholeModel (n := m) V) 2}
    {u : V → EReal} (h : (wholeModel (n := m) V).IsThetaPSH θ (ofManifold u)) :
    ThetaPlurisubharmonic (toManifoldForm θ) u := by
  intro e z hz
  obtain ⟨E, hE, -, g, hg, hres, hpsh⟩ := h ⟨e.val.symm z, mem_univ _⟩
  obtain ⟨W₁, hW₁, hzW₁, hW₁U, G, hG, hGmaps, hfac⟩ := exists_chartInverse_factor e E hz hE
  obtain ⟨b, hbG, -⟩ := hfac ⟨⟨z, hz⟩, trivial⟩ hzW₁
  obtain ⟨W₃, hW₃, hbW₃, -, ψ, hψ, hψeq⟩ :=
    SourceReducedComplexSpace.exists_ambient hpsh.2
      (LocalEmbedding.model E.ambient E.carrier E.analytic) b
  let W : Set (ComplexModel m) := W₁ ∩ G ⁻¹' W₃
  have hWo : IsOpen W := hG.continuousOn.isOpen_inter_preimage hW₁ hW₃
  have hzW : z ∈ W := ⟨hzW₁, by change G z ∈ W₃; rw [← hbG]; exact hbW₃⟩
  have hWW₁ : W ⊆ W₁ := inter_subset_left
  refine ⟨W, fun w => g (G w), hzW, ⟨hWo, fun w hw => hW₁U (hWW₁ hw), ?_, ?_⟩, ?_⟩
  · exact (hg.comp (hG.restrict_scalars ℝ) hGmaps).mono hWW₁
  · intro w hw
    rw [HolomorphicDDC.smoothDDC_comp hW₁ E.ambient.isOpen hG hg hGmaps (hWW₁ hw),
      toManifoldForm_coeff_eq_of_restrictsTo θ e hres hW₁ hW₁U
        (hG.differentiableOn (by simp)) hfac (hWW₁ hw)]
    rfl
  · have hψG : SGPT.Foundations.Analysis.PlurisubharmonicOn (fun w => ψ (G w)) W :=
      SGPT.Foundations.Analysis.Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
        hWo ((hG.differentiableOn (by simp)).mono hWW₁) (fun w hw => hw.2)
        (hψ.plurisubharmonicOn hW₃)
    refine (hψG.discPshOn.congr ?_).plurisubharmonicOn hWo
    intro w hw
    obtain ⟨c, hc, hpc⟩ := hfac ⟨⟨w, hW₁U (hWW₁ hw)⟩, trivial⟩ hw.1
    have hcW₃ : c.val.val ∈ W₃ := by rw [hc]; exact hw.2
    have hval := hψeq c hcW₃
    simp only [LocalEmbedding.model_toPoint] at hval
    change ψ (G w) = u (e.val.symm w) + (g (G w) : EReal)
    rw [← hc, ← hval, hpc, add_comm]
    rfl

/-- **`θ`-psh on the complex space ⇒ `θ`-psh potential on the manifold**, given density of the
finite locus (for instance on a unibranch target, by
`IsThetaPSH.dense_finite_pullback_of_isProperBimeromorphic`). -/
theorem isThetaPshPotential_of_isThetaPSH_of_dense {θ : SpaceForm (wholeModel (n := m) V) 2}
    {u : V → EReal} (h : (wholeModel (n := m) V).IsThetaPSH θ (ofManifold u))
    (hd : Dense {y : V | u y ≠ ⊥}) : IsThetaPshPotential (toManifoldForm θ) u := by
  refine ⟨thetaPlurisubharmonic_of_isThetaPSH h, ?_⟩
  intro x U hU hxU
  obtain ⟨y, hyU, hy⟩ := hd.inter_open_nonempty U hU ⟨x, hxU⟩
  exact ⟨y, hyU, hy⟩

/-- **`θ`-psh potential on the manifold ⇒ `θ`-psh on the complex space** (`def:unibranch:L105`,
second part), for the manifold form `toManifoldForm θ`. -/
theorem isThetaPSH_of_isThetaPshPotential {θ : SpaceForm (wholeModel (n := m) V) 2}
    {u : V → EReal} (h : IsThetaPshPotential (toManifoldForm θ) u) :
    (wholeModel (n := m) V).IsThetaPSH θ (ofManifold u) := by
  intro p
  let x : V := p.val
  let e : ComplexChart m V := complexChartAt (n := m) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxs
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := h.1 e (e.val x) hz
  obtain ⟨hWo, hWU, hρs, hρddc⟩ := hρ
  set e₀ := LocalEmbedding.ofChart (univ : Set V) (isComplexAnalyticSubset_univ (n := m)) x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hWo (e.val x) hzW
  let T : Opens (ComplexModel m) := ⟨Metric.ball (e.val x) r, Metric.isOpen_ball⟩
  have hTW : (T : Set (ComplexModel m)) ⊆ W := hball
  have hT : T ≤ e₀.ambient := fun w hw => hWU (hTW hw)
  have hC' : ∀ w, w ∈ (univ : Set T) ↔ Opens.inclusion hT w ∈ e₀.carrier :=
    fun _ => iff_of_true trivial trivial
  let E := e₀.restrictWith T hT univ hC'
  have hEpt : ∀ w : E.carrier, (E.toPoint w).val = e.val.symm w.val.val := fun _ => rfl
  have hTc : IsConnected (T : Set (ComplexModel m)) :=
    (convex_ball _ _).isConnected (Metric.nonempty_ball.mpr hr)
  refine ⟨E, ⟨⟨⟨e.val x, Metric.mem_ball_self hr⟩, trivial⟩, ?_⟩, hTc, ρ, hρs.mono hTW, ?_, ?_⟩
  · apply Subtype.ext
    change e.val.symm (e.val x) = x
    exact e.val.left_inv hxs
  · -- `θ` restricts to `ddᶜ ρ` on `E`
    intro i W' G hG
    apply vanishesOn_of_eqOn_zero
    intro w hw
    have hwT : w ∈ (T : Set (ComplexModel m)) := hG.2.1 hw
    rw [Pi.sub_apply, sub_eq_zero, hρddc (hTW hwT), toManifoldForm_coeff]
    -- a domain lift of the chart inverse through the transition `G`
    let A : SpaceForm.DomainLift θ (chartInverse e) ⟨w, hWU (hTW hwT)⟩ :=
      { chart := i
        window := W'
        isOpen := hG.1
        mem := hw
        subset := fun w' hw' => hWU (hTW (hG.2.1 hw'))
        lift := G
        holomorphic := contDiffOn_of_differentiableOn_complex hG.2.2.1 hG.1
        maps := hG.2.2.2.1
        factor := by
          intro y hy
          obtain ⟨c, hc, hpc⟩ := hG.2.2.2.2 ⟨⟨y.val.val, hG.2.1 hy⟩, trivial⟩ hy
          refine ⟨c, hc, hpc.trans ?_⟩
          apply Subtype.ext
          rfl }
    exact SpaceForm.pullbackToDomain_eq θ (chartInverse e) A hw
  · -- local plurisubharmonicity on the ball
    have key : SGPT.PSH.PSHOn (fun w => (ρ w : EReal) + u (e.val.symm w)) T := by
      refine ⟨?_, ?_⟩
      · have hT' : SGPT.Foundations.Analysis.PlurisubharmonicOn
            (fun w => chartFunction u e w + (ρ w : EReal)) T := fun w hw => hpsh w (hTW hw)
        refine hT'.discPshOn.congr ?_
        intro w _
        change u (e.val.symm w) + (ρ w : EReal) = (ρ w : EReal) + u (e.val.symm w)
        exact add_comm _ _
      · have hO : IsOpen (e.val.source ∩ e.val ⁻¹' (T : Set (ComplexModel m))) :=
          e.val.isOpen_inter_preimage T.isOpen
        obtain ⟨y, hyO, hy⟩ := h.2 x _ hO ⟨hxs, Metric.mem_ball_self hr⟩
        refine ⟨e.val y, hyO.2, ?_⟩
        rw [e.val.left_inv hyO.1]
        intro hbot
        exact hy ((EReal.add_eq_bot_iff.mp hbot).resolve_left (EReal.coe_ne_bot _))
    exact (isPSH_model_univ_iff hTc _).mpr key

end PSH

end SGPT.Unibranch.KSManifoldForm
