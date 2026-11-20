import SGPT.NAPotential.FSPosImmersion
import SGPT.Okounkov.SchemeLineBundleMetricGeometry
import SGPT.Foundations.Schemes.NativePositiveCoordinateCrossCoefficients

/-!
# The Fubini–Study metric on `𝒪_X(1)`

Blueprint `claude-fs-pos:metric`.

Let `X` be smooth of relative dimension `n` over `ℂ` with a closed projective embedding
`E.map : X ⟶ ℙᴺ`.

* `hyperplaneBundle E = E.map^* 𝒪(1)`, the genuine sheaf pullback of the twisting sheaf of
  `ℙᴺ = Proj ℂ[x₀, …, x_N]`, with its atlas `hyperplaneAtlas E` of pulled-back coordinate frames
  on the opens `Uᵢ = E.map⁻¹ D₊(xᵢ)`.
* `coordSection E k U`: the section `x_k|_U` of `𝒪_X(1)`; `coordCoef E α k = x_k / α ∈ Γ(X, U)`
  its coefficient in a local frame `α` on `U`; in the atlas frame `xᵢ` it is the ratio
  `x_k / x_i` (`coordCoef_atlas`).
* `fubiniStudyMetric f n E`: **the Fubini–Study metric**, as a `SchemeLineBundleMetric`
  (a positive smooth squared norm of every algebraic local frame, with the transition law):
  `|α|²(p) = (∑_k |(x_k / α)(p)|²)⁻¹`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.FSPos

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov
open scoped Topology Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (E : ClosedProjectiveEmbedding f)

/-! ### The algebraic line bundle `𝒪_X(1)` and its coordinate sections -/

/-- `𝒪_X(1) = E.map^* 𝒪_{ℙᴺ}(1)`. -/
abbrev hyperplaneBundle : X.Modules :=
  (Scheme.Modules.pullback E.map).obj (polynomialProjTwistingLine ℂ E.ambientDimension).sheaf

/-- The atlas of `𝒪_X(1)` by the pulled-back coordinate frames `xᵢ` on `Uᵢ = E.map⁻¹ D₊(xᵢ)`
(the atlas `nativePolynomialPullbackAtlas`, with its index type and opens displayed). -/
abbrev hyperplaneAtlas : LineBundleAtlas (hyperplaneBundle E) where
  I := Fin (E.ambientDimension + 1)
  opens := coordOpen E
  covers := (nativePolynomialPullbackAtlas ℂ E.ambientDimension E.map).covers
  frame := (nativePolynomialPullbackAtlas ℂ E.ambientDimension E.map).frame

theorem hyperplaneAtlas_opens (i : Fin (E.ambientDimension + 1)) :
    (hyperplaneAtlas E).opens i = coordOpen E i := rfl

/-- The pulled-back coordinate `x_k`, as a map `𝒪_X → 𝒪_X(1)`. -/
def coordHom (k : Fin (E.ambientDimension + 1)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ hyperplaneBundle E :=
  nativePullbackGlobalHom E.map (homogeneousPolynomialCoordinateGlobalHom (K := ℂ) k)

/-- The section `x_k|_U` of `𝒪_X(1)`. -/
def coordSection (k : Fin (E.ambientDimension + 1)) (U : X.Opens) :
    bundleSections (hyperplaneBundle E) U :=
  (coordHom E k).val.app (.op U) (1 : Γ(X, U))

theorem coordSection_restrict (k : Fin (E.ambientDimension + 1)) {U V : X.Opens} (h : V ⟶ U) :
    (hyperplaneBundle E).val.map h.op (coordSection E k U) = coordSection E k V := by
  have hn := PresheafOfModules.naturality_apply (coordHom E k).val h.op (1 : Γ(X, U))
  change (coordHom E k).val.app (.op V)
      ((SheafOfModules.unit X.ringCatSheaf).val.map h.op (1 : Γ(X, U))) =
    (hyperplaneBundle E).val.map h.op ((coordHom E k).val.app (.op U) (1 : Γ(X, U))) at hn
  have h1 : (SheafOfModules.unit X.ringCatSheaf).val.map h.op (1 : Γ(X, U)) = (1 : Γ(X, V)) :=
    (X.presheaf.map h.op).hom.map_one
  rw [h1] at hn
  exact hn.symm

/-- The coefficient `x_k / α ∈ Γ(X, U)` of the coordinate section in a local frame `α`. -/
def coordCoef {U : X.Opens} (α : LocalBundleFrame (hyperplaneBundle E) U)
    (k : Fin (E.ambientDimension + 1)) : Γ(X, U) :=
  α.coefficients (𝟙 U) (coordSection E k U)

theorem coordCoef_restrict {U V : X.Opens} (α : LocalBundleFrame (hyperplaneBundle E) U)
    (h : V ⟶ U) (k : Fin (E.ambientDimension + 1)) :
    α.coefficients h (coordSection E k V) = X.presheaf.map h.op (coordCoef E α k) := by
  have hc := α.coefficients_restrict (𝟙 U) h (coordSection E k U)
  rw [Category.comp_id, coordSection_restrict] at hc
  exact hc

/-- In the atlas frame `xᵢ`, the coefficient of `x_k` is the ratio `x_k / x_i`. -/
theorem coordCoef_atlas (i k : Fin (E.ambientDimension + 1)) :
    coordCoef E ((hyperplaneAtlas E).frame i) k = ratio E i k :=
  nativePolynomialPullbackCoordinate_cross_coefficients ℂ E.ambientDimension E.map i k

/-! ### The analytic coordinate functions and the Fubini–Study norm -/

variable (f) (n : ℕ) [SmoothOfRelativeDimension n f]

local instance fsPosMetricTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance fsPosMetricCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- The analytic function of `x_k / α` on `U(ℂ)`. -/
def coordFun {U : X.Opens} (α : LocalBundleFrame (hyperplaneBundle E) U)
    (k : Fin (E.ambientDimension + 1)) : SchemeComplexPoint f → ℂ :=
  schemeOpenRegularFunction f n E U (coordCoef E α k)

theorem coordFun_transition {U V : X.Opens} (α : LocalBundleFrame (hyperplaneBundle E) U)
    (β : LocalBundleFrame (hyperplaneBundle E) V) (k : Fin (E.ambientDimension + 1))
    (p : SchemeComplexPoint f) (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V) :
    coordFun f E n β k p = schemeFrameTransition f n E α β p * coordFun f E n α k p := by
  have hp : schemeComplexPointImage f p ∈ U ⊓ V := ⟨hpU, hpV⟩
  have hα : schemeOpenRegularFunction f n E (U ⊓ V)
      (α.coefficients (homOfLE inf_le_left) (coordSection E k (U ⊓ V))) p =
        coordFun f E n α k p := by
    rw [coordCoef_restrict]
    exact schemeOpenRegularFunction_restrict f n E (U ⊓ V) U inf_le_left _ hp
  have hβ : schemeOpenRegularFunction f n E (U ⊓ V)
      (β.coefficients (homOfLE inf_le_right) (coordSection E k (U ⊓ V))) p =
        coordFun f E n β k p := by
    rw [coordCoef_restrict]
    exact schemeOpenRegularFunction_restrict f n E (U ⊓ V) V inf_le_right _ hp
  have hm := schemeOpenRegularFunction_mul f n E (U ⊓ V)
    (localBundleFrameTransition α β (homOfLE inf_le_left) (homOfLE inf_le_right)).val
    (α.coefficients (homOfLE inf_le_left) (coordSection E k (U ⊓ V))) hp
  have ht := congrArg (fun r : Γ(X, U ⊓ V) => schemeOpenRegularFunction f n E (U ⊓ V) r p)
    (localBundleFrameTransition_coefficients α β (homOfLE inf_le_left) (homOfLE inf_le_right)
      (coordSection E k (U ⊓ V)))
  rw [← hβ, ← hα]
  exact ht.trans hm

theorem coordFun_atlas_self (i : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ coordOpen E i) :
    coordFun f E n ((hyperplaneAtlas E).frame i) i p = 1 := by
  rw [coordFun, coordCoef_atlas, ratio_self]
  exact schemeOpenRegularFunction_one f n E (coordOpen E i) hp

/-- `∑_k |x_k / α|²` on `U(ℂ)`. -/
def coordNormSq {U : X.Opens} (α : LocalBundleFrame (hyperplaneBundle E) U)
    (p : SchemeComplexPoint f) : ℝ :=
  ∑ k, Complex.normSq (coordFun f E n α k p)

theorem coordNormSq_transition {U V : X.Opens} (α : LocalBundleFrame (hyperplaneBundle E) U)
    (β : LocalBundleFrame (hyperplaneBundle E) V) (p : SchemeComplexPoint f)
    (hpU : schemeComplexPointImage f p ∈ U) (hpV : schemeComplexPointImage f p ∈ V) :
    coordNormSq f E n β p =
      Complex.normSq (schemeFrameTransition f n E α β p) * coordNormSq f E n α p := by
  unfold coordNormSq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [coordFun_transition f E n α β k p hpU hpV, Complex.normSq_mul]

/-- The coordinates have no common zero. -/
theorem coordNormSq_pos {U : X.Opens} (α : LocalBundleFrame (hyperplaneBundle E) U)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p ∈ U) :
    0 < coordNormSq f E n α p := by
  obtain ⟨i, hi⟩ : ∃ i : Fin (E.ambientDimension + 1),
      schemeComplexPointImage f p ∈ coordOpen E i :=
    (hyperplaneAtlas E).covers (schemeComplexPointImage f p)
  have hne : coordFun f E n α i p ≠ 0 := by
    rw [coordFun_transition f E n ((hyperplaneAtlas E).frame i) α i p hi hp,
      coordFun_atlas_self f E n i p hi, mul_one]
    exact schemeFrameTransition_ne_zero f n E _ _ p hi hp
  exact lt_of_lt_of_le (Complex.normSq_pos.mpr hne)
    (Finset.single_le_sum (f := fun k => Complex.normSq (coordFun f E n α k p))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i))

theorem coordNormSq_smooth {U : X.Opens} (α : LocalBundleFrame (hyperplaneBundle E) U)
    (e : ComplexChart n (SchemeComplexPoint f)) :
    ContDiffOn ℝ ∞ (fun z => coordNormSq f E n α (e.val.symm z))
      (e.val.target ∩ e.val.symm ⁻¹' (schemeComplexPointImage f ⁻¹' U)) := by
  let := E.isSeparated
  let := E.quasiCompact
  let := schemeAnalyticTN_isComplexManifold f n
  intro z hz
  refine ContDiffAt.contDiffWithinAt ?_
  unfold coordNormSq
  refine ContDiffAt.sum fun k _ => ?_
  apply BlanchardWeight.BlanchardData.contDiffAt_normSq_comp
  have hU : IsOpen (schemeComplexPointImage f ⁻¹' (U : Set X)) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [(e.val.isOpen_inter_preimage_symm hU).mem_nhds hz] with w hw
  exact FactorizedWeightForm.differentiableAt_comp_chart_symm e hw.1
    (schemeOpenRegularFunction_holomorphicAt f n E U _ (e.val.symm w) hw.2).mdifferentiableAt

/-- **The Fubini–Study metric on `𝒪_X(1)`**: `|α|² = (∑_k |x_k / α|²)⁻¹` for every algebraic
local frame `α`. -/
def fubiniStudyMetric : SchemeLineBundleMetric f n E (hyperplaneBundle E) where
  frameNormSq α p := (coordNormSq f E n α p)⁻¹
  smooth α e := (coordNormSq_smooth f E n α e).inv fun z hz =>
    (coordNormSq_pos f E n α _ hz.2).ne'
  positive α p hp := inv_pos.mpr (coordNormSq_pos f E n α p hp)
  transition α β p hpU hpV := by
    have hne : Complex.normSq (schemeFrameTransition f n E α β p) ≠ 0 :=
      (Complex.normSq_pos.mpr (schemeFrameTransition_ne_zero f n E α β p hpU hpV)).ne'
    rw [coordNormSq_transition f E n α β p hpU hpV, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ hne, one_mul]

theorem fubiniStudyMetric_frameNormSq {U : X.Opens}
    (α : LocalBundleFrame (hyperplaneBundle E) U) (p : SchemeComplexPoint f) :
    (fubiniStudyMetric f E n).frameNormSq α p = (coordNormSq f E n α p)⁻¹ := rfl

end SGPT.NAPotential.FSPos
