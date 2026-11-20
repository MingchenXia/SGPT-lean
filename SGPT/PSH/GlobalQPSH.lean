import SGPT.PSH.PlurifineQuasiPSH
import SGPT.PSH.QuasiExtrema
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe v
variable {X : Type v} [TopologicalSpace X]

/-- Actual real differential forms in the original varying-dimension atlas:
coefficients satisfy the genuine derivative tensor transformation law. -/
structure AtlasSmoothRealForm (A : VariableComplexAtlas X) (k : ℕ) where
  coeff : (i : A.Index) → ComplexModel (A.dimension i) →
    (ComplexModel (A.dimension i)) [⋀^Fin k]→L[ℝ] ℝ
  smooth : ∀ i, ContDiffOn ℝ ∞ (coeff i) (A.chart i).target
  compatible : ∀ i j z, z ∈ ((A.chart i).symm.trans (A.chart j)).source →
    ∀ w : Fin k → ComplexModel (A.dimension i),
      coeff i z w = coeff j (((A.chart i).symm.trans (A.chart j)) z)
        (fun a ↦ fderiv ℝ ((A.chart i).symm.trans (A.chart j)) z (w a))

variable {A : VariableComplexAtlas X}

/-- A genuine global smooth closed real form of type (1,1). -/
structure AtlasClosedRealOneOneForm (A : VariableComplexAtlas X) extends
    AtlasSmoothRealForm A 2 where
  closed : ∀ i z, z ∈ (A.chart i).target → extDeriv (coeff i) z = 0
  typeOneOne : ∀ i z, z ∈ (A.chart i).target → IsOneOne (coeff i z)

/-- Smoothness on the original manifold open set is tested in every chart. -/
def ChartSmoothOn (g : X → ℝ) (U : Set X) : Prop :=
  ∀ i, ContDiffOn ℝ ∞ (g ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)

/-- Every actual local potential, as a function on the original open set,
represents the entire differential two-form in every original chart. -/
def IsAtlasLocalPotential (θ : AtlasClosedRealOneOneForm A)
    (U : Set X) (g : X → ℝ) : Prop :=
  IsOpen U ∧ A.ChartSmoothOn g U ∧ ∀ i,
    EqOn (smoothDDC (g ∘ (A.chart i).symm)) (θ.coeff i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)

/-- The source universal local-potential definition, on the original manifold.
No particular potential or local PSH conclusion is stored in the form. -/
def IsThetaPSH (θ : AtlasClosedRealOneOneForm A) (u : X → EReal) : Prop :=
  (∀ x, u x ≠ ⊤) ∧ ∀ (U : Set X) (g : X → ℝ),
    A.IsAtlasLocalPotential θ U g → A.IsPSHOn (fun x ↦ u x + (g x : EReal)) U

/-- The exact existential global-background definition of quasi-PSH. -/
def IsQPSH (u : X → EReal) : Prop :=
  ∃ θ : AtlasClosedRealOneOneForm A, A.IsThetaPSH θ u

/-- Genuine local dd-bar existence is reused, including dimension zero. -/
theorem exists_chart_local_potential (θ : AtlasClosedRealOneOneForm A)
    (i : A.Index) {z : ComplexModel (A.dimension i)} (hz : z ∈ (A.chart i).target) :
    ∃ (W : Set (ComplexModel (A.dimension i))) (ρ : ComplexModel (A.dimension i) → ℝ),
      z ∈ W ∧ IsOpen W ∧ W ⊆ (A.chart i).target ∧ ContDiffOn ℝ ∞ ρ W ∧
        EqOn (smoothDDC ρ) (θ.coeff i) W :=
  SGPT.Foundations.Analysis.Pending.LocalPotentials.exists_smooth_local_ddc_potential
    (A.chart i).open_target (θ.coeff i) (θ.smooth i) (θ.closed i) (θ.typeOneOne i) hz

/-- A genuine coordinate potential becomes an actual manifold local potential.
The all-chart equality is proved by the existing complete dd-c pullback law. -/
theorem coordinate_potential_isAtlasLocalPotential (θ : AtlasClosedRealOneOneForm A)
    (i : A.Index) {W : Set (ComplexModel (A.dimension i))}
    {ρ : ComplexModel (A.dimension i) → ℝ} (hW : IsOpen W)
    (_hWe : W ⊆ (A.chart i).target) (hρ : ContDiffOn ℝ ∞ ρ W)
    (heq : EqOn (smoothDDC ρ) (θ.coeff i) W) :
    A.IsAtlasLocalPotential θ ((A.chart i).source ∩ (A.chart i) ⁻¹' W)
      (ρ ∘ (A.chart i)) := by
  let U := (A.chart i).source ∩ (A.chart i) ⁻¹' W
  have hU : IsOpen U := (A.chart i).isOpen_inter_preimage hW
  refine ⟨hU, ?_, ?_⟩
  · intro j
    let D := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U
    let F := (A.chart j).symm.trans (A.chart i)
    have hDF : D ⊆ F.source := fun _ hz ↦ ⟨hz.1, hz.2.1⟩
    have hF : DifferentiableOn ℂ (F : ComplexModel (A.dimension j) →
        ComplexModel (A.dimension i)) F.source := A.holomorphic j i
    have hFS : ContDiffOn ℂ ∞ (F : ComplexModel (A.dimension j) →
        ComplexModel (A.dimension i)) F.source := contDiffOn_of_differentiableOn_complex hF F.open_source
    have hFD : ContDiffOn ℂ ∞ F D := hFS.mono hDF
    exact hρ.comp (hFD.restrict_scalars ℝ) (fun _ hz ↦ hz.2.2)
  · intro j z hz
    let D := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U
    let F := (A.chart j).symm.trans (A.chart i)
    have hD : IsOpen D := (A.chart j).isOpen_inter_preimage_symm hU
    have hDF : D ⊆ F.source := fun _ hy ↦ ⟨hy.1, hy.2.1⟩
    have hF : DifferentiableOn ℂ (F : ComplexModel (A.dimension j) →
        ComplexModel (A.dimension i)) F.source := A.holomorphic j i
    have hFS : ContDiffOn ℂ ∞ (F : ComplexModel (A.dimension j) →
        ComplexModel (A.dimension i)) F.source := contDiffOn_of_differentiableOn_complex hF F.open_source
    have hFD : ContDiffOn ℂ ∞ F D := hFS.mono hDF
    change smoothDDC (fun y ↦ ρ (F y)) z = θ.coeff j z
    have hFz : F z ∈ W := hz.2.2
    have heqF : smoothDDC ρ (F z) = θ.coeff i (F z) := heq hFz
    rw [HolomorphicDDC.smoothDDC_comp hD hW hFD hρ
      (fun _ hy ↦ hy.2.2) hz, heqF]
    ext w
    exact (θ.compatible j i z (hDF hz) w).symm

/-- Local potentials really exist near every manifold point; universal testing
in the source definition therefore cannot be vacuous. -/
theorem exists_atlas_local_potential (θ : AtlasClosedRealOneOneForm A) (x : X) :
    ∃ U g, x ∈ U ∧ A.IsAtlasLocalPotential θ U g := by
  obtain ⟨i, hi⟩ := A.cover x
  obtain ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩ :=
    exists_chart_local_potential θ i ((A.chart i).map_source hi)
  exact ⟨(A.chart i).source ∩ (A.chart i) ⁻¹' W, ρ ∘ (A.chart i),
    ⟨hi, hzW⟩, coordinate_potential_isAtlasLocalPotential θ i hW hWe hρ heq⟩


/-- The universal original local-potential condition yields actual local
quasi-PSH germs in every chart, using produced potentials, not assumed ones. -/
theorem IsThetaPSH.chart_quasiPSH {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hu : A.IsThetaPSH θ u) (i : A.Index) :
    QuasiPlurisubharmonicOn (A.coordinate u i) (A.chart i).target := by
  intro z hz
  obtain ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩ := exists_chart_local_potential θ i hz
  let U := (A.chart i).source ∩ (A.chart i) ⁻¹' W
  let g := ρ ∘ (A.chart i)
  have hg : A.IsAtlasLocalPotential θ U g :=
    coordinate_potential_isAtlasLocalPotential θ i hW hWe hρ heq
  have hpsh := hu.2 U g hg
  have hzU : (A.chart i).symm z ∈ U := by
    refine ⟨(A.chart i).map_target hz, ?_⟩
    change (A.chart i) ((A.chart i).symm z) ∈ W
    simpa only [(A.chart i).right_inv hz] using hzW
  refine ⟨A.coordinate (fun x ↦ u x + (g x : EReal)) i, fun y ↦ -ρ y,
    hpsh.chartPlurisubharmonic i z ⟨hz, hzU⟩, ?_, ?_⟩
  · filter_upwards [hW.mem_nhds hzW] with y hy
    exact ((hρ.neg) y hy).contDiffAt (hW.mem_nhds hy)
  · filter_upwards [hW.mem_nhds hzW] with y hy
    change u ((A.chart i).symm y) =
      (u ((A.chart i).symm y) + (ρ ((A.chart i) ((A.chart i).symm y)) : EReal)) +
        ((-ρ y : ℝ) : EReal)
    rw [(A.chart i).right_inv (hWe hy), add_assoc, ← EReal.coe_add,
      add_neg_cancel, EReal.coe_zero, add_zero]

theorem IsQPSH.chart_quasiPSH {u : X → EReal} (hu : A.IsQPSH u) (i : A.Index) :
    QuasiPlurisubharmonicOn (A.coordinate u i) (A.chart i).target := by
  obtain ⟨θ, hθ⟩ := hu
  exact hθ.chart_quasiPSH i

theorem IsQPSH.ne_top {u : X → EReal} (hu : A.IsQPSH u) (x : X) : u x ≠ ⊤ := by
  obtain ⟨θ, hθ⟩ := hu
  exact hθ.1 x

/-- Source prop:pshfunFcont for the genuine existential global closed-form
QPSH definition, retaining all varying and zero chart dimensions. -/
theorem IsQPSH.continuous_plurifine {u : X → EReal} (hu : A.IsQPSH u) :
    @Continuous X EReal A.plurifineTopology inferInstance u :=
  continuous_plurifine_of_chart_quasiPSH hu.chart_quasiPSH

/-- Source cor:diffpshFopen on the actual original manifold, including poles. -/
theorem IsQPSH.isOpen_plurifine_gt {u w : X → EReal}
    (hu : A.IsQPSH u) (hw : A.IsQPSH w) :
    IsOpen[A.plurifineTopology] {x | u x > w x} :=
  isOpen_plurifine_lt_of_chart_quasiPSH hw.chart_quasiPSH hu.chart_quasiPSH

/-- True global-QPSH extrema survive every actual source pluripolar deletion. -/
theorem IsQPSH.extrema_eq_off_pluripolar {u : X → EReal} (hu : A.IsQPSH u)
    {Z : Set X} (hZ : A.LocallyPluripolar Z) :
    (⨆ x : ↥(Zᶜ), u x.val) = (⨆ x : X, u x) ∧
    (⨅ x : ↥(Zᶜ), u x.val) = (⨅ x : X, u x) :=
  @extrema_eq_of_dense_compl X A.plurifineTopology Z hZ.dense_plurifine_compl
    u hu.continuous_plurifine

/-- Exact quasi-extrema follow from genuine global QPSH and actual dense
pluripolar complements; no continuity premise remains. -/
theorem IsQPSH.quasiExtrema_eq {u : X → EReal} (hu : A.IsQPSH u)
    {Z : Set X} (hZ : A.LocallyPluripolar Z) :
    A.quasiSup (fun x : ↥(Zᶜ) ↦ u x.val) = (⨆ x : X, u x) ∧
    A.quasiInf (fun x : ↥(Zᶜ) ↦ u x.val) = (⨅ x : X, u x) :=
  quasiExtrema_eq_of_continuous hu.continuous_plurifine hZ

/-- Source cor:diffsupinfindeppluripolar on the original first non-pole locus. -/
theorem IsQPSH.difference_extrema_eq_on_left_finite_locus {u w : X → EReal}
    (hu : A.IsQPSH u) (hw : A.IsQPSH w) {Z : Set X} (hZ : A.LocallyPluripolar Z) :
    (⨆ x : {x : {y | u y ≠ ⊥} | x.val ∉ Z}, u x.val.val - w x.val.val) =
      (⨆ x : {y | u y ≠ ⊥}, u x.val - w x.val) ∧
    (⨅ x : {x : {y | u y ≠ ⊥} | x.val ∉ Z}, u x.val.val - w x.val.val) =
      (⨅ x : {y | u y ≠ ⊥}, u x.val - w x.val) :=
  @extrema_difference_eq_on_open_finite_locus X A.plurifineTopology u w
    hu.continuous_plurifine hw.continuous_plurifine hu.ne_top {x | u x ≠ ⊥} Z
    (@isOpen_finiteLocus_of_continuous X A.plurifineTopology u hu.continuous_plurifine)
    hZ.dense_plurifine_compl (fun _ hx ↦ Or.inl hx)

/-- The source's second permitted non-pole locus retains potentially infinite
original differences and also avoids every doubled-pole subtraction. -/
theorem IsQPSH.difference_extrema_eq_on_right_finite_locus {u w : X → EReal}
    (hu : A.IsQPSH u) (hw : A.IsQPSH w) {Z : Set X} (hZ : A.LocallyPluripolar Z) :
    (⨆ x : {x : {y | w y ≠ ⊥} | x.val ∉ Z}, u x.val.val - w x.val.val) =
      (⨆ x : {y | w y ≠ ⊥}, u x.val - w x.val) ∧
    (⨅ x : {x : {y | w y ≠ ⊥} | x.val ∉ Z}, u x.val.val - w x.val.val) =
      (⨅ x : {y | w y ≠ ⊥}, u x.val - w x.val) :=
  @extrema_difference_eq_on_open_finite_locus X A.plurifineTopology u w
    hu.continuous_plurifine hw.continuous_plurifine hu.ne_top {x | w x ≠ ⊥} Z
    (@isOpen_finiteLocus_of_continuous X A.plurifineTopology w hw.continuous_plurifine)
    hZ.dense_plurifine_compl (fun _ hx ↦ Or.inr hx)

end SGPT.PSH.VariableComplexAtlas
