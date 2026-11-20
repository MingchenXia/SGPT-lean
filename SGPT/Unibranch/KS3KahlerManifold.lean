import SGPT.Unibranch.KS3KahlerSpace
import SGPT.Unibranch.KSManifoldForm

/-!
# A Kähler form on a smooth complex space is a Kähler form on the manifold

For `def:unibranch:L212` one needs resolutions of a compact Kähler space by compact
Kähler *manifolds*.  The resolutions produced by `G11` are smooth complex spaces `Y`
(`SourceReducedComplexSpace.IsSmooth`), and a connected smooth complex space is isomorphic to
`wholeModel M` for a complex manifold `M`
(`HironakaG1NoncompactSmoothComponentModel.exists_connected_native_manifold_model`).  This file
transports Kähler forms along such an isomorphism.

* `fderiv_injective_of_isIso`: if `F : wholeModel V ⟶ X` is an isomorphism of complex spaces,
  every holomorphic lift `G` of `F ∘ e⁻¹` (`e` an atlas chart of `V`) into a local embedding of
  `X` is an immersion (its complex derivative is injective): composing with a holomorphic lift
  `H` of `F⁻¹` gives the chart transition, whose derivative is invertible.
* `manifoldPullback_isStrictlyPositive_of_isIso`: hence the manifold form `F^*κ` of a Kähler form
  `κ` on `X` (`SpaceForm.IsKahler`) is strictly positive in every chart.
* `kahlerBackgroundOfIso`: the Kähler background `F^*κ` on `V`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
open SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex (mem_range_chartModelMap)

namespace SGPT.Unibranch.KS3KahlerManifold

open SourceReducedComplexSpace OriginalNativeModification KSManifoldForm

variable {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]
  [IsComplexManifold m V] {X : SourceReducedComplexSpace}

/-- Injectivity of the derivative of a chart transition (it has a holomorphic local inverse). -/
theorem chartTransition_fderiv_injective (e f : ComplexChart m V) {z : ComplexModel m}
    (hz : z ∈ (chartTransition e f).source) :
    Function.Injective (fderiv ℂ (chartTransition e f) z) := by
  set T := chartTransition e f
  have hTz : T z ∈ (chartTransition f e).source := T.map_source hz
  have hTd : DifferentiableAt ℂ T z :=
    (HolomorphicMaps.chartTransition_contDiffAt e f hz).differentiableAt (by simp)
  have hSd : DifferentiableAt ℂ (chartTransition f e) (T z) :=
    (HolomorphicMaps.chartTransition_contDiffAt f e hTz).differentiableAt (by simp)
  have hsymm : (chartTransition f e : ComplexModel m → ComplexModel m) = T.symm := rfl
  have hloc : (chartTransition f e ∘ T) =ᶠ[𝓝 z] id := by
    filter_upwards [T.open_source.mem_nhds hz] with w hw
    change T.symm (T w) = w
    exact T.left_inv hw
  have h1 : HasFDerivAt (chartTransition f e ∘ T)
      ((fderiv ℂ (chartTransition f e) (T z)).comp (fderiv ℂ T z)) z :=
    hSd.hasFDerivAt.comp z hTd.hasFDerivAt
  have h2 : HasFDerivAt (chartTransition f e ∘ T) (ContinuousLinearMap.id ℂ (ComplexModel m)) z :=
    (hasFDerivAt_id z).congr_of_eventuallyEq hloc
  have hder := h1.unique h2
  intro a b hab
  have h := congrArg (fun L : ComplexModel m →L[ℂ] ComplexModel m => L a) hder
  have h' := congrArg (fun L : ComplexModel m →L[ℂ] ComplexModel m => L b) hder
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h h'
  rw [← h, ← h', hab]

/-- **Lifts of an isomorphism are immersions.**  Let `F : wholeModel V ⟶ X` be an isomorphism of
complex spaces, `e` an atlas chart of `V`, and `G` a holomorphic lift of `F ∘ e⁻¹` into a local
embedding `E` of `X`, near `z`.  Then the complex derivative of `G` at `z` is injective. -/
theorem fderiv_injective_of_isIso (F : wholeModel (n := m) V ⟶ X) [IsIso F]
    (e : ComplexChart m V) {z : ComplexModel m} (hz : z ∈ e.val.target)
    (E : LocalEmbedding X) {W : Set (ComplexModel m)} (hW : IsOpen W) (hzW : z ∈ W)
    (hWU : W ⊆ (chartTarget e : Set (ComplexModel m)))
    {G : ComplexModel m → ComplexModel E.dim} (hG : ContDiffOn ℂ ∞ G W)
    (hfac : ∀ y : (univ : Set (chartTarget e)), y.val.val ∈ W → ∃ b : E.carrier,
      b.val.val = G y.val.val ∧ E.toPoint b = (chartInverse e ≫ F).hom.left.base y) :
    Function.Injective (fderiv ℂ G z) := by
  set x' : V := e.val.symm z
  let e₀' : ComplexChart m V := complexChartAt (n := m) x'
  let e₀ : LocalEmbedding (wholeModel (n := m) V) :=
    LocalEmbedding.ofChart (univ : Set V) (isComplexAnalyticSubset_univ (n := m)) x'
  have he₀pt : ∀ c : e₀.carrier, (e₀.toPoint c).val = e₀'.val.symm c.val.val := fun _ => rfl
  let Finv : X ⟶ wholeModel (n := m) V := inv F
  have hFF : ∀ p, Finv.hom.left.base (F.hom.left.base p) = p := by
    intro p
    have h := congrArg (fun k : wholeModel (n := m) V ⟶ wholeModel (n := m) V =>
      k.hom.left.base p) (IsIso.hom_inv_id F)
    exact h
  -- the base point
  let y₀ : (univ : Set (chartTarget e)) := ⟨⟨z, hz⟩, trivial⟩
  obtain ⟨b, hbG, hbpt⟩ := hfac y₀ hzW
  -- a holomorphic lift `H` of `F⁻¹` into the chart at `x'`
  let K : (modelOver E.ambient E.carrier).left ⟶ (wholeModel (n := m) V).obj.left :=
    E.map ≫ Finv.hom.left
  have hK : K ≫ (wholeModel (n := m) V).obj.hom = (modelOver E.ambient E.carrier).hom := by
    change (E.map ≫ Finv.hom.left) ≫ _ = _
    rw [Category.assoc, Over.w Finv.hom, E.overPoint]
  have hKb : K.base b = (chartInverse e).hom.left.base y₀ := by
    change Finv.hom.left.base (E.toPoint b) = _
    rw [hbpt]
    exact hFF _
  have hc : K.base b ∈ range e₀.toPoint := by
    rw [hKb]
    exact mem_range_chartModelMap (n := m) (univ : Set V) (mem_univ x')
  obtain ⟨W', hW', hbW', -, H, hH, -, hHfac⟩ := LocalEmbedding.exists_contDiffOn_factor K hK e₀ b hc
  -- `H ∘ G` is the chart transition near `z`
  set T := chartTransition e e₀'
  have hzT : z ∈ T.source := by
    refine ⟨hz, ?_⟩
    exact mem_complexChartAt_source (n := m) x'
  let N : Set (ComplexModel m) := (W ∩ G ⁻¹' W') ∩ T.source
  have hN : IsOpen N :=
    (hG.continuousOn.isOpen_inter_preimage hW hW').inter T.open_source
  have hzN : z ∈ N := ⟨⟨hzW, by change G z ∈ W'; rw [← hbG]; exact hbW'⟩, hzT⟩
  have hHG : (H ∘ G) =ᶠ[𝓝 z] T := by
    filter_upwards [hN.mem_nhds hzN] with w hw
    obtain ⟨⟨hwW, hwW'⟩, hwT⟩ := hw
    let yw : (univ : Set (chartTarget e)) := ⟨⟨w, hWU hwW⟩, trivial⟩
    obtain ⟨bw, hbwG, hbwpt⟩ := hfac yw hwW
    obtain ⟨z', hz'H, hz'pt⟩ := hHfac bw (by rw [hbwG]; exact hwW')
    have hKbw : K.base bw = (chartInverse e).hom.left.base yw := by
      change Finv.hom.left.base (E.toPoint bw) = _
      rw [hbwpt]
      exact hFF _
    have hval : e₀'.val.symm z'.val.val = e.val.symm w := by
      have h := congrArg Subtype.val (hz'pt.trans hKbw)
      rw [he₀pt] at h
      exact h
    have htarget : z'.val.val ∈ e₀'.val.target := z'.val.property
    change H (G w) = e₀'.val (e.val.symm w)
    rw [← hbwG, ← hz'H, ← hval, e₀'.val.right_inv htarget]
  -- derivatives
  have hGd : DifferentiableAt ℂ G z :=
    (hG.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hzW)
  have hHd : DifferentiableAt ℂ H (G z) := by
    have hGzW' : G z ∈ W' := by rw [← hbG]; exact hbW'
    exact (hH.differentiableOn (by simp)).differentiableAt (hW'.mem_nhds hGzW')
  have h1 : HasFDerivAt (H ∘ G) ((fderiv ℂ H (G z)).comp (fderiv ℂ G z)) z :=
    hHd.hasFDerivAt.comp z hGd.hasFDerivAt
  have hTd : DifferentiableAt ℂ T z :=
    (HolomorphicMaps.chartTransition_contDiffAt e e₀' hzT).differentiableAt (by simp)
  have h2 : HasFDerivAt (H ∘ G) (fderiv ℂ T z) z :=
    hTd.hasFDerivAt.congr_of_eventuallyEq hHG
  have hder := h1.unique h2
  intro a a' haa
  apply chartTransition_fderiv_injective e e₀' hzT
  have e1 := congrArg (fun L => L a) hder
  have e2 := congrArg (fun L => L a') hder
  simp only [ContinuousLinearMap.comp_apply] at e1 e2
  rw [haa] at e1
  exact e1.symm.trans e2

/-- **Strict positivity of `F^*κ`.**  If `F : wholeModel V ⟶ X` is an isomorphism and `κ` is a
Kähler form on `X`, the manifold form `F^*κ` is strictly positive in every chart of `V`. -/
theorem manifoldPullback_isStrictlyPositive_of_isIso {κ : SpaceForm X 2}
    (hκ : κ.IsKahler) (F : wholeModel (n := m) V ⟶ X) [IsIso F] (e : ComplexChart m V)
    {z : ComplexModel m} (hz : z ∈ e.val.target) :
    IsStrictlyPositive ((manifoldPullback κ F).coeff e z) := by
  let y₀ : (univ : Set (chartTarget e)) := ⟨⟨z, hz⟩, trivial⟩
  obtain ⟨E, hE, v, -, -, hpos, hres⟩ := hκ ((chartInverse e ≫ F).hom.left.base y₀)
  obtain ⟨W, hW, hzW, hWU, G, hG, hGmaps, hfac⟩ := LocalEmbedding.exists_contDiffOn_factor
    (chartInverse e ≫ F).hom.left (Over.w (chartInverse e ≫ F).hom) E y₀ hE
  rw [manifoldPullback_coeff κ F e hz,
    SpaceForm.pullbackToDomain_eq_of_restrictsTo κ (chartInverse e ≫ F) hres hW hWU
      (hG.differentiableOn (by simp)) hfac hzW]
  have hinj := fderiv_injective_of_isIso F e hz E hW hzW hWU hG hfac
  have hGd : DifferentiableAt ℂ G z :=
    (hG.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hzW)
  intro u hu
  have hvec : ((fderiv ℝ G z) ∘ ![u, Complex.I • u]) =
      ![fderiv ℂ G z u, Complex.I • fderiv ℂ G z u] := by
    rw [hGd.fderiv_restrictScalars ℝ]
    funext i
    fin_cases i
    · rfl
    · exact (fderiv ℂ G z).map_smul Complex.I u
  change 0 < v (G z) ((fderiv ℝ G z) ∘ ![u, Complex.I • u])
  rw [hvec]
  refine (hpos (G z) (hGmaps hzW)).2 _ ?_
  intro h0
  exact hu (hinj (h0.trans (fderiv ℂ G z).map_zero.symm))

/-- **The Kähler background `F^*κ`** on a manifold `V`, for an isomorphism of complex spaces
`F : wholeModel V ⟶ X` and a Kähler form `κ` on `X`. -/
def kahlerBackgroundOfIso {κ : SpaceForm X 2} (hκ : κ.IsKahler)
    (F : wholeModel (n := m) V ⟶ X) [IsIso F] : KahlerBackground m V where
  form := manifoldPullbackClosed κ hκ.isClosed hκ.isOneOne F
  isKahler := by
    refine ⟨fun e z hz => ⟨?_, ?_⟩, (manifoldPullbackClosed κ hκ.isClosed hκ.isOneOne F).property.1⟩
    · exact (manifoldPullbackClosed κ hκ.isClosed hκ.isOneOne F).property.2 e z hz
    · exact manifoldPullback_isStrictlyPositive_of_isIso hκ F e hz

@[simp] theorem kahlerBackgroundOfIso_form {κ : SpaceForm X 2} (hκ : κ.IsKahler)
    (F : wholeModel (n := m) V ⟶ X) [IsIso F] :
    (kahlerBackgroundOfIso hκ F).form.val = manifoldPullback κ F := rfl

/-- A complex manifold isomorphic (as a complex space) to a Kähler space admits a Kähler
background. -/
theorem nonempty_kahlerBackground_of_iso (hX : X.IsKahlerSpace)
    (F : wholeModel (n := m) V ⟶ X) [IsIso F] : Nonempty (KahlerBackground m V) := by
  obtain ⟨κ, hκ⟩ := hX
  exact ⟨kahlerBackgroundOfIso hκ F⟩

end SGPT.Unibranch.KS3KahlerManifold
