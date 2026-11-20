import SGPT.Foundations.Analysis.Pending.GraphTangentialAlgebra
import SGPT.Foundations.Analysis.Pending.SkodaElMirHolomorphic

set_option autoImplicit false

/-!
# The graph retraction in product charts

Let `f : V → X` be a holomorphic map between complex manifolds of the same dimension `n`, and
`Φ(v, x) = (v, f v)` the holomorphic retraction of `V × X` onto the graph `Γ_f` (`graphProjMap`).
In the product chart `E` at a graph point `(v₀, f v₀)` (charts `a` at `v₀`, `b` at `f v₀`), with
`F = b ∘ f ∘ a⁻¹` the coordinate representative of `f`, on the open set
`graphDomain n f v₀ = {ζ = (z, w) ∈ E.target | z ∈ dom F}`:

* `Φ` reads `ζ = (z, w) ↦ (z, F z)` (`coordinateMap_graphProjMap`);
* its derivative is the `ℂ`-linear projection `π_ζ = graphProj (DF(z))`, `(ξ, η) ↦ (ξ, DF(z) ξ)`
  (`hasFDerivAt_graphModel`), so `(Φ^*b)_E(ζ) = b_E(Φ_E ζ) ∘ π_ζ` (`pullback_graphProjMap_coeff`);
* `ξ - π_ζ ξ = ∑ₐ ℓₐ(ξ) Nₐ` with the normal vectors `Nₐ` of the diagonal case and
  `ℓₐ = Re dLₐ(ζ)`, where `Lₐ(ζ) = (1, -i)_{a.1} (w - F z)_{a.2}` are HOLOMORPHIC normal coordinates
  of the graph (`sub_graphProj_eq`, `hasFDerivAt_re_graphNormalFun`);
* on the graph, `Φ_E ζ = ζ` and `Lₐ ζ = 0` (`graph_chart`).

Two chart-level tools are proved for arbitrary charts: cut-offs of real and imaginary parts of a
holomorphic function form a holomorphic pair in the sense of `NormalDirectionVanishing.IsHoloPairOn`
(`isHoloPairOn_re_im`, generalizing the linear `DiagonalTangentialReduction.isHoloPairOn_normal`), and
`d(χg ∧ dχk) = dg ∧ dk` near a point where the cut-off `χ` is `1`, for NONLINEAR `g`, `k`
(`exactPair_cutoff_coeff_of_hasFDerivAt`).

Step G3 of the graph support plan,
for TN-CLASSICAL's graph route of the `(P)` step of Boucksom 4.8 (earlier discussion the statement under discussion).
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.GraphTangentialChart

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses ProductComplexManifold
  HolomorphicMaps ChartPartition NormalDirectionVanishing ClosedProductCurrents
  DiagonalTangentialReduction GraphTangentialAlgebra SkodaElMirHolomorphic
open scoped ProductComplexManifold

/-! ### Linear algebra in the product model -/

section Model

variable {n : ℕ}

/-- `(u, u') ↦ u' - L u`, whose kernel is the graph of `L`. -/
def graphDiff (L : ComplexModel n →L[ℂ] ComplexModel n) :
    ComplexModel (n + n) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel n) -
    L.comp (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel n))).comp
      (prodModelEquiv n n).symm.toContinuousLinearMap

theorem graphDiff_apply (L : ComplexModel n →L[ℂ] ComplexModel n) (u u' : ComplexModel n) :
    graphDiff L (prodModelEquiv n n (u, u')) = u' - L u := by
  simp [graphDiff]

/-- `π_L (u, u') = (u, L u)`: the projection onto the graph of `L` along the second factor. -/
def graphProj (L : ComplexModel n →L[ℂ] ComplexModel n) :
    ComplexModel (n + n) →L[ℂ] ComplexModel (n + n) :=
  (prodModelEquiv n n).toContinuousLinearMap.comp
    (((ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel n)).prod
      (L.comp (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel n)))).comp
      (prodModelEquiv n n).symm.toContinuousLinearMap)

theorem graphProj_apply (L : ComplexModel n →L[ℂ] ComplexModel n) (u u' : ComplexModel n) :
    graphProj L (prodModelEquiv n n (u, u')) = prodModelEquiv n n (u, L u) := by
  simp [graphProj]

/-- The `ℂ`-linear normal coordinates `yⱼ`, `-i yⱼ` of the graph of `L`, `y = u' - L u`. -/
def graphNormalCoord (L : ComplexModel n →L[ℂ] ComplexModel n) (a : Fin 2 × Fin n) :
    ComplexModel (n + n) →L[ℂ] ℂ :=
  (![1, -Complex.I] a.1 : ℂ) •
    ((EuclideanSpace.proj a.2 : ComplexModel n →L[ℂ] ℂ).comp (graphDiff L))

/-- Their real parts. -/
def graphNormalRe (L : ComplexModel n →L[ℂ] ComplexModel n) (a : Fin 2 × Fin n) :
    ComplexModel (n + n) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((graphNormalCoord L a).restrictScalars ℝ)

theorem graphNormalRe_apply (L : ComplexModel n →L[ℂ] ComplexModel n) (a : Fin 2 × Fin n)
    (ξ : ComplexModel (n + n)) : graphNormalRe L a ξ = (graphNormalCoord L a ξ).re := rfl

/-- **`ξ - π_L ξ = ∑ₐ Re Lₐ(ξ) Nₐ`**, with the normal vectors `Nₐ` of the diagonal case. -/
theorem sub_graphProj_eq (L : ComplexModel n →L[ℂ] ComplexModel n) (ξ : ComplexModel (n + n)) :
    ξ - graphProj L ξ = ∑ a, graphNormalRe L a ξ • normalVec a := by
  obtain ⟨⟨u, u'⟩, rfl⟩ := (prodModelEquiv n n).surjective ξ
  rw [graphProj_apply, ← map_sub, Prod.mk_sub_mk, sub_self]
  have hterm : ∀ a : Fin 2 × Fin n, graphNormalRe L a (prodModelEquiv n n (u, u')) • normalVec a =
      prodModelEquiv n n (0, (((![1, -Complex.I] a.1 * (u' - L u) a.2).re : ℝ) : ℂ) •
        ((![1, Complex.I] a.1 : ℂ) • EuclideanSpace.single a.2 (1 : ℂ))) := by
    intro a
    rw [← Complex.coe_smul, normalVec, ← map_smul, Prod.smul_mk, smul_zero, graphNormalRe_apply,
      graphNormalCoord, smul_apply, ContinuousLinearMap.comp_apply,
      graphDiff_apply, smul_eq_mul]
    rfl
  simp_rw [hterm, ← map_sum]
  congr 1
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    simp
  · rw [Prod.snd_sum, Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
    dsimp only
    have hy : u' - L u = ∑ j, ((u' - L u) j • EuclideanSpace.single j (1 : ℂ)) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (u' - L u)]
      simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
    conv_lhs => rw [hy]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, one_smul]
    rw [smul_smul, ← add_smul]
    congr 1
    have hre : (-Complex.I * (u' - L u) j).re = ((u' - L u) j).im := by
      simp [Complex.mul_re]
    rw [hre, Complex.re_add_im]

/-- The base coordinate `ζ = (z, w) ↦ z`. -/
def baseCoord (ζ : ComplexModel (n + n)) : ComplexModel n := ((prodModelEquiv n n).symm ζ).1

/-- The base coordinate as a `ℂ`-linear map. -/
def baseCoordCLM : ComplexModel (n + n) →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel n)).comp
    (prodModelEquiv n n).symm.toContinuousLinearMap

theorem baseCoordCLM_apply (ζ : ComplexModel (n + n)) : baseCoordCLM ζ = baseCoord ζ := rfl

theorem continuous_baseCoord : Continuous (baseCoord (n := n)) :=
  (baseCoordCLM (n := n)).continuous

@[simp] theorem baseCoord_apply (u u' : ComplexModel n) :
    baseCoord (prodModelEquiv n n (u, u')) = u := by
  simp [baseCoord]

/-- `ζ = (z, w) ↦ (z, F z)`: the graph retraction in the model. -/
def graphModel (F : ComplexModel n → ComplexModel n) (ζ : ComplexModel (n + n)) :
    ComplexModel (n + n) :=
  prodModelEquiv n n (baseCoord ζ, F (baseCoord ζ))

/-- The holomorphic normal coordinates `Lₐ(z, w) = (1, -i)_{a.1} (w - F z)_{a.2}` of the graph. -/
def graphNormalFun (F : ComplexModel n → ComplexModel n) (a : Fin 2 × Fin n)
    (ζ : ComplexModel (n + n)) : ℂ :=
  (![1, -Complex.I] a.1 : ℂ) * (((prodModelEquiv n n).symm ζ).2 - F (baseCoord ζ)) a.2

/-- **`ℂ`-derivative of the graph retraction**: `D(z ↦ (z, F z)) = graphProj (DF)`. -/
theorem hasFDerivAt_graphModel {F : ComplexModel n → ComplexModel n} {ζ : ComplexModel (n + n)}
    (hF : DifferentiableAt ℂ F (baseCoord ζ)) :
    HasFDerivAt (graphModel F) (graphProj (fderiv ℂ F (baseCoord ζ))) ζ := by
  have hb : HasFDerivAt (baseCoord (n := n)) (baseCoordCLM (n := n)) ζ :=
    (baseCoordCLM (n := n)).hasFDerivAt
  have hpair : HasFDerivAt (fun ζ => (baseCoord ζ, F (baseCoord ζ)))
      ((baseCoordCLM (n := n)).prod ((fderiv ℂ F (baseCoord ζ)).comp baseCoordCLM)) ζ :=
    hb.prodMk (hF.hasFDerivAt.comp ζ hb)
  have h := (prodModelEquiv n n).toContinuousLinearMap.hasFDerivAt.comp ζ hpair
  refine h.congr_fderiv ?_
  ext ξ
  simp [graphProj, baseCoordCLM]

/-- **`ℂ`-derivative of the normal coordinates**: `dLₐ = graphNormalCoord (DF) a`. -/
theorem hasFDerivAt_graphNormalFun {F : ComplexModel n → ComplexModel n} {ζ : ComplexModel (n + n)}
    (hF : DifferentiableAt ℂ F (baseCoord ζ)) (a : Fin 2 × Fin n) :
    HasFDerivAt (graphNormalFun F a) (graphNormalCoord (fderiv ℂ F (baseCoord ζ)) a) ζ := by
  have hb : HasFDerivAt (baseCoord (n := n)) (baseCoordCLM (n := n)) ζ :=
    (baseCoordCLM (n := n)).hasFDerivAt
  have hsnd : HasFDerivAt (fun ζ : ComplexModel (n + n) => ((prodModelEquiv n n).symm ζ).2)
      ((ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel n)).comp
        (prodModelEquiv n n).symm.toContinuousLinearMap) ζ :=
    ((ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel n)).comp
      (prodModelEquiv n n).symm.toContinuousLinearMap).hasFDerivAt
  have hdiff := hsnd.sub (hF.hasFDerivAt.comp ζ hb)
  have hproj := ((EuclideanSpace.proj a.2 : ComplexModel n →L[ℂ] ℂ)).hasFDerivAt.comp ζ hdiff
  have h := hproj.const_mul (![1, -Complex.I] a.1 : ℂ)
  refine h.congr_fderiv ?_
  ext ξ
  simp [graphNormalCoord, graphDiff, baseCoordCLM]

/-- The real part of `Lₐ` has derivative `graphNormalRe (DF) a`. -/
theorem hasFDerivAt_re_graphNormalFun {F : ComplexModel n → ComplexModel n}
    {ζ : ComplexModel (n + n)} (hF : DifferentiableAt ℂ F (baseCoord ζ)) (a : Fin 2 × Fin n) :
    HasFDerivAt (fun ζ => (graphNormalFun F a ζ).re)
      (graphNormalRe (fderiv ℂ F (baseCoord ζ)) a) ζ :=
  Complex.reCLM.hasFDerivAt.comp ζ ((hasFDerivAt_graphNormalFun hF a).restrictScalars ℝ)

/-- On the graph of `F` (i.e. where `graphModel F ζ = ζ`), the normal coordinates vanish. -/
theorem graphNormalFun_eq_zero_of_graphModel_eq {F : ComplexModel n → ComplexModel n}
    {ζ : ComplexModel (n + n)} (h : graphModel F ζ = ζ) (a : Fin 2 × Fin n) :
    graphNormalFun F a ζ = 0 := by
  have h2 : ((prodModelEquiv n n).symm ζ).2 = F (baseCoord ζ) := by
    have := congrArg (fun x => ((prodModelEquiv n n).symm x).2) h
    simpa [graphModel] using this.symm
  simp [graphNormalFun, h2]

end Model

/-! ### Chart-level tools for nonlinear functions -/

section Tools

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- A function smooth on an open subset `O` of a chart target, multiplied by a smooth cut-off with
compact support in `O`, extends to a chart-smooth function. -/
theorem chartSmooth_chartExtend_mul_of_isOpen (E : ComplexChart N M) {O : Set (ComplexModel N)}
    (hO : IsOpen O) (hOt : O ⊆ E.val.target) {ψ : ComplexModel N → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψO : tsupport ψ ⊆ O) {g : ComplexModel N → ℝ}
    (hg : ContDiffOn ℝ ∞ g O) :
    ChartSmooth (n := N) (chartExtend E fun z => ψ z * g z) :=
  chartSmooth_chartExtend E
    (SmoothCurrentClosedness.contDiff_mul_of_tsupport_subset hO hψ hψO hg)
    (hψc.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left)
    (tsupport_mul_subset_left.trans (hψO.trans hOt))

/-- **`d(χg ∧ dχk) = dg ∧ dk`** at a point where the cut-off `χ` is `1` nearby, for arbitrary
(nonlinear) `g`, `k` differentiable there. -/
theorem exactPair_cutoff_coeff_of_hasFDerivAt (E : ComplexChart N M) {χ g k : ComplexModel N → ℝ}
    (hg : ChartSmooth (n := N) (chartExtend E fun z => χ z * g z))
    (hk : ChartSmooth (n := N) (chartExtend E fun z => χ z * k z)) {w : ComplexModel N}
    (hw : w ∈ E.val.target) (hχ : (fun z => χ z) =ᶠ[𝓝 w] fun _ => 1)
    {ℓ m : ComplexModel N →L[ℝ] ℝ} (hgd : HasFDerivAt g ℓ w) (hkd : HasFDerivAt k m w) :
    (exactPair _ _ hg hk).coeff E w = pairForm ℓ m := by
  have h1 : ∀ G : ComplexModel N → ℝ,
      (fun y => chartExtend E (fun z => χ z * G z) (E.val.symm y)) =ᶠ[𝓝 w] G := by
    intro G
    filter_upwards [SlotTestForms.chartExtend_eventuallyEq hw, hχ] with y hy1 hy2
    rw [hy1, hy2, one_mul]
  ext v
  rw [eq_vec_two v, exactPair_coeff_apply _ _ hg hk E hw, (h1 g).fderiv_eq, (h1 k).fderiv_eq,
    hgd.fderiv, hkd.fderiv, pairForm_apply]

/-- **Real and imaginary parts of a holomorphic function form a holomorphic pair**: if `L` is
`ℂ`-differentiable on an open `O`, `χ = 1` on `O` and `ρ = 0` off `O`, then the chart extensions of
`χ Re L`, `χ Im L` form a holomorphic pair where `ρ ≠ 0`. -/
theorem isHoloPairOn_re_im (E : ComplexChart N M) {L : ComplexModel N → ℂ}
    {O : Set (ComplexModel N)} (hO : IsOpen O) (hL : ∀ z ∈ O, DifferentiableAt ℂ L z)
    {χ ρ : ComplexModel N → ℝ} (hχO : ∀ z ∈ O, χ z = 1) (hρO : Function.support ρ ⊆ O) :
    IsHoloPairOn (N := N) (chartExtend E fun z => χ z * (L z).re)
      (chartExtend E fun z => χ z * (L z).im) (chartExtend E ρ) := by
  intro f z hz hρz v
  have hxs : f.val.symm z ∈ E.val.source := by
    by_contra h
    exact hρz (chartExtend_of_notMem h)
  have hEx : E.val (f.val.symm z) ∈ O := by
    rw [chartExtend_of_mem hxs] at hρz
    exact hρO hρz
  have hzd : z ∈ coordinateDomain id f E := ⟨hz, hxs⟩
  set Ψ := coordinateMap id f E with hΨ
  have hΨc : ContDiffAt ℝ ∞ Ψ z := coordinateMap_contDiffAt_real contMDiff_id f E hzd
  have hΨz : Ψ z = E.val (f.val.symm z) := rfl
  have hev : ∀ᶠ y in 𝓝 z, y ∈ coordinateDomain id f E ∧ Ψ y ∈ O := by
    have h1 : ∀ᶠ y in 𝓝 z, y ∈ coordinateDomain id f E :=
      (coordinateDomain_isOpen contMDiff_id f E).mem_nhds hzd
    exact h1.and (hΨc.continuousAt.preimage_mem_nhds (hO.mem_nhds hEx))
  have hg : (fun y => chartExtend E (fun z => χ z * (L z).re) (f.val.symm y)) =ᶠ[𝓝 z]
      fun y => (L (Ψ y)).re := by
    filter_upwards [hev] with y hy
    rw [chartExtend_of_mem (show f.val.symm y ∈ E.val.source from hy.1.2)]
    change χ (Ψ y) * (L (Ψ y)).re = _
    rw [hχO _ hy.2, one_mul]
  have hF : (fun y => chartExtend E (fun z => χ z * (L z).im) (f.val.symm y)) =ᶠ[𝓝 z]
      fun y => (L (Ψ y)).im := by
    filter_upwards [hev] with y hy
    rw [chartExtend_of_mem (show f.val.symm y ∈ E.val.source from hy.1.2)]
    change χ (Ψ y) * (L (Ψ y)).im = _
    rw [hχO _ hy.2, one_mul]
  have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ z) z := (hΨc.differentiableAt (by simp)).hasFDerivAt
  have hLd : HasFDerivAt L ((fderiv ℂ L (Ψ z)).restrictScalars ℝ) (Ψ z) :=
    (hL _ (hΨz ▸ hEx)).hasFDerivAt.restrictScalars ℝ
  have hRe : fderiv ℝ (fun y => (L (Ψ y)).re) z =
      Complex.reCLM.comp (((fderiv ℂ L (Ψ z)).restrictScalars ℝ).comp (fderiv ℝ Ψ z)) :=
    (Complex.reCLM.hasFDerivAt.comp z (hLd.comp z hΨd)).fderiv
  have hIm : fderiv ℝ (fun y => (L (Ψ y)).im) z =
      Complex.imCLM.comp (((fderiv ℂ L (Ψ z)).restrictScalars ℝ).comp (fderiv ℝ Ψ z)) :=
    (Complex.imCLM.hasFDerivAt.comp z (hLd.comp z hΨd)).fderiv
  rw [hg.fderiv_eq, hF.fderiv_eq, hRe, hIm]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [coordinateMap_fderiv_map_smul_complex contMDiff_id f E hzd Complex.I v, map_smul]
  simp only [Complex.imCLM_apply, Complex.reCLM_apply, smul_eq_mul, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  rfl

end Tools

/-! ### The graph chart on `V × X` -/

section Chart

variable {n : ℕ} {V X : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel n) V]
  [IsComplexManifold n V] [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {f : V → X}

variable (f) in
/-- `Φ(v, x) = (v, f v)`, i.e. `(id, f) ∘ p₁`: the retraction of `V × X` onto the graph of `f`. -/
def graphProjMap : V × X → V × X := fun p => (p.1, f p.1)

theorem contMDiff_graphProjMap (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) :
    ContMDiff 𝓘(ℂ, ComplexModel (n + n)) 𝓘(ℂ, ComplexModel (n + n)) ∞ (graphProjMap f) :=
  contMDiff_prodMk contMDiff_fst (hf.comp contMDiff_fst)

omit [TopologicalSpace V] [ChartedSpace (ComplexModel n) V] [IsComplexManifold n V]
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] in
theorem graphProjMap_eq_self {p : V × X} (hp : f p.1 = p.2) : graphProjMap f p = p := by
  obtain ⟨v, x⟩ := p
  simp only [graphProjMap, Prod.mk.injEq, true_and]
  exact hp

variable (n f) in
/-- The product chart at the graph point `(v₀, f v₀)`. -/
abbrev graphChart (v₀ : V) : ComplexChart (n + n) (V × X) :=
  complexChartAt (n := n + n) ((v₀, f v₀) : V × X)

variable (n f) in
/-- The coordinate representative `F = b ∘ f ∘ a⁻¹` of `f` in the charts at `v₀` and `f v₀`. -/
abbrev graphRep (v₀ : V) : ComplexModel n → ComplexModel n :=
  coordinateMap f (complexChartAt (n := n) v₀) (complexChartAt (n := n) (f v₀))

variable (n f) in
/-- The open set of the graph chart where the representative of `f` is defined. -/
def graphDomain (v₀ : V) : Set (ComplexModel (n + n)) :=
  (graphChart n f v₀).val.target ∩
    baseCoord ⁻¹' coordinateDomain f (complexChartAt (n := n) v₀) (complexChartAt (n := n) (f v₀))

omit [IsComplexManifold n V] [IsComplexManifold n X] in
theorem graphChart_val (v₀ : V) :
    (graphChart n f v₀).val =
      prodChart (chartAt (ComplexModel n) v₀) (chartAt (ComplexModel n) (f v₀)) :=
  rfl

omit [IsComplexManifold n V] [IsComplexManifold n X] in
theorem isOpen_graphDomain (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (v₀ : V) : IsOpen (graphDomain n f v₀) :=
  (graphChart n f v₀).val.open_target.inter
    ((coordinateDomain_isOpen hf _ _).preimage continuous_baseCoord)

omit [IsComplexManifold n V] [IsComplexManifold n X] in
theorem graphDomain_subset_target (v₀ : V) :
    graphDomain n f v₀ ⊆ (graphChart n f v₀).val.target :=
  inter_subset_left

omit [IsComplexManifold n V] [IsComplexManifold n X] in
/-- **`Φ` in the graph chart**: on `graphDomain`, `Φ` stays in the chart and reads
`ζ ↦ (z, F z)`. -/
theorem graphChart_mapsTo {v₀ : V} {p : V × X} (hp : p ∈ (graphChart n f v₀).val.source)
    (hW : (graphChart n f v₀).val p ∈ graphDomain n f v₀) :
    graphProjMap f p ∈ (graphChart n f v₀).val.source ∧
      (graphChart n f v₀).val (graphProjMap f p) =
        graphModel (graphRep n f v₀) ((graphChart n f v₀).val p) := by
  obtain ⟨p₁, p₂⟩ := p
  rw [graphChart_val, prodChart_source] at hp
  have hW2 := hW.2
  simp only [graphChart_val, prodChart_apply, mem_preimage, baseCoord_apply] at hW2
  have hfp : f p₁ ∈ (chartAt (ComplexModel n) (f v₀)).source := by
    have h := hW2.2
    simp only [mem_preimage] at h
    rwa [show (complexChartAt (n := n) v₀).val = chartAt (ComplexModel n) v₀ from rfl,
      (chartAt (ComplexModel n) v₀).left_inv hp.1] at h
  refine ⟨?_, ?_⟩
  · rw [graphChart_val, prodChart_source]
    exact ⟨hp.1, hfp⟩
  · simp only [graphChart_val, prodChart_apply, graphProjMap, graphModel, baseCoord_apply,
      graphRep, coordinateMap, Function.comp_apply]
    congr 2
    rw [show (complexChartAt (n := n) v₀).val = chartAt (ComplexModel n) v₀ from rfl,
      (chartAt (ComplexModel n) v₀).left_inv hp.1]
    rfl

omit [IsComplexManifold n V] [IsComplexManifold n X] in
theorem graphModel_mem_target {v₀ : V} {ζ : ComplexModel (n + n)}
    (hζ : ζ ∈ graphDomain n f v₀) : graphModel (graphRep n f v₀) ζ ∈ (graphChart n f v₀).val.target := by
  have hs := (graphChart n f v₀).val.map_target hζ.1
  have hW : (graphChart n f v₀).val ((graphChart n f v₀).val.symm ζ) ∈ graphDomain n f v₀ := by
    rwa [(graphChart n f v₀).val.right_inv hζ.1]
  have h := graphChart_mapsTo hs hW
  rw [(graphChart n f v₀).val.right_inv hζ.1] at h
  rw [← h.2]
  exact (graphChart n f v₀).val.map_source h.1

omit [IsComplexManifold n V] [IsComplexManifold n X] in
theorem coordinateMap_graphProjMap {v₀ : V} {ζ : ComplexModel (n + n)}
    (hζ : ζ ∈ graphDomain n f v₀) :
    coordinateMap (graphProjMap f) (graphChart n f v₀) (graphChart n f v₀) ζ =
      graphModel (graphRep n f v₀) ζ := by
  have hs := (graphChart n f v₀).val.map_target hζ.1
  have hW : (graphChart n f v₀).val ((graphChart n f v₀).val.symm ζ) ∈ graphDomain n f v₀ := by
    rwa [(graphChart n f v₀).val.right_inv hζ.1]
  change (graphChart n f v₀).val (graphProjMap f ((graphChart n f v₀).val.symm ζ)) = _
  rw [(graphChart_mapsTo hs hW).2, (graphChart n f v₀).val.right_inv hζ.1]

theorem differentiableAt_graphRep (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {v₀ : V} {ζ : ComplexModel (n + n)} (hζ : ζ ∈ graphDomain n f v₀) :
    DifferentiableAt ℂ (graphRep n f v₀) (baseCoord ζ) :=
  (coordinateMap_contDiffAt hf _ _ hζ.2).differentiableAt (by simp)

/-- **`Φ^*b` in the graph chart**: `(Φ^*b)(ζ) = π_ζ^*(b(Φ_E ζ))` with `π_ζ = graphProj (DF(z))`. -/
theorem pullback_graphProjMap_coeff
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (b : SmoothRealForm (n + n) (V × X) 2) {v₀ : V} {ζ : ComplexModel (n + n)}
    (hζ : ζ ∈ graphDomain n f v₀) :
    (SmoothRealForm.pullback (contMDiff_graphProjMap hf) b).coeff (graphChart n f v₀) ζ =
      (b.coeff (graphChart n f v₀) (graphModel (graphRep n f v₀) ζ)).compContinuousLinearMap
        ((graphProj (fderiv ℂ (graphRep n f v₀) (baseCoord ζ))).restrictScalars ℝ) := by
  have hs := (graphChart n f v₀).val.map_target hζ.1
  have hW : (graphChart n f v₀).val ((graphChart n f v₀).val.symm ζ) ∈ graphDomain n f v₀ := by
    rwa [(graphChart n f v₀).val.right_inv hζ.1]
  have hdom : ζ ∈ coordinateDomain (graphProjMap f) (graphChart n f v₀) (graphChart n f v₀) :=
    ⟨hζ.1, (graphChart_mapsTo hs hW).1⟩
  rw [SmoothRealForm.pullback_coeff _ b _ _ hdom, coordinateMap_graphProjMap hζ]
  have heq : coordinateMap (graphProjMap f) (graphChart n f v₀) (graphChart n f v₀) =ᶠ[𝓝 ζ]
      graphModel (graphRep n f v₀) := by
    filter_upwards [(isOpen_graphDomain hf v₀).mem_nhds hζ] with y hy
    exact coordinateMap_graphProjMap hy
  rw [heq.fderiv_eq,
    ((hasFDerivAt_graphModel (differentiableAt_graphRep hf hζ)).restrictScalars ℝ).fderiv]

omit [IsComplexManifold n V] [IsComplexManifold n X] in
/-- **On the graph**, `Φ_E` fixes the chart point. -/
theorem graphModel_eq_of_mem_graph {v₀ : V} {p : V × X} (hΓ : f p.1 = p.2)
    (hp : p ∈ (graphChart n f v₀).val.source)
    (hW : (graphChart n f v₀).val p ∈ graphDomain n f v₀) :
    graphModel (graphRep n f v₀) ((graphChart n f v₀).val p) = (graphChart n f v₀).val p := by
  rw [← (graphChart_mapsTo hp hW).2, graphProjMap_eq_self hΓ]

theorem differentiableAt_graphNormalFun
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {v₀ : V} {ζ : ComplexModel (n + n)} (hζ : ζ ∈ graphDomain n f v₀) (a : Fin 2 × Fin n) :
    DifferentiableAt ℂ (graphNormalFun (graphRep n f v₀) a) ζ :=
  (hasFDerivAt_graphNormalFun (differentiableAt_graphRep hf hζ) a).differentiableAt

end Chart

end SGPT.Foundations.Analysis.Pending.GraphTangentialChart
