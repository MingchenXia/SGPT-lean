import SGPT.Foundations.Analysis.Pending.GraphTangentialChart

set_option autoImplicit false

/-!
# The tangential reduction on the graph of a holomorphic map

Let `f : V → X` be a holomorphic map between compact complex manifolds of the same dimension `n`,
`Γ_f = {(v, x) | f v = x}` its graph and `Φ(v, x) = (v, f v)` the holomorphic retraction onto
`Γ_f` (`GraphTangentialChart.graphProjMap`).  For a closed positive current `Θ` on `V × X` carried
by `Γ_f`,

`Θ (Φ^* φ) = Θ (φ)` for every test form `φ` (`apply_pullback_graphProjMap_eq`),

i.e. `Θ = (id, f)_* p₁_* Θ` (`demailly-cadg:III.2.10` for the graph; the diagonal case `f = id`
is `DiagonalTangentialReduction.apply_pullback_diagProjMap_eq`).

*Proof.*  As in the diagonal case, with the point-dependent projection `π_ζ = graphProj (DF(z))`
of `GraphTangentialChart` in place of the constant `diagProj`: by
`GraphTangentialAlgebra.sub_comp_eq` and `GraphTangentialChart.sub_graphProj_eq`,
`b - Φ^*b = ∑ γ Π₁₁ d(Re Lₐ ∧ ds_c) + ∑ η Π₁₁ (ds_c ∧ ds_d)` near a graph point, where
`Lₐ = (1, -i)_{a.1} (w - F z)_{a.2}` are HOLOMORPHIC normal coordinates (so the first terms are
killed by `NormalDirectionVanishing.apply_wedge_normalPair_eq_zero`, through
`GraphTangentialChart.isHoloPairOn_re_im`), and `η` vanishes on `Γ_f` (killed by
`CarriedCurrentTests.apply_smulTest_eq_zero`).  The local statement is
`exists_nhds_apply_wedge_sub_pullback_eq_zero`; the slots are then pulled back one at a time and the
function `h` is replaced by `h ∘ Φ`, which agrees with `h` on `Γ_f`.

Steps G4 and G5 of the graph support plan,
for TN-CLASSICAL's graph route of the `(P)` step of Boucksom 4.8 (earlier discussion the statement under discussion).
-/

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.GraphTangentialReduction

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents ClosedProductCurrents CurrentTraceMeasure
  CurrentRestriction SlotTestForms CarriedCurrentTests TopDegreeDensity NormalDirectionVanishing
  DiagonalTangentialReduction GraphTangentialAlgebra GraphTangentialChart

/-! ### Smoothness of the coefficients -/

section Smooth

variable {N : ℕ} {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- A two-form in the standard real frame: `A(u, v) = ∑_{c,d} s_c(u) s_d(v) A(E_c, E_d)`. -/
theorem twoForm_apply_eq_sum (A : RealForm N 2) (u v : ComplexModel N) :
    A ![u, v] = ∑ c, ∑ d, coordFun c u * coordFun d v * A ![topBasis N c, topBasis N d] := by
  rw [← twoFormBilin_apply]
  conv_lhs => rw [← sum_coordFun_smul u, ← sum_coordFun_smul v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    twoFormBilin_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- **Smooth evaluation of a smooth two-form on smooth vector fields.** -/
theorem contDiffOn_twoForm_apply {s : Set D} {A : D → RealForm N 2} {u v : D → ComplexModel N}
    (hA : ContDiffOn ℝ ∞ A s) (hu : ContDiffOn ℝ ∞ u s) (hv : ContDiffOn ℝ ∞ v s) :
    ContDiffOn ℝ ∞ (fun x => A x ![u x, v x]) s := by
  have heq : (fun x => A x ![u x, v x]) = fun x => ∑ c, ∑ d,
      coordFun c (u x) * coordFun d (v x) * A x ![topBasis N c, topBasis N d] :=
    funext fun x => twoForm_apply_eq_sum (A x) (u x) (v x)
  rw [heq]
  refine ContDiffOn.sum fun c _ => ContDiffOn.sum fun d _ => ?_
  refine (((coordFun c).contDiff.comp_contDiffOn hu).mul
    ((coordFun d).contDiff.comp_contDiffOn hv)).mul ?_
  exact (ContinuousAlternatingMap.apply ℝ (ComplexModel N) ℝ
    ![topBasis N c, topBasis N d]).contDiff.comp_contDiffOn hA

end Smooth

/-! ### Smoothness in the graph chart -/

section ChartSmooth

open ProductComplexManifold HolomorphicMaps
open scoped ProductComplexManifold

variable {n : ℕ} {V X : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel n) V]
  [IsComplexManifold n V] [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {f : V → X}
  (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)

omit [IsComplexManifold n V] [IsComplexManifold n X] in
theorem mem_graphDomain_self (v₀ : V) :
    (graphChart n f v₀).val (v₀, f v₀) ∈ graphDomain n f v₀ := by
  refine ⟨(graphChart n f v₀).val.map_source (mem_complexChartAt_source _), ?_⟩
  change baseCoord ((graphChart n f v₀).val (v₀, f v₀)) ∈ coordinateDomain f
    (complexChartAt (n := n) v₀) (complexChartAt (n := n) (f v₀))
  rw [graphChart_val, prodChart_apply, baseCoord_apply]
  exact mem_coordinateDomain (mem_complexChartAt_source v₀)
    (mem_complexChartAt_source (n := n) (f v₀))

omit [IsComplexManifold n V] [IsComplexManifold n X] in
theorem baseCoord_mem_coordinateDomain {v₀ : V} {ζ : ComplexModel (n + n)}
    (hζ : ζ ∈ graphDomain n f v₀) :
    baseCoord ζ ∈ coordinateDomain f (complexChartAt (n := n) v₀)
      (complexChartAt (n := n) (f v₀)) :=
  hζ.2

include hf in
theorem contDiffOn_fderiv_graphRep_apply (v₀ : V) (u : ComplexModel n) :
    ContDiffOn ℝ ∞ (fun ζ => fderiv ℂ (graphRep n f v₀) (baseCoord ζ) u) (graphDomain n f v₀) := by
  have hD := coordinateDomain_isOpen hf (complexChartAt (n := n) v₀) (complexChartAt (n := n) (f v₀))
  have h1 : ContDiffOn ℂ ∞ (fun y => fderiv ℂ (graphRep n f v₀) y)
      (coordinateDomain f (complexChartAt (n := n) v₀) (complexChartAt (n := n) (f v₀))) :=
    (coordinateMap_contDiffOn hf _ _).fderiv_of_isOpen hD (by simp)
  have h2 : ContDiffOn ℂ ∞ (fun y => fderiv ℂ (graphRep n f v₀) y u)
      (coordinateDomain f (complexChartAt (n := n) v₀) (complexChartAt (n := n) (f v₀))) :=
    h1.clm_apply contDiffOn_const
  have h3 : ContDiffOn ℂ ∞ (fun ζ => fderiv ℂ (graphRep n f v₀) (baseCoord ζ) u)
      (graphDomain n f v₀) :=
    h2.comp (baseCoordCLM (n := n)).contDiff.contDiffOn fun ζ hζ => hζ.2
  exact h3.restrict_scalars ℝ

theorem graphProj_apply' (L : ComplexModel n →L[ℂ] ComplexModel n) (ξ : ComplexModel (n + n)) :
    graphProj L ξ = prodModelEquiv n n (baseCoord ξ, L (baseCoord ξ)) := by
  obtain ⟨⟨u, u'⟩, rfl⟩ := (prodModelEquiv n n).surjective ξ
  rw [graphProj_apply, baseCoord_apply]

include hf in
/-- `ζ ↦ π_ζ ξ` is smooth on the graph domain, for a fixed vector `ξ`. -/
theorem contDiffOn_graphProj_apply (v₀ : V) (ξ : ComplexModel (n + n)) :
    ContDiffOn ℝ ∞ (fun ζ => graphProj (fderiv ℂ (graphRep n f v₀) (baseCoord ζ)) ξ)
      (graphDomain n f v₀) := by
  simp_rw [graphProj_apply']
  have hP : ContDiff ℝ ∞ (fun p : ComplexModel n × ComplexModel n => prodModelEquiv n n p) :=
    ((prodModelEquiv n n).toContinuousLinearMap.restrictScalars ℝ).contDiff
  exact hP.comp_contDiffOn (contDiffOn_const.prodMk
    (contDiffOn_fderiv_graphRep_apply hf v₀ (baseCoord ξ)))

include hf in
theorem contDiffOn_graphModel (v₀ : V) :
    ContDiffOn ℝ ∞ (graphModel (graphRep n f v₀)) (graphDomain n f v₀) := by
  have hF : ContDiffOn ℝ ∞ (graphRep n f v₀)
      (coordinateDomain f (complexChartAt (n := n) v₀) (complexChartAt (n := n) (f v₀))) :=
    coordinateMap_contDiffOn_real hf _ _
  have hb : ContDiff ℝ ∞ (baseCoord (n := n)) :=
    ((baseCoordCLM (n := n)).restrictScalars ℝ).contDiff
  have hP : ContDiff ℝ ∞ (fun p : ComplexModel n × ComplexModel n => prodModelEquiv n n p) :=
    ((prodModelEquiv n n).toContinuousLinearMap.restrictScalars ℝ).contDiff
  exact hP.comp_contDiffOn (hb.contDiffOn.prodMk (hF.comp hb.contDiffOn fun ζ hζ => hζ.2))

include hf in
theorem contDiffOn_re_graphNormalFun (v₀ : V) (a : Fin 2 × Fin n) :
    ContDiffOn ℝ ∞ (fun ζ => (graphNormalFun (graphRep n f v₀) a ζ).re) (graphDomain n f v₀) := by
  have hF : ContDiffOn ℂ ∞ (graphRep n f v₀)
      (coordinateDomain f (complexChartAt (n := n) v₀) (complexChartAt (n := n) (f v₀))) :=
    coordinateMap_contDiffOn hf _ _
  have hb : ContDiff ℂ ∞ (baseCoord (n := n)) := (baseCoordCLM (n := n)).contDiff
  have hs : ContDiff ℂ ∞ (fun ζ : ComplexModel (n + n) => ((prodModelEquiv n n).symm ζ).2) :=
    ((ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel n)).comp
      (prodModelEquiv n n).symm.toContinuousLinearMap).contDiff
  have hL : ContDiffOn ℂ ∞ (graphNormalFun (graphRep n f v₀) a) (graphDomain n f v₀) := by
    have hdiff : ContDiffOn ℂ ∞ (fun ζ => ((prodModelEquiv n n).symm ζ).2 -
        graphRep n f v₀ (baseCoord ζ)) (graphDomain n f v₀) :=
      hs.contDiffOn.sub (hF.comp hb.contDiffOn fun ζ hζ => hζ.2)
    exact contDiffOn_const.mul
      ((EuclideanSpace.proj a.2 : ComplexModel n →L[ℂ] ℂ).contDiff.comp_contDiffOn hdiff)
  exact Complex.reCLM.contDiff.comp_contDiffOn (hL.restrict_scalars ℝ)

include hf in
theorem contDiffOn_im_graphNormalFun (v₀ : V) (a : Fin 2 × Fin n) :
    ContDiffOn ℝ ∞ (fun ζ => (graphNormalFun (graphRep n f v₀) a ζ).im) (graphDomain n f v₀) := by
  have hF : ContDiffOn ℂ ∞ (graphRep n f v₀)
      (coordinateDomain f (complexChartAt (n := n) v₀) (complexChartAt (n := n) (f v₀))) :=
    coordinateMap_contDiffOn hf _ _
  have hb : ContDiff ℂ ∞ (baseCoord (n := n)) := (baseCoordCLM (n := n)).contDiff
  have hs : ContDiff ℂ ∞ (fun ζ : ComplexModel (n + n) => ((prodModelEquiv n n).symm ζ).2) :=
    ((ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel n)).comp
      (prodModelEquiv n n).symm.toContinuousLinearMap).contDiff
  have hL : ContDiffOn ℂ ∞ (graphNormalFun (graphRep n f v₀) a) (graphDomain n f v₀) := by
    have hdiff : ContDiffOn ℂ ∞ (fun ζ => ((prodModelEquiv n n).symm ζ).2 -
        graphRep n f v₀ (baseCoord ζ)) (graphDomain n f v₀) :=
      hs.contDiffOn.sub (hF.comp hb.contDiffOn fun ζ hζ => hζ.2)
    exact contDiffOn_const.mul
      ((EuclideanSpace.proj a.2 : ComplexModel n →L[ℂ] ℂ).contDiff.comp_contDiffOn hdiff)
  exact Complex.imCLM.contDiff.comp_contDiffOn (hL.restrict_scalars ℝ)

end ChartSmooth

/-! ### The chart-local vanishing -/

section Core

open ProductComplexManifold SkodaElMirSubmanifold HolomorphicMaps ChartPartition
open scoped ProductComplexManifold

variable {n : ℕ} {V X : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel n) V]
  [IsComplexManifold n V] [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {f : V → X}
  (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)

theorem isTypeOneOne_sub_pullback_graph {b : SmoothRealForm (n + n) (V × X) 2}
    (hb : b.IsTypeOneOne) :
    (b - SmoothRealForm.pullback (contMDiff_graphProjMap hf) b).IsTypeOneOne :=
  isTypeOneOne_sub hb (isTypeOneOne_pullback (contMDiff_graphProjMap hf) hb)

omit [IsComplexManifold n V] in
include hf in
theorem isClosed_graph : IsClosed {p : V × X | f p.1 = p.2} :=
  isClosed_eq (hf.continuous.comp continuous_fst) continuous_snd

variable [CompactSpace V] [CompactSpace X] [MeasurableSpace (V × X)] [BorelSpace (V × X)]
  (w : KahlerBackground (n + n) (V × X)) {q : ℕ} {Θ : ProductCurrent (n + n) (V × X) (q + 1)}
  (hΘ : IsPositive Θ)

include hΘ in
/-- **The chart-local vanishing**: near every point of the graph, a closed positive current
carried by `Γ_f` does not see `R ∧ (b - Φ^*b)` for elementary `R` supported near the point. -/
theorem exists_nhds_apply_wedge_sub_pullback_eq_zero (hΘc : IsClosedCurrent Θ)
    (hcar : traceMeasure w Θ hΘ {p : V × X | f p.1 = p.2}ᶜ = 0) (v₀ : V) :
    ∃ U : Set (V × X), IsOpen U ∧ (v₀, f v₀) ∈ U ∧
      ∀ (h : V × X → ℝ) (hh : ChartSmooth (n := n + n) h), tsupport h ⊆ U →
      ∀ (c : Fin q → SmoothRealForm (n + n) (V × X) 2) (hc : ∀ i, (c i).IsTypeOneOne)
        (b : SmoothRealForm (n + n) (V × X) 2) (hb : b.IsTypeOneOne),
        Θ (wedgeTestLM (isTypeOneOne_sub_pullback_graph hf hb) q (elemTest h hh q c hc)) = 0 := by
  set E := graphChart n f v₀ with hE
  set W := graphDomain n f v₀ with hWdef
  set F := graphRep n f v₀ with hFdef
  have hWo : IsOpen W := isOpen_graphDomain hf v₀
  have hWt : W ⊆ E.val.target := graphDomain_subset_target v₀
  have hx₀ : ((v₀, f v₀) : V × X) ∈ E.val.source := mem_complexChartAt_source _
  set z₀ := E.val (v₀, f v₀) with hz₀
  obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.mp hWo z₀ (mem_graphDomain_self v₀)
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hball : ∀ s, s < ε → closedBall z₀ s ⊆ W := fun s hs =>
    (closedBall_subset_ball hs).trans hεt
  have hBW : ball z₀ r ⊆ W :=
    ball_subset_closedBall.trans (hball r (by rw [hr]; linarith))
  have hBt : ball z₀ r ⊆ E.val.target := hBW.trans hWt
  refine ⟨E.val.symm '' ball z₀ r, E.val.symm.isOpen_image_of_subset_source isOpen_ball
    (by simpa using hBt), ⟨z₀, mem_ball_self hr0, E.val.left_inv hx₀⟩, ?_⟩
  intro h hh hhU c hc b hb
  have hΓm : MeasurableSet {p : V × X | f p.1 = p.2} := (isClosed_graph hf).measurableSet
  -- cut-offs
  let χ : ContDiffBump z₀ := ⟨3 * r, 7 / 2 * r, by positivity, by linarith⟩
  let ρb : ContDiffBump z₀ := ⟨2 * r, 5 / 2 * r, by positivity, by linarith⟩
  let ρc : ContDiffBump z₀ := ⟨r, 3 / 2 * r, hr0, by linarith⟩
  have hχW : tsupport χ ⊆ W := by
    rw [χ.tsupport_eq]; exact hball (7 / 2 * r) (by rw [hr]; linarith)
  have hρW : tsupport ρb ⊆ W := by
    rw [ρb.tsupport_eq]; exact hball (5 / 2 * r) (by rw [hr]; linarith)
  have hρcW : tsupport ρc ⊆ W := by
    rw [ρc.tsupport_eq]; exact hball (3 / 2 * r) (by rw [hr]; linarith)
  have hcl : ∀ L : ComplexModel (n + n) →L[ℝ] ℝ, ContDiffOn ℝ ∞ (fun z => L z) W :=
    fun L => L.contDiff.contDiffOn
  -- the global functions
  have hg : ∀ a, ChartSmooth (n := n + n)
      (chartExtend E fun z => χ z * (graphNormalFun F a z).re) := fun a =>
    chartSmooth_chartExtend_mul_of_isOpen E hWo hWt χ.contDiff χ.hasCompactSupport hχW
      (contDiffOn_re_graphNormalFun hf v₀ a)
  have hF : ∀ a, ChartSmooth (n := n + n)
      (chartExtend E fun z => χ z * (graphNormalFun F a z).im) := fun a =>
    chartSmooth_chartExtend_mul_of_isOpen E hWo hWt χ.contDiff χ.hasCompactSupport hχW
      (contDiffOn_im_graphNormalFun hf v₀ a)
  have hS : ∀ c', ChartSmooth (n := n + n) (chartExtend E fun z => χ z * coordFun c' z) :=
    fun c' => chartSmooth_chartExtend_mul_of_isOpen E hWo hWt χ.contDiff χ.hasCompactSupport hχW
      (hcl _)
  have hρ : ChartSmooth (n := n + n) (chartExtend E fun z => ρb z) :=
    chartSmooth_chartExtend E ρb.contDiff ρb.hasCompactSupport (hρW.trans hWt)
  -- the coefficient functions
  set π : ComplexModel (n + n) → ComplexModel (n + n) →L[ℂ] ComplexModel (n + n) :=
    fun z => graphProj (fderiv ℂ F (baseCoord z)) with hπdef
  set γ : Fin 2 × Fin n → Fin (2 * (n + n)) → ComplexModel (n + n) → ℝ :=
    fun a c' z => (b.coeff E z) ![normalVec a, halfVecOf (π z) c'] with hγdef
  set η : Fin (2 * (n + n)) → Fin (2 * (n + n)) → ComplexModel (n + n) → ℝ :=
    fun c' d z => (b.coeff E z - b.coeff E (graphModel F z))
      ![π z (topBasis (n + n) c'), π z (topBasis (n + n) d)] / 2 with hηdef
  have hbE : ContDiffOn ℝ ∞ (b.coeff E) W := (b.smooth E).mono hWt
  have hbπ : ContDiffOn ℝ ∞ (fun z => b.coeff E (graphModel F z)) W :=
    (b.smooth E).comp (contDiffOn_graphModel hf v₀) fun z hz => graphModel_mem_target hz
  have hπv : ∀ ξ, ContDiffOn ℝ ∞ (fun z => π z ξ) W := fun ξ =>
    contDiffOn_graphProj_apply hf v₀ ξ
  have hhalf : ∀ c', ContDiffOn ℝ ∞ (fun z => halfVecOf (π z) c') W := fun c' => by
    simp only [halfVecOf]
    exact (hπv _).add ((contDiffOn_const.sub (hπv _)).const_smul (1 / 2 : ℝ))
  have hγ : ∀ a c', ContDiffOn ℝ ∞ (γ a c') W := fun a c' =>
    contDiffOn_twoForm_apply hbE contDiffOn_const (hhalf c')
  have hη : ∀ c' d, ContDiffOn ℝ ∞ (η c' d) W := fun c' d =>
    (contDiffOn_twoForm_apply (hbE.sub hbπ) (hπv _) (hπv _)).div_const 2
  have hΓ : ∀ a c', ChartSmooth (n := n + n) (chartExtend E fun z => ρc z * γ a c' z) :=
    fun a c' => chartSmooth_chartExtend_mul_of_isOpen E hWo hWt ρc.contDiff ρc.hasCompactSupport
      hρcW (hγ a c')
  have hΛ : ∀ c' d, ChartSmooth (n := n + n) (chartExtend E fun z => ρc z * η c' d z) :=
    fun c' d => chartSmooth_chartExtend_mul_of_isOpen E hWo hWt ρc.contDiff ρc.hasCompactSupport
      hρcW (hη c' d)
  set R := elemTest h hh q c hc with hRdef
  have hRcoeff : ∀ (f' : ComplexChart (n + n) (V × X)) z,
      ((R : testSpace (n + n) (V × X) q) : SmoothRealForm (n + n) (V × X) (2 * q)).coeff f' z =
        h (f'.val.symm z) • wedgeProd q fun i => (c i).coeff f' z :=
    fun f' z => elemForm_coeff h hh q c f' z
  have hW : ∀ {β : SmoothRealForm (n + n) (V × X) 2} (hβ : β.IsTypeOneOne)
      (f' : ComplexChart (n + n) (V × X)) z,
      ((wedgeTestLM hβ q R : testSpace (n + n) (V × X) (q + 1)) :
        SmoothRealForm (n + n) (V × X) (2 * (q + 1))).coeff f' z =
        coordinateWedge (((R : testSpace (n + n) (V × X) q) :
          SmoothRealForm (n + n) (V × X) (2 * q)).coeff f' z) (β.coeff f' z) :=
    fun _ _ _ => rfl
  have hsm : ∀ {H : V × X → ℝ} (hH : ChartSmooth (n := n + n) H)
      (φ : testSpace (n + n) (V × X) (q + 1)) (f' : ComplexChart (n + n) (V × X)) z,
      ((smulTest H hH φ : testSpace (n + n) (V × X) (q + 1)) :
        SmoothRealForm (n + n) (V × X) (2 * (q + 1))).coeff f' z =
        H (f'.val.symm z) • (φ : SmoothRealForm (n + n) (V × X) (2 * (q + 1))).coeff f' z :=
    fun _ _ _ _ => rfl
  have hsuppB : ∀ z ∈ E.val.target, h (E.val.symm z) ≠ 0 → z ∈ ball z₀ r := by
    intro z hz h0
    obtain ⟨z', hz', hzz'⟩ := hhU (subset_tsupport _ h0)
    have hzz : z' = z := by
      have h' := congrArg E.val hzz'
      rwa [E.val.right_inv (hBt hz'), E.val.right_inv hz] at h'
    rwa [← hzz]
  have hχ1 : ∀ z ∈ ball z₀ r, (fun y => χ y) =ᶠ[𝓝 z] fun _ => 1 := by
    intro z hz
    have hz3 : z ∈ ball z₀ (3 * r) := ball_subset_ball (by linarith) hz
    filter_upwards [isOpen_ball.mem_nhds hz3] with y hy
    exact χ.one_of_mem_closedBall (ball_subset_closedBall hy)
  have hρc1 : ∀ z ∈ ball z₀ r, ρc z = 1 := fun z hz =>
    ρc.one_of_mem_closedBall (ball_subset_closedBall hz)
  have hzero : ∀ (f' : ComplexChart (n + n) (V × X)) z, h (f'.val.symm z) = 0 →
      ∀ β : SmoothRealForm (n + n) (V × X) 2,
        coordinateWedge (((R : testSpace (n + n) (V × X) q) :
          SmoothRealForm (n + n) (V × X) (2 * q)).coeff f' z) (β.coeff f' z) = 0 := by
    intro f' z h0 β
    rw [hRcoeff, h0, coordinateWedge_smul_zero_left]
  -- the decomposition
  have hsplit : Θ (wedgeTestLM (isTypeOneOne_sub_pullback_graph hf hb) q R) =
      (∑ a, ∑ c', Θ (smulTest _ (hΓ a c')
        (wedgeTestLM (isTypeOneOne_pi11Form (exactPair _ _ (hg a) (hS c'))) q R))) +
      ∑ c', ∑ d, Θ (smulTest _ (hΛ c' d)
        (wedgeTestLM (isTypeOneOne_pi11Form (exactPair _ _ (hS c') (hS d))) q R)) := by
    simp only [← map_sum, ← map_add]
    refine hΘ.apply_eq_of_coeff_eqOn fun f' z hz => ?_
    refine SlotTestForms.coeff_eq_of_chart E (K := tsupport h)
      (hhU.trans (image_symm_subset_source hBt)) ?_ ?_ ?_ f' hz
    · intro z hz
      simp only [Submodule.coe_add, Submodule.coe_sum, coeff_add,
        ClosedCurrentLocalTests.coeff_sum, hsm, hW]
      by_cases h0 : h (E.val.symm z) = 0
      · simp only [hzero E z h0, smul_zero, Finset.sum_const_zero, add_zero]
      · have hzB := hsuppB z hz h0
        have hzW : z ∈ W := hBW hzB
        have hX : ∀ a c', (exactPair _ _ (hg a) (hS c')).coeff E z =
            pairForm (graphNormalRe (fderiv ℂ F (baseCoord z)) a) (coordFun c') := fun a c' =>
          exactPair_cutoff_coeff_of_hasFDerivAt E (hg a) (hS c') hz (hχ1 z hzB)
            (hasFDerivAt_re_graphNormalFun (differentiableAt_graphRep hf hzW) a)
            (coordFun c').hasFDerivAt
        have hY : ∀ c' d, (exactPair _ _ (hS c') (hS d)).coeff E z =
            pairForm (coordFun c') (coordFun d) := fun c' d =>
          exactPair_cutoff_coeff_of_hasFDerivAt E (hS c') (hS d) hz (hχ1 z hzB)
            (coordFun c').hasFDerivAt (coordFun d).hasFDerivAt
        have hΓz : ∀ a c', chartExtend E (fun z => ρc z * γ a c' z) (E.val.symm z) =
            γ a c' z := fun a c' => by
          rw [SlotTestForms.chartExtend_symm hz, hρc1 z hzB, one_mul]
        have hΛz : ∀ c' d, chartExtend E (fun z => ρc z * η c' d z) (E.val.symm z) =
            η c' d z := fun c' d => by
          rw [SlotTestForms.chartExtend_symm hz, hρc1 z hzB, one_mul]
        rw [coeff_sub, pullback_graphProjMap_coeff hf b hzW,
          sub_comp_eq (π z) (graphNormalRe (fderiv ℂ F (baseCoord z))) normalVec
            (sub_graphProj_eq _) _ _ (hb E z hz) (hb E _ (graphModel_mem_target hzW))]
        simp only [pi11Form_coeff, hX, hY, hΓz, hΛz]
        rw [← wedgeCLM_apply, map_add, map_sum, map_sum]
        simp only [map_sum, map_smul, wedgeCLM_apply, hγdef, hηdef]
        rfl
    · intro f' z' _ hK
      rw [hW]
      exact hzero f' z' (image_eq_zero_of_notMem_tsupport hK) _
    · intro f' z' _ hK
      simp only [Submodule.coe_add, Submodule.coe_sum, coeff_add,
        ClosedCurrentLocalTests.coeff_sum, hsm, hW,
        hzero f' z' (image_eq_zero_of_notMem_tsupport hK), smul_zero, Finset.sum_const_zero,
        add_zero]
  rw [hsplit]
  -- on the graph, inside the chart: the chart point is fixed by `Φ_E` or lies outside `W`
  have hgraph : ∀ x ∈ {p : V × X | f p.1 = p.2}, x ∈ E.val.source → E.val x ∈ W →
      graphModel F (E.val x) = E.val x := fun x hx hxs hxW =>
    graphModel_eq_of_mem_graph hx hxs hxW
  -- the normal terms vanish
  have hg0 : ∀ a, ∀ x ∈ {p : V × X | f p.1 = p.2},
      chartExtend E (fun z => χ z * (graphNormalFun F a z).re) x = 0 := by
    intro a x hx
    by_cases hxs : x ∈ E.val.source
    · rw [chartExtend_of_mem hxs]
      by_cases hxW : E.val x ∈ W
      · rw [graphNormalFun_eq_zero_of_graphModel_eq (hgraph x hx hxs hxW) a, Complex.zero_re,
          mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport (fun h' => hxW (hχW h')), zero_mul]
    · exact chartExtend_of_notMem hxs
  have hpair : ∀ a, IsHoloPairOn (N := n + n)
      (chartExtend E fun z => χ z * (graphNormalFun F a z).re)
      (chartExtend E fun z => χ z * (graphNormalFun F a z).im)
      (chartExtend E fun z => ρb z) := fun a =>
    isHoloPairOn_re_im E (O := ball z₀ (3 * r)) isOpen_ball
      (fun z hz => differentiableAt_graphNormalFun hf
        (hball (7 / 2 * r) (by rw [hr]; linarith)
          (ball_subset_closedBall (ball_subset_ball (by linarith) hz))) a)
      (fun z hz => χ.one_of_mem_closedBall (ball_subset_closedBall hz))
      (by
        rw [ρb.support_eq]
        exact ball_subset_ball (show (5 / 2 * r : ℝ) ≤ 3 * r by linarith))
  have hρ0 : ∀ x, 0 ≤ chartExtend E (fun z => ρb z) x :=
    chartExtend_nonneg fun _ => ρb.nonneg
  have hΓρ : ∀ a c' x, chartExtend E (fun z => ρc z * γ a c' z) x ≠ 0 →
      chartExtend E (fun z => ρb z) x = 1 := by
    intro a c' x hx
    have hxs : x ∈ E.val.source := by
      by_contra hxs
      exact hx (chartExtend_of_notMem hxs)
    rw [chartExtend_of_mem hxs] at hx ⊢
    have hρx : E.val x ∈ ball z₀ (3 / 2 * r) := by
      rw [← ρc.support_eq]
      exact left_ne_zero_of_mul hx
    exact ρb.one_of_mem_closedBall (show E.val x ∈ closedBall z₀ (2 * r) from
      ball_subset_closedBall (ball_subset_ball (show (3 / 2 * r : ℝ) ≤ 2 * r by linarith) hρx))
  have h1 : ∀ a c', Θ (smulTest _ (hΓ a c')
      (wedgeTestLM (isTypeOneOne_pi11Form (exactPair _ _ (hg a) (hS c'))) q R)) = 0 :=
    fun a c' => apply_wedge_normalPair_eq_zero w hΘ (hg a) (hF a) (hS c') hΘc hΓm hcar (hg0 a)
      (hpair a) hρ hρ0 (hΓ a c') (hΓρ a c') R
  -- the remaining terms vanish on the graph
  have hΛ0 : ∀ c' d, ∀ x ∈ {p : V × X | f p.1 = p.2},
      chartExtend E (fun z => ρc z * η c' d z) x = 0 := by
    intro c' d x hx
    by_cases hxs : x ∈ E.val.source
    · rw [chartExtend_of_mem hxs]
      by_cases hxW : E.val x ∈ W
      · simp only [hηdef]
        rw [hgraph x hx hxs hxW, sub_self]
        simp
      · rw [image_eq_zero_of_notMem_tsupport (fun h' => hxW (hρcW h')), zero_mul]
    · exact chartExtend_of_notMem hxs
  have h2 : ∀ c' d, Θ (smulTest _ (hΛ c' d)
      (wedgeTestLM (isTypeOneOne_pi11Form (exactPair _ _ (hS c') (hS d))) q R)) = 0 :=
    fun c' d => apply_smulTest_eq_zero w hΘ hΓm hcar _ (hΛ c' d) (hΛ0 c' d)
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

end Core

/-! ### The tangential reduction -/

section Reduction

open ProductComplexManifold SkodaElMirSubmanifold ChartPartition
open scoped ProductComplexManifold

variable {n : ℕ} {V X : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel n) V]
  [IsComplexManifold n V] [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {f : V → X}
  (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
  [CompactSpace V] [CompactSpace X] [MeasurableSpace (V × X)] [BorelSpace (V × X)]
  (w : KahlerBackground (n + n) (V × X)) {q : ℕ} {Θ : ProductCurrent (n + n) (V × X) (q + 1)}
  (hΘ : IsPositive Θ)

/-- The pulled-back slots. -/
abbrev pullSlotsGraph (b : Fin (q + 1) → SmoothRealForm (n + n) (V × X) 2) :
    Fin (q + 1) → SmoothRealForm (n + n) (V × X) 2 :=
  fun i => SmoothRealForm.pullback (contMDiff_graphProjMap hf) (b i)

omit [CompactSpace V] [CompactSpace X] [MeasurableSpace (V × X)] [BorelSpace (V × X)] in
include hΘ in
/-- Permuting the slots of an elementary form does not change the value of a positive current. -/
theorem apply_elemTest_comp_perm {h : V × X → ℝ} (hh : ChartSmooth (n := n + n) h)
    (b : Fin (q + 1) → SmoothRealForm (n + n) (V × X) 2) (hb : ∀ i, (b i).IsTypeOneOne)
    (σ : Equiv.Perm (Fin (q + 1))) :
    Θ (elemTest h hh (q + 1) (fun j => b (σ j)) fun j => hb (σ j)) =
      Θ (elemTest h hh (q + 1) b hb) := by
  refine hΘ.apply_eq_of_coeff_eqOn fun e z _ => ?_
  rw [coe_elemTest, coe_elemTest, elemForm_coeff, elemForm_coeff]
  exact congrArg _ (wedgeProd_comp_perm (q + 1) (fun j => (b j).coeff e z) σ)

omit [CompactSpace V] [CompactSpace X] [MeasurableSpace (V × X)] [BorelSpace (V × X)] in
include hΘ in
/-- **Replacing one slot `bᵢ` by `Φ^*bᵢ`.** -/
theorem apply_elemTest_update_pullback {U : Set (V × X)}
    (hU : ∀ (h : V × X → ℝ) (hh : ChartSmooth (n := n + n) h), tsupport h ⊆ U →
      ∀ (c : Fin q → SmoothRealForm (n + n) (V × X) 2) (hc : ∀ i, (c i).IsTypeOneOne)
        (b : SmoothRealForm (n + n) (V × X) 2) (hb : b.IsTypeOneOne),
        Θ (wedgeTestLM (isTypeOneOne_sub_pullback_graph hf hb) q (elemTest h hh q c hc)) = 0)
    {h : V × X → ℝ} (hh : ChartSmooth (n := n + n) h) (hhU : tsupport h ⊆ U)
    (b : Fin (q + 1) → SmoothRealForm (n + n) (V × X) 2) (hb : ∀ i, (b i).IsTypeOneOne)
    (i : Fin (q + 1)) (hb' : ∀ j, (Function.update b i
      (SmoothRealForm.pullback (contMDiff_graphProjMap hf) (b i)) j).IsTypeOneOne) :
    Θ (elemTest h hh (q + 1) b hb) =
      Θ (elemTest h hh (q + 1) (Function.update b i
        (SmoothRealForm.pullback (contMDiff_graphProjMap hf) (b i))) hb') := by
  classical
  set σ := Equiv.swap i (Fin.last q)
  set b' := SmoothRealForm.pullback (contMDiff_graphProjMap hf) (b i)
  rw [← apply_elemTest_comp_perm hΘ hh b hb σ,
    ← apply_elemTest_comp_perm hΘ hh (Function.update b i b') hb' σ]
  have hupd : (fun j => Function.update b i b' (σ j)) =
      Function.update (fun j => b (σ j)) (Fin.last q) b' := by
    have h1 := Function.update_comp_equiv b σ i b'
    have h2 : σ.symm i = Fin.last q := by
      rw [Equiv.symm_swap, Equiv.swap_apply_left]
    rw [h2] at h1
    exact h1
  have hlast : b (σ (Fin.last q)) = b i := by rw [Equiv.swap_apply_right]
  have hdiff : elemTest h hh (q + 1) (fun j => b (σ j)) (fun j => hb (σ j)) -
      elemTest h hh (q + 1) (fun j => Function.update b i b' (σ j)) (fun j => hb' (σ j)) =
      wedgeTestLM (isTypeOneOne_sub_pullback_graph hf (hb i)) q
        (elemTest h hh q (fun j => b (σ j.castSucc)) fun j => hb (σ j.castSucc)) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sub, coe_elemTest, coe_elemTest, coe_wedgeTestLM, coe_elemTest, hupd,
      elemForm_succ, elemForm_succ]
    have hinit : (fun j : Fin q => Function.update (fun j => b (σ j)) (Fin.last q) b'
        j.castSucc) = fun j => b (σ j.castSucc) := by
      funext j
      rw [Function.update_of_ne (Fin.castSucc_lt_last j).ne]
    rw [hinit, Function.update_self, hlast]
    refine smoothRealForm_ext fun e z => ?_
    simp only [coeff_sub, wedgeTwo_coeff]
    rw [← wedgeCLM_apply, ← wedgeCLM_apply, ← wedgeCLM_apply, map_sub]
  have h0 := hU h hh hhU _ (fun j => hb (σ j.castSucc)) (b i) (hb i)
  rw [← hdiff, map_sub] at h0
  exact sub_eq_zero.mp h0

omit [CompactSpace V] [CompactSpace X] [MeasurableSpace (V × X)] [BorelSpace (V × X)] in
theorem elemTest_congr {h : V × X → ℝ} (hh : ChartSmooth (n := n + n) h) {k : ℕ}
    {b b' : Fin k → SmoothRealForm (n + n) (V × X) 2} (hbb : b = b')
    (hb : ∀ i, (b i).IsTypeOneOne) (hb' : ∀ i, (b' i).IsTypeOneOne) :
    elemTest h hh k b hb = elemTest h hh k b' hb' := by
  subst hbb
  rfl

omit [CompactSpace V] [CompactSpace X] [MeasurableSpace (V × X)] [BorelSpace (V × X)] in
include hΘ in
/-- **Replacing all the slots `bᵢ` by `Φ^*bᵢ`.** -/
theorem apply_elemTest_pullSlots {U : Set (V × X)}
    (hU : ∀ (h : V × X → ℝ) (hh : ChartSmooth (n := n + n) h), tsupport h ⊆ U →
      ∀ (c : Fin q → SmoothRealForm (n + n) (V × X) 2) (hc : ∀ i, (c i).IsTypeOneOne)
        (b : SmoothRealForm (n + n) (V × X) 2) (hb : b.IsTypeOneOne),
        Θ (wedgeTestLM (isTypeOneOne_sub_pullback_graph hf hb) q (elemTest h hh q c hc)) = 0)
    {h : V × X → ℝ} (hh : ChartSmooth (n := n + n) h) (hhU : tsupport h ⊆ U)
    (b : Fin (q + 1) → SmoothRealForm (n + n) (V × X) 2) (hb : ∀ i, (b i).IsTypeOneOne) :
    Θ (elemTest h hh (q + 1) b hb) =
      Θ (elemTest h hh (q + 1) (pullSlotsGraph hf b)
        fun i => isTypeOneOne_pullback (contMDiff_graphProjMap hf) (hb i)) := by
  classical
  set bk : ℕ → Fin (q + 1) → SmoothRealForm (n + n) (V × X) 2 := fun k j =>
    if (j : ℕ) < k then SmoothRealForm.pullback (contMDiff_graphProjMap hf) (b j) else b j
    with hbkdef
  have hbk : ∀ k j, (bk k j).IsTypeOneOne := fun k j => by
    simp only [hbkdef]
    split_ifs
    · exact isTypeOneOne_pullback (contMDiff_graphProjMap hf) (hb j)
    · exact hb j
  have hstep : ∀ k, k < q + 1 → Θ (elemTest h hh (q + 1) (bk k) (hbk k)) =
      Θ (elemTest h hh (q + 1) (bk (k + 1)) (hbk (k + 1))) := by
    intro k hk
    have hkk : bk k ⟨k, hk⟩ = b ⟨k, hk⟩ := by simp [hbkdef]
    have hupd : Function.update (bk k) ⟨k, hk⟩
        (SmoothRealForm.pullback (contMDiff_graphProjMap hf) (bk k ⟨k, hk⟩)) = bk (k + 1) := by
      funext j
      by_cases hj : j = ⟨k, hk⟩
      · subst hj
        rw [Function.update_self, hkk]
        simp [hbkdef]
      · rw [Function.update_of_ne hj]
        have hjk : (j : ℕ) ≠ k := fun h' => hj (Fin.ext h')
        simp only [hbkdef]
        split_ifs with h1 h2 h2 <;> first | rfl | omega
    rw [apply_elemTest_update_pullback hf hΘ hU hh hhU (bk k) (hbk k) ⟨k, hk⟩
      (by rw [hupd]; exact hbk (k + 1))]
    exact congrArg Θ (elemTest_congr hh hupd _ _)
  have hall : ∀ k, k ≤ q + 1 → Θ (elemTest h hh (q + 1) b hb) =
      Θ (elemTest h hh (q + 1) (bk k) (hbk k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact congrArg Θ (elemTest_congr hh (funext fun j => by simp [hbkdef]) _ _)
    | succ k ih =>
      intro hk
      rw [ih (Nat.le_of_succ_le hk), hstep k (Nat.lt_of_succ_le hk)]
  rw [hall (q + 1) le_rfl]
  exact congrArg Θ (elemTest_congr hh (funext fun j => by simp [hbkdef, j.isLt]) _ _)

include hΘ in
/-- **`h` may be replaced by `h ∘ Φ`** (they agree on `Γ_f`). -/
theorem apply_elemTest_comp_graphProjMap
    (hcar : traceMeasure w Θ hΘ {p : V × X | f p.1 = p.2}ᶜ = 0)
    {h : V × X → ℝ} (hh : ChartSmooth (n := n + n) h)
    (c : Fin (q + 1) → SmoothRealForm (n + n) (V × X) 2) (hc : ∀ i, (c i).IsTypeOneOne) :
    Θ (elemTest (fun x => h (graphProjMap f x)) (chartSmooth_comp (contMDiff_graphProjMap hf) hh)
      (q + 1) c hc) = Θ (elemTest h hh (q + 1) c hc) := by
  have hΓm : MeasurableSet {p : V × X | f p.1 = p.2} := (isClosed_graph hf).measurableSet
  have hd : ChartSmooth (n := n + n) (fun x => h (graphProjMap f x) - h x) := fun e =>
    ((chartSmooth_comp (contMDiff_graphProjMap hf) hh) e).sub (hh e)
  have hsplit : elemTest (fun x => h (graphProjMap f x))
      (chartSmooth_comp (contMDiff_graphProjMap hf) hh) (q + 1) c hc =
      elemTest h hh (q + 1) c hc +
        smulTest _ hd (elemTest (fun _ => 1) (chartSmooth_const 1) (q + 1) c hc) := by
    refine Subtype.ext (smoothRealForm_ext fun e z => ?_)
    simp only [Submodule.coe_add, coeff_add, coe_elemTest, elemForm_coeff]
    change _ = _ + (fun x => h (graphProjMap f x) - h x) (e.val.symm z) •
      (elemForm (fun _ => 1) (chartSmooth_const 1) (q + 1) c).coeff e z
    rw [elemForm_coeff, one_smul, ← add_smul, add_sub_cancel]
  rw [hsplit, map_add, apply_smulTest_eq_zero w hΘ hΓm hcar _ hd, add_zero]
  intro p hp
  rw [graphProjMap_eq_self hp, sub_self]

include hΘ in
/-- **The tangential reduction on the graph** (`demailly-cadg:III.2.10` for `Γ_f`): a closed
positive current carried by the graph of a holomorphic `f : V → X` satisfies
`Θ (Φ^*φ) = Θ φ` for every test form `φ`, `Φ(v, x) = (v, f v)`. -/
theorem apply_pullback_graphProjMap_eq (hΘc : IsClosedCurrent Θ)
    (hcar : traceMeasure w Θ hΘ {p : V × X | f p.1 = p.2}ᶜ = 0)
    (φ : testSpace (n + n) (V × X) (q + 1)) :
    Θ (pullbackTestLM (contMDiff_graphProjMap hf) (q + 1) φ) = Θ φ := by
  classical
  have hΓm : MeasurableSet {p : V × X | f p.1 = p.2} := (isClosed_graph hf).measurableSet
  choose U hUo hUmem hUvan using
    exists_nhds_apply_wedge_sub_pullback_eq_zero hf w hΘ hΘc hcar (q := q)
  suffices hsuff : Θ ∘ₗ pullbackTestLM (contMDiff_graphProjMap hf) (q + 1) = Θ from
    LinearMap.congr_fun hsuff φ
  refine linearMap_ext_elem fun h hh b hb => ?_
  set S : V × X → TopologicalSpace.Opens (V × X) := fun p =>
    if f p.1 = p.2 then ⟨U p.1, hUo p.1⟩
    else ⟨{p : V × X | f p.1 = p.2}ᶜ, (isClosed_graph hf).isOpen_compl⟩ with hSdef
  have hcover : ∀ p : V × X, ∃ i, p ∈ S i := by
    intro p
    refine ⟨p, ?_⟩
    by_cases hp : f p.1 = p.2
    · simp only [hSdef, hp, if_true, TopologicalSpace.Opens.mem_mk]
      obtain ⟨v, x⟩ := p
      simp only at hp
      subst hp
      exact hUmem v
    · simp only [hSdef, hp, if_false, TopologicalSpace.Opens.mem_mk]
      exact hp
  obtain ⟨N, χ, idx, hχs, -, hχS, -, hsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n + n) S hcover
  have hdecomp : elemTest h hh (q + 1) b hb =
      ∑ a, elemTest (fun x => χ a x * h x) (chartSmooth_mul (hχs a) hh) (q + 1) b hb := by
    refine Subtype.ext (smoothRealForm_ext fun e z => ?_)
    simp only [Submodule.coe_sum, ClosedCurrentLocalTests.coeff_sum, coe_elemTest, elemForm_coeff]
    rw [← Finset.sum_smul, ← Finset.sum_mul, hsum, one_mul]
  rw [LinearMap.comp_apply, hdecomp, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  set ha := chartSmooth_mul (hχs a) hh
  have hpull : pullbackTestLM (contMDiff_graphProjMap hf) (q + 1)
      (elemTest (fun x => χ a x * h x) ha (q + 1) b hb) =
      elemTest (fun x => (fun x => χ a x * h x) (graphProjMap f x))
        (chartSmooth_comp (contMDiff_graphProjMap hf) ha) (q + 1) (pullSlotsGraph hf b)
        (fun i => isTypeOneOne_pullback (contMDiff_graphProjMap hf) (hb i)) :=
    Subtype.ext (pullback_elemForm (contMDiff_graphProjMap hf) _ ha (q + 1) b)
  rw [hpull, apply_elemTest_comp_graphProjMap hf w hΘ hcar ha]
  by_cases hp : f (idx a).1 = (idx a).2
  · have hsub : tsupport (fun x => χ a x * h x) ⊆ U (idx a).1 := by
      refine tsupport_mul_subset_left.trans ?_
      have h' := hχS a
      simp only [hSdef, hp, if_true, TopologicalSpace.Opens.coe_mk] at h'
      exact h'
    exact (apply_elemTest_pullSlots hf hΘ (hUvan (idx a).1) ha hsub b hb).symm
  · have hsub : tsupport (χ a) ⊆ {p : V × X | f p.1 = p.2}ᶜ := by
      have h' := hχS a
      simp only [hSdef, hp, if_false, TopologicalSpace.Opens.coe_mk] at h'
      exact h'
    have hvan : ∀ x ∈ {p : V × X | f p.1 = p.2}, χ a x * h x = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hsub h' hx), zero_mul]
    have hz : ∀ (c : Fin (q + 1) → SmoothRealForm (n + n) (V × X) 2)
        (hc : ∀ i, (c i).IsTypeOneOne), Θ (elemTest _ ha (q + 1) c hc) = 0 := by
      intro c hc
      have he : elemTest _ ha (q + 1) c hc =
          smulTest _ ha (elemTest (fun _ => 1) (chartSmooth_const 1) (q + 1) c hc) := by
        refine Subtype.ext (smoothRealForm_ext fun e z => ?_)
        change (elemForm _ ha (q + 1) c).coeff e z =
          (fun x => χ a x * h x) (e.val.symm z) •
            (elemForm (fun _ => 1) (chartSmooth_const 1) (q + 1) c).coeff e z
        rw [elemForm_coeff, elemForm_coeff, one_smul]
      rw [he]
      exact apply_smulTest_eq_zero w hΘ hΓm hcar _ ha hvan
    rw [hz, hz]

end Reduction

end SGPT.Foundations.Analysis.Pending.GraphTangentialReduction
