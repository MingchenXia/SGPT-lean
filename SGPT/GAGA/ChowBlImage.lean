import SGPT.GAGA.ChowBlCone
import SGPT.GAGA.SerreM6Segre
import SGPT.Foundations.Analysis.Pending.CartanLocalReduction

/-!
# Analytic subsets of a projective manifold are analytic in `ℙᴺ`


Let `M` be a compact complex manifold and `Ψ : M → ℙᴺ` a holomorphic embedding
(`SGPT.GAGA.H0S.IsHolomorphicEmbedding`).  Near a point `Ψ(c)`, `Ψ(M)` is the graph
`{(L₀ y)₂ = g((L₀ y)₁)}` in the affine chart, and its points come from `M` through the
holomorphic map `ψ` of the `exists_affine_graph`.  Hence:

* `isComplexAnalyticSubset_image`: the image `Ψ(C)` of an analytic subset `C ⊆ M` is an analytic
  subset of `ℙᴺ` (equations: the graph equations and the equations of `C` composed with `ψ`).
  In particular (`chow_image`) Chow's theorem applies to `Ψ(C)`.
* **Theorem A for `𝓘_C(m)`** (`isInSpanAt_genFun_iff`): if homogeneous polynomials `P_k` generate
  the ideal of the cone over `Ψ(C)`, their restrictions `f_k = P_k(Λᵢ)` to `M`, read in the
  affine chart `U_i` (`Λᵢ(x) = (Ψ x)/(Ψ x)_i`), generate the ideal sheaf `𝓘_C` of `C` at every
  point of `Ψ⁻¹(U_i)`.  (A germ vanishing on `C` extends, through the retraction
  `y ↦ ψ((L₀ y)₁)` onto `Ψ(M)`, to a germ on the cone vanishing on the cone over `Ψ(C)`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.GAGA.H0S
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf (HolAt)
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

noncomputable section

namespace SGPT.GAGA.ChowBl

variable {n N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The constant presentation of a closed set near a point of its complement. -/
def complementPresentation {A : Set M} (hA : IsClosed A) {x : M} (hx : x ∉ A) :
    ComplexAnalyticPresentationAt (n := n) A x where
  generatorCount := 1
  generator _ _ := 1
  coordinateNeighborhood := (complexChartAt (n := n) x).val.target ∩
    (complexChartAt (n := n) x).val.symm ⁻¹' Aᶜ
  isOpen_coordinateNeighborhood :=
    (complexChartAt (n := n) x).val.isOpen_inter_preimage_symm hA.isOpen_compl
  center_mem_coordinateNeighborhood := by
    have hxs := mem_complexChartAt_source (n := n) x
    refine ⟨(complexChartAt (n := n) x).val.map_source hxs, ?_⟩
    simp only [mem_preimage, (complexChartAt (n := n) x).val.left_inv hxs]
    exact hx
  coordinateNeighborhood_subset_target := inter_subset_left
  generator_holomorphic _ := differentiableOn_const 1
  zeroLocus := by
    intro y hy hyN
    have hyA : y ∉ A := by
      have := hyN.2
      simp only [mem_preimage, (complexChartAt (n := n) x).val.left_inv hy] at this
      exact this
    simp only [hyA, false_iff, not_forall]
    exact ⟨0, one_ne_zero⟩

variable [CompactSpace M] {Ψ : M → ComplexProjectiveSpace N}

/-- **The image of an analytic subset under a holomorphic embedding is analytic in `ℙᴺ`.** -/
theorem isComplexAnalyticSubset_image (hΨ : IsHolomorphicEmbedding (n := n) Ψ) {C : Set M}
    (hC : IsComplexAnalyticSubset (n := n) C) :
    IsComplexAnalyticSubset (n := N) (Ψ '' C) := by
  intro x
  by_cases hx : x ∈ Ψ '' C
  swap
  · exact ⟨complementPresentation
      (hC.isClosed.isCompact.image hΨ.continuous).isClosed hx⟩
  obtain ⟨c, hcC, rfl⟩ := hx
  set i := chartIndex (Ψ c) with hi
  have hp₀ : Ψ c ∈ (affineChart i).source := mem_affineChart_chartIndex (Ψ c)
  obtain ⟨-, L0, ε, O, g, ψ, hε, hO, hg, hψ, hψmem, -, hgraph⟩ := exists_affine_graph hΨ c i hp₀
  set e := (complexChartAt (n := n) c).val with he
  obtain ⟨P⟩ := hC c
  have hchart : (complexChartAt (n := N) (Ψ c)).val = affineChart i := rfl
  set y₀ := affineChart i (Ψ c) with hy₀
  -- the center
  have hy₀ball : y₀ ∈ ball y₀ ε := mem_ball_self hε
  obtain ⟨hO₀, -, hgr₀⟩ := hgraph y₀ hy₀ball
  have haff₀ : affinePoint i y₀ = Ψ c := by
    rw [hy₀]
    exact (affineChart i).left_inv hp₀
  have hgraph₀ : (L0 y₀).2 = g (L0 y₀).1 :=
    ((hgraph y₀ hy₀ball).2.1).mp (by rw [haff₀]; exact mem_range_self c)
  obtain ⟨hψt₀, hψΨ₀⟩ := hgr₀ hgraph₀
  have hψc : e.symm (ψ (L0 y₀).1) = c := hΨ.injective (by rw [hψΨ₀, haff₀])
  have hψe : ψ (L0 y₀).1 = e c := by
    rw [← hψc, e.right_inv hψt₀]
  -- the map `y ↦ ψ((L₀ y)₁)` is continuous on the open set `{(L₀ y)₁ ∈ O}`
  have hL1 : Continuous fun y : ComplexModel N => (L0 y).1 := continuous_fst.comp L0.continuous
  have hOpre : IsOpen {y : ComplexModel N | (L0 y).1 ∈ O} := hO.preimage hL1
  have hψc' : ContinuousOn (fun y : ComplexModel N => ψ (L0 y).1)
      {y : ComplexModel N | (L0 y).1 ∈ O} :=
    hψ.continuousOn.comp hL1.continuousOn fun _ hy => hy
  refine ⟨{ generatorCount := (N - n) + P.generatorCount
            generator := fun l y => Fin.addCases (motive := fun _ => ℂ) (fun a : Fin (N - n) => ((L0 y).2 - g (L0 y).1) a)
              (fun b : Fin P.generatorCount => P.generator b (ψ (L0 y).1)) l
            coordinateNeighborhood := ball y₀ ε ∩ ({y | (L0 y).1 ∈ O} ∩
              (fun y => ψ (L0 y).1) ⁻¹' P.coordinateNeighborhood)
            isOpen_coordinateNeighborhood := isOpen_ball.inter
              (hψc'.isOpen_inter_preimage hOpre P.isOpen_coordinateNeighborhood)
            center_mem_coordinateNeighborhood := ?_
            coordinateNeighborhood_subset_target := ?_
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · show y₀ ∈ _
    refine ⟨hy₀ball, hO₀, ?_⟩
    show ψ (L0 y₀).1 ∈ P.coordinateNeighborhood
    rw [hψe]
    exact P.center_mem_coordinateNeighborhood
  · intro y _
    show y ∈ (affineChart i).target
    rw [affineChart_target]; trivial
  · intro l
    refine Fin.addCases (fun a => ?_) (fun b => ?_) l
    · simp only [Fin.addCases_left]
      intro y hy
      have h1 : DifferentiableAt ℂ (fun y : ComplexModel N => (L0 y).2) y :=
        (ContinuousLinearMap.snd ℂ _ _ ∘L L0.toContinuousLinearMap).differentiableAt
      have h2 : DifferentiableAt ℂ (fun y : ComplexModel N => (L0 y).1) y :=
        (ContinuousLinearMap.fst ℂ _ _ ∘L L0.toContinuousLinearMap).differentiableAt
      have h3 : DifferentiableAt ℂ (fun y : ComplexModel N => g (L0 y).1) y :=
        (hg.differentiableAt (hO.mem_nhds hy.2.1)).comp y h2
      exact ((EuclideanSpace.proj (𝕜 := ℂ) a).differentiableAt.comp y
        (h1.sub h3)).differentiableWithinAt
    · simp only [Fin.addCases_right]
      intro y hy
      have h2 : DifferentiableAt ℂ (fun y : ComplexModel N => (L0 y).1) y :=
        (ContinuousLinearMap.fst ℂ _ _ ∘L L0.toContinuousLinearMap).differentiableAt
      have h3 : DifferentiableAt ℂ (fun y : ComplexModel N => ψ (L0 y).1) y :=
        (hψ.differentiableAt (hO.mem_nhds hy.2.1)).comp y h2
      exact (((P.generator_holomorphic b).differentiableAt
        (P.isOpen_coordinateNeighborhood.mem_nhds hy.2.2)).comp y h3).differentiableWithinAt
  · intro y' hy' hyN
    change y' ∈ (affineChart i).source at hy'
    set y := affineChart i y' with hydef
    change y ∈ _ at hyN
    show y' ∈ Ψ '' C ↔ ∀ l, Fin.addCases (motive := fun _ => ℂ) (fun a : Fin (N - n) => ((L0 y).2 - g (L0 y).1) a)
      (fun b : Fin P.generatorCount => P.generator b (ψ (L0 y).1)) l = 0
    obtain ⟨hyball, hyO, hyW⟩ := hyN
    have hyy' : affinePoint i y = y' := (affineChart i).left_inv hy'
    obtain ⟨-, hrange, hgr⟩ := hgraph y hyball
    constructor
    · rintro ⟨c', hc'C, hc'⟩
      have hgr' : (L0 y).2 = g (L0 y).1 := hrange.mp (by rw [hyy', ← hc']; exact mem_range_self c')
      obtain ⟨hψt, hψΨ⟩ := hgr hgr'
      have hcc : e.symm (ψ (L0 y).1) = c' := hΨ.injective (by rw [hψΨ, hyy', hc'])
      have hsrc : c' ∈ e.source := by rw [← hcc]; exact e.map_target hψt
      have hec : e c' = ψ (L0 y).1 := by rw [← hcc, e.right_inv hψt]
      have hz := (P.zeroLocus hsrc (by rw [hec]; exact hyW)).mp hc'C
      intro l
      refine Fin.addCases (fun a => ?_) (fun b => ?_) l
      · simp only [Fin.addCases_left]
        show ((L0 y).2 - g (L0 y).1) a = 0
        rw [hgr', sub_self]; rfl
      · simp only [Fin.addCases_right]
        rw [← hec]
        exact hz b
    · intro h0
      have hgr' : (L0 y).2 = g (L0 y).1 := by
        ext a
        have := h0 (Fin.castAdd P.generatorCount a)
        simp only [Fin.addCases_left] at this
        exact sub_eq_zero.mp (by simpa using this)
      obtain ⟨hψt, hψΨ⟩ := hgr hgr'
      have hsrc : e.symm (ψ (L0 y).1) ∈ e.source := e.map_target hψt
      have hec : e (e.symm (ψ (L0 y).1)) = ψ (L0 y).1 := e.right_inv hψt
      have hC' : e.symm (ψ (L0 y).1) ∈ C := by
        refine (P.zeroLocus hsrc (by rw [hec]; exact hyW)).mpr fun b => ?_
        have := h0 (Fin.natAdd (N - n) b)
        simp only [Fin.addCases_right] at this
        rw [hec]
        exact this
      exact ⟨_, hC', by rw [hψΨ, hyy']⟩

/-- **Chow's theorem for the image of an analytic subset of a projective manifold.** -/
theorem chow_image (hΨ : IsHolomorphicEmbedding (n := n) Ψ) {C : Set M}
    (hC : IsComplexAnalyticSubset (n := n) C) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ (μ : Type) (_ : Fintype μ) (P : μ → MvPolynomial (Fin (N + 1)) ℂ),
      (∀ k, (P k).IsHomogeneous m) ∧
      (coneIdeal (Ψ '' C)).GeneratedOn (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N))
        (fun k => SGPT.GAGA.PN.polyTuple (P k)) ∧
      Ψ '' C = {x | ∀ k, MvPolynomial.eval x.rep (P k) = 0} :=
  chow (isComplexAnalyticSubset_image hΨ hC)

/-! ### Theorem A for the ideal of `C`: the restrictions of the generators -/

/-- The homogeneous lift of `Ψ x` normalized in the chart `U_i`. -/
def coneLift (Ψ : M → ComplexProjectiveSpace N) (i : Fin (N + 1)) (x : M) :
    SGPT.GAGA.PN.ConeSpace N :=
  WithLp.toLp 2 (affineLift i (affineChart i (Ψ x)))

/-- The restriction `f_k = P_k(Λᵢ)` of a polynomial to `M`, read in the chart `U_i`. -/
def genFun (Ψ : M → ComplexProjectiveSpace N) (i : Fin (N + 1))
    (P : MvPolynomial (Fin (N + 1)) ℂ) (x : M) : ℂ :=
  SGPT.GAGA.PN.polyTuple P () (coneLift Ψ i x)

theorem coneLift_ne_zero (i : Fin (N + 1)) (x : M) : coneLift Ψ i x ≠ 0 := by
  intro h
  have := congrArg (fun v => v i) h
  simp [coneLift] at this

theorem coneLift_mem_affineCone {A : Set (ComplexProjectiveSpace N)} {i : Fin (N + 1)} {x : M}
    (hx : Ψ x ∈ (affineChart i).source) (hxA : Ψ x ∈ A) : coneLift Ψ i x ∈ affineCone A := by
  intro h
  change mk (affineLift i (affineChart i (Ψ x))) h ∈ A
  have : mk (affineLift i (affineChart i (Ψ x))) h = Ψ x :=
    (affineChart i).left_inv hx
  rw [this]; exact hxA


/-- `Λᵢ` read in the chart of `M` at `x` is holomorphic near `e x`. -/
theorem eventually_differentiableAt_coneLift (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {i : Fin (N + 1)} {x : M} (hx : Ψ x ∈ (affineChart i).source) :
    ∀ᶠ z in 𝓝 ((complexChartAt (n := n) x).val x), DifferentiableAt ℂ
      (fun z => coneLift Ψ i ((complexChartAt (n := n) x).val.symm z)) z := by
  filter_upwards [hΨ.holomorphic x i hx] with z hz
  have h1 : Differentiable ℂ (fun y : ComplexModel N =>
      (WithLp.toLp 2 (affineLift i y) : SGPT.GAGA.PN.ConeSpace N)) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (N + 1) => ℂ)).symm.differentiable.comp
      (differentiable_affineLift i)
  exact (h1 _).comp z hz

/-- A germ holomorphic at `Λᵢ x` pulls back to a germ holomorphic at `x`. -/
theorem holomorphicAt_comp_coneLift (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {i : Fin (N + 1)} {x : M} (hx : Ψ x ∈ (affineChart i).source)
    {c : SGPT.GAGA.PN.ConeSpace N → ℂ} (hc : OkaRelationSheaf.HolAt c (coneLift Ψ i x)) :
    HolomorphicAt n (fun x' => c (coneLift Ψ i x')) x := by
  have hxs : x ∈ (chartAt (ComplexModel n) x).source := mem_chart_source _ x
  refine (CoherentIdealColon.holomorphicAt_iff_holAt_chart hxs).mpr ?_
  refine SGPT.GAGA.PN.HolAt.comp_of_eventually (φ := fun z => coneLift Ψ i
    ((chartAt (ComplexModel n) x).symm z)) ?_ (eventually_differentiableAt_coneLift hΨ hx)
  rw [(chartAt (ComplexModel n) x).left_inv hxs]
  exact hc

theorem holomorphicAt_genFun (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {i : Fin (N + 1)} {x : M} (hx : Ψ x ∈ (affineChart i).source)
    (P : MvPolynomial (Fin (N + 1)) ℂ) : HolomorphicAt n (genFun Ψ i P) x :=
  holomorphicAt_comp_coneLift hΨ hx (Eventually.of_forall fun _ =>
    (SGPT.GAGA.PN.differentiable_eval_poly P).differentiableAt)

/-- **Theorem A for `𝓘_C(m)`**: if the homogeneous polynomials `P_k` generate the ideal sheaf of
the cone over `Ψ(C)` on `ℂ^{N+1} ∖ 0`, then their restrictions `f_k = P_k(Λᵢ)` generate the ideal
sheaf `𝓘_C ⊆ 𝒪_M` at every point of `Ψ⁻¹(U_i)`. -/
theorem vanishingIdeal_mem_iff_isInSpanAt_genFun (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    {C : Set M} {K : ℕ} {P : Fin K → MvPolynomial (Fin (N + 1)) ℂ}
    (hgen : (coneIdeal (Ψ '' C)).GeneratedOn (SGPT.GAGA.PN.puncture (SGPT.GAGA.PN.ConeSpace N))
      (fun k => SGPT.GAGA.PN.polyTuple (P k)))
    {i : Fin (N + 1)} {x : M} (hx : Ψ x ∈ (affineChart i).source) (g : M → ℂ) :
    (vanishingIdeal (n := n) C).mem x g ↔
      IsInSpanAt (n := n) (· ∈ range fun k => genFun Ψ i (P k)) x g := by
  constructor
  · rintro ⟨hg, hgC⟩
    obtain ⟨-, L0, ε, O, gr, ψ, hε, hO, -, hψ, hψmem, -, hgraph⟩ := exists_affine_graph hΨ x i hx
    set e := (complexChartAt (n := n) x).val with he
    set y₀ := affineChart i (Ψ x) with hy₀
    -- the retraction onto `Ψ(M)`, from the cone
    set ρ : SGPT.GAGA.PN.ConeSpace N → M := fun Z =>
      e.symm (ψ (L0 (affineRatio i (WithLp.ofLp Z))).1) with hρ
    set Z₀ := coneLift Ψ i x with hZ₀
    have hZ₀i : (WithLp.ofLp Z₀) i ≠ 0 := by simp [hZ₀, coneLift]
    have hratio₀ : affineRatio i (WithLp.ofLp Z₀) = y₀ := by
      simp only [hZ₀, coneLift, WithLp.ofLp_toLp]
      exact affineRatio_affineLift i _
    have hR : ∀ᶠ Z in 𝓝 Z₀, (WithLp.ofLp Z) i ≠ 0 :=
      (continuous_apply i |>.comp (PiLp.continuous_ofLp 2 _)).continuousAt.eventually_ne hZ₀i
    have hratio_cont : ContinuousAt (fun Z : SGPT.GAGA.PN.ConeSpace N =>
        affineRatio i (WithLp.ofLp Z)) Z₀ :=
      ((differentiableAt_affineRatio i hZ₀i).comp Z₀
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (N + 1) => ℂ)).differentiableAt).continuousAt
    have hratio_t : Tendsto (fun Z : SGPT.GAGA.PN.ConeSpace N => affineRatio i (WithLp.ofLp Z))
        (𝓝 Z₀) (𝓝 y₀) := by
      have := hratio_cont.tendsto
      simp only [hratio₀] at this
      exact this
    have hball : ∀ᶠ Z in 𝓝 Z₀, affineRatio i (WithLp.ofLp Z) ∈ ball y₀ ε :=
      hratio_t.eventually (isOpen_ball.mem_nhds (mem_ball_self hε))
    -- `x` is the retraction of `Z₀`
    have hx₀ : affinePoint i y₀ = Ψ x := (affineChart i).left_inv hx
    have hgr₀ : (L0 y₀).2 = gr (L0 y₀).1 :=
      ((hgraph y₀ (mem_ball_self hε)).2.1).mp (by rw [hx₀]; exact mem_range_self x)
    obtain ⟨hψt₀, hψΨ₀⟩ := (hgraph y₀ (mem_ball_self hε)).2.2 hgr₀
    have hρ₀ : ρ Z₀ = x := by
      show e.symm (ψ (L0 (affineRatio i (WithLp.ofLp Z₀))).1) = x
      rw [hratio₀]
      exact hΨ.injective (by rw [hψΨ₀, hx₀])
    have hψe : ψ (L0 y₀).1 = e x := by
      have : e.symm (ψ (L0 y₀).1) = x := by rw [← hratio₀]; exact hρ₀
      rw [← this, e.right_inv hψt₀]
    -- the extension `F = g ∘ ρ`
    have hFhol : OkaRelationSheaf.HolAt (fun Z => g (ρ Z)) Z₀ := by
      have hgc : OkaRelationSheaf.HolAt (fun z => g (e.symm z)) (e x) :=
        CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x) hg
      have hO₀ : (L0 y₀).1 ∈ O := (hgraph y₀ (mem_ball_self hε)).1
      have hinner : ∀ᶠ Z in 𝓝 Z₀, DifferentiableAt ℂ
          (fun Z : SGPT.GAGA.PN.ConeSpace N => ψ (L0 (affineRatio i (WithLp.ofLp Z))).1) Z := by
        filter_upwards [hR, hball] with Z hZi hZb
        have h1 : DifferentiableAt ℂ (fun Z : SGPT.GAGA.PN.ConeSpace N =>
            (L0 (affineRatio i (WithLp.ofLp Z))).1) Z :=
          ((ContinuousLinearMap.fst ℂ _ _ ∘L L0.toContinuousLinearMap).differentiableAt).comp Z
            ((differentiableAt_affineRatio i hZi).comp Z
              (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (N + 1) => ℂ)).differentiableAt)
        exact (hψ.differentiableAt (hO.mem_nhds (hgraph _ hZb).1)).comp Z h1
      have hgc' : HolAt (fun z => g (e.symm z)) (ψ (L0 (affineRatio i (WithLp.ofLp Z₀))).1) := by
        rw [hratio₀, hψe]
        exact hgc
      exact SGPT.GAGA.PN.HolAt.comp_of_eventually (f := fun z => g (e.symm z))
        (φ := fun Z : SGPT.GAGA.PN.ConeSpace N => ψ (L0 (affineRatio i (WithLp.ofLp Z))).1)
        hgc' hinner
    have hρcont : ContinuousAt ρ Z₀ := by
      have hO₀ : (L0 y₀).1 ∈ O := (hgraph y₀ (mem_ball_self hε)).1
      have h1 : ContinuousAt (fun Z : SGPT.GAGA.PN.ConeSpace N =>
          ψ (L0 (affineRatio i (WithLp.ofLp Z))).1) Z₀ := by
        refine ContinuousAt.comp (g := ψ) ?_ ((continuous_fst.comp L0.continuous).continuousAt.comp
          hratio_cont)
        show ContinuousAt ψ (L0 (affineRatio i (WithLp.ofLp Z₀))).1
        rw [hratio₀]
        exact (hψ.differentiableAt (hO.mem_nhds hO₀)).continuousAt
      refine ContinuousAt.comp (g := e.symm) ?_ h1
      show ContinuousAt e.symm (ψ (L0 (affineRatio i (WithLp.ofLp Z₀))).1)
      rw [hratio₀]
      exact e.continuousAt_symm hψt₀
    have hFmem : (coneIdeal (Ψ '' C)).mem Z₀ (fun _ Z => g (ρ Z)) := by
      refine ⟨hFhol, ?_⟩
      have hgC' : ∀ᶠ Z in 𝓝 Z₀, ρ Z ∈ C → g (ρ Z) = 0 := by
        have := hρcont.eventually (hρ₀.symm ▸ hgC)
        exact this
      filter_upwards [hR, hball, hgC'] with Z hZi hZb hZC hZcone
      refine hZC ?_
      have hmem := (mem_affineCone_iff hZi).mp hZcone
      obtain ⟨c', hc'C, hc'⟩ := hmem
      obtain ⟨-, hrange, hgr⟩ := hgraph _ hZb
      have hgr' := hrange.mp ⟨c', hc'⟩
      obtain ⟨-, hψΨ⟩ := hgr hgr'
      have : ρ Z = c' := hΨ.injective (by rw [hc']; exact hψΨ)
      rw [this]; exact hc'C
    obtain ⟨c, hc, hcomb⟩ := (hgen.2 Z₀ (coneLift_ne_zero i x) _).mp hFmem
    -- pull back along `Λᵢ`
    have hΛcont : ContinuousAt (coneLift Ψ i) x := by
      have hxs : x ∈ e.source := mem_chart_source _ x
      have h1 := (eventually_differentiableAt_coneLift hΨ hx).self_of_nhds.continuousAt
      have h2 : ContinuousAt (fun x' => (fun z => coneLift Ψ i (e.symm z)) (e x')) x :=
        h1.comp (e.continuousAt hxs)
      refine h2.congr ?_
      filter_upwards [e.open_source.mem_nhds hxs] with x' hx'
      simp only [e.left_inv hx']
    have hback : ∀ᶠ x' in 𝓝 x, ρ (coneLift Ψ i x') = x' := by
      have hU : ∀ᶠ x' in 𝓝 x, Ψ x' ∈ (affineChart i).source :=
        hΨ.continuous.continuousAt.eventually ((affineChart i).open_source.mem_nhds hx)
      have hB : ∀ᶠ x' in 𝓝 x, affineChart i (Ψ x') ∈ ball y₀ ε :=
        ((affineChart i).continuousAt hx).comp hΨ.continuous.continuousAt |>.eventually
          (isOpen_ball.mem_nhds (mem_ball_self hε))
      filter_upwards [hU, hB] with x' hx'U hx'B
      have hrat : affineRatio i (WithLp.ofLp (coneLift Ψ i x')) = affineChart i (Ψ x') := by
        simp [coneLift, affineRatio_affineLift]
      obtain ⟨-, hrange, hgr⟩ := hgraph _ hx'B
      have haff : affinePoint i (affineChart i (Ψ x')) = Ψ x' := (affineChart i).left_inv hx'U
      have hgr' := hrange.mp (by rw [haff]; exact mem_range_self x')
      obtain ⟨-, hψΨ⟩ := hgr hgr'
      show e.symm (ψ (L0 (affineRatio i (WithLp.ofLp (coneLift Ψ i x')))).1) = x'
      rw [hrat]
      exact hΨ.injective (by rw [hψΨ, haff])
    refine (CoherentIdealColon.isInSpanAt_range_iff (S := fun k => genFun Ψ i (P k))).mpr
      ⟨hg, fun k x' => c k (coneLift Ψ i x'), fun k => holomorphicAt_comp_coneLift hΨ hx (hc k),
        ?_⟩
    filter_upwards [hback, hΛcont.eventually (hcomb ())] with x' hx'ρ hx'c
    simp only [hx'ρ] at hx'c
    exact hx'c
  · intro hspan
    obtain ⟨hg, c, hc, hgc⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp hspan
    refine ⟨hg, ?_⟩
    have hU : ∀ᶠ x' in 𝓝 x, Ψ x' ∈ (affineChart i).source :=
      hΨ.continuous.continuousAt.eventually ((affineChart i).open_source.mem_nhds hx)
    filter_upwards [hgc, hU] with x' hx' hx'U hx'C
    rw [hx']
    refine Finset.sum_eq_zero fun k _ => ?_
    have hmem := hgen.gen_mem (coneLift_ne_zero (Ψ := Ψ) i x') k
    have h0 := hmem.2.self_of_nhds (coneLift_mem_affineCone hx'U ⟨x', hx'C, rfl⟩)
    simp only [genFun]
    rw [h0, mul_zero]

end SGPT.GAGA.ChowBl
