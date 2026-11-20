import SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceLocal
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

/-!
# Curve selection through singular points of embedded analytic sets

Let `Ω ⊆ ℂ^N` be open, `C ⊆ Ω` a closed analytic subset and `A ⊆ Ω` an analytic subset such
that `A ∩ C` has empty interior in `C`. Through every point `c ∈ C` there is a holomorphic disc
`G : Δ → C` with `G(0) = c` and `G(t) ∉ A` for `t ≠ 0` (`exists_avoiding_disc`).

This is the curve selection used in the uniqueness part of the Grauert--Remmert extension theorem
(source `thm:GRexten2`, Appendix B, `appendix_unibranch.tex`): "take `z ∈ Z` and a holomorphic map
`f : Δ → X` such that `f(0) = z` and `f(Δ) ⊄ Z`". At a singular point of `C` no straight disc of
`ℂ^N` need lie in `C`; we use the local resolution of singularities
(`HironakaResolutionSpaceLocal.exists_isStrictTransformResolution_local`, G11): the strict
transform `C'` of `C ∩ B` (`B` a small ball) is a closed submanifold of the blown-up manifold, it
maps onto `C ∩ B`, and the blow-up is an isomorphism over the regular part. We take a point `c'`
of `C'` over `c`, a submanifold chart of `C'` at `c'`, and a straight disc in that chart: since the
preimage of `A` is nowhere dense in `C'` (this uses that the blow-up is a closed map which is
bijective over the regular part, and that the regular part is dense), some local equation of `A`
does not vanish identically along some line of the chart, and by the isolated zeros theorem it
vanishes only at the centre on a small disc of that line.

Lane PD, blueprint `pd.tex`.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.PDCurveSelection

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.HironakaResolutionSpace
open SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceLocal
open SGPT.Foundations.Analysis.Pending.HironakaEmbeddedAnalytic (singularSet isClosed_singularSet)

noncomputable section

theorem norm_complexModel_one (z : ComplexModel 1) : ‖z‖ = ‖z 0‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]

theorem smul_mem_complexCoordinatePlane {N k : ℕ} {p : ComplexModel N}
    (hp : p ∈ complexCoordinatePlane N k) (t : ℂ) : t • p ∈ complexCoordinatePlane N k := by
  intro i hi
  simp [hp i hi]

/-- **Curve selection.** Let `C` and `A` be analytic subsets of an open set `Ω ⊆ ℂ^N`, `C` closed,
and let `c` be a point of the closure of `C \ A`. There is a holomorphic disc `G : Δ → C`
(`Δ` the unit disc of `ℂ^1`) with `G(0) = c` and `G(t) ∉ A` for every `t ≠ 0`. -/
theorem exists_avoiding_disc_of_mem_closure {N : ℕ} {Ω : Opens (ComplexModel N)} {C A : Set Ω}
    (hC : IsComplexAnalyticSubset (n := N) C) (hA : IsComplexAnalyticSubset (n := N) A)
    {c : Ω} (hcl : c ∈ closure (C \ A)) :
    ∃ G : ComplexModel 1 → ComplexModel N,
      ContDiffOn ℂ ∞ G (ball 0 1) ∧ G 0 = (c : ComplexModel N) ∧
      (∀ z ∈ ball (0 : ComplexModel 1) 1, ∃ y ∈ C, (y : ComplexModel N) = G z) ∧
      (∀ z ∈ ball (0 : ComplexModel 1) 1, z ≠ 0 →
        ∀ y : Ω, (y : ComplexModel N) = G z → y ∉ A) := by
  classical
  /- A relatively compact ball around `c` inside `Ω`. -/
  obtain ⟨ρ₀, hρ₀, hρ₀Ω⟩ : ∃ ρ₀ > 0, closedBall (c : ComplexModel N) ρ₀ ⊆ Ω := by
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen c c.property
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεΩ⟩
  let X₀ : Opens Ω := ⟨(Subtype.val : Ω → ComplexModel N) ⁻¹' ball (c : ComplexModel N) ρ₀,
    isOpen_ball.preimage continuous_subtype_val⟩
  let K : Set Ω := (Subtype.val : Ω → ComplexModel N) ⁻¹' closedBall (c : ComplexModel N) ρ₀
  have hK : IsCompact K := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    have himg : (Subtype.val : Ω → ComplexModel N) '' K = closedBall (c : ComplexModel N) ρ₀ := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hq
      · intro hy
        exact ⟨⟨y, hρ₀Ω hy⟩, hy, rfl⟩
    rw [himg]
    exact isCompact_closedBall _ _
  have hX₀K : (X₀ : Set Ω) ⊆ K := fun y hy => ball_subset_closedBall hy
  /- The local resolution of `C ∩ X₀`. -/
  obtain ⟨X₀', _, _, _, σ, E, hσp, hres⟩ :=
    exists_isStrictTransformResolution_local (n := N) hC X₀ hK hX₀K
  set W₀ : Set X₀ := (Subtype.val : X₀ → Ω) ⁻¹' C with hW₀
  set W' : Set X₀' := strictTransform N σ W₀ with hW'
  set A₀ : Set X₀ := (Subtype.val : X₀ → Ω) ⁻¹' A with hA₀
  let c₀ : X₀ := ⟨c, mem_ball_self hρ₀⟩
  /- A point `w'` of the strict transform over `c` which is a limit of points not over `A`. -/
  obtain ⟨w', hw'cl, hσw'⟩ : c₀ ∈ σ '' closure (W' \ σ ⁻¹' A₀) := by
    by_contra hno
    have hT : IsClosed (σ '' closure (W' \ σ ⁻¹' A₀)) := hσp.isClosedMap _ isClosed_closure
    let U : Set X₀ := (σ '' closure (W' \ σ ⁻¹' A₀))ᶜ
    have hUA : U ∩ W₀ ⊆ A₀ := by
      rintro x ⟨hxU, hxW⟩
      by_contra hxA
      have hxim : x ∈ σ '' W' := by
        rw [hW', hres.image_eq]
        exact hxW
      obtain ⟨w, hw, rfl⟩ := hxim
      exact hxU ⟨w, subset_closure ⟨hw, hxA⟩, rfl⟩
    let O : Set Ω := Subtype.val '' U
    have hO : IsOpen O := X₀.isOpen.isOpenMap_subtype_val _ hT.isOpen_compl
    have hcO : c ∈ O := ⟨c₀, hno, rfl⟩
    obtain ⟨y, hyO, hyC, hyA⟩ := mem_closure_iff.mp hcl O hO hcO
    obtain ⟨x, hxU, rfl⟩ := hyO
    exact hyA (hUA ⟨hxU, hyC⟩)
  have hw' : w' ∈ W' :=
    closure_minimal sdiff_subset hres.isClosed_strictTransform hw'cl
  /- A submanifold chart of the strict transform at `w'`. -/
  obtain ⟨k, hkreg⟩ := hres.isClosedSubmanifold.2 w' hw'
  obtain ⟨-, -, Φ, hΦsrc, hΦ0, hiff⟩ := hkreg
  let φ' := (complexChartAt (n := N) w').val
  have hΦ0' : Φ.toFun (φ' w') = 0 := hΦ0
  have hctr : φ' w' ∈ Φ.source := Φ.center_mem_source
  have hw'src : w' ∈ φ'.source := mem_complexChartAt_source (n := N) w'
  /- The holomorphic parametrization `Ψ` of `C` near `c` through the chart. -/
  let Ψ : ComplexModel N → ComplexModel N :=
    fun p => ((σ (φ'.symm (Φ.invFun p)) : Ω) : ComplexModel N)
  have hΨ : ContDiffOn ℂ ∞ Ψ Φ.target := by
    have h1 : ContMDiffOn 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ Φ.invFun Φ.target :=
      contMDiffOn_iff_contDiffOn.mpr
        (contDiffOn_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target)
    have h2 : ContMDiffOn 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞ φ'.symm φ'.target :=
      contMDiffOn_chart_symm
    have h3 : ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞
        (fun y : X₀' => ((σ y : Ω) : ComplexModel N)) :=
      (contMDiff_subtype_val.comp contMDiff_subtype_val).comp hres.contMDiff
    have h123 := (h3.comp_contMDiffOn h2).comp h1 (fun p hp => hΦsrc (Φ.mapsTo_invFun hp))
    exact contMDiffOn_iff_contDiffOn.mp h123
  have hΦinv0 : Φ.invFun 0 = φ' w' := by
    rw [← hΦ0']
    exact Φ.left_inv _ hctr
  have hΨ0 : Ψ 0 = (c : ComplexModel N) := by
    change ((σ (φ'.symm (Φ.invFun 0)) : Ω) : ComplexModel N) = (c : ComplexModel N)
    rw [hΦinv0, φ'.left_inv hw'src, hσw']
  have h0T : (0 : ComplexModel N) ∈ Φ.target := by
    rw [← hΦ0']
    exact Φ.mapsTo_toFun hctr
  /- Local equations of `A` at `c`; the preferred chart of `Ω` is the identity. -/
  obtain ⟨pA⟩ := hA c
  set U_A := pA.coordinateNeighborhood with hU_A
  set g := pA.generator with hg
  have hchart : ∀ y : Ω, (complexChartAt (n := N) c).val y = (y : ComplexModel N) := fun y => rfl
  have hsrcA : ∀ y : Ω, y ∈ (complexChartAt (n := N) c).val.source := by
    intro y
    show y ∈ ((chartAt (ComplexModel N) (c : ComplexModel N)).subtypeRestr ⟨c⟩).source
    rw [OpenPartialHomeomorph.subtypeRestr_source, chartAt_self_eq]
    simp
  have hzero : ∀ y : Ω, (y : ComplexModel N) ∈ U_A → (y ∈ A ↔ ∀ i, g i y = 0) := by
    intro y hy
    have h := pA.zeroLocus (hsrcA y) (by rw [hchart]; exact hy)
    simpa only [hchart] using h
  have hcU : (c : ComplexModel N) ∈ U_A := by
    have h := pA.center_mem_coordinateNeighborhood
    rwa [hchart] at h
  /- A ball `B(0, ρ)` in chart coordinates on which everything is defined. -/
  have hT : IsOpen (Φ.target ∩ Ψ ⁻¹' U_A) :=
    hΨ.continuousOn.isOpen_inter_preimage Φ.isOpen_target pA.isOpen_coordinateNeighborhood
  obtain ⟨ρ, hρ, hρT⟩ := Metric.isOpen_iff.mp hT 0 ⟨h0T, by
    change Ψ 0 ∈ U_A
    rw [hΨ0]
    exact hcU⟩
  have hplane_mem : ∀ p ∈ ball (0 : ComplexModel N) ρ, p ∈ complexCoordinatePlane N k →
      φ'.symm (Φ.invFun p) ∈ W' := by
    intro p hp hpl
    have hpT : p ∈ Φ.target := (hρT hp).1
    have hinvS : Φ.invFun p ∈ Φ.source := Φ.mapsTo_invFun hpT
    have hsrc' : φ'.symm (Φ.invFun p) ∈ φ'.source := φ'.map_target (hΦsrc hinvS)
    have hφφ : φ' (φ'.symm (Φ.invFun p)) = Φ.invFun p := φ'.right_inv (hΦsrc hinvS)
    have h2 : φ' (φ'.symm (Φ.invFun p)) ∈ Φ.source := by
      rw [hφφ]
      exact hinvS
    refine (hiff hsrc' h2).mpr ?_
    show Φ.toFun (φ' (φ'.symm (Φ.invFun p))) ∈ complexCoordinatePlane N k
    rw [hφφ, Φ.right_inv p hpT]
    exact hpl
  /- Some point of the chart plane is sent off `A`, since `w'` is a limit of points of the strict
  transform not over `A`. -/
  have hex : ∃ p ∈ ball (0 : ComplexModel N) ρ, p ∈ complexCoordinatePlane N k ∧
      ∃ i, g i (Ψ p) ≠ 0 := by
    let Sx : Set X₀' := φ'.source ∩ φ' ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' ball 0 ρ)
    have hΦc : ContinuousOn Φ.toFun Φ.source :=
      Φ.toFun_holomorphic.continuousOn
    have hO1 : IsOpen (Φ.source ∩ Φ.toFun ⁻¹' ball (0 : ComplexModel N) ρ) :=
      hΦc.isOpen_inter_preimage Φ.isOpen_source isOpen_ball
    have hSx : IsOpen Sx := φ'.isOpen_inter_preimage hO1
    have hw'B : Φ.toFun (φ' w') ∈ ball (0 : ComplexModel N) ρ := by
      rw [hΦ0']
      exact mem_ball_self hρ
    have hw'Sx : w' ∈ Sx := by
      refine ⟨hw'src, ?_⟩
      show φ' w' ∈ Φ.source ∩ Φ.toFun ⁻¹' ball (0 : ComplexModel N) ρ
      exact ⟨hctr, hw'B⟩
    obtain ⟨y, ⟨hys, hyΦ, hyB⟩, hyW, hyA⟩ := mem_closure_iff.mp hw'cl Sx hSx hw'Sx
    have hpl : Φ.toFun (φ' y) ∈ complexCoordinatePlane N k := (hiff hys hyΦ).mp hyW
    have hinv : φ'.symm (Φ.invFun (Φ.toFun (φ' y))) = y := by
      rw [Φ.left_inv _ hyΦ]
      exact φ'.left_inv hys
    have hΨp : Ψ (Φ.toFun (φ' y)) = ((σ y : Ω) : ComplexModel N) := by
      change ((σ (φ'.symm (Φ.invFun (Φ.toFun (φ' y)))) : Ω) : ComplexModel N) = _
      rw [hinv]
    have hU : ((σ y : Ω) : ComplexModel N) ∈ U_A := by
      rw [← hΨp]
      exact (hρT hyB).2
    refine ⟨Φ.toFun (φ' y), hyB, hpl, ?_⟩
    by_contra hall
    push Not at hall
    apply hyA
    change (σ y : Ω) ∈ A
    rw [hzero _ hU]
    intro i
    rw [← hΨp]
    exact hall i
  /- The line through `0` and `p` in the chart plane. -/
  obtain ⟨p, hp, hpl, i, hpi⟩ := hex
  let h : ℂ → ℂ := fun t => g i (Ψ (t • p))
  let D : Set ℂ := (fun t : ℂ => t • p) ⁻¹' ball (0 : ComplexModel N) ρ
  have hDopen : IsOpen D := isOpen_ball.preimage (continuous_id.smul continuous_const)
  have hDconv : Convex ℝ D := by
    let f : ℂ →ₗ[ℝ] ComplexModel N :=
      ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight p).restrictScalars ℝ
    exact (convex_ball (0 : ComplexModel N) ρ).linear_preimage f
  have h0D : (0 : ℂ) ∈ D := by
    change (0 : ℂ) • p ∈ ball (0 : ComplexModel N) ρ
    rw [zero_smul]
    exact mem_ball_self hρ
  have h1D : (1 : ℂ) ∈ D := by
    change (1 : ℂ) • p ∈ ball (0 : ComplexModel N) ρ
    rw [one_smul]
    exact hp
  have hΨball : DifferentiableOn ℂ Ψ (ball (0 : ComplexModel N) ρ) :=
    (hΨ.differentiableOn (by simp)).mono fun q hq => (hρT hq).1
  have hdiff : DifferentiableOn ℂ h D :=
    ((pA.generator_holomorphic i).comp hΨball fun q hq => (hρT hq).2).comp
      (differentiableOn_id.smul_const p) fun t ht => ht
  have hhol : AnalyticOnNhd ℂ h D := hdiff.analyticOnNhd hDopen
  have hnot : ¬ (∀ᶠ t in 𝓝 (0 : ℂ), h t = 0) := by
    intro hev
    have hzeroD := hhol.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDconv.isPreconnected h0D
      hev h1D
    apply hpi
    simpa [h] using hzeroD
  obtain ⟨r, hr, hrball⟩ : ∃ r > 0, ∀ t : ℂ, t ∈ ball (0 : ℂ) r → t ≠ 0 → h t ≠ 0 := by
    rcases (hhol 0 h0D).eventually_eq_zero_or_eventually_ne_zero with hev | hev
    · exact absurd hev hnot
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
    exact ⟨r, hr, fun t ht htne => hball ht htne⟩
  /- The disc. -/
  set r' : ℝ := min r 1 / 2 with hr'
  have hr'pos : 0 < r' := by
    rw [hr']
    exact div_pos (lt_min hr one_pos) two_pos
  have hr'1 : r' < 1 := by
    have := min_le_right r 1
    rw [hr']
    linarith
  have hr'r : r' < r := by
    have := min_le_left r 1
    rw [hr']
    linarith
  let L : ComplexModel 1 → ℂ := fun z => (r' : ℂ) * z 0
  have hLnorm : ∀ z ∈ ball (0 : ComplexModel 1) 1, ‖L z‖ < r' := by
    intro z hz
    have hz' : ‖z 0‖ < 1 := by
      rw [← norm_complexModel_one]
      exact mem_ball_zero_iff.mp hz
    change ‖(r' : ℂ) * z 0‖ < r'
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr'pos.le]
    nlinarith [norm_nonneg (z 0)]
  have hLball : ∀ z ∈ ball (0 : ComplexModel 1) 1, L z • p ∈ ball (0 : ComplexModel N) ρ := by
    intro z hz
    have hpn : ‖p‖ < ρ := mem_ball_zero_iff.mp hp
    rw [mem_ball_zero_iff, norm_smul]
    have hL1 : ‖L z‖ ≤ 1 := (hLnorm z hz).le.trans hr'1.le
    nlinarith [norm_nonneg (L z), norm_nonneg p]
  let G : ComplexModel 1 → ComplexModel N := fun z => Ψ (L z • p)
  have hLc : ContDiff ℂ ∞ (fun z : ComplexModel 1 => L z • p) := by
    have hproj : ContDiff ℂ ∞ (fun z : ComplexModel 1 => z 0) :=
      (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contDiff
    exact (contDiff_const.mul hproj).smul contDiff_const
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · exact hΨ.comp hLc.contDiffOn fun z hz => (hρT (hLball z hz)).1
  · change Ψ (L 0 • p) = (c : ComplexModel N)
    have hL0 : L 0 = 0 := by simp [L]
    rw [hL0, zero_smul, hΨ0]
  · intro z hz
    refine ⟨(σ (φ'.symm (Φ.invFun (L z • p))) : Ω), ?_, rfl⟩
    exact hres.strictTransform_subset_preimage
      (hplane_mem _ (hLball z hz) (smul_mem_complexCoordinatePlane hpl _))
  · intro z hz hz0 y hy hyA
    have hz0' : z 0 ≠ 0 := by
      intro h0
      apply hz0
      rw [← norm_eq_zero, norm_complexModel_one, h0, norm_zero]
    have hLne : L z ≠ 0 := mul_ne_zero (by exact_mod_cast hr'pos.ne') hz0'
    have hLr : L z ∈ ball (0 : ℂ) r :=
      mem_ball_zero_iff.mpr ((hLnorm z hz).trans hr'r)
    have hU : (y : ComplexModel N) ∈ U_A := by
      rw [hy]
      exact (hρT (hLball z hz)).2
    have hall := (hzero y hU).mp hyA i
    rw [hy] at hall
    exact hrball (L z) hLr hLne hall

/-- **Curve selection**, global form: if `A` contains no nonempty relatively open subset of the
closed analytic set `C`, then through every point `c ∈ C` there is a holomorphic disc
`G : Δ → C` with `G(0) = c` and `G(t) ∉ A` for `t ≠ 0`. -/
theorem exists_avoiding_disc {N : ℕ} {Ω : Opens (ComplexModel N)} {C A : Set Ω}
    (hC : IsComplexAnalyticSubset (n := N) C) (hA : IsComplexAnalyticSubset (n := N) A)
    (hthin : ∀ O : Set Ω, IsOpen O → O ∩ C ⊆ A → O ∩ C = ∅)
    {c : Ω} (hc : c ∈ C) :
    ∃ G : ComplexModel 1 → ComplexModel N,
      ContDiffOn ℂ ∞ G (ball 0 1) ∧ G 0 = (c : ComplexModel N) ∧
      (∀ z ∈ ball (0 : ComplexModel 1) 1, ∃ y ∈ C, (y : ComplexModel N) = G z) ∧
      (∀ z ∈ ball (0 : ComplexModel 1) 1, z ≠ 0 →
        ∀ y : Ω, (y : ComplexModel N) = G z → y ∉ A) := by
  refine exists_avoiding_disc_of_mem_closure hC hA ?_
  rw [_root_.mem_closure_iff]
  intro O hO hcO
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hOC : O ∩ C ⊆ A := by
    intro y hy
    by_contra hyA
    have : y ∈ O ∩ (C \ A) := ⟨hy.1, hy.2, hyA⟩
    rw [hne] at this
    exact this
  have h := hthin O hO hOC
  have : c ∈ O ∩ C := ⟨hcO, hc⟩
  rw [h] at this
  exact this

end

end SGPT.Unibranch.PDCurveSelection
