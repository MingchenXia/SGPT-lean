import SGPT.Envelopes.DNTC11Main

/-!
# The density formula for `θ_fⁿ`

Lane S53 (`claude-dnt-c11`).  The measure `c11TopMeasure ω θ f` of an obstacle `f` with bounded
complex Hessian is the measure of the density of the distributional complex Hessian:

* `c11TopMeasure_image_eq` (**density formula**): in every chart `e`, for every smooth local
  potential `ρ` of `θ` on `W` and every bounded density `h` of the complex Hessian of
  `f ∘ e⁻¹ + ρ` on `W`, `θ_fⁿ(e⁻¹(K)) = ∫_K max((n!/πⁿ) det h, 0) dV` for measurable `K ⊆ W`.
* `c11TopMeasure_eq_of_isThetaPshPotential`: if `f` is `θ`-psh, `θ_fⁿ` is the non-pluripolar
  Monge–Ampère measure `⟨(θ + ddᶜf)ⁿ⟩`.
* `c11TopMeasure_unique`: a measure on `X` is determined by its chart densities (so the
  definition does not depend on the auxiliary threshold and nodes).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Envelopes.DNTC11

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity
open SGPT.Okounkov.TranscendentalWNReg

variable {n : ℕ}

/-! ### Lagrange interpolation of determinants -/

theorem complex_eval_zero_eq_sum_lagWeight (T : ℝ) {p : Polynomial ℂ} (hp : p.natDegree ≤ n) :
    p.eval 0 = ∑ k : Fin (n + 1), (lagWeight T k : ℂ) * p.eval (lagNode T k : ℂ) := by
  have hinj : Set.InjOn (fun k : Fin (n + 1) => ((lagNode T k : ℝ) : ℂ))
      (Finset.univ : Finset (Fin (n + 1))) := by
    intro a ha b hb hab
    exact lagNode_injOn T ha hb (Complex.ofReal_injective hab)
  have hdeg : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hp)
      (by exact_mod_cast Nat.lt_succ_self n)
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm]
  congr 1
  simp only [lagWeight, Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    Complex.ofReal_prod, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub,
    Complex.ofReal_zero]

/-- `∑_k L_k det(A + t_k B) = det A`. -/
theorem sum_lagWeight_mul_det (T : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∑ k : Fin (n + 1), (lagWeight T k : ℂ) * (A + ((lagNode T k : ℝ) : ℂ) • B).det = A.det := by
  set P : Polynomial ℂ :=
    ((Polynomial.X : Polynomial ℂ) • B.map Polynomial.C + A.map Polynomial.C).det with hP
  have hdeg : P.natDegree ≤ n := by
    have := Polynomial.natDegree_det_X_add_C_le B A
    simpa [Fintype.card_fin] using this
  have heval : ∀ t : ℂ, P.eval t = (A + t • B).det := by
    intro t
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  have h := complex_eval_zero_eq_sum_lagWeight (n := n) T hdeg
  rw [heval, zero_smul, add_zero] at h
  rw [h]
  exact Finset.sum_congr rfl fun k _ => by rw [heval]

/-- `∑_k L_k (n!/πⁿ) Re det(h + t_k H) = (n!/πⁿ) Re det h`. -/
theorem sum_lagWeight_mul_hessDensity (T : ℝ) (h H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ)
    (z : ComplexModel n) :
    ∑ k : Fin (n + 1), lagWeight T k *
        hessDensity (fun y => h y + ((lagNode T k : ℝ) : ℂ) • H y) z = hessDensity h z := by
  have h1 := congrArg Complex.re (sum_lagWeight_mul_det (n := n) T (h z) (H z))
  rw [Complex.re_sum] at h1
  simp only [Complex.re_ofReal_mul] at h1
  simp only [hessDensity, ← h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### Almost everywhere statements on open sets -/

theorem ae_restrict_of_forall_mem_nhds {p : ComplexModel n → Prop} {W : Set (ComplexModel n)}
    (h : ∀ z ∈ W, ∃ N : Set (ComplexModel n), IsOpen N ∧ z ∈ N ∧ ∀ᵐ y ∂volume.restrict N, p y) :
    ∀ᵐ y ∂volume.restrict W, p y := by
  classical
  choose N hNo hzN hN using h
  set S : W → Set (ComplexModel n) := fun z => N z.1 z.2 with hS
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable S fun z => hNo z.1 z.2
  have : Countable T := hTc.to_subtype
  have hWsub : W ⊆ ⋃ i : T, S i := by
    intro z hz
    have : z ∈ ⋃ i, S i := mem_iUnion.mpr ⟨⟨z, hz⟩, hzN z hz⟩
    rw [← hTU] at this
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp this
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  exact ae_restrict_of_ae_restrict_of_subset hWsub
    ((ae_restrict_iUnion_iff _ _).mpr fun i => hN i.1.1 i.1.2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-! ### The non-pluripolar measure is determined by its chart densities -/

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem isLocallyBoundedPshOn_chart {θ : ClosedRealOneOneForm n M} {f : M → ℝ}
    (hfpsh : IsThetaPshPotential θ.val (fun x => (f x : EReal))) {e : ComplexChart n M}
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential θ.val e W ρ)
    (hc : ContinuousOn (fun z => f (e.val.symm z) + ρ z) W) :
    IsLocallyBoundedPshOn ⟨W, hρ.1⟩ (fun z => f (e.val.symm z) + ρ z) := by
  have hpsh := plurisubharmonicOn_chartFunction_add_potential hfpsh.1 hρ
  have hfun : (fun z => chartFunction (fun x => (f x : EReal)) e z + (ρ z : EReal)) =
      fun z => ((f (e.val.symm z) + ρ z : ℝ) : EReal) := by
    funext z
    simp only [chartFunction, EReal.coe_add]
  refine ⟨hfun ▸ hpsh, fun z hz => ?_⟩
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hρ.1 z hz
  have hcb : closedBall z (ε / 2) ⊆ W := (closedBall_subset_ball (by linarith)).trans hεW
  obtain ⟨C, hC⟩ := (isCompact_closedBall z (ε / 2)).exists_bound_of_continuousOn (hc.mono hcb)
  refine ⟨⟨ball z (ε / 2), isOpen_ball⟩, mem_ball_self (by linarith),
    ball_subset_closedBall.trans hcb, C, fun y hy => ?_⟩
  have := hC y (ball_subset_closedBall hy)
  rwa [Real.norm_eq_abs] at this

theorem IsBoundedHessianDensityOn.congr_fun {g g' : ComplexModel n → ℝ}
    {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {U : Set (ComplexModel n)}
    (hg : IsBoundedHessianDensityOn g h U) (heq : g = g') : IsBoundedHessianDensityOn g' h U :=
  heq ▸ hg

/-- **The density formula for `θ_fⁿ`.**  For every chart `e`, every smooth local potential `ρ` of
`θ` on `W ⊆ e.target`, every bounded density `h` of the complex Hessian of `f ∘ e⁻¹ + ρ` on `W` and
every measurable `K ⊆ W`: `θ_fⁿ(e⁻¹(K)) = ∫_K max((n!/πⁿ) Re det h, 0) dV`. -/
theorem c11TopMeasure_image_eq (hn : 0 < n) (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f)
    {e : ComplexChart n M} {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e W ρ) {h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ}
    (hh : IsBoundedHessianDensityOn (fun z => f (e.val.symm z) + ρ z) h W)
    {K : Set (ComplexModel n)} (hK : MeasurableSet K) (hKW : K ⊆ W) :
    c11TopMeasure w θ f (e.val.symm '' K) = ∫⁻ z in K, ENNReal.ofReal (hessDensity h z) := by
  classical
  obtain ⟨hT1, hT⟩ := c11Threshold_spec w θ hf
  set T := c11Threshold w θ f with hTdef
  have hnode : ∀ k : Fin (n + 1), T ≤ lagNode T k := fun k => by
    simp only [lagNode]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℕ))]
  have hfk : ∀ k : Fin (n + 1), IsThetaPshPotential (θ + lagNode T k • w.form).val
      (fun x => (f x : EReal)) := fun k => hT _ (hnode k)
  have hω : ∀ _ : Fin n, ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w = globalMixedMeasure (fun _ : Fin n => w.form) (fun _ _ => 0) hω := rfl
  have hWt : W ⊆ e.val.target := hρ.2.1
  set D : ComplexModel n → ℝ≥0∞ := chartDensity (fun _ : Fin n => w.form) e with hD
  set rn : Fin (n + 1) → M → ℝ≥0∞ := fun k x =>
    (bumpMeasure w θ f (lagNode T k)).rnDeriv (kahlerVolume w) x with hrn
  have hDfin : ∀ z, D z ≠ ⊤ := fun z => ENNReal.ofReal_ne_top
  -- the local identification of the densities
  have hloc : ∀ z₀ ∈ W, ∃ N : Set (ComplexModel n), IsOpen N ∧ z₀ ∈ N ∧
      ∀ᵐ z ∂volume.restrict N, D z * ENNReal.ofReal (c11Ratio w θ f (e.val.symm z)) =
        ENNReal.ofReal (hessDensity h z) := by
    intro z₀ hz₀
    obtain ⟨Wω, ρω, hz₀ω, hρω⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials w.form e z₀ (hWt hz₀)
    have hO : IsOpen (W ∩ Wω) := hρ.1.inter hρω.1
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO z₀ ⟨hz₀, hz₀ω⟩
    set R := ε / 5 with hR
    have hR0 : 0 < R := by positivity
    have hball : closedBall z₀ (4 * R) ⊆ W ∩ Wω := (closedBall_subset_ball (by linarith)).trans hεO
    set B := ball z₀ (2 * R) with hB
    have hBO : B ⊆ W ∩ Wω :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hball
    have hBt : B ⊆ e.val.target := hBO.trans (inter_subset_left.trans hWt)
    refine ⟨B, isOpen_ball, mem_ball_self (by positivity), ?_⟩
    have hρO := hρ.mono hO inter_subset_left
    have hρωO := hρω.mono hO inter_subset_right
    have hhO := hh.mono hO inter_subset_left
    have hωd := isBoundedHessianDensityOn_of_contDiffOn hO hρωO.2.2.1
    set Hk : Fin (n + 1) → ComplexModel n → Matrix (Fin n) (Fin n) ℂ := fun k y =>
      h y + ((lagNode T k : ℝ) : ℂ) • smoothHess (W ∩ Wω) ρω y with hHk
    -- the identification at each node
    have hnodeEq : ∀ k : Fin (n + 1), ∀ᵐ z ∂volume.restrict B,
        D z * rn k (e.val.symm z) = ENNReal.ofReal (hessDensity (Hk k) z) ∧
          0 ≤ hessDensity (Hk k) z := by
      intro k
      set t := lagNode T k with ht
      set ρ' : ComplexModel n → ℝ := fun y => ρ y + t * ρω y with hρ'
      have hρ's : ContDiffOn ℝ ∞ ρ' (W ∩ Wω) :=
        hρO.2.2.1.add ((contDiffOn_const (c := t)).mul hρωO.2.2.1)
      have hpot : IsSmoothLocalPotential (θ + t • w.form).val e (W ∩ Wω) ρ' := by
        refine ⟨hO, inter_subset_left.trans hWt, hρ's, fun z hz => ?_⟩
        have h1 := FirstPass.smoothDDC_add hO hρO.2.2.1
          ((contDiffOn_const (c := t)).mul hρωO.2.2.1) hz
        have h2 := FirstPass.smoothDDC_smul hO hρωO.2.2.1 t hz
        simp only [smul_eq_mul] at h2
        rw [h1, h2, hρO.2.2.2 hz, hρωO.2.2.2 hz, ClosedRealOneOneForm.coeff_add,
          ClosedRealOneOneForm.coeff_smul]
      have hdk : IsBoundedHessianDensityOn (fun z => f (e.val.symm z) + ρ' z) (Hk k) (W ∩ Wω) :=
        (hhO.add (hωd.smul t)).congr_fun (by funext z; simp only [hρ']; ring)
      have hQb := isLocallyBoundedPshOn_chart (hfk k) hpot hdk.continuousOn
      have hnn := ae_hessDensity_nonneg_of_psh hQb hdk hR0 hball
      have hac : bumpMeasure w θ f t ≪ kahlerVolume w := by
        rw [bumpMeasure_eq w θ (hfk k)]
        exact diagonalPotentialMeasure_absolutelyContinuous w _ hf (hfk k)
      have hF1 : AEMeasurable (fun z => D z * rn k (e.val.symm z)) (volume.restrict B) :=
        (((continuousOn_chartDensity _ e).mono hBt).aemeasurable isOpen_ball.measurableSet).mul
          ((Measure.measurable_rnDeriv _ _).comp_aemeasurable
            ((e.val.continuousOn_symm.mono hBt).aemeasurable isOpen_ball.measurableSet))
      have hF2 : AEMeasurable (fun z => ENNReal.ofReal (hessDensity (Hk k) z))
          (volume.restrict B) :=
        (ENNReal.measurable_ofReal.comp (measurable_hessDensity hdk.measurable)).aemeasurable
      have hint : ∀ s, MeasurableSet s → volume.restrict B s < ⊤ →
          ∫⁻ z in s, D z * rn k (e.val.symm z) ∂volume.restrict B =
            ∫⁻ z in s, ENNReal.ofReal (hessDensity (Hk k) z) ∂volume.restrict B := by
        intro s hs _
        rw [Measure.restrict_restrict hs]
        have hsB : s ∩ B ⊆ W ∩ Wω := inter_subset_right.trans hBO
        have hsBt : s ∩ B ⊆ e.val.target := inter_subset_right.trans hBt
        have hsBm : MeasurableSet (s ∩ B) := hs.inter isOpen_ball.measurableSet
        rw [← diagonalPotentialMeasure_image_eq_density hn _ (hfk k) hpot hdk hsB,
          ← bumpMeasure_eq w θ (hfk k), ← Measure.setLIntegral_rnDeriv hac, hvol,
          setLIntegral_image_eq hω e hsBm hsBt (Measure.measurable_rnDeriv _ _)]
        rfl
      have hae := ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hF1 hF2 hint
      filter_upwards [hae, (ae_restrict_iff' isOpen_ball.measurableSet).mpr hnn] with z hz hz'
      exact ⟨hz, hz'⟩
    have hall : ∀ᵐ z ∂volume.restrict B, ∀ k : Fin (n + 1),
        D z * rn k (e.val.symm z) = ENNReal.ofReal (hessDensity (Hk k) z) ∧
          0 ≤ hessDensity (Hk k) z := ae_all_iff.mpr hnodeEq
    filter_upwards [hall, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzB
    have hDpos : 0 < D z := chartDensity_kahler_pos w e (hBt hzB)
    have hDr : 0 < (D z).toReal := ENNReal.toReal_pos hDpos.ne' (hDfin z)
    have hk : ∀ k : Fin (n + 1), (D z).toReal * (rn k (e.val.symm z)).toReal =
        hessDensity (Hk k) z := by
      intro k
      have h1 := congrArg ENNReal.toReal (hz k).1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hz k).2] at h1
    have hsum : (D z).toReal * c11Ratio w θ f (e.val.symm z) = hessDensity h z := by
      rw [← sum_lagWeight_mul_hessDensity T h (smoothHess (W ∩ Wω) ρω) z]
      simp only [c11Ratio, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hTdef, ← hk k]
      ring
    rw [← ENNReal.ofReal_toReal (hDfin z), ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, hsum]
  have hW := ae_restrict_of_forall_mem_nhds hloc
  rw [c11TopMeasure, withDensity_apply', hvol,
    setLIntegral_image_eq hω e hK (hKW.trans hWt) (g := fun x => ENNReal.ofReal (c11Ratio w θ f x))
      (ENNReal.measurable_ofReal.comp (measurable_c11Ratio w θ f))]
  exact setLIntegral_congr_fun_ae hK
    ((ae_restrict_iff' hK).mp (ae_restrict_of_ae_restrict_of_subset hKW hW))


/-! ### Uniqueness and identifications -/

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **Bounded Hessian densities are unique almost everywhere** (both are almost everywhere limits of
the complex Hessians of the same mollifications). -/
theorem IsBoundedHessianDensityOn.ae_eq {g : ComplexModel n → ℝ}
    {h h' : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {U : Set (ComplexModel n)}
    (hg : IsBoundedHessianDensityOn g h U) (hg' : IsBoundedHessianDensityOn g h' U) :
    ∀ᵐ z ∂volume.restrict U, h z = h' z := by
  refine ae_restrict_of_forall_mem_nhds fun z₀ hz₀ => ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hg.isOpen z₀ hz₀
  set R := ε / 5 with hR
  have hR0 : 0 < R := by positivity
  let Ω : Opens (ComplexModel n) := ⟨U, hg.isOpen⟩
  have hball : closedBall z₀ (4 * R) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hεU
  refine ⟨ball z₀ (2 * R), isOpen_ball, mem_ball_self (by positivity), ?_⟩
  have h1 := ae_tendsto_complexHessian_mollified (Ω := Ω) hg hR0 hball
  have h2 := ae_tendsto_complexHessian_mollified (Ω := Ω) hg' hR0 hball
  filter_upwards [ae_restrict_of_ae h1, ae_restrict_of_ae h2,
    ae_restrict_mem isOpen_ball.measurableSet] with z hz1 hz2 hzB
  exact tendsto_nhds_unique (hz1 hzB) (hz2 hzB)

/-- **A measure is determined by its chart densities.**  If `μ` satisfies the density formula of
`c11TopMeasure_image_eq` in every chart, then `μ = θ_fⁿ`.  In particular `θ_fⁿ` does not depend on
the Kähler form `ω`, the threshold or the interpolation nodes used to construct it. -/
theorem eq_c11TopMeasure_of_image_eq (hn : 0 < n) (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f)
    (μ : Measure M)
    (hμ : ∀ (e : ComplexChart n M) (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ)
      (h : ComplexModel n → Matrix (Fin n) (Fin n) ℂ), IsSmoothLocalPotential θ.val e W ρ →
      IsBoundedHessianDensityOn (fun z => f (e.val.symm z) + ρ z) h W →
      ∀ K, MeasurableSet K → K ⊆ W →
        μ (e.val.symm '' K) = ∫⁻ z in K, ENNReal.ofReal (hessDensity h z)) :
    μ = c11TopMeasure w θ f := by
  classical
  -- the patches `e⁻¹(W)` with a local potential
  have hpatch : ∀ x : M, ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ μ.restrict N = (c11TopMeasure w θ f).restrict N := by
    intro x
    set e := complexChartAt (n := n) x with he
    have hxe : x ∈ e.val.source := mem_complexChartAt_source x
    have hz₀ : e.val x ∈ e.val.target := e.val.map_source hxe
    obtain ⟨W, ρ, hz₀W, hρ⟩ :=
      Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ e (e.val x) hz₀
    obtain ⟨h, hh⟩ := hf.exists_density_add e hρ.1 hρ.2.1 hρ.2.2.1
    set N := e.val.source ∩ e.val ⁻¹' W with hN
    refine ⟨N, e.val.isOpen_inter_preimage hρ.1, ⟨hxe, hz₀W⟩, ?_⟩
    ext S hS
    rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
    have hSN : S ∩ N ⊆ e.val.source := fun y hy => hy.2.1
    set K := e.val '' (S ∩ N) with hK
    have hKm : MeasurableSet K := by
      rw [hK, e.val.image_eq_target_inter_inv_preimage hSN]
      exact measurableSet_inter_preimage_of_continuousOn e.val.open_target.measurableSet
        e.val.continuousOn_symm (hS.inter (e.val.isOpen_inter_preimage hρ.1).measurableSet)
    have hKW : K ⊆ W := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy.2.2
    have hSK : S ∩ N = e.val.symm '' K := (e.val.symm_image_image_of_subset_source hSN).symm
    rw [hSK, hμ e W ρ h hρ hh K hKm hKW, c11TopMeasure_image_eq hn w θ hf hρ hh hKm hKW]
  choose N hNo hxN hN using hpatch
  exact GlobalSlotStokes.measure_eq_of_restrict_eq_of_openCover (fun x => N x) hNo
    (fun x => ⟨x, hxN x⟩) hN

/-- **For a `θ`-psh obstacle, `θ_fⁿ` is the non-pluripolar Monge–Ampère measure.** -/
theorem c11TopMeasure_eq_of_isThetaPshPotential (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : HasBoundedComplexHessian (n := n) f)
    (hfpsh : IsThetaPshPotential θ.val (fun x => (f x : EReal))) :
    c11TopMeasure w θ f = diagonalPotentialMeasure θ (fun x => (f x : EReal)) hfpsh := by
  have h := diagonalPotentialMeasure_restrict_contact_eq w θ hfpsh hf (fun _ => le_rfl)
  have huniv : {x : M | (f x : EReal) = (f x : EReal)} = univ := by ext; simp
  rw [huniv, Measure.restrict_univ, Measure.restrict_univ] at h
  exact h.symm

/-- **For a smooth obstacle, `θ_fⁿ` is the measure `max((θ + ddᶜf)ⁿ/ωⁿ, 0) ωⁿ` of the smooth top
form** (`positiveTopMeasure`, the right-hand side of the and WN-REG2's smooth contact
formulas). -/
theorem c11TopMeasure_eq_positiveTopMeasure (hn : 0 < n) (w : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {f : M → ℝ} (hf : ChartSmooth (n := n) f) :
    c11TopMeasure w θ f = positiveTopMeasure w (θ + ddcClosedForm f hf) := by
  refine (eq_c11TopMeasure_of_image_eq hn w θ (HasBoundedComplexHessian.of_chartSmooth hf) _
    fun e W ρ h hρ hh K hK hKW => ?_).symm
  have hq : ContDiffOn ℝ ∞ (fun z => f (e.val.symm z) + ρ z) W :=
    ((hf e).mono hρ.2.1).add hρ.2.2.1
  have hsm := isBoundedHessianDensityOn_of_contDiffOn hρ.1 hq
  have hae := hh.ae_eq hsm
  rw [SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure_eq_topFormMeasure,
    SGPT.Okounkov.TranscendentalWN.topFormMeasure_image_eq w _ e hK (hKW.trans hρ.2.1)]
  refine setLIntegral_congr_fun_ae hK ?_
  filter_upwards [(ae_restrict_iff' hρ.1.measurableSet).mp hae] with z hz hzK
  have hzW := hKW hzK
  have h1 : hessDensity h z = hessDensity (smoothHess W fun z => f (e.val.symm z) + ρ z) z := by
    simp only [hessDensity, hz hzW]
  have h2 : hessDensity (smoothHess W fun z => f (e.val.symm z) + ρ z) z =
      smoothDensity (fun z => f (e.val.symm z) + ρ z) z := by
    unfold hessDensity smoothDensity
    simp only [smoothHess, hzW, if_true]
  rw [h1, h2, SGPT.Okounkov.TranscendentalWN.smoothDensity_eq_topDensity_formPow θ hf hρ hzW]


/-! ### Comparison with WN-REG's `IsCOneOneBar` -/

omit [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A function with bounded complex Hessian is `C^{1,1̄}` in the sense of WN-REG's `IsCOneOneBar`
(the distributional complex Hessian is locally bounded, without a chosen density). -/
theorem HasBoundedComplexHessian.isCOneOneBar {f : M → ℝ}
    (hf : HasBoundedComplexHessian (n := n) f) : IsCOneOneBar (N := n) f := by
  refine ⟨hf.1, fun e K hK hKt => ?_⟩
  obtain ⟨h, hh⟩ := hf.2 e
  obtain ⟨C, hC0, hC⟩ := hh.exists_ae_abs_hermQuad_le hK hKt
  refine ⟨C, fun φ hφ hφK v => ?_⟩
  have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport φ) hφK
  rw [hh.levi φ hφ hφc (hφK.trans hKt) v]
  have hC' : ∀ᵐ z, z ∈ K → ∀ v, |hermQuad (h z) v| ≤ C * ‖v‖ ^ 2 :=
    (ae_restrict_iff' hK.measurableSet).mp hC
  have hbound : ∀ᵐ z, ‖hermQuad (h z) v * φ z‖ ≤ C * ‖v‖ ^ 2 * |φ z| := by
    filter_upwards [hC'] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hzK : z ∈ K
    · exact mul_le_mul_of_nonneg_right (hz hzK v) (abs_nonneg _)
    · have h0 : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hzK (hφK h')
      simp [h0]
  calc |∫ z, hermQuad (h z) v * φ z| = ‖∫ z, hermQuad (h z) v * φ z‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, C * ‖v‖ ^ 2 * |φ z| :=
        norm_integral_le_of_norm_le ((hφ.continuous.abs.integrable_of_hasCompactSupport
          hφc.abs).const_mul _) hbound
    _ = C * ‖v‖ ^ 2 * ∫ z, |φ z| := integral_const_mul _ _

end SGPT.Envelopes.DNTC11
