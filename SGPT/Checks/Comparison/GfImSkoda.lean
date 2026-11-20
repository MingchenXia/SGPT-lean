import SGPT.Okounkov.TranscendentalSkodaManifold
import SGPT.NAPotential.GAGAMultSiuGerms

/-!
# Multiplier ideals of analytic singularities: the two inclusions used for `lma:gfinimage`

Infrastructure for `lma:gfinimage` (`chapter_NApotential.tex`, *The comparison theorem*). For a
quasi-psh `φ` on a complex manifold of dimension `n > 0` with analytic singularities
`φ = log ∑ᵢ |gᵢ|² + R` near `y` (`R` bounded), and `J = (g₁, …, g_r)`:

* `prod_mem_multiplierIdeal` (the easy inclusion `J^j ⊆ 𝓘(jφ)`): every product of `j ≥ 1`
  generators lies in `𝓘(jφ)_y` (its weighted density `|∏ g|² e^{-j log ∑|g|²}` is bounded by `1`).
* the reverse inclusion `𝓘((j + n)φ)_y ⊆ J^j` is Skoda's theorem
  (`SGPT.Okounkov.TranscendentalSkoda.manifoldSkodaStatement`), used in `GfImSections`.
* `pow_span_le_of_prod_mem`: an ideal containing all `j`-fold products of the generators of
  `span G` contains `(span G)^j`.

Together these give `v(𝓘(cφ)) = c · v(J) + O(1)` at every point `v` of `X^An` (no divisorial or
Briançon–Skoda/integral-closure theory is needed beyond Skoda's division theorem).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJ.GfIm

open Filter Set MeasureTheory Metric
open scoped Topology Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.Okounkov.TranscendentalSkoda

/-! ### Ideals containing all products of generators -/

/-- If an ideal contains every `j`-fold product of the elements `G k`, it contains
`(span G)^j`. -/
theorem pow_span_le_of_prod_mem {R : Type*} [CommRing R] {ι : Type*} (G : ι → R) :
    ∀ (j : ℕ) (I : Ideal R), (∀ β : Fin j → ι, ∏ l, G (β l) ∈ I) →
      Ideal.span (Set.range G) ^ j ≤ I := by
  intro j
  induction j with
  | zero =>
    intro I h
    have h1 : (1 : R) ∈ I := by simpa using h Fin.elim0
    rw [(Ideal.eq_top_iff_one I).mpr h1]
    exact le_top
  | succ j ih =>
    intro I h
    rw [pow_succ]
    refine Ideal.mul_le.mpr fun a ha b hb => ?_
    refine Submodule.span_induction (p := fun b _ => a * b ∈ I) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨k, rfl⟩
      have hk : Ideal.span (Set.range G) ^ j ≤ I.colon {G k} := by
        refine ih _ fun β => ?_
        rw [Submodule.mem_colon_singleton, smul_eq_mul]
        have := h (Fin.snoc β k)
        rw [Fin.prod_univ_castSucc, Fin.snoc_last] at this
        simpa only [Fin.snoc_castSucc] using this
      have := Submodule.mem_colon_singleton.mp (hk ha)
      simpa [smul_eq_mul] using this
    · simp
    · intro b₁ b₂ _ _ h₁ h₂
      rw [mul_add]
      exact I.add_mem h₁ h₂
    · intro c b _ hb'
      rw [smul_eq_mul, mul_left_comm]
      exact I.mul_mem_left c hb'

/-! ### Bounded weighted densities -/

/-- A holomorphic function with bounded weighted density `|F|² e^{-c log ∑ |G|²}` near `x` lies in
the multiplier ideal at `x`. -/
theorem multiplierIntegrableAt_of_bounded_density {n r : ℕ} {G : Fin r → ComplexModel n → ℂ}
    {x : ComplexModel n} (hG : HolomorphicGeneratorsAt G x) {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ F z) {c : ℝ} (hc : 0 < c) {K : ℝ≥0∞} (hK : K < ⊤)
    (hbound : ∀ᶠ z in 𝓝 x, multiplierDensity (generatorLog G) c F z ≤ K) :
    MultiplierIntegrableAt (generatorLog G) c F x volume := by
  obtain ⟨V, hV, hxV, hGV⟩ := hG
  have hev : ∀ᶠ z in 𝓝 x, z ∈ V ∧ DifferentiableAt ℂ F z ∧
      multiplierDensity (generatorLog G) c F z ≤ K := by
    filter_upwards [hV.mem_nhds hxV, hF, hbound] with z hzV hzF hzb
    exact ⟨hzV, hzF, hzb⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hFV : DifferentiableOn ℂ F (ball x ε) := fun y hy =>
    (hball y hy).2.1.differentiableWithinAt
  refine ⟨hc, ball x ε, isOpen_ball, mem_ball_self hε, hFV,
    aemeasurable_multiplierDensity_generatorLog isOpen_ball
      (fun i => (hGV i).continuousOn.mono (fun y hy => (hball y hy).1)) hc.ne' hFV.continuousOn, ?_⟩
  calc (∫⁻ y in ball x ε, multiplierDensity (generatorLog G) c F y)
      ≤ ∫⁻ _y in ball x ε, K :=
        setLIntegral_mono' measurableSet_ball (fun y hy => (hball y hy).2.2)
    _ = K * volume (ball x ε) := by rw [setLIntegral_const, mul_comm]
    _ < ⊤ := ENNReal.mul_lt_top hK measure_ball_lt_top

/-- `|∏ₗ G_{β l}|² e^{-j log ∑ₖ |G_k|²} ≤ 1` for `j ≥ 1`. -/
theorem multiplierDensity_prod_le_one {E : Type*} {r j : ℕ} (hj : 0 < j) (G : Fin r → E → ℂ)
    (β : Fin j → Fin r) (z : E) :
    multiplierDensity (generatorLog G) (j : ℝ) (fun w => ∏ l, G (β l) w) z ≤ 1 := by
  set S : ℝ := ∑ k, ‖G k z‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by positivity
  have hle : ∀ k, ‖G k z‖ ^ 2 ≤ S := fun k =>
    Finset.single_le_sum (f := fun k => ‖G k z‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ k)
  have hprod : ‖∏ l, G (β l) z‖ ^ 2 ≤ S ^ j := by
    rw [norm_prod, ← Finset.prod_pow]
    calc ∏ l, ‖G (β l) z‖ ^ 2 ≤ ∏ _l : Fin j, S :=
          Finset.prod_le_prod (fun l _ => by positivity) (fun l _ => hle (β l))
      _ = S ^ j := by simp
  unfold multiplierDensity
  rw [generatorLog_eq_log_sum]
  rcases hS0.lt_or_eq with hpos | hzero
  · rw [← hS, ENNReal.log_ofReal_of_pos hpos, multiplierWeight_coe, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_one.mpr ?_
    have hexp : Real.exp (-((j : ℝ) * Real.log S)) * S ^ j = 1 := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hpos, ← Real.exp_add]
      simp [mul_comm]
    calc ‖∏ l, G (β l) z‖ ^ 2 * Real.exp (-((j : ℝ) * Real.log S))
        ≤ S ^ j * Real.exp (-((j : ℝ) * Real.log S)) :=
          mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
      _ = 1 := by rw [mul_comm]; exact hexp
  · have hG0 : ∀ k, G k z = 0 := fun k => by
      have h := hle k
      rw [← hzero] at h
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h (by positivity)))
    have h0 : ‖∏ l, G (β l) z‖ = 0 := by
      rw [norm_eq_zero]
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hj⟩) (hG0 _)
    simp [h0]

/-! ### The easy inclusion on a complex manifold -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- A finite product of holomorphic germs is holomorphic. -/
theorem holomorphicAt_prod {ι : Type*} (s : Finset ι) {F : ι → M → ℂ} {y : M}
    (hF : ∀ i ∈ s, HolomorphicAt n (F i) y) : HolomorphicAt n (fun z => ∏ i ∈ s, F i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holomorphicAt_const (n := n) (x := y) (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).mul (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- **The easy inclusion `J^j ⊆ 𝓘(jφ)`**: for `φ = log ∑ᵢ |gᵢ|² + R` near `y` (`R` bounded,
`φ` quasi-psh), every product of `j ≥ 1` generators lies in `𝓘(jφ)_y`. -/
theorem prod_mem_multiplierIdeal {φ : M → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    {r : ℕ} {g : Fin r → M → ℂ} {U : Set M} (hU : IsOpen U)
    (hg : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (g i) U) {R : M → ℝ} {C : ℝ}
    (hRC : ∀ y ∈ U, |R y| ≤ C) (hφeq : ∀ y ∈ U, φ y = generatorLog g y + (R y : EReal))
    {y : M} (hy : y ∈ U) {j : ℕ} (hj : 0 < j) (β : Fin j → Fin r) :
    (multiplierIdeal (n := n) (j : ℝ) φ).mem y (fun z => ∏ l, g (β l) z) := by
  set e := complexChartAt (n := n) y with he
  have hsrc : y ∈ e.val.source := mem_complexChartAt_source y
  set z₀ := e.val y with hz₀def
  have hz₀t : z₀ ∈ e.val.target := e.val.map_source hsrc
  have hleft : e.val.symm z₀ = y := e.val.left_inv hsrc
  set Ω := e.val.target ∩ e.val.symm ⁻¹' U with hΩdef
  have hΩ : IsOpen Ω := e.val.isOpen_inter_preimage_symm hU
  have hz₀Ω : z₀ ∈ Ω := ⟨hz₀t, by simp only [mem_preimage, hleft]; exact hy⟩
  set g' : Fin r → ComplexModel n → ℂ := fun i z => g i (e.val.symm z) with hg'def
  have hg' : ∀ i, DifferentiableOn ℂ (g' i) Ω := fun i =>
    differentiableOn_comp_chartSymm (n := n) y (hg i)
  have hgen : HolomorphicGeneratorsAt g' z₀ := ⟨Ω, hΩ, hz₀Ω, hg'⟩
  set φ' := chartFunction φ e with hφ'def
  have hval : ∀ z ∈ Ω, φ' z = generatorLog g' z + (R (e.val.symm z) : EReal) :=
    fun z hz => hφeq _ hz.2
  have hsame : SameSingularityTypeOn φ' (generatorLog g') Ω := by
    refine ⟨⟨C, fun z hz => ?_⟩, ⟨C, fun z hz => ?_⟩⟩
    · rw [hval z hz]
      gcongr
      exact (le_abs_self _).trans (hRC _ hz.2)
    · rw [hval z hz, add_assoc, ← EReal.coe_add]
      refine le_add_of_nonneg_right (EReal.coe_nonneg.mpr ?_)
      linarith [neg_abs_le (R (e.val.symm z)), hRC _ hz.2]
  have hφq : QuasiPlurisubharmonicAt φ' z₀ := hφ e z₀ hz₀t
  have hlq : QuasiPlurisubharmonicAt (generatorLog g') z₀ :=
    quasiPlurisubharmonicAt_generatorLog hgen
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  refine ⟨?_, ?_⟩
  · refine holomorphicAt_prod Finset.univ fun l _ => ?_
    filter_upwards [hU.mem_nhds hy] with z hz
    exact (hg (β l) z hz).mdifferentiableAt (hU.mem_nhds hz)
  · refine (Pending.multiplierIntegrableAt_iff_of_sameSingularityTypeOn hφq hlq
      (hΩ.mem_nhds hz₀Ω) hsame).mpr ?_
    refine multiplierIntegrableAt_of_bounded_density hgen ?_ hjR ENNReal.one_lt_top
      (Eventually.of_forall fun z => multiplierDensity_prod_le_one hj g' β z)
    filter_upwards [hΩ.mem_nhds hz₀Ω] with z hz
    have hd : ∀ l, DifferentiableAt ℂ (g' (β l)) z :=
      fun l => (hg' (β l) z hz).differentiableAt (hΩ.mem_nhds hz)
    have key : ∀ s : Finset (Fin j), DifferentiableAt ℂ (fun w => ∏ l ∈ s, g' (β l) w) z := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact (hd a).mul ih
    exact key Finset.univ

end Manifold

end SGPT.NAPotential.BJ.GfIm
