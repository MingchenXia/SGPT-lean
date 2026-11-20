import SGPT.Okounkov.TranscendentalWNConvFL2Density

/-!
# Uniformly small fibre volumes: the predicate and the covering argument

Blueprint `claude-tok-wn-fl2`, nodes `tok-wn-fl2:fibre-small` and `tok-wn-fl2:cover`; source WN21
§7, estimate (eqeq) (`references/wn21-restricted-volume`).

For the deformation `μ : 𝒳 → X × ℙ¹` and a closed real `(1,1)`-form `Θ` on `𝒳`, a set `U ⊆ 𝒳`
has **fibre volumes at most `ε`** (`FibreSmall`) if there is `r > 0` such that
`∫_{s⁻¹(U)} (s^*Θ)ⁿ ≤ ε` (the measure `topFormMeasure ω (s^*Θ)ⁿ` of `X`) for every `τ` with
`0 < |τ| < r` and every holomorphic section `s` of `μ` over `x ↦ (x, τ)`.

* `FibreSmall.mono`, `FibreSmall.union`, `fibreSmall_empty`: monotonicity and subadditivity.
* `exists_fibreSmall_of_local` (`tok-wn-fl2:cover`): if every point `q` of a compact set `S`
  has an open neighbourhood `O_q` such that for every `ε > 0` some open `U ⊇ T ∩ O_q` has fibre
  volumes at most `ε`, then for every `ε > 0` some open `U ⊇ T ∩ S` has fibre volumes at most
  `ε` (finite subcover and `ε = ε/2 + ε/2` by induction).
* Analytic helpers used by the local estimates: bounds of derivatives and of form coefficients
  on compact sets, partial derivatives of jointly smooth maps, and the affine coordinate of `ℙ¹`
  near `0`.
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWN.FL2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN

/-! ### Analytic helpers -/

section Helpers

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- A map smooth on an open set has bounded derivative on every compact subset. -/
theorem exists_bound_fderiv {f : E → G} {O K : Set E} (hO : IsOpen O)
    (hf : ∀ p ∈ O, ContDiffAt ℝ ∞ f p) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ‖fderiv ℝ f p‖ ≤ C := by
  have hf1 : ContDiffOn ℝ 1 f O := fun p hp => ((hf p hp).of_le (by simp)).contDiffWithinAt
  have hc : ContinuousOn (fderiv ℝ f) O := hf1.continuousOn_fderiv_of_isOpen hO le_rfl
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hKO)
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩

omit [NormedSpace ℝ G] in
/-- A map continuous on a compact set with values where a function is continuous gives a bounded
composite. -/
theorem exists_bound_comp {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q] {h : P → Q}
    {a : Q → G} {K : Set P} {T : Set Q} (hK : IsCompact K) (hh : ContinuousOn h K)
    (hKT : MapsTo h K T) (ha : ContinuousOn a T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ‖a (h p)‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (ha.comp hh hKT)
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
  [NormedSpace ℝ B]

/-- The partial derivative in the first factor is bounded by the full derivative. -/
theorem norm_fderiv_left_le {f : A × B → G} {a : A} {b : B}
    (hf : DifferentiableAt ℝ f (a, b)) :
    ‖fderiv ℝ (fun a' => f (a', b)) a‖ ≤ ‖fderiv ℝ f (a, b)‖ := by
  have h : HasFDerivAt (fun a' => f (a', b))
      ((fderiv ℝ f (a, b)).comp (ContinuousLinearMap.inl ℝ A B)) a :=
    hf.hasFDerivAt.comp a (hasFDerivAt_prodMk_left a b)
  rw [h.fderiv]
  calc ‖(fderiv ℝ f (a, b)).comp (ContinuousLinearMap.inl ℝ A B)‖
      ≤ ‖fderiv ℝ f (a, b)‖ * ‖ContinuousLinearMap.inl ℝ A B‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ f (a, b)‖ * 1 := by
        gcongr
        exact ContinuousLinearMap.norm_inl_le_one _ _ _
    _ = _ := mul_one _

/-- The partial derivative in the second factor is bounded by the full derivative. -/
theorem norm_fderiv_right_le {f : A × B → G} {a : A} {b : B}
    (hf : DifferentiableAt ℝ f (a, b)) :
    ‖fderiv ℝ (fun b' => f (a, b')) b‖ ≤ ‖fderiv ℝ f (a, b)‖ := by
  have h : HasFDerivAt (fun b' => f (a, b'))
      ((fderiv ℝ f (a, b)).comp (ContinuousLinearMap.inr ℝ A B)) b :=
    hf.hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)
  rw [h.fderiv]
  calc ‖(fderiv ℝ f (a, b)).comp (ContinuousLinearMap.inr ℝ A B)‖
      ≤ ‖fderiv ℝ f (a, b)‖ * ‖ContinuousLinearMap.inr ℝ A B‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ f (a, b)‖ * 1 := by
        gcongr
        exact ContinuousLinearMap.norm_inr_le_one _ _ _
    _ = _ := mul_one _

omit [NormedSpace ℝ A] [NormedSpace ℝ B] in
/-- A closed product of balls inside an open set of a product. -/
theorem exists_closedBall_prod_subset {O : Set (A × B)} (hO : IsOpen O) {a : A} {b : B}
    (h : (a, b) ∈ O) : ∃ R : ℝ, 0 < R ∧ closedBall a R ×ˢ closedBall b R ⊆ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO _ h
  refine ⟨ε / 2, by positivity, fun p hp => hball ?_⟩
  rw [← ball_prod_same]
  exact ⟨mem_ball.mpr ((mem_closedBall.mp hp.1).trans_lt (by linarith)),
    mem_ball.mpr ((mem_closedBall.mp hp.2).trans_lt (by linarith))⟩

/-- `ε ≥ M · vol(V)` once `vol(V) < ε / M` (`M ≥ 1`). -/
theorem ofReal_mul_le_of_lt_div {M : ℝ} (hM : 1 ≤ M) {ε v : ℝ≥0∞}
    (hv : v < ε / ENNReal.ofReal M) : ENNReal.ofReal M * v ≤ ε := by
  have h0 : ENNReal.ofReal M ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  calc ENNReal.ofReal M * v ≤ ENNReal.ofReal M * (ε / ENNReal.ofReal M) := by gcongr
    _ = ε := ENNReal.mul_div_cancel h0 ENNReal.ofReal_ne_top

/-- `ε / M > 0` for `ε > 0`. -/
theorem div_ofReal_pos {M : ℝ} {ε : ℝ≥0∞} (hε : 0 < ε) : 0 < ε / ENNReal.ofReal M :=
  ENNReal.div_pos hε.ne' ENNReal.ofReal_ne_top

end Helpers

/-! ### The affine coordinate of `ℙ¹` near `0` -/

/-- `τ ↦ [τ : 1]` is continuous. -/
theorem continuous_affineLinePoint : Continuous affineLinePoint :=
  SGPT.Toric.projectiveLineHomeomorph.continuous.comp OnePoint.continuous_coe

/-- For `|τ|` small, `[τ : 1]` lies in the chart of `ℙ¹` at `0`, with coordinate close to that
of `0`. -/
theorem exists_radius_chart (R : ℝ) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ ∀ τ : ℂ, ‖τ‖ < r →
      affineLinePoint τ ∈ (chartAt (ComplexModel 1) projectiveZero).source ∧
        (chartAt (ComplexModel 1) projectiveZero) (affineLinePoint τ) ∈
          ball ((chartAt (ComplexModel 1) projectiveZero) projectiveZero) R := by
  set c₀ := chartAt (ComplexModel 1) projectiveZero
  have h0 : affineLinePoint 0 = projectiveZero := affineLinePoint_zero
  have hc : ContinuousAt (fun τ => c₀ (affineLinePoint τ)) 0 := by
    refine ContinuousAt.comp (f := affineLinePoint) ?_ continuous_affineLinePoint.continuousAt
    rw [h0]
    exact c₀.continuousAt (mem_chart_source _ _)
  have hs : ∀ᶠ τ in 𝓝 (0 : ℂ), affineLinePoint τ ∈ c₀.source := by
    refine continuous_affineLinePoint.continuousAt.preimage_mem_nhds ?_
    rw [h0]
    exact c₀.open_source.mem_nhds (mem_chart_source _ _)
  have hb : ∀ᶠ τ in 𝓝 (0 : ℂ), c₀ (affineLinePoint τ) ∈ ball (c₀ projectiveZero) R := by
    refine hc.preimage_mem_nhds ?_
    rw [h0]
    exact ball_mem_nhds _ hR
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hs.and hb)
  exact ⟨r, hr, fun τ hτ => hball (by simpa using hτ)⟩

/-! ### Uniformly small fibre volumes -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳]

/-- **`tok-wn-fl2:fibre-small`**: `U` has fibre volumes at most `ε` for small `τ ≠ 0`. -/
def FibreSmall (μ : 𝒳 → F.carrier × ProjectiveLine) (Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳)
    (U : Set 𝒳) (ε : ℝ≥0∞) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ τ : ℂ, τ ≠ 0 → ‖τ‖ < r →
    ∀ (s : F.carrier → 𝒳)
      (hs : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s),
      (∀ x, μ (s x) = (x, affineLinePoint τ)) →
        (letI : MeasurableSpace F.carrier := borel F.carrier
         haveI : BorelSpace F.carrier := ⟨rfl⟩
         topFormMeasure F.omega (formPow (ClosedRealOneOneForm.pullback hs Θ).val (m + 1))
           (s ⁻¹' U)) ≤ ε

variable {F} {μ : 𝒳 → F.carrier × ProjectiveLine} {Θ : ClosedRealOneOneForm (m + 1 + 1) 𝒳}

theorem FibreSmall.mono {U V : Set 𝒳} {ε ε' : ℝ≥0∞} (h : FibreSmall F μ Θ U ε) (hVU : V ⊆ U)
    (hε : ε ≤ ε') : FibreSmall F μ Θ V ε' := by
  obtain ⟨r, hr, h⟩ := h
  refine ⟨r, hr, fun τ hτ hτr s hs hsμ => ?_⟩
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  exact (measure_mono (preimage_mono hVU)).trans ((h τ hτ hτr s hs hsμ).trans hε)

theorem FibreSmall.union {U V : Set 𝒳} {a b : ℝ≥0∞} (hU : FibreSmall F μ Θ U a)
    (hV : FibreSmall F μ Θ V b) : FibreSmall F μ Θ (U ∪ V) (a + b) := by
  obtain ⟨r, hr, hU⟩ := hU
  obtain ⟨r', hr', hV⟩ := hV
  refine ⟨min r r', lt_min hr hr', fun τ hτ hτr s hs hsμ => ?_⟩
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  rw [preimage_union]
  exact (measure_union_le _ _).trans (add_le_add
    (hU τ hτ (hτr.trans_le (min_le_left _ _)) s hs hsμ)
    (hV τ hτ (hτr.trans_le (min_le_right _ _)) s hs hsμ))

theorem fibreSmall_empty (ε : ℝ≥0∞) : FibreSmall F μ Θ ∅ ε := by
  refine ⟨1, one_pos, fun τ _ _ s hs _ => ?_⟩
  let _ : MeasurableSpace F.carrier := borel F.carrier
  have _ : BorelSpace F.carrier := ⟨rfl⟩
  simp

/-- **`tok-wn-fl2:cover`**: local smallness on a compact set gives global smallness. -/
theorem exists_fibreSmall_of_local {S T : Set 𝒳} (hS : IsCompact S)
    (hloc : ∀ q ∈ S, ∃ O : Set 𝒳, IsOpen O ∧ q ∈ O ∧ ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ U : Set 𝒳, IsOpen U ∧ T ∩ O ⊆ U ∧ FibreSmall F μ Θ U ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ U : Set 𝒳, IsOpen U ∧ T ∩ S ⊆ U ∧ FibreSmall F μ Θ U ε := by
  classical
  choose O hOo hqO hO using hloc
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun q : S => O q.1 q.2)
    (fun q => hOo q.1 q.2) (fun q hq => mem_iUnion.mpr ⟨⟨q, hq⟩, hqO q hq⟩)
  have key : ∀ t : Finset S, ∀ ε : ℝ≥0∞, 0 < ε → ∃ U : Set 𝒳, IsOpen U ∧
      T ∩ (⋃ i ∈ t, O i.1 i.2) ⊆ U ∧ FibreSmall F μ Θ U ε := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro ε _
      exact ⟨∅, isOpen_empty, by simp, fibreSmall_empty ε⟩
    | insert i t _ ih =>
      intro ε hε
      have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
      obtain ⟨U₁, hU₁o, hU₁, hU₁s⟩ := ih (ε / 2) hε2
      obtain ⟨U₂, hU₂o, hU₂, hU₂s⟩ := hO i.1 i.2 (ε / 2) hε2
      refine ⟨U₂ ∪ U₁, hU₂o.union hU₁o, ?_, ?_⟩
      · rintro z ⟨hzT, hz⟩
        rw [Finset.set_biUnion_insert] at hz
        rcases hz with hz | hz
        · exact Or.inl (hU₂ ⟨hzT, hz⟩)
        · exact Or.inr (hU₁ ⟨hzT, hz⟩)
      · exact (hU₂s.union hU₁s).mono subset_rfl (ENNReal.add_halves ε).le
  intro ε hε
  obtain ⟨U, hUo, hU, hUs⟩ := key t ε hε
  exact ⟨U, hUo, fun z hz => hU ⟨hz.1, ht hz.2⟩, hUs⟩

end SGPT.Okounkov.TranscendentalWN.FL2
