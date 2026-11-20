import SGPT.Foundations.Analysis.Pending.GlobalWeightedDecreasingLimit
import SGPT.Foundations.Analysis.Pending.GlobalSlotLinear
import SGPT.Foundations.Analysis.Pending.BoundedPotentialSmoothingOfAlgebraicApproximation
import SGPT.Foundations.Analysis.Pending.KahlerDomination

set_option autoImplicit false

/-!
# Integration by parts for bounded potentials on a compact Kähler manifold

Let `(M, ω)` be a compact Kähler manifold, `η₁, …, ηₙ` and `θ'` closed real `(1,1)`-forms and
`w` a tuple of bounded `ηᵢ`-PSH functions. For a slot `i₀` write

* `μ[a]` for the global mixed measure with forms `η` and the bounded `η_{i₀}`-PSH function `a`
  in slot `i₀` (the other slots `wᵢ`),
* `μ'[c]` for the global mixed measure with forms `η`, except `θ'` in slot `i₀`, and the
  bounded `θ'`-PSH function `c` in slot `i₀`.

Then for bounded `a, b` (`η_{i₀}`-PSH) and `c, d` (`θ'`-PSH)

  `∫ (a - b) dμ'[c] - ∫ (a - b) dμ'[d] = ∫ (c - d) dμ[a] - ∫ (c - d) dμ[b]`

(`integral_sub_symm`), that is `∫ f ddᶜg ∧ T = ∫ g ddᶜf ∧ T` for `f = a - b`, `g = c - d` and
`T = ⋀_{i ≠ i₀} (ηᵢ + ddᶜwᵢ)`. This is the integration by parts formula for bounded
potentials (Bedford–Taylor; Boucksom–Eyssidieux–Guedj–Zeriahi, *Monge–Ampère equations in big
cohomology classes*, Thm. 1.14 in the bounded case; used in Xia's SGPT notes, proof of
Lemma 3.1.3).

## The proof

1. *A chart-smooth function against bounded slots* (`integral_sub_eq_defect_of_chartSmooth`):
   for a chart-smooth `F`, `∫ F dμ[v ← c] - ∫ F dμ[v] = ∫ (c - v_{i₀}) d(T(F) - T(0))`, where
   `T(F)` carries `F` in slot `i₀` with the form `η_{i₀} + Cω`. Each chart-supported piece
   `χ_b F` of a partition of unity is `GlobalSlotStokes.integral_sub_eq_defect`, and the
   defects add up (`sum_defectMeasure_add_eq`: locally, Bedford–Taylor limits are additive in
   one slot).
2. *Chart-smooth `a`, `b`* (`integral_sub_symm_of_chartSmooth`): apply 1 to `a` and to `b` with
   one constant `C`; one-slot linearity (`GlobalSlotLinear`) replaces `T(a) - T(b)` by
   `μ[a] - μ[b]`.
3. *Bounded `a, b, c, d`*: Demailly's regularization (`exists_antitone_chartSmooth`, from
   `Demailly1992AlgebraicApproximation`) gives decreasing chart-smooth approximations of all
   slots and weights, with curvature loss `ω / (k + 1)`; step 2 holds at every level, and every
   term converges by `GlobalWeightedDecreasingLimit.tendsto_integral_globalMixedMeasure_of_antitone`.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.BoundedIntegrationByParts

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open MixedNonPluripolar MixedMongeAmpere GlobalNonPluripolar BoundedGlobalProduct
open BedfordTaylor FirstPass.MongeAmpere GlobalSlotStokes

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Enlarging the Kähler multiple -/

/-- A `(θ + Aω)`-PSH function is `(θ + Bω)`-PSH for `A ≤ B`. -/
theorem thetaPlurisubharmonic_add_smul_mono (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {A B : ℝ} (hAB : A ≤ B) {u : M → EReal}
    (hu : ThetaPlurisubharmonic (θ + A • omega.form).val u) :
    ThetaPlurisubharmonic (θ + B • omega.form).val u := by
  have h := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hu
    (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hAB))
  have e : θ + A • omega.form + (B - A) • omega.form = θ + B • omega.form := by
    rw [add_assoc, ← add_smul, add_sub_cancel]
  rwa [e] at h

/-- Equal forms and equal potentials give equal global mixed measures. -/
theorem globalMixedMeasure_congr' [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    {θ θ' : Fin n → ClosedRealOneOneForm n M} {u u' : Fin n → M → EReal} (hθ : θ = θ')
    (hu : u = u') (h : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (h' : ∀ i, ThetaPlurisubharmonic (θ' i).val (u' i)) :
    globalMixedMeasure θ u h = globalMixedMeasure θ' u' h' := by
  subst hθ hu
  rfl

/-! ### Decreasing smooth approximation of a bounded potential -/

/-- **Demailly's decreasing regularization of a bounded potential**, with curvature loss
`ω / (k + 1)`: a bounded `θ`-PSH function on a compact Kähler manifold is the pointwise limit of a
decreasing sequence of chart-smooth `(θ + ω / (k + 1))`-PSH functions. -/
theorem exists_antitone_chartSmooth [CompactSpace M] (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {u : M → EReal} (hu : ThetaPlurisubharmonic θ.val u)
    (hub : IsBoundedPotential u) :
    ∃ uk : ℕ → M → ℝ, (∀ k, ChartSmooth (n := n) (uk k)) ∧
      (∀ k : ℕ, ThetaPlurisubharmonic (θ + (1 / ((k : ℝ) + 1)) • omega.form).val
        fun x => ((uk k x : ℝ) : EReal)) ∧
      (∀ x, Antitone fun k => uk k x) ∧
      ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x).toReal) := by
  obtain ⟨a, b, hab⟩ := hub
  obtain ⟨psiSeq, delta, -, hsmooth, hanti, hinf, -, hdlim, hpsh⟩ :=
    Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation omega θ u
      ⟨hu, BoundedPotentialSmoothingOfAlgebraicApproximation.locallyNondegenerate_of_coe_le
        (fun x => (hab x).1)⟩
  have hge : ∀ k x, u x ≤ psiSeq k x := fun k x => by rw [← hinf x]; exact iInf_le _ k
  have hbot : ∀ k x, psiSeq k x ≠ ⊥ := fun k x =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) ((hab x).1.trans (hge k x))
  have htop : ∀ k x, psiSeq k x ≠ ⊤ := fun k x => (hpsh k).quasiPshPotential.1.ne_top x
  have hcoe : ∀ k x, (((psiSeq k x).toReal : ℝ) : EReal) = psiSeq k x :=
    fun k x => EReal.coe_toReal (htop k x) (hbot k x)
  have hev : ∀ j : ℕ, ∀ᶠ k in atTop, delta k ≤ 1 / ((j : ℝ) + 1) := fun j =>
    hdlim.eventually (Iic_mem_nhds (by positivity))
  obtain ⟨φ, hφ, hφd⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨fun j x => (psiSeq (φ j) x).toReal, fun j => ?_, fun j => ?_, fun x => ?_, fun x => ?_⟩
  · exact BoundedPotentialSmoothingOfAlgebraicApproximation.chartSmooth_toReal_of_smoothOffPoleSet
      (AdmissibleCurrentFormPositivity.SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole
        (hsmooth _)) (hbot _)
  · have h := thetaPlurisubharmonic_add_smul_mono omega (hφd j) (hpsh (φ j)).1
    have e : (fun x => (((psiSeq (φ j) x).toReal : ℝ) : EReal)) = psiSeq (φ j) := by
      funext x; exact hcoe _ x
    rw [e]
    exact h
  · intro i j hij
    exact EReal.toReal_le_toReal (hanti x (hφ.monotone hij)) (hbot _ x) (htop _ x)
  · have h1 : Tendsto (fun k => psiSeq k x) atTop (𝓝 (⨅ k, psiSeq k x)) :=
      tendsto_atTop_iInf (hanti x)
    rw [hinf x] at h1
    have hlim : Tendsto (fun j => psiSeq (φ j) x) atTop (𝓝 (u x)) :=
      h1.comp hφ.tendsto_atTop
    have hut : u x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top b) (hab x).2
    have hub' : u x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hab x).1
    exact (EReal.tendsto_toReal hut hub').comp hlim

/-! ### Step 1: a chart-smooth function against bounded slots -/

section StepOne

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {η : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}
  {v : Fin n → M → EReal} (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i))
  (hb : ∀ i, IsBoundedPotential (v i)) (i₀ : Fin n) (C : ℝ)

include hb in
/-- **The defects of pieces add up to the defect of their sum**:
`Σ_b T(f_b) + T(0) = T(Σ_b f_b) + Σ_b T(0)`. Chartwise both sides are the Bedford–Taylor
limit of the tuple with `Σ_b f_b + (N + 2) p` in slot `i₀`. -/
theorem sum_defectMeasure_add_eq {N : ℕ} {f : Fin (N + 1) → M → ℝ}
    (hf : ∀ b, ThetaPlurisubharmonic (η i₀ + C • κ).val fun x => ((f b x : ℝ) : EReal))
    (hfc : ∀ b, Continuous (f b)) {F : M → ℝ}
    (hF : ThetaPlurisubharmonic (η i₀ + C • κ).val fun x => ((F x : ℝ) : EReal))
    (hFc : Continuous F) (hsum : ∀ x, ∑ b, f b x = F x)
    (h0 : ThetaPlurisubharmonic (η i₀ + C • κ).val fun _ => (((0 : ℝ) : ℝ) : EReal)) :
    (∑ b, defectMeasure hv i₀ C (f b) (hf b)) + defectMeasure hv i₀ C (fun _ => 0) h0 =
      defectMeasure hv i₀ C F hF + ∑ _b : Fin (N + 1), defectMeasure hv i₀ C (fun _ => 0) h0 := by
  refine measure_eq_of_restrict_eq_of_openCover (fun J : SlotChart η κ => (J.source : Set M))
    (fun J => J.source.isOpen) (fun x => SlotChart.exists_mem_source η κ x) fun J => ?_
  choose μ hμ heq using fun b => J.exists_isBTLimit_defect hv hb i₀ C (hf b) (hfc b)
  obtain ⟨μ0, hμ0, h0eq⟩ := J.exists_isBTLimit_defect hv hb i₀ C h0 continuous_const
  obtain ⟨μF, hμF, hFeq⟩ := J.exists_isBTLimit_defect hv hb i₀ C hF hFc
  rw [Measure.restrict_add, Measure.restrict_add, restrict_finset_sum, restrict_finset_sum]
  simp only [heq, h0eq, hFeq]
  have hsumμ := IsBTLimit.sum_slot i₀
    (s := fun b z => f b (J.chart.val.symm z) + J.regularizer i₀ C z) hμ
  have hsum0 := IsBTLimit.sum_slot i₀ (N := N)
    (s := fun _ z => (fun _ : M => (0 : ℝ)) (J.chart.val.symm z) + J.regularizer i₀ C z)
    (ν := fun _ => μ0) fun _ => hμ0
  obtain ⟨ρ, hρ⟩ := exists_isBTLimit_update_add i₀ hsumμ hμ0
  have hρeq := IsBTLimit.add_slot i₀ hρ hsumμ hμ0
  obtain ⟨ρ', hρ'⟩ := exists_isBTLimit_update_add i₀ hμF hsum0
  have hρ'eq := IsBTLimit.add_slot i₀ hρ' hμF hsum0
  have hloc : ∑ b, μ b + μ0 = μF + ∑ _b : Fin (N + 1), μ0 := by
    rw [← hρeq, ← hρ'eq]
    refine (hρ.congr fun i z _ => ?_).unique hρ'
    classical
    by_cases h : i = i₀
    · subst h
      simp only [Function.update_self, Finset.sum_add_distrib, hsum, zero_add]
      ring
    · simp [Function.update_of_ne h]
  ext s hs
  simp only [Measure.add_apply, Measure.coe_finsetSum, Finset.sum_apply, Patch.pushMeasure_apply]
  have e1 := congrArg (fun ρ : Measure (ComplexModel n) =>
    ρ ((J.domain : Set (ComplexModel n)) ∩ J.chart.val.symm ⁻¹' s)) hloc
  simp only [Measure.add_apply, Measure.coe_finsetSum, Finset.sum_apply] at e1
  exact e1

end StepOne

section StepOneGlobal

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **A chart-smooth function against bounded slots.** For a bounded tuple `v`, a bounded
`a` and a chart-smooth `F`, there is `C₀` such that for every `C ≥ C₀` the function `F` is
`(η_{i₀} + Cω)`-PSH and
`∫ F dμ[v ← a] - ∫ F dμ[v] = ∫ (a - v_{i₀}) dT(F) - ∫ (a - v_{i₀}) dT(0)`,
where `T(f)` carries the background `η_{i₀} + Cω` and the potential `f` in slot `i₀`. -/
theorem integral_sub_eq_defect_of_chartSmooth (omega : KahlerBackground n M)
    {η : Fin n → ClosedRealOneOneForm n M} {v : Fin n → M → EReal}
    (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i)) (hb : ∀ i, IsBoundedPotential (v i))
    (i₀ : Fin n) {a : M → EReal}
    (hva : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update v i₀ a i))
    (ha : IsBoundedPotential a) {F : M → ℝ} (hFs : ChartSmooth (n := n) F) :
    ∃ C₀ : ℝ, (∀ C, C₀ ≤ C → (η i₀ + C • omega.form).val.IsSemipositive ∧
        ThetaPlurisubharmonic (η i₀ + C • omega.form).val fun x => ((F x : ℝ) : EReal)) ∧
      ∀ C, C₀ ≤ C →
        ∀ (hF : ThetaPlurisubharmonic (η i₀ + C • omega.form).val fun x => ((F x : ℝ) : EReal))
          (h0 : ThetaPlurisubharmonic (η i₀ + C • omega.form).val
            fun _ => (((0 : ℝ) : ℝ) : EReal)),
          (∫ x, F x ∂(globalMixedMeasure η (Function.update v i₀ a) hva)) -
              ∫ x, F x ∂(globalMixedMeasure η v hv) =
            (∫ x, ((a x).toReal - (v i₀ x).toReal) ∂(defectMeasure hv i₀ C F hF)) -
              ∫ x, ((a x).toReal - (v i₀ x).toReal) ∂(defectMeasure hv i₀ C (fun _ => 0) h0) := by
  classical
  choose J hJ using SlotChart.exists_mem_source η omega.form
  obtain ⟨m, χ, idx, hsm, -, hsupp, hcpt, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n)
      (fun x => (J x).source) fun x => ⟨x, hJ x⟩
  set f : Fin m → M → ℝ := fun b x => χ b x * F x with hf_def
  have hfs : ∀ b, ChartSmooth (n := n) (f b) := fun b e => (hsm b e).mul (hFs e)
  obtain ⟨C₁, -, hsemi₁, hpsh₁⟩ := SmoothDDCForm.exists_pos_thetaPlurisubharmonic_smooth omega
    (fun _ : Option (Fin m) => η i₀) (fun o => o.elim F f)
    (fun o => by cases o <;> simp [hFs, hfs])
  refine ⟨C₁, fun C hC => ⟨KahlerDomination.isSemipositive_add_smul_mono omega.isSemipositive hC
    (hsemi₁ none), thetaPlurisubharmonic_add_smul_mono omega hC (by simpa using hpsh₁ none)⟩,
    fun C hC hF h0 => ?_⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · simp [Measure.eq_zero_of_isEmpty]
  obtain ⟨x₀⟩ := hM
  have hm : m ≠ 0 := by
    rintro rfl
    simpa using hsum x₀
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hfC : ∀ b, ThetaPlurisubharmonic (η i₀ + C • omega.form).val
      fun x => ((f b x : ℝ) : EReal) :=
    fun b => thetaPlurisubharmonic_add_smul_mono omega hC (by simpa using hpsh₁ (some b))
  have hχc : ∀ b, Continuous (χ b) := fun b => ChartSmooth.continuous (hsm b)
  have hFc : Continuous F := ChartSmooth.continuous hFs
  have hfc : ∀ b, Continuous (f b) := fun b => (hχc b).mul hFc
  have hbd : ∀ {g : M → ℝ}, Continuous g → ∃ Q : ℝ, ∀ x, |g x| ≤ Q := fun hg => by
    obtain ⟨Q, hQ⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact ⟨Q, fun x => by simpa [Real.norm_eq_abs] using hQ x (mem_univ x)⟩
  have hbva : ∀ i, IsBoundedPotential (Function.update v i₀ a i) := by
    intro i
    by_cases h : i = i₀
    · subst h; simpa using ha
    · simpa [Function.update_of_ne h] using hb i
  have hfa := globalMixedMeasure_isFiniteMeasure_of_bounded hva hbva
  have hfv := globalMixedMeasure_isFiniteMeasure_of_bounded hv hb
  have hsplit : ∀ (μ : Measure M) [IsFiniteMeasure μ], ∫ x, F x ∂μ = ∑ b, ∫ x, f b x ∂μ :=
    fun μ _ => GlobalWeightedDecreasingLimit.integral_eq_sum_mul (fun b => (hχc b).measurable)
      (fun b => hbd (hχc b)) hsum μ hFc.measurable (hbd hFc)
  have hpiece : ∀ b, (∫ x, f b x ∂(globalMixedMeasure η (Function.update v i₀ a) hva)) -
      ∫ x, f b x ∂(globalMixedMeasure η v hv) =
        (∫ x, ((a x).toReal - (v i₀ x).toReal) ∂(defectMeasure hv i₀ C (f b) (hfC b))) -
          ∫ x, ((a x).toReal - (v i₀ x).toReal) ∂(defectMeasure hv i₀ C (fun _ => 0) h0) :=
    fun b => integral_sub_eq_defect hv hb i₀ C hva ha (J (idx b)) (hfs b)
      (tsupport_mul_subset_left.trans (hsupp b))
      ((hcpt b).of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left) (hfC b) h0
  set g : M → ℝ := fun x => (a x).toReal - (v i₀ x).toReal with hg
  have hgmeas : Measurable g :=
    (ThetaPlurisubharmonic.measurable_toReal (by simpa using hva i₀)).sub
      (ThetaPlurisubharmonic.measurable_toReal (hv i₀))
  obtain ⟨Qa, hQa⟩ := IsBoundedPotential.exists_abs_toReal_le ha
  obtain ⟨Qv, hQv⟩ := IsBoundedPotential.exists_abs_toReal_le (hb i₀)
  have hgb : ∀ x, |g x| ≤ Qa + Qv := fun x =>
    (abs_sub _ _).trans (add_le_add (hQa x) (hQv x))
  have hgint : ∀ {f' : M → ℝ} (hf' : ThetaPlurisubharmonic (η i₀ + C • omega.form).val
      fun x => ((f' x : ℝ) : EReal)), Continuous f' →
        Integrable g (defectMeasure hv i₀ C f' hf') := by
    intro f' hf' hf'c
    have : IsFiniteMeasure (defectMeasure hv i₀ C f' hf') :=
      globalMixedMeasure_isFiniteMeasure_of_bounded
        (slotTuple_thetaPlurisubharmonic hv i₀ C hf') (slotTuple_isBoundedPotential hb i₀ hf'c)
    exact integrable_of_measurable_bounded hgmeas hgb _
  have htel := sum_defectMeasure_add_eq hv hb i₀ C hfC hfc hF hFc
    (fun x => by simp only [hf_def, ← Finset.sum_mul, hsum x, one_mul]) h0
  have h1 := congrArg (fun ρ : Measure M => ∫ x, g x ∂ρ) htel
  simp only at h1
  rw [integral_add_measure (integrable_finsetSum_measure.2 fun b _ => hgint (hfC b) (hfc b))
      (hgint h0 continuous_const),
    integral_finsetSum_measure (fun b _ => hgint (hfC b) (hfc b)),
    integral_add_measure (hgint hF hFc)
      (integrable_finsetSum_measure.2 fun b _ => hgint h0 continuous_const),
    integral_finsetSum_measure (fun b _ => hgint h0 continuous_const)] at h1
  rw [hsplit, hsplit, ← Finset.sum_sub_distrib]
  simp only [hpiece]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 ⊢
  linarith

end StepOneGlobal

/-! ### Step 2: chart-smooth `a`, `b` -/

section StepTwo

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Splitting off a semipositive part of one slot.** If `a` is bounded and `η_{i₀}`-PSH,
the measure with background `θ' + Cω` and potential `a` in slot `i₀` is the measure with
background `η_{i₀}` plus a measure that does not depend on `a`. -/
theorem globalMixedMeasure_update_split (omega : KahlerBackground n M)
    {η : Fin n → ClosedRealOneOneForm n M} {w : Fin n → M → EReal} (i₀ : Fin n)
    {θ' : ClosedRealOneOneForm n M} {C : ℝ} {a : M → EReal} (hab : IsBoundedPotential a)
    (ha : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update w i₀ a i))
    (hT : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ (θ' + C • omega.form) i).val
      (Function.update w i₀ a i))
    (h0 : ∀ i, ThetaPlurisubharmonic
      (Function.update η i₀ (θ' - η i₀ + C • omega.form) i).val
      (Function.update w i₀ (fun _ => 0) i)) :
    globalMixedMeasure (Function.update η i₀ (θ' + C • omega.form)) (Function.update w i₀ a) hT =
      globalMixedMeasure η (Function.update w i₀ a) ha +
        globalMixedMeasure (Function.update η i₀ (θ' - η i₀ + C • omega.form))
          (Function.update w i₀ (fun _ => 0)) h0 := by
  classical
  set Θ := Function.update η i₀ (θ' + C • omega.form) with hΘ
  have hθ : Θ i₀ = (1 : ℝ) • η i₀ + (1 : ℝ) • (θ' - η i₀ + C • omega.form) := by
    simp only [hΘ, Function.update_self, one_smul]
    abel
  have hfun : (fun p => ((1 : ℝ) : EReal) * a p + ((1 : ℝ) : EReal) * (fun _ => (0 : EReal)) p) =
      a := by
    funext p; simp
  have hc : ∀ i, ThetaPlurisubharmonic (Θ i).val (Function.update w i₀
      (fun p => ((1 : ℝ) : EReal) * a p + ((1 : ℝ) : EReal) * (fun _ => (0 : EReal)) p) i) := by
    rw [hfun]; exact hT
  have hα : Function.update Θ i₀ (η i₀) = η := by
    rw [hΘ, Function.update_idem, Function.update_eq_self]
  have hβ : Function.update Θ i₀ (θ' - η i₀ + C • omega.form) =
      Function.update η i₀ (θ' - η i₀ + C • omega.form) := by
    rw [hΘ, Function.update_idem]
  have ha' : ∀ i, ThetaPlurisubharmonic (Function.update Θ i₀ (η i₀) i).val
      (Function.update w i₀ a i) := by rw [hα]; exact ha
  have h0' : ∀ i, ThetaPlurisubharmonic
      (Function.update Θ i₀ (θ' - η i₀ + C • omega.form) i).val
      (Function.update w i₀ (fun _ => (0 : EReal)) i) := by rw [hβ]; exact h0
  have hpa : globalMixedMeasure (Function.update Θ i₀ (θ' - η i₀ + C • omega.form))
      (Function.update w i₀ (fun _ => (0 : EReal))) h0' {p | a p = ⊥} = 0 := by
    have : {p | a p = ⊥} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun p hp => hab.ne_bot p hp
    rw [this, measure_empty]
  have hpb : globalMixedMeasure (Function.update Θ i₀ (η i₀)) (Function.update w i₀ a) ha'
      {p | (fun _ => (0 : EReal)) p = ⊥} = 0 := by
    simp
  have h := GlobalSlotLinear.globalMixedMeasure_update_add_smul i₀ one_pos one_pos hθ hc ha' h0'
    hpa hpb
  rw [ENNReal.ofReal_one, one_smul, one_smul] at h
  calc globalMixedMeasure Θ (Function.update w i₀ a) hT
      = globalMixedMeasure Θ (Function.update w i₀
          (fun p => ((1 : ℝ) : EReal) * a p + ((1 : ℝ) : EReal) * (fun _ => (0 : EReal)) p)) hc :=
        globalMixedMeasure_congr' rfl (by rw [hfun]) _ _
    _ = _ := h
    _ = _ := by
        rw [globalMixedMeasure_congr' hα rfl ha' ha,
          globalMixedMeasure_congr' hβ rfl h0' h0]

/-- **Integration by parts with chart-smooth `a`, `b`.** For a bounded tuple `w`, chart-smooth
`η_{i₀}`-PSH `a`, `b` and bounded `θ'`-PSH `c`, `d`,
`∫ (a - b) dμ'[c] - ∫ (a - b) dμ'[d] = ∫ (c - d) dμ[a] - ∫ (c - d) dμ[b]`. -/
theorem integral_sub_symm_of_chartSmooth (omega : KahlerBackground n M)
    {η : Fin n → ClosedRealOneOneForm n M} {w : Fin n → M → EReal}
    (hwb : ∀ i, IsBoundedPotential (w i)) (i₀ : Fin n) {θ' : ClosedRealOneOneForm n M}
    {a b : M → ℝ} (has : ChartSmooth (n := n) a) (hbs : ChartSmooth (n := n) b)
    (ha : ∀ i, ThetaPlurisubharmonic (η i).val
      (Function.update w i₀ (fun x => ((a x : ℝ) : EReal)) i))
    (hb : ∀ i, ThetaPlurisubharmonic (η i).val
      (Function.update w i₀ (fun x => ((b x : ℝ) : EReal)) i))
    {c d : M → EReal} (hcb : IsBoundedPotential c) (hdb : IsBoundedPotential d)
    (hc : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ θ' i).val (Function.update w i₀ c i))
    (hd : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ θ' i).val (Function.update w i₀ d i)) :
    (∫ x, (a x - b x) ∂(globalMixedMeasure (Function.update η i₀ θ') (Function.update w i₀ c) hc)) -
        ∫ x, (a x - b x) ∂(globalMixedMeasure (Function.update η i₀ θ') (Function.update w i₀ d) hd) =
      (∫ x, ((c x).toReal - (d x).toReal) ∂(globalMixedMeasure η
          (Function.update w i₀ fun x => ((a x : ℝ) : EReal)) ha)) -
        ∫ x, ((c x).toReal - (d x).toReal) ∂(globalMixedMeasure η
          (Function.update w i₀ fun x => ((b x : ℝ) : EReal)) hb) := by
  classical
  set η' := Function.update η i₀ θ' with hη'
  set v := Function.update w i₀ d with hv_def
  have hvb : ∀ i, IsBoundedPotential (v i) := by
    intro i
    by_cases h : i = i₀
    · subst h; simpa [hv_def] using hdb
    · simpa [hv_def, Function.update_of_ne h] using hwb i
  have hupd : Function.update v i₀ c = Function.update w i₀ c := by
    rw [hv_def, Function.update_idem]
  have hva : ∀ i, ThetaPlurisubharmonic (η' i).val (Function.update v i₀ c i) := by
    rw [hupd]; exact hc
  obtain ⟨Ca, hCa, hA⟩ := integral_sub_eq_defect_of_chartSmooth omega hd hvb i₀ hva hcb has
  obtain ⟨Cb, hCb, hB⟩ := integral_sub_eq_defect_of_chartSmooth omega hd hvb i₀ hva hcb hbs
  obtain ⟨A, -, hAsemi⟩ :=
    KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega fun _ : Unit => θ' - η i₀
  set C := max (max Ca Cb) A with hC
  have hCa' : Ca ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCb' : Cb ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hAC : A ≤ C := le_max_right _ _
  have hsemiβ : (θ' - η i₀ + C • omega.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_add_smul_mono omega.isSemipositive hAC (hAsemi ())
  have hη'i : η' i₀ = θ' := by rw [hη', Function.update_self]
  -- the two instances of step 1, with one constant
  obtain ⟨hsemiC, hFa⟩ := hCa C hCa'
  have hFb := (hCb C hCb').2
  have h0 : ThetaPlurisubharmonic (η' i₀ + C • omega.form).val
      fun _ => (((0 : ℝ) : ℝ) : EReal) :=
    BoundedGlobalProduct.thetaPlurisubharmonic_const _ hsemiC 0
  have eA := hA C hCa' hFa h0
  have eB := hB C hCb' hFb h0
  -- the defect measures as split measures
  have hforms : SlotChart.regForms η' omega.form i₀ C =
      Function.update η i₀ (θ' + C • omega.form) := by
    rw [SlotChart.regForms, hη'i, hη', Function.update_idem]
  have htuple : ∀ f : M → ℝ, slotTuple v i₀ f = Function.update w i₀ fun x => ((f x : ℝ) : EReal) := by
    intro f
    rw [slotTuple, hv_def, Function.update_idem]
  have h0β : ∀ i, ThetaPlurisubharmonic
      (Function.update η i₀ (θ' - η i₀ + C • omega.form) i).val
      (Function.update w i₀ (fun _ => 0) i) := by
    intro i
    by_cases h : i = i₀
    · subst h
      simp only [Function.update_self]
      simpa using BoundedGlobalProduct.thetaPlurisubharmonic_const _ hsemiβ 0
    · simpa [Function.update_of_ne h] using ha i
  have hsplitT : ∀ (f : M → ℝ) (hf : ThetaPlurisubharmonic (η' i₀ + C • omega.form).val
      fun x => ((f x : ℝ) : EReal)) (hfη : ∀ i, ThetaPlurisubharmonic (η i).val
        (Function.update w i₀ (fun x => ((f x : ℝ) : EReal)) i)) (hfb : IsBoundedPotential
          fun x => ((f x : ℝ) : EReal)),
      defectMeasure hd i₀ C f hf = globalMixedMeasure η
        (Function.update w i₀ fun x => ((f x : ℝ) : EReal)) hfη +
          globalMixedMeasure (Function.update η i₀ (θ' - η i₀ + C • omega.form))
            (Function.update w i₀ (fun _ => 0)) h0β := by
    intro f hf hfη hfb
    have hT : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ (θ' + C • omega.form) i).val
        (Function.update w i₀ (fun x => ((f x : ℝ) : EReal)) i) := by
      rw [← hforms, ← htuple]
      exact slotTuple_thetaPlurisubharmonic hd i₀ C hf
    rw [defectMeasure, globalMixedMeasure_congr' hforms (htuple f) _ hT]
    exact globalMixedMeasure_update_split omega i₀ hfb hfη hT h0β
  -- integrability
  have hbd : ∀ {g : M → ℝ}, Continuous g → ∃ Q : ℝ, ∀ x, |g x| ≤ Q := fun hg => by
    obtain ⟨Q, hQ⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact ⟨Q, fun x => by simpa [Real.norm_eq_abs] using hQ x (mem_univ x)⟩
  have hab_a : IsBoundedPotential fun x => ((a x : ℝ) : EReal) :=
    GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous (ChartSmooth.continuous has)
  have hab_b : IsBoundedPotential fun x => ((b x : ℝ) : EReal) :=
    GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous (ChartSmooth.continuous hbs)
  have hwa : ∀ i, IsBoundedPotential (Function.update w i₀ (fun x => ((a x : ℝ) : EReal)) i) := by
    intro i; by_cases h : i = i₀
    · subst h; simpa using hab_a
    · simpa [Function.update_of_ne h] using hwb i
  have hwb' : ∀ i, IsBoundedPotential (Function.update w i₀ (fun x => ((b x : ℝ) : EReal)) i) := by
    intro i; by_cases h : i = i₀
    · subst h; simpa using hab_b
    · simpa [Function.update_of_ne h] using hwb i
  have hwc : ∀ i, IsBoundedPotential (Function.update w i₀ c i) := by
    intro i; by_cases h : i = i₀
    · subst h; simpa using hcb
    · simpa [Function.update_of_ne h] using hwb i
  have hw0 : ∀ i, IsBoundedPotential (Function.update w i₀ (fun _ => (0 : EReal)) i) := by
    intro i; by_cases h : i = i₀
    · subst h
      simp only [Function.update_self]
      exact ⟨0, 0, fun _ => by simp⟩
    · simpa [Function.update_of_ne h] using hwb i
  have := globalMixedMeasure_isFiniteMeasure_of_bounded ha hwa
  have := globalMixedMeasure_isFiniteMeasure_of_bounded hb hwb'
  have := globalMixedMeasure_isFiniteMeasure_of_bounded hc hwc
  have := globalMixedMeasure_isFiniteMeasure_of_bounded hd hvb
  have := globalMixedMeasure_isFiniteMeasure_of_bounded h0β hw0
  set g : M → ℝ := fun x => (c x).toReal - (d x).toReal with hg
  have hcpsh : ThetaPlurisubharmonic θ'.val c := by simpa [hη'] using hc i₀
  have hdpsh : ThetaPlurisubharmonic θ'.val d := by simpa [hη', hv_def] using hd i₀
  have hgmeas : Measurable g :=
    (ThetaPlurisubharmonic.measurable_toReal hcpsh).sub
      (ThetaPlurisubharmonic.measurable_toReal hdpsh)
  obtain ⟨Qc, hQc⟩ := IsBoundedPotential.exists_abs_toReal_le hcb
  obtain ⟨Qd, hQd⟩ := IsBoundedPotential.exists_abs_toReal_le hdb
  have hgb : ∀ x, |g x| ≤ Qc + Qd := fun x =>
    (abs_sub _ _).trans (add_le_add (hQc x) (hQd x))
  have hgi : ∀ (μ : Measure M) [IsFiniteMeasure μ], Integrable g μ := fun μ _ =>
    integrable_of_measurable_bounded hgmeas hgb μ
  have hai : ∀ (μ : Measure M) [IsFiniteMeasure μ], Integrable a μ := fun μ _ => by
    obtain ⟨Q, hQ⟩ := hbd (ChartSmooth.continuous has)
    exact integrable_of_measurable_bounded (ChartSmooth.continuous has).measurable hQ μ
  have hbi : ∀ (μ : Measure M) [IsFiniteMeasure μ], Integrable b μ := fun μ _ => by
    obtain ⟨Q, hQ⟩ := hbd (ChartSmooth.continuous hbs)
    exact integrable_of_measurable_bounded (ChartSmooth.continuous hbs).measurable hQ μ
  -- assemble
  have hvi : (fun x => ((c x).toReal - (v i₀ x).toReal)) = g := by
    funext x; simp [hv_def, hg]
  rw [hvi, hsplitT a hFa ha hab_a, integral_add_measure (hgi _) (hgi _)] at eA
  rw [hvi, hsplitT b hFb hb hab_b, integral_add_measure (hgi _) (hgi _)] at eB
  rw [globalMixedMeasure_congr' rfl hupd hva hc] at eA eB
  rw [integral_sub (hai _) (hbi _), integral_sub (hai _) (hbi _)]
  linarith

end StepTwo

/-! ### Step 3: bounded potentials -/

section StepThree

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [BorelSpace M] [CompactSpace M] in
/-- The integral of a difference of bounded measurable functions against a finite measure. -/
theorem integral_sub_of_bounded {μ : Measure M} [IsFiniteMeasure μ] {f g : M → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∃ Q : ℝ, ∀ x, |f x| ≤ Q)
    (hgb : ∃ Q : ℝ, ∀ x, |g x| ≤ Q) :
    ∫ x, (f x - g x) ∂μ = (∫ x, f x ∂μ) - ∫ x, g x ∂μ := by
  obtain ⟨Qf, hQf⟩ := hfb
  obtain ⟨Qg, hQg⟩ := hgb
  exact integral_sub (integrable_of_measurable_bounded hf hQf μ)
    (integrable_of_measurable_bounded hg hQg μ)

/-- **Integration by parts for bounded potentials** on a compact Kähler manifold. Let `w` be
a bounded tuple, `a, b` bounded with `w[i₀ ← a]`, `w[i₀ ← b]` `η`-PSH, and `c, d` bounded with
`w[i₀ ← c]`, `w[i₀ ← d]` PSH for the forms `η[i₀ ← θ']`. Then
`∫ (a - b) dμ'[c] - ∫ (a - b) dμ'[d] = ∫ (c - d) dμ[a] - ∫ (c - d) dμ[b]`, where `μ[x]` and
`μ'[x]` are the global mixed measures of `w[i₀ ← x]` for the forms `η` and `η[i₀ ← θ']`. -/
theorem integral_sub_symm (omega : KahlerBackground n M)
    {η : Fin n → ClosedRealOneOneForm n M} {w : Fin n → M → EReal}
    (hwb : ∀ i, IsBoundedPotential (w i)) (i₀ : Fin n) {θ' : ClosedRealOneOneForm n M}
    {a b c d : M → EReal} (hab : IsBoundedPotential a) (hbb : IsBoundedPotential b)
    (hcb : IsBoundedPotential c) (hdb : IsBoundedPotential d)
    (ha : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update w i₀ a i))
    (hb : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update w i₀ b i))
    (hc : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ θ' i).val (Function.update w i₀ c i))
    (hd : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ θ' i).val (Function.update w i₀ d i)) :
    (∫ x, ((a x).toReal - (b x).toReal) ∂(globalMixedMeasure (Function.update η i₀ θ')
        (Function.update w i₀ c) hc)) -
      ∫ x, ((a x).toReal - (b x).toReal) ∂(globalMixedMeasure (Function.update η i₀ θ')
        (Function.update w i₀ d) hd) =
    (∫ x, ((c x).toReal - (d x).toReal) ∂(globalMixedMeasure η (Function.update w i₀ a) ha)) -
      ∫ x, ((c x).toReal - (d x).toReal) ∂(globalMixedMeasure η (Function.update w i₀ b) hb) := by
  classical
  -- a tuple all of whose slots are bounded and PSH
  set w' := Function.update w i₀ a with hw'
  have hupd : ∀ x : M → EReal, Function.update w' i₀ x = Function.update w i₀ x := fun x => by
    rw [hw', Function.update_idem]
  have hw'psh : ∀ i, ThetaPlurisubharmonic (η i).val (w' i) := ha
  have hw'b : ∀ i, IsBoundedPotential (w' i) := by
    intro i; by_cases h : i = i₀
    · subst h; simpa [hw'] using hab
    · simpa [hw', Function.update_of_ne h] using hwb i
  have hpshη : ∀ {x : M → EReal}, (∀ i, ThetaPlurisubharmonic (η i).val (Function.update w i₀ x i)) →
      ThetaPlurisubharmonic (η i₀).val x := fun h => by simpa using h i₀
  have hpshθ : ∀ {x : M → EReal}, (∀ i, ThetaPlurisubharmonic (Function.update η i₀ θ' i).val
      (Function.update w i₀ x i)) → ThetaPlurisubharmonic θ'.val x := fun h => by simpa using h i₀
  -- Demailly's approximations of every slot and weight, with loss `ω / (k + 1)`
  choose wk hwks hwk hwanti hwlim using fun i =>
    exists_antitone_chartSmooth omega (η i) (hw'psh i) (hw'b i)
  obtain ⟨ak, haks, hak, haanti, halim⟩ := exists_antitone_chartSmooth omega (η i₀) (hpshη ha) hab
  obtain ⟨bk, hbks, hbk, hbanti, hblim⟩ := exists_antitone_chartSmooth omega (η i₀) (hpshη hb) hbb
  obtain ⟨ck, hcks, hck, hcanti, hclim⟩ := exists_antitone_chartSmooth omega θ' (hpshθ hc) hcb
  obtain ⟨dk, hdks, hdk, hdanti, hdlim⟩ := exists_antitone_chartSmooth omega θ' (hpshθ hd) hdb
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hδ_def
  have hδ : Antitone δ := fun i j hij => by
    simp only [hδ_def]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- general limit statement for one slot and one weight
  have key : ∀ (θ₀ θ₁ : ClosedRealOneOneForm n M) (s : M → EReal)
      (hs : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ θ₀ i).val (Function.update w' i₀ s i))
      (hsb : IsBoundedPotential s) (sk : ℕ → M → ℝ) (hsks : ∀ k, ChartSmooth (n := n) (sk k))
      (hsanti : ∀ x, Antitone fun k => sk k x)
      (hslim : ∀ x, Tendsto (fun k => sk k x) atTop (𝓝 (s x).toReal))
      (hzk : ∀ k i, ThetaPlurisubharmonic (Function.update η i₀ θ₀ i + δ k • omega.form).val
        fun x => ((Function.update (fun i => wk i k) i₀ (sk k) i x : ℝ) : EReal))
      (t : M → EReal) (htb : IsBoundedPotential t) (tk : ℕ → M → ℝ)
      (htks : ∀ k, ChartSmooth (n := n) (tk k))
      (htk : ∀ k, ThetaPlurisubharmonic (θ₁ + δ k • omega.form).val
        fun x => ((tk k x : ℝ) : EReal))
      (htanti : ∀ x, Antitone fun k => tk k x)
      (htlim : ∀ x, Tendsto (fun k => tk k x) atTop (𝓝 (t x).toReal)),
      Tendsto (fun k => ∫ x, tk k x ∂(globalMixedMeasure
          (fun i => Function.update η i₀ θ₀ i + δ k • omega.form)
          (fun i x => ((Function.update (fun i => wk i k) i₀ (sk k) i x : ℝ) : EReal)) (hzk k)))
        atTop (𝓝 (∫ x, (t x).toReal ∂(globalMixedMeasure (Function.update η i₀ θ₀)
          (Function.update w' i₀ s) hs))) := by
    intro θ₀ θ₁ s hs hsb sk hsks hsanti hslim hzk t htb tk htks htk htanti htlim
    have hzb : ∀ i, IsBoundedPotential (Function.update w' i₀ s i) := by
      intro i; by_cases h : i = i₀
      · subst h; simpa using hsb
      · simpa [Function.update_of_ne h] using hw'b i
    refine GlobalWeightedDecreasingLimit.tendsto_integral_globalMixedMeasure_of_antitone hs hzb
      hδ hδ0 (fun k i => ?_) hzk (fun i x => ?_) (fun i x => ?_) htb htks htk htanti htlim
    · by_cases h : i = i₀
      · subst h; simpa using hsks k
      · simpa [Function.update_of_ne h] using hwks i k
    · by_cases h : i = i₀
      · subst h; simpa using hsanti x
      · simpa [Function.update_of_ne h] using hwanti i x
    · by_cases h : i = i₀
      · subst h; simpa using hslim x
      · simpa [Function.update_of_ne h] using hwlim i x
  -- PSH of the level-`k` tuples
  have hlev : ∀ (θ₀ : ClosedRealOneOneForm n M) (sk : ℕ → M → ℝ),
      (∀ k, ThetaPlurisubharmonic (θ₀ + δ k • omega.form).val fun x => ((sk k x : ℝ) : EReal)) →
      ∀ k i, ThetaPlurisubharmonic (Function.update η i₀ θ₀ i + δ k • omega.form).val
        fun x => ((Function.update (fun i => wk i k) i₀ (sk k) i x : ℝ) : EReal) := by
    intro θ₀ sk hsk k i
    by_cases h : i = i₀
    · subst h; simpa using hsk k
    · simpa [Function.update_of_ne h, hδ_def] using hwk i k
  have hlevη : ∀ (sk : ℕ → M → ℝ),
      (∀ k, ThetaPlurisubharmonic (η i₀ + δ k • omega.form).val fun x => ((sk k x : ℝ) : EReal)) →
      ∀ k i, ThetaPlurisubharmonic (η i + δ k • omega.form).val
        fun x => ((Function.update (fun i => wk i k) i₀ (sk k) i x : ℝ) : EReal) := by
    intro sk hsk k i
    by_cases h : i = i₀
    · subst h; simpa using hsk k
    · simpa [Function.update_of_ne h, hδ_def] using hwk i k
  have hηupd : Function.update η i₀ (η i₀) = η := Function.update_eq_self i₀ η
  -- the eight limits
  have hc' : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ θ' i).val (Function.update w' i₀ c i) := by
    rw [hupd]; exact hc
  have hd' : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ θ' i).val (Function.update w' i₀ d i) := by
    rw [hupd]; exact hd
  have ha' : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ (η i₀) i).val
      (Function.update w' i₀ a i) := by rw [hupd, hηupd]; exact ha
  have hb' : ∀ i, ThetaPlurisubharmonic (Function.update η i₀ (η i₀) i).val
      (Function.update w' i₀ b i) := by rw [hupd, hηupd]; exact hb
  have L1 := key θ' (η i₀) c hc' hcb ck hcks hcanti hclim (hlev θ' ck hck) a hab ak haks hak haanti halim
  have L2 := key θ' (η i₀) c hc' hcb ck hcks hcanti hclim (hlev θ' ck hck) b hbb bk hbks hbk hbanti hblim
  have L3 := key θ' (η i₀) d hd' hdb dk hdks hdanti hdlim (hlev θ' dk hdk) a hab ak haks hak haanti halim
  have L4 := key θ' (η i₀) d hd' hdb dk hdks hdanti hdlim (hlev θ' dk hdk) b hbb bk hbks hbk hbanti hblim
  have R1 := key (η i₀) θ' a ha' hab ak haks haanti halim (hlev (η i₀) ak hak) c hcb ck hcks hck hcanti hclim
  have R2 := key (η i₀) θ' a ha' hab ak haks haanti halim (hlev (η i₀) ak hak) d hdb dk hdks hdk hdanti hdlim
  have R3 := key (η i₀) θ' b hb' hbb bk hbks hbanti hblim (hlev (η i₀) bk hbk) c hcb ck hcks hck hcanti hclim
  have R4 := key (η i₀) θ' b hb' hbb bk hbks hbanti hblim (hlev (η i₀) bk hbk) d hdb dk hdks hdk hdanti hdlim
  -- the limit measures are the ones of the statement
  rw [globalMixedMeasure_congr' rfl (hupd c) hc' hc] at L1 L2
  rw [globalMixedMeasure_congr' rfl (hupd d) hd' hd] at L3 L4
  rw [globalMixedMeasure_congr' hηupd (hupd a) ha' ha] at R1 R2
  rw [globalMixedMeasure_congr' hηupd (hupd b) hb' hb] at R3 R4
  -- the identity at every level (step 2)
  have hbdc : ∀ {f : M → ℝ}, Continuous f → ∃ Q : ℝ, ∀ x, |f x| ≤ Q := fun hf => by
    obtain ⟨Q, hQ⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
    exact ⟨Q, fun x => by simpa [Real.norm_eq_abs] using hQ x (mem_univ x)⟩
  have hwkb : ∀ k i, IsBoundedPotential fun x => ((wk i k x : ℝ) : EReal) := fun k i =>
    GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous
      (ChartSmooth.continuous (hwks i k))
  have hcont : ∀ {f : M → ℝ}, ChartSmooth (n := n) f → Continuous f := fun hf =>
    ChartSmooth.continuous hf
  have hlevel : ∀ k,
      ((∫ x, ak k x ∂(globalMixedMeasure (fun i => Function.update η i₀ θ' i + δ k • omega.form)
          (fun i x => ((Function.update (fun i => wk i k) i₀ (ck k) i x : ℝ) : EReal))
          (hlev θ' ck hck k))) -
        ∫ x, bk k x ∂(globalMixedMeasure (fun i => Function.update η i₀ θ' i + δ k • omega.form)
          (fun i x => ((Function.update (fun i => wk i k) i₀ (ck k) i x : ℝ) : EReal))
          (hlev θ' ck hck k))) -
      ((∫ x, ak k x ∂(globalMixedMeasure (fun i => Function.update η i₀ θ' i + δ k • omega.form)
          (fun i x => ((Function.update (fun i => wk i k) i₀ (dk k) i x : ℝ) : EReal))
          (hlev θ' dk hdk k))) -
        ∫ x, bk k x ∂(globalMixedMeasure (fun i => Function.update η i₀ θ' i + δ k • omega.form)
          (fun i x => ((Function.update (fun i => wk i k) i₀ (dk k) i x : ℝ) : EReal))
          (hlev θ' dk hdk k))) =
      ((∫ x, ck k x ∂(globalMixedMeasure (fun i => Function.update η i₀ (η i₀) i + δ k • omega.form)
          (fun i x => ((Function.update (fun i => wk i k) i₀ (ak k) i x : ℝ) : EReal))
          (hlev (η i₀) ak hak k))) -
        ∫ x, dk k x ∂(globalMixedMeasure (fun i => Function.update η i₀ (η i₀) i + δ k • omega.form)
          (fun i x => ((Function.update (fun i => wk i k) i₀ (ak k) i x : ℝ) : EReal))
          (hlev (η i₀) ak hak k))) -
      ((∫ x, ck k x ∂(globalMixedMeasure (fun i => Function.update η i₀ (η i₀) i + δ k • omega.form)
          (fun i x => ((Function.update (fun i => wk i k) i₀ (bk k) i x : ℝ) : EReal))
          (hlev (η i₀) bk hbk k))) -
        ∫ x, dk k x ∂(globalMixedMeasure (fun i => Function.update η i₀ (η i₀) i + δ k • omega.form)
          (fun i x => ((Function.update (fun i => wk i k) i₀ (bk k) i x : ℝ) : EReal))
          (hlev (η i₀) bk hbk k))) := by
    intro k
    set ηk : Fin n → ClosedRealOneOneForm n M := fun i => η i + δ k • omega.form with hηk
    set Wk : Fin n → M → EReal := fun i x => ((wk i k x : ℝ) : EReal) with hWk
    have hWkb : ∀ i, IsBoundedPotential (Wk i) := hwkb k
    have hformsθ : Function.update ηk i₀ (θ' + δ k • omega.form) =
        fun i => Function.update η i₀ θ' i + δ k • omega.form := by
      funext i; by_cases h : i = i₀
      · subst h; simp [hηk]
      · simp [hηk, Function.update_of_ne h]
    have hformsη : ηk = fun i => Function.update η i₀ (η i₀) i + δ k • omega.form := by
      rw [hηupd]
    have htup : ∀ s : M → ℝ, Function.update Wk i₀ (fun x => ((s x : ℝ) : EReal)) =
        fun i x => ((Function.update (fun i => wk i k) i₀ s i x : ℝ) : EReal) := by
      intro s; funext i x; by_cases h : i = i₀
      · subst h; simp
      · simp [hWk, Function.update_of_ne h]
    have hA : ∀ i, ThetaPlurisubharmonic (ηk i).val
        (Function.update Wk i₀ (fun x => ((ak k x : ℝ) : EReal)) i) := by
      rw [htup, hformsη]; exact hlev (η i₀) ak hak k
    have hB : ∀ i, ThetaPlurisubharmonic (ηk i).val
        (Function.update Wk i₀ (fun x => ((bk k x : ℝ) : EReal)) i) := by
      rw [htup, hformsη]; exact hlev (η i₀) bk hbk k
    have hC : ∀ i, ThetaPlurisubharmonic (Function.update ηk i₀ (θ' + δ k • omega.form) i).val
        (Function.update Wk i₀ (fun x => ((ck k x : ℝ) : EReal)) i) := by
      rw [htup, hformsθ]; exact hlev θ' ck hck k
    have hD : ∀ i, ThetaPlurisubharmonic (Function.update ηk i₀ (θ' + δ k • omega.form) i).val
        (Function.update Wk i₀ (fun x => ((dk k x : ℝ) : EReal)) i) := by
      rw [htup, hformsθ]; exact hlev θ' dk hdk k
    have h := integral_sub_symm_of_chartSmooth omega hWkb i₀ (haks k) (hbks k) hA hB
      (GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous (hcont (hcks k)))
      (GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous (hcont (hdks k))) hC hD
    rw [globalMixedMeasure_congr' hformsθ (htup (ck k)) hC (hlev θ' ck hck k),
      globalMixedMeasure_congr' hformsθ (htup (dk k)) hD (hlev θ' dk hdk k),
      globalMixedMeasure_congr' hformsη (htup (ak k)) hA (hlev (η i₀) ak hak k),
      globalMixedMeasure_congr' hformsη (htup (bk k)) hB (hlev (η i₀) bk hbk k)] at h
    simp only [EReal.toReal_coe] at h
    have hfinC := globalMixedMeasure_isFiniteMeasure_of_bounded (hlev θ' ck hck k) fun i =>
      GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous
        (hcont (by by_cases h : i = i₀
                   · subst h; simpa using hcks k
                   · simpa [Function.update_of_ne h] using hwks i k))
    have hfinD := globalMixedMeasure_isFiniteMeasure_of_bounded (hlev θ' dk hdk k) fun i =>
      GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous
        (hcont (by by_cases h : i = i₀
                   · subst h; simpa using hdks k
                   · simpa [Function.update_of_ne h] using hwks i k))
    have hfinA := globalMixedMeasure_isFiniteMeasure_of_bounded (hlev (η i₀) ak hak k) fun i =>
      GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous
        (hcont (by by_cases h : i = i₀
                   · subst h; simpa using haks k
                   · simpa [Function.update_of_ne h] using hwks i k))
    have hfinB := globalMixedMeasure_isFiniteMeasure_of_bounded (hlev (η i₀) bk hbk k) fun i =>
      GlobalWeightedDecreasingLimit.isBoundedPotential_coe_of_continuous
        (hcont (by by_cases h : i = i₀
                   · subst h; simpa using hbks k
                   · simpa [Function.update_of_ne h] using hwks i k))
    rw [integral_sub_of_bounded (hcont (haks k)).measurable (hcont (hbks k)).measurable
        (hbdc (hcont (haks k))) (hbdc (hcont (hbks k))),
      integral_sub_of_bounded (hcont (haks k)).measurable (hcont (hbks k)).measurable
        (hbdc (hcont (haks k))) (hbdc (hcont (hbks k))),
      integral_sub_of_bounded (hcont (hcks k)).measurable (hcont (hdks k)).measurable
        (hbdc (hcont (hcks k))) (hbdc (hcont (hdks k))),
      integral_sub_of_bounded (hcont (hcks k)).measurable (hcont (hdks k)).measurable
        (hbdc (hcont (hcks k))) (hbdc (hcont (hdks k)))] at h
    exact h
  -- passing to the limit
  have hlimL := (L1.sub L2).sub (L3.sub L4)
  have hlimR := (R1.sub R2).sub (R3.sub R4)
  have heq := tendsto_nhds_unique (hlimL.congr hlevel) hlimR
  -- splitting the integrals of the statement
  have hmeas : ∀ {x : M → EReal} {θ₀ : SmoothRealForm n M 2}, ThetaPlurisubharmonic θ₀ x →
      Measurable fun p => (x p).toReal := fun h => ThetaPlurisubharmonic.measurable_toReal h
  have hfinc := globalMixedMeasure_isFiniteMeasure_of_bounded hc fun i => by
    by_cases h : i = i₀
    · subst h; simpa using hcb
    · simpa [Function.update_of_ne h] using hwb i
  have hfind := globalMixedMeasure_isFiniteMeasure_of_bounded hd fun i => by
    by_cases h : i = i₀
    · subst h; simpa using hdb
    · simpa [Function.update_of_ne h] using hwb i
  have hfina := globalMixedMeasure_isFiniteMeasure_of_bounded ha hw'b
  have hfinb := globalMixedMeasure_isFiniteMeasure_of_bounded hb fun i => by
    by_cases h : i = i₀
    · subst h; simpa using hbb
    · simpa [Function.update_of_ne h] using hwb i
  rw [integral_sub_of_bounded (hmeas (hpshη ha)) (hmeas (hpshη hb))
      (IsBoundedPotential.exists_abs_toReal_le hab) (IsBoundedPotential.exists_abs_toReal_le hbb),
    integral_sub_of_bounded (hmeas (hpshη ha)) (hmeas (hpshη hb))
      (IsBoundedPotential.exists_abs_toReal_le hab) (IsBoundedPotential.exists_abs_toReal_le hbb),
    integral_sub_of_bounded (hmeas (hpshθ hc)) (hmeas (hpshθ hd))
      (IsBoundedPotential.exists_abs_toReal_le hcb) (IsBoundedPotential.exists_abs_toReal_le hdb),
    integral_sub_of_bounded (hmeas (hpshθ hc)) (hmeas (hpshθ hd))
      (IsBoundedPotential.exists_abs_toReal_le hcb) (IsBoundedPotential.exists_abs_toReal_le hdb)]
  exact heq

end StepThree

end

end SGPT.Foundations.Analysis.Pending.BoundedIntegrationByParts
