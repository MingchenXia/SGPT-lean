import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass GlobalNonPluripolar GlobalDiagonalScaling
open GlobalMultilinearExpansion MixedMassProductCalculus

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual original mixed product of the unchanged forms and entire potentials. -/
def sourceMixedNonPluripolarMeasure
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i)) : Measure M :=
  globalMixedMeasure (fun i => atlasClosedFormToNative (θ i)) u
    (fun i => ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)).1)

omit [BorelSpace M] in
/-- The constant actual source tuple is exactly the existing source diagonal measure. -/
theorem sourceMixedNonPluripolarMeasure_diagonal
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceMixedNonPluripolarMeasure (fun _ => θ) (fun _ => u) (fun _ => hu) =
      sourcePotentialNonPluripolarMeasure θ u hu := rfl

/-- Any genuine original potential's pole set is null for the actual whole mixed product. -/
theorem sourceMixedNonPluripolarMeasure_pole_null
    {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : Fin n → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (u i))
    {η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : M → EReal}
    (hv : (ofFixedModel n M).IsThetaPSH η v) :
    sourceMixedNonPluripolarMeasure θ u hu {x | v x = ⊥} = 0 :=
  globalMixedMeasure_pole_null_of_nondegenerate
    (fun i => ((isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)).1)
    ((isThetaPSH_iff_nativeThetaPotential η v).mp hv)

omit [BorelSpace M] in
/-- The zero actual endpoint selects the second potential in every slot. -/
theorem sourceEndpointMixedMeasure_zero
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (v u : M → EReal)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceEndpointMixedMeasure θ v u hv hu ⟨0, Nat.zero_lt_succ n⟩ =
      sourcePotentialNonPluripolarMeasure θ v hv := by
  unfold sourceEndpointMixedMeasure sourcePotentialNonPluripolarMeasure diagonalPotentialMeasure
  exact globalMixedMeasure_congr rfl (by funext i; simp) _ _

variable [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u v w : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- Actual E1 signed differences are integrable against an independent E1 diagonal measure. -/
theorem sourceRelativeFiniteEnergy_integrable_independent_diagonal
    (ω : KahlerBackground n M) (hu : SourceRelativeFiniteEnergy θ φ u hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ) (hw : SourceRelativeFiniteEnergy θ φ w hφ) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
      (sourcePotentialNonPluripolarMeasure θ w hw.1.choose) := by
  have hiu := sourceRelativeFiniteEnergy_endpoint_integrable ω hu hw ⟨0, Nat.zero_lt_succ n⟩
  have hiv := sourceRelativeFiniteEnergy_endpoint_integrable ω hv hw ⟨0, Nat.zero_lt_succ n⟩
  rw [sourceEndpointMixedMeasure_zero] at hiu hiv
  let μ := sourcePotentialNonPluripolarMeasure θ w hw.1.choose
  have hpole (a : M → EReal) (ha : (ofFixedModel n M).IsThetaPSH θ a) :
      ∀ᵐ x ∂μ, a x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not, μ, ← sourceMixedNonPluripolarMeasure_diagonal] using
      sourceMixedNonPluripolarMeasure_pole_null (fun _ : Fin n => hw.1.choose) ha
  apply (hiu.sub hiv).congr
  filter_upwards [hpole u hu.1.choose, hpole v hv.1.choose, hpole w hw.1.choose]
    with x hub hvb hwb
  change canonicalERealDiffToReal (u x) (w x) - canonicalERealDiffToReal (v x) (w x) = _
  rw [← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1.choose).1.quasiPlurisubharmonic.ne_top x) hub,
    ← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1.choose).1.quasiPlurisubharmonic.ne_top x) hvb,
    ← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ w).mp hw.1.choose).1.quasiPlurisubharmonic.ne_top x) hwb]
  simp only [canonicalERealDiffToReal_coe_coe]
  ring

omit [ConnectedSpace M] in
/-- The same original positive-mass model itself belongs to its actual E1 class. -/
theorem sourceModelPotential_finiteEnergy (ω : KahlerBackground n M)
    (hφ : SourceModelPotential θ φ) : SourceRelativeFiniteEnergy θ φ φ hφ := by
  apply (sourceRelativeFiniteEnergy_iff_native θ φ φ hφ).mpr
  exact RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity ω
    ⟨hφ.toNative.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩

/-- A genuine E1 lower barrier for an entire finite family is produced by actual rooftops. -/
theorem sourceRelativeFiniteEnergy_common_lower {I : Type*} [Fintype I]
    (ω : KahlerBackground n M) {f : I → M → EReal}
    (hf : ∀ i, SourceRelativeFiniteEnergy θ φ (f i) hφ) :
    ∃ r : M → EReal, SourceRelativeFiniteEnergy θ φ r hφ ∧ ∀ i, r ≤ f i := by
  classical
  have hfinite (s : Finset I) :
      ∃ r : M → EReal, SourceRelativeFiniteEnergy θ φ r hφ ∧ ∀ i ∈ s, r ≤ f i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨φ, sourceModelPotential_finiteEnergy ω hφ, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨r, hr, hrl⟩ := ih
      refine ⟨thetaRooftop θ r (f i), sourceRelativeFiniteEnergy_rooftop ω hr (hf i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact thetaRooftop_le_right θ r (f j)
      · exact (thetaRooftop_le_left θ r (f i)).trans (hrl j hjs)
  obtain ⟨r, hr, hrl⟩ := hfinite Finset.univ
  exact ⟨r, hr, fun i => hrl i (Finset.mem_univ i)⟩

/-- The actual uniform positive finite sum, with a nonempty index set of size m+1. -/
def sourceUniformAverage {m : ℕ} (f : Fin (m + 1) → M → EReal) : M → EReal :=
  sumPot Finset.univ (fun _ => 1 / (m + 1 : ℝ)) f

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The exact normalized constant identity includes every genuine negative-infinite value. -/
theorem sourceUniformAverage_const {m : ℕ} (u : M → EReal) (hu : ∀ x, u x ≠ ⊤) :
    sourceUniformAverage (fun _ : Fin (m + 1) => u) = u := by
  classical
  have hc : 0 < 1 / (m + 1 : ℝ) := by positivity
  funext x
  induction hux : u x using EReal.rec with
  | bot =>
    unfold sourceUniformAverage sumPot
    simp only [hux, EReal.coe_mul_bot_of_pos hc, Fin.sum_univ_succ, EReal.bot_add]
  | top => exact (hu x hux).elim
  | coe a =>
    have hsum (s : Finset (Fin (m + 1))) :
        (∑ i ∈ s, (((1 / (m + 1 : ℝ)) * a : ℝ) : EReal)) =
          ((∑ i ∈ s, (1 / (m + 1 : ℝ)) * a : ℝ) : EReal) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => simp only [Finset.sum_insert hi, ih, EReal.coe_add]
    simp only [sourceUniformAverage, sumPot, hux, ← EReal.coe_mul]
    rw [hsum]
    congr 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Positivity gives monotonicity in every actual member of the finite average. -/
theorem sourceUniformAverage_mono {m : ℕ} {f g : Fin (m + 1) → M → EReal}
    (hfg : ∀ i, f i ≤ g i) : sourceUniformAverage f ≤ sourceUniformAverage g := by
  intro x
  unfold sourceUniformAverage sumPot
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (hfg i x) (EReal.coe_nonneg.mpr (by positivity))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The finite average has precisely the unchanged background form. -/
theorem sourceUniformAverage_form (m : ℕ) (θ : ClosedRealOneOneForm n M) :
    sumForm Finset.univ (fun _ : Fin (m + 1) => 1 / (m + 1 : ℝ)) (fun _ => θ) = θ := by
  unfold sumForm
  rw [← Finset.sum_smul]
  have hc : (∑ _i : Fin (m + 1), 1 / (m + 1 : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  rw [hc, one_smul]

/-- Genuine PSH, preceq and E1 of the whole finite average are manufactured internally. -/
theorem sourceRelativeFiniteEnergy_uniformAverage {m : ℕ}
    (ω : KahlerBackground n M) {f : Fin (m + 1) → M → EReal}
    (hf : ∀ i, SourceRelativeFiniteEnergy θ φ (f i) hφ) :
    SourceRelativeFiniteEnergy θ φ (sourceUniformAverage f) hφ := by
  classical
  obtain ⟨r, hr, hrl⟩ := sourceRelativeFiniteEnergy_common_lower ω hf
  have hrtop : ∀ x, r x ≠ ⊤ :=
    ((isThetaPSH_iff_nativeThetaPotential θ r).mp hr.1.choose).1.quasiPlurisubharmonic.ne_top
  have hlow : r ≤ sourceUniformAverage f := by
    have h := sourceUniformAverage_mono hrl
    rwa [sourceUniformAverage_const r hrtop] at h
  have hraw := thetaPlurisubharmonic_sumPot
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (m + 1))).Nonempty)
    (fun _ : Fin (m + 1) => show 0 < 1 / (m + 1 : ℝ) by positivity)
    (fun i => ((isThetaPSH_iff_nativeThetaPotential θ (f i)).mp (hf i).1.choose).1)
  rw [sourceUniformAverage_form] at hraw
  have hstrong : IsThetaPshPotential (atlasClosedFormToNative θ).val (sourceUniformAverage f) := by
    refine ⟨hraw, ?_⟩
    intro x U hU hx
    obtain ⟨y, hy, hry⟩ := ((isThetaPSH_iff_nativeThetaPotential θ r).mp hr.1.choose).2 x U hU hx
    exact ⟨y, hy, ne_bot_of_le_ne_bot hry (hlow y)⟩
  have hpre (i : Fin (m + 1)) : MoreSingularOn (f i) φ univ := (hf i).1.choose_spec.1
  choose D hD using hpre
  let C : ℝ := ∑ i, |D i|
  have hDC (i : Fin (m + 1)) : D i ≤ C :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_univ i))
  have hbound : ∀ i, f i ≤ fun x => φ x + (C : EReal) := by
    intro i x
    exact (hD i x (mem_univ x)).trans
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (hDC i)))
  have htop : ∀ x, φ x + (C : EReal) ≠ ⊤ :=
    (hφ.toNative.plurisubharmonic.add_const C).1.quasiPlurisubharmonic.ne_top
  have hhigh : sourceUniformAverage f ≤ fun x => φ x + (C : EReal) := by
    have h := sourceUniformAverage_mono hbound
    rwa [sourceUniformAverage_const _ htop] at h
  exact sourceRelativeFiniteEnergy_upward ω hr
    ⟨(isThetaPSH_iff_nativeThetaPotential θ _).mpr hstrong, ⟨C, fun x _ => hhigh x⟩⟩
    (MoreSingularOn.of_le fun x _ => hlow x)

/-- Every selected actual mixed product is dominated by the genuine E1 average diagonal. -/
theorem sourceMixedNonPluripolarMeasure_le_average {m : ℕ}
    (ω : KahlerBackground n M) {f : Fin (m + 1) → M → EReal}
    (hf : ∀ i, SourceRelativeFiniteEnergy θ φ (f i) hφ) (g : Fin n → Fin (m + 1)) :
    sourceMixedNonPluripolarMeasure (fun _ => θ) (fun i => f (g i))
        (fun i => (hf (g i)).1.choose) ≤
      ENNReal.ofReal ((m + 1 : ℝ) ^ n) • sourcePotentialNonPluripolarMeasure θ
        (sourceUniformAverage f) (sourceRelativeFiniteEnergy_uniformAverage ω hf).1.choose := by
  classical
  have hnat (i : Fin (m + 1)) :=
    (isThetaPSH_iff_nativeThetaPotential θ (f i)).mp (hf i).1.choose
  have hc (_ : Fin n) (_ : Fin (m + 1)) : 0 ≤ 1 / (m + 1 : ℝ) := by positivity
  have hexp := globalMixedMeasure_sumPot_expand ω hc hnat
  change globalMixedMeasure _ (fun _ : Fin n => sourceUniformAverage f) _ = _ at hexp
  have hforms : (fun _ : Fin n => sumForm Finset.univ
      (fun _ : Fin (m + 1) => 1 / (m + 1 : ℝ)) (fun _ => atlasClosedFormToNative θ)) =
      fun _ => atlasClosedFormToNative θ := by
    funext i
    exact sourceUniformAverage_form m _
  erw [globalMixedMeasure_congr hforms rfl _
    (fun _ => ((isThetaPSH_iff_nativeThetaPotential θ _).mp
      (sourceRelativeFiniteEnergy_uniformAverage ω hf).1.choose).1)] at hexp
  apply Measure.le_iff.mpr
  intro s _
  have he := congrArg (fun μ : Measure M => μ s) hexp
  rw [Measure.coe_finsetSum, Finset.sum_apply] at he
  have hterm := Finset.single_le_sum (fun (a : Fin n → Fin (m + 1)) _ =>
    bot_le (a := (ENNReal.ofReal (∏ _i : Fin n, 1 / (m + 1 : ℝ)) •
      globalMixedMeasure (fun _ => atlasClosedFormToNative θ) (fun i => f (a i))
        (fun i => (hnat (a i)).1)) s)) (Finset.mem_univ g)
  rw [← he] at hterm
  have hweight : (∏ _i : Fin n, 1 / (m + 1 : ℝ)) = (1 / (m + 1 : ℝ)) ^ n := by simp
  change (ENNReal.ofReal (∏ _i : Fin n, 1 / (m + 1 : ℝ)) •
    sourceMixedNonPluripolarMeasure (fun _ => θ) (fun i => f (g i))
      (fun i => (hf (g i)).1.choose)) s ≤
    sourcePotentialNonPluripolarMeasure θ (sourceUniformAverage f)
      (sourceRelativeFiniteEnergy_uniformAverage ω hf).1.choose s at hterm
  rw [hweight, Measure.smul_apply, smul_eq_mul] at hterm
  rw [Measure.smul_apply, smul_eq_mul]
  have hinv : ENNReal.ofReal ((m + 1 : ℝ) ^ n) *
      ENNReal.ofReal ((1 / (m + 1 : ℝ)) ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    have hpos : (m + 1 : ℝ) ≠ 0 := by positivity
    rw [mul_one_div_cancel hpos, one_pow, ENNReal.ofReal_one]
  calc sourceMixedNonPluripolarMeasure (fun _ => θ) (fun i => f (g i))
        (fun i => (hf (g i)).1.choose) s =
      ENNReal.ofReal ((m + 1 : ℝ) ^ n) *
        (ENNReal.ofReal ((1 / (m + 1 : ℝ)) ^ n) *
          sourceMixedNonPluripolarMeasure (fun _ => θ) (fun i => f (g i))
            (fun i => (hf (g i)).1.choose) s) := by rw [← mul_assoc, hinv, one_mul]
    _ ≤ _ := mul_le_mul_right hterm _

/-- The whole original independent-gamma E1 mixed-integrability assertion, including n=0. -/
theorem sourceRelativeFiniteEnergy_integrable_independent_mixed
    (ω : KahlerBackground n M) (hu : SourceRelativeFiniteEnergy θ φ u hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ) {γ : Fin n → M → EReal}
    (hγ : ∀ i, SourceRelativeFiniteEnergy θ φ (γ i) hφ) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
      (sourceMixedNonPluripolarMeasure (fun _ => θ) γ (fun i => (hγ i).1.choose)) := by
  let f : Fin (n + 1) → M → EReal := Fin.cases φ γ
  have hf (i : Fin (n + 1)) : SourceRelativeFiniteEnergy θ φ (f i) hφ := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact sourceModelPotential_finiteEnergy ω hφ
    · exact hγ j
  have hi := sourceRelativeFiniteEnergy_integrable_independent_diagonal ω hu hv
    (sourceRelativeFiniteEnergy_uniformAverage ω hf)
  exact Integrable.of_measure_le_smul ENNReal.ofReal_ne_top
    (sourceMixedNonPluripolarMeasure_le_average ω hf Fin.succ) hi

/-- The literal real signed difference is integrable on the actual original mixed domain. -/
theorem sourceRelativeFiniteEnergy_integrable_independent_mixed_toReal
    (ω : KahlerBackground n M) (hu : SourceRelativeFiniteEnergy θ φ u hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ) {γ : Fin n → M → EReal}
    (hγ : ∀ i, SourceRelativeFiniteEnergy θ φ (γ i) hφ) :
    Integrable (fun x => (u x).toReal - (v x).toReal)
      (sourceMixedNonPluripolarMeasure (fun _ => θ) γ (fun i => (hγ i).1.choose)) := by
  apply (sourceRelativeFiniteEnergy_integrable_independent_mixed ω hu hv hγ).congr
  have hpole (a : M → EReal) (ha : (ofFixedModel n M).IsThetaPSH θ a) :
      ∀ᵐ x ∂sourceMixedNonPluripolarMeasure (fun _ => θ) γ (fun i => (hγ i).1.choose),
        a x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not] using
      sourceMixedNonPluripolarMeasure_pole_null (fun i => (hγ i).1.choose) ha
  filter_upwards [hpole u hu.1.choose, hpole v hv.1.choose] with x hub hvb
  rw [← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1.choose).1.quasiPlurisubharmonic.ne_top x) hub,
    ← EReal.coe_toReal
      (((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1.choose).1.quasiPlurisubharmonic.ne_top x) hvb]
  simp only [canonicalERealDiffToReal_coe_coe, EReal.toReal_coe]

end SGPT.PSH.VariableComplexAtlas
