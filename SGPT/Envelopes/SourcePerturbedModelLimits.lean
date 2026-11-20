import SGPT.Envelopes.SourceEqualMassEnvelope
import SGPT.Envelopes.SourceZeroContactL1
import SGPT.PSH.SourceThetaPSHCompactness
import SGPT.Foundations.Analysis.Pending.TraceFreeLimit
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive

/-!
# Decreasing nets of model potentials with vanishing Kähler perturbation

Source: Chapter "The envelope operators", `prop:vol_limit_model` (the model and the
mass clauses) and `cor:varphiperturbtheta`.

Let `ω` be a Kähler form, `(ε_i)_{i ∈ I}` a decreasing net in `ℝ_{≥ 0}` with limit `0`
and `(φ_i)_{i ∈ I}` a decreasing net with `φ_i ∈ PSH(X, θ + ε_i ω)` and
`P_{θ + ε_i ω}[φ_i] = φ_i`. Then `φ = inf_i φ_i` satisfies `P_θ[φ] = φ` and
`∫ (θ + ε_i ω)_{φ_i}^n → ∫ θ_φ^n`.

The proof is the source's. The infimum is `(θ + ε_{i₀} ω)`-psh for every `i₀` (its tail
is a decreasing net of such potentials with supremum `0`), hence `θ`-psh. The lower
bound of the masses is monotonicity. For the upper bound, `θ_{φ_i}^n` is carried by
`{φ_i = 0}` (`thm:Pvarphisupport`, contact part), the contact mass is monotone in the
background and upper semicontinuous along `L¹`-convergent nets (`cor:intcontlimsup`),
and the mass of the fixed potential `φ` is continuous in the background.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Envelopes.PerturbedModelLimit

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass TraceFreeLimit
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] [ConnectedSpace M] in
/-- Diagonal measures only depend on the background form and the potential. -/
theorem diagonalPotentialMeasure_congr {T T' : ClosedRealOneOneForm n M}
    (hT : T = T') {u v : M → EReal} (huv : u = v) (hu : IsThetaPshPotential T.val u)
    (hv : IsThetaPshPotential T'.val v) :
    diagonalPotentialMeasure T u hu = diagonalPotentialMeasure T' v hv := by
  subst hT huv
  rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Enlarging the Kähler perturbation preserves `θ`-psh potentials. -/
theorem isThetaPshPotential_perturb_mono (ω : KahlerBackground n M)
    {T : ClosedRealOneOneForm n M} {s t : ℝ} (hst : s ≤ t) {u : M → EReal}
    (hu : IsThetaPshPotential (T + s • ω.form).val u) :
    IsThetaPshPotential (T + t • ω.form).val u := by
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hu
    (KahlerDomination.isSemipositive_smul ω.isSemipositive (sub_nonneg.2 hst))
  rwa [show T + s • ω.form + (t - s) • ω.form = T + t • ω.form by module] at h

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Enlarging the Kähler perturbation enlarges the `P`-envelope. -/
theorem singularityEnvelope_perturb_mono (ω : KahlerBackground n M)
    {T : ClosedRealOneOneForm n M} {s t : ℝ} (hst : s ≤ t) (u : M → EReal) :
    singularityEnvelope (T + s • ω.form).val u ≤ singularityEnvelope (T + t • ω.form).val u := by
  have h := singularityEnvelope_le_add (θ := T + s • ω.form) (η := (t - s) • ω.form)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive (sub_nonneg.2 hst)) u
  rwa [show T + s • ω.form + (t - s) • ω.form = T + t • ω.form by module] at h

section Nets

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- The tail `{i | i₀ ≤ i}` of a directed set is directed. -/
instance isDirectedOrder_Ici (i₀ : I) : IsDirectedOrder (Ici i₀) :=
  ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨c, le_trans a.2 hac⟩, hac, hbc⟩⟩

omit [Nonempty I] in
/-- The infimum of an antitone net equals the infimum over any tail. -/
theorem iInf_Ici_eq_of_antitone {f : I → EReal} (hf : Antitone f) (i₀ : I) :
    (⨅ j : Ici i₀, f j) = ⨅ i, f i := by
  apply le_antisymm
  · refine le_iInf fun i => ?_
    obtain ⟨c, h1, h2⟩ := exists_ge_ge i₀ i
    exact (iInf_le (fun j : Ici i₀ => f j) ⟨c, h1⟩).trans (hf h2)
  · exact le_iInf fun j => iInf_le f j.1

variable (ω : KahlerBackground n M) (T : ClosedRealOneOneForm n M)
  {ε : I → ℝ} {φ : I → M → EReal}

omit [Preorder I] [IsDirectedOrder I] [Nonempty I] [MeasurableSpace M] [BorelSpace M] in
/-- A fixed point of a `P`-envelope vanishes somewhere and is nonpositive. -/
theorem fixedPoint_zero_and_nonpos
    (hφ : ∀ i, IsThetaPshPotential (T + ε i • ω.form).val (φ i))
    (hfix : ∀ i, singularityEnvelope (T + ε i • ω.form).val (φ i) = φ i) (i : I) :
    (∃ x, φ i x = 0) ∧ φ i ≤ 0 := by
  obtain ⟨x, hx⟩ := exists_singularityEnvelope_eq_zero (hφ i)
  refine ⟨⟨x, by rwa [hfix i] at hx⟩, ?_⟩
  rw [← hfix i]
  exact singularityEnvelope_le_zero _ _

omit [Nonempty I] in
/-- Every tail of the net lies in `PSH(X, θ + ε_{i₀} ω)`, its infimum is the infimum of
the whole net, which is therefore `(θ + ε_{i₀} ω)`-psh, and the tail converges in `L¹`. -/
theorem tail_isThetaPshPotential_and_L1 (hεanti : Antitone ε) (hφanti : Antitone φ)
    (hφ : ∀ i, IsThetaPshPotential (T + ε i • ω.form).val (φ i))
    (hfix : ∀ i, singularityEnvelope (T + ε i • ω.form).val (φ i) = φ i) (i₀ : I) :
    IsThetaPshPotential (T + ε i₀ • ω.form).val (fun x => ⨅ i, φ i x) ∧
      Tendsto (fun j : Ici i₀ => sourceGlobalL1Distance ω (φ j) (fun x => ⨅ i, φ i x))
        atTop (𝓝 0) := by
  have hJ : ∀ j : Ici i₀, IsThetaPshPotential (T + ε i₀ • ω.form).val (φ j) := fun j =>
    isThetaPshPotential_perturb_mono ω (hεanti j.2) (hφ j)
  have hanti : ∀ x, Antitone (fun j : Ici i₀ => φ j x) := fun x a b hab => hφanti hab x
  have ha : ∀ j : Ici i₀, ((0 : ℝ) : EReal) ≤ ⨆ x, φ j x := by
    intro j
    obtain ⟨x, hx⟩ := (fixedPoint_zero_and_nonpos ω T hφ hfix j).1
    refine le_trans (le_of_eq ?_) (le_iSup (fun x => φ j x) x)
    rw [hx]
    rfl
  obtain ⟨hpsh, hL1, -⟩ := SGPT.PSH.ConnectedThetaPSHCompactness.native_decreasing_net_L1
    (θ := T + ε i₀ • ω.form) hJ hanti 0 ha
  have heq : (fun x => ⨅ j : Ici i₀, φ j x) = fun x => ⨅ i, φ i x :=
    funext fun x => iInf_Ici_eq_of_antitone (fun a b h => hφanti h x) i₀
  rw [heq] at hpsh hL1
  refine ⟨hpsh, ?_⟩
  exact (ChartwiseGlobalL1.manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ω)
    (fun j => (hJ j).1.quasiPlurisubharmonic.upperSemicontinuous.measurable)
    hpsh.1.quasiPlurisubharmonic.upperSemicontinuous.measurable).mp hL1

/-- `prop:vol_limit_model`, first step: the infimum of the net is `θ`-psh. -/
theorem iInf_isThetaPshPotential (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (hφanti : Antitone φ) (hφ : ∀ i, IsThetaPshPotential (T + ε i • ω.form).val (φ i))
    (hfix : ∀ i, singularityEnvelope (T + ε i • ω.form).val (φ i) = φ i) :
    IsThetaPshPotential T.val (fun x => ⨅ i, φ i x) := by
  have hall := fun i₀ => (tail_isThetaPshPotential_and_L1 ω T hεanti hφanti hφ hfix i₀).1
  let c : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hc : ∀ k, ThetaPlurisubharmonic (T + c k • ω.form).val (fun x => ⨅ i, φ i x) := by
    intro k
    have hcpos : 0 < c k := by positivity
    obtain ⟨i, hi⟩ := (hεlim.eventually (gt_mem_nhds hcpos)).exists
    exact (isThetaPshPotential_perturb_mono ω hi.le (hall i)).1
  have hcanti : Antitone c := by
    intro a b hab
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hab 1
  have hclim : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨thetaPlurisubharmonic_of_forall_add_smul hcanti hclim hc,
    (hall (Classical.arbitrary I)).2⟩

omit [Preorder I] [IsDirectedOrder I] [MeasurableSpace M] [BorelSpace M] in
/-- `prop:vol_limit_model`, `P_θ[φ] = φ`. -/
theorem iInf_singularityEnvelope_eq (hε0 : ∀ i, 0 ≤ ε i)
    (hφ : ∀ i, IsThetaPshPotential (T + ε i • ω.form).val (φ i))
    (hfix : ∀ i, singularityEnvelope (T + ε i • ω.form).val (φ i) = φ i)
    (hinf : IsThetaPshPotential T.val (fun x => ⨅ i, φ i x)) :
    singularityEnvelope T.val (fun x => ⨅ i, φ i x) = fun x => ⨅ i, φ i x := by
  apply le_antisymm
  · intro x
    refine le_iInf fun i => ?_
    have h1 := singularityEnvelope_perturb_mono ω (T := T) (hε0 i) (fun x => ⨅ i, φ i x)
    simp only [zero_smul, add_zero] at h1
    calc singularityEnvelope T.val (fun x => ⨅ i, φ i x) x
        ≤ singularityEnvelope (T + ε i • ω.form).val (fun x => ⨅ i, φ i x) x := h1 x
      _ ≤ singularityEnvelope (T + ε i • ω.form).val (φ i) x :=
        singularityEnvelope_mono (MoreSingularOn.of_le fun y _ => iInf_le (fun i => φ i y) i) x
      _ = φ i x := by rw [hfix i]
  · exact self_le_singularityEnvelope hinf fun x =>
      (iInf_le (fun i => φ i x) (Classical.arbitrary I)).trans
        ((fixedPoint_zero_and_nonpos ω T hφ hfix _).2 x)

/-- `prop:vol_limit_model`, equation `eq:massmodeldec`: the masses converge. -/
theorem tendsto_diagonalPotentialMass_iInf (hε0 : ∀ i, 0 ≤ ε i) (hεanti : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0)) (hφanti : Antitone φ)
    (hφ : ∀ i, IsThetaPshPotential (T + ε i • ω.form).val (φ i))
    (hfix : ∀ i, singularityEnvelope (T + ε i • ω.form).val (φ i) = φ i)
    (hinf : IsThetaPshPotential T.val (fun x => ⨅ i, φ i x)) :
    Tendsto (fun i => diagonalPotentialMass (T + ε i • ω.form) (φ i) (hφ i)) atTop
      (𝓝 (diagonalPotentialMass T (fun x => ⨅ i, φ i x) hinf)) := by
  set u : M → EReal := fun x => ⨅ i, φ i x with hu_def
  set m : I → ℝ≥0∞ := fun i => diagonalPotentialMass (T + ε i • ω.form) (φ i) (hφ i) with hm_def
  have hall := fun i₀ => (tail_isThetaPshPotential_and_L1 ω T hεanti hφanti hφ hfix i₀).1
  have hu0 : IsThetaPshPotential (T + (0 : ℝ) • ω.form).val u := by
    simpa only [zero_smul, add_zero] using hinf
  -- the lower bound
  have hlow : ∀ i, diagonalPotentialMass T u hinf ≤ m i := by
    intro i
    calc diagonalPotentialMass T u hinf
        = diagonalPotentialMeasure (T + (0 : ℝ) • ω.form) u hu0 univ := by
          unfold diagonalPotentialMass
          rw [diagonalPotentialMeasure_congr (by simp only [zero_smul, add_zero]) rfl hinf hu0]
      _ ≤ diagonalPotentialMeasure (T + ε i • ω.form) u (hall i) univ :=
          diagonalPotentialMeasure_le_of_le ω (hε0 i) hu0 (hall i) univ
      _ ≤ m i := diagonalPotentialMass_mono_of_kahler ω (hall i) (hφ i)
          (MoreSingularOn.of_le fun y _ => iInf_le (fun i => φ i y) i)
  -- the upper bound, for every tail
  have hupper : ∀ i₀, limsup m atTop ≤
      diagonalPotentialMass (T + ε i₀ • ω.form) u (hall i₀) := by
    intro i₀
    have hJ : ∀ j : Ici i₀, IsThetaPshPotential (T + ε i₀ • ω.form).val (φ j) := fun j =>
      isThetaPshPotential_perturb_mono ω (hεanti j.2) (hφ j)
    have hcontact : ∀ j : Ici i₀, m j ≤
        diagonalPotentialMeasure (T + ε i₀ • ω.form) (φ j) (hJ j) {x | φ j x = 0} := by
      intro j
      have hP : IsThetaPshPotential (T + ε j • ω.form).val
          (singularityEnvelope (T + ε j • ω.form).val (φ j)) := by
        rw [hfix j]
        exact hφ j
      have hc := SingularityEnvelopeContact.diagonalPotentialMeasure_singularityEnvelope_lt_zero
        ω (T + ε j • ω.form) (hφ j) hP
      rw [diagonalPotentialMeasure_congr rfl (hfix j) hP (hφ j)] at hc
      rw [hfix j] at hc
      have hsplit : (univ : Set M) ⊆ {x | φ j x < 0} ∪ {x | φ j x = 0} := by
        intro x _
        rcases ((fixedPoint_zero_and_nonpos ω T hφ hfix j).2 x).lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr h
      calc m j = diagonalPotentialMeasure (T + ε j • ω.form) (φ j) (hφ j) univ := rfl
        _ ≤ diagonalPotentialMeasure (T + ε j • ω.form) (φ j) (hφ j)
              ({x | φ j x < 0} ∪ {x | φ j x = 0}) := measure_mono hsplit
        _ ≤ diagonalPotentialMeasure (T + ε j • ω.form) (φ j) (hφ j) {x | φ j x < 0} +
            diagonalPotentialMeasure (T + ε j • ω.form) (φ j) (hφ j) {x | φ j x = 0} :=
              measure_union_le _ _
        _ = diagonalPotentialMeasure (T + ε j • ω.form) (φ j) (hφ j) {x | φ j x = 0} := by
              rw [hc, zero_add]
        _ ≤ _ := diagonalPotentialMeasure_le_of_le ω (hεanti j.2) _ _ _
    -- upper semicontinuity of the contact mass along the L¹-convergent tail
    let Θ : AtlasClosedRealOneOneForm (ofFixedModel n M) :=
      nativeClosedFormToAtlas (T + ε i₀ • ω.form)
    have hround : atlasClosedFormToNative Θ = T + ε i₀ • ω.form :=
      sourceNativeAtlasForm_roundTrip _
    have hsJ : ∀ j : Ici i₀, (ofFixedModel n M).IsThetaPSH Θ (φ j) := fun j =>
      (isThetaPSH_iff_nativeThetaPotential _ _).mpr (by rw [hround]; exact hJ j)
    have hsu : (ofFixedModel n M).IsThetaPSH Θ u :=
      (isThetaPSH_iff_nativeThetaPotential _ _).mpr (by rw [hround]; exact hall i₀)
    have hlim := sourceZeroContactMass_limsup_net ω (θ := Θ) hsJ
      (fun j => (fixedPoint_zero_and_nonpos ω T hφ hfix j).2) hsu
      (tail_isThetaPshPotential_and_L1 ω T hεanti hφanti hφ hfix i₀).2
    have hzc : ∀ j : Ici i₀, sourceZeroContactMass Θ (φ j) (hsJ j) =
        diagonalPotentialMeasure (T + ε i₀ • ω.form) (φ j) (hJ j) {x | φ j x = 0} := by
      intro j
      exact congrArg (fun μ : Measure M => μ {x | φ j x = 0})
        (diagonalPotentialMeasure_congr hround rfl _ _)
    have hzu : sourceZeroContactMass Θ u hsu =
        diagonalPotentialMeasure (T + ε i₀ • ω.form) u (hall i₀) {x | u x = 0} :=
      congrArg (fun μ : Measure M => μ {x | u x = 0})
        (diagonalPotentialMeasure_congr hround rfl _ _)
    simp only [hzc, hzu] at hlim
    calc limsup m atTop = limsup (fun j : Ici i₀ => m j) atTop := by
          rw [← map_val_Ici_atTop i₀]
          rfl
      _ ≤ limsup (fun j : Ici i₀ => diagonalPotentialMeasure (T + ε i₀ • ω.form) (φ j) (hJ j)
            {x | φ j x = 0}) atTop :=
          limsup_le_limsup (Eventually.of_forall hcontact)
      _ ≤ diagonalPotentialMeasure (T + ε i₀ • ω.form) u (hall i₀) {x | u x = 0} := hlim
      _ ≤ diagonalPotentialMass (T + ε i₀ • ω.form) u (hall i₀) := measure_mono (subset_univ _)
  -- continuity of the mass of the fixed potential `u` in the background
  obtain ⟨K, hK, hle⟩ := exists_diagonalPotentialMass_add_smul_le ω hinf
  have hbound : ∀ i₀, ε i₀ ≤ 1 → diagonalPotentialMass (T + ε i₀ • ω.form) u (hall i₀) ≤
      diagonalPotentialMass T u hinf + ENNReal.ofReal (ε i₀) * K := by
    intro i₀ h1
    rcases (hε0 i₀).eq_or_lt with h | h
    · have he : diagonalPotentialMass (T + ε i₀ • ω.form) u (hall i₀) =
          diagonalPotentialMass T u hinf := by
        unfold diagonalPotentialMass
        rw [diagonalPotentialMeasure_congr (by rw [← h, zero_smul, add_zero]) rfl (hall i₀) hinf]
      rw [he]
      exact le_self_add
    · exact hle (ε i₀) h h1 (hall i₀)
  have hT : Tendsto (fun i => diagonalPotentialMass T u hinf + ENNReal.ofReal (ε i) * K) atTop
      (𝓝 (diagonalPotentialMass T u hinf)) := by
    have h1 : Tendsto (fun i => ENNReal.ofReal (ε i)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hεlim
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hK.ne)
    simpa using tendsto_const_nhds.add h2
  have hlimsup : limsup m atTop ≤ diagonalPotentialMass T u hinf := by
    refine ge_of_tendsto hT ?_
    filter_upwards [hεlim.eventually (ge_mem_nhds one_pos)] with i₀ hi₀
    exact (hupper i₀).trans (hbound i₀ hi₀)
  exact tendsto_of_le_liminf_of_limsup_le (le_liminf_of_le (by isBoundedDefault)
    (Eventually.of_forall hlow)) hlimsup

end Nets

end SGPT.Envelopes.PerturbedModelLimit

namespace SGPT.PSH.VariableComplexAtlas

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending DiagonalMass
open SGPT.Envelopes.PerturbedModelLimit

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Source `prop:vol_limit_model`, the model clause and equation `eq:massmodeldec`.
Let `ω` be a Kähler form, `(ε_i)` a decreasing net in `ℝ_{≥0}` with limit `0`, and
`(φ_i)` a decreasing net with `φ_i ∈ PSH(X, θ + ε_i ω)` and
`P_{θ + ε_i ω}[φ_i] = φ_i`. Then `φ = inf_i φ_i ∈ PSH(X,θ)`, `P_θ[φ] = φ` and
`∫_X (θ + ε_i ω)^n_{φ_i} → ∫_X θ_φ^n`. -/
theorem sourcePerturbedModel_iInf (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {ε : I → ℝ} (hε0 : ∀ i, 0 ≤ ε i) (hεanti : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {φ : I → M → EReal} (hφanti : Antitone φ)
    (hφ : ∀ i, (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + ε i • ω.form)) (φ i))
    (hfix : ∀ i, sourceSingularityEnvelope
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + ε i • ω.form)) (φ i) = φ i) :
    ∃ hinf : (ofFixedModel n M).IsThetaPSH θ (fun x => ⨅ i, φ i x),
      sourceSingularityEnvelope θ (fun x => ⨅ i, φ i x) = (fun x => ⨅ i, φ i x) ∧
      Tendsto (fun i => sourcePotentialNonPluripolarMeasure
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + ε i • ω.form)) (φ i) (hφ i) univ)
        atTop (𝓝 (sourcePotentialNonPluripolarMeasure θ (fun x => ⨅ i, φ i x) hinf univ)) := by
  set T := atlasClosedFormToNative θ with hTdef
  have hφn : ∀ i, IsThetaPshPotential (T + ε i • ω.form).val (φ i) := by
    intro i
    have h := (isThetaPSH_iff_nativeThetaPotential _ _).mp (hφ i)
    rwa [sourceNativeAtlasForm_roundTrip] at h
  have hfixn : ∀ i, singularityEnvelope (T + ε i • ω.form).val (φ i) = φ i := by
    intro i
    have h := hfix i
    rwa [sourceSingularityEnvelope_eq_native, sourceNativeAtlasForm_roundTrip] at h
  have hinfn := iInf_isThetaPshPotential ω T hεanti hεlim hφanti hφn hfixn
  refine ⟨(isThetaPSH_iff_nativeThetaPotential θ _).mpr hinfn, ?_, ?_⟩
  · rw [sourceSingularityEnvelope_eq_native]
    exact iInf_singularityEnvelope_eq ω T hε0 hφn hfixn hinfn
  · have h := tendsto_diagonalPotentialMass_iInf ω T hε0 hεanti hεlim hφanti hφn hfixn hinfn
    have he : (fun i => sourcePotentialNonPluripolarMeasure
        (nativeClosedFormToAtlas (T + ε i • ω.form)) (φ i) (hφ i) univ) =
        fun i => diagonalPotentialMass (T + ε i • ω.form) (φ i) (hφn i) := by
      funext i
      exact congrArg (fun μ : Measure M => μ univ)
        (diagonalPotentialMeasure_congr (sourceNativeAtlasForm_roundTrip _) rfl _ _)
    rw [he]
    exact h

/-- Source `cor:varphiperturbtheta`: a model potential `φ ∈ PSH(X,θ)_{>0}` is the
infimum over `ε > 0` of its envelopes `P_{θ + ε ω}[φ]`. -/
theorem sourceModelPotential_eq_iInf_perturbedEnvelope (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) :
    φ = fun x => ⨅ ε : {ε : ℝ // 0 < ε}, sourceSingularityEnvelope
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + ε.1 • ω.form)) φ x := by
  obtain ⟨hφs, hfix, hpos⟩ := hφ
  set T := atlasClosedFormToNative θ with hTdef
  have hφn : IsThetaPshPotential T.val φ := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφs
  have hfixn : singularityEnvelope T.val φ = φ := by
    have h := hfix.symm
    rwa [sourceSingularityEnvelope_eq_native] at h
  have hposn : 0 < diagonalPotentialMass T φ hφn := hpos
  -- the sequence `c_k = 1/(k+1)` of perturbations and the envelopes `ψ_k`
  let c : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hcpos : ∀ k, 0 < c k := fun k => by positivity
  have hcanti : Antitone c := by
    intro a b hab
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hab 1
  have hclim : Tendsto c atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hφc : ∀ k, IsThetaPshPotential (T + c k • ω.form).val φ := fun k =>
    LocalPotentials.isThetaPshPotential_add_of_semipositive hφn
      (KahlerDomination.isSemipositive_smul ω.isSemipositive (hcpos k).le)
  let ψ : ℕ → M → EReal := fun k => singularityEnvelope (T + c k • ω.form).val φ
  have hψ : ∀ k, IsThetaPshPotential (T + c k • ω.form).val (ψ k) := fun k =>
    FirstPass.singularityEnvelope_isThetaPshPotential _ (T + c k • ω.form).2.1
      (T + c k • ω.form).2.2
      (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ (hφc k)
  have hposc : ∀ k, HasPositivePotentialMass (T + c k • ω.form) φ (hφc k) := fun k =>
    lt_of_lt_of_le hposn
      (AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul ω.isSemipositive
        (hcpos k) hφn (hφc k))
  have hψfix : ∀ k, singularityEnvelope (T + c k • ω.form).val (ψ k) = ψ k := fun k =>
    RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass ω
      (T + c k • ω.form) φ (hφc k) (hposc k)
  have hψanti : Antitone ψ := fun a b hab =>
    singularityEnvelope_perturb_mono ω (hcanti hab) φ
  -- the infimum `η`
  have hηn := iInf_isThetaPshPotential ω T hcanti hclim hψanti hψ hψfix
  set η : M → EReal := fun x => ⨅ k, ψ k x with hηdef
  have hmassη := tendsto_diagonalPotentialMass_iInf ω T (fun k => (hcpos k).le) hcanti hclim
    hψanti hψ hψfix hηn
  have hmassφ := TraceFreeLimit.tendsto_diagonalPotentialMass_add_smul ω hφn hcpos hclim hφc
  have hmass_eq : ∀ k, diagonalPotentialMass (T + c k • ω.form) (ψ k) (hψ k) =
      diagonalPotentialMass (T + c k • ω.form) φ (hφc k) := fun k =>
    singularityEnvelopeMassPreserving ω (T + c k • ω.form) φ (hφc k) (hψ k)
  simp only [hmass_eq] at hmassη
  have hmass : diagonalPotentialMass T φ hφn = diagonalPotentialMass T η hηn :=
    tendsto_nhds_unique hmassφ hmassη
  -- `φ ≤ η ≤ 0`
  have hφη : φ ≤ η := by
    intro x
    refine le_iInf fun k => ?_
    have h := singularityEnvelope_perturb_mono ω (T := T) (hcpos k).le φ
    simp only [zero_smul, add_zero] at h
    calc φ x = singularityEnvelope T.val φ x := by rw [hfixn]
      _ ≤ ψ k x := h x
  have hη0 : η ≤ 0 := fun x =>
    (iInf_le (fun k => ψ k x) 0).trans (singularityEnvelope_le_zero _ _ x)
  -- the equal-mass characterization gives `η ≤ P_θ[φ] = φ`
  have hηφ : η ≤ φ := by
    have h := equalMassLeSingularityEnvelope ω T φ η hφn hηn hposn hη0
      (MoreSingularOn.of_le fun x _ => hφη x) hmass
    rwa [hfixn] at h
  -- the infimum over all `ε > 0` is the infimum over the sequence
  funext x
  apply le_antisymm
  · refine le_iInf fun ε => ?_
    rw [sourceSingularityEnvelope_eq_native, sourceNativeAtlasForm_roundTrip]
    have h := singularityEnvelope_perturb_mono ω (T := T) ε.2.le φ
    simp only [zero_smul, add_zero] at h
    calc φ x = singularityEnvelope T.val φ x := by rw [hfixn]
      _ ≤ _ := h x
  · refine le_trans ?_ (hηφ x)
    refine le_iInf fun k => ?_
    refine (iInf_le _ ⟨c k, hcpos k⟩).trans ?_
    rw [sourceSingularityEnvelope_eq_native, sourceNativeAtlasForm_roundTrip]

end SGPT.PSH.VariableComplexAtlas
