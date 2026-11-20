import SGPT.Bergman.SourcePartialEnvelopePOrder
import SGPT.PSH.SourceGlobalPluripolarPole
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMaximumOrders
import SGPT.Envelopes.SourceGlobalPRelativeEnvelope
import SGPT.PSH.SourceIEnvelopeMonotonicity
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds
import SGPT.PSH.Pluripolar
import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive
import SGPT.Envelopes.SourcePositiveMassCurrents
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingGlobalAE
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence

/-! Exact frozen new11 tail only; canonical import/private/production acceptance pending. -/

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology
set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.PartialEnvelopeEverywhere

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialPOrder
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open scoped Topology Classical

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem genuine_add {T S : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential T.val u) (hv : IsThetaPshPotential S.val v) :
    IsThetaPshPotential (T + S).val (fun x => u x + v x) := by
  let α : Bool → ClosedRealOneOneForm n M := fun b => if b then T else S
  let p : Bool → M → EReal := fun b => if b then u else v
  have hp (b : Bool) : IsThetaPshPotential (α b).val (p b) := by
    cases b
    · exact hv
    · exact hu
  have h := MixedSummandCapacityDomination.isThetaPshPotential_sumPot
    (T := Finset.univ) (w := fun _ : Bool => (1 : ℝ)) Finset.univ_nonempty
    (fun _ => zero_lt_one) hp
  have heq : GlobalMultilinearExpansion.sumPot Finset.univ (fun _ : Bool => (1 : ℝ)) p =
      fun x => u x + v x := by
    funext x
    simp only [GlobalMultilinearExpansion.sumPot, Fintype.sum_bool, p,
      Bool.false_eq_true, ↓reduceIte, EReal.coe_one, one_mul]
  rw [heq] at h
  simpa only [GlobalMultilinearExpansion.sumForm, Fintype.sum_bool, α,
    Bool.false_eq_true, ↓reduceIte, one_smul] using h

private theorem ereal_convex_self {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : EReal) :
    (t : EReal) * a + ((1 - t : ℝ) : EReal) * a = a := by
  induction a with
  | bot => simp only [EReal.coe_mul_bot_of_pos ht0,
      EReal.coe_mul_bot_of_pos (sub_pos.mpr ht1), EReal.bot_add]
  | top => simp only [EReal.coe_mul_top_of_pos ht0,
      EReal.coe_mul_top_of_pos (sub_pos.mpr ht1), EReal.top_add_top]
  | coe a =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

def everywhereCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) :=
  {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
    (∀ x : K, v x.val ≤ f x) ∧ SGPT.PSH.SingularityLE v φ}

def positiveEverywhereCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) :=
  {v : everywhereCompetitors θ φ K f //
    0 < sourcePotentialNonPluripolarMeasure θ v.val v.property.1 univ}

def everywherePCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) :=
  {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
    (∀ x : K, v x.val ≤ f x) ∧ GlobalPComparison.sourcePOrder (n := n) v φ}

def positiveEverywherePCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) :=
  {v : everywherePCompetitors θ φ K f //
    0 < sourcePotentialNonPluripolarMeasure θ v.val v.property.1 univ}

/-- Actual positive theta-mass and actual ambient local PP manufacture a
genuine positive lower theta-potential with EVERY prescribed pole internally. -/
theorem exists_positive_pole_minorant (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {η : M → EReal}
    (hη : (ofFixedModel n M).IsThetaPSH θ η)
    (hηpos : 0 < sourcePotentialNonPluripolarMeasure θ η hη univ)
    {S : Set M} (hS : (ofFixedModel n M).LocallyPluripolar S) :
    ∃ χ : M → EReal, ∃ hχ : (ofFixedModel n M).IsThetaPSH θ χ,
      0 < sourcePotentialNonPluripolarMeasure θ χ hχ univ ∧
        χ ≤ η ∧ ∀ x ∈ S, χ x = ⊥ := by
  obtain ⟨q, hq, _hqQ, hq0, hqS⟩ :=
    SGPT.PSH.GlobalPluripolarPole.source_exists_nonpositive_global_pluripolar_pole ω hS
  obtain ⟨δ, hδ, s, _hs, hstrict, hsη⟩ := sourcePositiveMass_strictMinorant ω hη hηpos
  let T := atlasClosedFormToNative θ
  let a : ℝ := δ / 2
  have ha : 0 < a := div_pos hδ (by norm_num)
  have hsn : IsThetaPshPotential (T - δ • ω.form).val s := by
    have h := (isThetaPSH_iff_nativeThetaPotential _ s).mp hstrict
    simpa only [sourceNativeAtlasForm_roundTrip] using h
  have hqn : IsThetaPshPotential ω.form.val q := by
    have h := (isThetaPSH_iff_nativeThetaPotential _ q).mp hq
    simpa only [sourceNativeAtlasForm_roundTrip] using h
  have haq := RestrictedApproximantComparison.isThetaPshPotential_smul hqn ha
  let χ : M → EReal := fun x => s x + (a : EReal) * q x
  have hχstrict : IsThetaPshPotential (T - a • ω.form).val χ := by
    have h := genuine_add hsn haq
    have hforms : (T - δ • ω.form) + a • ω.form = T - a • ω.form := by
      dsimp only [a]
      module
    rw [hforms] at h
    exact h
  have hχn : IsThetaPshPotential T.val χ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hχstrict
      (KahlerDomination.isSemipositive_smul ω.isSemipositive ha.le)
    simpa only [sub_add_cancel] using h
  have hχ : (ofFixedModel n M).IsThetaPSH θ χ :=
    (isThetaPSH_iff_nativeThetaPotential θ χ).mpr hχn
  have hχpos : 0 < sourcePotentialNonPluripolarMeasure θ χ hχ univ := by
    have h := SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul ω hχstrict ha
    simpa only [DiagonalMass.HasPositivePotentialMass, DiagonalMass.diagonalPotentialMass,
      sourcePotentialNonPluripolarMeasure, sub_add_cancel] using h
  have hχs : χ ≤ s := by
    intro x
    have hneg : (a : EReal) * q x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr ha.le) (hq0 x)
    simpa only [add_zero] using add_le_add (le_refl (s x)) hneg
  refine ⟨χ, hχ, hχpos, hχs.trans hsη, ?_⟩
  intro x hx
  change s x + (a : EReal) * q x = ⊥
  rw [hqS x hx, EReal.coe_mul_bot_of_pos ha, EReal.add_bot]

omit [ConnectedSpace M] in
/-- Existing actual monotone/global-volume AE PSH reconstruction proves the
SAME literal mixed supremum equals eta; pointwise convergence at extra poles
is neither assumed nor asserted, and no finite-energy/model premise is used. -/
theorem currentMinorant_uscSup_eq (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {η χ : M → EReal}
    (hη : (ofFixedModel n M).IsThetaPSH θ η) (hχ : (ofFixedModel n M).IsThetaPSH θ χ)
    (hχη : χ ≤ η) : uscSup (sourceCurrentMinorant η χ) = η := by
  have hg (j : ℕ) := sourceCurrentMinorant_genuine hη hχ j
  have hm := sourceCurrentMinorant_mono hη hχη
  have hl := sourceCurrentMinorant_ae_tendsto ω hη hχ
  rw [sourceKahlerVolume_eq_native] at hl
  have heq := SingularModelEnergyIncreasingGlobalAE.uscRegularization_iSup_eq_of_directed_monotone_ae_kahlerVolume
    ω (fun j => (isThetaPSH_iff_nativeThetaPotential θ _).mp (hg j))
      ((isThetaPSH_iff_nativeThetaPotential θ η).mp hη)
      (fun x j k hjk => hm hjk x) hl
  have hfn : (⨆ j, sourceCurrentMinorant η χ j) = fun x => ⨆ j, sourceCurrentMinorant η χ j x := by
    funext x
    exact iSup_apply
  rw [hfn] at heq
  exact heq

/-- The original natural positive/QE candidate produces an ACTUAL positive
everywhere approximation family and its genuine regularized recovery identity. -/
theorem exists_everywhere_positive_approximants (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {η : M → EReal}
    (hη : (ofFixedModel n M).IsThetaPSH θ η)
    (hηpos : 0 < sourcePotentialNonPluripolarMeasure θ η hη univ)
    {K : Set M} {f : K → EReal} (hK : partialObstacle (n := n) K f η) :
    ∃ u : ℕ → M → EReal, ∃ hu : ∀ j, (ofFixedModel n M).IsThetaPSH θ (u j),
      (∀ j, 0 < sourcePotentialNonPluripolarMeasure θ (u j) (hu j) univ) ∧
        (∀ j, u j ≤ η) ∧ (∀ j, ∀ x : K, u j x.val ≤ f x) ∧ uscSup u = η := by
  obtain ⟨S, hS, hηK⟩ := (partialObstacle_iff_exists_pluripolar K f η).mp hK
  obtain ⟨χ, hχ, hχpos, hχη, hχS⟩ := exists_positive_pole_minorant ω hη hηpos hS
  let u := sourceCurrentMinorant η χ
  have hu (j : ℕ) : (ofFixedModel n M).IsThetaPSH θ (u j) :=
    sourceCurrentMinorant_genuine hη hχ j
  have hlo (j : ℕ) : χ ≤ u j := by
    have hw := sourceCurrentMinorant_weights j
    intro x
    calc
      χ x = (((j : ℝ) + 2)⁻¹ : EReal) * χ x +
          ((1 - ((j : ℝ) + 2)⁻¹ : ℝ) : EReal) * χ x := (ereal_convex_self hw.1 hw.2 _).symm
      _ ≤ u j x := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hχη x) (EReal.coe_nonneg.mpr (sub_pos.mpr hw.2).le))
  have hup (j : ℕ) : u j ≤ η := by
    have hw := sourceCurrentMinorant_weights j
    intro x
    calc
      u j x ≤ (((j : ℝ) + 2)⁻¹ : EReal) * η x +
          ((1 - ((j : ℝ) + 2)⁻¹ : ℝ) : EReal) * η x := add_le_add
        (mul_le_mul_of_nonneg_left (hχη x) (EReal.coe_nonneg.mpr hw.1.le)) le_rfl
      _ = η x := ereal_convex_self hw.1 hw.2 _
  have hpos (j : ℕ) : 0 < sourcePotentialNonPluripolarMeasure θ (u j) (hu j) univ :=
    hχpos.trans_le (sourcePotentialNonPluripolarMass_mono ω hχ (hu j)
      (MoreSingularOn.of_le fun x _ => hlo j x))
  have huf (j : ℕ) (x : K) : u j x.val ≤ f x := by
    by_cases hx : x.val ∈ S
    · change (((j : ℝ) + 2)⁻¹ : EReal) * χ x.val +
        ((1 - ((j : ℝ) + 2)⁻¹ : ℝ) : EReal) * η x.val ≤ f x
      rw [hχS x.val hx]
      have hpole : (((j : ℝ) + 2)⁻¹ : EReal) * (⊥ : EReal) = ⊥ :=
        EReal.coe_mul_bot_of_pos (sourceCurrentMinorant_weights j).1
      rw [hpole, EReal.bot_add]
      exact bot_le
    · exact (hup j x.val).trans (hηK x hx)
  exact ⟨u, hu, hpos, hup, huf, currentMinorant_uscSup_eq ω hη hχ hχη⟩

/-- WHOLE original lma:PKoutsidepps and eq:PthetaK_new_def, BOTH ordinary
everywhere RHS families, from only original positive reference/lower obstacle. -/
theorem partialEnvelope_eq_everywhere (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ f x) :
    partialEnvelope θ φ K f = uscSup (fun v : everywhereCompetitors θ φ K f => v.val) ∧
      partialEnvelope θ φ K f =
        uscSup (fun v : positiveEverywhereCompetitors θ φ K f => v.val.val) := by
  let H := partialEnvelope θ φ K f
  let A := uscSup (fun v : everywhereCompetitors θ φ K f => v.val)
  let B := uscSup (fun v : positiveEverywhereCompetitors θ φ K f => v.val.val)
  have hAH : A ≤ H := by
    apply uscRegularization_le (upperSemicontinuous_partialEnvelope θ φ K f)
    intro x
    apply iSup_le
    intro v
    exact le_partialEnvelope v.property.1 (partialObstacle_of_forall v.property.2.1) v.property.2.2 x
  have hBA : B ≤ A := by
    apply uscRegularization_mono
    intro x
    apply iSup_le
    intro v
    exact le_iSup (fun w : everywhereCompetitors θ φ K f => w.val x) v.val
  have hHB : H ≤ B := by
    change partialEnvelope θ φ K f ≤ B
    rw [partialEnvelope_eq_positive ω hφ hφpos hf]
    apply uscRegularization_le (upperSemicontinuous_uscRegularization _)
    intro x
    apply iSup_le
    intro v
    obtain ⟨u, hu, hpos, hle, huf, heq⟩ := exists_everywhere_positive_approximants
      ω v.val.property.1 v.property v.val.property.2.1
    have huB (j : ℕ) : u j ≤ B := by
      have hord : SGPT.PSH.SingularityLE (u j) φ :=
        (MoreSingularOn.of_le (fun y _ => hle j y)).trans v.val.property.2.2
      intro y
      exact (le_iSup (fun w : positiveEverywhereCompetitors θ φ K f => w.val.val y)
        ⟨⟨u j, hu j, huf j, hord⟩, hpos j⟩).trans
          (le_uscRegularization (fun z => ⨆ w : positiveEverywhereCompetitors θ φ K f, w.val.val z) y)
    have hs : uscSup u ≤ B := uscRegularization_le (upperSemicontinuous_uscRegularization _)
      (fun y => iSup_le fun j => huB j y)
    exact (heq.symm.le.trans hs) x
  exact ⟨le_antisymm (hHB.trans hBA) hAH, le_antisymm hHB (hBA.trans hAH)⟩

/-- ALL FOUR full original cor:partial_P_new_def identities, keeping the
already verified first two QE identities and actually proving both remaining
EVERYWHERE identities by the genuine approximation family (not one minorant). -/
theorem partialEnvelope_globalP_full_descriptions (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ f x) :
    partialEnvelope θ φ K f = uscSup (fun v : partialPCompetitors θ φ K f => v.val) ∧
      partialEnvelope θ φ K f = uscSup (fun v : positivePartialPCompetitors θ φ K f => v.val.val) ∧
      partialEnvelope θ φ K f = uscSup (fun v : everywherePCompetitors θ φ K f => v.val) ∧
      partialEnvelope θ φ K f = uscSup (fun v : positiveEverywherePCompetitors θ φ K f => v.val.val) := by
  obtain ⟨hQE, hQEpos⟩ := partialEnvelope_globalP_qe_descriptions ω hφ hφpos hf
  let H := partialEnvelope θ φ K f
  let A := uscSup (fun v : everywherePCompetitors θ φ K f => v.val)
  let B := uscSup (fun v : positiveEverywherePCompetitors θ φ K f => v.val.val)
  have hAH : A ≤ H := by
    change A ≤ partialEnvelope θ φ K f
    rw [hQE]
    apply uscRegularization_mono
    intro x
    apply iSup_le
    intro v
    exact le_iSup (fun w : partialPCompetitors θ φ K f => w.val x)
      ⟨v.val, v.property.1, partialObstacle_of_forall v.property.2.1, v.property.2.2⟩
  have hBA : B ≤ A := by
    apply uscRegularization_mono
    intro x
    apply iSup_le
    intro v
    exact le_iSup (fun w : everywherePCompetitors θ φ K f => w.val x) v.val
  have hHB : H ≤ B := by
    change partialEnvelope θ φ K f ≤ B
    rw [hQEpos]
    apply uscRegularization_le (upperSemicontinuous_uscRegularization _)
    intro x
    apply iSup_le
    intro v
    obtain ⟨u, hu, hpos, hle, huf, heq⟩ := exists_everywhere_positive_approximants
      ω v.val.property.1 v.property v.val.property.2.1
    have huB (j : ℕ) : u j ≤ B := by
      have huη : GlobalPComparison.sourcePOrder (n := n) (u j) v.val.val :=
        GlobalPComparison.sourcePOrder_of_moreSingular ω
          ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hu j)).quasiPshPotential
          ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.val.property.1).quasiPshPotential
          (MoreSingularOn.of_le fun y _ => hle j y)
      have huφ : GlobalPComparison.sourcePOrder (n := n) (u j) φ :=
        GlobalPComparison.sourcePOrder_trans ω huη v.val.property.2.2
      intro y
      exact (le_iSup (fun w : positiveEverywherePCompetitors θ φ K f => w.val.val y)
        ⟨⟨u j, hu j, huf j, huφ⟩, hpos j⟩).trans
          (le_uscRegularization (fun z => ⨆ w : positiveEverywherePCompetitors θ φ K f, w.val.val z) y)
    have hs : uscSup u ≤ B := uscRegularization_le (upperSemicontinuous_uscRegularization _)
      (fun y => iSup_le fun j => huB j y)
    exact (heq.symm.le.trans hs) x
  exact ⟨hQE, hQEpos, le_antisymm (hHB.trans hBA) hAH, le_antisymm hHB (hBA.trans hAH)⟩

end SGPT.Bergman.PartialEnvelopeEverywhere
