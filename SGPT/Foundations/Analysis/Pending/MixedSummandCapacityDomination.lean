import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
import SGPT.Foundations.Analysis.Pending.ThetaCapacity
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

set_option autoImplicit false

/-!
# Actual mixed summands are dominated by diagonal relative capacity

Lu, arXiv:2005.04264v1, Lemma 4.1 Step 1.2. Extract a genuine positive
summand from the full actual multilinear expansion, then apply the proved
relative-capacity bound to the actual finite positive combination.
The common coalescing reference and comparison to zero-reference capacity
remain separate producers.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination

open FirstPass FirstPass.PositiveClasses
open GlobalNonPluripolar GlobalMultilinearExpansion ThetaCapacity DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {iota : Type*} [DecidableEq iota]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [DecidableEq iota] in
/-- A finite positive sum is genuine: the finite union of its summands' pole
sets is locally pluripolar and cannot contain any nonempty open set. -/
theorem isThetaPshPotential_sumPot
    {T : Finset iota} (hT : T.Nonempty) {w : iota → ℝ} (hw : ∀ i, 0 < w i)
    {alpha : iota → ClosedRealOneOneForm n M} {f : iota → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (alpha i).val (f i)) :
    IsThetaPshPotential (sumForm T w alpha).val (sumPot T w f) := by
  refine ⟨thetaPlurisubharmonic_sumPot hT hw (fun i => (hf i).1), ?_⟩
  apply ThetaPshConvexCombination.locallyNondegenerate_of_poles_pluripolar (n := n)
  have hpolar : ManifoldLocallyPluripolar (n := n) (⋃ i ∈ T, {x | f i x = ⊥}) := by
    induction hT using Finset.Nonempty.cons_induction with
    | singleton a =>
      simpa using
        quasiPsh_poles_manifoldLocallyPluripolar (hf a).quasiPshPotential
    | cons a S ha hS ih =>
      have heq : (⋃ i ∈ Finset.cons a S ha, {x | f i x = ⊥}) =
          {x | f a x = ⊥} ∪ ⋃ i ∈ S, {x | f i x = ⊥} := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_cons, Set.mem_union, Set.mem_ofPred_eq]
        aesop
      rw [heq]
      exact manifoldLocallyPluripolar_union
        (quasiPsh_poles_manifoldLocallyPluripolar (hf a).quasiPshPotential) ih
  exact hpolar.mono (sumPot_poles_subset hw)

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [DecidableEq iota] in
/-- Adding real constants to the summands adds their weighted real sum,
including at poles. -/
theorem sumPot_add_const {T : Finset iota} {w : iota → ℝ} (hw : ∀ i, 0 < w i)
    (f : iota → M → EReal) (B : iota → ℝ) (x : M) :
    sumPot T w (fun i y => f i y + (B i : EReal)) x =
      sumPot T w f x + ((∑ i ∈ T, w i * B i : ℝ) : EReal) := by
  simp only [sumPot]
  simp_rw [ThetaPshConvexCombination.coe_mul_add_coe (hw _)]
  rw [Finset.sum_add_distrib]
  congr 1
  induction T using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => simp only [Finset.sum_cons, ih, EReal.coe_add]

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [DecidableEq iota] in
/-- A positive weighted sum preserves pointwise order. -/
theorem sumPot_mono {T : Finset iota} {w : iota → ℝ} (hw : ∀ i, 0 < w i)
    {f g : iota → M → EReal} (hfg : ∀ i, f i ≤ g i) :
    sumPot T w f ≤ sumPot T w g := by
  intro x
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hfg i x) (EReal.coe_nonneg.mpr (hw i).le)

/-- Every actual selected positive mixed summand is bounded by the diagonal
measure of the actual positive combination. -/
theorem selectedMixedMeasure_le_diagonal_sum
    {T : Finset iota} (hT : T.Nonempty) {w : iota → ℝ} (hw : ∀ i, 0 < w i)
    {alpha : iota → ClosedRealOneOneForm n M} {f : iota → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (alpha i).val (f i))
    (s : Fin n → iota) (hs : ∀ j, s j ∈ T) :
    ENNReal.ofReal (∏ j, w (s j)) •
      globalMixedMeasure (fun j => alpha (s j)) (fun j => f (s j)) (fun j => (hf (s j)).1) ≤
    globalMixedMeasure (fun _ => sumForm T w alpha) (fun _ => sumPot T w f)
      (fun _ => thetaPlurisubharmonic_sumPot hT hw (fun i => (hf i).1)) := by
  rw [globalMixedMeasure_diagonal_sumPot hT hw (fun i => (hf i).1)
    (fun i => (hf i).quasiPshPotential)]
  apply Finset.single_le_sum (fun _ _ => (show (0 : Measure M) ≤ _ from bot_le))
  exact Fintype.mem_piFinset.mpr hs

/-- The measure inequality holds on every set; no measurability restriction
on the evaluated set is needed. -/
theorem selectedMixedMeasure_apply_le_diagonal_sum
    {T : Finset iota} (hT : T.Nonempty) {w : iota → ℝ} (hw : ∀ i, 0 < w i)
    {alpha : iota → ClosedRealOneOneForm n M} {f : iota → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (alpha i).val (f i))
    (s : Fin n → iota) (hs : ∀ j, s j ∈ T) (E : Set M) :
    ENNReal.ofReal (∏ j, w (s j)) *
      globalMixedMeasure (fun j => alpha (s j)) (fun j => f (s j)) (fun j => (hf (s j)).1) E ≤
    globalMixedMeasure (fun _ => sumForm T w alpha) (fun _ => sumPot T w f)
      (fun _ => thetaPlurisubharmonic_sumPot hT hw (fun i => (hf i).1)) E := by
  have h := selectedMixedMeasure_le_diagonal_sum hT hw hf s hs E
  simpa only [Measure.smul_apply, smul_eq_mul] using h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [DecidableEq iota] in
/-- Finite distance below a genuine reference makes the raw positive sum
genuine, including its local nondegeneracy at poles. -/
theorem isThetaPshPotential_sum_of_reference_bound
    {T : Finset iota} (hT : T.Nonempty) {w : iota → ℝ} (hw : ∀ i, 0 < w i)
    {alpha : iota → ClosedRealOneOneForm n M} {f : iota → M → EReal}
    (hf : ∀ i, ThetaPlurisubharmonic (alpha i).val (f i))
    {V : M → EReal} (hV : IsThetaPshPotential (sumForm T w alpha).val V)
    {C : ℝ} (hbound : ∀ x, V x ≤ sumPot T w f x + (C : EReal)) :
    IsThetaPshPotential (sumForm T w alpha).val (sumPot T w f) := by
  refine ⟨thetaPlurisubharmonic_sumPot hT hw hf, ?_⟩
  intro x U hU hx
  obtain ⟨y, hy, hVy⟩ := hV.2 x U hU hx
  refine ⟨y, hy, fun hbot => hVy ?_⟩
  have h := hbound y
  rw [hbot, EReal.bot_add] at h
  exact le_bot_iff.mp h

/-- Actual mixed summands are controlled by the relative capacity of a
genuine reference at a uniformly bounded distance from their positive sum. -/
theorem selectedMixedMeasure_apply_le_thetaCapacity
    {T : Finset iota} (hT : T.Nonempty) {w : iota → ℝ} (hw : ∀ i, 0 < w i)
    {alpha : iota → ClosedRealOneOneForm n M} {f : iota → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (alpha i).val (f i))
    (s : Fin n → iota) (hs : ∀ j, s j ∈ T)
    {V : M → EReal} (hV : IsThetaPshPotential (sumForm T w alpha).val V)
    {C : ℝ} (hC : 1 ≤ C) (hle : sumPot T w f ≤ V)
    (hbound : ∀ x, V x ≤ sumPot T w f x + (C : EReal)) (E : Set M) :
    ENNReal.ofReal (∏ j, w (s j)) *
      globalMixedMeasure (fun j => alpha (s j)) (fun j => f (s j)) (fun j => (hf (s j)).1) E ≤
    ENNReal.ofReal (C ^ n) * thetaCapacity (sumForm T w alpha) V E := by
  have hsum := isThetaPshPotential_sum_of_reference_bound hT hw (fun i => (hf i).1) hV hbound
  exact (selectedMixedMeasure_apply_le_diagonal_sum hT hw hf s hs E).trans
    (diagonalPotentialMeasure_le_thetaCapacity_of_bounds hV hsum hC hle hbound E)

/-- One fixed reference controls every selected mixed term in a finite box.
The reference and the capacity bound are produced from the genuine family
and its pointwise bounds, rather than assumed as domination certificates. -/
theorem selectedMixedMeasure_apply_le_capacity_of_box
    {T : Finset iota} (hT : T.Nonempty) {w : iota → ℝ} (hw : ∀ i, 0 < w i)
    {alpha : iota → ClosedRealOneOneForm n M} {f g : iota → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (alpha i).val (f i))
    (hg : ∀ i, IsThetaPshPotential (alpha i).val (g i))
    (hgf : ∀ i, g i ≤ f i) {B : iota → ℝ}
    (hfg : ∀ i x, f i x ≤ g i x + (B i : EReal))
    {C : ℝ} (hC : 1 ≤ C) (hBC : ∑ i ∈ T, w i * B i ≤ C)
    (s : Fin n → iota) (hs : ∀ j, s j ∈ T) (E : Set M) :
    ENNReal.ofReal (∏ j, w (s j)) *
      globalMixedMeasure (fun j => alpha (s j)) (fun j => g (s j)) (fun j => (hg (s j)).1) E ≤
    ENNReal.ofReal (C ^ n) * thetaCapacity (sumForm T w alpha) (sumPot T w f) E := by
  apply selectedMixedMeasure_apply_le_thetaCapacity hT hw hg s hs
    (isThetaPshPotential_sumPot hT hw hf) hC (sumPot_mono hw hgf)
  intro x
  have h := sumPot_mono (T := T) hw hfg x
  rw [sumPot_add_const hw g B x] at h
  exact h.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hBC))

end

end SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
