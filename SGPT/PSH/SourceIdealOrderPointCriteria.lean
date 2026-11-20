import SGPT.PSH.SourceIEnvelope
import SGPT.PSH.SourceGenericLelong
import SGPT.Okounkov.IntrinsicModificationRestriction
import SGPT.Foundations.Analysis.Pending.PositiveIntegerMultiplierOrder
import SGPT.Foundations.Analysis.Pending.RawIntegerPointComparison
import SGPT.Foundations.Analysis.Pending.FiniteConnectedSmoothPrimeIdealOrder
import SGPT.Foundations.Analysis.Pending.LocusProperties
import SGPT.Foundations.Analysis.Pending.GenuineModificationIdealOrderInvariance

/-! Exact first-four-clause support for original prop:Iequivchar2.
No prime-presentation or generated-quotient declaration is included.
The complete five-way proposition retains the separate original prime-class debt.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.PSH.VariableComplexAtlas

open Set
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy
open PositiveIntegerMultiplierOrder SquaredLogLelongSourceNormalization

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

def sourcePositiveIntegerOrder (u v : X → EReal) : Prop :=
  ∀ p : ℕ, 0 < p → ∀ i,
    chartMultiplierIncluded (ofFixedModel n X) u (p : ℝ) v (p : ℝ) i

/-- Fixed-level identity at the SAME positive integer; no universal reindexing. -/
theorem sourcePositiveIntegerOrder_iff_native (u v : X → EReal) :
    sourcePositiveIntegerOrder (n := n) u v ↔ PositiveIntegerIOrder (n := n) u v := Iff.rfl

private theorem genuine_of_sourceQPSH {u : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) : IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ, hθ⟩ := hu
  exact ((isThetaPSH_iff_nativeThetaPotential θ u).mp hθ).quasiPshPotential

/-- Original clauses1 and2 on the full genuine QPSH domain. -/
theorem sourcePositiveIntegerOrder_iff_sourceIOrder {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    sourcePositiveIntegerOrder (n := n) u v ↔ sourceIOrder (ofFixedModel n X) u v := by
  rw [sourcePositiveIntegerOrder_iff_native, sourceIOrder_iff_native hu hv]
  exact positiveIntegerIOrder_iff_iOrder (genuine_of_sourceQPSH hu).1 (genuine_of_sourceQPSH hv)


/-- The original finite smooth-center modification point criterion. -/
def finiteModificationPointComparison (u v : X → EReal) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (π : Y → X), IsBlowupSequence n X Y π → ∀ y : Y,
      (ofFixedModel n Y).sourceLelong (v ∘ π) y ≤ (ofFixedModel n Y).sourceLelong (u ∘ π) y

/-- Every actual proper analytic modification whose source has a genuine
Kähler background is tested; no finite factorization is requested. -/
def kahlerModificationPointComparison (u v : X → EReal) : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (_omegaY : KahlerBackground n Y) (π : Y → X),
    IsAnalyticModification (n := n) π → ∀ y : Y,
      (ofFixedModel n Y).sourceLelong (v ∘ π) y ≤ (ofFixedModel n Y).sourceLelong (u ∘ π) y

theorem sourceIOrder_of_finiteModificationPointComparison {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v)
    (hpoint : finiteModificationPointComparison (n := n) u v) :
    sourceIOrder (ofFixedModel n X) u v := by
  apply (sourceIOrder_iff_native hu hv).mpr
  apply (FiniteConnectedSmoothPrimeIdealOrder.iOrder_iff_all_finite_connected_smooth_prime_orders_of_genuine_right
    (genuine_of_sourceQPSH hu).1 (genuine_of_sourceQPSH hv)).mpr
  intro Y _ _ _ π _hπ hseq E _hclosed _hconn hhyper
  obtain ⟨k, hk, _hreg⟩ := hhyper
  have hn : n ≠ 0 := by omega
  apply (iInf_lelongNumber_le_iff_squaredLog hn (fun y => u (π y)) (fun y => v (π y)) E).mpr
  exact iInf_mono fun y => iInf_mono fun _hy => by
    simpa only [sourceLelong_ofFixedModel_eq, Function.comp_def] using hpoint Y π hseq y

theorem finitePointComparison_of_kahlerPointComparison [CompactSpace X]
    (omega : KahlerBackground n X) {u v : X → EReal}
    (hpoint : kahlerModificationPointComparison (n := n) u v) :
    finiteModificationPointComparison (n := n) u v := by
  intro Y _ _ _ π hseq y
  obtain ⟨_compactY, ⟨omegaY⟩⟩ :=
    LocusProperties.compactSpace_and_kahler_of_isBlowupSequence ⟨omega⟩ π hseq
  exact hpoint Y omegaY π (SGPT.Okounkov.isAnalyticModification_of_isBlowupSequence hseq) y

theorem sourceIOrder_of_kahlerModificationPointComparison [CompactSpace X]
    (omega : KahlerBackground n X) {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v)
    (hpoint : kahlerModificationPointComparison (n := n) u v) :
    sourceIOrder (ofFixedModel n X) u v :=
  sourceIOrder_of_finiteModificationPointComparison hu hv
    (finitePointComparison_of_kahlerPointComparison omega hpoint)

/-- Literal pullback point comparison on EVERY actual smooth proper model,
without a finite-blowup restriction or supplied Kähler structure upstairs. -/
theorem sourcePointComparison_of_sourceIOrder_on_analyticModification
    {u v : X → EReal} (hu : (ofFixedModel n X).IsQPSH u)
    (hv : (ofFixedModel n X).IsQPSH v)
    (hI : sourceIOrder (ofFixedModel n X) u v)
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π) (y : Y) :
    (ofFixedModel n Y).sourceLelong (v ∘ π) y ≤
      (ofFixedModel n Y).sourceLelong (u ∘ π) y := by
  by_cases hn : n = 0
  · simp only [sourceLelong_ofFixedModel_eq, squaredLogLelongNumber, hn, ↓reduceIte, le_refl]
  have huRaw := (genuine_of_sourceQPSH hu).1
  have hvGenuine := genuine_of_sourceQPSH hv
  have hIpull := (GenuineModificationIdealOrderInvariance.iOrder_iff_comp hπ huRaw hvGenuine).mp
    ((sourceIOrder_iff_native hu hv).mp hI)
  have hpoint := RawIntegerPointComparison.lelongNumber_le_of_iOrderOnManifold
    (GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ.1 huRaw) hIpull y
  simp only [sourceLelong_ofFixedModel_eq]
  apply (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog hn, ← lelongNumber_eq_two_mul_squaredLog hn]
  exact hpoint

/-- Original clause3 uses the book's explicitly finite smooth-center convention. -/
theorem sourceIOrder_iff_finiteModificationPointComparison
    {u v : X → EReal} (hu : (ofFixedModel n X).IsQPSH u)
    (hv : (ofFixedModel n X).IsQPSH v) :
    sourceIOrder (ofFixedModel n X) u v ↔ finiteModificationPointComparison (n := n) u v := by
  constructor
  · intro hI Y _ _ _ π hseq y
    exact sourcePointComparison_of_sourceIOrder_on_analyticModification hu hv hI
      (SGPT.Okounkov.isAnalyticModification_of_isBlowupSequence hseq) y
  · exact sourceIOrder_of_finiteModificationPointComparison hu hv

/-- Original clause4 tests every actual Kähler-source proper modification.
The reverse direction manufactures Kähler backgrounds on finite blowups. -/
theorem sourceIOrder_iff_kahlerModificationPointComparison [CompactSpace X]
    (omega : PositiveClasses.KahlerBackground n X) {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    sourceIOrder (ofFixedModel n X) u v ↔ kahlerModificationPointComparison (n := n) u v := by
  constructor
  · intro hI Y _ _ _ _omegaY π hπ y
    exact sourcePointComparison_of_sourceIOrder_on_analyticModification hu hv hI hπ y
  · exact sourceIOrder_of_kahlerModificationPointComparison omega hu hv


end SGPT.PSH.VariableComplexAtlas
