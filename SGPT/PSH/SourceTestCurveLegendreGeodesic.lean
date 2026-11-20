import SGPT.PSH.SourceTestCurveLegendreFullMass
import SGPT.PSH.SourceTestCurveLegendreSupremum
import SGPT.PSH.SourceSubgeodesicOperations
import SGPT.PSH.SourcePerronStability

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

private def assignedLegendre (Γ : SourceTestCurvePredata θ) : ℝ → M → EReal :=
  sourceRayExtension (sourceTestCurveLegendreRay Γ)

private def physicalLegendrePerron (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) (a b : ℝ) (t : ℝ) : M → EReal :=
  sourcePerronClosedSlice omega θ (assignedLegendre Γ a) (assignedLegendre Γ b)
    ((t - a) / (b - a))

/-- Literal physical-interval replacement of the SAME assigned-zero raw ray.
Both seams retain the original values. -/
def sourceTestCurvePerronReplacementRay (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) (a b : ℝ) : SourceRayFamily M :=
  fun t ↦ sourceSubgeodesicReplacementCurve (assignedLegendre Γ)
    (physicalLegendrePerron omega Γ a b) a b t.1

private theorem assignedLegendre_le_cutoff (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {t : ℝ} (ht : 0 ≤ t) :
    assignedLegendre Γ t ≤ fun _ ↦ ((t * Γ.max : ℝ) : EReal) := by
  unfold assignedLegendre
  rw [Γ.legendreRay_eq_regularized omega,
    sourceRayExtension_nonneg (sourceTestCurveRegularizedRay Γ) t ht]
  exact Γ.regularizedLegendre_le_cutoff ht

omit [BorelSpace M] [ConnectedSpace M] in
private theorem physicalLegendrePerron_endpoints (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (hab : a < b) :
    physicalLegendrePerron omega Γ a b a = assignedLegendre Γ a ∧
      physicalLegendrePerron omega Γ a b b = assignedLegendre Γ b := by
  constructor
  · simp only [physicalLegendrePerron, sub_self, zero_div,
      sourcePerronClosedSlice, closedSubgeodesicSlice_zero]
  · simp only [physicalLegendrePerron, div_self (sub_pos.mpr hab).ne',
      sourcePerronClosedSlice, closedSubgeodesicSlice_one]

private theorem physicalLegendrePerron_subgeodesic (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    SourceSubgeodesicClosedInterval omega θ a b (physicalLegendrePerron omega Γ a b) := by
  have hL := ((Γ.legendreRay_emanates omega).1 a b ha hab.le).2
  have hP := hL.sourcePerron_isSubgeodesicFrom
  have he := physicalLegendrePerron_endpoints omega Γ hab
  refine ⟨hab.le, ?_⟩
  rw [he.1, he.2]
  apply hP.congr_Ioo
  intro s hs
  have htime : (s * b + (1 - s) * a - a) / (b - a) = s := by
    field_simp [(sub_pos.mpr hab).ne']
    ring
  simp only [physicalLegendrePerron, htime, sourcePerronClosedSlice,
    closedSubgeodesicSlice_eq_curve hs, assignedLegendre]

private theorem physicalLegendrePerron_dominates (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    assignedLegendre Γ t ≤ physicalLegendrePerron omega Γ a b t := by
  have hL := ((Γ.legendreRay_emanates omega).1 a b ha hab.le).2
  let s : ℝ := (t - a) / (b - a)
  have hs : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr ht.1) (sub_pos.mpr hab),
      (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])⟩
  have htime : s * b + (1 - s) * a = t := by
    dsimp [s]
    field_simp [(sub_pos.mpr hab).ne']
    ring
  have hc : (fun q ↦ assignedLegendre Γ (q * b + (1 - q) * a)) ∈
      sourcePerronCompetitors omega θ (assignedLegendre Γ a) (assignedLegendre Γ b) :=
    ⟨_, _, hL.1, hL.2.1, le_rfl, le_rfl, hL⟩
  have hdom := sourcePerron_competitor_le hc s
  change assignedLegendre Γ t ≤ sourcePerronClosedSlice omega θ
    (assignedLegendre Γ a) (assignedLegendre Γ b) s
  rw [sourcePerronClosedSlice, closedSubgeodesicSlice_eq_curve hs]
  simpa only [htime] using hdom

private theorem physicalLegendrePerron_le_cutoff (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M) :
    physicalLegendrePerron omega Γ a b t x ≤ ((t * Γ.max : ℝ) : EReal) := by
  have hL := ((Γ.legendreRay_emanates omega).1 a b ha hab.le).2
  have hP := hL.sourcePerron_isSubgeodesicFrom
  let s : ℝ := (t - a) / (b - a)
  have hs : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr ht.1) (sub_pos.mpr hab),
      (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])⟩
  have hc := hP.le_closedChord (a := 0) (b := 1) le_rfl le_rfl zero_lt_one
    ⟨hs.1.le, hs.2.le⟩ x
  simp only [mul_zero, mul_one, zero_add, closedSubgeodesicSlice_zero,
    closedSubgeodesicSlice_one] at hc
  have hbound := hc.trans (eRealChord_mono
    (assignedLegendre_le_cutoff omega Γ ha x)
    (assignedLegendre_le_cutoff omega Γ (ha.trans hab.le) x) hs.1.le hs.2.le)
  rw [SubgeodesicInfimum.eRealChord_coe_coe] at hbound
  have heq : (1 - s) * (a * Γ.max) + s * (b * Γ.max) = t * Γ.max := by
    dsimp [s]
    field_simp [(sub_pos.mpr hab).ne']
    ring
  simpa only [physicalLegendrePerron, sourcePerronClosedSlice, heq, assignedLegendre, s] using hbound

/-- Every original physical-time replacement has the SAME finite linear
upper bound, produced by the existing genuine Perron endpoint chord. -/
theorem SourceTestCurvePredata.perronReplacement_le_cutoff
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (t : Ici (0 : ℝ)) :
    sourceTestCurvePerronReplacementRay omega Γ a b t ≤
      fun _ ↦ ((t.1 * Γ.max : ℝ) : EReal) := by
  classical
  intro x
  unfold sourceTestCurvePerronReplacementRay sourceSubgeodesicReplacementCurve
  by_cases ht : t.1 ∈ Ioo a b
  · simp only [if_pos ht]
    exact physicalLegendrePerron_le_cutoff omega Γ ha hab ht x
  · simp only [if_neg ht]
    exact assignedLegendre_le_cutoff omega Γ t.2 x

private theorem perronReplacement_dominates (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (t : Ici (0 : ℝ)) :
    assignedLegendre Γ t.1 ≤ sourceTestCurvePerronReplacementRay omega Γ a b t := by
  classical
  unfold sourceTestCurvePerronReplacementRay sourceSubgeodesicReplacementCurve
  by_cases ht : t.1 ∈ Ioo a b
  · simp only [if_pos ht]
    exact physicalLegendrePerron_dominates omega Γ ha hab ht
  · simp only [if_neg ht, le_refl]

/-- The SAME actual Perron replacement is a genuine WHOLE source
subgeodesic ray, with every closed segment and original global L1 endpoints. -/
theorem SourceTestCurvePredata.perronReplacement_isSubgeodesic
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    SourceIsSubgeodesicRay omega θ (sourceTestCurvePerronReplacementRay omega Γ a b) := by
  intro A B hA hAB
  let T : ℝ := Max.max B b + 1
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hT : 0 < T := lt_of_lt_of_le hb (le_max_right B b) |>.trans (by dsimp [T]; linarith)
  have hBT : B < T := by dsimp [T]; linarith [le_max_left B b]
  have hbT : b < T := by dsimp [T]; linarith [le_max_right B b]
  let c : ℝ → M → EReal := fun s ↦ assignedLegendre Γ (s * T)
  let r : ℝ → M → EReal := fun s ↦ physicalLegendrePerron omega Γ a b (s * T)
  have hbase : SourceSubgeodesicClosedInterval omega θ 0 1 c := by
    apply sourceSubgeodesicClosedInterval_unit_iff.mpr
    have hh := ((Γ.legendreRay_emanates omega).1 0 T le_rfl hT.le).2
    simpa only [c, assignedLegendre, mul_zero, zero_mul, mul_one, one_mul, add_zero] using hh
  have ha' : 0 ≤ a / T := div_nonneg ha hT.le
  have hb' : b / T ≤ 1 := (div_le_one hT).mpr hbT.le
  have hab' : a / T < b / T := (div_lt_div_iff_of_pos_right hT).mpr hab
  have htime (s : ℝ) : (s * (b / T) + (1 - s) * (a / T)) * T =
      s * b + (1 - s) * a := by
    field_simp [hT.ne']
  have hr : SourceSubgeodesicClosedInterval omega θ (a / T) (b / T) r := by
    refine ⟨hab'.le, ?_⟩
    have hh := (physicalLegendrePerron_subgeodesic omega Γ ha hab).2
    simpa only [r, htime, div_mul_cancel₀ a hT.ne', div_mul_cancel₀ b hT.ne'] using hh
  have he := physicalLegendrePerron_endpoints omega Γ hab
  have hleft : r (a / T) = c (a / T) := by
    dsimp [r, c]
    rw [div_mul_cancel₀ a hT.ne']
    exact he.1
  have hright : r (b / T) = c (b / T) := by
    dsimp [r, c]
    rw [div_mul_cancel₀ b hT.ne']
    exact he.2
  have hdom (s : ℝ) (hs : s ∈ Ioo (a / T) (b / T)) : c s ≤ r s := by
    apply physicalLegendrePerron_dominates omega Γ ha hab
    exact ⟨(div_lt_iff₀ hT).mp hs.1, (lt_div_iff₀ hT).mp hs.2⟩
  let q := sourceSubgeodesicReplacementCurve c r (a / T) (b / T)
  have hq : SourceSubgeodesicClosedInterval omega θ 0 1 q :=
    source_subgeodesic_gluing hbase ha' hb' hab' hr hleft hright hdom
  have hread (s : ℝ) (hs : 0 ≤ s) : q s =
      sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) (s * T) := by
    rw [sourceRayExtension_nonneg _ _ (mul_nonneg hs hT.le)]
    have hm : s ∈ Ioo (a / T) (b / T) ↔ s * T ∈ Ioo a b :=
      and_congr (div_lt_iff₀ hT) (lt_div_iff₀ hT)
    simp only [q, sourceSubgeodesicReplacementCurve,
      sourceTestCurvePerronReplacementRay, hm, c, r]
  have hres := hq.restrict_unit (div_nonneg hA hT.le)
    ((div_le_one hT).mpr hBT.le) ((div_le_div_iff_of_pos_right hT).mpr hAB)
  refine ⟨hAB, ?_⟩
  have hh := hres.2
  rw [hread (A / T) (div_nonneg hA hT.le), div_mul_cancel₀ A hT.ne',
    hread (B / T) (div_nonneg (hA.trans hAB) hT.le), div_mul_cancel₀ B hT.ne'] at hh
  apply hh.congr_Ioo
  intro s hs
  have hnonneg : 0 ≤ s * (B / T) + (1 - s) * (A / T) :=
    add_nonneg (mul_nonneg hs.1.le (div_nonneg (hA.trans hAB) hT.le))
      (mul_nonneg (sub_nonneg.mpr hs.2.le) (div_nonneg hA hT.le))
  rw [hread _ hnonneg]
  congr 1
  field_simp [hT.ne']

/-- The literal WHOLE positive-time inverse of any actual source ray. -/
def sourcePositiveRayInverse {X : Type*} (ℓ : SourceRayFamily X) (τ : ℝ) : X → EReal :=
  fun x ↦ ⨅ t : Ioi (0 : ℝ), sourceRayExtension ℓ t.1 x - ((t.1 * τ : ℝ) : EReal)

/-- Exact whole-inverse/conjugate dictionary for ANY original ray,
including every bottom/top value; this is only finite-real order algebra. -/
theorem sourcePositiveRayInverse_conjugate {X : Type*} (ℓ : SourceRayFamily X)
    (τ : ℝ) (x : X) :
    SGPT.Convex.halfLineConjugate (fun t ↦ sourceRayExtension ℓ t x) τ =
      -sourcePositiveRayInverse ℓ τ x := by
  have hn : -sourcePositiveRayInverse ℓ τ x =
      ⨆ t : Ioi (0 : ℝ), -(sourceRayExtension ℓ t.1 x - ((t.1 * τ : ℝ) : EReal)) :=
    map_iInf EReal.negOrderIso _
  rw [hn]
  have he (t : Ioi (0 : ℝ)) :
      -(sourceRayExtension ℓ t.1 x - ((t.1 * τ : ℝ) : EReal)) =
        ((t.1 * τ : ℝ) : EReal) - sourceRayExtension ℓ t.1 x := by
    rw [EReal.neg_sub (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))]
    simp only [sub_eq_add_neg, add_comm]
  simp_rw [he]
  simp only [SGPT.Convex.halfLineConjugate, iSup_subtype, mem_Ioi]

/-- The unchanged original whole inverse of the SAME actual replacement. -/
def sourceTestCurvePerronReplacementInverse (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) (a b τ : ℝ) : M → EReal :=
  sourcePositiveRayInverse (sourceTestCurvePerronReplacementRay omega Γ a b) τ

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem assignedLegendre_pos (Γ : SourceTestCurvePredata θ)
    {t : ℝ} (ht : 0 < t) : assignedLegendre Γ t = sourceTestCurveRawLegendre Γ t := by
  unfold assignedLegendre
  rw [sourceRayExtension_nonneg _ _ ht.le]
  simp only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial,
    if_neg ht.ne']

private theorem at_le_perronReplacementInverse (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (τ : ℝ) :
    sourceTestCurveAt Γ τ ≤ sourceTestCurvePerronReplacementInverse omega Γ a b τ := by
  intro x
  unfold sourceTestCurvePerronReplacementInverse sourcePositiveRayInverse
  apply le_iInf
  intro t
  have ht : 0 < t.1 := t.2
  have hdom := perronReplacement_dominates omega Γ ha hab ⟨t.1, ht.le⟩ x
  rw [assignedLegendre_pos Γ ht] at hdom
  rw [sourceRayExtension_nonneg _ _ ht.le]
  rw [Γ.at_eq_iInf_positive_rawLegendre τ x]
  exact (iInf_le (fun s : Ioi (0 : ℝ) ↦ sourceTestCurveRawLegendre Γ s.1 x -
    ((s.1 * τ : ℝ) : EReal)) t).trans (EReal.sub_le_sub hdom le_rfl)

private def replacementWindowLeft (j : ℕ) : ℝ := 1 / ((j : ℝ) + 2)
private def replacementWindowRight (j : ℕ) : ℝ := (j : ℝ) + 2

private theorem replacementWindow_pos (j : ℕ) :
    0 < replacementWindowLeft j ∧ replacementWindowLeft j < replacementWindowRight j := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hr : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  refine ⟨one_div_pos.mpr hr, ?_⟩
  change 1 / ((j : ℝ) + 2) < (j : ℝ) + 2
  apply (div_lt_iff₀ hr).mpr
  nlinarith

private theorem replacementWindow_mono {i j : ℕ} (hij : i ≤ j) :
    Ioo (replacementWindowLeft i) (replacementWindowRight i) ⊆
      Ioo (replacementWindowLeft j) (replacementWindowRight j) := by
  have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hl : replacementWindowLeft j ≤ replacementWindowLeft i :=
    one_div_le_one_div_of_le (by positivity)
      (by change (i : ℝ) + 2 ≤ (j : ℝ) + 2; linarith)
  have hr : replacementWindowRight i ≤ replacementWindowRight j := by
    dsimp [replacementWindowRight]
    linarith
  exact fun _ ht ↦ ⟨hl.trans_lt ht.1, ht.2.trans_le hr⟩

private theorem replacementWindow_exhaust {t : ℝ} (ht : 0 < t) :
    ∃ j : ℕ, t ∈ Ioo (replacementWindowLeft j) (replacementWindowRight j) := by
  obtain ⟨j, hj⟩ := exists_nat_gt (Max.max t (1 / t))
  have hj' : (j : ℝ) < (j : ℝ) + 2 := lt_add_of_pos_right _ (by norm_num)
  have hr : t < (j : ℝ) + 2 := ((le_max_left _ _).trans_lt hj).trans hj'
  have hl : 1 / t < (j : ℝ) + 2 := ((le_max_right _ _).trans_lt hj).trans hj'
  exact ⟨j, (one_div_lt (by positivity) ht).mpr hl, hr⟩

private def positiveRayWindowInverse {X : Type*} (ℓ : SourceRayFamily X)
    (τ : ℝ) (j : ℕ) : X → EReal :=
  fun x ↦ ⨅ t : Ioo (replacementWindowLeft j) (replacementWindowRight j),
    sourceRayExtension ℓ t.1 x - ((t.1 * τ : ℝ) : EReal)

private theorem positiveRayWindowInverse_thetaPSH
    {omega : KahlerBackground n M} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) (τ : ℝ) (j : ℕ) :
    (ofFixedModel n M).IsThetaPSH θ (positiveRayWindowInverse ℓ τ j) := by
  have hw := replacementWindow_pos j
  exact (h (replacementWindowLeft j) (replacementWindowRight j)
    hw.1.le hw.2.le).isThetaPSH_timeInf_sub_affine hw.2 τ

private theorem positiveInverse_le_window {X : Type*} (ℓ : SourceRayFamily X)
    (τ : ℝ) (j : ℕ) : sourcePositiveRayInverse ℓ τ ≤ positiveRayWindowInverse ℓ τ j := by
  intro x
  apply le_iInf
  intro t
  exact iInf_le (fun s : Ioi (0 : ℝ) ↦ sourceRayExtension ℓ s.1 x -
    ((s.1 * τ : ℝ) : EReal)) ⟨t.1, (replacementWindow_pos j).1.trans t.2.1⟩

private theorem positiveWindowInverse_exhaust {X : Type*} (ℓ : SourceRayFamily X)
    (τ : ℝ) : (fun x ↦ ⨅ j, positiveRayWindowInverse ℓ τ j x) = sourcePositiveRayInverse ℓ τ := by
  funext x
  apply le_antisymm
  · apply le_iInf
    intro t
    obtain ⟨j, hj⟩ := replacementWindow_exhaust t.2
    exact (iInf_le (fun j ↦ positiveRayWindowInverse ℓ τ j x) j).trans
      (iInf_le (fun s : Ioo (replacementWindowLeft j) (replacementWindowRight j) ↦
        sourceRayExtension ℓ s.1 x - ((s.1 * τ : ℝ) : EReal)) ⟨t.1, hj⟩)
  · exact le_iInf fun j ↦ positiveInverse_le_window ℓ τ j x

/-- ANY original subgeodesic ray and a genuine ordinary fixed-point lower
barrier produce the ACTUAL whole positive-time inverse as theta-PSH.
No whole-infimum PSH, noncollapse or positive-mass certificate is an input. -/
theorem SourceIsSubgeodesicRay.inverse_thetaPSH_of_lower_fixedPoint
    {omega : KahlerBackground n M} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hfix : sourceSingularityEnvelope θ u = u) (τ : ℝ)
    (hbelow : ∀ t : ℝ, 0 < t → u ≤
      fun x ↦ sourceRayExtension ℓ t x - ((t * τ : ℝ) : EReal)) :
    (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ τ) := by
  have hsup := sourceOrdinaryFixedPoint_globalSup_zero hu hfix
  have hlower (j : ℕ) : (0 : EReal) ≤ ⨆ x, positiveRayWindowInverse ℓ τ j x := by
    rw [← hsup]
    apply iSup_mono
    intro x
    exact le_iInf fun t ↦ hbelow t.1 ((replacementWindow_pos j).1.trans t.2.1) x
  have hanti (x : M) : Antitone (fun j ↦ positiveRayWindowInverse ℓ τ j x) := by
    intro i j hij
    apply le_iInf
    intro t
    exact iInf_le (fun s : Ioo (replacementWindowLeft j) (replacementWindowRight j) ↦
      sourceRayExtension ℓ s.1 x - ((s.1 * τ : ℝ) : EReal))
        ⟨t.1, replacementWindow_mono hij t.2⟩
  have hh := (SGPT.PSH.isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    (fun j ↦ (isThetaPSH_iff_nativeThetaPotential θ _).mp
      (positiveRayWindowInverse_thetaPSH h τ j)) hanti 0
    (by simpa only [EReal.coe_zero] using hlower)).1
  rw [positiveWindowInverse_exhaust] at hh
  exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr hh

/-- Genuine replacement inverse PSH, discharging EVERY generic lower-barrier
hypothesis internally from the SAME original test curve, through the cutoff. -/
theorem SourceTestCurvePredata.perronReplacement_inverse_thetaPSH
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {τ : ℝ} (hτ : τ ≤ Γ.max) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurvePerronReplacementInverse omega Γ a b τ) := by
  have hAt := (source_test_curve_extension_whole Γ).2.2.2 τ hτ
  have hfix : sourceSingularityEnvelope θ (sourceTestCurveAt Γ τ) = sourceTestCurveAt Γ τ := by
    rcases hτ.eq_or_lt with heq | hlt
    · rw [heq, sourceTestCurveAt_eq_max]
      exact Γ.cutoff_fixedPoint
    · rw [sourceTestCurveAt_of_lt Γ hlt]
      exact Γ.fixedPoint ⟨τ, hlt⟩
  apply (Γ.perronReplacement_isSubgeodesic omega ha hab).inverse_thetaPSH_of_lower_fixedPoint hAt hfix τ
  intro t ht x
  exact (at_le_perronReplacementInverse omega Γ ha hab τ x).trans
    (iInf_le (fun s : Ioi (0 : ℝ) ↦
      sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) s.1 x -
        ((s.1 * τ : ℝ) : EReal)) ⟨t, ht⟩)

omit [BorelSpace M] [ConnectedSpace M] in
private theorem perronReplacement_eq_assigned_outside (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) (a b : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hout : t ∉ Ioo a b) :
    sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) t =
      assignedLegendre Γ t := by
  rw [sourceRayExtension_nonneg _ _ ht]
  simp only [sourceTestCurvePerronReplacementRay, sourceSubgeodesicReplacementCurve, if_neg hout]

private theorem replacementInverse_le_linear (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (τ : ℝ) {t : ℝ} (ht : 0 < t) (x : M) :
    sourceTestCurvePerronReplacementInverse omega Γ a b τ x ≤
      ((t * (Γ.max - τ) : ℝ) : EReal) := by
  have hle := Γ.perronReplacement_le_cutoff omega ha hab ⟨t, ht.le⟩ x
  have hh := iInf_le (fun s : Ioi (0 : ℝ) ↦
    sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) s.1 x -
      ((s.1 * τ : ℝ) : EReal)) ⟨t, ht⟩
  have hbound := hh.trans (EReal.sub_le_sub
    (by simpa only [sourceRayExtension_nonneg _ _ ht.le] using hle) le_rfl)
  simpa only [sourceTestCurvePerronReplacementInverse, sourcePositiveRayInverse,
    ← EReal.coe_sub, ← mul_sub] using hbound

omit [BorelSpace M] in
private theorem replacementInverse_le_shifted (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {τ : ℝ} (hτ : τ ≤ Γ.max) (x : M) :
    sourceTestCurvePerronReplacementInverse omega Γ a b τ x ≤
      sourceTestCurveAt Γ τ x + (((b - a) * (Γ.max - τ) : ℝ) : EReal) := by
  let C : ℝ := (b - a) * (Γ.max - τ)
  have hC : 0 ≤ C := mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hτ)
  rw [Γ.at_eq_iInf_positive_rawLegendre τ x,
    ← ThetaPshDecreasingLimit.iInf_add_coe]
  apply le_iInf
  intro s
  have hs : 0 < s.1 := s.2
  by_cases hsin : s.1 ∈ Ioo a b
  · have hb : 0 < b := lt_of_le_of_lt ha hab
    have houtside : b ∉ Ioo a b := fun hh ↦ (lt_irrefl b) hh.2
    have hread := perronReplacement_eq_assigned_outside omega Γ a b hb.le houtside
    have hinf : sourceTestCurvePerronReplacementInverse omega Γ a b τ x ≤
        sourceTestCurveRawLegendre Γ b x - ((b * τ : ℝ) : EReal) := by
      have hh := iInf_le (fun t : Ioi (0 : ℝ) ↦
        sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) t.1 x -
          ((t.1 * τ : ℝ) : EReal)) ⟨b, hb⟩
      simpa only [sourceTestCurvePerronReplacementInverse, sourcePositiveRayInverse,
        hread, assignedLegendre_pos Γ hb] using hh
    have hnorm := Γ.rawLegendre_normalized_antitone x hsin.2.le
    apply hinf.trans
    calc
      sourceTestCurveRawLegendre Γ b x - ((b * τ : ℝ) : EReal) =
          (sourceTestCurveRawLegendre Γ b x - ((b * Γ.max : ℝ) : EReal)) +
            ((b * Γ.max - b * τ : ℝ) : EReal) := by
        simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add]
        congr 2
        ring
      _ ≤ (sourceTestCurveRawLegendre Γ s.1 x - ((s.1 * Γ.max : ℝ) : EReal)) +
          ((b * Γ.max - b * τ : ℝ) : EReal) := add_le_add hnorm le_rfl
      _ = sourceTestCurveRawLegendre Γ s.1 x +
          ((b * Γ.max - b * τ - s.1 * Γ.max : ℝ) : EReal) := by
        simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add]
        congr 2
        ring
      _ ≤ sourceTestCurveRawLegendre Γ s.1 x + ((C - s.1 * τ : ℝ) : EReal) := by
        apply add_le_add le_rfl
        apply EReal.coe_le_coe
        dsimp [C]
        nlinarith [mul_nonneg (sub_nonneg.mpr hsin.1.le) (sub_nonneg.mpr hτ)]
      _ = (sourceTestCurveRawLegendre Γ s.1 x - ((s.1 * τ : ℝ) : EReal)) + (C : EReal) := by
        simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add]
        congr 2
        ring
  · have hread := perronReplacement_eq_assigned_outside omega Γ a b hs.le hsin
    have hh := iInf_le (fun t : Ioi (0 : ℝ) ↦
      sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) t.1 x -
        ((t.1 * τ : ℝ) : EReal)) s
    have hbound : sourceTestCurvePerronReplacementInverse omega Γ a b τ x ≤
        sourceTestCurveRawLegendre Γ s.1 x - ((s.1 * τ : ℝ) : EReal) := by
      simpa only [sourceTestCurvePerronReplacementInverse, sourcePositiveRayInverse,
        hread, assignedLegendre_pos Γ hs] using hh
    exact hbound.trans (le_add_of_nonneg_right (EReal.coe_nonneg.mpr hC))

private theorem replacementInverse_nonpositive (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (τ : ℝ) :
    sourceTestCurvePerronReplacementInverse omega Γ a b τ ≤ 0 := by
  intro x
  have hlim : Tendsto (fun t : ℝ ↦ ((-(t * (Γ.max - τ)) : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : EReal)) := by
    have hf : Continuous (fun t : ℝ ↦ ((-(t * (Γ.max - τ)) : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp ((continuous_id.mul continuous_const).neg)
    simpa only [zero_mul, neg_zero, EReal.coe_zero] using
      (hf.tendsto (0 : ℝ)).mono_left
        (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hneg : (0 : EReal) ≤ -sourceTestCurvePerronReplacementInverse omega Γ a b τ x := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hh := EReal.neg_le_neg_iff.mpr (replacementInverse_le_linear omega Γ ha hab τ ht x)
    simpa only [EReal.coe_neg] using hh
  exact EReal.neg_nonneg.mp hneg

private theorem replacementInverse_bot_above (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {τ : ℝ} (hτ : Γ.max < τ) :
    sourceTestCurvePerronReplacementInverse omega Γ a b τ = ⊥ := by
  funext x
  apply le_bot_iff.mp
  apply EReal.le_of_forall_lt_iff_le.mp
  intro r _
  let t : ℝ := Max.max 1 ((r - 1) / (Γ.max - τ))
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hδ : Γ.max - τ < 0 := sub_neg.mpr hτ
  have hmul : t * (Γ.max - τ) ≤ r - 1 := by
    have hh := mul_le_mul_of_nonpos_right (le_max_right (1 : ℝ)
      ((r - 1) / (Γ.max - τ))) hδ.le
    simpa only [div_mul_cancel₀ _ hδ.ne] using hh
  exact (replacementInverse_le_linear omega Γ ha hab τ ht x).trans
    (EReal.coe_le_coe (by linarith : t * (Γ.max - τ) ≤ r))

/-- Exact original finite comparison and zero normalization through the
cutoff, together with the literal bottom branch above the cutoff. -/
theorem SourceTestCurvePredata.perronReplacement_inverse_comparison
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (τ : ℝ) :
    (τ ≤ Γ.max → sourceTestCurveAt Γ τ ≤ sourceTestCurvePerronReplacementInverse omega Γ a b τ ∧
      sourceTestCurvePerronReplacementInverse omega Γ a b τ ≤
        (fun x ↦ sourceTestCurveAt Γ τ x + (((b - a) * (Γ.max - τ) : ℝ) : EReal)) ∧
      sourceTestCurvePerronReplacementInverse omega Γ a b τ ≤ 0) ∧
    (Γ.max < τ → sourceTestCurvePerronReplacementInverse omega Γ a b τ = ⊥) := by
  refine ⟨fun hτ ↦ ⟨at_le_perronReplacementInverse omega Γ ha hab τ,
    replacementInverse_le_shifted omega Γ ha hab hτ,
    replacementInverse_nonpositive omega Γ ha hab τ⟩,
    replacementInverse_bot_above omega Γ ha hab⟩

/-- The SAME literal whole replacement inverse equals the original whole
extension at EVERY real parameter, including its cutoff and bottom branch. -/
theorem SourceTestCurvePredata.perronReplacement_inverse_eq
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (τ : ℝ) :
    sourceTestCurvePerronReplacementInverse omega Γ a b τ = sourceTestCurveAt Γ τ := by
  have hc := Γ.perronReplacement_inverse_comparison omega ha hab τ
  by_cases hτ : τ ≤ Γ.max
  · have hχ := Γ.perronReplacement_inverse_thetaPSH omega ha hab hτ
    have hfix : sourceSingularityEnvelope θ (sourceTestCurveAt Γ τ) = sourceTestCurveAt Γ τ := by
      rcases hτ.eq_or_lt with heq | hlt
      · rw [heq, sourceTestCurveAt_eq_max]
        exact Γ.cutoff_fixedPoint
      · rw [sourceTestCurveAt_of_lt Γ hlt]
        exact Γ.fixedPoint ⟨τ, hlt⟩
    have hmore : SGPT.PSH.SingularityLE
        (sourceTestCurvePerronReplacementInverse omega Γ a b τ) (sourceTestCurveAt Γ τ) :=
      ⟨(b - a) * (Γ.max - τ), fun x _ ↦ (hc.1 hτ).2.1 x⟩
    exact le_antisymm ((le_sourceSingularityEnvelope hχ (hc.1 hτ).2.2 hmore).trans_eq hfix)
      (hc.1 hτ).1
  · have hgt : Γ.max < τ := lt_of_not_ge hτ
    rw [hc.2 hgt, sourceTestCurveAt_of_gt Γ hgt]

private theorem perronReplacement_eq_assigned_pos (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {t : ℝ} (ht : 0 < t) :
    sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) t =
      assignedLegendre Γ t := by
  funext x
  have hR := Γ.perronReplacement_isSubgeodesic omega ha hab
  have hfinite (s : ℝ) (hs : 0 < s) :
      sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) s x < ⊤ := by
    rw [sourceRayExtension_nonneg _ _ hs.le]
    exact (Γ.perronReplacement_le_cutoff omega ha hab ⟨s, hs.le⟩ x).trans_lt (EReal.coe_lt_top _)
  have hconj (τ : ℝ) : SGPT.Convex.halfLineConjugate
      (fun s ↦ sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) s x) τ =
      -sourceTestCurveAt Γ τ x := by
    rw [sourcePositiveRayInverse_conjugate]
    change -sourceTestCurvePerronReplacementInverse omega Γ a b τ x = -sourceTestCurveAt Γ τ x
    rw [Γ.perronReplacement_inverse_eq omega ha hab τ]
  have hinv := SGPT.Convex.halfLineConjugate_inversion (hR.positiveEpigraph_convex x) hfinite ht
  calc
    sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) t x =
        SGPT.Convex.conjugate SGPT.Convex.scalarPairing
          (SGPT.Convex.halfLineConjugate
            (fun s ↦ sourceRayExtension (sourceTestCurvePerronReplacementRay omega Γ a b) s x)) t :=
      hinv.symm
    _ = sourceTestCurveRawLegendre Γ t x := by
      simp only [SGPT.Convex.conjugate, SGPT.Convex.scalarPairing, LinearMap.mul_apply',
        hconj, sub_eq_add_neg, neg_neg, sourceTestCurveRawLegendre]
      apply iSup_congr
      intro τ
      rw [mul_comm]
    _ = assignedLegendre Γ t x := (congrFun (assignedLegendre_pos Γ ht) x).symm

/-- Genuine original Perron maximality on EVERY nonnegative closed segment,
including the degenerate interval. The SAME raw ray is unchanged. -/
theorem SourceTestCurvePredata.legendre_geodesic_closed
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    SourceGeodesicClosedInterval omega θ a b (sourceRayExtension (sourceTestCurveLegendreRay Γ)) := by
  have hR := (Γ.legendreRay_emanates omega).1
  have hslice (t : ℝ) (ht : 0 ≤ t) :
      (ofFixedModel n M).IsThetaPSH θ (sourceRayExtension (sourceTestCurveLegendreRay Γ) t) := by
    rw [sourceRayExtension_nonneg _ _ ht]
    exact hR.thetaPSH ⟨t, ht⟩
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    exact (sourceGeodesicClosedInterval_self_iff omega θ a _).mpr (hslice a ha)
  refine ⟨hab, fun t ht ↦ hslice t (ha.trans ht.1),
    hslice a ha, hslice b (ha.trans hab), ?_, ?_⟩
  · intro s hs
    apply Or.inl
    apply hslice
    exact add_nonneg (mul_nonneg hs.1.le (ha.trans hab))
      (mul_nonneg (sub_nonneg.mpr hs.2.le) ha)
  · intro s hs
    let t : ℝ := s * b + (1 - s) * a
    have ht : t ∈ Ioo a b := by
      dsimp [t]
      constructor <;> nlinarith [mul_pos hs.1 (sub_pos.mpr hlt),
        mul_pos (sub_pos.mpr hs.2) (sub_pos.mpr hlt)]
    have hpos : 0 < t := lt_of_le_of_lt ha ht.1
    have heq := perronReplacement_eq_assigned_pos omega Γ ha hlt hpos
    rw [sourceRayExtension_nonneg _ _ hpos.le] at heq
    simp only [sourceTestCurvePerronReplacementRay, sourceSubgeodesicReplacementCurve,
      if_pos ht] at heq
    have htime : (t - a) / (b - a) = s := by
      dsimp [t]
      field_simp [(sub_pos.mpr hlt).ne']
      ring
    simpa only [physicalLegendrePerron, htime, sourcePerronClosedSlice,
      closedSubgeodesicSlice_eq_curve hs, assignedLegendre] using heq.symm

/-- ENTIRE original lma:LegsendsTCtoR, on its original based test curves,
actual full-mass class and every closed geodesic interval; original global
L1 emanation is retained as a genuine additional conclusion. -/
theorem source_test_curve_legendre_geodesic_whole
    (omega : KahlerBackground n M) (Γ : SourceTestCurve θ)
    {φ : M → EReal} {hφ : SourceModelPotential θ φ}
    (hbased : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata ∈ sourceGeodesicRays omega θ φ hφ ∧
      SourceSubgeodesicRayEmanatesFrom omega θ
        (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata) φ := by
  have heman := (source_test_curve_legendre_psh_whole omega Γ hbased).2.2
  refine ⟨⟨⟨?_, ?_⟩, heman.2⟩, heman⟩
  · intro t
    by_cases ht : t.1 = 0
    · have hzero : t = ⟨0, by simp⟩ := Subtype.ext ht
      rw [hzero, heman.2]
      exact ⟨hφ.thetaPSH, MoreSingularOn.refl φ univ, rfl⟩
    · have hpos : 0 < t.1 := lt_of_le_of_ne t.2 (Ne.symm ht)
      have hf := source_test_curve_legendre_fullMass_whole omega Γ hbased t.1 hpos
      simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial,
        if_neg ht] using hf
  · intro a b ha hab
    exact Γ.toSourceTestCurvePredata.legendre_geodesic_closed omega a b ha hab

end SGPT.PSH.VariableComplexAtlas
