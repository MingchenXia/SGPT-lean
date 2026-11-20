import SGPT.TestCurve.RWNTwistedConvex
import SGPT.TestCurve.TestConfTwisted
import SGPT.PSH.SourceTestCurveJoinInverse

/-!
# Subgeodesic rays and their inverse Legendre transforms

Source `rmk:testcurve:L815` (chapter *Test curves*): general facts on a subgeodesic ray
`(ℓ_t)_{t ≥ 0}` and its inverse Legendre transform `ℓ*_τ = inf_{t > 0} (ℓ_t - tτ)`
(`eq:invLeg`), used for rays emanating from an arbitrary potential `Φ`. Nothing here refers to
the normalisation `sup_X ℓ_t = t sup_X ℓ_1` of rays emanating from a model potential
(`prop:raysuplinear`), which fails in the twisted setting.

* `rayInverse_thetaPSH_of_ne_bot`: `ℓ*_τ` is `θ`-psh as soon as it is not identically `-∞`
  (Kiselman's principle, `prop:Kis`).
* `rayInverse_le_initial`: `ℓ*_τ ≤ ℓ_0`.
* `rayInverse_eq_bot_of_linear_bound`: `ℓ*_τ ≡ -∞` for `τ > m` if `ℓ_t ≤ c + tm`.
* `ray_positive_inversion`, `ray_positive_inversion_Iio`: `ℓ_t = sup_τ (tτ + ℓ*_τ)` for `t > 0`.
* `rayInverse_uscSup_eq_initial`: `usc sup_{τ < c} ℓ*_τ = ℓ_0`.
* `perronReplacement`: the ray obtained by replacing `ℓ` on `(a, b)` by the geodesic from
  `ℓ_a` to `ℓ_b`; it is a subgeodesic ray dominating `ℓ` (`lma:subgeodgluing`), with the same
  linear upper bound.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.RWNTwisted

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas
open SGPT.TestCurve.TestConf

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- A `θ`-psh function does not take the value `+∞`. -/
theorem thetaPSH_ne_top {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (x : M) :
    u x ≠ ⊤ :=
  ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).1.quasiPlurisubharmonic.ne_top x

/-- A `θ`-psh function is not identically `-∞`. -/
theorem thetaPSH_exists_ne_bot [Nonempty M] {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) : ∃ x, u x ≠ ⊥ := by
  obtain ⟨x⟩ := ‹Nonempty M›
  obtain ⟨y, -, hy⟩ :=
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).2 x univ isOpen_univ (mem_univ x)
  exact ⟨y, hy⟩

/-- A `θ`-psh function on a compact manifold is bounded from above. -/
theorem thetaPSH_exists_upper [CompactSpace M] [Nonempty M] {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) : ∃ C : ℝ, ∀ x, u x ≤ C :=
  ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).exists_global_upper_bound

/-- Above the slope of a linear upper bound the inverse Legendre transform of a ray is `-∞`. -/
theorem rayInverse_eq_bot_of_linear_bound {X : Type*} {ℓ : SourceRayFamily X} {c m : ℝ}
    (hb : ∀ (t : Ici (0 : ℝ)) (x : X), ℓ t x ≤ ((c + t.1 * m : ℝ) : EReal)) {τ : ℝ}
    (hτ : m < τ) : sourcePositiveRayInverse ℓ τ = ⊥ := by
  funext x
  change (⨅ s : Ioi (0 : ℝ), sourceRayExtension ℓ s.1 x - ((s.1 * τ : ℝ) : EReal)) = ⊥
  apply iInf_sub_eq_bot_of_linear_bound (F := fun s ↦ sourceRayExtension ℓ s x) (c := c)
    (m := m) _ hτ
  intro s hs
  rw [sourceRayExtension_nonneg ℓ s hs.le]
  exact hb ⟨s, hs.le⟩ x

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {omega : KahlerBackground n M} {ℓ : SourceRayFamily M}

omit [ConnectedSpace M] [BorelSpace M] in
/-- The unit segment of a subgeodesic ray is a subgeodesic from `ℓ_0` to `ℓ_1`. -/
theorem subgeodesicRay_unitSegment (h : SourceIsSubgeodesicRay omega θ ℓ) :
    SourceSubgeodesicFrom omega θ (fun s ↦ sourceRayExtension ℓ s) (ℓ ⟨0, by simp⟩)
      (ℓ ⟨1, by norm_num⟩) := by
  have hh := (h 0 1 le_rfl zero_le_one).2
  simpa only [mul_one, mul_zero, add_zero, sourceRayExtension_nonneg ℓ 0 le_rfl,
    sourceRayExtension_nonneg ℓ 1 zero_le_one] using hh

omit [ConnectedSpace M] [BorelSpace M] in
/-- The positive-time values of a subgeodesic ray are `< +∞`. -/
theorem subgeodesicRay_lt_top (h : SourceIsSubgeodesicRay omega θ ℓ) {s : ℝ}
    (hs : 0 < s) (x : M) : sourceRayExtension ℓ s x < ⊤ := by
  rw [sourceRayExtension_nonneg ℓ s hs.le]
  exact lt_top_iff_ne_top.mpr (thetaPSH_ne_top (h.thetaPSH ⟨s, hs.le⟩) x)

/-- Kiselman's principle (`prop:Kis`) for the inverse Legendre transform of a subgeodesic ray:
`ℓ*_τ` is `θ`-psh as soon as it is not identically `-∞`. -/
theorem rayInverse_thetaPSH_of_ne_bot (h : SourceIsSubgeodesicRay omega θ ℓ) (τ : ℝ)
    (hx : ∃ x, sourcePositiveRayInverse ℓ τ x ≠ ⊥) :
    (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ τ) := by
  obtain ⟨x₀, hx₀⟩ := hx
  obtain ⟨a, -, ha⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hx₀)
  have hlow (j : ℕ) : (a : EReal) ≤ ⨆ x, sourcePositiveRayInverseWindow ℓ τ j x := by
    refine ha.le.trans (le_trans ?_ (le_iSup (fun x ↦ sourcePositiveRayInverseWindow ℓ τ j x) x₀))
    have hex := congrFun (sourcePositiveRayInverseWindow_exhaust ℓ τ) x₀
    rw [← hex]
    exact iInf_le (fun j ↦ sourcePositiveRayInverseWindow ℓ τ j x₀) j
  have hh := (SGPT.PSH.isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    (fun j ↦ (isThetaPSH_iff_nativeThetaPotential θ _).mp
      (sourcePositiveRayInverseWindow_thetaPSH h τ j))
    (sourcePositiveRayInverseWindow_antitone ℓ τ) a hlow).1
  rw [sourcePositiveRayInverseWindow_exhaust] at hh
  exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr hh

/-- The inverse Legendre transform of a subgeodesic ray lies below its initial value. -/
theorem rayInverse_le_initial (h : SourceIsSubgeodesicRay omega θ ℓ) (τ : ℝ) :
    sourcePositiveRayInverse ℓ τ ≤ ℓ ⟨0, by simp⟩ := by
  intro x
  have hw := source_subgeodesic_endpoints_whole (subgeodesicRay_unitSegment h)
  refine le_trans ?_ (hw.2.2.1 x)
  have hL := hw.1 x
  have hc : Tendsto (fun s : ℝ ↦ ((-(s * τ) : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : EReal)) := by
    have hf : Continuous (fun s : ℝ ↦ ((-(s * τ) : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp ((continuous_id.mul continuous_const).neg)
    simpa only [zero_mul, neg_zero, EReal.coe_zero] using
      (hf.tendsto (0 : ℝ)).mono_left
        (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hadd : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2)
      (sourceSubgeodesicLeftLimit (fun s ↦ sourceRayExtension ℓ s) x, (0 : EReal)) :=
    EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
  have hlim : Tendsto (fun s : ℝ ↦ sourceRayExtension ℓ s x + ((-(s * τ) : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (sourceSubgeodesicLeftLimit (fun s ↦ sourceRayExtension ℓ s) x)) := by
    simpa only [Function.comp_def, add_zero] using hadd.tendsto.comp (hL.prodMk_nhds hc)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hh := iInf_le (fun t : Ioi (0 : ℝ) ↦
    sourceRayExtension ℓ t.1 x - ((t.1 * τ : ℝ) : EReal)) ⟨s, hs⟩
  simpa only [sourcePositiveRayInverse, sub_eq_add_neg, EReal.coe_neg] using hh

omit [ConnectedSpace M] in
/-- Legendre duality on the half line: a subgeodesic ray is recovered at positive times from
its inverse Legendre transform. -/
theorem ray_positive_inversion (h : SourceIsSubgeodesicRay omega θ ℓ) {t : ℝ} (ht : 0 < t)
    (x : M) : sourceRayExtension ℓ t x =
      ⨆ τ : ℝ, ((t * τ : ℝ) : EReal) + sourcePositiveRayInverse ℓ τ x := by
  have hi := SGPT.Convex.halfLineConjugate_inversion (h.positiveEpigraph_convex x)
    (fun s hs ↦ subgeodesicRay_lt_top h hs x) ht
  rw [← hi]
  simp only [SGPT.Convex.conjugate, SGPT.Convex.scalarPairing, LinearMap.mul_apply',
    sourcePositiveRayInverse_conjugate, sub_eq_add_neg, neg_neg]
  apply iSup_congr
  intro τ
  rw [mul_comm]

omit [ConnectedSpace M] in
/-- Legendre duality on the half line, with the supremum over `τ < m` when the inverse
transform is `-∞` above `m`. -/
theorem ray_positive_inversion_Iio (h : SourceIsSubgeodesicRay omega θ ℓ) {m : ℝ}
    (hbot : ∀ τ, m < τ → sourcePositiveRayInverse ℓ τ = ⊥) {t : ℝ} (ht : 0 < t) (x : M) :
    sourceRayExtension ℓ t x =
      ⨆ τ : Iio m, ((t * τ.1 : ℝ) : EReal) + sourcePositiveRayInverse ℓ τ.1 x := by
  rw [ray_positive_inversion h ht x]
  exact iSup_real_eq_iSup_Iio (q := fun τ ↦ sourcePositiveRayInverse ℓ τ x)
    (sourceRayLegendre_inverse_antitone ℓ x) (fun τ hτ ↦ by rw [hbot τ hτ]; rfl) t

/-- The condition at `-∞` (end of the proof of `lma:LegendsRtoTC`): the regularized supremum of
the inverse Legendre transforms `ℓ*_τ`, `τ < c`, of a subgeodesic ray is its initial value. -/
theorem rayInverse_uscSup_eq_initial (h : SourceIsSubgeodesicRay omega θ ℓ) (c : ℝ)
    (hpsh : ∀ τ : Iio c, (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ τ.1)) :
    SGPT.PSH.uscSup (fun τ : Iio c ↦ sourcePositiveRayInverse ℓ τ.1) = ℓ ⟨0, by simp⟩ := by
  have hΦ := h.thetaPSH ⟨0, by simp⟩
  have : Nonempty (Iio c) := ⟨⟨c - 1, by change c - 1 < c; linarith⟩⟩
  obtain ⟨C, hC⟩ := thetaPSH_exists_upper hΦ
  have hψ : (ofFixedModel n M).IsThetaPSH θ
      (SGPT.PSH.uscSup (fun τ : Iio c ↦ sourcePositiveRayInverse ℓ τ.1)) := by
    apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    exact SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
      (fun τ ↦ (isThetaPSH_iff_nativeThetaPotential θ _).mp (hpsh τ)) (C := C)
      (fun τ x ↦ (rayInverse_le_initial h τ.1 x).trans (hC x))
  apply le_antisymm
  · apply uscRegularization_le (sourceThetaPSH_upperSemicontinuous hΦ)
    intro x
    exact iSup_le fun τ ↦ rayInverse_le_initial h τ.1 x
  · apply (sourceQuasiEverywhere_le_iff hΦ hψ).mp
    apply (sourceQuasiEverywhere_iff_native _).mpr
    apply ((sourceQuasiEverywhere_iff_native _).mp
      (sourceSubgeodesicLeftLimit_quasiEverywhere (subgeodesicRay_unitSegment h))).mono
    intro x hx
    have hL := tendsto_sourceSubgeodesicLeftLimit (subgeodesicRay_unitSegment h) x
    rw [hx] at hL
    have hb := boundary_le_iSup_iInf (g := fun s ↦ sourceRayExtension ℓ s x)
      (h.positiveEpigraph_convex x) (fun s hs ↦ subgeodesicRay_lt_top h hs x) hL c
    exact hb.trans
      (le_uscRegularization (fun y ↦ ⨆ τ : Iio c, sourcePositiveRayInverse ℓ τ.1 y) x)

/-! ### Replacing a segment of a subgeodesic ray by the geodesic between its endpoints -/

/-- The Perron geodesic from `R_a` to `R_b`, in physical time `t ∈ [a, b]`. -/
def perronSegment (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (R : SourceRayFamily M) (a b t : ℝ) :
    M → EReal :=
  sourcePerronClosedSlice omega θ (sourceRayExtension R a) (sourceRayExtension R b)
    ((t - a) / (b - a))

/-- The ray `R` with its restriction to `(a, b)` replaced by the geodesic from `R_a` to `R_b`
(proof of `lma:LegsendsTCtoR`). -/
def perronReplacement (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (R : SourceRayFamily M) (a b : ℝ) :
    SourceRayFamily M :=
  fun t ↦ sourceSubgeodesicReplacementCurve (sourceRayExtension R)
    (perronSegment omega θ R a b) a b t.1

variable {R : SourceRayFamily M}

omit [BorelSpace M] [ConnectedSpace M] in
theorem perronSegment_endpoints (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (R : SourceRayFamily M) {a b : ℝ}
    (hab : a < b) :
    perronSegment omega θ R a b a = sourceRayExtension R a ∧
      perronSegment omega θ R a b b = sourceRayExtension R b := by
  constructor
  · simp only [perronSegment, sub_self, zero_div,
      sourcePerronClosedSlice, closedSubgeodesicSlice_zero]
  · simp only [perronSegment, div_self (sub_pos.mpr hab).ne',
      sourcePerronClosedSlice, closedSubgeodesicSlice_one]

theorem perronSegment_subgeodesic (hR : SourceIsSubgeodesicRay omega θ R) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) :
    SourceSubgeodesicClosedInterval omega θ a b (perronSegment omega θ R a b) := by
  have hL := (hR a b ha hab.le).2
  have hP := hL.sourcePerron_isSubgeodesicFrom
  have he := perronSegment_endpoints omega θ R hab
  refine ⟨hab.le, ?_⟩
  rw [he.1, he.2]
  apply hP.congr_Ioo
  intro s hs
  have htime : (s * b + (1 - s) * a - a) / (b - a) = s := by
    field_simp [(sub_pos.mpr hab).ne']
    ring
  simp only [perronSegment, htime, sourcePerronClosedSlice,
    closedSubgeodesicSlice_eq_curve hs]

omit [ConnectedSpace M] in
theorem le_perronSegment (hR : SourceIsSubgeodesicRay omega θ R) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) {t : ℝ} (ht : t ∈ Ioo a b) :
    sourceRayExtension R t ≤ perronSegment omega θ R a b t := by
  have hL := (hR a b ha hab.le).2
  let s : ℝ := (t - a) / (b - a)
  have hs : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr ht.1) (sub_pos.mpr hab),
      (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])⟩
  have htime : s * b + (1 - s) * a = t := by
    dsimp [s]
    field_simp [(sub_pos.mpr hab).ne']
    ring
  have hc : (fun q ↦ sourceRayExtension R (q * b + (1 - q) * a)) ∈
      sourcePerronCompetitors omega θ (sourceRayExtension R a) (sourceRayExtension R b) :=
    ⟨_, _, hL.1, hL.2.1, le_rfl, le_rfl, hL⟩
  have hdom := sourcePerron_competitor_le hc s
  change sourceRayExtension R t ≤ sourcePerronClosedSlice omega θ
    (sourceRayExtension R a) (sourceRayExtension R b) s
  rw [sourcePerronClosedSlice, closedSubgeodesicSlice_eq_curve hs]
  simpa only [htime] using hdom

theorem perronSegment_le_linear (hR : SourceIsSubgeodesicRay omega θ R) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) {c m : ℝ}
    (hb : ∀ (t : Ici (0 : ℝ)) (x : M), R t x ≤ ((c + t.1 * m : ℝ) : EReal))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : M) :
    perronSegment omega θ R a b t x ≤ ((c + t * m : ℝ) : EReal) := by
  have hL := (hR a b ha hab.le).2
  have hP := hL.sourcePerron_isSubgeodesicFrom
  let s : ℝ := (t - a) / (b - a)
  have hs : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr ht.1) (sub_pos.mpr hab),
      (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])⟩
  have hc := hP.le_closedChord (a := 0) (b := 1) le_rfl le_rfl zero_lt_one
    ⟨hs.1.le, hs.2.le⟩ x
  simp only [mul_zero, mul_one, zero_add, closedSubgeodesicSlice_zero,
    closedSubgeodesicSlice_one] at hc
  have hba : sourceRayExtension R a x ≤ ((c + a * m : ℝ) : EReal) := by
    rw [sourceRayExtension_nonneg R a ha]
    exact hb ⟨a, ha⟩ x
  have hbb : sourceRayExtension R b x ≤ ((c + b * m : ℝ) : EReal) := by
    rw [sourceRayExtension_nonneg R b (ha.trans hab.le)]
    exact hb ⟨b, ha.trans hab.le⟩ x
  have hbound := hc.trans (eRealChord_mono hba hbb hs.1.le hs.2.le)
  rw [SubgeodesicInfimum.eRealChord_coe_coe] at hbound
  have heq : (1 - s) * (c + a * m) + s * (c + b * m) = c + t * m := by
    dsimp [s]
    field_simp [(sub_pos.mpr hab).ne']
    ring
  simpa only [perronSegment, sourcePerronClosedSlice, heq, s] using hbound

omit [BorelSpace M] [ConnectedSpace M] in
/-- Outside `(a, b)` the replacement is the original ray. -/
theorem perronReplacement_of_not_mem (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (R : SourceRayFamily M) (a b : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hout : t ∉ Ioo a b) :
    sourceRayExtension (perronReplacement omega θ R a b) t = sourceRayExtension R t := by
  rw [sourceRayExtension_nonneg _ _ ht]
  simp only [perronReplacement, sourceSubgeodesicReplacementCurve, if_neg hout]

omit [BorelSpace M] [ConnectedSpace M] in
/-- Inside `(a, b)` the replacement is the geodesic from `R_a` to `R_b`. -/
theorem perronReplacement_of_mem (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (R : SourceRayFamily M) (a b : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (hin : t ∈ Ioo a b) :
    sourceRayExtension (perronReplacement omega θ R a b) t = perronSegment omega θ R a b t := by
  rw [sourceRayExtension_nonneg _ _ ht]
  simp only [perronReplacement, sourceSubgeodesicReplacementCurve, if_pos hin]

omit [ConnectedSpace M] in
/-- The replacement dominates the original ray. -/
theorem le_perronReplacement (hR : SourceIsSubgeodesicRay omega θ R) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) {t : ℝ} (ht : 0 ≤ t) :
    sourceRayExtension R t ≤ sourceRayExtension (perronReplacement omega θ R a b) t := by
  by_cases hin : t ∈ Ioo a b
  · rw [perronReplacement_of_mem omega θ R a b ht hin]
    exact le_perronSegment hR ha hab hin
  · rw [perronReplacement_of_not_mem omega θ R a b ht hin]

/-- The replacement keeps a linear upper bound of the original ray. -/
theorem perronReplacement_le_linear (hR : SourceIsSubgeodesicRay omega θ R) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) {c m : ℝ}
    (hb : ∀ (t : Ici (0 : ℝ)) (x : M), R t x ≤ ((c + t.1 * m : ℝ) : EReal))
    (t : Ici (0 : ℝ)) (x : M) :
    perronReplacement omega θ R a b t x ≤ ((c + t.1 * m : ℝ) : EReal) := by
  classical
  unfold perronReplacement sourceSubgeodesicReplacementCurve
  by_cases ht : t.1 ∈ Ioo a b
  · simp only [if_pos ht]
    exact perronSegment_le_linear hR ha hab hb ht x
  · simp only [if_neg ht]
    rw [sourceRayExtension_nonneg R t.1 t.2]
    exact hb t x

/-- The replacement of a subgeodesic ray is a subgeodesic ray (gluing lemma
`lma:subgeodgluing`). -/
theorem perronReplacement_isSubgeodesic (hR : SourceIsSubgeodesicRay omega θ R) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) :
    SourceIsSubgeodesicRay omega θ (perronReplacement omega θ R a b) := by
  intro A B hA hAB
  let T : ℝ := Max.max B b + 1
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hT : 0 < T := lt_of_lt_of_le hb (le_max_right B b) |>.trans (by dsimp [T]; linarith)
  have hBT : B < T := by dsimp [T]; linarith [le_max_left B b]
  have hbT : b < T := by dsimp [T]; linarith [le_max_right B b]
  let c : ℝ → M → EReal := fun s ↦ sourceRayExtension R (s * T)
  let r : ℝ → M → EReal := fun s ↦ perronSegment omega θ R a b (s * T)
  have hbase : SourceSubgeodesicClosedInterval omega θ 0 1 c := by
    apply sourceSubgeodesicClosedInterval_unit_iff.mpr
    have hh := (hR 0 T le_rfl hT.le).2
    simpa only [c, mul_zero, zero_mul, mul_one, one_mul, add_zero] using hh
  have ha' : 0 ≤ a / T := div_nonneg ha hT.le
  have hb' : b / T ≤ 1 := (div_le_one hT).mpr hbT.le
  have hab' : a / T < b / T := (div_lt_div_iff_of_pos_right hT).mpr hab
  have htime (s : ℝ) : (s * (b / T) + (1 - s) * (a / T)) * T =
      s * b + (1 - s) * a := by
    field_simp [hT.ne']
  have hr : SourceSubgeodesicClosedInterval omega θ (a / T) (b / T) r := by
    refine ⟨hab'.le, ?_⟩
    have hh := (perronSegment_subgeodesic hR ha hab).2
    simpa only [r, htime, div_mul_cancel₀ a hT.ne', div_mul_cancel₀ b hT.ne'] using hh
  have he := perronSegment_endpoints omega θ R hab
  have hleft : r (a / T) = c (a / T) := by
    dsimp [r, c]
    rw [div_mul_cancel₀ a hT.ne']
    exact he.1
  have hright : r (b / T) = c (b / T) := by
    dsimp [r, c]
    rw [div_mul_cancel₀ b hT.ne']
    exact he.2
  have hdom (s : ℝ) (hs : s ∈ Ioo (a / T) (b / T)) : c s ≤ r s := by
    apply le_perronSegment hR ha hab
    exact ⟨(div_lt_iff₀ hT).mp hs.1, (lt_div_iff₀ hT).mp hs.2⟩
  let q := sourceSubgeodesicReplacementCurve c r (a / T) (b / T)
  have hq : SourceSubgeodesicClosedInterval omega θ 0 1 q :=
    source_subgeodesic_gluing hbase ha' hb' hab' hr hleft hright hdom
  have hread (s : ℝ) (hs : 0 ≤ s) : q s =
      sourceRayExtension (perronReplacement omega θ R a b) (s * T) := by
    rw [sourceRayExtension_nonneg _ _ (mul_nonneg hs hT.le)]
    have hm : s ∈ Ioo (a / T) (b / T) ↔ s * T ∈ Ioo a b :=
      and_congr (div_lt_iff₀ hT) (lt_div_iff₀ hT)
    simp only [q, sourceSubgeodesicReplacementCurve, perronReplacement, hm, c, r]
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

end SGPT.TestCurve.RWNTwisted
