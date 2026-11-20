import SGPT.PSH.SourceTestCurveLegendreAlgebra
import SGPT.PSH.SourcePerronStability
import SGPT.PSH.SourceSubgeodesicRays
import SGPT.PSH.SourceGeodesicOrder
import SGPT.Convex.HalfLine
import SGPT.Foundations.Analysis.Pending.SubgeodesicBoundaryUpperControl

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Spatial regularization is a PROOF object only: the final original
Legendre map remains the literal unregularized source supremum. -/
def sourceTestCurveRegularizedLegendre (Γ : SourceTestCurvePredata θ) (t : ℝ) :
    M → EReal := uscRegularization (sourceTestCurveRawLegendre Γ t)

/-- Every original real parameter gives the SAME actual regularized family. -/
theorem SourceTestCurvePredata.regularizedLegendre_eq_uscSup
    (Γ : SourceTestCurvePredata θ) (t : ℝ) :
    sourceTestCurveRegularizedLegendre Γ t =
      uscSup (fun σ : Iio Γ.max ↦ fun x ↦ Γ.potential σ x + ((t * σ.1 : ℝ) : EReal)) := by
  apply congrArg uscRegularization
  funext x
  rw [Γ.rawLegendre_eq_iSup_open t x]
  exact iSup_congr fun σ ↦ add_comm _ _

/-- The ACTUAL zero-time regularization equals the original limit definition,
without claiming that the RAW supremum has that assigned value. -/
theorem SourceTestCurvePredata.regularizedLegendre_zero
    (Γ : SourceTestCurvePredata θ) :
    sourceTestCurveRegularizedLegendre Γ 0 = sourceTestCurveLimit Γ := by
  rw [Γ.regularizedLegendre_eq_uscSup]
  apply congrArg uscRegularization
  funext x
  simp only [zero_mul, EReal.coe_zero, add_zero]

/-- The produced finite real upper bound survives genuine upper regularization. -/
theorem SourceTestCurvePredata.regularizedLegendre_le_cutoff
    (Γ : SourceTestCurvePredata θ) {t : ℝ} (ht : 0 ≤ t) :
    sourceTestCurveRegularizedLegendre Γ t ≤ fun _ ↦ ((t * Γ.max : ℝ) : EReal) :=
  uscRegularization_le upperSemicontinuous_const (Γ.rawLegendre_le_cutoff ht)

private lemma affine_slice_upper (Γ : SourceTestCurvePredata θ) {t : ℝ} (ht : 0 ≤ t)
    (σ : Iio Γ.max) (x : M) :
    Γ.potential σ x + ((t * σ.1 : ℝ) : EReal) ≤ ((t * Γ.max : ℝ) : EReal) := by
  calc
    _ ≤ (0 : EReal) + ((t * σ.1 : ℝ) : EReal) :=
      add_le_add (show Γ.potential σ x ≤ (0 : EReal) from Γ.le_zero σ x) le_rfl
    _ ≤ _ := by
      simpa only [zero_add] using EReal.coe_le_coe
        (mul_le_mul_of_nonneg_left (show σ.1 ≤ Γ.max from le_of_lt σ.2) ht)

/-- Genuine arbitrary-family theta-PSH stability produces the actual regularized
slice, with SAME-member nondegeneracy, no supplied supremum certificate. -/
theorem SourceTestCurvePredata.regularizedLegendre_thetaPSH
    (Γ : SourceTestCurvePredata θ) {t : ℝ} (ht : 0 ≤ t) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveRegularizedLegendre Γ t) := by
  have : Nonempty (Iio Γ.max) := ⟨⟨Γ.max - 1,
    by change Γ.max - 1 < Γ.max; linarith⟩⟩
  rw [Γ.regularizedLegendre_eq_uscSup]
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  exact SubgeodesicSupremumInterior.isThetaPshPotential_uscRegularization_iSup
    (fun σ ↦ (Γ.native_thetaPSH σ).add_const (t * σ.1)) (affine_slice_upper Γ ht)

/-- The actual original nonnegative-time domain, including its ACTUAL initial value. -/
def sourceTestCurveRegularizedRay (Γ : SourceTestCurvePredata θ) : SourceRayFamily M :=
  fun t ↦ sourceTestCurveRegularizedLegendre Γ t.1

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Existing full arbitrary-family Perron stability manufactures EVERY source
closed segment and both original GLOBAL L1 endpoints, including a=0 and a=b. -/
theorem SourceTestCurvePredata.regularizedRay_isSubgeodesic
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ) :
    SourceIsSubgeodesicRay omega θ (sourceTestCurveRegularizedRay Γ) := by
  intro a b ha hab
  have hb : 0 ≤ b := ha.trans hab
  have : Nonempty (Iio Γ.max) := ⟨⟨Γ.max - 1,
    by change Γ.max - 1 < Γ.max; linarith⟩⟩
  let curve : Iio Γ.max → ℝ → M → EReal := fun σ s x ↦
    Γ.potential σ x + ((((b - a) * σ.1) * s + a * σ.1 : ℝ) : EReal)
  let u₀ : Iio Γ.max → M → EReal := fun σ x ↦
    Γ.potential σ x + ((a * σ.1 : ℝ) : EReal)
  let u₁ : Iio Γ.max → M → EReal := fun σ x ↦
    Γ.potential σ x + ((b * σ.1 : ℝ) : EReal)
  have h (σ : Iio Γ.max) : SourceSubgeodesicFrom omega θ (curve σ) (u₀ σ) (u₁ σ) := by
    have hh := (sourceSubgeodesic_const omega (Γ.thetaPSH σ)).affineTranslated
      ((b - a) * σ.1) (a * σ.1)
    change SourceSubgeodesicFrom omega θ
      (fun s x ↦ Γ.potential σ x + ((((b - a) * σ.1) * s + a * σ.1 : ℝ) : EReal))
      (fun x ↦ Γ.potential σ x + ((a * σ.1 : ℝ) : EReal))
      (fun x ↦ Γ.potential σ x + (((b - a) * σ.1 + a * σ.1 : ℝ) : EReal)) at hh
    have he : (b - a) * σ.1 + a * σ.1 = b * σ.1 := by ring
    simpa only [curve, u₀, u₁, he] using hh
  have hP := sourceSubgeodesic_uscSup omega h
    ⟨a * Γ.max, affine_slice_upper Γ ha⟩ ⟨b * Γ.max, affine_slice_upper Γ hb⟩
  have heq (s : ℝ) : uscSup (fun σ ↦ curve σ s) =
      sourceTestCurveRegularizedLegendre Γ (s * b + (1 - s) * a) := by
    rw [Γ.regularizedLegendre_eq_uscSup]
    apply congrArg uscRegularization
    funext x
    apply iSup_congr
    intro σ
    change Γ.potential σ x + _ = Γ.potential σ x + _
    congr 2
    ring
  have he₀ : uscSup u₀ = sourceTestCurveRegularizedLegendre Γ a := by
    simpa only [u₀] using (Γ.regularizedLegendre_eq_uscSup a).symm
  have he₁ : uscSup u₁ = sourceTestCurveRegularizedLegendre Γ b := by
    simpa only [u₁] using (Γ.regularizedLegendre_eq_uscSup b).symm
  rw [he₀, he₁] at hP
  refine ⟨hab, ?_⟩
  rw [sourceRayExtension_nonneg (sourceTestCurveRegularizedRay Γ) a ha,
    sourceRayExtension_nonneg (sourceTestCurveRegularizedRay Γ) b hb]
  apply hP.congr_Ioo
  intro s hs
  have htime : 0 ≤ s * b + (1 - s) * a := by
    have hh := mul_nonneg hs.1.le (sub_nonneg.mpr hab)
    nlinarith
  rw [sourceRayExtension_nonneg (sourceTestCurveRegularizedRay Γ) _ htime]
  exact heq s


omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Genuine existing affine extended-constant epigraphs and arbitrary suprema
produce convexity of the LITERAL raw transform, including all its poles. -/
theorem SourceTestCurvePredata.rawLegendre_convex (Γ : SourceTestCurvePredata θ) (x : M) :
    SGPT.Convex.IsConvex (fun t ↦ sourceTestCurveRawLegendre Γ t x) := by
  change SGPT.Convex.IsConvex (fun t : ℝ ↦
    ⨆ σ : ℝ, ((t * σ : ℝ) : EReal) + sourceTestCurveAt Γ σ x)
  apply SGPT.Convex.isConvex_iSup
  intro σ
  simpa only [SGPT.Convex.scalarPairing, LinearMap.mul_apply', sub_eq_add_neg,
    neg_neg, mul_comm] using
    SGPT.Convex.isConvex_linear_sub (SGPT.Convex.scalarPairing σ) (-sourceTestCurveAt Γ σ x)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The original raw positive-time epigraph is a genuine convex restriction. -/
theorem SourceTestCurvePredata.rawLegendre_positiveEpigraph_convex
    (Γ : SourceTestCurvePredata θ) (x : M) :
    Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧ sourceTestCurveRawLegendre Γ p.1 x ≤ (p.2 : EReal)} := by
  have hh := ((convex_Ioi (0 : ℝ)).prod (convex_univ : Convex ℝ (univ : Set ℝ))).inter
    (Γ.rawLegendre_convex x)
  convert hh using 1
  ext p
  simp [SGPT.Convex.epigraph]

omit [ConnectedSpace M] in
/-- Every genuine original subgeodesic ray has the actual positive-time
convex epigraph. This transports EXISTING closed-trace convexity by real
scaling; its equal-time, zero-weight and bottom cases are already proved. -/
theorem SourceIsSubgeodesicRay.positiveEpigraph_convex
    {omega : KahlerBackground n M} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) (x : M) :
    Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧ sourceRayExtension ℓ p.1 x ≤ (p.2 : EReal)} := by
  intro p hp q hq α β hα hβ hsum
  let b : ℝ := max p.1 q.1 + 1
  have hpb : p.1 < b := (le_max_left _ _).trans_lt (lt_add_one _)
  have hqb : q.1 < b := (le_max_right _ _).trans_lt (lt_add_one _)
  have hb : 0 < b := hp.1.trans hpb
  have hs := (h 0 b le_rfl hb.le).2
  have hs' : SourceSubgeodesicFrom omega θ (fun s ↦ sourceRayExtension ℓ (s * b))
      (sourceRayExtension ℓ 0) (sourceRayExtension ℓ b) := by
    simpa only [mul_zero, add_zero] using hs
  let f := sourceClosedIntervalTrace (fun s ↦ sourceRayExtension ℓ (s * b))
    (sourceRayExtension ℓ 0) (sourceRayExtension ℓ b) x
  have hread (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) b) :
      f (t / b) = sourceRayExtension ℓ t x := by
    have hti : t / b ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos ht.1 hb, (div_lt_one hb).mpr ht.2⟩
    dsimp only [f, sourceClosedIntervalTrace]
    rw [if_pos ⟨hti.1.le, hti.2.le⟩, closedSubgeodesicSlice_eq_curve hti]
    rw [div_mul_cancel₀ _ (ne_of_gt hb)]
  have hp' : (p.1 / b, p.2) ∈ SGPT.Convex.epigraph f := by
    change f (p.1 / b) ≤ (p.2 : EReal)
    rw [hread p.1 ⟨hp.1, hpb⟩]
    exact hp.2
  have hq' : (q.1 / b, q.2) ∈ SGPT.Convex.epigraph f := by
    change f (q.1 / b) ≤ (q.2 : EReal)
    rw [hread q.1 ⟨hq.1, hqb⟩]
    exact hq.2
  have hh := hs'.isConvex_closedIntervalTrace x hp' hq' hα hβ hsum
  let c : ℝ := α * p.1 + β * q.1
  have hc : c ∈ Ioo (0 : ℝ) b := by
    simpa only [c, smul_eq_mul] using
      (convex_Ioo (0 : ℝ) b) ⟨hp.1, hpb⟩ ⟨hq.1, hqb⟩ hα hβ hsum
  have he : α * (p.1 / b) + β * (q.1 / b) = c / b := by dsimp [c]; ring
  change f (α * (p.1 / b) + β * (q.1 / b)) ≤ ((α * p.2 + β * q.2 : ℝ) : EReal) at hh
  rw [he, hread c hc] at hh
  exact ⟨hc.1, hh⟩

/-- The genuine produced regularized ray supplies precisely the positive-time
convex epigraph required by the EXISTING half-line rational/inversion mothers. -/
theorem SourceTestCurvePredata.regularizedLegendre_positiveEpigraph_convex
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ) (x : M) :
    Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧
      sourceTestCurveRegularizedLegendre Γ p.1 x ≤ (p.2 : EReal)} := by
  have hh := (Γ.regularizedRay_isSubgeodesic omega).positiveEpigraph_convex x
  convert hh using 1
  ext p
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    simpa only [sourceRayExtension_nonneg (sourceTestCurveRegularizedRay Γ) p.1 hp.1.le,
      sourceTestCurveRegularizedRay] using hp.2
  · intro hp
    refine ⟨hp.1, ?_⟩
    simpa only [sourceRayExtension_nonneg (sourceTestCurveRegularizedRay Γ) p.1 hp.1.le,
      sourceTestCurveRegularizedRay] using hp.2


omit [ConnectedSpace M] in
/-- Existing actual joint USC of a source segment, transported by genuine
real affine time, gives joint USC on the ORIGINAL positive-time product. -/
theorem SourceIsSubgeodesicRay.joint_positive_upperSemicontinuous
    {omega : KahlerBackground n M} {ℓ : SourceRayFamily M}
    (h : SourceIsSubgeodesicRay omega θ ℓ) :
    UpperSemicontinuous (fun p : M × Ioi (0 : ℝ) ↦ sourceRayExtension ℓ p.2.1 p.1) := by
  intro p
  let b : ℝ := 2 * p.2.1
  have ht : 0 < p.2.1 := p.2.2
  have hb : 0 < b := by dsimp [b]; linarith
  have htb : p.2.1 < b := by dsimp [b]; linarith
  have hseg := (h 0 b le_rfl hb.le).2
  have hn := (sourceSubgeodesicFrom_iff_native omega θ _ _ _).mp hseg
  have htime : p.2.1 / b ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ht hb, (div_lt_one hb).mpr htb⟩
  have husc := SubgeodesicBoundaryUpperControl.upperSemicontinuousAt_of_isSubgeodesicFrom
    hn p.1 htime
  let T : M × Ioi (0 : ℝ) → M × ℝ := fun q ↦ (q.1, q.2.1 / b)
  have hT : Continuous T := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).div_const b)
  have hh := UpperSemicontinuousAt.comp (g := T) (c := p) husc hT.continuousAt
  simpa only [T, Function.comp_def, mul_zero, add_zero, div_mul_cancel₀ _ (ne_of_gt hb)] using hh

/-- The produced regularized source ray has joint USC in exactly the original
space × positive-real-time domain, without an off-time hypothesis. -/
theorem SourceTestCurvePredata.regularizedLegendre_joint_upperSemicontinuous
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ) :
    UpperSemicontinuous (fun p : M × Ioi (0 : ℝ) ↦
      sourceTestCurveRegularizedLegendre Γ p.2.1 p.1) := by
  have hh := (Γ.regularizedRay_isSubgeodesic omega).joint_positive_upperSemicontinuous
  have heq : (fun p : M × Ioi (0 : ℝ) ↦
      sourceRayExtension (sourceTestCurveRegularizedRay Γ) p.2.1 p.1) =
      (fun p : M × Ioi (0 : ℝ) ↦ sourceTestCurveRegularizedLegendre Γ p.2.1 p.1) := by
    funext p
    exact congrFun (sourceRayExtension_nonneg (sourceTestCurveRegularizedRay Γ)
      p.2.1 (show 0 ≤ p.2.1 from le_of_lt p.2.2)) p.1
  rwa [heq] at hh


omit [MeasurableSpace M] [BorelSpace M] in
/-- A genuine ACTUAL Choquet subsequence and proved negligible-set pluripolarity
give the raw-vs-USC equality in the EXACT original source QE sense. -/
theorem SourceTestCurvePredata.rawLegendre_eq_regularized_quasiEverywhere
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    {t : ℝ} (ht : 0 ≤ t) :
    SourceQuasiEverywhere (n := n) (fun x ↦
      sourceTestCurveRawLegendre Γ t x = sourceTestCurveRegularizedLegendre Γ t x) := by
  classical
  have : Nonempty (Iio Γ.max) := ⟨⟨Γ.max - 1,
    by change Γ.max - 1 < Γ.max; linarith⟩⟩
  let u : Iio Γ.max → M → EReal := fun σ x ↦
    Γ.potential σ x + ((t * σ.1 : ℝ) : EReal)
  obtain ⟨s, hs, hseq⟩ := exists_seq_uscRegularization_iSup_eq (F := range u) (range_nonempty u)
  choose idx hidx using hs
  have hsg (j : ℕ) : IsThetaPshPotential (atlasClosedFormToNative θ).val (s j) := by
    rw [← hidx j]
    exact (Γ.native_thetaPSH (idx j)).add_const (t * (idx j).1)
  have hsC (j : ℕ) (x : M) : s j x ≤ ((t * Γ.max : ℝ) : EReal) := by
    rw [← hidx j]
    exact affine_slice_upper Γ ht (idx j) x
  have hneg := NegligibleSetsPluripolarProof.negligibleSetsPluripolar
    omega (atlasClosedFormToNative θ) s (t * Γ.max) hsg hsC
  have hfun : (⨆ σ, u σ) = fun x ↦ ⨆ σ, u σ x := funext fun x ↦ iSup_apply
  have hreg : uscRegularization (⨆ j, s j) = sourceTestCurveRegularizedLegendre Γ t := by
    rw [sSup_range, hfun] at hseq
    exact hseq.trans (Γ.regularizedLegendre_eq_uscSup t).symm
  have hsraw (j : ℕ) (x : M) : s j x ≤ sourceTestCurveRawLegendre Γ t x := by
    rw [← hidx j]
    simpa only [u, sourceTestCurveRawLegendre,
      sourceTestCurveAt_of_lt Γ (show (idx j).1 < Γ.max from (idx j).2), add_comm] using
      (le_iSup (fun σ : ℝ ↦ ((t * σ : ℝ) : EReal) + sourceTestCurveAt Γ σ x) (idx j).1)
  apply (sourceQuasiEverywhere_iff_native _).mpr
  refine hneg.mono fun x hx ↦ le_antisymm
    (le_uscRegularization (sourceTestCurveRawLegendre Γ t) x) ?_
  rw [congrFun hreg x] at hx
  apply hx.trans
  simpa only [iSup_apply] using (iSup_le fun j ↦ hsraw j x)

omit [MeasurableSpace M] [BorelSpace M] in
/-- ONE genuine source pluripolar exceptional set controls ALL positive
rational times. Only the actual rational type is enumerated, not source nets. -/
theorem SourceTestCurvePredata.rawLegendre_eq_regularized_rat_quasiEverywhere
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ) :
    SourceQuasiEverywhere (n := n) (fun x ↦ ∀ q : ℚ, 0 < q →
      sourceTestCurveRawLegendre Γ (q : ℝ) x =
        sourceTestCurveRegularizedLegendre Γ (q : ℝ) x) := by
  obtain ⟨r, hr⟩ := exists_surjective_nat ℚ
  have hP (j : ℕ) : QuasiEverywhere (n := n) (fun x ↦ 0 < r j →
      sourceTestCurveRawLegendre Γ ((r j : ℚ) : ℝ) x =
        sourceTestCurveRegularizedLegendre Γ ((r j : ℚ) : ℝ) x) := by
    by_cases hj : 0 < r j
    · have hreal : (0 : ℝ) ≤ ((r j : ℚ) : ℝ) := by exact_mod_cast hj.le
      exact ((sourceQuasiEverywhere_iff_native _).mp
        (Γ.rawLegendre_eq_regularized_quasiEverywhere omega hreal)).mono fun _ hx _ ↦ hx
    · exact quasiEverywhere_of_forall fun _ hx ↦ False.elim (hj hx)
  have hh := RooftopObstacleQuasiEverywhere.quasiEverywhere_forall
    (PluripolarOuterCapacity.countablyStablePluripolar omega) hP
  apply (sourceQuasiEverywhere_iff_native _).mpr
  refine hh.mono ?_
  intro x hx q hq
  obtain ⟨j, rfl⟩ := hr q
  exact hx j hq

/-- Existing EXACT positive-rational conjugacy upgrades one actual countable
QE equality to equality of the entire conjugates at ALL real dual parameters. -/
theorem SourceTestCurvePredata.halfLineConjugates_eq_quasiEverywhere
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ) :
    SourceQuasiEverywhere (n := n) (fun x ↦ ∀ τ : ℝ,
      SGPT.Convex.halfLineConjugate (fun t ↦ sourceTestCurveRegularizedLegendre Γ t x) τ =
        SGPT.Convex.halfLineConjugate (fun t ↦ sourceTestCurveRawLegendre Γ t x) τ) := by
  apply (sourceQuasiEverywhere_iff_native _).mpr
  refine ((sourceQuasiEverywhere_iff_native _).mp
    (Γ.rawLegendre_eq_regularized_rat_quasiEverywhere omega)).mono ?_
  intro x hx τ
  have hraw (t : ℝ) (ht : 0 < t) : sourceTestCurveRawLegendre Γ t x < ⊤ :=
    (Γ.rawLegendre_le_cutoff ht.le x).trans_lt (EReal.coe_lt_top _)
  have hreg (t : ℝ) (ht : 0 < t) : sourceTestCurveRegularizedLegendre Γ t x < ⊤ :=
    (Γ.regularizedLegendre_le_cutoff ht.le x).trans_lt (EReal.coe_lt_top _)
  rw [SGPT.Convex.halfLineConjugate_eq_iSup_rat
    (Γ.regularizedLegendre_positiveEpigraph_convex omega x) hreg τ,
    SGPT.Convex.halfLineConjugate_eq_iSup_rat (Γ.rawLegendre_positiveEpigraph_convex x) hraw τ]
  apply iSup_congr
  intro q
  apply iSup_congr
  intro hq
  rw [hx q hq]

private lemma positiveInf_eq_neg_halfLineConjugate (u : ℝ → EReal) (τ : ℝ) :
    (⨅ t : Ioi (0 : ℝ), u t.1 - ((t.1 * τ : ℝ) : EReal)) =
      -SGPT.Convex.halfLineConjugate u τ := by
  have heq : SGPT.Convex.halfLineConjugate u τ =
      ⨆ t : Ioi (0 : ℝ), ((t.1 * τ : ℝ) : EReal) - u t.1 := by
    apply le_antisymm
    · apply iSup_le
      intro t
      apply iSup_le
      intro ht
      exact le_iSup (fun t : Ioi (0 : ℝ) ↦ ((t.1 * τ : ℝ) : EReal) - u t.1) ⟨t, ht⟩
    · apply iSup_le
      intro t
      exact le_iSup_of_le t.1 (le_iSup_of_le t.2 le_rfl)
  rw [heq]
  have hneg : -(⨆ t : Ioi (0 : ℝ), ((t.1 * τ : ℝ) : EReal) - u t.1) =
      ⨅ t : Ioi (0 : ℝ), -(((t.1 * τ : ℝ) : EReal) - u t.1) :=
    map_iSup EReal.negOrderIso _
  rw [hneg]
  apply iInf_congr
  intro t
  rw [EReal.neg_sub (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))]
  simp only [sub_eq_add_neg, add_comm]

/-- The EXACT whole positive-time infimum of the actual regularized functions. -/
def sourceTestCurveRegularizedInverse (Γ : SourceTestCurvePredata θ) (τ : ℝ) : M → EReal :=
  fun x ↦ ⨅ t : Ioi (0 : ℝ), sourceTestCurveRegularizedLegendre Γ t.1 x -
    ((t.1 * τ : ℝ) : EReal)

/-- The SAME one genuinely pluripolar failure set gives the whole-real inverse
identity QE, retaining both extended endpoints without an uncountable union. -/
theorem SourceTestCurvePredata.regularizedInverse_quasiEverywhere
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ) :
    SourceQuasiEverywhere (n := n) (fun x ↦ ∀ τ : ℝ,
      sourceTestCurveRegularizedInverse Γ τ x = sourceTestCurveAt Γ τ x) := by
  apply (sourceQuasiEverywhere_iff_native _).mpr
  refine ((sourceQuasiEverywhere_iff_native _).mp
    (Γ.halfLineConjugates_eq_quasiEverywhere omega)).mono ?_
  intro x hx τ
  rw [sourceTestCurveRegularizedInverse,
    positiveInf_eq_neg_halfLineConjugate (fun t ↦ sourceTestCurveRegularizedLegendre Γ t x) τ,
    hx τ]
  have hh := Γ.at_eq_iInf_positive_rawLegendre τ x
  rw [positiveInf_eq_neg_halfLineConjugate (fun t ↦ sourceTestCurveRawLegendre Γ t x) τ] at hh
  exact hh.symm


private lemma iInf_affineTime_eq (u : ℝ → EReal) {a b : ℝ} (hab : a < b) :
    (⨅ s : Ioo (0 : ℝ) 1, u (s.1 * b + (1 - s.1) * a)) =
      ⨅ t : Ioo a b, u t.1 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  apply le_antisymm
  · apply le_iInf
    intro t
    let s : ℝ := (t.1 - a) / (b - a)
    have hs : s ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos (sub_pos.mpr t.2.1) hba, (div_lt_one hba).mpr (by linarith [t.2.2])⟩
    have he : s * b + (1 - s) * a = t.1 := by
      dsimp [s]
      field_simp [ne_of_gt hba]
      ring
    exact (iInf_le (fun s : Ioo (0 : ℝ) 1 ↦ u (s.1 * b + (1 - s.1) * a))
      ⟨s, hs⟩).trans_eq (congrArg u he)
  · apply le_iInf
    intro s
    have hs0 : 0 < s.1 := s.2.1
    have hs1 : s.1 < 1 := s.2.2
    have ht : s.1 * b + (1 - s.1) * a ∈ Ioo a b := by
      constructor
      · nlinarith [mul_pos hs0 hba]
      · nlinarith [mul_pos (sub_pos.mpr hs1) hba]
    exact iInf_le (fun t : Ioo a b ↦ u t.1) ⟨s.1 * b + (1 - s.1) * a, ht⟩

/-- EXISTING genuine fixed-strip Kiselman and affine translation give the
actual physical-interval infimum, by a complete literal real reindexing. -/
theorem SourceSubgeodesicClosedInterval.isThetaPSH_timeInf_sub_affine
    {omega : KahlerBackground n M} {curve : ℝ → M → EReal} {a b : ℝ}
    (h : SourceSubgeodesicClosedInterval omega θ a b curve) (hab : a < b) (τ : ℝ) :
    (ofFixedModel n M).IsThetaPSH θ
      (fun x ↦ ⨅ t : Ioo a b, curve t.1 x - ((t.1 * τ : ℝ) : EReal)) := by
  have hh := h.2.affineTranslated (-(b - a) * τ) (-a * τ)
  have hinf := hh.isThetaPSH_sliceInfimum
  have heq : sourceSliceInfimum
      (affineTranslatedCurve (fun s ↦ curve (s * b + (1 - s) * a))
        (-(b - a) * τ) (-a * τ)) =
      (fun x ↦ ⨅ t : Ioo a b, curve t.1 x - ((t.1 * τ : ℝ) : EReal)) := by
    funext x
    change (⨅ s : Ioo (0 : ℝ) 1, curve (s.1 * b + (1 - s.1) * a) x +
      ((-(b - a) * τ * s.1 + -a * τ : ℝ) : EReal)) = _
    calc
      _ = ⨅ s : Ioo (0 : ℝ) 1,
          (curve (s.1 * b + (1 - s.1) * a) x -
            (((s.1 * b + (1 - s.1) * a) * τ : ℝ) : EReal)) := by
        apply iInf_congr
        intro s
        have hc : (-(b - a) * τ * s.1 + -a * τ : ℝ) =
            -((s.1 * b + (1 - s.1) * a) * τ) := by ring
        rw [hc, EReal.coe_neg]
        rfl
      _ = _ := iInf_affineTime_eq (fun t ↦ curve t x - ((t * τ : ℝ) : EReal)) hab
  rwa [heq] at hinf


private def legendreWindowLeft (j : ℕ) : ℝ := 1 / ((j : ℝ) + 2)
private def legendreWindowRight (j : ℕ) : ℝ := (j : ℝ) + 2

private lemma legendreWindow_pos (j : ℕ) : 0 < legendreWindowLeft j ∧
    legendreWindowLeft j < legendreWindowRight j := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hright : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  refine ⟨one_div_pos.mpr hright, ?_⟩
  change 1 / ((j : ℝ) + 2) < (j : ℝ) + 2
  apply (div_lt_iff₀ hright).mpr
  nlinarith

private lemma legendreWindow_mono {i j : ℕ} (hij : i ≤ j) :
    Ioo (legendreWindowLeft i) (legendreWindowRight i) ⊆
      Ioo (legendreWindowLeft j) (legendreWindowRight j) := by
  have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hright : legendreWindowRight i ≤ legendreWindowRight j := by
    dsimp [legendreWindowRight]; linarith
  have hleft : legendreWindowLeft j ≤ legendreWindowLeft i :=
    one_div_le_one_div_of_le (show (0 : ℝ) < (i : ℝ) + 2 by positivity)
      (show (i : ℝ) + 2 ≤ (j : ℝ) + 2 by linarith)
  exact fun _ ht ↦ ⟨hleft.trans_lt ht.1, ht.2.trans_le hright⟩

private lemma legendreWindow_exhaust {t : ℝ} (ht : 0 < t) :
    ∃ j : ℕ, t ∈ Ioo (legendreWindowLeft j) (legendreWindowRight j) := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max t (1 / t))
  have hj2 : (j : ℝ) < (j : ℝ) + 2 := lt_add_of_pos_right _ (by norm_num)
  have htr : t < (j : ℝ) + 2 := ((le_max_left _ _).trans_lt hj).trans hj2
  have hir : 1 / t < (j : ℝ) + 2 := ((le_max_right _ _).trans_lt hj).trans hj2
  exact ⟨j, (one_div_lt (by positivity) ht).mpr hir, htr⟩

private def legendreWindowInf (Γ : SourceTestCurvePredata θ) (τ : ℝ) (j : ℕ) :
    M → EReal := fun x ↦ ⨅ t : Ioo (legendreWindowLeft j) (legendreWindowRight j),
      sourceTestCurveRegularizedLegendre Γ t.1 x - ((t.1 * τ : ℝ) : EReal)

private lemma legendreWindowInf_thetaPSH (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) (τ : ℝ) (j : ℕ) :
    (ofFixedModel n M).IsThetaPSH θ (legendreWindowInf Γ τ j) := by
  have hwin := legendreWindow_pos j
  have hh := ((Γ.regularizedRay_isSubgeodesic omega)
    (legendreWindowLeft j) (legendreWindowRight j) hwin.1.le hwin.2.le).isThetaPSH_timeInf_sub_affine hwin.2 τ
  convert hh using 1
  funext x
  apply iInf_congr
  intro t
  rw [sourceRayExtension_nonneg (sourceTestCurveRegularizedRay Γ) t.1
    (hwin.1.trans t.2.1).le]
  rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private lemma legendreWindowInf_antitone (Γ : SourceTestCurvePredata θ) (τ : ℝ)
    (x : M) : Antitone (fun j ↦ legendreWindowInf Γ τ j x) := by
  intro i j hij
  apply le_iInf
  intro t
  exact iInf_le (fun s : Ioo (legendreWindowLeft j) (legendreWindowRight j) ↦
    sourceTestCurveRegularizedLegendre Γ s.1 x - ((s.1 * τ : ℝ) : EReal))
      ⟨t.1, legendreWindow_mono hij t.2⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private lemma legendreWindowInf_exhaust (Γ : SourceTestCurvePredata θ) (τ : ℝ) :
    (fun x ↦ ⨅ j : ℕ, legendreWindowInf Γ τ j x) =
      sourceTestCurveRegularizedInverse Γ τ := by
  funext x
  apply le_antisymm
  · apply le_iInf
    intro t
    obtain ⟨j, hj⟩ := legendreWindow_exhaust (show 0 < t.1 from t.2)
    exact (iInf_le (fun j ↦ legendreWindowInf Γ τ j x) j).trans
      (iInf_le (fun s : Ioo (legendreWindowLeft j) (legendreWindowRight j) ↦
        sourceTestCurveRegularizedLegendre Γ s.1 x - ((s.1 * τ : ℝ) : EReal)) ⟨t.1, hj⟩)
  · apply le_iInf
    intro j
    apply le_iInf
    intro t
    exact iInf_le (fun s : Ioi (0 : ℝ) ↦ sourceTestCurveRegularizedLegendre Γ s.1 x -
      ((s.1 * τ : ℝ) : EReal)) ⟨t.1, (legendreWindow_pos j).1.trans t.2.1⟩

omit [MeasurableSpace M] [BorelSpace M] in
private lemma at_le_legendreWindowInf (Γ : SourceTestCurvePredata θ) (τ : ℝ) (j : ℕ) :
    sourceTestCurveAt Γ τ ≤ legendreWindowInf Γ τ j := by
  intro x
  rw [Γ.at_eq_iInf_positive_rawLegendre τ x]
  apply le_iInf
  intro t
  have ht : 0 < t.1 := (legendreWindow_pos j).1.trans t.2.1
  exact (iInf_le (fun s : Ioi (0 : ℝ) ↦ sourceTestCurveRawLegendre Γ s.1 x -
    ((s.1 * τ : ℝ) : EReal)) ⟨t.1, ht⟩).trans
      (EReal.sub_le_sub (le_uscRegularization (sourceTestCurveRawLegendre Γ t.1) x) le_rfl)

/-- Genuine actual compact decreasing-PSH noncollapse is manufactured from
original fixedpoint normalization, even when the actual cutoff mass is zero. -/
theorem SourceTestCurvePredata.regularizedInverse_thetaPSH
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    {τ : ℝ} (hτ : τ ≤ Γ.max) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveRegularizedInverse Γ τ) := by
  have hat : (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveAt Γ τ) :=
    (source_test_curve_extension_whole Γ).2.2.2 τ hτ
  have hfix : sourceSingularityEnvelope θ (sourceTestCurveAt Γ τ) =
      sourceTestCurveAt Γ τ := by
    rcases hτ.eq_or_lt with heq | hlt
    · rw [heq, sourceTestCurveAt_eq_max]
      exact Γ.cutoff_fixedPoint
    · rw [sourceTestCurveAt_of_lt Γ hlt]
      exact Γ.fixedPoint ⟨τ, hlt⟩
  have hsup := sourceOrdinaryFixedPoint_globalSup_zero hat hfix
  have hlower (j : ℕ) : (0 : EReal) ≤ ⨆ x, legendreWindowInf Γ τ j x := by
    rw [← hsup]
    exact iSup_mono (at_le_legendreWindowInf Γ τ j)
  have hh := (SGPT.PSH.isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    (fun j ↦ (isThetaPSH_iff_nativeThetaPotential θ _).mp
      (legendreWindowInf_thetaPSH omega Γ τ j))
    (legendreWindowInf_antitone Γ τ) 0 (by simpa only [EReal.coe_zero] using hlower)).1
  rw [legendreWindowInf_exhaust] at hh
  exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr hh

/-- Actual QE comparison applies only AFTER both actual PSH functions have
been produced, giving the literal every-point identity through the cutoff. -/
theorem SourceTestCurvePredata.regularizedInverse_eq_of_le
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    {τ : ℝ} (hτ : τ ≤ Γ.max) :
    sourceTestCurveRegularizedInverse Γ τ = sourceTestCurveAt Γ τ := by
  have hc := Γ.regularizedInverse_thetaPSH omega hτ
  have ha := (source_test_curve_extension_whole Γ).2.2.2 τ hτ
  have hqe := (sourceQuasiEverywhere_iff_native _).mp (Γ.regularizedInverse_quasiEverywhere omega)
  apply le_antisymm
  · exact (sourceQuasiEverywhere_le_iff hc ha).mp
      ((sourceQuasiEverywhere_iff_native _).mpr (hqe.mono fun x hx ↦ (hx τ).le))
  · exact (sourceQuasiEverywhere_le_iff ha hc).mp
      ((sourceQuasiEverywhere_iff_native _).mpr (hqe.mono fun x hx ↦ (hx τ).ge))


omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The literal super-cutoff infimum is bottom, forced by an ACTUAL finite
negative-slope bound and concrete arbitrarily large positive times. -/
theorem SourceTestCurvePredata.regularizedInverse_eq_bot_of_gt
    (Γ : SourceTestCurvePredata θ) {τ : ℝ} (hτ : Γ.max < τ) :
    sourceTestCurveRegularizedInverse Γ τ = ⊥ := by
  funext x
  apply (EReal.eq_bot_iff_forall_lt _).mpr
  intro r
  let t : ℝ := Max.max 1 ((r - 1) / (Γ.max - τ))
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcoef : Γ.max - τ < 0 := sub_neg.mpr hτ
  have hm : t * (Γ.max - τ) ≤ r - 1 := by
    calc
      _ ≤ ((r - 1) / (Γ.max - τ)) * (Γ.max - τ) :=
        mul_le_mul_of_nonpos_right (le_max_right _ _) hcoef.le
      _ = r - 1 := div_mul_cancel₀ _ (ne_of_lt hcoef)
  have hbound : sourceTestCurveRegularizedInverse Γ τ x ≤
      ((t * (Γ.max - τ) : ℝ) : EReal) := by
    calc
      _ ≤ sourceTestCurveRegularizedLegendre Γ t x - ((t * τ : ℝ) : EReal) :=
        iInf_le (fun s : Ioi (0 : ℝ) ↦ sourceTestCurveRegularizedLegendre Γ s.1 x -
          ((s.1 * τ : ℝ) : EReal)) ⟨t, ht⟩
      _ ≤ ((t * Γ.max : ℝ) : EReal) - ((t * τ : ℝ) : EReal) :=
        EReal.sub_le_sub (Γ.regularizedLegendre_le_cutoff ht.le x) le_rfl
      _ = _ := by rw [← EReal.coe_sub, mul_sub]
  exact hbound.trans_lt (EReal.coe_lt_coe (by linarith))

/-- ALL original real parameters, all original points and both infinite
endpoints, with the PSH/QE recovery and super-cutoff branch produced. -/
theorem SourceTestCurvePredata.regularizedInverse_eq
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ) (τ : ℝ) :
    sourceTestCurveRegularizedInverse Γ τ = sourceTestCurveAt Γ τ := by
  by_cases hτ : τ ≤ Γ.max
  · exact Γ.regularizedInverse_eq_of_le omega hτ
  · rw [Γ.regularizedInverse_eq_bot_of_gt (lt_of_not_ge hτ),
      sourceTestCurveAt_of_gt Γ (lt_of_not_ge hτ)]

/-- DIRECT reuse of the already complete genuine half-line inversion theorem.
No scalar duality/continuity/separation proof is duplicated here. -/
theorem SourceTestCurvePredata.rawLegendre_eq_regularized
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    {t : ℝ} (ht : 0 < t) :
    sourceTestCurveRawLegendre Γ t = sourceTestCurveRegularizedLegendre Γ t := by
  funext x
  have hfinite (s : ℝ) (hs : 0 < s) :
      sourceTestCurveRegularizedLegendre Γ s x < ⊤ :=
    (Γ.regularizedLegendre_le_cutoff hs.le x).trans_lt (EReal.coe_lt_top _)
  have hinv := SGPT.Convex.halfLineConjugate_inversion
    (Γ.regularizedLegendre_positiveEpigraph_convex omega x) hfinite ht
  have hconj (τ : ℝ) : SGPT.Convex.halfLineConjugate
      (fun s ↦ sourceTestCurveRegularizedLegendre Γ s x) τ = -sourceTestCurveAt Γ τ x := by
    have hh := congrFun (Γ.regularizedInverse_eq omega τ) x
    change (⨅ s : Ioi (0 : ℝ), sourceTestCurveRegularizedLegendre Γ s.1 x -
      ((s.1 * τ : ℝ) : EReal)) = sourceTestCurveAt Γ τ x at hh
    rw [positiveInf_eq_neg_halfLineConjugate
      (fun s ↦ sourceTestCurveRegularizedLegendre Γ s x) τ] at hh
    simpa only [neg_neg] using congrArg Neg.neg hh
  calc
    _ = SGPT.Convex.conjugate SGPT.Convex.scalarPairing
        (SGPT.Convex.halfLineConjugate
          (fun s ↦ sourceTestCurveRegularizedLegendre Γ s x)) t := by
      simp only [SGPT.Convex.conjugate, SGPT.Convex.scalarPairing, LinearMap.mul_apply',
        hconj, sub_eq_add_neg, neg_neg, sourceTestCurveRawLegendre]
      apply iSup_congr
      intro τ
      rw [mul_comm]
    _ = _ := hinv

/-- The literal ORIGINAL raw value is genuinely source theta-PSH at EVERY
positive time. Its actual formula contains NO upper regularization. -/
theorem SourceTestCurvePredata.rawLegendre_thetaPSH
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ)
    {t : ℝ} (ht : 0 < t) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveRawLegendre Γ t) := by
  rw [Γ.rawLegendre_eq_regularized omega ht]
  exact Γ.regularizedLegendre_thetaPSH ht.le

/-- ENTIRE original positive-real-domain PSH-valued map, with literally the
printed raw supremum as its underlying function. -/
def sourceTestCurveLegendrePSHMap (omega : KahlerBackground n M)
    (Γ : SourceTestCurvePredata θ) : Ioi (0 : ℝ) →
      {u : M → EReal // (ofFixedModel n M).IsThetaPSH θ u} :=
  fun t ↦ ⟨sourceTestCurveRawLegendre Γ t.1, Γ.rawLegendre_thetaPSH omega t.2⟩

/-- Actual joint USC on the exact original space × positive-time domain,
transported only after literal raw equality at EVERY point and positive time. -/
theorem SourceTestCurvePredata.rawLegendre_joint_upperSemicontinuous
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ) :
    UpperSemicontinuous (fun p : M × Ioi (0 : ℝ) ↦
      sourceTestCurveRawLegendre Γ p.2.1 p.1) := by
  have heq : (fun p : M × Ioi (0 : ℝ) ↦ sourceTestCurveRawLegendre Γ p.2.1 p.1) =
      (fun p : M × Ioi (0 : ℝ) ↦ sourceTestCurveRegularizedLegendre Γ p.2.1 p.1) := by
    funext p
    exact congrFun (Γ.rawLegendre_eq_regularized omega p.2.2) p.1
  rw [heq]
  exact Γ.regularizedLegendre_joint_upperSemicontinuous omega

/-- The original assigned-zero family. Only the POSITIVE values use the raw
formula; the original initial value is the genuine source limit. -/
def sourceTestCurveLegendreRay (Γ : SourceTestCurvePredata θ) : SourceRayFamily M :=
  fun t ↦ sourceTestCurveLegendreWithInitial Γ (sourceTestCurveLimit Γ) t.1

/-- Exact SAME nonnegative-time functions, including the assigned initial
value; no raw zero-time formula or off-time condition is inferred. -/
theorem SourceTestCurvePredata.legendreRay_eq_regularized
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ) :
    sourceTestCurveLegendreRay Γ = sourceTestCurveRegularizedRay Γ := by
  funext t
  by_cases ht : t.1 = 0
  · simp only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, ht,
      if_true, sourceTestCurveRegularizedRay, Γ.regularizedLegendre_zero]
  · have hpos : 0 < t.1 := lt_of_le_of_ne t.2 (Ne.symm ht)
    simp only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, if_neg ht,
      sourceTestCurveRegularizedRay]
    exact Γ.rawLegendre_eq_regularized omega hpos

/-- Genuine full source subgeodesic ray with every closed segment and original
GLOBAL L1 endpoint conditions, emanating from the literal source limit. -/
theorem SourceTestCurvePredata.legendreRay_emanates
    (omega : KahlerBackground n M) (Γ : SourceTestCurvePredata θ) :
    SourceSubgeodesicRayEmanatesFrom omega θ (sourceTestCurveLegendreRay Γ)
      (sourceTestCurveLimit Γ) := by
  rw [Γ.legendreRay_eq_regularized omega]
  exact ⟨Γ.regularizedRay_isSubgeodesic omega, Γ.regularizedLegendre_zero⟩

/-- WHOLE original def:Legtrans and lma:testcurvelegusc, with their original
based class, literal raw supremum, actual PSH codomain and joint USC. The
stronger subgeodesic emanation conclusion adds no GEODESIC/E1/fullmass claim. -/
theorem source_test_curve_legendre_psh_whole
    (omega : KahlerBackground n M) (Γ : SourceTestCurve θ)
    {φ : M → EReal} {hφ : SourceModelPotential θ φ}
    (hbased : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    (∀ t : ℝ, 0 < t →
      (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t)) ∧
    UpperSemicontinuous (fun p : M × Ioi (0 : ℝ) ↦
      sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata p.2.1 p.1) ∧
    SourceSubgeodesicRayEmanatesFrom omega θ
      (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata) φ := by
  refine ⟨fun _ ht ↦ Γ.toSourceTestCurvePredata.rawLegendre_thetaPSH omega ht,
    Γ.toSourceTestCurvePredata.rawLegendre_joint_upperSemicontinuous omega, ?_⟩
  change sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ at hbased
  rw [← hbased]
  exact Γ.toSourceTestCurvePredata.legendreRay_emanates omega

end SGPT.PSH.VariableComplexAtlas
