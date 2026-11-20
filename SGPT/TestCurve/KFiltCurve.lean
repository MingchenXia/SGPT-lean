import SGPT.TestCurve.KFiltObstacle
import SGPT.TestCurve.RWNClauseReduction

/-!
# The test curve of a filtration and its ray (abstract metered section ring)

Sources `ex:RWN` and `rmk:max_filt` (chapter *Test curves*). Blueprint `claude-k-filt`, nodes
`claude-k-filt:curve`, `claude-k-filt:reduction`.

For a filtration `𝓕` of a metered graded section ring `D` (`SectionMetric`, curvature
`θ = c₁(L, h)`) on a compact connected complex manifold, this file ports the projective
packaging (`SGPT.TestCurve.TestConf`, `SGPT.TestCurve.RWN`) to the abstract interface:

* `GradedFiltration.IModelClause` (clause (a) of `ex:RWN`: `Γ^𝓕_τ` is `𝓘`-model for `τ < τ(𝓕)`)
  and `GradedFiltration.MinimalClause` (clause (b), `eq:Gammatautheta`: `Γ^𝓕_τ = V_θ` for
  `τ ≤ -C`);
* `GradedFiltration.iModelClause_of_minimalClause`: (b) implies (a) when `{θ}` is big;
* `GradedFiltration.filtrationTestCurve`: under (a), (b), the family `(Γ^𝓕_τ)_{τ<τ(𝓕)}` is a
  test curve (`def:testcur`) for the atlas form of `θ` with `Γ_max = τ(𝓕)`, based at `V_θ`,
  `𝓘`-model and bounded (`filtrationTestCurve_mem_based`, `_mem_iModel`, `_isBounded`);
* `GradedFiltration.filtrationRay_mem_maximal`: its Legendre transform `Γ^{𝓕*}` is a maximal
  geodesic ray emanating from `V_θ` (`rmk:max_filt`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.KFilt

open Filter Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.FirstPass.POrder SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH.VariableComplexAtlas
open SGPT.TestCurve.RWN SGPT.LineBundle
open scoped Topology

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
variable {S : ℕ → Type} [∀ k, AddCommGroup (S k)] [∀ k, Module ℂ (S k)]
  {mul : ∀ k k' : ℕ, S k → S k' → S (k + k')}

namespace SectionMetric

variable (D : SectionMetric n X S mul)

/-- `θ = c₁(L, h)` on the original atlas of `X` (`nativeClosedFormToAtlas` keeps the
coefficients). -/
def atlasForm : AtlasClosedRealOneOneForm (ofFixedModel n X) :=
  nativeClosedFormToAtlas D.θ

theorem atlasForm_native : atlasClosedFormToNative D.atlasForm = D.θ :=
  sourceNativeAtlasForm_roundTrip _

/-- `V_θ` of the original atlas is the native `V_θ`. -/
theorem sourceMinimalEnvelope_atlasForm :
    sourceMinimalEnvelope D.atlasForm = thetaPshSupremum D.θ.val := by
  rw [sourceMinimalEnvelope_eq_native, D.atlasForm_native]

/-- `V_θ` is a model potential of positive mass when `{θ}` is big. -/
theorem sourceMinimalEnvelope_atlasForm_model [CompactSpace X] [ConnectedSpace X]
    [MeasurableSpace X] [BorelSpace X] (omega : KahlerBackground n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative D.θ)) :
    SourceModelPotential D.atlasForm (sourceMinimalEnvelope D.atlasForm) := by
  apply sourceMinimalEnvelope_model omega
  rw [D.atlasForm_native]
  exact hbig

end SectionMetric

namespace GradedFiltration

variable (F : GradedFiltration mul) (D : SectionMetric n X S mul)

/-- Clause (a) of `ex:RWN`: for every `τ < τ(𝓕)`, `Γ^𝓕_τ` is `𝓘`-model. -/
def IModelClause : Prop :=
  ∀ τ : ℝ, (τ : EReal) < F.slope →
    IsIModelPotential D.θ.val (F.testCurvePotential D τ)

/-- Open clause (b) of `ex:RWN`, `eq:Gammatautheta`: `Γ^𝓕_τ = V_θ` for every `τ ≤ -C`, where
`C` is the constant of the linear boundedness `eq:Flinearlybdd` of `𝓕`. -/
def MinimalClause : Prop :=
  ∀ τ : ℝ, τ ≤ -(F.bound : ℝ) → F.testCurvePotential D τ = thetaPshSupremum D.θ.val

/-! ### Degenerate filtrations -/

/-- If `H⁰(X, L^k) = 0`, then `Γ^{𝓕,k}_τ ≡ -∞`. -/
theorem sectionPotential_eq_bot_of_subsingleton {k : ℕ}
    (hk : Subsingleton (S k)) (τ : ℝ) :
    F.sectionPotential D k τ = fun _ => ⊥ := by
  have h : (fun x => ⨆ s : F.normalizedSections D k τ, D.logNormSq k s.1 x) =
      fun _ => (⊥ : EReal) := by
    funext x
    refine le_antisymm (iSup_le fun s => ?_) bot_le
    have h0 : s.1 = 0 := Subsingleton.elim _ _
    rw [h0, D.logNormSq_zero]
  change uscRegularization (fun x =>
    ⨆ s : F.normalizedSections D k τ, D.logNormSq k s.1 x) = _
  rw [h, uscRegularization_const]

/-- If `τ(𝓕) = -∞` (no nonzero section in positive degree), the obstacle is `-∞`. -/
theorem obstacle_eq_bot_of_slope_eq_bot (hs : F.slope = ⊥) (τ : ℝ) :
    F.obstacle D τ = fun _ => ⊥ := by
  have hsub : ∀ k : ℕ, 0 < k → Subsingleton (S k) := by
    intro k hk
    by_contra hn
    have : Nontrivial (S k) := not_subsingleton_iff_nontrivial.mp hn
    exact F.slope_ne_bot hk hs
  have hraw : F.rawObstacle D τ = fun _ => ⊥ := by
    funext x
    refine le_antisymm (iSup₂_le fun k hk => ?_) bot_le
    change F.sectionPotential D k τ x / ((k : ℝ) : EReal) ≤ ⊥
    rw [sectionPotential_eq_bot_of_subsingleton F D (hsub k hk) τ]
    exact (EReal.bot_div_of_pos_ne_top (EReal.coe_pos.mpr (Nat.cast_pos.mpr hk))
      (EReal.coe_ne_top _)).le
  change uscRegularization (F.rawObstacle D τ) = _
  rw [hraw, uscRegularization_const]

/-- The `P`-envelope of the constant `-∞` is `-∞`: it has no competitor. -/
theorem singularityEnvelope_bot [Nonempty X]
    (θ : SmoothRealForm n X 2) :
    singularityEnvelope θ (fun _ => (⊥ : EReal)) = fun _ => ⊥ := by
  apply singularityEnvelope_of_empty
  refine Set.eq_empty_of_forall_notMem fun u hu => ?_
  obtain ⟨⟨hu, -⟩, C, hC⟩ := hu
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, -, hy⟩ := hu.2 x univ isOpen_univ (mem_univ x)
  exact hy (le_bot_iff.mp (by simpa using hC y (mem_univ y)))

/-- Clause (b) of `ex:RWN` forces `τ(𝓕) > -∞` when `{θ}` is big. -/
theorem slope_ne_bot_of_minimalClause [Nonempty X]
    [CompactSpace X]
    (hbig : IsBigClass (RealBottChern.ofRepresentative D.θ))
    (hb : F.MinimalClause D) : F.slope ≠ ⊥ := by
  intro hs
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum
    D.θ hbig
  have h := hb (-(F.bound : ℝ)) le_rfl
  have hbot : F.testCurvePotential D (-(F.bound : ℝ)) = fun _ => ⊥ := by
    change singularityEnvelope D.θ.val (F.obstacle D _) = _
    rw [obstacle_eq_bot_of_slope_eq_bot F D hs]
    exact singularityEnvelope_bot (X := X) _
  rw [hbot] at h
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, -, hy⟩ := hV.2 x univ isOpen_univ (mem_univ x)
  exact hy (congrFun h y).symm

/-! ### The test curve of a filtration -/

variable [CompactSpace X] [ConnectedSpace X] [∀ k, FiniteDimensional ℂ (S k)]

/-- The real number `τ(𝓕)` (finite under clause (b) and bigness). -/
def slopeReal : ℝ := F.slope.toReal

omit [∀ k, FiniteDimensional ℂ (S k)] in
/-- `τ < τ(𝓕)` in `ℝ` gives `τ < τ(𝓕)` in `[-∞, ∞]`. -/
theorem coe_lt_slope_of_lt {hbig : IsBigClass (RealBottChern.ofRepresentative D.θ)}
    {hb : F.MinimalClause D} {τ : ℝ} (hτ : τ < slopeReal F) : (τ : EReal) < F.slope := by
  have hne := slope_ne_bot_of_minimalClause F D hbig hb
  rw [← EReal.coe_toReal F.slope_ne_top hne]
  exact EReal.coe_lt_coe_iff.mpr hτ

omit [∀ k, FiniteDimensional ℂ (S k)] in
/-- `τ(𝓕)` is the real number `slopeReal F`. -/
theorem coe_slopeReal (hbig : IsBigClass (RealBottChern.ofRepresentative D.θ))
    (hb : F.MinimalClause D) : ((slopeReal F : ℝ) : EReal) = F.slope :=
  EReal.coe_toReal F.slope_ne_top (slope_ne_bot_of_minimalClause F D hbig hb)

omit [∀ k, FiniteDimensional ℂ (S k)] in
/-- Under clause (a), `Γ^𝓕_τ` is a `P`-model potential: `P_θ[Γ^𝓕_τ] = Γ^𝓕_τ`. -/
theorem singularityEnvelope_testCurvePotential (ha : F.IModelClause D) {τ : ℝ}
    (hτ : (τ : EReal) < F.slope) :
    singularityEnvelope D.θ.val (F.testCurvePotential D τ) =
      F.testCurvePotential D τ := by
  have hI := ha τ hτ
  have hpsh : IsThetaPshPotential D.θ.val (F.testCurvePotential D τ) := hI.1
  conv_lhs => rw [hI.2]
  rw [singularityEnvelope_iSingularityEnvelope D.θ.val D.θ.property.1
    D.θ.property.2 (LocalPotentials.closedRealOneOne_hasLocalPotentials _) _ hpsh]
  exact hI.2.symm

/-- Chords of the family `τ ↦ Γ^𝓕_τ` in both orders. -/
theorem testCurvePotential_chord {p q τ₀ : ℝ} (hp : (p : EReal) < τ₀) (hq : (q : EReal) < τ₀)
    (hτ₀ : (τ₀ : EReal) ≤ F.slope) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ThetaPshConvexCombination.convexComb t (F.testCurvePotential D p)
        (F.testCurvePotential D q) ≤ F.testCurvePotential D (t * p + (1 - t) * q) := by
  have hps : (p : EReal) < F.slope := hp.trans_le hτ₀
  have hqs : (q : EReal) < F.slope := hq.trans_le hτ₀
  rcases lt_trichotomy q p with hlt | heq | hgt
  · exact F.testCurvePotential_concave D hlt hps ht0 ht1
  · subst heq
    intro x
    rw [ThetaPshConvexCombination.convexComb_apply, show t * q + (1 - t) * q = q by ring]
    induction F.testCurvePotential D q x with
    | bot =>
      rw [EReal.mul_bot_of_pos (EReal.coe_pos.mpr ht0),
        EReal.mul_bot_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ht1))]
      exact bot_le
    | top =>
      rw [EReal.mul_top_of_pos (EReal.coe_pos.mpr ht0),
        EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ht1))]
      exact le_top
    | coe r =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr (by ring_nf; exact le_rfl)
  · have h := F.testCurvePotential_concave D hgt hqs (sub_pos.mpr ht1)
      (by linarith : 1 - t < 1)
    intro x
    have hx := h x
    rw [ThetaPshConvexCombination.convexComb_apply] at hx ⊢
    rw [show 1 - (1 - t) = t by ring] at hx
    rw [show t * p + (1 - t) * q = (1 - t) * q + t * p by ring, add_comm]
    exact hx

variable [MeasurableSpace X] [BorelSpace X]
variable (omega : KahlerBackground n X) (hbig : IsBigClass (RealBottChern.ofRepresentative D.θ))
  (ha : F.IModelClause D) (hb : F.MinimalClause D)

/-- The family `(Γ^𝓕_τ)_{τ < τ(𝓕)}` of `ex:RWN` as test-curve data (`def:testcur`, without the
mass clause). -/
def filtrationTestCurvePredata : SourceTestCurvePredata (D.atlasForm) where
  max := slopeReal F
  potential τ := F.testCurvePotential D τ.1
  thetaPSH τ := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    rw [D.atlasForm_native]
    exact F.testCurvePotential_isThetaPshPotential D (coe_lt_slope_of_lt F D (hbig := hbig)
      (hb := hb) τ.2)
  antitone x := fun τ τ' h => F.testCurvePotential_anti D h x
  concave x := by
    apply sourceTestCurveNegativeTrace_convex_of_chords
    intro p q t ht0 ht1
    exact testCurvePotential_chord F D (EReal.coe_lt_coe_iff.mpr p.2)
      (EReal.coe_lt_coe_iff.mpr q.2) (coe_slopeReal F D hbig hb).le ht0 ht1
  fixedPoint τ := by
    rw [sourceSingularityEnvelope_eq_native, D.atlasForm_native]
    exact singularityEnvelope_testCurvePotential F D ha
      (coe_lt_slope_of_lt F D (hbig := hbig) (hb := hb) τ.2)

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem filtrationTestCurvePredata_max :
    (filtrationTestCurvePredata F D hbig ha hb).max = slopeReal F := rfl

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem filtrationTestCurvePredata_potential (τ : Iio (slopeReal F)) :
    (filtrationTestCurvePredata F D hbig ha hb).potential τ = F.testCurvePotential D τ.1 := rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- `Γ_{-∞} = usc sup_{τ < τ(𝓕)} Γ^𝓕_τ = V_θ`. -/
theorem filtrationTestCurvePredata_limit :
    sourceTestCurveLimit (filtrationTestCurvePredata F D hbig ha hb) =
      sourceMinimalEnvelope (D.atlasForm) := by
  rw [D.sourceMinimalEnvelope_atlasForm]
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum
    D.θ hbig
  let τ₀ : ℝ := min (slopeReal F - 1) (-(F.bound : ℝ))
  have hτ₀ : τ₀ < slopeReal F := (min_le_left _ _).trans_lt (by linarith)
  have hsup : (fun x => ⨆ τ : Iio (slopeReal F),
      (filtrationTestCurvePredata F D hbig ha hb).potential τ x) =
      thetaPshSupremum D.θ.val := by
    funext x
    apply le_antisymm
    · refine iSup_le fun τ => ?_
      have hpsh := F.testCurvePotential_isThetaPshPotential D
        (coe_lt_slope_of_lt F D (hbig := hbig) (hb := hb) τ.2)
      exact le_thetaPshSupremum hpsh (singularityEnvelope_le_zero _ _) x
    · refine le_trans (le_of_eq ?_) (le_iSup (fun τ : Iio (slopeReal F) =>
        (filtrationTestCurvePredata F D hbig ha hb).potential τ x) ⟨τ₀, hτ₀⟩)
      rw [filtrationTestCurvePredata_potential, hb τ₀ (min_le_right _ _)]
  exact (congrArg uscRegularization hsup).trans
    (uscRegularization_eq hV.1.quasiPlurisubharmonic.upperSemicontinuous)

include omega in
/-- **The test curve `Γ^𝓕` of `ex:RWN`** (conditional on the open clauses (a), (b)): the actual
family `(Γ^𝓕_τ)_{τ < τ(𝓕)}` with `Γ_max = τ(𝓕)`; the mass of `Γ_{-∞} = V_θ` is positive. -/
def filtrationTestCurve : SourceTestCurve (D.atlasForm) where
  toSourceTestCurvePredata := filtrationTestCurvePredata F D hbig ha hb
  positiveLimitMass := by
    obtain ⟨hV, -, hmass⟩ := D.sourceMinimalEnvelope_atlasForm_model omega hbig
    have hlim := filtrationTestCurvePredata_limit F D hbig ha hb
    have key : ∀ (u : X → EReal)
        (hu : (ofFixedModel n X).IsThetaPSH
          (D.atlasForm) u),
        u = sourceMinimalEnvelope (D.atlasForm) →
        0 < sourcePotentialNonPluripolarMeasure (D.atlasForm) u hu univ := by
      rintro u hu rfl
      exact hmass
    exact key _ _ hlim

@[simp] theorem filtrationTestCurve_max :
    (filtrationTestCurve F D omega hbig ha hb).max = slopeReal F := rfl

@[simp] theorem filtrationTestCurve_potential (τ : Iio (slopeReal F)) :
    (filtrationTestCurve F D omega hbig ha hb).potential τ = F.testCurvePotential D τ.1 := rfl

/-- `Γ_max = τ(𝓕)` in `[-∞, ∞]`. -/
theorem coe_filtrationTestCurve_max :
    (((filtrationTestCurve F D omega hbig ha hb).max : ℝ) : EReal) = F.slope :=
  coe_slopeReal F D hbig hb

/-- `Γ^𝓕 ∈ TC(X, θ; V_θ)`. -/
theorem filtrationTestCurve_mem_based :
    filtrationTestCurve F D omega hbig ha hb ∈ SourceTestCurvesBased (D.atlasForm)
      (sourceMinimalEnvelope (D.atlasForm))
      (D.sourceMinimalEnvelope_atlasForm_model omega hbig) :=
  filtrationTestCurvePredata_limit F D hbig ha hb

/-- **Conclusion of `ex:RWN`** (from its clauses (a), (b)): `Γ^𝓕` is an `𝓘`-model test curve
based at `V_θ`, i.e. `Γ^𝓕 ∈ 𝓔^{NA}(X, θ)`. -/
theorem filtrationTestCurve_mem_iModel :
    filtrationTestCurve F D omega hbig ha hb ∈ SourceIModelTestCurves (D.atlasForm)
      (sourceMinimalEnvelope (D.atlasForm))
      (D.sourceMinimalEnvelope_atlasForm_model omega hbig) := by
  refine ⟨filtrationTestCurve_mem_based F D omega hbig ha hb, fun τ => ?_⟩
  rw [D.atlasForm_native]
  exact ha τ.1 (coe_lt_slope_of_lt F D (hbig := hbig) (hb := hb) τ.2)

/-- **Conclusion of `ex:RWN`** (from clause (b)): `Γ^𝓕` is bounded, `Γ^𝓕_τ = V_θ` for all
`τ` near `-∞`. -/
theorem filtrationTestCurve_isBounded :
    SourceTestCurveIsBounded (sourceMinimalEnvelope (D.atlasForm))
      (filtrationTestCurve F D omega hbig ha hb) := by
  rw [D.sourceMinimalEnvelope_atlasForm]
  have hne : Nonempty (Iio (filtrationTestCurve F D omega hbig ha hb).max) :=
    ⟨⟨slopeReal F - 1, by change slopeReal F - 1 < slopeReal F; linarith⟩⟩
  rw [SourceTestCurveIsBounded, Filter.eventually_atBot]
  refine ⟨⟨min (slopeReal F - 1) (-(F.bound : ℝ)),
    (min_le_left _ _).trans_lt (by change slopeReal F - 1 < slopeReal F; linarith)⟩,
    fun τ hτ => ?_⟩
  exact hb τ.1 (le_trans (Subtype.coe_le_coe.mpr hτ) (min_le_right _ _))

/-- **Source `rmk:max_filt`** (conditional on the open clauses (a), (b) of `ex:RWN`): the ray
`Γ^{𝓕*}` induced by the filtration `𝓕` — the Legendre transform of the actual family
`(Γ^𝓕_τ)_{τ < τ(𝓕)}` — is a maximal geodesic ray emanating from `V_θ`, for every Kähler
background `ω` of `X^{an}`. -/
theorem filtrationRay_mem_maximal (omega' : KahlerBackground n X) :
    sourceTestCurveLegendreRay (filtrationTestCurvePredata F D hbig ha hb) ∈
      sourceMaximalGeodesicRays omega' (D.atlasForm)
        (sourceMinimalEnvelope (D.atlasForm))
        (D.sourceMinimalEnvelope_atlasForm_model omega hbig) := by
  have hbased := filtrationTestCurve_mem_based F D omega hbig ha hb
  refine ⟨(source_test_curve_legendre_geodesic_whole omega' _ hbased).1, ?_⟩
  exact (sourceTestCurveLegendreRay_isMaximal_iff omega' _ hbased).mpr
    (filtrationTestCurve_mem_iModel F D omega hbig ha hb).2


/-! ### Clause (b) implies clause (a) -/

omit [∀ k, FiniteDimensional ℂ (S k)] in
/-- If `H⁰(X, L^k) ≠ 0` for some `k > 0`, then `τ(𝓕) ≥ -C > -C - 1`. -/
theorem neg_bound_sub_one_lt_slope_of_nontrivial {k : ℕ} (hk : 0 < k)
    (hnt : Nontrivial (S k)) :
    ((-(F.bound : ℝ) - 1 : ℝ) : EReal) < F.slope := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hj := F.neg_bound_le_jump hk
  have h1 : ((-(F.bound : ℝ) : ℝ) : EReal) ≤ F.jump k / ((k : ℝ) : EReal) := by
    rw [EReal.le_div_iff_mul_le (EReal.coe_pos.mpr hkR) (EReal.coe_ne_top _), ← EReal.coe_mul]
    refine le_trans (le_of_eq ?_) hj
    congr 1
    ring
  have h2 : F.jump k / ((k : ℝ) : EReal) ≤ F.slope :=
    le_iSup₂ (f := fun (k : ℕ) (_ : 0 < k) => F.jump k / ((k : ℝ) : EReal)) k hk
  refine lt_of_lt_of_le ?_ (h1.trans h2)
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

omit [∀ k, FiniteDimensional ℂ (S k)] in
/-- If `τ(𝓕) > -∞`, then `τ(𝓕) > -C - 1`. -/
theorem neg_bound_sub_one_lt_slope_of_ne_bot (hs : F.slope ≠ ⊥) :
    ((-(F.bound : ℝ) - 1 : ℝ) : EReal) < F.slope := by
  by_cases hex : ∃ k : ℕ, 0 < k ∧ Nontrivial (S k)
  · obtain ⟨k, hk, hnt⟩ := hex
    exact neg_bound_sub_one_lt_slope_of_nontrivial F hk hnt
  · push Not at hex
    exfalso
    apply hs
    refine le_bot_iff.mp (iSup₂_le fun k hk => ?_)
    have hb : F.jump k = ⊥ := (F.jump_eq_bot_iff hk).mpr (not_nontrivial_iff_subsingleton.mpr
      (hex k hk))
    rw [hb, EReal.bot_div_of_pos_ne_top (EReal.coe_pos.mpr (by exact_mod_cast hk))
      (EReal.coe_ne_top _)]



omit [ConnectedSpace X] in
/-- **Positivity of the mass of the obstacle propagates**: if `∫_X θ_{ψ_{τ₀}}ⁿ > 0` for one
`τ₀ < τ(𝓕)`, then `∫_X θ_{ψ_τ}ⁿ > 0` for every `τ < τ(𝓕)`. For `τ ≤ τ₀` by monotonicity
(`thm:mono`), otherwise by concavity of `τ ↦ ψ_τ` and `∫ θ_{tu+(1-t)v}ⁿ ≥ tⁿ ∫ θ_uⁿ`. -/
theorem obstacle_hasPositiveMass_of_pos (omega : KahlerBackground n X) {τ₀ : ℝ}
    (hτ₀ : (τ₀ : EReal) < F.slope)
    (hpos₀ : HasPositivePotentialMass D.θ (F.obstacle D τ₀)
        (F.obstacle_isThetaPshPotential D hτ₀))
    {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    HasPositivePotentialMass D.θ (F.obstacle D τ)
      (F.obstacle_isThetaPshPotential D hτ) := by
  set θ := D.θ with hθ
  have hψ₀ := F.obstacle_isThetaPshPotential D hτ₀
  have hψ := F.obstacle_isThetaPshPotential D hτ
  rcases le_or_gt τ τ₀ with hle | hlt
  · exact hpos₀.trans_le (diagonalPotentialMass_mono_of_kahler omega hψ₀ hψ
      (MoreSingularOn.of_le fun x _ => F.obstacle_anti D hle x))
  · obtain ⟨τ₁, hττ₁, hτ₁⟩ := EReal.lt_iff_exists_real_btwn.mp hτ
    have hττ₁' : τ < τ₁ := EReal.coe_lt_coe_iff.mp hττ₁
    have hden : 0 < τ₁ - τ₀ := by linarith
    set t : ℝ := (τ - τ₀) / (τ₁ - τ₀) with ht_def
    have ht0 : 0 < t := div_pos (by linarith) hden
    have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
    have hpar : t * τ₁ + (1 - t) * τ₀ = τ := by
      rw [ht_def]
      field_simp
      ring
    have hψ₁ := F.obstacle_isThetaPshPotential D hτ₁
    have hcc := F.obstacle_concave D (show τ₀ < τ₁ by linarith) hτ₁ ht0 ht1
    rw [hpar] at hcc
    have hcomm : convexComb (1 - t) (F.obstacle D τ₀) (F.obstacle D τ₁) =
        convexComb t (F.obstacle D τ₁) (F.obstacle D τ₀) := by
      funext x
      rw [convexComb_apply, convexComb_apply, show 1 - (1 - t) = t by ring, add_comm]
    have h1t0 : 0 < 1 - t := by linarith
    have h1t1 : 1 - t < 1 := by linarith
    have hw := isThetaPshPotential_convexComb hψ₀ hψ₁ h1t0 h1t1
    have hscale := GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le
      (θ := θ) hψ₀ hψ₁ h1t0 h1t1 univ
    change ENNReal.ofReal ((1 - t) ^ n) * diagonalPotentialMass θ (F.obstacle D τ₀) hψ₀ ≤
      diagonalPotentialMass θ _ hw at hscale
    have hmono := diagonalPotentialMass_mono_of_kahler omega hw hψ
      (MoreSingularOn.of_le fun x _ => by rw [hcomm]; exact hcc x)
    exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (pow_pos h1t0 _)).ne' hpos₀.ne').trans_le
      (hscale.trans hmono)

/-- **Clause (a) of `ex:RWN` from the positive mass of one obstacle**: if
`∫_X θ_{ψ_{τ₀}}ⁿ > 0` for some `τ₀ < τ(𝓕)`, then every `Γ^𝓕_τ`, `τ < τ(𝓕)`, is `𝓘`-model
(`ψ_τ` is `𝓘`-good, `SGPT.LineBundle.SectionFiltration.obstacle_iGood_of_lt_slope`, and has
positive mass, so `Γ^𝓕_τ = P_θ[ψ_τ] = P_θ[ψ_τ]_𝓘`). -/
theorem iModelClause_of_obstacle_mass_pos (omega : KahlerBackground n X) {τ₀ : ℝ}
    (hτ₀ : (τ₀ : EReal) < F.slope)
    (hpos₀ : HasPositivePotentialMass D.θ (F.obstacle D τ₀)
        (F.obstacle_isThetaPshPotential D hτ₀)) :
    F.IModelClause D := by
  intro τ hτ
  exact iModel_singularityEnvelope_of_iGood (omega)
    (F.obstacle_isThetaPshPotential D hτ) (F.obstacle_iGood_of_lt_slope D omega hτ)
    (obstacle_hasPositiveMass_of_pos F D omega hτ₀ hpos₀ hτ)

/-- **Clause (b) of `ex:RWN` implies clause (a)** (`{θ}` big, unconditionally): if
`Γ^𝓕_τ = V_θ` for `τ ≤ -C`, then every `Γ^𝓕_τ`, `τ < τ(𝓕)`, is `𝓘`-model. Indeed
`τ(𝓕) > -C - 1` and `∫ θ_{ψ_{-C-1}}ⁿ = ∫ θ_{P_θ[ψ_{-C-1}]}ⁿ = ∫ θ_{V_θ}ⁿ > 0`
(`prop:Ppresmass`). -/
theorem iModelClause_of_minimalClause (omega : KahlerBackground n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative D.θ))
    (hb : F.MinimalClause D) :
    F.IModelClause D := by
  set θ := D.θ with hθ
  have hτ₀ := neg_bound_sub_one_lt_slope_of_ne_bot F
    (slope_ne_bot_of_minimalClause F D hbig hb)
  apply iModelClause_of_obstacle_mass_pos F D omega hτ₀
  have hψ₀ := F.obstacle_isThetaPshPotential D hτ₀
  have hlocal := LocalPotentials.closedRealOneOne_hasLocalPotentials θ
  have hP := Pending.singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
    hlocal _ hψ₀
  have hmass := singularityEnvelopeMassPreserving omega θ _ hψ₀ hP
  have hmodel := SingularMinimalCanonicalRay.isModelPotential_thetaPshSupremum omega θ hbig
  have hΓ : singularityEnvelope θ.val (F.obstacle D (-(F.bound : ℝ) - 1)) =
      thetaPshSupremum θ.val := hb _ (by linarith)
  change 0 < diagonalPotentialMass θ (F.obstacle D (-(F.bound : ℝ) - 1)) hψ₀
  rw [← hmass, SGPT.IGood.Misc2VolBigL.diagonalPotentialMass_congr θ hΓ hP
    hmodel.plurisubharmonic]
  exact hmodel.positive_mass

/-- **Source `rmk:max_filt` from clause (b) of `ex:RWN` alone** (clause (a) follows,
`iModelClause_of_minimalClause`): the ray `Γ^{𝓕*}` induced by `𝓕` is a maximal geodesic ray
emanating from `V_θ`, for every Kähler background `ω'`. -/
theorem filtrationRay_mem_maximal_of_minimalClause [Nonempty X] (omega : KahlerBackground n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative D.θ)) (hb : F.MinimalClause D)
    (omega' : KahlerBackground n X) :
    sourceTestCurveLegendreRay (filtrationTestCurvePredata F D hbig
        (iModelClause_of_minimalClause F D omega hbig hb) hb) ∈
      sourceMaximalGeodesicRays omega' D.atlasForm (sourceMinimalEnvelope D.atlasForm)
        (D.sourceMinimalEnvelope_atlasForm_model omega hbig) :=
  filtrationRay_mem_maximal F D omega hbig _ hb omega'

end GradedFiltration

end SGPT.TestCurve.KFilt
