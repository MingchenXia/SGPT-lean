import SGPT.Okounkov.TranscendentalWNLegendreBounded
import SGPT.Foundations.Analysis.Pending.SingularReferenceStripNonpluripolarZero
import SGPT.Foundations.Analysis.Pending.NonPluripolarGauge
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm
import SGPT.Foundations.Analysis.FirstPass.CoordinateDensityGeometry

/-!
# WN21 Theorem 3.3: reduction to the locally bounded case (package WN-LEG)

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:reduction`; `claude-tok-wn`, node
`tok-wn:legendre-ma`.  **`partialLegendreMALocalStatement : PartialLegendreMALocalStatement N`**:
for `Ω ⊆ ℂᴺ` open and `u` circle-invariant psh on `Ω × ℂ*` with `û_λ ≡ -∞` on `Ω` for
`λ ∉ [a, b]` and, for `λ ∈ [a, b]`, `û_λ` locally bounded on `Ω \ A` with `A` locally
pluripolar, every Borel `E` satisfies

  `⟨(dd^c u)^{N+1}⟩ (E × ℂ*) = (N + 1) ∫_a^b ⟨(dd^c û_λ)^N⟩ (E) dλ`.

* `a = b`: by duality `u = û_a(z) + a log |τ|²`; the non-pluripolar measure is unchanged by the
  pluriharmonic term (TN gauge invariance) and vanishes for functions of `z` alone
  (`truncationLimitMeasure_eq_zero_of_eq`); the right side is an integral over a point.
* `a < b`: on the open set `O ⊇ Ω \ A` of points with a ball where `|û_λ| ≤ C` for all
  `λ ∈ [a, b]` (concavity in `λ` for the lower bound, `û_λ ≤ u(·, 1)` and upper semicontinuity
  for the upper bound) the locally bounded case applies (`legendreIdentityOn_good`); the
  rest `Ω \ O ⊆ A` and `(Ω \ O) × ℂ*` are locally pluripolar, uncharged by the non-pluripolar
  measures.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
  SGPT.Foundations.Analysis.Pending.BedfordTaylorStripCovariance

variable {N : ℕ}

/-! ### Pluripolar sets pull back to `ℂᴺ⁺¹` -/

theorem stripFst_apply' (q : ComplexModel (N + 1)) : stripFst N q = (stripModelEquiv N q).1 := rfl

/-- `A × ℂ` is locally pluripolar in `Ω × ℂ*` when `A` is locally pluripolar in `Ω`. -/
theorem locallyPluripolarOn_preimage {A : Set (ComplexModel N)} {Ω : Opens (ComplexModel N)}
    (hA : LocallyPluripolarOn A Ω) :
    LocallyPluripolarOn (stripModelEquiv N ⁻¹' (A ×ˢ univ)) (puncturedProductOpens Ω) := by
  intro q hq
  obtain ⟨V, w, hVo, hzV, hVc, hw, ⟨a₀, ha₀V, ha₀⟩, hpole⟩ := hA _ hq.1
  refine ⟨stripDomain V, fun y => w (stripFst N y), isOpen_stripDomain hVo, hzV,
    isPreconnected_stripDomain hVc, hw.comp_continuousLinearMap (stripFst N),
    ⟨(stripModelEquiv N).symm (a₀, 0), stripModelEquiv_symm_mem_stripDomain ha₀V 0, ?_⟩,
    fun y hy hyA => hpole _ hy hyA.1⟩
  show w (stripFst N ((stripModelEquiv N).symm (a₀, 0))) ≠ ⊥
  rw [stripFst_apply', ContinuousLinearEquiv.apply_symm_apply]
  exact ha₀

/-! ### The case `a = b` -/

theorem stripLift_puncturedPlane (Ω : Opens (ComplexModel N)) :
    stripLift Ω puncturedPlane isOpen_puncturedPlane = puncturedProductOpens Ω := rfl

/-- `a log |τ|²` is smooth pluriharmonic on `Ω × ℂ*`. -/
theorem isSmoothPluriharmonicOn_mul_logNormSq (Ω : Opens (ComplexModel N)) (a : ℝ) :
    BedfordTaylor.IsSmoothPluriharmonicOn (puncturedProductOpens Ω)
      (fun q => a * logNormSq (stripModelEquiv N q).2) := by
  have hsnd : ContDiff ℝ ∞ fun q : ComplexModel (N + 1) => (stripModelEquiv N q).2 :=
    (((ContinuousLinearMap.snd ℂ (ComplexModel N) ℂ).comp
      (stripModelEquiv N : ComplexModel (N + 1) →L[ℂ] ComplexModel N × ℂ)).restrictScalars
        ℝ).contDiff
  have hL : ∀ q ∈ puncturedProductOpens Ω,
      ContDiffAt ℝ ∞ (fun q : ComplexModel (N + 1) => logNormSq (stripModelEquiv N q).2) q :=
    fun q hq => ContDiffAt.comp (g := logNormSq) (f := fun q => (stripModelEquiv N q).2) q
      (contDiffAt_logNormSq hq.2) hsnd.contDiffAt
  refine ⟨fun q hq => (contDiffAt_const.mul (hL q hq)).contDiffWithinAt, fun q hq => ?_⟩
  have h2 : ContDiffAt ℝ 2 (fun q : ComplexModel (N + 1) => logNormSq (stripModelEquiv N q).2) q :=
    (hL q hq).of_le two_le_infty
  have hfun : (fun q : ComplexModel (N + 1) => logNormSq (stripModelEquiv N q).2) =
      fun y => Real.log (Complex.normSq ((stripModelEquiv N y).2)) := by
    funext y
    rw [logNormSq, Complex.normSq_eq_norm_sq]
  have hdd : smoothDDC (fun q : ComplexModel (N + 1) => logNormSq (stripModelEquiv N q).2) q = 0 := by
    rw [hfun]
    refine PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero (Eventually.of_forall fun y => ?_)
      hq.2
    exact (((ContinuousLinearMap.snd ℂ (ComplexModel N) ℂ).comp
      (stripModelEquiv N : ComplexModel (N + 1) →L[ℂ] ComplexModel N × ℂ)).differentiableAt)
  have hH : complexHessian (fun q : ComplexModel (N + 1) => logNormSq (stripModelEquiv N q).2) q =
      0 := by
    rw [← normalizedHermitianMatrix_smoothDDC h2, hdd]
    ext j k
    simp [normalizedHermitianMatrix]
  rw [show (fun q : ComplexModel (N + 1) => a * logNormSq (stripModelEquiv N q).2) =
      a • fun q : ComplexModel (N + 1) => logNormSq (stripModelEquiv N q).2 from rfl,
    complexHessian_smul h2, hH, smul_zero]

/-- **The case `a = b`**: `u = û_a(z) + a log |τ|²` has no non-pluripolar Monge–Ampère mass. -/
theorem truncationLimitMeasure_eq_zero_of_eq {Ω : Opens (ComplexModel N)}
    {u : ComplexModel N → ℂ → EReal} {a : ℝ} {A : Set (ComplexModel N)}
    (h : IsLegendreMAData Ω u a a A)
    (hu : PlurisubharmonicOn (productModelFunction u) (puncturedProductOpens Ω)) :
    MongeAmpere.truncationLimitMeasure (puncturedProductOpens Ω) (productModelFunction u) hu = 0 := by
  set P := puncturedProductOpens Ω
  have hû := h.plurisubharmonicOn_partialLegendre a
  set v : ComplexModel (N + 1) → EReal := fun q => partialLegendre u a (stripFst N q)
  have hv : PlurisubharmonicOn v P :=
    SingularReferenceStripNonpluripolarZero.plurisubharmonicOn_comp_stripFst
      isOpen_puncturedPlane hû
  set hh : ComplexModel (N + 1) → ℝ := fun q => a * logNormSq (stripModelEquiv N q).2
  have heq : EqOn (productModelFunction u) (fun q => v q + (hh q : EReal)) P := by
    intro q hq
    have hd := partialLegendre_duality_Icc Ω.isOpen h.psh h.circleInvariant hq.1
      (fun lam hlam => h.eq_bot_of_notMem lam hlam _ hq.1) hq.2
    rw [Icc_self, iSup_singleton] at hd
    exact hd
  have hvh : PlurisubharmonicOn (fun q => v q + (hh q : EReal)) P :=
    plurisubharmonicOn_congr_of_eqOn P.isOpen hu heq
  rw [truncationLimitMeasure_congr hu hvh heq,
    ← MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal (Nat.succ_pos N) hvh]
  rw [MixedNonPluripolar.mixedTruncationLimitMeasure_add_pluriharmonic (v := fun _ => v)
    (fun _ => hv) (h := fun _ => hh) (fun _ => isSmoothPluriharmonicOn_mul_logNormSq Ω a)
    (fun _ => hvh), MixedNonPluripolar.mixedTruncationLimitMeasure_diagonal (Nat.succ_pos N) hv]
  exact SingularReferenceStripNonpluripolarZero.truncationLimitMeasure_comp_stripFst_eq_zero
    isOpen_puncturedPlane hû

/-! ### The good set `O ⊇ Ω \ A` -/

/-- The points with a ball in `Ω` on which `|û_λ| ≤ C` for all `λ ∈ [a, b]`. -/
def goodSet (Ω : Opens (ComplexModel N)) (u : ComplexModel N → ℂ → EReal) (a b : ℝ) :
    Set (ComplexModel N) :=
  {z | ∃ r > 0, ball z r ⊆ Ω ∧ ∃ C : ℝ, ∀ lam ∈ Icc a b, ∀ w ∈ ball z r,
    ((-C : ℝ) : EReal) ≤ partialLegendre u lam w ∧ partialLegendre u lam w ≤ (C : EReal)}

theorem isOpen_goodSet (Ω : Opens (ComplexModel N)) (u : ComplexModel N → ℂ → EReal) (a b : ℝ) :
    IsOpen (goodSet Ω u a b) := by
  rw [Metric.isOpen_iff]
  rintro z ⟨r, hr, hball, C, hC⟩
  refine ⟨r / 2, by linarith, fun z' hz' => ⟨r / 2, by linarith, ?_, C, fun lam hlam w hw => ?_⟩⟩
  · exact (ball_subset_ball' (by rw [mem_ball] at hz'; linarith)).trans hball
  · refine hC lam hlam w ?_
    rw [mem_ball] at hz' hw ⊢
    linarith [dist_triangle w z' z]

theorem goodSet_subset (Ω : Opens (ComplexModel N)) (u : ComplexModel N → ℂ → EReal) (a b : ℝ) :
    goodSet Ω u a b ⊆ Ω := fun _ ⟨_, hr, hball, _⟩ => hball (mem_ball_self hr)

/-- `û_λ(w) ≤ u(w, 1)`. -/
theorem partialLegendre_le_one {X : Type*} (u : X → ℂ → EReal) (lam : ℝ) (w : X) :
    partialLegendre u lam w ≤ u w 1 := by
  refine (iInf_le _ (⟨1, one_ne_zero⟩ : puncturedPlane)).trans ?_
  simp [logNormSq]

/-- **`Ω \ A ⊆ O`** (for `a < b`). -/
theorem diff_subset_goodSet {Ω : Opens (ComplexModel N)} {u : ComplexModel N → ℂ → EReal}
    {a b : ℝ} {A : Set (ComplexModel N)} (h : IsLegendreMAData Ω u a b A) (hab : a < b) :
    (Ω : Set (ComplexModel N)) \ A ⊆ goodSet Ω u a b := by
  intro z hz
  obtain ⟨Ca, hCa⟩ := h.locallyBounded a ⟨le_rfl, hab.le⟩ z hz
  obtain ⟨Cb, hCb⟩ := h.locallyBounded b ⟨hab.le, le_rfl⟩ z hz
  -- the upper bound from `u(·, 1)`
  have hz1 : (z, (1 : ℂ)) ∈ (Ω : Set (ComplexModel N)) ×ˢ puncturedPlane :=
    ⟨hz.1, one_ne_zero⟩
  have hpsh := h.psh _ hz1
  obtain ⟨K, hK, -⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr hpsh.ne_top)
  have hevK : ∀ᶠ w in 𝓝 z, u w 1 < (K : EReal) := by
    have h1 := hpsh.upperSemicontinuousAt K hK
    have hc : Tendsto (fun w : ComplexModel N => ((w, (1 : ℂ)) : ComplexModel N × ℂ)) (𝓝 z)
        (𝓝 (z, 1)) := (continuous_id.prodMk continuous_const).tendsto z
    exact hc.eventually h1
  have hev := (hCa.and hCb).and (hevK.and (Ω.isOpen.mem_nhds hz.1))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨r, hr, fun w hw => (hball w hw).2.2, max (max Ca Cb) |K|, fun lam hlam w hw => ?_⟩
  obtain ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, hwK, -⟩ := hball w hw
  constructor
  · -- concavity in `λ`
    have hane : partialLegendre u a w ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) ha1
    have hant : partialLegendre u a w ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) ha2
    have hbne : partialLegendre u b w ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hb1
    have hbnt : partialLegendre u b w ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hb2
    set x := (partialLegendre u a w).toReal
    set y := (partialLegendre u b w).toReal
    have hx : partialLegendre u a w = (x : EReal) := (EReal.coe_toReal hant hane).symm
    have hy : partialLegendre u b w = (y : EReal) := (EReal.coe_toReal hbnt hbne).symm
    rw [hx, EReal.coe_le_coe_iff] at ha1
    rw [hy, EReal.coe_le_coe_iff] at hb1
    set t := (b - lam) / (b - a)
    have hba : 0 < b - a := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith [hlam.2]) hba.le
    have ht1 : t ≤ 1 := (div_le_one hba).mpr (by linarith [hlam.1])
    have hlam' : t * a + (1 - t) * b = lam := by
      simp only [t]
      field_simp
      ring
    have hconc := isConcaveFamilyAt_partialLegendre u (Icc a b) w a ⟨le_rfl, hab.le⟩ b
      ⟨hab.le, le_rfl⟩ t ht0 ht1
    beta_reduce at hconc
    rw [hlam', hx, hy, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hconc
    refine le_trans ?_ hconc
    rw [EReal.coe_le_coe_iff]
    have h1 : -max (max Ca Cb) |K| ≤ x := by
      linarith [le_max_left Ca Cb, le_max_left (max Ca Cb) |K|]
    have h2 : -max (max Ca Cb) |K| ≤ y := by
      linarith [le_max_right Ca Cb, le_max_left (max Ca Cb) |K|]
    nlinarith [mul_le_mul_of_nonneg_left h1 ht0, mul_le_mul_of_nonneg_left h2
      (show 0 ≤ 1 - t by linarith)]
  · refine (partialLegendre_le_one u lam w).trans (hwK.le.trans ?_)
    exact EReal.coe_le_coe_iff.mpr ((le_abs_self K).trans (le_max_right _ _))

/-- **The identity on the good set** (`a < b`), from the locally bounded case. -/
theorem legendreIdentityOn_good {Ω : Opens (ComplexModel N)} {u : ComplexModel N → ℂ → EReal}
    {a b : ℝ} {A : Set (ComplexModel N)} (h : IsLegendreMAData Ω u a b A) (hab : a < b)
    (hu : PlurisubharmonicOn (productModelFunction u) (puncturedProductOpens Ω))
    (hû : ∀ lam : ℝ, PlurisubharmonicOn (partialLegendre u lam) Ω) :
    LegendreIdentityOn Ω u a b hu hû (goodSet Ω u a b) := by
  refine legendreIdentityOn_of_local fun z hz => ?_
  obtain ⟨r, hr, hball, C, hC⟩ := hz
  have hdata : IsBoundedLegendreData (ball z r) u a b C :=
    ⟨isOpen_ball, h.psh.mono (prod_mono hball subset_rfl), h.circleInvariant, hab,
      fun lam hlam w hw => h.eq_bot_of_notMem lam hlam w (hball hw),
      fun lam hlam w hw => (hC lam hlam w hw).1, fun lam hlam w hw => (hC lam hlam w hw).2⟩
  exact ⟨ball z (r / 8), isOpen_ball, mem_ball_self (by linarith),
    legendreIdentityOn_ball hu hû hr hball hdata⟩

/-! ### WN21 Theorem 3.3 -/

/-- **`tok-wn:legendre-ma`** (WN21 Theorem 3.3 with Theorem 3.5's exceptional set, local form):
`PartialLegendreMALocalStatement N` holds. -/
theorem partialLegendreMALocalStatement : PartialLegendreMALocalStatement N := by
  intro Ω u a b A h hu hû E hE
  rcases h.le.eq_or_lt with hab | hab
  · subst hab
    have hR : ∫⁻ lam in Icc a a, MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam)
        (hû lam) E = 0 := by
      rw [Icc_self, Measure.restrict_eq_zero.mpr Real.volume_singleton, lintegral_zero_measure]
    rw [hR, mul_zero, truncationLimitMeasure_eq_zero_of_eq h hu]
    rfl
  -- `a < b`
  set P := puncturedProductOpens Ω
  set μ := MongeAmpere.truncationLimitMeasure P (productModelFunction u) hu
  set O := goodSet Ω u a b
  have hO : IsOpen O := isOpen_goodSet Ω u a b
  have hOΩ := goodSet_subset Ω u a b
  have hΩA := diff_subset_goodSet h hab
  have hid := legendreIdentityOn_good h hab hu hû
  have hE1 : MeasurableSet (E ∩ O) := hE.inter hO.measurableSet
  have hE2 : MeasurableSet (E \ O) := hE.diff hO.measurableSet
  -- the left side does not charge `(E \ O) × ℂ*`
  have hL0 : μ (stripModelEquiv N ⁻¹' ((E \ O) ×ˢ puncturedPlane)) = 0 := by
    have hpp := MongeAmpere.truncationLimitMeasure_doesNotChargePluripolarOn hu _
      (locallyPluripolarOn_preimage h.pluripolar)
    have hsub : stripModelEquiv N ⁻¹' ((E \ O) ×ˢ puncturedPlane) ⊆
        (stripModelEquiv N ⁻¹' (A ×ˢ univ) ∩ P) ∪ (P : Set (ComplexModel (N + 1)))ᶜ := by
      intro q hq
      by_cases hqP : q ∈ (P : Set (ComplexModel (N + 1)))
      · refine Or.inl ⟨⟨?_, mem_univ _⟩, hqP⟩
        by_contra hnA
        exact hq.1.2 (hΩA ⟨hqP.1, hnA⟩)
      · exact Or.inr hqP
    exact measure_mono_null hsub (measure_union_null hpp
      (MongeAmpere.truncationLimitMeasure_compl hu))
  -- the right side does not charge `E \ O`
  have hR0 : ∀ lam, MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam) (hû lam)
      (E \ O) = 0 := by
    intro lam
    have hpp := MongeAmpere.truncationLimitMeasure_doesNotChargePluripolarOn (hû lam) A
      h.pluripolar
    have hsub : E \ O ⊆ (A ∩ Ω) ∪ (Ω : Set (ComplexModel N))ᶜ := by
      intro z hz
      by_cases hzΩ : z ∈ (Ω : Set (ComplexModel N))
      · refine Or.inl ⟨?_, hzΩ⟩
        by_contra hnA
        exact hz.2 (hΩA ⟨hzΩ, hnA⟩)
      · exact Or.inr hzΩ
    exact measure_mono_null hsub (measure_union_null hpp
      (MongeAmpere.truncationLimitMeasure_compl (hû lam)))
  have hsplitL : stripModelEquiv N ⁻¹' (E ×ˢ puncturedPlane) =
      stripModelEquiv N ⁻¹' ((E ∩ O) ×ˢ puncturedPlane) ∪
        stripModelEquiv N ⁻¹' ((E \ O) ×ˢ puncturedPlane) := by
    rw [← preimage_union, ← union_prod, inter_union_sdiff]
  have hdisjL : Disjoint (stripModelEquiv N ⁻¹' ((E ∩ O) ×ˢ puncturedPlane))
      (stripModelEquiv N ⁻¹' ((E \ O) ×ˢ puncturedPlane)) :=
    ((disjoint_sdiff_inter.symm.mono_right (le_refl _)).set_prod_left _ _).preimage _
  rw [hsplitL, measure_union hdisjL ((stripModelEquiv N).continuous.measurable
    (hE2.prod isOpen_puncturedPlane.measurableSet)), hL0, add_zero, (hid _ hE1 inter_subset_right).2]
  congr 1
  refine lintegral_congr fun lam => ?_
  rw [← measure_inter_add_sdiff E hO.measurableSet, hR0 lam, add_zero]

/-- **The Monge–Ampère identity of WN21 Theorem 3.3, unconditionally**, in applicable form. -/
theorem IsLegendreMAData.mongeAmpere_eq' {Ω : Opens (ComplexModel N)}
    {u : ComplexModel N → ℂ → EReal} {a b : ℝ} {A : Set (ComplexModel N)}
    (h : IsLegendreMAData Ω u a b A) {E : Set (ComplexModel N)} (hE : MeasurableSet E) :
    MongeAmpere.truncationLimitMeasure (puncturedProductOpens Ω) (productModelFunction u)
        h.plurisubharmonicOn_productModelFunction (stripModelEquiv N ⁻¹' (E ×ˢ puncturedPlane)) =
      ((N + 1 : ℕ) : ENNReal) * ∫⁻ lam in Icc a b,
        MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam)
          (h.plurisubharmonicOn_partialLegendre lam) E :=
  h.mongeAmpere_eq partialLegendreMALocalStatement hE

end SGPT.Okounkov.TranscendentalWN
