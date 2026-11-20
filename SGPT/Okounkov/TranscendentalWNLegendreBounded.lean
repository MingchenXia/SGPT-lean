import SGPT.Okounkov.TranscendentalWNLegendreBoundedBall

/-!
# The locally bounded case of WN21 Theorem 3.3 (package WN-LEG)

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:bounded-case`.

* `LegendreIdentityOn Ω u a b hu hû V`: for every Borel `E ⊆ V`, `λ ↦ MA(û_λ)(E)` is
  a.e.-measurable on `[a, b]` and `MA(u)(E × ℂ*) = (N + 1) ∫_a^b MA(û_λ)(E) dλ` (measures on
  `Ω × ℂ*` and `Ω`).
* `legendreIdentityOn_of_local`: the identity is local — if every point of an open `O` has an
  open neighbourhood where it holds, it holds on `O` (Lindelöf, disjointification, countable
  additivity on both sides).
* `legendreIdentityOn_ball`: it holds on `ball z (r/8)` whenever `ball z r ⊆ Ω` carries bounded
  data (`IsBoundedLegendreData.ball_identity` and locality of the non-pluripolar measures).
* **`boundedLegendreMAStatement`**: `BoundedLegendreMAStatement N` holds.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
  SGPT.Foundations.Analysis.Pending.PshRadialRegularization

variable {N : ℕ}

/-- **The partial Legendre Monge–Ampère identity on Borel subsets of `V`**, with the measures on
`Ω × ℂ*` and `Ω`. -/
def LegendreIdentityOn (Ω : Opens (ComplexModel N)) (u : ComplexModel N → ℂ → EReal) (a b : ℝ)
    (hu : PlurisubharmonicOn (productModelFunction u) (puncturedProductOpens Ω))
    (hû : ∀ lam : ℝ, PlurisubharmonicOn (partialLegendre u lam) Ω)
    (V : Set (ComplexModel N)) : Prop :=
  ∀ E : Set (ComplexModel N), MeasurableSet E → E ⊆ V →
    AEMeasurable (fun lam => MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam) (hû lam) E)
        (volume.restrict (Icc a b)) ∧
      MongeAmpere.truncationLimitMeasure (puncturedProductOpens Ω) (productModelFunction u) hu
          (stripModelEquiv N ⁻¹' (E ×ˢ puncturedPlane)) =
        ((N + 1 : ℕ) : ℝ≥0∞) *
          ∫⁻ lam in Icc a b, MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam) (hû lam) E

section Gluing

variable {Ω : Opens (ComplexModel N)} {u : ComplexModel N → ℂ → EReal} {a b : ℝ}
  {hu : PlurisubharmonicOn (productModelFunction u) (puncturedProductOpens Ω)}
  {hû : ∀ lam : ℝ, PlurisubharmonicOn (partialLegendre u lam) Ω}

theorem LegendreIdentityOn.mono {V V' : Set (ComplexModel N)}
    (h : LegendreIdentityOn Ω u a b hu hû V) (hV' : V' ⊆ V) : LegendreIdentityOn Ω u a b hu hû V' :=
  fun E hE hEV => h E hE (hEV.trans hV')

/-- **Gluing**: the identity is local in `z`. -/
theorem legendreIdentityOn_of_local {O : Set (ComplexModel N)}
    (hloc : ∀ z ∈ O, ∃ V : Set (ComplexModel N), IsOpen V ∧ z ∈ V ∧
      LegendreIdentityOn Ω u a b hu hû V) :
    LegendreIdentityOn Ω u a b hu hû O := by
  intro E hE hEO
  rcases E.eq_empty_or_nonempty with hE0 | hEne
  · subst hE0
    simp
  choose V hVo hzV hV using hloc
  set W : O → Set (ComplexModel N) := fun z => V z.1 z.2
  obtain ⟨T, hTc, hTU⟩ := isOpen_iUnion_countable W fun z => hVo z.1 z.2
  have hcov : E ⊆ ⋃ z ∈ T, W z := by
    rw [hTU]
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hEO hx⟩, hzV x (hEO hx)⟩
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hEne
    obtain ⟨z, hzT, -⟩ := mem_iUnion₂.mp (hcov hx)
    exact ⟨z, hzT⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  have hcov' : E ⊆ ⋃ n, W (f n) := by
    intro x hx
    obtain ⟨z, hzT, hxz⟩ := mem_iUnion₂.mp (hcov hx)
    rw [hf] at hzT
    obtain ⟨n, rfl⟩ := hzT
    exact mem_iUnion.mpr ⟨n, hxz⟩
  set G : ℕ → Set (ComplexModel N) := fun n => E ∩ W (f n)
  set Eₙ : ℕ → Set (ComplexModel N) := disjointed G
  have hGm : ∀ n, MeasurableSet (G n) := fun n => hE.inter (hVo _ _).measurableSet
  have hEm : ∀ n, MeasurableSet (Eₙ n) := MeasurableSet.disjointed hGm
  have hEsub : ∀ n, Eₙ n ⊆ W (f n) := fun n => (disjointed_subset G n).trans inter_subset_right
  have hdisj : Pairwise (Function.onFun Disjoint Eₙ) := disjoint_disjointed G
  have hU : ⋃ n, Eₙ n = E := by
    rw [iUnion_disjointed]
    exact subset_antisymm (iUnion_subset fun n => inter_subset_left) fun x hx => by
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hcov' hx)
      exact mem_iUnion.mpr ⟨n, hx, hn⟩
  have hloc' : ∀ n, AEMeasurable (fun lam => MongeAmpere.truncationLimitMeasure Ω
        (partialLegendre u lam) (hû lam) (Eₙ n)) (volume.restrict (Icc a b)) ∧
      MongeAmpere.truncationLimitMeasure (puncturedProductOpens Ω) (productModelFunction u) hu
          (stripModelEquiv N ⁻¹' (Eₙ n ×ˢ puncturedPlane)) =
        ((N + 1 : ℕ) : ℝ≥0∞) * ∫⁻ lam in Icc a b,
          MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam) (hû lam) (Eₙ n) :=
    fun n => hV (f n).1 (f n).2 (Eₙ n) (hEm n) (hEsub n)
  have hsumR : ∀ lam, MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam) (hû lam) E =
      ∑' n, MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam) (hû lam) (Eₙ n) := by
    intro lam
    conv_lhs => rw [← hU]
    exact measure_iUnion hdisj hEm
  have hdisjL : Pairwise (Function.onFun Disjoint fun n => stripModelEquiv N ⁻¹' (Eₙ n ×ˢ puncturedPlane)) :=
    fun i j hij => ((hdisj hij).set_prod_left _ _).preimage _
  have hEmL : ∀ n, MeasurableSet (stripModelEquiv N ⁻¹' (Eₙ n ×ˢ puncturedPlane)) := fun n =>
    (stripModelEquiv N).continuous.measurable ((hEm n).prod isOpen_puncturedPlane.measurableSet)
  have hUL : stripModelEquiv N ⁻¹' (E ×ˢ puncturedPlane) =
      ⋃ n, stripModelEquiv N ⁻¹' (Eₙ n ×ˢ puncturedPlane) := by
    rw [← preimage_iUnion, ← iUnion_prod_const, hU]
  refine ⟨?_, ?_⟩
  · simp_rw [hsumR]
    exact AEMeasurable.tsum fun n => (hloc' n).1
  · rw [hUL, measure_iUnion hdisjL hEmL]
    simp_rw [(hloc' _).2, hsumR]
    rw [ENNReal.tsum_mul_left, lintegral_tsum fun n => (hloc' n).1]

end Gluing

/-! ### Bounded data restrict to smaller open sets -/

theorem IsBoundedLegendreData.mono {B B' : Set (ComplexModel N)} {u : ComplexModel N → ℂ → EReal}
    {a b C : ℝ} (h : IsBoundedLegendreData B u a b C) (hB' : IsOpen B') (hB'B : B' ⊆ B) :
    IsBoundedLegendreData B' u a b C :=
  ⟨hB', h.psh.mono (prod_mono hB'B subset_rfl), h.circleInvariant, h.lt,
    fun lam hlam z hz => h.eq_bot lam hlam z (hB'B hz),
    fun lam hlam z hz => h.lower lam hlam z (hB'B hz),
    fun lam hlam z hz => h.upper lam hlam z (hB'B hz)⟩

theorem puncturedProductOpens_mono {V Ω : Opens (ComplexModel N)} (hVΩ : V ≤ Ω) :
    puncturedProductOpens V ≤ puncturedProductOpens Ω := fun _ hq => ⟨hVΩ hq.1, hq.2⟩

/-- **The identity on `ball z (r/8)`** when `ball z r ⊆ Ω` carries bounded data. -/
theorem legendreIdentityOn_ball {Ω : Opens (ComplexModel N)} {u : ComplexModel N → ℂ → EReal}
    {a b C : ℝ} (hu : PlurisubharmonicOn (productModelFunction u) (puncturedProductOpens Ω))
    (hû : ∀ lam : ℝ, PlurisubharmonicOn (partialLegendre u lam) Ω) {z : ComplexModel N} {r : ℝ}
    (hr : 0 < r) (hball : ball z r ⊆ Ω) (h : IsBoundedLegendreData (ball z r) u a b C) :
    LegendreIdentityOn Ω u a b hu hû (ball z (r / 8)) := by
  intro E hE hEW
  obtain ⟨ρ, hρ⟩ := exists_isRadialKernel (n := N + 1)
  set D := approxDomain (ball z r) (localScale r)
  have hDΩ : D ≤ Ω := (approxDomain_subset (localScale_pos hr).le).trans hball
  have huD : PlurisubharmonicOn (productModelFunction u) (puncturedProductOpens D) :=
    hu.mono (puncturedProductOpens_mono hDΩ)
  have hûD : ∀ lam, PlurisubharmonicOn (partialLegendre u lam) D := fun lam => (hû lam).mono hDΩ
  obtain ⟨hmeas, hid⟩ := h.ball_identity hρ hr huD hûD hE hEW
  have hED : E ⊆ D := hEW.trans (ball_eighth_subset_approxDomain hr)
  have hR : ∀ lam, MongeAmpere.truncationLimitMeasure Ω (partialLegendre u lam) (hû lam) E =
      MongeAmpere.truncationLimitMeasure D (partialLegendre u lam) (hûD lam) E := fun lam =>
    truncationLimitMeasure_apply_of_subset hDΩ (hû lam) (hûD lam) hED
  have hL : MongeAmpere.truncationLimitMeasure (puncturedProductOpens Ω) (productModelFunction u) hu
        (stripModelEquiv N ⁻¹' (E ×ˢ puncturedPlane)) =
      MongeAmpere.truncationLimitMeasure (puncturedProductOpens D) (productModelFunction u) huD
        (stripModelEquiv N ⁻¹' (E ×ˢ puncturedPlane)) :=
    truncationLimitMeasure_apply_of_subset (puncturedProductOpens_mono hDΩ) hu huD
      fun q hq => ⟨hED hq.1, hq.2⟩
  have hrestr : volume.restrict (Icc a b) = volume.restrict (Ioo a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  simp_rw [hR]
  refine ⟨?_, ?_⟩
  · rw [hrestr]
    exact hmeas.aemeasurable.congr ((ae_restrict_mem measurableSet_Ioo).mono fun lam hlam =>
      indicator_of_mem hlam _)
  · rw [hL, hid, hrestr]

/-- **`tok-wn-leg:bounded-case`**: WN21 Theorem 3.3 for locally bounded transforms. -/
theorem boundedLegendreMAStatement : BoundedLegendreMAStatement N := by
  intro B u a b C h hu hû E hE hEB
  have hglob : LegendreIdentityOn B u a b hu hû B := by
    refine legendreIdentityOn_of_local fun z hz => ?_
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp B.isOpen z hz
    exact ⟨ball z (r / 8), isOpen_ball, mem_ball_self (by linarith),
      legendreIdentityOn_ball hu hû hr hball (h.mono isOpen_ball hball)⟩
  exact (hglob E hE hEB).2

end SGPT.Okounkov.TranscendentalWN
