import SGPT.Okounkov.TranscendentalVolumeConcavityMinkowski
import SGPT.Foundations.Analysis.Pending.MovingBottChernClassCurrentCompactness

/-!
# Continuity of the volume on `H^{1,1}(X, ℝ)`

Source: blueprint node `tok:ext-volume-concave` (Boucksom, *On the volume of a line bundle*,
published Proposition 4.5: continuity on the big cone and upper semicontinuity on the
pseudo-effective cone; DRWNXZ uses "`vol` is continuous on `H^{1,1}(X, ℝ)`, `vol = 0` outside the
big cone").

The topology is TN's quotient `C⁰` topology `classC0Topology w`. If `θ` represents `α` and
`‖η - θ‖_{C⁰, w} < ε`, then `-εw ≤ η - θ ≤ εw`, so by monotonicity under semipositive additions
`vol(α - ε{w}) ≤ vol({η}) ≤ vol(α + ε{w})` (`sourceClassVolume_sandwich`). Hence:

* **upper semicontinuity**: for pseudo-effective `α`, `vol(α + ε{w}) → vol(α)` (Boucksom's
  Theorem 4.6, TN); for non-pseudo-effective `α`, the pseudo-effective cone is closed
  (`classPseudoeffective_of_forall_add_smul`, weak compactness of currents with bounded mass), so
  `α + ε{w}` is not pseudo-effective for some `ε > 0` and `vol = 0` near `α`;
* **lower semicontinuity**: trivial where `vol α = 0`; if `vol α > 0`, `α` is big, so
  `α - δ{w}` is pseudo-effective for some `δ > 0`, and for `t ∈ (0, 1)`,
  `α - tδ{w} = (1 - t)α + t(α - δ{w})`, whence `vol(α - tδ{w}) ≥ vol((1 - t)α) = (1 - t)^n vol α`
  (Minkowski and homogeneity).

`volumeContinuity` is `VolumeContinuityStatement`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalVolumeConcavity

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
open SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
open SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
open SGPT.Foundations.Analysis.Pending.XiaoFormC0Topology
open SGPT.Foundations.Analysis.Pending.XiaoPureSmoothTopology
open SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

/-! ### Closedness of the pseudo-effective cone -/

/-- **The pseudo-effective cone is closed** in the direction of a Kähler class: if
`α + ε{ω}` is pseudo-effective for every `ε > 0`, so is `α` (a weak limit of currents in
`α + ε_j{ω}`, TN `MovingBottChernClassCurrentCompactness`). -/
theorem classPseudoeffective_of_forall_add_smul (ω : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X)
    (h : ∀ ε : ℝ, 0 < ε →
      ClassPseudoeffectiveViaPotentials (α + ε • RealBottChern.ofRepresentative ω.form)) :
    ClassPseudoeffectiveViaPotentials α := by
  classical
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcur (j : ℕ) := (PseudoeffectiveOriginalCurrentEquivalence.classPseudoeffectiveViaPotentials_iff_exists_original_current
    _).mp (h (ε j) (hεpos j))
  choose T hT hTc using hcur
  have hclasses : Tendsto (fun j => α + ε j • RealBottChern.ofRepresentative ω.form)
      atTop (@nhds (RealBottChern (m + 1) X)
        XiaoPureSmoothBottChernClosure.classPureSmoothTopology α) := by
    refine Quotient.inductionOn α ?_
    intro θ
    change Tendsto (fun j => RealBottChern.ofRepresentative θ +
      ε j • RealBottChern.ofRepresentative ω.form) atTop
      (@nhds (RealBottChern (m + 1) X) XiaoPureSmoothBottChernClosure.classPureSmoothTopology
        (RealBottChern.ofRepresentative θ))
    let : TopologicalSpace (ClosedRealOneOneForm (m + 1) X) := formPureSmoothTopology
    let : TopologicalSpace (RealBottChern (m + 1) X) :=
      XiaoPureSmoothBottChernClosure.classPureSmoothTopology
    let : IsTopologicalAddGroup (ClosedRealOneOneForm (m + 1) X) :=
      formPureSmoothTopology_isTopologicalAddGroup
    let : ContinuousSMul ℝ (ClosedRealOneOneForm (m + 1) X) :=
      formPureSmoothTopology_continuousSMul
    have hform : Tendsto (fun j => θ + ε j • ω.form) atTop (𝓝 θ) := by
      simpa only [zero_smul, add_zero] using
        tendsto_const_nhds.add (hεlim.smul_const ω.form)
    have h' := (XiaoPureSmoothBottChernClosure.isOpenQuotientMap_ofRepresentative
      ω).continuous.tendsto θ |>.comp hform
    have hf : (fun j => RealBottChern.ofRepresentative θ +
        ε j • RealBottChern.ofRepresentative ω.form) =
        RealBottChern.ofRepresentative ∘ (fun j => θ + ε j • ω.form) := by
      funext j
      simp only [Function.comp_apply, RealBottChern.ofRepresentative_add,
        RealBottChern.ofRepresentative_smul]
    rw [hf]
    exact h'
  have hclassT : Tendsto (fun j => bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (T j)) atTop (@nhds (RealBottChern (m + 1) X)
        XiaoPureSmoothBottChernClosure.classPureSmoothTopology α) := by
    simpa only [hTc] using hclasses
  obtain ⟨S, hS, hSclass, -⟩ :=
    MovingBottChernClassCurrentCompactness.exists_tendsto_moving_class_originalClosedPositiveCurrent
      ω (Ultrafilter.of (atTop : Filter ℕ)) (Ultrafilter.of_le _) α T hT hclassT
  exact (PseudoeffectiveOriginalCurrentEquivalence.classPseudoeffectiveViaPotentials_iff_exists_original_current
    α).mpr ⟨S, hS, hSclass⟩

/-- A big class stays pseudo-effective after subtracting a small multiple of a Kähler class. -/
theorem exists_pos_classPseudoeffective_sub_smul (ω : KahlerBackground (m + 1) X)
    {α : RealBottChern (m + 1) X} (hα : IsBigClass α) :
    ∃ δ : ℝ, 0 < δ ∧
      ClassPseudoeffectiveViaPotentials (α - δ • RealBottChern.ofRepresentative ω.form) := by
  obtain ⟨K⟩ := hα
  obtain ⟨A, hA, hAsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul K.lowerBound (-ω.form)
  refine ⟨A⁻¹, inv_pos.mpr hA, ?_⟩
  have hsemi : (K.lowerBound.form - A⁻¹ • ω.form).val.IsSemipositive := by
    have h := KahlerDomination.isSemipositive_smul hAsemi (inv_pos.mpr hA).le
    have he : A⁻¹ • (-ω.form + A • K.lowerBound.form) = K.lowerBound.form - A⁻¹ • ω.form := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
      abel
    rwa [he] at h
  have hpsh := LocalPotentials.isThetaPshPotential_add_of_semipositive K.strictlyPsh hsemi
  have he : K.representative - K.lowerBound.form + (K.lowerBound.form - A⁻¹ • ω.form) =
      K.representative - A⁻¹ • ω.form := by abel
  rw [he] at hpsh
  have hcl : RealBottChern.ofRepresentative (K.representative - A⁻¹ • ω.form) =
      α - A⁻¹ • RealBottChern.ofRepresentative ω.form := by
    rw [sub_eq_add_neg, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg,
      RealBottChern.ofRepresentative_smul, K.represents, sub_eq_add_neg]
  rw [← hcl, classPseudoeffectiveViaPotentials_ofRepresentative]
  exact ⟨K.potential, hpsh⟩

variable [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### Monotonicity and the sandwich -/

/-- The volume increases along the pseudo-effective order: `vol x ≤ vol (x + y)` for
pseudo-effective `x`, `y`. -/
theorem sourceClassVolume_le_add_of_pseudoeffective (ω : KahlerBackground (m + 1) X)
    {x y : RealBottChern (m + 1) X} (hx : ClassPseudoeffectiveViaPotentials x)
    (hy : ClassPseudoeffectiveViaPotentials y) :
    sourceClassVolume x ≤ sourceClassVolume (x + y) := by
  have h := volumeRoot_add_le ω hx hy
  have hy0 : 0 ≤ volumeRoot y := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hle : volumeRoot x ≤ volumeRoot (x + y) := le_of_add_le_of_nonneg_left h hy0
  unfold volumeRoot at hle
  have hr : 0 < (((m + 1 : ℕ) : ℝ))⁻¹ := by positivity
  rw [Real.rpow_le_rpow_iff ENNReal.toReal_nonneg ENNReal.toReal_nonneg hr] at hle
  exact (ENNReal.toReal_le_toReal (sourceClassVolume_lt_top ω x).ne
    (sourceClassVolume_lt_top ω (x + y)).ne).mp hle

/-- **The sandwich**: if `‖η - θ‖_{C⁰, w} < ε`, then
`vol({θ} - ε{w}) ≤ vol({η}) ≤ vol({θ} + ε{w})`. -/
theorem sourceClassVolume_sandwich (w : KahlerBackground (m + 1) X)
    {θ η : ClosedRealOneOneForm (m + 1) X} {ε : ℝ} (hε : formC0Seminorm w (η - θ) < ε) :
    sourceClassVolume (RealBottChern.ofRepresentative θ -
        ε • RealBottChern.ofRepresentative w.form) ≤
        sourceClassVolume (RealBottChern.ofRepresentative η) ∧
      sourceClassVolume (RealBottChern.ofRepresentative η) ≤
        sourceClassVolume (RealBottChern.ofRepresentative θ +
          ε • RealBottChern.ofRepresentative w.form) := by
  have hup := isSemipositive_sub_add_smul_of_formC0_lt w θ η hε
  have hε' : formC0Seminorm w (θ - η) < ε := by
    rwa [← neg_sub, map_neg_eq_map]
  have hlow := isSemipositive_sub_add_smul_of_formC0_lt w η θ hε'
  constructor
  · have h := sourceClassVolume_le_add_semipositive w
      (RealBottChern.ofRepresentative θ - ε • RealBottChern.ofRepresentative w.form)
      (η - θ + ε • w.form) hlow
    have he : RealBottChern.ofRepresentative θ - ε • RealBottChern.ofRepresentative w.form +
        RealBottChern.ofRepresentative (η - θ + ε • w.form) =
        RealBottChern.ofRepresentative η := by
      rw [RealBottChern.ofRepresentative_add, sub_eq_add_neg η θ,
        RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg,
        RealBottChern.ofRepresentative_smul]
      abel
    rwa [he] at h
  · have h := sourceClassVolume_le_add_semipositive w (RealBottChern.ofRepresentative η)
      (θ - η + ε • w.form) hup
    have he : RealBottChern.ofRepresentative η +
        RealBottChern.ofRepresentative (θ - η + ε • w.form) =
        RealBottChern.ofRepresentative θ + ε • RealBottChern.ofRepresentative w.form := by
      rw [RealBottChern.ofRepresentative_add, sub_eq_add_neg θ η,
        RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg,
        RealBottChern.ofRepresentative_smul]
      abel
    rwa [he] at h

/-! ### Semicontinuity -/

/-- **Upper semicontinuity input**: above `vol α` there is `vol(α + ε{w})` for some `ε > 0`. -/
theorem exists_sourceClassVolume_add_smul_lt (w : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) {a : ℝ≥0∞} (ha : sourceClassVolume α < a) :
    ∃ ε : ℝ, 0 < ε ∧
      sourceClassVolume (α + ε • RealBottChern.ofRepresentative w.form) < a := by
  by_cases hα : ClassPseudoeffectiveViaPotentials α
  · have hlim := tendsto_sourceClassVolume_add_smul_right w α hα
    obtain ⟨ε, hεa, hε⟩ := ((hlim.eventually (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    exact ⟨ε, hε, hεa⟩
  · by_contra hne
    push Not at hne
    apply hα
    apply classPseudoeffective_of_forall_add_smul w α
    intro ε hε
    by_contra hnp
    have h0 := sourceClassVolume_eq_zero_of_not_pseudoeffective hnp
    have h1 := hne ε hε
    rw [h0] at h1
    exact (lt_of_le_of_lt zero_le ha).not_ge h1

/-- **Lower semicontinuity input**: below `vol α` there is `vol(α - ε{w})` for some `ε > 0`. -/
theorem exists_lt_sourceClassVolume_sub_smul (w : KahlerBackground (m + 1) X)
    (α : RealBottChern (m + 1) X) {a : ℝ≥0∞} (ha : a < sourceClassVolume α) :
    ∃ ε : ℝ, 0 < ε ∧
      a < sourceClassVolume (α - ε • RealBottChern.ofRepresentative w.form) := by
  have hpos : 0 < sourceClassVolume α := lt_of_le_of_lt zero_le ha
  have hbig := (sourceClassVolume_pos_iff_isBigClass w α).mp hpos
  have hαp := classPseudoeffective_of_isBigClass w hbig
  obtain ⟨δ, hδ, hδp⟩ := exists_pos_classPseudoeffective_sub_smul w hbig
  -- `t ↦ (1 - t)^n vol α` is continuous at `0`
  have hcont : Tendsto (fun t : ℝ => ENNReal.ofReal ((1 - t) ^ (m + 1)) * sourceClassVolume α)
      (𝓝 0) (𝓝 (ENNReal.ofReal ((1 - 0) ^ (m + 1)) * sourceClassVolume α)) := by
    apply ENNReal.Tendsto.mul_const _ (Or.inr (sourceClassVolume_lt_top w α).ne)
    exact (ENNReal.continuous_ofReal.comp
      ((continuous_const.sub continuous_id).pow (m + 1))).tendsto 0
  rw [sub_zero, one_pow, ENNReal.ofReal_one, one_mul] at hcont
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (a < ENNReal.ofReal ((1 - t) ^ (m + 1)) * sourceClassVolume α ∧ t < 1) ∧ t ∈ Ioi 0 :=
    (((hcont.eventually (lt_mem_nhds ha)).and
      (eventually_lt_nhds (zero_lt_one' ℝ))).filter_mono nhdsWithin_le_nhds).and
        self_mem_nhdsWithin
  obtain ⟨t, ⟨hta, ht1⟩, ht0⟩ := hev.exists
  have ht0' : (0 : ℝ) < t := ht0
  refine ⟨t * δ, mul_pos ht0' hδ, hta.trans_le ?_⟩
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  have hdecomp : α - (t * δ) • RealBottChern.ofRepresentative w.form =
      (1 - t) • α + t • (α - δ • RealBottChern.ofRepresentative w.form) := by
    rw [smul_sub, smul_smul, sub_smul, one_smul]
    abel
  rw [hdecomp, ← sourceClassVolume_smul w α h1t]
  exact sourceClassVolume_le_add_of_pseudoeffective w (classPseudoeffective_smul hαp h1t.le)
    (classPseudoeffective_smul hδp ht0'.le)

/-! ### Continuity -/

/-- The volume is continuous at the class of `θ`, along the `C⁰` topology of forms. -/
theorem tendsto_sourceClassVolume_ofRepresentative (w : KahlerBackground (m + 1) X)
    (θ : ClosedRealOneOneForm (m + 1) X) :
    Tendsto (fun η => sourceClassVolume (RealBottChern.ofRepresentative η))
      (@nhds _ (formC0Topology w) θ)
      (𝓝 (sourceClassVolume (RealBottChern.ofRepresentative θ))) := by
  let : TopologicalSpace (ClosedRealOneOneForm (m + 1) X) := formC0Topology w
  have hball (ε : ℝ) (hε : 0 < ε) : ∀ᶠ η in 𝓝 θ, formC0Seminorm w (η - θ) < ε := by
    filter_upwards [(isOpen_formC0Seminorm_ball w θ ε).mem_nhds
      ((formC0Seminorm w).mem_ball_self hε)] with η hη
    exact (formC0Seminorm w).mem_ball.mp hη
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨ε, hε, hlt⟩ := exists_lt_sourceClassVolume_sub_smul w _ ha
    filter_upwards [hball ε hε] with η hη
    exact hlt.trans_le (sourceClassVolume_sandwich w hη).1
  · obtain ⟨ε, hε, hlt⟩ := exists_sourceClassVolume_add_smul_lt w _ ha
    filter_upwards [hball ε hε] with η hη
    exact (sourceClassVolume_sandwich w hη).2.trans_lt hlt

/-- **`tok:ext-volume-concave`, continuity**: `α ↦ vol(α)` is continuous on `H^{1,1}(X, ℝ)` for
the `C⁰` quotient topology. -/
theorem volumeContinuity : VolumeContinuityStatement (m := m) X := by
  intro w
  let : TopologicalSpace (ClosedRealOneOneForm (m + 1) X) := formC0Topology w
  let : TopologicalSpace (RealBottChern (m + 1) X) := XiaoBottChernC0Closure.classC0Topology w
  rw [continuous_iff_continuousAt]
  intro α
  obtain ⟨θ, rfl⟩ : ∃ θ, RealBottChern.ofRepresentative θ = α :=
    ⟨Quotient.out α, Quotient.out_eq α⟩
  unfold ContinuousAt
  rw [← (XiaoBottChernC0Closure.isOpenQuotientMap_ofRepresentative w).map_nhds_eq θ,
    tendsto_map'_iff]
  exact tendsto_sourceClassVolume_ofRepresentative w θ

/-- The big cone is open in `H^{1,1}(X, ℝ)` (for the `C⁰` quotient topology): it is
`{vol > 0}`. -/
theorem isOpen_bigCone (ω : KahlerBackground (m + 1) X) (w : KahlerBackground (m + 1) X) :
    @IsOpen (RealBottChern (m + 1) X) (XiaoBottChernC0Closure.classC0Topology w)
      (bigCone (m := m) X) := by
  let : TopologicalSpace (RealBottChern (m + 1) X) := XiaoBottChernC0Closure.classC0Topology w
  have h : bigCone (m := m) X = sourceClassVolume ⁻¹' Ioi 0 := by
    ext α
    exact (volumePositiveIffBig ω α).symm
  rw [h]
  exact isOpen_Ioi.preimage (volumeContinuity w)

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Affine lines `t ↦ α + tβ` are continuous into `H^{1,1}(X, ℝ)` (`C⁰` quotient topology). -/
theorem continuous_add_smul_class (w : KahlerBackground (m + 1) X) (α β : RealBottChern (m + 1) X) :
    @Continuous ℝ (RealBottChern (m + 1) X) _ (XiaoBottChernC0Closure.classC0Topology w)
      (fun t : ℝ => α + t • β) := by
  let : TopologicalSpace (ClosedRealOneOneForm (m + 1) X) := formC0Topology w
  let : TopologicalSpace (RealBottChern (m + 1) X) := XiaoBottChernC0Closure.classC0Topology w
  let : IsTopologicalAddGroup (ClosedRealOneOneForm (m + 1) X) :=
    formC0Topology_isTopologicalAddGroup w
  let : ContinuousSMul ℝ (ClosedRealOneOneForm (m + 1) X) := formC0Topology_continuousSMul w
  obtain ⟨θ, rfl⟩ : ∃ θ, RealBottChern.ofRepresentative θ = α :=
    ⟨Quotient.out α, Quotient.out_eq α⟩
  obtain ⟨η, rfl⟩ : ∃ η, RealBottChern.ofRepresentative η = β :=
    ⟨Quotient.out β, Quotient.out_eq β⟩
  have hf : (fun t : ℝ => RealBottChern.ofRepresentative θ + t • RealBottChern.ofRepresentative η) =
      RealBottChern.ofRepresentative ∘ (fun t : ℝ => θ + t • η) := by
    funext t
    simp only [Function.comp_apply, RealBottChern.ofRepresentative_add,
      RealBottChern.ofRepresentative_smul]
  rw [hf]
  exact (XiaoBottChernC0Closure.isOpenQuotientMap_ofRepresentative w).continuous.comp
    (continuous_const.add (continuous_id.smul continuous_const))

/-- **Continuity of the volume along affine lines**: `t ↦ vol(α + tβ)` is continuous on `ℝ`
(DRWNXZ uses it for `t ↦ vol(ξ - t{Z})`). -/
theorem continuous_sourceClassVolume_add_smul (w : KahlerBackground (m + 1) X)
    (α β : RealBottChern (m + 1) X) :
    Continuous (fun t : ℝ => sourceClassVolume (α + t • β)) := by
  let : TopologicalSpace (RealBottChern (m + 1) X) := XiaoBottChernC0Closure.classC0Topology w
  exact (volumeContinuity w).comp (continuous_add_smul_class w α β)

/-- **Concavity of `vol^{1/n}` along affine lines**: `t ↦ vol(α + tβ)^{1/n}` is concave on
every interval of parameters whose classes are big. -/
theorem concaveOn_volumeRoot_add_smul (ω : KahlerBackground (m + 1) X)
    (α β : RealBottChern (m + 1) X) {I : Set ℝ} (hI : Convex ℝ I)
    (hbig : ∀ t ∈ I, SGPT.PSH.BookCurrent.IsBig (α + t • β)) :
    ConcaveOn ℝ I (fun t : ℝ => volumeRoot (α + t • β)) := by
  refine ⟨hI, fun s hs t ht a b ha hb hab => ?_⟩
  have h := (volumeRootConcave ω).2 (hbig s hs) (hbig t ht) ha hb hab
  have he : a • (α + s • β) + b • (α + t • β) = α + (a • s + b • t) • β := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_smul, smul_eq_mul, smul_eq_mul]
    calc a • α + (a * s) • β + (b • α + (b * t) • β)
        = (a + b) • α + ((a * s) • β + (b * t) • β) := by rw [add_smul]; abel
      _ = α + ((a * s) • β + (b * t) • β) := by rw [hab, one_smul]
  simpa only [he] using h

/-- **`tok:ext-volume-concave`** (Bou02b): on a connected compact Kähler manifold,
`vol^{1/n}` is concave on the big cone, `vol` is continuous on `H^{1,1}(X, ℝ)`, and
`vol α > 0 ⟺ α` big. -/
theorem volumeConcavity (ω : KahlerBackground (m + 1) X) :
    VolumeConcavityStatement (m := m) X :=
  ⟨volumeRootConcave ω, volumeContinuity, volumePositiveIffBig ω⟩

end SGPT.Okounkov.TranscendentalVolumeConcavity
