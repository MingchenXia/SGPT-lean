import SGPT.NPP.NonPluripolarCurrent4Bounded
import SGPT.NPP.NonPluripolarClosedLocal
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus

/-! Body-preserving consolidation PLAN ONLY. Fresh proper-name checking is
required; private flat objects are provenance, never providers for this file. -/

-- Exact frozen body: WeightedOpenRestrictionDraft
section OriginalFragment_01

/-! Actual weighted-current locality for the relative non-pluripolar route. -/
set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Distributions

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality

variable {n q : ℕ} {U V : TopologicalSpace.Opens (ComplexModel n)}

/-- A genuine Borel-weighted current depends only on its actual open
restriction wherever the original weight is supported. No density equality
or current-output certificate is an input. -/
theorem mulBorel_eq_of_restrict_eq_of_zero_off
    {R S : LocalProductCurrent n U q} (hR : IsPositive R) (hS : IsPositive S)
    (hVU : V ≤ U) (hRS : restrict hVU R = restrict hVU S)
    {w : ComplexModel n → ℝ} (hwm : Measurable w) (hwb : IsLocallyBoundedOn w U)
    (hw0 : ∀ x ∉ (V : Set (ComplexModel n)), w x = 0) :
    mulBorel R w = mulBorel S w := by
  have readback (T : LocalProductCurrent n U q) (hT : IsPositive T)
      (γ : formSpan n q) (φ : 𝓓(U, ℝ)) :
      mulBorel T w γ φ =
        ∫ x, φ x * (w x * (isPositive_restrict hT hVU).density γ x)
          ∂(isPositive_restrict hT hVU).traceMeasure := by
    rw [mulBorel_apply hT hwm hwb]
    calc
      (∫ x, φ x * (w x * hT.density γ x) ∂hT.traceMeasure) =
          ∫ x, φ x * (w x * hT.density γ x) ∂hT.traceMeasure.restrict V := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [hw0 x hx, zero_mul, mul_zero]
      _ = _ := by
        rw [← traceMeasure_restrict hT hVU]
        apply integral_congr_ae
        filter_upwards [density_restrict_ae hT hVU γ] with x hx
        rw [hx]
  ext γ φ
  rw [readback R hR γ φ, readback S hS γ φ]
  have congr_current (A B : LocalProductCurrent n V q)
      (hA : IsPositive A) (hB : IsPositive B) (hAB : A = B) :
      (∫ x, φ x * (w x * hA.density γ x) ∂hA.traceMeasure) =
        ∫ x, φ x * (w x * hB.density γ x) ∂hB.traceMeasure := by
    subst hAB
    rfl
  exact congr_current _ _ (isPositive_restrict hR hVU) (isPositive_restrict hS hVU) hRS

/-- Actual open restrictions have the same globally extended indicator
current, including all boundary points of the original open set. -/
theorem mulBorel_indicator_eq_of_restrict_eq
    {R S : LocalProductCurrent n U q} (hR : IsPositive R) (hS : IsPositive S)
    (hVU : V ≤ U) (hRS : restrict hVU R = restrict hVU S) :
    mulBorel R ((V : Set (ComplexModel n)).indicator fun _ => (1 : ℝ)) =
      mulBorel S ((V : Set (ComplexModel n)).indicator fun _ => (1 : ℝ)) := by
  apply mulBorel_eq_of_restrict_eq_of_zero_off hR hS hVU hRS
    (measurable_const.indicator V.isOpen.measurableSet)
  · intro K hK hKU
    refine ⟨1, fun x hx => ?_⟩
    by_cases hxV : x ∈ (V : Set (ComplexModel n)) <;> simp [hxV]
  · intro x hx
    simp [hx]

end SGPT.NPP.RelativeNonPluripolar

set_option pp.universes true
set_option pp.proofs false
#check @SGPT.NPP.RelativeNonPluripolar.mulBorel_eq_of_restrict_eq_of_zero_off
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_eq_of_restrict_eq_of_zero_off
#check @SGPT.NPP.RelativeNonPluripolar.mulBorel_indicator_eq_of_restrict_eq
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_indicator_eq_of_restrict_eq

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_01

-- Exact frozen body: RelativeMaximumApproximationDraft
section OriginalFragment_02

/-! Relative bounded-potential maximum locality from actual smooth approximations. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorDecreasing LocalBedfordTaylorContinuity

variable {n q : ℕ} {U A : Opens (ComplexModel n)}

/-- Genuine weighted maximum locality for ANY closed positive base current.
The larger original domain supplies smooth approximations internally; the
weight, all approximation currents and their weak limits are produced. -/
theorem mulBorel_ddcMul_max_const_weighted_relCompact
    (hA : RelativelyCompactIn A U) {T : LocalProductCurrent n A (q + 1)}
    (hT : IsPositive T) (hTc : IsClosedCurrent T) {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn U u) (c : ℝ) :
    mulBorel (ddcMul T (fun x => max (u x) c))
        ((A : Set (ComplexModel n)).indicator fun x => max (u x - c) 0) =
      mulBorel (ddcMul T u)
        ((A : Set (ComplexModel n)).indicator fun x => max (u x - c) 0) := by
  have hAU : A ≤ U := subset_closure.trans hA.2
  have huA := isLocallyBoundedPshOn_mono hu hAU
  let v : ComplexModel n → ℝ := fun x => max (u x) c
  let w : ComplexModel n → ℝ := fun x => max (u x - c) 0
  have hv : IsLocallyBoundedPshOn A v :=
    NonPluripolarCurrent.isLocallyBoundedPshOn_max' huA
      (NonPluripolarCurrent.isLocallyBoundedPshOn_const A c)
  have hw : IsLocallyBoundedPshOn A w := by
    simpa only [w, sub_eq_add_neg] using
      NonPluripolarCurrent.isLocallyBoundedPshOn_max'
        (isLocallyBoundedPshOn_add_const huA (-c))
        (NonPluripolarCurrent.isLocallyBoundedPshOn_const A 0)
  let W := (A : Set (ComplexModel n)).indicator w
  have hWm : Measurable W := measurable_indicator_of_isLocallyBoundedPshOn hw
  have hWb : IsLocallyBoundedOn W A := isLocallyBoundedOn_indicator hw
  obtain ⟨f, hf⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hu hA
  have hfA (j : ℕ) : IsLocallyBoundedPshOn A (f j) :=
    isLocallyBoundedPshOn_of_isSmoothPshOn (hf.1 j)
  let g : ℕ → ComplexModel n → ℝ := fun j x => max (f j x) c
  have hgA (j : ℕ) : IsLocallyBoundedPshOn A (g j) :=
    NonPluripolarCurrent.isLocallyBoundedPshOn_max' (hfA j)
      (NonPluripolarCurrent.isLocallyBoundedPshOn_const A c)
  have hterm (j : ℕ) : mulBorel (ddcMul T (g j)) W = mulBorel (ddcMul T (f j)) W := by
    let O : Opens (ComplexModel n) :=
      ⟨(A : Set (ComplexModel n)) ∩ (f j) ⁻¹' Ioi c,
        (hf.1 j).1.continuousOn.isOpen_inter_preimage A.isOpen isOpen_Ioi⟩
    have hOA : O ≤ A := inter_subset_left
    have hloc : restrict hOA (ddcMul T (g j)) = restrict hOA (ddcMul T (f j)) := by
      rw [← ddcMul_restrict hT hOA (hgA j), ← ddcMul_restrict hT hOA (hfA j)]
      have hind : (O : Set (ComplexModel n)).indicator (g j) =
          (O : Set (ComplexModel n)).indicator (f j) := by
        funext x
        by_cases hx : x ∈ (O : Set (ComplexModel n))
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          exact max_eq_left hx.2.le
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      rw [ddcMul, ddcMul, hind]
    apply mulBorel_eq_of_restrict_eq_of_zero_off
      (isPositive_ddcMul hT hTc (hgA j)).1 (isPositive_ddcMul hT hTc (hfA j)).1
      hOA hloc hWm hWb
    intro x hxO
    by_cases hxA : x ∈ (A : Set (ComplexModel n))
    · have hfj : f j x ≤ c := by
        by_contra hnot
        exact hxO ⟨hxA, lt_of_not_ge hnot⟩
      have huf : u x ≤ f j x := (hf.2.1 x hxA).le_of_tendsto (hf.2.2 x hxA) j
      simp only [W, Set.indicator_of_mem hxA, w]
      exact max_eq_right (sub_nonpos.mpr (huf.trans hfj))
    · simp only [W, Set.indicator_of_notMem hxA]
  have weighted_limit (a : ℕ → ComplexModel n → ℝ) (a₀ : ComplexModel n → ℝ)
      (ha : ∀ j, IsLocallyBoundedPshOn A (a j)) (ha₀ : IsLocallyBoundedPshOn A a₀)
      (hanti : ∀ x ∈ A, Antitone fun j => a j x)
      (hlim : ∀ x ∈ A, Tendsto (fun j => a j x) atTop (𝓝 (a₀ x))) :
      WeakTendsto (fun j => mulBorel (ddcMul T (a j)) W) (mulBorel (ddcMul T a₀) W) := by
    let b : ℕ → Fin 2 → ComplexModel n → ℝ := fun j => ![w, a j]
    let b₀ : Fin 2 → ComplexModel n → ℝ := ![w, a₀]
    have hb : ∀ j i, IsLocallyBoundedPshOn A (b j i) := by
      intro j i
      fin_cases i
      · exact hw
      · exact ha j
    have hb₀ : ∀ i, IsLocallyBoundedPshOn A (b₀ i) := by
      intro i
      fin_cases i
      · exact hw
      · exact ha₀
    have hbanti : ∀ i, ∀ x ∈ A, Antitone fun j => b j i x := by
      intro i x hx
      fin_cases i
      · exact fun _ _ _ => le_rfl
      · exact hanti x hx
    have hblim : ∀ i, ∀ x ∈ A, Tendsto (fun j => b j i x) atTop (𝓝 (b₀ i x)) := by
      intro i x hx
      fin_cases i
      · exact tendsto_const_nhds
      · exact hlim x hx
    exact weakTendsto_mulBorel_btProduct_of_antitone 1 q T hT hTc b b₀ hb hb₀ hbanti hblim
  have hplain := weighted_limit f u hfA huA hf.2.1 hf.2.2
  have hmax := weighted_limit g v hgA hv
    (fun x hx i j hij => max_le_max (hf.2.1 x hx hij) le_rfl)
    (fun x hx => (hf.2.2 x hx).max tendsto_const_nhds)
  ext γ φ
  exact tendsto_nhds_unique (hmax γ φ)
    ((hplain γ φ).congr' (Filter.Eventually.of_forall fun j =>
      (congrArg (fun R : LocalProductCurrent n A q => R γ φ) (hterm j)).symm))

end SGPT.NPP.RelativeNonPluripolar

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_02

-- Exact frozen body: RelativePositiveWeightRecoveryDraft
section OriginalFragment_03

/-! Recover the actual strict-locus restriction from a nonnegative weight. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorDecreasing LocalBedfordTaylorContinuity
open SGPT.NPP.NonPluripolarCurrent

variable {n q : ℕ} {U A : Opens (ComplexModel n)}

/-- A genuine weighted current equality determines the whole Borel locus
where the weight is positive, by bounded reciprocal cutoffs. -/
theorem mulBorel_indicator_pos_eq_of_mulBorel_eq
    {R S : LocalProductCurrent n U q} (hR : IsPositive R) (hS : IsPositive S)
    {w : ComplexModel n → ℝ} (hw : Measurable w)
    (hwb : IsLocallyBoundedOn w U) (hw0 : ∀ x, 0 ≤ w x)
    (h : mulBorel R w = mulBorel S w) :
    mulBorel R ({x | 0 < w x}.indicator fun _ => (1 : ℝ)) =
      mulBorel S ({x | 0 < w x}.indicator fun _ => (1 : ℝ)) := by
  let g : ℕ → ComplexModel n → ℝ := fun k x =>
    if 0 < w x then min ((k : ℝ) + 1) (w x)⁻¹ else 0
  have hgm (k : ℕ) : Measurable (g k) :=
    Measurable.ite (measurableSet_lt measurable_const hw)
      (measurable_const.min hw.inv) measurable_const
  have hg (k : ℕ) (x : ComplexModel n) : 0 ≤ g k x ∧ g k x ≤ (k : ℝ) + 1 := by
    by_cases hx : 0 < w x
    · simp only [g, if_pos hx]
      exact ⟨le_min (by positivity) (inv_nonneg.mpr hx.le), min_le_left _ _⟩
    · simp only [g, if_neg hx]
      exact ⟨le_rfl, by positivity⟩
  have hgb (k : ℕ) : IsLocallyBoundedOn (g k) U := by
    intro K _ _
    exact ⟨(k : ℝ) + 1, fun x _ => (abs_of_nonneg (hg k x).1).trans_le (hg k x).2⟩
  let a : ℕ → ComplexModel n → ℝ := fun k x => w x * g k x
  let a₀ : ComplexModel n → ℝ := {x | 0 < w x}.indicator fun _ => 1
  have ham (k : ℕ) : Measurable (a k) := hw.mul (hgm k)
  have ha₀m : Measurable a₀ := measurable_const.indicator (measurableSet_lt measurable_const hw)
  have ha01 (k : ℕ) (x : ComplexModel n) : 0 ≤ a k x ∧ a k x ≤ 1 := by
    refine ⟨mul_nonneg (hw0 x) (hg k x).1, ?_⟩
    by_cases hx : 0 < w x
    · simp only [a, g, if_pos hx]
      calc
        w x * min ((k : ℝ) + 1) (w x)⁻¹ ≤ w x * (w x)⁻¹ :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hx.le
        _ = 1 := mul_inv_cancel₀ hx.ne'
    · simp [a, g, hx]
  have ha₀b (x : ComplexModel n) : |a₀ x| ≤ 1 := by
    by_cases hx : 0 < w x <;> simp [a₀, hx]
  have hlim (x : ComplexModel n) :
      Tendsto (fun k => a k x) atTop (𝓝 (a₀ x)) := by
    by_cases hx : 0 < w x
    · obtain ⟨N, hN⟩ := exists_nat_ge (w x)⁻¹
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with k hk
      have hk' : (w x)⁻¹ ≤ (k : ℝ) + 1 :=
        (hN.trans (Nat.cast_le.mpr hk)).trans (le_add_of_nonneg_right zero_le_one)
      simp [a, a₀, g, hx, min_eq_right hk', mul_inv_cancel₀ hx.ne']
    · simp [a, a₀, g, hx]
  have hterm (k : ℕ) : mulBorel R (a k) = mulBorel S (a k) := by
    change mulBorel R (fun x => w x * g k x) = mulBorel S (fun x => w x * g k x)
    rw [← mulBorel_mulBorel hR hw hwb hw0 (hgm k) (hgb k), h,
      mulBorel_mulBorel hS hw hwb hw0 (hgm k) (hgb k)]
  have hab (k : ℕ) (x : ComplexModel n) : |a k x| ≤ 1 :=
    (abs_of_nonneg (ha01 k x).1).trans_le (ha01 k x).2
  ext γ φ
  exact tendsto_nhds_unique
    (tendsto_mulBorel_apply_of_tendsto hR ham ha₀m hab ha₀b (fun x _ => hlim x) γ φ)
    ((tendsto_mulBorel_apply_of_tendsto hS ham ha₀m hab ha₀b
      (fun x _ => hlim x) γ φ).congr' (Filter.Eventually.of_forall fun k =>
        (congrArg (fun T : LocalProductCurrent n U q => T γ φ) (hterm k)).symm))

/-- Relative one-factor plurifine maximum locality for an arbitrary actual
closed positive current; no non-pluripolar assumption on the base current. -/
theorem mulBorel_ddcMul_max_const_indicator_relCompact
    (hA : RelativelyCompactIn A U) {T : LocalProductCurrent n A (q + 1)}
    (hT : IsPositive T) (hTc : IsClosedCurrent T) {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn U u) (c : ℝ) :
    mulBorel (ddcMul T (fun x => max (u x) c))
        (((A : Set (ComplexModel n)) ∩ {x | c < u x}).indicator fun _ => (1 : ℝ)) =
      mulBorel (ddcMul T u)
        (((A : Set (ComplexModel n)) ∩ {x | c < u x}).indicator fun _ => (1 : ℝ)) := by
  have huA := isLocallyBoundedPshOn_mono hu (subset_closure.trans hA.2)
  let w : ComplexModel n → ℝ := fun x => max (u x - c) 0
  let W := (A : Set (ComplexModel n)).indicator w
  have hw : IsLocallyBoundedPshOn A w := by
    simpa only [w, sub_eq_add_neg] using
      isLocallyBoundedPshOn_max' (isLocallyBoundedPshOn_add_const huA (-c))
        (isLocallyBoundedPshOn_const A 0)
  have hW0 (x : ComplexModel n) : 0 ≤ W x := by
    by_cases hx : x ∈ (A : Set (ComplexModel n))
    · simp only [W, Set.indicator_of_mem hx, w]
      exact le_max_right _ _
    · simp [W, hx]
  have hrec := mulBorel_indicator_pos_eq_of_mulBorel_eq
    (isPositive_ddcMul hT hTc (isLocallyBoundedPshOn_max' huA
      (isLocallyBoundedPshOn_const A c))).1 (isPositive_ddcMul hT hTc huA).1
    (measurable_indicator_of_isLocallyBoundedPshOn hw)
    (isLocallyBoundedOn_indicator hw) hW0
    (mulBorel_ddcMul_max_const_weighted_relCompact hA hT hTc hu c)
  have hset : {x | 0 < W x} = (A : Set (ComplexModel n)) ∩ {x | c < u x} := by
    ext x
    by_cases hx : x ∈ (A : Set (ComplexModel n))
    · simp [W, w, hx]
    · simp [W, hx]
  simpa only [← hset] using hrec

end SGPT.NPP.RelativeNonPluripolar

set_option pp.universes true
set_option pp.explicit true
#check @SGPT.NPP.RelativeNonPluripolar.mulBorel_indicator_pos_eq_of_mulBorel_eq
#check @SGPT.NPP.RelativeNonPluripolar.mulBorel_ddcMul_max_const_indicator_relCompact
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_indicator_pos_eq_of_mulBorel_eq
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_ddcMul_max_const_indicator_relCompact
#check @SGPT.NPP.RelativeNonPluripolar.mulBorel_ddcMul_max_const_weighted_relCompact
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_ddcMul_max_const_weighted_relCompact

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_03

-- Exact frozen body: RelativeProductMaximumDraft
section OriginalFragment_04

/-! Relative maximum locality in a genuine recursive product against arbitrary T. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCollar LocalBedfordTaylorCalculus
open SGPT.NPP.NonPluripolarCurrent

variable {n : ℕ} {U A : Opens (ComplexModel n)}

/-- Actual Borel restriction equality passes to a smaller measurable locus. -/
theorem mulBorel_indicator_eq_of_indicator_eq_of_subset {r : ℕ}
    {R S : LocalProductCurrent n A r} (hR : IsPositive R) (hS : IsPositive S)
    {B C : Set (ComplexModel n)} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : B ⊆ C)
    (h : mulBorel R (C.indicator fun _ => (1 : ℝ)) =
      mulBorel S (C.indicator fun _ => (1 : ℝ))) :
    mulBorel R (B.indicator fun _ => (1 : ℝ)) =
      mulBorel S (B.indicator fun _ => (1 : ℝ)) := by
  have hCI : Measurable (C.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hC
  have hBI : Measurable (B.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hB
  have hC0 (x : ComplexModel n) : 0 ≤ C.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ C <;> simp [hx]
  have hp : (fun x => C.indicator (fun _ => (1 : ℝ)) x *
      B.indicator (fun _ => (1 : ℝ)) x) = B.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ B
    · simp [hx, hBC hx]
    · simp [hx]
  calc
    mulBorel R (B.indicator fun _ => (1 : ℝ)) =
        mulBorel (mulBorel R (C.indicator fun _ => (1 : ℝ)))
          (B.indicator fun _ => (1 : ℝ)) := by
      rw [mulBorel_mulBorel hR hCI (isLocallyBoundedOn_indicator_one C) hC0 hBI
        (isLocallyBoundedOn_indicator_one B), hp]
    _ = mulBorel (mulBorel S (C.indicator fun _ => (1 : ℝ)))
        (B.indicator fun _ => (1 : ℝ)) := congrArg (fun T => mulBorel T _) h
    _ = mulBorel S (B.indicator fun _ => (1 : ℝ)) := by
      rw [mulBorel_mulBorel hS hCI (isLocallyBoundedOn_indicator_one C) hC0 hBI
        (isLocallyBoundedOn_indicator_one B), hp]

/-- Maximum replacement in the outermost genuine relative-product slot. -/
theorem btProduct_update_zero_max_indicator {p r : ℕ}
    (hA : RelativelyCompactIn A U)
    (T : LocalProductCurrent n A (r + (p + 1))) (hT : IsPositive T)
    (hTc : IsClosedAny (r + (p + 1)) T)
    (u : Fin (p + 1) → ComplexModel n → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (c : ℝ)
    {B : Set (ComplexModel n)} (hB : MeasurableSet B)
    (hBsub : B ⊆ (A : Set (ComplexModel n)) ∩ {x | c < u 0 x}) :
    mulBorel (btProduct (p + 1) r
        (Function.update u 0 (fun x => max (u 0 x) c)) T)
        (B.indicator fun _ => (1 : ℝ)) =
      mulBorel (btProduct (p + 1) r u T) (B.indicator fun _ => (1 : ℝ)) := by
  have hAU : A ≤ U := subset_closure.trans hA.2
  have huA (i : Fin (p + 1)) : IsLocallyBoundedPshOn A (u i) :=
    isLocallyBoundedPshOn_mono (hu i) hAU
  have hd : r + (p + 1) = r + 1 + p := by omega
  let T' := castLPC hd T
  let S := btProduct p (r + 1) (Fin.tail u) T'
  have hS : IsPositive S ∧ IsClosedAny (r + 1) S :=
    isPositive_btProduct p (r + 1) (Fin.tail u) T'
      (isPositive_castLPC hd hT) (isClosedAny_castLPC hd hTc) (fun i => huA i.succ)
  have heq : btProduct (p + 1) r u T = ddcMul S (u 0) :=
    btProduct_succ_eq_ddcMul p r u T T' (heq_castLPC hd T)
  have htail : Fin.tail (Function.update u 0 (fun x => max (u 0 x) c)) = Fin.tail u := by
    funext i
    simp [Fin.tail]
  have heqmax : btProduct (p + 1) r
      (Function.update u 0 (fun x => max (u 0 x) c)) T =
      ddcMul S (fun x => max (u 0 x) c) := by
    rw [btProduct_succ_eq_ddcMul p r _ T T' (heq_castLPC hd T), htail]
    simp [S]
  rw [heq, heqmax]
  have hc := isLocallyBoundedPshOn_max' (huA 0) (isLocallyBoundedPshOn_const A c)
  have hC : MeasurableSet ((A : Set (ComplexModel n)) ∩ {x | c < u 0 x}) := by
    have hset : (A : Set (ComplexModel n)) ∩ {x | c < u 0 x} =
        (A : Set (ComplexModel n)) ∩ {x | c < (A : Set (ComplexModel n)).indicator (u 0) x} := by
      ext x
      by_cases hx : x ∈ (A : Set (ComplexModel n)) <;> simp [hx]
    rw [hset]
    exact A.isOpen.measurableSet.inter
      (measurableSet_lt measurable_const (measurable_indicator_of_isLocallyBoundedPshOn (huA 0)))
  apply mulBorel_indicator_eq_of_indicator_eq_of_subset
    (isPositive_ddcMul hS.1 hS.2 hc).1
    (isPositive_ddcMul hS.1 hS.2 (huA 0)).1 hB hC hBsub
  exact mulBorel_ddcMul_max_const_indicator_relCompact hA hS.1 hS.2 (hu 0) c

end SGPT.NPP.RelativeNonPluripolar

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_04

-- Exact frozen body: RelativeProductSlotMaximumDraft
section OriginalFragment_05

/-! Genuine finite-slot maximum replacement for arbitrary relative BT products. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCalculus
open LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent

variable {n : ℕ} {U A : Opens (ComplexModel n)}

/-- Move an arbitrary ORIGINAL slot to the front using genuine relative
permutation symmetry, then use the internally proved maximum locality. -/
theorem btProduct_update_max_indicator {p r : ℕ}
    (hA : RelativelyCompactIn A U)
    (T : LocalProductCurrent n A (r + (p + 1))) (hT : IsPositive T)
    (hTc : IsClosedAny (r + (p + 1)) T)
    (u : Fin (p + 1) → ComplexModel n → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (j : Fin (p + 1)) (c : ℝ)
    {B : Set (ComplexModel n)} (hB : MeasurableSet B)
    (hBsub : B ⊆ (A : Set (ComplexModel n)) ∩ {x | c < u j x}) :
    mulBorel (btProduct (p + 1) r
        (Function.update u j (fun x => max (u j x) c)) T)
        (B.indicator fun _ => (1 : ℝ)) =
      mulBorel (btProduct (p + 1) r u T) (B.indicator fun _ => (1 : ℝ)) := by
  have hAU : A ≤ U := subset_closure.trans hA.2
  have huA (i : Fin (p + 1)) : IsLocallyBoundedPshOn A (u i) :=
    isLocallyBoundedPshOn_mono (hu i) hAU
  have hc := isLocallyBoundedPshOn_max' (huA j) (isLocallyBoundedPshOn_const A c)
  rw [btProduct_update_eq p r T hT hTc u huA j hc,
    ← btProduct_comp_perm (p + 1) r T hT hTc u huA (Equiv.swap 0 j)]
  have hB' : B ⊆ (A : Set (ComplexModel n)) ∩
      {x | c < (u ∘ Equiv.swap 0 j) 0 x} := by
    simpa only [Function.comp_apply, Equiv.swap_apply_left] using hBsub
  simpa only [Function.comp_apply, Equiv.swap_apply_left] using
    btProduct_update_zero_max_indicator hA T hT hTc (u ∘ Equiv.swap 0 j)
      (fun i => hu _) c hB hB'

/-- Replace all original bounded potentials by their maxima, on ANY
measurable locus where every original potential is above its cutoff.
The base current is arbitrary positive closed; the finite replacement
sequence and all its intermediate bounded PSH tuples are manufactured. -/
theorem btProduct_max_all_indicator {p r : ℕ}
    (hA : RelativelyCompactIn A U)
    (T : LocalProductCurrent n A (r + (p + 1))) (hT : IsPositive T)
    (hTc : IsClosedAny (r + (p + 1)) T)
    (u : Fin (p + 1) → ComplexModel n → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (c : Fin (p + 1) → ℝ)
    {B : Set (ComplexModel n)} (hB : MeasurableSet B)
    (hBA : B ⊆ (A : Set (ComplexModel n)))
    (hstrict : ∀ x ∈ B, ∀ i, c i < u i x) :
    mulBorel (btProduct (p + 1) r (fun i x => max (u i x) (c i)) T)
        (B.indicator fun _ => (1 : ℝ)) =
      mulBorel (btProduct (p + 1) r u T) (B.indicator fun _ => (1 : ℝ)) := by
  classical
  let us : Finset (Fin (p + 1)) → Fin (p + 1) → ComplexModel n → ℝ :=
    fun s i x => if i ∈ s then max (u i x) (c i) else u i x
  have hus (s : Finset (Fin (p + 1))) (i : Fin (p + 1)) :
      IsLocallyBoundedPshOn U (us s i) := by
    by_cases hi : i ∈ s
    · simpa only [us, if_pos hi] using
        isLocallyBoundedPshOn_max' (hu i) (isLocallyBoundedPshOn_const U (c i))
    · simpa only [us, if_neg hi] using hu i
  have stage (s : Finset (Fin (p + 1))) :
      mulBorel (btProduct (p + 1) r (us s) T) (B.indicator fun _ => (1 : ℝ)) =
        mulBorel (btProduct (p + 1) r u T) (B.indicator fun _ => (1 : ℝ)) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : us ∅ = u := by
        funext i x
        simp [us]
      rw [he]
    | @insert j s hj ih =>
      have hjval : us s j = u j := by
        funext x
        simp [us, hj]
      have hnew : us (insert j s) =
          Function.update (us s) j (fun x => max (u j x) (c j)) := by
        funext i x
        by_cases hij : i = j
        · subst i
          simp [us]
        · simp [us, hij]
      rw [hnew]
      have hB' : B ⊆ (A : Set (ComplexModel n)) ∩ {x | c j < us s j x} := by
        intro x hx
        exact ⟨hBA hx, by simpa only [Set.mem_ofPred_eq, hjval] using hstrict x hx j⟩
      have hstep := btProduct_update_max_indicator hA T hT hTc (us s)
        (hus s) j (c j) hB hB'
      calc
        mulBorel (btProduct (p + 1) r
            (Function.update (us s) j (fun x => max (u j x) (c j))) T)
            (B.indicator fun _ => (1 : ℝ)) =
            mulBorel (btProduct (p + 1) r (us s) T)
              (B.indicator fun _ => (1 : ℝ)) := by
          simpa only [hjval] using hstep
        _ = mulBorel (btProduct (p + 1) r u T)
            (B.indicator fun _ => (1 : ℝ)) := ih
  have hall : us Finset.univ = (fun i x => max (u i x) (c i)) := by
    funext i x
    simp [us]
  simpa only [hall] using stage Finset.univ

end SGPT.NPP.RelativeNonPluripolar

set_option pp.universes true
set_option pp.explicit true
#check @SGPT.NPP.RelativeNonPluripolar.btProduct_update_max_indicator
#check @SGPT.NPP.RelativeNonPluripolar.btProduct_max_all_indicator
#print axioms SGPT.NPP.RelativeNonPluripolar.btProduct_update_max_indicator
#print axioms SGPT.NPP.RelativeNonPluripolar.btProduct_max_all_indicator
#check @SGPT.NPP.RelativeNonPluripolar.mulBorel_indicator_eq_of_indicator_eq_of_subset
#check @SGPT.NPP.RelativeNonPluripolar.btProduct_update_zero_max_indicator
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_indicator_eq_of_indicator_eq_of_subset
#print axioms SGPT.NPP.RelativeNonPluripolar.btProduct_update_zero_max_indicator

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_05

-- Exact frozen body: RelativeTruncationConsistencyDraft
section OriginalFragment_06

/-! Actual truncation consistency for an arbitrary closed positive base current. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorDecreasing
open SGPT.NPP.NonPluripolarCurrent

variable {n : ℕ} {U A : Opens (ComplexModel n)}

/-- Genuine finite-level relative BT product of the ORIGINAL EReal potentials. -/
def relativeTruncatedBT {p r : ℕ} (A : Opens (ComplexModel n))
    (φ : Fin p → ComplexModel n → EReal)
    (T : LocalProductCurrent n A (r + p)) (k : ℕ) : LocalProductCurrent n A r :=
  btProduct p r (fun i => truncationReal (φ i) k) T

/-- Every strict truncation identity is manufactured for arbitrary T, including
the empty tuple and all original poles. No consistency certificate is input. -/
theorem mulBorel_relativeTruncatedBT_consistent_relCompact {p r : ℕ}
    (hA : RelativelyCompactIn A U)
    (T : LocalProductCurrent n A (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) {k l : ℕ} (hkl : k ≤ l) :
    mulBorel (relativeTruncatedBT A φ T l)
        ((BedfordTaylorTopDegree.strictLocus A φ k).indicator fun _ => (1 : ℝ)) =
      mulBorel (relativeTruncatedBT A φ T k)
        ((BedfordTaylorTopDegree.strictLocus A φ k).indicator fun _ => (1 : ℝ)) := by
  unfold relativeTruncatedBT
  cases p with
  | zero => rfl
  | succ p =>
    have hAU : A ≤ U := subset_closure.trans hA.2
    have hφA (i : Fin (p + 1)) : PlurisubharmonicOn (φ i) A :=
      fun x hx => hφ i x (hAU hx)
    have hB : MeasurableSet (BedfordTaylorTopDegree.strictLocus A φ k) :=
      BedfordTaylorTopDegree.measurableSet_strictLocus hφA k
    have hBA : BedfordTaylorTopDegree.strictLocus A φ k ⊆ (A : Set (ComplexModel n)) :=
      fun _ hx => hx.1
    have hstrict : ∀ x ∈ BedfordTaylorTopDegree.strictLocus A φ k, ∀ i,
        -(k : ℝ) < truncationReal (φ i) l x := by
      intro x hx i
      rw [← EReal.coe_lt_coe_iff, coe_truncationReal (hφ i) l (hAU hx.1)]
      exact (hx.2 i).trans_le (le_max_left _ _)
    have hmax := btProduct_max_all_indicator hA T hT hTc
      (fun i => truncationReal (φ i) l)
      (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) l)
      (fun _ => -(k : ℝ)) hB hBA hstrict
    have heq : btProduct (p + 1) r
        (fun i x => max (truncationReal (φ i) l x) (-(k : ℝ))) T =
        btProduct (p + 1) r (fun i => truncationReal (φ i) k) T :=
      btProduct_congr (p + 1) r _ _ T
        (fun i x hx => truncationReal_nested (hφ i) hkl (hAU hx))
    rw [heq] at hmax
    exact hmax.symm

/-- The SAME original strict loci and actual arbitrary-T truncations form a
genuine positive truncation family on A; all fields are proved internally. -/
theorem isTruncationFamily_relative_relCompact {p r : ℕ}
    (hA : RelativelyCompactIn A U)
    (T : LocalProductCurrent n A (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) :
    IsTruncationFamily (relativeTruncatedBT A φ T)
      (BedfordTaylorTopDegree.strictLocus A φ) := by
  have hAU : A ≤ U := subset_closure.trans hA.2
  have hφA (i : Fin p) : PlurisubharmonicOn (φ i) A := fun x hx => hφ i x (hAU hx)
  exact {
    isPositive := fun k => (isPositive_btProduct p r _ T hT hTc
      (fun i => truncationReal_isLocallyBoundedPshOn (hφA i) k)).1
    measurableSet := BedfordTaylorTopDegree.measurableSet_strictLocus hφA
    subset := fun _ _ hx => hx.1
    mono := fun _ _ hkl => BedfordTaylorTopDegree.strictLocus_mono A φ hkl
    consistent := fun hkl =>
      mulBorel_relativeTruncatedBT_consistent_relCompact hA T hT hTc φ hφ hkl }

end SGPT.NPP.RelativeNonPluripolar

set_option pp.universes true
set_option pp.explicit true
#check @SGPT.NPP.RelativeNonPluripolar.relativeTruncatedBT
#check @SGPT.NPP.RelativeNonPluripolar.mulBorel_relativeTruncatedBT_consistent_relCompact
#check @SGPT.NPP.RelativeNonPluripolar.isTruncationFamily_relative_relCompact
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeTruncatedBT
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_relativeTruncatedBT_consistent_relCompact
#print axioms SGPT.NPP.RelativeNonPluripolar.isTruncationFamily_relative_relCompact

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_06

-- Exact frozen body: RelativeTruncationGlobalDraft
section OriginalFragment_07

/-! Original-domain relative truncation consistency, with all local data produced. -/
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorDecreasing
open LocalBedfordTaylorLocality LocalBedfordTaylorCalculus
open SGPT.NPP.NonPluripolarCurrent

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Every actual original-domain strict truncation identity for arbitrary T.
Compactly contained neighborhoods and restriction comparisons are produced;
there is no larger-domain, avoiding-poles, consistency or locality premise. -/
theorem mulBorel_relativeTruncatedBT_consistent {p r : ℕ}
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) {k l : ℕ} (hkl : k ≤ l) :
    mulBorel (relativeTruncatedBT U φ T l)
        ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) =
      mulBorel (relativeTruncatedBT U φ T k)
        ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) := by
  let O := BedfordTaylorTopDegree.strictLocus U φ k
  have hOm : MeasurableSet O := BedfordTaylorTopDegree.measurableSet_strictLocus hφ k
  have hpos (j : ℕ) : IsPositive (relativeTruncatedBT U φ T j) :=
    (isPositive_btProduct p r _ T hT hTc
      (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) j)).1
  apply eq_of_local
  intro x hx
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds hx)
  let A : Opens (ComplexModel n) := ⟨ball x (R / 2), isOpen_ball⟩
  have hA : RelativelyCompactIn A U := relativelyCompactIn_half_ball hR hball
  have hAU : A ≤ U := subset_closure.trans hA.2
  refine ⟨A, hAU, mem_ball_self (half_pos hR), ?_⟩
  have hTA := isPositive_restrict hT hAU
  have hTcA := isClosedAny_restrict hTc hAU
  have hφA (i : Fin p) : PlurisubharmonicOn (φ i) A := fun y hy => hφ i y (hAU hy)
  let OA := BedfordTaylorTopDegree.strictLocus A φ k
  have hOAm : MeasurableSet OA := BedfordTaylorTopDegree.measurableSet_strictLocus hφA k
  have hposA (j : ℕ) : IsPositive (relativeTruncatedBT A φ (restrict hAU T) j) :=
    (isPositive_btProduct p r _ _ hTA hTcA
      (fun i => truncationReal_isLocallyBoundedPshOn (hφA i) j)).1
  have hind : ∀ y ∈ (A : Set (ComplexModel n)),
      O.indicator (fun _ => (1 : ℝ)) y = OA.indicator (fun _ => (1 : ℝ)) y := by
    intro y hy
    by_cases hc : ∀ i, ((-(k : ℝ) : ℝ) : EReal) < φ i y
    · have hyO : y ∈ O := ⟨hAU hy, hc⟩
      have hyOA : y ∈ OA := ⟨hy, hc⟩
      rw [Set.indicator_of_mem hyO, Set.indicator_of_mem hyOA]
    · have hyO : y ∉ O := fun h => hc h.2
      have hyOA : y ∉ OA := fun h => hc h.2
      rw [Set.indicator_of_notMem hyO, Set.indicator_of_notMem hyOA]
  have hread (j : ℕ) :
      restrict hAU (mulBorel (relativeTruncatedBT U φ T j)
          (O.indicator fun _ => (1 : ℝ))) =
        mulBorel (relativeTruncatedBT A φ (restrict hAU T) j)
          (OA.indicator fun _ => (1 : ℝ)) := by
    rw [← mulBorel_restrict (hpos j) hAU (measurable_const.indicator hOm)
      (isLocallyBoundedOn_indicator_one O)]
    have hprod : restrict hAU (relativeTruncatedBT U φ T j) =
        relativeTruncatedBT A φ (restrict hAU T) j := by
      exact (btProduct_restrict hAU p r _ T hT hTc
        (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) j)).symm
    rw [hprod]
    exact mulBorel_congr (hposA j) (measurable_const.indicator hOm)
      (isLocallyBoundedOn_indicator_one O) (measurable_const.indicator hOAm)
      (isLocallyBoundedOn_indicator_one OA) hind
  rw [hread l, hread k]
  exact mulBorel_relativeTruncatedBT_consistent_relCompact hA
    (restrict hAU T) hTA hTcA φ hφ hkl

/-- Actual positive truncation family on the SAME original domain for
every original closed positive T; its consistency field is a proved producer. -/
theorem isTruncationFamily_relative {p r : ℕ}
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) :
    IsTruncationFamily (relativeTruncatedBT U φ T)
      (BedfordTaylorTopDegree.strictLocus U φ) := {
  isPositive := fun k => (isPositive_btProduct p r _ T hT hTc
    (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k)).1
  measurableSet := BedfordTaylorTopDegree.measurableSet_strictLocus hφ
  subset := fun _ _ hx => hx.1
  mono := fun _ _ hkl => BedfordTaylorTopDegree.strictLocus_mono U φ hkl
  consistent := fun hkl => mulBorel_relativeTruncatedBT_consistent T hT hTc φ hφ hkl }

end SGPT.NPP.RelativeNonPluripolar

set_option pp.universes true
set_option pp.explicit true
#check @SGPT.NPP.RelativeNonPluripolar.mulBorel_relativeTruncatedBT_consistent
#check @SGPT.NPP.RelativeNonPluripolar.isTruncationFamily_relative
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_relativeTruncatedBT_consistent
#print axioms SGPT.NPP.RelativeNonPluripolar.isTruncationFamily_relative

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_07

-- Exact frozen body: RelativeFiniteMassDraft
section OriginalFragment_08

/-!
# The actual finite-mass relative non-pluripolar current

The original base current may charge pluripolar sets. The mass hypothesis
is the actual compact-uniform bound on the relative truncation trace
measures, not a supplied output current or a truncation-family certificate.
The current is returned as a positive-current subtype whose construction
uses the proved mass condition. There is no universal zero-fallback claim.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorContinuity
open SGPT.NPP.NonPluripolarCurrent

variable {n p r : ℕ} {U : Opens (ComplexModel n)}

/-- Finite relative mass of the SAME actual arbitrary-T truncation products. -/
def HasFiniteRelativeMass
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) : Prop :=
  ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ U →
    ⨆ k, ((isTruncationFamily_relative T hT hTc φ hφ).isPositive k).traceMeasure
      (K ∩ BedfordTaylorTopDegree.strictLocus U φ k) < ⊤

/-- The source mass condition selects the genuine integration branch of glue. -/
theorem hasLocallyFiniteMass_relative_iff
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) :
    (isTruncationFamily_relative T hT hTc φ hφ).HasLocallyFiniteMass ↔
      HasFiniteRelativeMass T hT hTc φ hφ :=
  (isTruncationFamily_relative T hT hTc φ hφ).hasLocallyFiniteMass_iff

/-- The relative product is supplied only under actual finite relative mass;
its positivity proof uses that mass condition in the genuine gluing theorem. -/
def relativeNonPluripolarProduct
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) :
    {S : LocalProductCurrent n U r // IsPositive S} :=
  ⟨(isTruncationFamily_relative T hT hTc φ hφ).glue,
    (isTruncationFamily_relative T hT hTc φ hφ).isPositive_glue
      ((hasLocallyFiniteMass_relative_iff T hT hTc φ hφ).mpr hm)⟩

/-- Actual closedness, with every cutoff manufactured from the original PSH
tuple and no hypothesis that the arbitrary original T avoids pole sets. -/
theorem isClosedAny_relativeNonPluripolarProduct
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) :
    IsClosedAny r (relativeNonPluripolarProduct T hT hTc φ hφ hm).val := by
  cases r with
  | zero => trivial
  | succ r =>
    exact (isTruncationFamily_relative T hT hTc φ hφ).isClosedCurrent_glue
      ((hasLocallyFiniteMass_relative_iff T hT hTc φ hφ).mpr hm)
      (fun k => (isPositive_btProduct p (r + 1) _ T hT hTc
        (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k)).2)
      (hasPshCutoffs_strictLocus hφ)

/-- The actual restricted truncations converge to the actual constructed current. -/
theorem weakTendsto_relativeTruncations
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) :
    WeakTendsto
      (truncAt (relativeTruncatedBT U φ T) (BedfordTaylorTopDegree.strictLocus U φ))
      (relativeNonPluripolarProduct T hT hTc φ hφ hm).val :=
  (isTruncationFamily_relative T hT hTc φ hφ).weakTendsto_truncAt_glue
    ((hasLocallyFiniteMass_relative_iff T hT hTc φ hφ).mpr hm)

/-- Exact source strict-locus current identity at every original level. -/
theorem mulBorel_relativeNonPluripolarProduct_strictLocus
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) (k : ℕ) :
    mulBorel (relativeNonPluripolarProduct T hT hTc φ hφ hm).val
      ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) =
      truncAt (relativeTruncatedBT U φ T) (BedfordTaylorTopDegree.strictLocus U φ) k :=
  (isTruncationFamily_relative T hT hTc φ hφ).mulBorel_glue_indicator
    ((hasLocallyFiniteMass_relative_iff T hT hTc φ hφ).mpr hm) k

/-- Extension by zero off the union of original strict finite loci. -/
theorem mulBorel_relativeNonPluripolarProduct_compl
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ) :
    mulBorel (relativeNonPluripolarProduct T hT hTc φ hφ hm).val
      ((⋃ k, BedfordTaylorTopDegree.strictLocus U φ k)ᶜ.indicator
        fun _ => (1 : ℝ)) = 0 :=
  (isTruncationFamily_relative T hT hTc φ hφ).mulBorel_glue_compl
    ((hasLocallyFiniteMass_relative_iff T hT hTc φ hφ).mpr hm)

/-- Uniqueness among ALL positive currents with the defining identities;
neither closedness nor order relative to the constructed current is a premise. -/
theorem eq_relativeNonPluripolarProduct_of_mulBorel
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hm : HasFiniteRelativeMass T hT hTc φ hφ)
    {S : LocalProductCurrent n U r} (hS : IsPositive S)
    (h₁ : ∀ k, mulBorel S
      ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) =
        truncAt (relativeTruncatedBT U φ T) (BedfordTaylorTopDegree.strictLocus U φ) k)
    (h₂ : mulBorel S ((⋃ k, BedfordTaylorTopDegree.strictLocus U φ k)ᶜ.indicator
      fun _ => (1 : ℝ)) = 0) :
    S = (relativeNonPluripolarProduct T hT hTc φ hφ hm).val :=
  (isTruncationFamily_relative T hT hTc φ hφ).eq_glue_of_mulBorel
    ((hasLocallyFiniteMass_relative_iff T hT hTc φ hφ).mpr hm) hS h₁ h₂

/-- Any actual positive extension bounds ALL original truncated trace masses. -/
theorem hasFiniteRelativeMass_of_positive_extension
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    {S : LocalProductCurrent n U r} (hS : IsPositive S)
    (h₁ : ∀ k, mulBorel S
      ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) =
        truncAt (relativeTruncatedBT U φ T) (BedfordTaylorTopDegree.strictLocus U φ) k) :
    HasFiniteRelativeMass T hT hTc φ hφ := by
  intro K hK hKU
  refine lt_of_le_of_lt (iSup_le fun k => ?_) (hS.traceMeasure_lt_top hK hKU)
  have heq := traceMeasure_inter_eq_of_mulBorel_eq
    ((isTruncationFamily_relative T hT hTc φ hφ).isPositive k) hS
    (BedfordTaylorTopDegree.measurableSet_strictLocus hφ k) (h₁ k).symm hK hKU
  exact heq.trans_le (measure_mono inter_subset_left)

/-- Finite relative mass is exactly existence of an actual weak limit;
the forward implication constructs that limit from the original inputs. -/
theorem hasFiniteRelativeMass_iff_exists_weak_limit
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) :
    HasFiniteRelativeMass T hT hTc φ hφ ↔
      ∃ S : LocalProductCurrent n U r,
        WeakTendsto
          (truncAt (relativeTruncatedBT U φ T) (BedfordTaylorTopDegree.strictLocus U φ)) S := by
  constructor
  · intro hm
    exact ⟨_, weakTendsto_relativeTruncations T hT hTc φ hφ hm⟩
  · rintro ⟨S, hS⟩
    exact (hasLocallyFiniteMass_relative_iff T hT hTc φ hφ).mp
      ((isTruncationFamily_relative T hT hTc φ hφ).hasLocallyFiniteMass_of_weakTendsto hS)

end SGPT.NPP.RelativeNonPluripolar

set_option pp.universes true
set_option pp.explicit true
#check @SGPT.NPP.RelativeNonPluripolar.HasFiniteRelativeMass
#check @SGPT.NPP.RelativeNonPluripolar.relativeNonPluripolarProduct
#check @SGPT.NPP.RelativeNonPluripolar.isClosedAny_relativeNonPluripolarProduct
#check @SGPT.NPP.RelativeNonPluripolar.weakTendsto_relativeTruncations
#check @SGPT.NPP.RelativeNonPluripolar.mulBorel_relativeNonPluripolarProduct_strictLocus
#check @SGPT.NPP.RelativeNonPluripolar.eq_relativeNonPluripolarProduct_of_mulBorel
#print axioms SGPT.NPP.RelativeNonPluripolar.HasFiniteRelativeMass
#print axioms SGPT.NPP.RelativeNonPluripolar.hasLocallyFiniteMass_relative_iff
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeNonPluripolarProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.isClosedAny_relativeNonPluripolarProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.weakTendsto_relativeTruncations
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_relativeNonPluripolarProduct_strictLocus
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_relativeNonPluripolarProduct_compl
#print axioms SGPT.NPP.RelativeNonPluripolar.eq_relativeNonPluripolarProduct_of_mulBorel
#print axioms SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_of_positive_extension
#print axioms SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_iff_exists_weak_limit

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_08

-- Exact frozen body: RelativeBoundedCompatibilityDraft
section OriginalFragment_09

/-!
# Bounded relative products: actual maximum locality and automatic finite mass

The base current is arbitrary closed positive, including currents charging
pluripolar sets. All local neighborhoods, relative maximum replacements,
trace bounds and defining-current identities are manufactured internally.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.RelativeNonPluripolar

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCalculus
open LocalBedfordTaylorLocality
open SGPT.NPP.NonPluripolarCurrent

variable {n p r : ℕ} {U : Opens (ComplexModel n)}

/-- Arbitrary-relative all-slot maximum locality on the ORIGINAL open domain.
The compactly contained neighborhoods and all restriction dictionaries are
manufactured; no larger-domain or local-output premise is supplied. -/
theorem btProduct_max_all_indicator_global
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (u : Fin p → ComplexModel n → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (c : Fin p → ℝ)
    {B : Set (ComplexModel n)} (hB : MeasurableSet B)
    (hstrict : ∀ x ∈ B, ∀ i, c i < u i x) :
    mulBorel (btProduct p r (fun i x => max (u i x) (c i)) T)
        (B.indicator fun _ => (1 : ℝ)) =
      mulBorel (btProduct p r u T) (B.indicator fun _ => (1 : ℝ)) := by
  cases p with
  | zero => rfl
  | succ p =>
    have hmax (i : Fin (p + 1)) :
        IsLocallyBoundedPshOn U (fun x => max (u i x) (c i)) :=
      isLocallyBoundedPshOn_max' (hu i) (isLocallyBoundedPshOn_const U (c i))
    apply eq_of_local
    intro x hx
    obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (U.isOpen.mem_nhds hx)
    let A : Opens (ComplexModel n) := ⟨ball x (R / 2), isOpen_ball⟩
    have hA : RelativelyCompactIn A U := relativelyCompactIn_half_ball hR hball
    have hAU : A ≤ U := subset_closure.trans hA.2
    refine ⟨A, hAU, mem_ball_self (half_pos hR), ?_⟩
    have hTA := isPositive_restrict hT hAU
    have hTcA := isClosedAny_restrict hTc hAU
    let BA := B ∩ (A : Set (ComplexModel n))
    have hBAm : MeasurableSet BA := hB.inter A.isOpen.measurableSet
    have hread (v : Fin (p + 1) → ComplexModel n → ℝ)
        (hv : ∀ i, IsLocallyBoundedPshOn U (v i)) :
        restrict hAU (mulBorel (btProduct (p + 1) r v T)
          (B.indicator fun _ => (1 : ℝ))) =
        mulBorel (btProduct (p + 1) r v (restrict hAU T))
          (BA.indicator fun _ => (1 : ℝ)) := by
      have hpos := (isPositive_btProduct (p + 1) r v T hT hTc hv).1
      rw [← mulBorel_restrict hpos hAU (measurable_const.indicator hB)
        (isLocallyBoundedOn_indicator_one _)]
      have hprod : restrict hAU (btProduct (p + 1) r v T) =
          btProduct (p + 1) r v (restrict hAU T) :=
        (btProduct_restrict hAU (p + 1) r v T hT hTc hv).symm
      rw [hprod]
      exact mulBorel_congr
        (isPositive_btProduct (p + 1) r v _ hTA hTcA
          (fun i => isLocallyBoundedPshOn_mono (hv i) hAU)).1
        (measurable_const.indicator hB) (isLocallyBoundedOn_indicator_one _)
        (measurable_const.indicator hBAm) (isLocallyBoundedOn_indicator_one _)
        (fun y hy => by
          by_cases hyB : y ∈ B
          · rw [Set.indicator_of_mem hyB, Set.indicator_of_mem (show y ∈ BA from ⟨hyB, hy⟩)]
          · rw [Set.indicator_of_notMem hyB,
              Set.indicator_of_notMem (show y ∉ BA from fun h => hyB h.1)])
    rw [hread _ hmax, hread _ hu]
    exact btProduct_max_all_indicator hA (restrict hAU T) hTA hTcA u hu c hBAm
      inter_subset_right (fun y hy i => hstrict y hy.1 i)

/-- The actual arbitrary-T bounded product and its actual truncation have
the SAME strict-locus restriction, on every original level and domain. -/
theorem mulBorel_relativeTruncatedBT_coe_eq_btProduct
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (u : Fin p → ComplexModel n → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (k : ℕ) :
    truncAt (relativeTruncatedBT U (fun i x => (u i x : EReal)) T)
        (BedfordTaylorTopDegree.strictLocus U (fun i x => (u i x : EReal))) k =
      mulBorel (btProduct p r u T)
        ((BedfordTaylorTopDegree.strictLocus U (fun i x => (u i x : EReal)) k).indicator
          fun _ => (1 : ℝ)) := by
  unfold truncAt relativeTruncatedBT
  have heq : (fun i => truncationReal (fun x => (u i x : EReal)) k) =
      (fun i x => max (u i x) (-(k : ℝ))) := by
    funext i x
    exact truncationReal_coe (u i) k x
  rw [heq]
  exact btProduct_max_all_indicator_global T hT hTc u hu (fun _ => -(k : ℝ))
    (BedfordTaylorTopDegree.measurableSet_strictLocus (fun i => (hu i).1) k)
    (fun _ hx i => EReal.coe_lt_coe_iff.mp (hx.2 i))

/-- Automatic finite relative mass for every ORIGINAL bounded PSH tuple
against every ORIGINAL closed positive T, including its pluripolar mass. -/
theorem hasFiniteRelativeMass_of_isLocallyBoundedPshOn
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (u : Fin p → ComplexModel n → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    HasFiniteRelativeMass T hT hTc (fun i x => (u i x : EReal)) (fun i => (hu i).1) :=
  hasFiniteRelativeMass_of_positive_extension T hT hTc
    (fun i x => (u i x : EReal)) (fun i => (hu i).1)
    (isPositive_btProduct p r u T hT hTc hu).1
    (fun k => (mulBorel_relativeTruncatedBT_coe_eq_btProduct T hT hTc u hu k).symm)

/-- A single genuine strict truncation level contains every finite slot at
each original nonpole point. Empty tuples and arbitrary pole sets are retained. -/
theorem iUnion_strictLocus_eq_nonpole
    (φ : Fin p → ComplexModel n → EReal) :
    (⋃ k, BedfordTaylorTopDegree.strictLocus U φ k) =
      {x | x ∈ U ∧ ∀ i, φ i x ≠ ⊥} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact ⟨hk.1, fun i => ne_bot_of_gt (hk.2 i)⟩
  · intro hx
    choose k hk using fun i => exists_nat_neg_lt (hx.2 i)
    let K := Finset.univ.sup k
    refine mem_iUnion.mpr ⟨K, hx.1, fun i => ?_⟩
    have hki : k i ≤ K := Finset.le_sup (Finset.mem_univ i)
    exact (strictTruncationLocus_mono U (φ i) hki ⟨hx.1, hk i⟩).2

/-- Actual relative NPP of bounded original potentials equals the genuine
relative BT product, with its mass condition proved rather than supplied. -/
theorem relativeNonPluripolarProduct_of_isLocallyBoundedPshOn
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T)
    (u : Fin p → ComplexModel n → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    (relativeNonPluripolarProduct T hT hTc (fun i x => (u i x : EReal))
      (fun i => (hu i).1) (hasFiniteRelativeMass_of_isLocallyBoundedPshOn T hT hTc u hu)).val =
      btProduct p r u T := by
  have hR := (isPositive_btProduct p r u T hT hTc hu).1
  apply (eq_relativeNonPluripolarProduct_of_mulBorel T hT hTc
    (fun i x => (u i x : EReal)) (fun i => (hu i).1)
    (hasFiniteRelativeMass_of_isLocallyBoundedPshOn T hT hTc u hu) hR
    (fun k => (mulBorel_relativeTruncatedBT_coe_eq_btProduct T hT hTc u hu k).symm) ?_).symm
  have hunion : (⋃ k, BedfordTaylorTopDegree.strictLocus U
      (fun i x => (u i x : EReal)) k) = (U : Set (ComplexModel n)) := by
    rw [iUnion_strictLocus_eq_nonpole]
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun i => EReal.coe_ne_bot _⟩⟩
  rw [hunion]
  calc
    mulBorel (btProduct p r u T)
        ((U : Set (ComplexModel n))ᶜ.indicator fun _ => (1 : ℝ)) =
        mulBorel (btProduct p r u T) (fun _ => (0 : ℝ)) := by
      apply mulBorel_congr hR
        (measurable_const.indicator U.isOpen.measurableSet.compl)
        (isLocallyBoundedOn_indicator_one _) measurable_const
        (fun _ _ _ => ⟨0, fun _ _ => by simp⟩)
      intro x hx
      rw [Set.indicator_of_notMem (show x ∉ (U : Set (ComplexModel n))ᶜ from fun h => h hx)]
    _ = 0 := by rw [mulBorel_const hR 0, zero_smul]

end SGPT.NPP.RelativeNonPluripolar

set_option pp.universes true
set_option pp.explicit true
#check @SGPT.NPP.RelativeNonPluripolar.btProduct_max_all_indicator_global
#check @SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_of_isLocallyBoundedPshOn
#check @SGPT.NPP.RelativeNonPluripolar.relativeNonPluripolarProduct_of_isLocallyBoundedPshOn
#print axioms SGPT.NPP.RelativeNonPluripolar.btProduct_max_all_indicator_global
#print axioms SGPT.NPP.RelativeNonPluripolar.mulBorel_relativeTruncatedBT_coe_eq_btProduct
#print axioms SGPT.NPP.RelativeNonPluripolar.hasFiniteRelativeMass_of_isLocallyBoundedPshOn
#print axioms SGPT.NPP.RelativeNonPluripolar.iUnion_strictLocus_eq_nonpole
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeNonPluripolarProduct_of_isLocallyBoundedPshOn

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_09
