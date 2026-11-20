import SGPT.Okounkov.TranscendentalMainStatement
import SGPT.AlmostSemigroup.BodyFubini
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The volume identity: Fubini along the first coordinate

Package VOL of the formalization of `thm:Okounkovtranmain` (blueprint
`claude-okounkov-transcendental`, node `tok:Cn-implies-An`, and the chapter `claude-tok-volid`,
node `tok-volid:fubini`): Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov
bodies* (DRWNXZ), Lemma 7.3 (`C_n ⇒ A_n`), measure-theoretic part.

* `volume_eq_lintegral_firstCoordinateSlice`: for a measurable `Δ ⊆ ℝⁿ⁺¹`,
  `vol Δ = ∫ vol {y : (t, y) ∈ Δ} dt` (Fubini--Tonelli for `ℝⁿ⁺¹ = ℝ × ℝⁿ`).
* `volume_eq_lintegral_Ioo_firstCoordinateSlice`: if the first coordinate of `Δ` ranges in
  `[a, b]`, the integral may be taken over `(a, b)`.
* `volume_eq_div_factorial_of_sliceIdentity` (`tok:Cn-implies-An`, abstract form): if
  `V = (m + 2) ∫_a^b R` and `R(t) = (m + 1)! vol Δ_t` on `(a, b)`, then `vol Δ = V / (m + 2)!`.
* `continuousOn_volume_firstCoordinateSlice` (`ok:source-body-slice-continuity` with
  `ok:hausdorff-body-volume-continuous`, transported from the Euclidean statement of
  `SGPT.AlmostSemigroup.BodyFubini`): for a nonempty compact convex `Δ`, the slice volume
  `t ↦ vol Δ_t` is continuous on the projection `[a, b]` of `Δ`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalVolId

open Set Filter MeasureTheory
open scoped ENNReal Nat Topology
open SGPT.Okounkov.TranscendentalMain

/-- The inverse of the head/tail splitting `ℝⁿ⁺¹ ≅ ℝ × ℝⁿ` is `(t, y) ↦ (t, y)` (`Fin.cons`). -/
theorem piFinSuccAbove_symm_apply_eq_cons {m : ℕ} (p : ℝ × (Fin m → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm p = Fin.cons p.1 p.2 := by
  change Fin.insertNth (α := fun _ => ℝ) 0 p.1 p.2 = _
  exact Fin.insertNth_zero' p.1 p.2

/-- **Fubini along the first coordinate**: `vol Δ = ∫ vol {y : (t, y) ∈ Δ} dt`. -/
theorem volume_eq_lintegral_firstCoordinateSlice {m : ℕ} {Δ : Set (Fin (m + 1) → ℝ)}
    (hΔ : MeasurableSet Δ) :
    volume Δ = ∫⁻ t : ℝ, volume (firstCoordinateSlice Δ t) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 with he
  have hmp : MeasurePreserving e :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hmps : MeasurePreserving e.symm := hmp.symm e
  have hpre : MeasurableSet (e.symm ⁻¹' Δ) := e.symm.measurable hΔ
  rw [← hmps.measure_preimage hΔ.nullMeasurableSet]
  change (volume : Measure (ℝ × (Fin m → ℝ))) (e.symm ⁻¹' Δ) = _
  rw [Measure.volume_eq_prod, Measure.prod_apply hpre]
  refine lintegral_congr fun t => ?_
  congr 1
  ext y
  simp only [mem_preimage, firstCoordinateSlice]
  rw [piFinSuccAbove_symm_apply_eq_cons]
  rfl

/-- Slices outside the projection are empty. -/
theorem firstCoordinateSlice_eq_empty {m : ℕ} {Δ : Set (Fin (m + 1) → ℝ)} {a b : ℝ}
    (hproj : (fun x : Fin (m + 1) → ℝ => x 0) '' Δ ⊆ Icc a b) {t : ℝ} (ht : t ∉ Icc a b) :
    firstCoordinateSlice Δ t = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun y hy => ht ?_
  have h := hproj ⟨_, hy, rfl⟩
  simpa using h

/-- **Fubini over the projection**: if the first coordinate of `Δ` lies in `[a, b]`, then
`vol Δ = ∫_{(a, b)} vol Δ_t dt`. -/
theorem volume_eq_lintegral_Ioo_firstCoordinateSlice {m : ℕ} {Δ : Set (Fin (m + 1) → ℝ)}
    (hΔ : MeasurableSet Δ) {a b : ℝ}
    (hproj : (fun x : Fin (m + 1) → ℝ => x 0) '' Δ ⊆ Icc a b) :
    volume Δ = ∫⁻ t in Ioo a b, volume (firstCoordinateSlice Δ t) := by
  rw [volume_eq_lintegral_firstCoordinateSlice hΔ]
  have h1 : ∫⁻ t : ℝ, volume (firstCoordinateSlice Δ t) =
      ∫⁻ t in Icc a b, volume (firstCoordinateSlice Δ t) := by
    rw [← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ Icc a b
    · rw [indicator_of_mem ht]
    · rw [indicator_of_notMem ht, firstCoordinateSlice_eq_empty hproj ht, measure_empty]
  rw [h1]
  exact (setLIntegral_congr Ioo_ae_eq_Icc).symm

/-- **`tok:Cn-implies-An`, abstract form** (DRWNXZ Lemma 7.3): if the first coordinate of `Δ`
ranges in `[a, b]`, `V = (m + 2) ∫_a^b R(t) dt` and `R(t) = (m + 1)! vol Δ_t` for
`t ∈ (a, b)`, then `vol Δ = V / (m + 2)!`. -/
theorem volume_eq_div_factorial_of_sliceIdentity {m : ℕ} {Δ : Set (Fin (m + 2) → ℝ)}
    (hΔ : MeasurableSet Δ) {a b : ℝ}
    (hproj : (fun x : Fin (m + 2) → ℝ => x 0) '' Δ ⊆ Icc a b) (R : ℝ → ℝ≥0∞) (V : ℝ≥0∞)
    (hV : V = ((m + 2 : ℕ) : ℝ≥0∞) * ∫⁻ t in Ioo a b, R t)
    (hC : ∀ t ∈ Ioo a b, R t = ((m + 1)! : ℝ≥0∞) * volume (firstCoordinateSlice Δ t)) :
    volume Δ = V / ((m + 2)! : ℝ≥0∞) := by
  have hf0 : ((m + 1)! : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (m + 1)).ne'
  have hft : ((m + 1)! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h20 : ((m + 2 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.succ_pos (m + 1)).ne'
  have h2t : ((m + 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [volume_eq_lintegral_Ioo_firstCoordinateSlice hΔ hproj]
  have hslice : ∫⁻ t in Ioo a b, volume (firstCoordinateSlice Δ t) =
      (∫⁻ t in Ioo a b, R t) / ((m + 1)! : ℝ≥0∞) := by
    rw [ENNReal.div_eq_inv_mul, ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hf0)]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [hC t ht, ← mul_assoc, ENNReal.inv_mul_cancel hf0 hft, one_mul]
  rw [hslice, hV, Nat.factorial_succ (m + 1), Nat.cast_mul]
  rw [ENNReal.mul_div_mul_left _ _ h20 h2t]

/-! ### Continuity of slice volumes -/

/-- The convex body `Δ ⊆ ℝⁿ` as a `ConvexBody` of the Euclidean space. -/
def euclideanConvexBody {k : ℕ} {Δ : Set (Fin k → ℝ)} (hconv : Convex ℝ Δ) (hcpt : IsCompact Δ)
    (hne : Δ.Nonempty) : ConvexBody (EuclideanSpace ℝ (Fin k)) where
  carrier := euclideanImage Δ
  convex' := by
    unfold euclideanImage
    exact hconv.linear_image ((EuclideanSpace.equiv (Fin k) ℝ).symm.toLinearEquiv.toLinearMap)
  isCompact' := hcpt.image (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous
  nonempty' := hne.image _

/-- The Euclidean fibre of `Δ` at `t` is the Euclidean copy of the slice `Δ_t`. -/
theorem euclideanFiber_euclideanConvexBody {m : ℕ} {Δ : Set (Fin (m + 1) → ℝ)}
    (hconv : Convex ℝ Δ) (hcpt : IsCompact Δ) (hne : Δ.Nonempty) (t : ℝ) :
    SGPT.AlmostSemigroup.BodyFubini.euclideanFiber
        ((euclideanConvexBody hconv hcpt hne : Set (EuclideanSpace ℝ (Fin (m + 1))))) t =
      (EuclideanSpace.equiv (Fin m) ℝ) ⁻¹' firstCoordinateSlice Δ t := by
  ext y
  simp only [SGPT.AlmostSemigroup.BodyFubini.euclideanFiber,
    SGPT.AlmostSemigroup.BodyFubini.productFiber, mem_preimage,
    firstCoordinateSlice]
  set e := SGPT.AlmostSemigroup.BodyFubini.splitMeasureEquiv m
  rw [e.image_eq_preimage_symm]
  change e.symm (t, y) ∈ euclideanImage Δ ↔ Fin.cons t ((EuclideanSpace.equiv (Fin m) ℝ) y) ∈ Δ
  unfold euclideanImage
  rw [(EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.image_eq_preimage_symm, mem_preimage]
  have : (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.symm (e.symm (t, y)) =
      Fin.cons t ((EuclideanSpace.equiv (Fin m) ℝ) y) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  rw [this]

/-- The volume of the Euclidean fibre is the volume of the slice. -/
theorem volume_euclideanFiber_euclideanConvexBody {m : ℕ} {Δ : Set (Fin (m + 1) → ℝ)}
    (hconv : Convex ℝ Δ) (hcpt : IsCompact Δ) (hne : Δ.Nonempty) (t : ℝ) :
    volume (SGPT.AlmostSemigroup.BodyFubini.euclideanFiber
        ((euclideanConvexBody hconv hcpt hne : Set (EuclideanSpace ℝ (Fin (m + 1))))) t) =
      volume (firstCoordinateSlice Δ t) := by
  rw [euclideanFiber_euclideanConvexBody]
  have hmp := PiLp.volume_preserving_ofLp (Fin m)
  have hcl : IsClosed (firstCoordinateSlice Δ t) :=
    hcpt.isClosed.preimage (by fun_prop : Continuous fun y : Fin m → ℝ =>
      (Fin.cons t y : Fin (m + 1) → ℝ))
  exact hmp.measure_preimage hcl.measurableSet.nullMeasurableSet

/-- **Continuity of the slice volumes** (`ok:source-body-slice-continuity`): for a nonempty
compact convex `Δ ⊆ ℝⁿ⁺¹` whose first coordinate ranges over `[a, b]`, `t ↦ vol Δ_t` is
continuous on `[a, b]` (as a real function). -/
theorem continuousOn_volume_firstCoordinateSlice {m : ℕ} {Δ : Set (Fin (m + 1) → ℝ)}
    (hconv : Convex ℝ Δ) (hcpt : IsCompact Δ) {a b : ℝ}
    (hproj : (fun x : Fin (m + 1) → ℝ => x 0) '' Δ = Icc a b) (hab : a ≤ b) :
    ContinuousOn (fun t => (volume (firstCoordinateSlice Δ t)).toReal) (Icc a b) := by
  have hne : Δ.Nonempty := by
    have : (Icc a b).Nonempty := nonempty_Icc.mpr hab
    rw [← hproj] at this
    exact this.of_image
  set K := euclideanConvexBody hconv hcpt hne
  have hcont := SGPT.AlmostSemigroup.BodyFubini.continuous_real_euclideanFiber m K
  -- the projection of `K` is `[a, b]`
  have hKproj : (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' (K : Set _) = Icc a b := by
    rw [← hproj]
    change (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' euclideanImage Δ = _
    unfold euclideanImage
    rw [image_image]
    rfl
  have hmin : SGPT.AlmostSemigroup.BodyExtrema.coordinateMin 0 K = a := by
    change sInf ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' (K : Set _)) = a
    rw [hKproj, csInf_Icc hab]
  have hmax : SGPT.AlmostSemigroup.BodyExtrema.coordinateMax 0 K = b := by
    change sSup ((fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) '' (K : Set _)) = b
    rw [hKproj, csSup_Icc hab]
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : (Icc a b).domRestrict (fun t => (volume (firstCoordinateSlice Δ t)).toReal) =
      (fun t : Icc (SGPT.AlmostSemigroup.BodyExtrema.coordinateMin 0 K)
          (SGPT.AlmostSemigroup.BodyExtrema.coordinateMax 0 K) =>
        volume.real (SGPT.AlmostSemigroup.BodyFubini.euclideanFiber
          (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) t)) ∘
        (fun t : Icc a b => (⟨t.1, by rw [hmin, hmax]; exact t.2⟩ :
          Icc (SGPT.AlmostSemigroup.BodyExtrema.coordinateMin 0 K)
            (SGPT.AlmostSemigroup.BodyExtrema.coordinateMax 0 K))) := by
    funext t
    simp only [Function.comp_apply, Set.domRestrict_apply, Measure.real]
    rw [volume_euclideanFiber_euclideanConvexBody]
  rw [hfun]
  exact hcont.comp (by fun_prop)

end SGPT.Okounkov.TranscendentalVolId
