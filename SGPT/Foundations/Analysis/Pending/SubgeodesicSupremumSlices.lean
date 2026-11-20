import SGPT.Foundations.Analysis.FirstPass.SubgeodesicConvexity
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicChordBound
import SGPT.Foundations.Analysis.Pending.StripSliceRegularization

/-!
# Interior slices of a regularized subgeodesic supremum

A finite common upper bound and the three-point chord inequality control time
variation locally, uniformly in space and in the family index. Consequently
joint regularization commutes with interior slices, including polar slices.
The abstract result works for a continuous real time map on any topological
parameter space. Applying it to complex real part supplies the interior
interchange in Xia, SGPT Proposition 4.1.3, PDF page 0151.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumSlices

open FirstPass

noncomputable section

/-- Joint regularization commutes with an interior slice of an extended-real
curve satisfying the chord inequality and a finite common upper bound. -/
theorem uscRegularization_time_slice_eq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : ℝ → X → EReal)
    (time : Y → ℝ) (htime : Continuous time) {C : ℝ}
    (hC : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, f t x ≤ (C : EReal))
    (hchord : ∀ a t b : ℝ, a ∈ Ioo (0 : ℝ) 1 → t ∈ Ioo (0 : ℝ) 1 →
      b ∈ Ioo (0 : ℝ) 1 → a < t → t < b → ∀ x,
      f t x ≤ eRealChord (f a x) (f b x) ((t - a) / (b - a)))
    (x : X) {y : Y} (hy : time y ∈ Ioo (0 : ℝ) 1) :
    uscRegularization (fun p : X × Y => f (time p.2) p.1) (x, y) =
      uscRegularization (f (time y)) x := by
  refine le_antisymm ?_
    (StripSliceRegularization.uscRegularization_slice_le
      (fun p : X × Y => f (time p.2) p.1) x y)
  apply le_of_forall_gt
  intro c hc
  obtain ⟨r, hvr, hrc⟩ := EReal.lt_iff_exists_real_btwn.mp hc
  obtain ⟨K, hvK, hKr⟩ := EReal.lt_iff_exists_real_btwn.mp hvr
  have hKr' : K < r := EReal.coe_lt_coe_iff.mp hKr
  set t₀ : ℝ := time y with ht₀
  set a : ℝ := t₀ / 2 with ha_def
  set b : ℝ := (t₀ + 1) / 2 with hb_def
  have ht : t₀ ∈ Ioo (0 : ℝ) 1 := hy
  have ha : a ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [a]; linarith [ht.1],
    by dsimp [a]; linarith [ht.1, ht.2]⟩
  have hb : b ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [b]; linarith [ht.1],
    by dsimp [b]; linarith [ht.2]⟩
  have hat : a < t₀ := by dsimp [a]; linarith [ht.1]
  have htb : t₀ < b := by dsimp [b]; linarith [ht.2]
  let L : ℝ → ℝ := fun s => (1 - (s - a) / (t₀ - a)) * C +
    ((s - a) / (t₀ - a)) * K
  let R : ℝ → ℝ := fun s => (1 - (s - t₀) / (b - t₀)) * K +
    ((s - t₀) / (b - t₀)) * C
  have hLt : L t₀ = K := by simp [L, ne_of_gt (sub_pos.mpr hat)]
  have hRt : R t₀ = K := by simp [R]
  have hL : {s | L s < r} ∈ 𝓝 t₀ :=
    (show Continuous L by fun_prop).continuousAt
      (isOpen_Iio.mem_nhds (by simpa [hLt] using hKr'))
  have hR : {s | R s < r} ∈ 𝓝 t₀ :=
    (show Continuous R by fun_prop).continuousAt
      (isOpen_Iio.mem_nhds (by simpa [hRt] using hKr'))
  have hT : Ioo a b ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ⟨hat, htb⟩
  have hV : time ⁻¹' ({s | L s < r} ∩ {s | R s < r} ∩ Ioo a b) ∈ 𝓝 y :=
    htime.continuousAt.preimage_mem_nhds (inter_mem (inter_mem hL hR) hT)
  have hU : {z | uscRegularization (f t₀) z < (K : EReal)} ∈ 𝓝 x :=
    upperSemicontinuous_uscRegularization (f t₀) x _ hvK
  have hbound : ∀ᶠ p : X × Y in 𝓝 (x, y), f (time p.2) p.1 ≤ (r : EReal) := by
    rw [nhds_prod_eq]
    filter_upwards [Filter.prod_mem_prod hU hV] with p hp
    obtain ⟨hpU, ⟨⟨hpL, hpR⟩, hpT⟩⟩ := hp
    have hpK : f t₀ p.1 ≤ (K : EReal) :=
      (le_uscRegularization (f t₀) p.1).trans hpU.le
    have hpI : time p.2 ∈ Ioo (0 : ℝ) 1 :=
      ⟨ha.1.trans hpT.1, hpT.2.trans hb.2⟩
    rcases lt_trichotomy (time p.2) t₀ with hleft | heq | hright
    · have hs : (time p.2 - a) / (t₀ - a) ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos (sub_pos.mpr hpT.1) (sub_pos.mpr hat),
          (div_lt_one (sub_pos.mpr hat)).2 (by linarith)⟩
      calc f (time p.2) p.1
          ≤ eRealChord (f a p.1) (f t₀ p.1) ((time p.2 - a) / (t₀ - a)) :=
            hchord a _ t₀ ha hpI ht hpT.1 hleft p.1
        _ ≤ eRealChord (C : EReal) (K : EReal) ((time p.2 - a) / (t₀ - a)) :=
            eRealChord_mono (hC a ha p.1) hpK hs.1.le hs.2.le
        _ = (L (time p.2) : EReal) := by
            simp only [eRealChord, L, EReal.coe_add, EReal.coe_mul]
        _ ≤ (r : EReal) := EReal.coe_le_coe_iff.mpr hpL.le
    · simpa [heq] using hpK.trans hKr.le
    · have hs : (time p.2 - t₀) / (b - t₀) ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos (sub_pos.mpr hright) (sub_pos.mpr htb),
          (div_lt_one (sub_pos.mpr htb)).2 (by linarith [hpT.2])⟩
      calc f (time p.2) p.1
          ≤ eRealChord (f t₀ p.1) (f b p.1) ((time p.2 - t₀) / (b - t₀)) :=
            hchord t₀ _ b ht hpI hb hright hpT.2 p.1
        _ ≤ eRealChord (K : EReal) (C : EReal) ((time p.2 - t₀) / (b - t₀)) :=
            eRealChord_mono hpK (hC b hb p.1) hs.1.le hs.2.le
        _ = (R (time p.2) : EReal) := by
            simp only [eRealChord, R, EReal.coe_add, EReal.coe_mul]
        _ ≤ (r : EReal) := EReal.coe_le_coe_iff.mpr hpR.le
  have hsup : (⨆ p ∈ {p : X × Y | f (time p.2) p.1 ≤ (r : EReal)},
      f (time p.2) p.1) ≤ (r : EReal) := iSup₂_le fun p hp => hp
  exact ((uscRegularization_le_localSup
    (fun p : X × Y => f (time p.2) p.1) hbound).trans hsup).trans_lt hrc

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The raw pointwise supremum of a subgeodesic family satisfies the
three-point chord inequality, including an empty family. -/
theorem iSup_le_eRealChord_between {ι : Type*} {theta : SmoothRealForm n M 2}
    {curve : ι → ℝ → M → EReal} (h : ∀ i, IsSubgeodesicInterior theta (curve i))
    {a t b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hb : b ∈ Ioo (0 : ℝ) 1) (hat : a < t) (htb : t < b) (x : M) :
    (⨆ i, curve i t x) ≤ eRealChord (⨆ i, curve i a x) (⨆ i, curve i b x)
      ((t - a) / (b - a)) := by
  have hs : (t - a) / (b - a) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hat) (sub_pos.mpr (hat.trans htb)),
      (div_lt_one (sub_pos.mpr (hat.trans htb))).2 (by linarith)⟩
  exact iSup_le fun i => ((h i).le_eRealChord_between ha ht hb hat htb x).trans
    (eRealChord_mono (le_iSup (fun i => curve i a x) i)
      (le_iSup (fun i => curve i b x) i) hs.1.le hs.2.le)

/-- Joint space/complex-time regularization of a uniformly bounded-above
subgeodesic supremum agrees with spatial regularization on every interior slice.
No countability, compactness or bounded lower obstacle is needed. -/
theorem uscRegularization_iSup_complex_slice_eq {ι : Type*}
    {theta : SmoothRealForm n M 2} {curve : ι → ℝ → M → EReal}
    (h : ∀ i, IsSubgeodesicInterior theta (curve i)) {C : ℝ}
    (hC : ∀ i t, t ∈ Ioo (0 : ℝ) 1 → ∀ x, curve i t x ≤ (C : EReal))
    (x : M) {tau : ℂ} (htau : tau.re ∈ Ioo (0 : ℝ) 1) :
    uscRegularization (fun p : M × ℂ => ⨆ i, curve i p.2.re p.1) (x, tau) =
      uscRegularization (fun z => ⨆ i, curve i tau.re z) x := by
  apply uscRegularization_time_slice_eq (fun t x => ⨆ i, curve i t x)
    Complex.re Complex.continuous_re (fun t ht x => iSup_le fun i => hC i t ht x)
    (fun a t b ha ht hb hat htb x => iSup_le_eRealChord_between h ha ht hb hat htb x)
    x htau

/-- One upper bound for the two endpoint families bounds every interior
slice of every corresponding subgeodesic. -/
theorem uniform_upper_bound_of_endpoint_bounds {ι : Type*}
    {theta : SmoothRealForm n M 2} {curve : ι → ℝ → M → EReal}
    {u₀ u₁ : ι → M → EReal} (h : ∀ i, IsSubgeodesicFrom theta (curve i) (u₀ i) (u₁ i))
    {C : ℝ} (h₀ : ∀ i x, u₀ i x ≤ (C : EReal))
    (h₁ : ∀ i x, u₁ i x ≤ (C : EReal)) :
    ∀ i t, t ∈ Ioo (0 : ℝ) 1 → ∀ x, curve i t x ≤ (C : EReal) := by
  intro i t ht x
  refine ((h i).le_eRealChord ht x).trans
    ((eRealChord_mono (h₀ i x) (h₁ i x) ht.1.le ht.2.le).trans_eq ?_)
  unfold eRealChord
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  congr 1
  ring

/-- The interior regularization interchange under the endpoint-family
hypotheses of Perron stability. -/
theorem uscRegularization_iSup_complex_slice_eq_of_endpoint_bounds {ι : Type*}
    {theta : SmoothRealForm n M 2} {curve : ι → ℝ → M → EReal}
    {u₀ u₁ : ι → M → EReal} (h : ∀ i, IsSubgeodesicFrom theta (curve i) (u₀ i) (u₁ i))
    {C : ℝ} (h₀ : ∀ i x, u₀ i x ≤ (C : EReal))
    (h₁ : ∀ i x, u₁ i x ≤ (C : EReal))
    (x : M) {tau : ℂ} (htau : tau.re ∈ Ioo (0 : ℝ) 1) :
    uscRegularization (fun p : M × ℂ => ⨆ i, curve i p.2.re p.1) (x, tau) =
      uscRegularization (fun z => ⨆ i, curve i tau.re z) x :=
  uscRegularization_iSup_complex_slice_eq (fun i => (h i).interior)
    (uniform_upper_bound_of_endpoint_bounds h h₀ h₁) x htau

end

end SGPT.Foundations.Analysis.Pending.SubgeodesicSupremumSlices
