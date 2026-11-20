import SGPT.Envelopes.MADirichlet4Compactness
import SGPT.PSH.LocalL1Recovery
import SGPT.Foundations.Analysis.Pending.RegularizedIncreasingPshGapCapacityZero

/-!
# `L¹_loc` convergence of bounded plurisubharmonic functions against a fixed measure

Xia, *Foundations of pluripotential theory* (FPT), `lem:bounded-psh-fixed-measure-continuity`:
let `D ⊆ ℂⁿ` be open, `ν` a finite measure on `D` that does not charge sets of capacity zero,
and `v_j` plurisubharmonic on `D` with `|v_j| ≤ L` converging in `L¹_loc(D)` to the
plurisubharmonic `v`. Then `∫_D |v_j - v| dν → 0` (`tendsto_lintegral_abs_sub_of_localL1`).
The hypothesis on `ν` holds if `ν ≤ (ddᶜw)ⁿ` for a bounded plurisubharmonic `w`
(`capacityNull_of_le_ma`).

Here "capacity zero" refers to TN's relative capacity `Cap_D` (`relCapacity`) and `L¹_loc`
convergence is `∫⁻_K |v_j - v| → 0` for every compact `K ⊆ D`. (FPT's hypothesis on `ν` uses
the outer capacity; for the measures `ν ≤ (ddᶜw)ⁿ` used later both versions hold.)

*Proof* (FPT). **Step 1** (`ae_frequently_lt_of_localL1`): for every `ℓ`, TN's regularized
supremum `V_ℓ` of the increasing sequence `max(v_ℓ, …, v_{ℓ+k})` is plurisubharmonic, lies above
`v` (it lies above `v_j`, `j ≥ ℓ`, and `L¹_loc` convergence preserves this almost everywhere,
hence everywhere), and differs from `sup_{j ≥ ℓ} v_j` only on a set of capacity zero (TN
`regularized_isIncApprox_and_relCapacity_gap_eq_zero`). Hence `ν`-almost everywhere
`v ≤ sup_{j≥ℓ} v_j` for every `ℓ`, i.e. `v ≤ limsup v_j`. With Hartogs' lemma
(`limsup v_j ≤ v` everywhere) this identifies the limit of every `ν`-a.e. convergent subsequence
of convex combinations. **Step 2** (`exists_convexHull_tendsto_integral`): convex combinations
`r_ℓ` of `v_ℓ, v_{ℓ+1}, …` with almost minimal `L²(ν)` norm form a Cauchy sequence (parallelogram
identity); a fast subsequence converges `ν`-a.e. (Borel–Cantelli), hence to `v`, and dominated
convergence gives `∫ r_ℓ dν → ∫ v dν`; therefore `liminf ∫ v_j dν ≥ ∫ v dν`. **Step 3**:
`(v_j - v)₊ → 0` pointwise (Hartogs) and `|t| = 2t₊ - t`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-! ### Measurability and `L¹_loc` order -/

/-- A locally bounded plurisubharmonic function is upper semicontinuous on its domain. -/
theorem upperSemicontinuousOn_of_isLocallyBoundedPshOn {D : Opens (ComplexModel n)}
    {φ : ComplexModel n → ℝ} (hφ : IsLocallyBoundedPshOn D φ) :
    UpperSemicontinuousOn φ D := by
  intro x hx y hy
  have h := hφ.1.upperSemicontinuousOn x hx (y : EReal) (EReal.coe_lt_coe_iff.mpr hy)
  exact h.mono fun z hz => EReal.coe_lt_coe_iff.mp hz

/-- A locally bounded plurisubharmonic function is almost everywhere measurable for every measure
restricted to its domain. -/
theorem aemeasurable_of_isLocallyBoundedPshOn {D : Opens (ComplexModel n)}
    {φ : ComplexModel n → ℝ} (hφ : IsLocallyBoundedPshOn D φ) (μ : Measure (ComplexModel n)) :
    AEMeasurable φ (μ.restrict D) := by
  refine aemeasurable_restrict_of_measurable_subtype D.isOpen.measurableSet ?_
  exact (upperSemicontinuousOn_iff_restrict.mpr (upperSemicontinuousOn_of_isLocallyBoundedPshOn hφ)).measurable

/-- Countable exhaustion: a property holding almost everywhere on every compact subset of an
open set holds almost everywhere on the open set. -/
theorem ae_restrict_of_forall_compact {D : Opens (ComplexModel n)} {μ : Measure (ComplexModel n)}
    {P : ComplexModel n → Prop}
    (h : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D → ∀ᵐ x ∂μ.restrict K, P x) :
    ∀ᵐ x ∂μ.restrict D, P x := by
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion D
  have hD : (D : Set (ComplexModel n)) = ⋃ m, closure (U m : Set (ComplexModel n)) := by
    refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun m => (hUrc m).2)
    obtain ⟨m, hm⟩ := hUabs {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    exact mem_iUnion.mpr ⟨m, subset_closure (hm rfl)⟩
  rw [hD, ae_restrict_iUnion_iff]
  exact fun m => h _ (hUrc m).1 (hUrc m).2

/-- **`L¹_loc` limits preserve upper bounds almost everywhere.** -/
theorem ae_le_of_localL1 {D : Opens (ComplexModel n)} {f : ℕ → ComplexModel n → ℝ}
    {v W : ComplexModel n → ℝ} (hv : AEMeasurable v (volume.restrict D))
    (hW : AEMeasurable W (volume.restrict D))
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun j => ∫⁻ x in K, ENNReal.ofReal |f j x - v x|) atTop (𝓝 0))
    {ℓ : ℕ} (hle : ∀ j, ℓ ≤ j → ∀ z ∈ D, f j z ≤ W z) :
    ∀ᵐ x ∂volume.restrict D, v x ≤ W x := by
  refine ae_restrict_of_forall_compact fun K hK hKD => ?_
  have hbound : ∀ j, ℓ ≤ j → ∫⁻ x in K, ENNReal.ofReal (v x - W x) ≤
      ∫⁻ x in K, ENNReal.ofReal |f j x - v x| := by
    intro j hj
    refine setLIntegral_mono' hK.measurableSet fun x hx => ENNReal.ofReal_le_ofReal ?_
    have := hle j hj x (hKD hx)
    rw [abs_sub_comm]
    exact (by linarith : v x - W x ≤ v x - f j x).trans (le_abs_self _)
  have hzero : ∫⁻ x in K, ENNReal.ofReal (v x - W x) = 0 :=
    le_antisymm (ge_of_tendsto (hlim K hK hKD)
      ((eventually_ge_atTop ℓ).mono fun j hj => hbound j hj)) bot_le
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (v x - W x)) (volume.restrict K) :=
    ((hv.sub hW).mono_measure (Measure.restrict_mono hKD le_rfl)).ennreal_ofReal
  filter_upwards [(lintegral_eq_zero_iff' hmeas).mp hzero] with x hx
  exact sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hx)

/-- **Hartogs' lemma, pointwise** (FPT `thm:psh-compactness-hartogs`): `limsup v_j ≤ v`
everywhere on `D`. -/
theorem eventually_lt_add_of_localL1 {D : Opens (ComplexModel n)} {f : ℕ → ComplexModel n → ℝ}
    {v : ComplexModel n → ℝ} (hf : ∀ j, IsLocallyBoundedPshOn D (f j))
    (hv : IsLocallyBoundedPshOn D v)
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun j => ∫⁻ x in K, ENNReal.ofReal |f j x - v x|) atTop (𝓝 0))
    {x : ComplexModel n} (hx : x ∈ D) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ j in atTop, f j x < v x + δ := by
  have hlim' : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun j => ∫⁻ y in K, canonicalERealAbsDiff (f j y : EReal) (v y : EReal))
        atTop (𝓝 0) := by
    intro K hK hKD
    simpa only [canonicalERealAbsDiff_coe_coe] using hlim K hK hKD
  have h := SGPT.PSH.LocalL1Recovery.eventually_lt_of_localL1
    (fun j => (hf j).1.discPshOn) hv.1.discPshOn D.isOpen volume hlim' hx
    (a := v x + δ) (EReal.coe_lt_coe_iff.mpr (by linarith))
  exact h.mono fun j hj => EReal.coe_lt_coe_iff.mp hj

/-! ### Step 1: the upper limit is `v` almost everywhere for measures not charging capacity zero -/

/-- The partial maxima `max(f_ℓ, …, f_{ℓ+k})`. -/
def partialMax (f : ℕ → ComplexModel n → ℝ) (ℓ : ℕ) : ℕ → ComplexModel n → ℝ
  | 0 => f ℓ
  | k + 1 => fun z => max (partialMax f ℓ k z) (f (ℓ + (k + 1)) z)

theorem partialMax_mono (f : ℕ → ComplexModel n → ℝ) (ℓ : ℕ) (z : ComplexModel n) :
    Monotone fun k => partialMax f ℓ k z :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

theorem le_partialMax (f : ℕ → ComplexModel n → ℝ) (ℓ : ℕ) (z : ComplexModel n) :
    ∀ k j, ℓ ≤ j → j ≤ ℓ + k → f j z ≤ partialMax f ℓ k z := by
  intro k
  induction k with
  | zero =>
    intro j h1 h2
    have : j = ℓ := by omega
    subst this
    exact le_rfl
  | succ k ih =>
    intro j h1 h2
    rcases Nat.lt_or_ge j (ℓ + (k + 1)) with h | h
    · exact (ih j h1 (by omega)).trans (le_max_left _ _)
    · have : j = ℓ + (k + 1) := by omega
      subst this
      exact le_max_right _ _

theorem exists_eq_partialMax (f : ℕ → ComplexModel n → ℝ) (ℓ : ℕ) (z : ComplexModel n) :
    ∀ k, ∃ j, ℓ ≤ j ∧ partialMax f ℓ k z = f j z := by
  intro k
  induction k with
  | zero => exact ⟨ℓ, le_rfl, rfl⟩
  | succ k ih =>
    obtain ⟨j, hj, hje⟩ := ih
    change ∃ i, ℓ ≤ i ∧ max (partialMax f ℓ k z) (f (ℓ + (k + 1)) z) = f i z
    rcases le_total (partialMax f ℓ k z) (f (ℓ + (k + 1)) z) with h | h
    · exact ⟨ℓ + (k + 1), by omega, max_eq_right h⟩
    · exact ⟨j, hj, (max_eq_left h).trans hje⟩

theorem isLocallyBoundedPshOn_partialMax {D : Opens (ComplexModel n)}
    {f : ℕ → ComplexModel n → ℝ} (hf : ∀ j, IsLocallyBoundedPshOn D (f j)) {L : ℝ}
    (hL : ∀ j, ∀ z ∈ D, |f j z| ≤ L) (ℓ k : ℕ) :
    IsLocallyBoundedPshOn D (partialMax f ℓ k) ∧ ∀ z ∈ D, |partialMax f ℓ k z| ≤ L := by
  induction k with
  | zero => exact ⟨hf ℓ, hL ℓ⟩
  | succ k ih =>
    have hb : ∀ z ∈ D, |partialMax f ℓ (k + 1) z| ≤ L := fun z hz =>
      abs_max_le_max_abs_abs.trans (max_le (ih.2 z hz) (hL _ z hz))
    refine ⟨isLocallyBoundedPshOn_of_abs_le ?_ hb, hb⟩
    have h := ih.1.1.max (hf (ℓ + (k + 1))).1
    refine fun z hz => (h z hz).congr ?_
    exact Eventually.of_forall fun y => (EReal.coe_strictMono.monotone.map_max).symm

/-- Sets of relative capacity zero are null for `ν`. -/
def CapacityNull (D : Opens (ComplexModel n)) (ν : Measure (ComplexModel n)) : Prop :=
  ∀ E : Set (ComplexModel n), E ⊆ D → relCapacity D E = 0 → ν E = 0

/-- A measure dominated by the Monge–Ampère measure of a bounded plurisubharmonic function does
not charge sets of capacity zero (FPT, last assertion of
`lem:bounded-psh-fixed-measure-continuity`). -/
theorem capacityNull_of_le_ma {D : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    (hw : IsLocallyBoundedPshOn D w) {a M : ℝ} (hM : 0 ≤ M)
    (hwb : ∀ z ∈ D, a ≤ w z ∧ w z ≤ a + M) {ν : Measure (ComplexModel n)}
    (hν : ν.restrict D ≤ canonicalBedfordTaylorMeasure D w hw) : CapacityNull D ν := by
  intro E hED hE
  have h1 : ν E = ν.restrict D E := by
    rw [Measure.restrict_apply' D.isOpen.measurableSet, inter_eq_left.mpr hED]
  have h2 := ma_le_ofReal_pow_mul_relCapacity hw hM hwb (E := E) (by rw [hE]; exact ENNReal.zero_ne_top)
  rw [hE, mul_zero] at h2
  exact le_antisymm (h1 ▸ (Measure.le_iff'.mp hν E).trans h2) bot_le

/-- **Step 1 of FPT `lem:bounded-psh-fixed-measure-continuity`**: `ν`-almost everywhere on `D`,
`v ≤ sup_{j ≥ ℓ} v_j` for every `ℓ`; in particular `v ≤ limsup v_j`. -/
theorem ae_frequently_lt_of_localL1 {D : Opens (ComplexModel n)} {f : ℕ → ComplexModel n → ℝ}
    {v : ComplexModel n → ℝ} (hf : ∀ j, IsLocallyBoundedPshOn D (f j))
    (hv : IsLocallyBoundedPshOn D v) {L : ℝ} (hL : ∀ j, ∀ z ∈ D, |f j z| ≤ L)
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun j => ∫⁻ x in K, ENNReal.ofReal |f j x - v x|) atTop (𝓝 0))
    {ν : Measure (ComplexModel n)} (hν : CapacityNull D ν) :
    ∀ᵐ x ∂ν.restrict D, ∀ ℓ : ℕ, ∀ δ : ℝ, 0 < δ → ∃ j, ℓ ≤ j ∧ v x - δ < f j x := by
  set c : ℝ := (|L| + 1)⁻¹ with hcdef
  have hc : 0 < c := by positivity
  have hcL : c * |L| ≤ 1 := by
    rw [hcdef, inv_mul_le_iff₀ (by positivity)]
    linarith
  have hgap : ∀ ℓ : ℕ, ∃ N : Set (ComplexModel n), ν N = 0 ∧ ∀ x ∈ D, x ∉ N →
      ∀ δ : ℝ, 0 < δ → ∃ j, ℓ ≤ j ∧ v x - δ < f j x := by
    intro ℓ
    set g : ℕ → ComplexModel n → ℝ := fun k z => c * partialMax f ℓ k z with hgdef
    have hpm := isLocallyBoundedPshOn_partialMax hf hL ℓ
    have hgpsh : ∀ k, IsLocallyBoundedPshOn D (g k) := fun k =>
      isLocallyBoundedPshOn_const_mul (hpm k).1 hc.le
    have hgb : ∀ k x, x ∈ D → -1 ≤ g k x ∧ g k x ≤ 1 := by
      intro k x hx
      refine abs_le.mp ?_
      change |c * partialMax f ℓ k x| ≤ 1
      rw [abs_mul, abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left (((hpm k).2 x hx).trans (le_abs_self L)) hc.le).trans hcL
    have hmono : ∀ x ∈ D, Monotone fun k => g k x := fun x _ a b hab =>
      mul_le_mul_of_nonneg_left (partialMax_mono f ℓ x hab) hc.le
    have hreg := RegularizedIncreasingPshGapCapacityZero.regularized_isIncApprox_and_relCapacity_gap_eq_zero
      (le_refl D) g (fun k => (hgpsh k).1) hmono hgb
    dsimp only at hreg
    obtain ⟨hV, -, hinc, hgapD⟩ := hreg
    set p : ComplexModel n → EReal := fun x => ⨆ k, ((g k x : ℝ) : EReal) with hpdef
    set V : ComplexModel n → ℝ := fun x => (uscRegularization p x).toReal with hVdef
    refine ⟨{x | x ∈ D ∧ p x < uscRegularization p x}, hν _ (fun x hx => hx.1) (hgapD D le_rfl),
      fun x hx hxN δ hδ => ?_⟩
    -- `v ≤ c⁻¹ V` on `D`
    have hcV : IsLocallyBoundedPshOn D fun z => c⁻¹ * V z :=
      isLocallyBoundedPshOn_const_mul hV (inv_nonneg.mpr hc.le)
    have hae := ae_le_of_localL1 (aemeasurable_of_isLocallyBoundedPshOn hv volume)
      (aemeasurable_of_isLocallyBoundedPshOn hcV volume) hlim (ℓ := ℓ)
      (fun j hj z hz => by
        have h1 : g (j - ℓ) z ≤ V z := hinc.2.2.1 (j - ℓ) z hz
        have h2 : f j z ≤ partialMax f ℓ (j - ℓ) z :=
          le_partialMax f ℓ z (j - ℓ) j hj (by omega)
        rw [le_inv_mul_iff₀ hc]
        exact (mul_le_mul_of_nonneg_left h2 hc.le).trans h1)
    have hvV : (v x : EReal) ≤ ((c⁻¹ * V x : ℝ) : EReal) :=
      hv.1.le_of_ae_le D.isOpen hcV.1.upperSemicontinuousOn volume
        (hae.mono fun z hz => EReal.coe_le_coe_iff.mpr hz) x hx
    have hvV' : c * v x ≤ V x := by
      have := EReal.coe_le_coe_iff.mp hvV
      rwa [le_inv_mul_iff₀ hc] at this
    -- off the gap, `V = sup_k g_k`
    have hPp : uscRegularization p x ≤ p x := not_lt.mp fun h => hxN ⟨hx, h⟩
    have hp1 : p x ≤ 1 := iSup_le fun k => by exact_mod_cast (hgb k x hx).2
    have hp0 : ((-1 : ℝ) : EReal) ≤ p x :=
      (EReal.coe_le_coe_iff.mpr (hgb 0 x hx).1).trans (le_iSup (fun k => ((g k x : ℝ) : EReal)) 0)
    have hPeq : uscRegularization p x = p x := le_antisymm hPp (le_uscRegularization p x)
    have hpfin : ((p x).toReal : EReal) = p x :=
      EReal.coe_toReal (ne_of_lt (hp1.trans_lt (EReal.coe_lt_top 1)))
        (ne_of_gt ((EReal.bot_lt_coe (-1)).trans_le hp0))
    have hlt : (((c * (v x - δ)) : ℝ) : EReal) < p x := by
      rw [← hpfin]
      refine EReal.coe_lt_coe_iff.mpr ?_
      have : V x = (p x).toReal := by simp only [hVdef, hPeq]
      rw [← this]
      nlinarith
    obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt
    have hk' : c * (v x - δ) < c * partialMax f ℓ k x := EReal.coe_lt_coe_iff.mp hk
    obtain ⟨j, hj, hje⟩ := exists_eq_partialMax f ℓ x k
    exact ⟨j, hj, hje ▸ lt_of_mul_lt_mul_left hk' hc.le⟩
  choose N hN0 hN using hgap
  have hnull : ∀ ℓ, ∀ᵐ x ∂ν.restrict D, x ∉ N ℓ := fun ℓ =>
    measure_eq_zero_iff_ae_notMem.mp
      (le_antisymm ((Measure.le_iff'.mp Measure.restrict_le_self (N ℓ)).trans (hN0 ℓ).le) bot_le)
  filter_upwards [ae_all_iff.mpr hnull, ae_restrict_mem D.isOpen.measurableSet] with x hx hxD
  exact fun ℓ => hN ℓ x hxD (hx ℓ)

/-! ### Step 2: convex combinations -/

/-- Elements of the convex hull of a tail of the sequence keep the bounds, plurisubharmonicity
and the `L¹_loc` distance to `v` (bounded by the supremum `e K` over the tail). -/
theorem convexHull_tail_props {D : Opens (ComplexModel n)} {f : ℕ → ComplexModel n → ℝ}
    {v : ComplexModel n → ℝ} (hf : ∀ j, IsLocallyBoundedPshOn D (f j)) {L : ℝ}
    (hL : ∀ j, ∀ z ∈ D, |f j z| ≤ L) (hv : IsLocallyBoundedPshOn D v) (ℓ : ℕ)
    (e : Set (ComplexModel n) → ℝ≥0∞)
    (he : ∀ j, ℓ ≤ j → ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      ∫⁻ x in K, ENNReal.ofReal |f j x - v x| ≤ e K) :
    ∀ r ∈ convexHull ℝ (f '' Ici ℓ), IsLocallyBoundedPshOn D r ∧ (∀ z ∈ D, |r z| ≤ L) ∧
      ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
        ∫⁻ x in K, ENNReal.ofReal |r x - v x| ≤ e K := by
  refine convexHull_min ?_ ?_
  · rintro _ ⟨j, hj, rfl⟩
    exact ⟨hf j, hL j, he j hj⟩
  intro r hr s hs a b ha hb hab
  have hfun : (a • r + b • s) = fun z => a * r z + b * s z + 0 * ‖z‖ ^ 2 := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero]
  refine ⟨?_, fun z hz => ?_, fun K hK hKD => ?_⟩
  · rw [hfun]
    exact isLocallyBoundedPshOn_linComb hr.1 hs.1 ha hb le_rfl
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * r z + b * s z| ≤ |a * r z| + |b * s z| := abs_add_le _ _
      _ = a * |r z| + b * |s z| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * L + b * L := add_le_add (mul_le_mul_of_nonneg_left (hr.2.1 z hz) ha)
          (mul_le_mul_of_nonneg_left (hs.2.1 z hz) hb)
      _ = L := by rw [← add_mul, hab, one_mul]
  · have hmr : AEMeasurable (fun x => ENNReal.ofReal a * ENNReal.ofReal |r x - v x|)
        (volume.restrict K) :=
      (((continuous_abs.measurable.comp_aemeasurable
        ((aemeasurable_of_isLocallyBoundedPshOn hr.1 volume).sub
          (aemeasurable_of_isLocallyBoundedPshOn hv volume))).ennreal_ofReal).const_mul _).mono_measure
        (Measure.restrict_mono hKD le_rfl)
    calc ∫⁻ x in K, ENNReal.ofReal |(a • r + b • s) x - v x|
        ≤ ∫⁻ x in K, (ENNReal.ofReal a * ENNReal.ofReal |r x - v x| +
            ENNReal.ofReal b * ENNReal.ofReal |s x - v x|) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
            ← ENNReal.ofReal_add (mul_nonneg ha (abs_nonneg _)) (mul_nonneg hb (abs_nonneg _))]
          refine ENNReal.ofReal_le_ofReal ?_
          have : (a • r + b • s) x - v x = a * (r x - v x) + b * (s x - v x) := by
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            linear_combination (v x) * hab
          rw [this]
          calc |a * (r x - v x) + b * (s x - v x)| ≤ |a * (r x - v x)| + |b * (s x - v x)| :=
                abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ = ENNReal.ofReal a * (∫⁻ x in K, ENNReal.ofReal |r x - v x|) +
            ENNReal.ofReal b * ∫⁻ x in K, ENNReal.ofReal |s x - v x| := by
          rw [lintegral_add_left' hmr, lintegral_const_mul' (ENNReal.ofReal a) _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' (ENNReal.ofReal b) _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal a * e K + ENNReal.ofReal b * e K :=
          add_le_add (mul_le_mul_right (hr.2.2 K hK hKD) _) (mul_le_mul_right (hs.2.2 K hK hKD) _)
      _ = e K := by rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]

/-- Bounded plurisubharmonic functions are integrable against a finite measure on `D`. -/
theorem integrable_of_isLocallyBoundedPshOn {D : Opens (ComplexModel n)}
    {ν : Measure (ComplexModel n)} [IsFiniteMeasure ν] {r : ComplexModel n → ℝ}
    (hr : IsLocallyBoundedPshOn D r) {L : ℝ} (hL : ∀ z ∈ D, |r z| ≤ L) :
    Integrable r (ν.restrict D) := by
  refine (integrable_const L).mono' (aemeasurable_of_isLocallyBoundedPshOn hr ν).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
  exact hL z hz

/-- **Step 2 of FPT `lem:bounded-psh-fixed-measure-continuity`**: there are convex combinations
`r_i` of `v_i, v_{i+1}, …` with `∫_D r_i dν → ∫_D v dν`. -/
theorem exists_convexHull_tendsto_integral {D : Opens (ComplexModel n)}
    {f : ℕ → ComplexModel n → ℝ} {v : ComplexModel n → ℝ}
    (hf : ∀ j, IsLocallyBoundedPshOn D (f j)) (hv : IsLocallyBoundedPshOn D v) {L : ℝ}
    (hL : ∀ j, ∀ z ∈ D, |f j z| ≤ L)
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun j => ∫⁻ x in K, ENNReal.ofReal |f j x - v x|) atTop (𝓝 0))
    {ν : Measure (ComplexModel n)} [IsFiniteMeasure ν] (hν : CapacityNull D ν) :
    ∃ r : ℕ → ComplexModel n → ℝ, (∀ i, r i ∈ convexHull ℝ (f '' Ici i)) ∧
      Tendsto (fun i => ∫ x in D, r i x ∂ν) atTop (𝓝 (∫ x in D, v x ∂ν)) := by
  classical
  set μ : Measure (ComplexModel n) := ν.restrict D with hμdef
  -- the tail suprema of the `L¹_loc` distances
  set e : ℕ → Set (ComplexModel n) → ℝ≥0∞ :=
    fun ℓ K => ⨆ j, ⨆ (_ : ℓ ≤ j), ∫⁻ x in K, ENNReal.ofReal |f j x - v x| with hedef
  have he : ∀ ℓ j, ℓ ≤ j → ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      ∫⁻ x in K, ENNReal.ofReal |f j x - v x| ≤ e ℓ K := fun ℓ j hj K _ _ =>
    le_iSup₂_of_le (f := fun j (_ : ℓ ≤ j) => ∫⁻ x in K, ENNReal.ofReal |f j x - v x|) j hj le_rfl
  have he0 : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun ℓ => e ℓ K) atTop (𝓝 0) := by
    intro K hK hKD
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp (hlim K hK hKD) ε hε
    exact ⟨N, fun ℓ hℓ => iSup₂_le fun j hj => hN j (hℓ.trans hj)⟩
  set C : ℕ → Set (ComplexModel n → ℝ) := fun ℓ => convexHull ℝ (f '' Ici ℓ) with hCdef
  have hCsub : ∀ ℓ k, ℓ ≤ k → C k ⊆ C ℓ := fun ℓ k h =>
    convexHull_mono (image_mono (Ici_subset_Ici.mpr h))
  have hprops : ∀ ℓ, ∀ r ∈ C ℓ, IsLocallyBoundedPshOn D r ∧ (∀ z ∈ D, |r z| ≤ L) ∧
      ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
        ∫⁻ x in K, ENNReal.ofReal |r x - v x| ≤ e ℓ K := fun ℓ =>
    convexHull_tail_props hf hL hv ℓ (e ℓ) (he ℓ)
  have hsqint : ∀ ℓ, ∀ r ∈ C ℓ, Integrable (fun x => r x ^ 2) μ := by
    intro ℓ r hr
    refine (integrable_const (L ^ 2)).mono'
      ((aemeasurable_of_isLocallyBoundedPshOn (hprops ℓ r hr).1 ν).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((hprops ℓ r hr).2.1 z hz) 2
  set Φ : (ComplexModel n → ℝ) → ℝ := fun r => ∫ x, r x ^ 2 ∂μ with hΦdef
  set d : ℕ → ℝ := fun ℓ => sInf (Φ '' C ℓ) with hddef
  have hfC : ∀ ℓ, f ℓ ∈ C ℓ := fun ℓ => subset_convexHull ℝ _ ⟨ℓ, self_mem_Ici, rfl⟩
  have hne : ∀ ℓ, (Φ '' C ℓ).Nonempty := fun ℓ => ⟨_, f ℓ, hfC ℓ, rfl⟩
  have hbdd : ∀ ℓ, BddBelow (Φ '' C ℓ) := fun ℓ =>
    ⟨0, by rintro _ ⟨r, -, rfl⟩; exact integral_nonneg fun x => sq_nonneg _⟩
  have hdle : ∀ ℓ, ∀ r ∈ C ℓ, d ℓ ≤ Φ r := fun ℓ r hr => csInf_le (hbdd ℓ) ⟨r, hr, rfl⟩
  have hdmono : Monotone d := monotone_nat_of_le_succ fun ℓ =>
    csInf_le_csInf (hbdd ℓ) (hne (ℓ + 1)) (image_mono (hCsub ℓ (ℓ + 1) (Nat.le_succ ℓ)))
  have hΦle : ∀ ℓ, ∀ r ∈ C ℓ, Φ r ≤ L ^ 2 * μ.real univ := by
    intro ℓ r hr
    have h := integral_mono_ae (hsqint ℓ r hr) (integrable_const (L ^ 2)) (by
      filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((hprops ℓ r hr).2.1 z hz) 2)
    rwa [integral_const, smul_eq_mul, mul_comm] at h
  have hdbdd : BddAbove (range d) :=
    ⟨L ^ 2 * μ.real univ, by rintro _ ⟨ℓ, rfl⟩; exact (hdle ℓ _ (hfC ℓ)).trans (hΦle ℓ _ (hfC ℓ))⟩
  set dl : ℝ := ⨆ ℓ, d ℓ with hdldef
  have hdl : Tendsto d atTop (𝓝 dl) := tendsto_atTop_ciSup hdmono hdbdd
  have hdle_lim : ∀ ℓ, d ℓ ≤ dl := fun ℓ => le_ciSup hdbdd ℓ
  -- almost minimizers
  have hex : ∀ ℓ, ∃ r ∈ C ℓ, Φ r < d ℓ + 1 / ((ℓ : ℝ) + 1) := fun ℓ => by
    obtain ⟨_, ⟨r, hr, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hne ℓ) (lt_add_of_pos_right (d ℓ) (by positivity : (0 : ℝ) < 1 / ((ℓ : ℝ) + 1)))
    exact ⟨r, hr, hlt⟩
  choose r hrC hrΦ using hex
  -- the parallelogram estimate
  have hpar : ∀ ℓ k, ℓ ≤ k → Φ (r k - r ℓ) ≤ 2 * (dl - d ℓ) + 4 / ((ℓ : ℝ) + 1) := by
    intro ℓ k hk
    have hrk : r k ∈ C ℓ := hCsub ℓ k hk (hrC k)
    set m : ComplexModel n → ℝ := (1 / 2 : ℝ) • r k + (1 / 2 : ℝ) • r ℓ with hmdef
    have hm : m ∈ C ℓ := (convex_convexHull ℝ _) hrk (hrC ℓ) (by norm_num) (by norm_num) (by norm_num)
    have hid : Φ (r k - r ℓ) = 2 * Φ (r k) + 2 * Φ (r ℓ) - 4 * Φ m := by
      calc Φ (r k - r ℓ) = ∫ x, (2 * r k x ^ 2 + 2 * r ℓ x ^ 2 - 4 * m x ^ 2) ∂μ := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            simp only [hmdef, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            ring
        _ = 2 * Φ (r k) + 2 * Φ (r ℓ) - 4 * Φ m := by
            have hI1 : Integrable (fun x => 2 * r k x ^ 2 + 2 * r ℓ x ^ 2) μ :=
              ((hsqint ℓ _ hrk).const_mul 2).add ((hsqint ℓ _ (hrC ℓ)).const_mul 2)
            rw [integral_sub hI1 ((hsqint ℓ _ hm).const_mul 4),
              integral_add ((hsqint ℓ _ hrk).const_mul 2) ((hsqint ℓ _ (hrC ℓ)).const_mul 2),
              integral_const_mul, integral_const_mul, integral_const_mul]
    have h1 : d ℓ ≤ Φ m := hdle ℓ m hm
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((ℓ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    have h3 : 4 / ((ℓ : ℝ) + 1) = 4 * (1 / ((ℓ : ℝ) + 1)) := by ring
    rw [hid, h3]
    linarith [hrΦ k, hrΦ ℓ, hdle_lim k]
  have hbound0 : Tendsto (fun ℓ : ℕ => 2 * (dl - d ℓ) + 4 / ((ℓ : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun ℓ : ℕ => 2 * (dl - d ℓ)) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := dl)).sub hdl).const_mul 2
    have h2 : Tendsto (fun ℓ : ℕ => 4 / ((ℓ : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    simpa using h1.add h2
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_eventually
    (P := fun i ℓ => 2 * (dl - d ℓ) + 4 / ((ℓ : ℝ) + 1) < (1 / 8 : ℝ) ^ i)
    fun i => (tendsto_order.1 hbound0).2 _ (by positivity)
  set ρ : ℕ → ComplexModel n → ℝ := fun i => r (φ i) with hρdef
  have hρC : ∀ i, ρ i ∈ C i := fun i => hCsub i (φ i) (hφ.id_le i) (hrC (φ i))
  have hρprops : ∀ i, IsLocallyBoundedPshOn D (ρ i) ∧ (∀ z ∈ D, |ρ i z| ≤ L) ∧
      ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
        ∫⁻ x in K, ENNReal.ofReal |ρ i x - v x| ≤ e (φ i) K := fun i =>
    hprops (φ i) (ρ i) (hrC (φ i))
  -- consecutive differences are small in `L²(μ)`
  have hdiff : ∀ i, Φ (ρ (i + 1) - ρ i) < (1 / 8 : ℝ) ^ i := fun i =>
    (hpar (φ i) (φ (i + 1)) (hφ.monotone (Nat.le_succ i))).trans_lt (hφP i)
  -- Borel–Cantelli
  set A : ℕ → Set (ComplexModel n) :=
    fun i => {x | (1 / 4 : ℝ) ^ i ≤ (ρ (i + 1) x - ρ i x) ^ 2} with hAdef
  have hA : ∀ i, μ (A i) ≤ (2⁻¹ : ℝ≥0∞) ^ i := by
    intro i
    have hsq : Integrable (fun x => (ρ (i + 1) x - ρ i x) ^ 2) μ := by
      refine (integrable_const ((2 * L) ^ 2)).mono'
        ((((aemeasurable_of_isLocallyBoundedPshOn (hρprops (i + 1)).1 ν).sub
          (aemeasurable_of_isLocallyBoundedPshOn (hρprops i).1 ν)).pow_const 2).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
      rw [Real.norm_eq_abs, abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |ρ (i + 1) z - ρ i z| ≤ |ρ (i + 1) z| + |ρ i z| := abs_sub _ _
        _ ≤ L + L := add_le_add ((hρprops (i + 1)).2.1 z hz) ((hρprops i).2.1 z hz)
        _ = 2 * L := by ring
    have hcheb := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun x => sq_nonneg (ρ (i + 1) x - ρ i x)) hsq ((1 / 4 : ℝ) ^ i)
    have hΦ : (∫ x, (ρ (i + 1) x - ρ i x) ^ 2 ∂μ) = Φ (ρ (i + 1) - ρ i) := rfl
    rw [hΦ] at hcheb
    have hreal : μ.real (A i) ≤ (1 / 2 : ℝ) ^ i := by
      have h4 : (0 : ℝ) < (1 / 4 : ℝ) ^ i := by positivity
      have h8 : (1 / 8 : ℝ) ^ i = (1 / 4 : ℝ) ^ i * (1 / 2 : ℝ) ^ i := by
        rw [← mul_pow]; norm_num
      have := hcheb.trans (hdiff i).le
      rw [h8] at this
      exact le_of_mul_le_mul_left this h4
    calc μ (A i) = ENNReal.ofReal (μ.real (A i)) := (ofReal_measureReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ i) := ENNReal.ofReal_le_ofReal hreal
      _ = (2⁻¹ : ℝ≥0∞) ^ i := by
          rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
  have hsum : ∑' i, μ (A i) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hA)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hev := ae_eventually_notMem hsum
  -- `ρ` converges `μ`-almost everywhere
  have hcauchy : ∀ᵐ x ∂μ, ∃ y, Tendsto (fun i => ρ i x) atTop (𝓝 y) := by
    filter_upwards [hev] with x hx
    have hsumm : Summable fun i => dist (ρ i x) (ρ i.succ x) := by
      refine Summable.of_norm_bounded_eventually (g := fun i : ℕ => (1 / 2 : ℝ) ^ i)
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [hx] with i hi
      have hlt : (ρ (i + 1) x - ρ i x) ^ 2 < ((1 / 2 : ℝ) ^ i) ^ 2 := by
        have : ¬ (1 / 4 : ℝ) ^ i ≤ (ρ (i + 1) x - ρ i x) ^ 2 := hi
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num at this ⊢
        exact this
      rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Real.dist_eq, abs_sub_comm]
      exact (abs_lt_of_sq_lt_sq hlt (by positivity)).le
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsumm)
  -- the limit is `v` (Step 1 and Hartogs' lemma)
  have hρlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun i => ∫⁻ x in K, ENNReal.ofReal |ρ i x - v x|) atTop (𝓝 0) := fun K hK hKD =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((he0 K hK hKD).comp hφ.tendsto_atTop) (fun _ => bot_le)
      fun i => (hρprops i).2.2 K hK hKD
  have hstep1 := ae_frequently_lt_of_localL1 (fun i => (hρprops i).1) hv (fun i => (hρprops i).2.1)
    hρlim hν
  have hlimv : ∀ᵐ x ∂μ, Tendsto (fun i => ρ i x) atTop (𝓝 (v x)) := by
    filter_upwards [hcauchy, hstep1, ae_restrict_mem D.isOpen.measurableSet] with x hx hfreq hxD
    obtain ⟨y, hy⟩ := hx
    have hyle : y ≤ v x := by
      refine le_of_forall_pos_le_add fun δ hδ => le_of_tendsto hy ?_
      exact (eventually_lt_add_of_localL1 (fun i => (hρprops i).1) hv hρlim hxD hδ).mono
        fun i hi => hi.le
    have hley : v x ≤ y := by
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      obtain ⟨N, hN⟩ := eventually_atTop.mp
        ((tendsto_order.1 hy).2 (y + δ / 2) (by linarith))
      obtain ⟨i, hi, hvi⟩ := hfreq N (δ / 2) (by positivity)
      linarith [hN i hi]
    rwa [le_antisymm hyle hley] at hy
  refine ⟨ρ, hρC, ?_⟩
  exact tendsto_integral_of_dominated_convergence (fun _ => L)
    (fun i => (aemeasurable_of_isLocallyBoundedPshOn (hρprops i).1 ν).aestronglyMeasurable)
    (integrable_const L)
    (fun i => by
      filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
      exact (hρprops i).2.1 z hz)
    hlimv

/-! ### Step 3: conclusion -/

/-- The `L¹_loc` limit keeps the bound `|v| ≤ L` everywhere on `D` (FPT, first paragraph of the
proof of `lem:bounded-psh-fixed-measure-continuity`). -/
theorem abs_le_of_localL1 {D : Opens (ComplexModel n)} {f : ℕ → ComplexModel n → ℝ}
    {v : ComplexModel n → ℝ} (hf : ∀ j, IsLocallyBoundedPshOn D (f j))
    (hv : IsLocallyBoundedPshOn D v) {L : ℝ} (hL : ∀ j, ∀ z ∈ D, |f j z| ≤ L)
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun j => ∫⁻ x in K, ENNReal.ofReal |f j x - v x|) atTop (𝓝 0)) :
    ∀ z ∈ D, |v z| ≤ L := by
  intro z hz
  refine abs_le.mpr ⟨?_, ?_⟩
  · refine le_of_forall_pos_lt_add fun δ hδ => ?_
    obtain ⟨j, hj⟩ := (eventually_lt_add_of_localL1 hf hv hlim hz hδ).exists
    linarith [(abs_le.mp (hL j z hz)).1]
  · have hae := ae_le_of_localL1 (aemeasurable_of_isLocallyBoundedPshOn hv volume)
      aemeasurable_const hlim (W := fun _ => L) (ℓ := 0) fun j _ y hy => (abs_le.mp (hL j y hy)).2
    have h := hv.1.le_of_ae_le D.isOpen
      (UpperSemicontinuous.upperSemicontinuousOn
        (f := fun _ : ComplexModel n => ((L : ℝ) : EReal)) upperSemicontinuous_const _) volume
      (hae.mono fun y hy => EReal.coe_le_coe_iff.mpr hy) z hz
    exact EReal.coe_le_coe_iff.mp h

/-- **FPT `lem:bounded-psh-fixed-measure-continuity`**: if plurisubharmonic `v_j` with
`|v_j| ≤ L` converge in `L¹_loc(D)` to the plurisubharmonic `v`, and the finite measure `ν` does
not charge sets of capacity zero (in particular if `ν ≤ (ddᶜw)ⁿ` for a bounded plurisubharmonic
`w`, `capacityNull_of_le_ma`), then `∫_D |v_j - v| dν → 0`. -/
theorem tendsto_integral_abs_sub_of_localL1 {D : Opens (ComplexModel n)}
    {f : ℕ → ComplexModel n → ℝ} {v : ComplexModel n → ℝ}
    (hf : ∀ j, IsLocallyBoundedPshOn D (f j)) (hv : IsLocallyBoundedPshOn D v) {L : ℝ}
    (hL : ∀ j, ∀ z ∈ D, |f j z| ≤ L)
    (hlim : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ D →
      Tendsto (fun j => ∫⁻ x in K, ENNReal.ofReal |f j x - v x|) atTop (𝓝 0))
    {ν : Measure (ComplexModel n)} [IsFiniteMeasure ν] (hν : CapacityNull D ν) :
    Tendsto (fun j => ∫ x in D, |f j x - v x| ∂ν) atTop (𝓝 0) := by
  set μ : Measure (ComplexModel n) := ν.restrict D with hμdef
  have hvL := abs_le_of_localL1 hf hv hL hlim
  have hfi : ∀ j, Integrable (f j) μ := fun j => integrable_of_isLocallyBoundedPshOn (hf j) (hL j)
  have hvi : Integrable v μ := integrable_of_isLocallyBoundedPshOn hv hvL
  have hpi : ∀ j, Integrable (fun x => max (f j x - v x) 0) μ := fun j => ((hfi j).sub hvi).pos_part
  -- the positive parts
  have hpos : Tendsto (fun j => ∫ x, max (f j x - v x) 0 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun j x => max (f j x - v x) 0) (f := fun _ => (0 : ℝ)) (fun _ => 2 * L)
      (fun j => (hpi j).aestronglyMeasurable) (integrable_const _)
      (fun j => by
        filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        refine max_le ?_ (by linarith [(abs_nonneg (v z)).trans (hvL z hz)])
        linarith [(abs_le.mp (hL j z hz)).2, (abs_le.mp (hvL z hz)).1])
      (by
        filter_upwards [ae_restrict_mem D.isOpen.measurableSet] with z hz
        refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun j =>
          ha.trans_le (le_max_right _ _), fun a ha => ?_⟩
        filter_upwards [eventually_lt_add_of_localL1 hf hv hlim hz ha] with j hj
        exact max_lt (by linarith) ha)
    simpa using h
  -- the lower bound for the integrals, from Step 2
  have hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∫ x, v x ∂μ - ε < ∫ x, f j x ∂μ := by
    intro ε hε
    by_contra hcon
    obtain ⟨ψ, hψ, hψle⟩ := extraction_of_frequently_atTop (not_eventually.mp hcon)
    obtain ⟨r, hr, hrlim⟩ := exists_convexHull_tendsto_integral (f := fun k => f (ψ k))
      (fun k => hf (ψ k)) hv (fun k => hL (ψ k))
      (fun K hK hKD => (hlim K hK hKD).comp hψ.tendsto_atTop) hν
    have hT : ∀ i, ∫ x, r i x ∂μ ≤ ∫ x, v x ∂μ - ε := by
      intro i
      have hsub : convexHull ℝ ((fun k => f (ψ k)) '' Ici i) ⊆
          {g | Integrable g μ ∧ ∫ x, g x ∂μ ≤ ∫ x, v x ∂μ - ε} := by
        refine convexHull_min ?_ ?_
        · rintro _ ⟨k, -, rfl⟩
          exact ⟨hfi (ψ k), le_of_not_gt (hψle k)⟩
        · intro g hg h hh a b ha hb hab
          refine ⟨(hg.1.smul a).add (hh.1.smul b), ?_⟩
          have hsplit : ∫ x, (a • g + b • h) x ∂μ = a * ∫ x, g x ∂μ + b * ∫ x, h x ∂μ := by
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [integral_add (hg.1.const_mul a) (hh.1.const_mul b), integral_const_mul,
              integral_const_mul]
          rw [hsplit]
          calc a * ∫ x, g x ∂μ + b * ∫ x, h x ∂μ ≤
                a * (∫ x, v x ∂μ - ε) + b * (∫ x, v x ∂μ - ε) :=
              add_le_add (mul_le_mul_of_nonneg_left hg.2 ha) (mul_le_mul_of_nonneg_left hh.2 hb)
            _ = ∫ x, v x ∂μ - ε := by rw [← add_mul, hab, one_mul]
      exact (hsub (hr i)).2
    have h2 : ∫ x, v x ∂μ ≤ ∫ x, v x ∂μ - ε := le_of_tendsto' hrlim hT
    linarith
  -- convergence of the integrals
  have hint : Tendsto (fun j => ∫ x, f j x ∂μ) atTop (𝓝 (∫ x, v x ∂μ)) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [hlow (∫ x, v x ∂μ - a) (by linarith)] with j hj
      linarith
    · filter_upwards [(tendsto_order.1 hpos).2 (a - ∫ x, v x ∂μ) (by linarith)] with j hj
      have h1 : ∫ x, f j x ∂μ - ∫ x, v x ∂μ ≤ ∫ x, max (f j x - v x) 0 ∂μ := by
        rw [← integral_sub (hfi j) hvi]
        exact integral_mono ((hfi j).sub hvi) (hpi j) fun x => le_max_left _ _
      linarith
  have hid : ∀ j, ∫ x, |f j x - v x| ∂μ =
      2 * ∫ x, max (f j x - v x) 0 ∂μ - (∫ x, f j x ∂μ - ∫ x, v x ∂μ) := by
    intro j
    have hd : Integrable (fun x => f j x - v x) μ := (hfi j).sub hvi
    have h2 : Integrable (fun x => 2 * max (f j x - v x) 0) μ := (hpi j).const_mul 2
    calc ∫ x, |f j x - v x| ∂μ = ∫ x, (2 * max (f j x - v x) 0 - (f j x - v x)) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          rcases le_total 0 (f j x - v x) with h0 | h0
          · simp only [abs_of_nonneg h0, max_eq_left h0]; ring
          · simp only [abs_of_nonpos h0, max_eq_right h0]; ring
      _ = 2 * ∫ x, max (f j x - v x) 0 ∂μ - ∫ x, (f j x - v x) ∂μ := by
          rw [integral_sub h2 hd, integral_const_mul]
      _ = _ := by rw [integral_sub (hfi j) hvi]
  simp only [hid]
  simpa using (hpos.const_mul 2).sub (hint.sub_const (∫ x, v x ∂μ))

end SGPT.Envelopes.MADirichlet
