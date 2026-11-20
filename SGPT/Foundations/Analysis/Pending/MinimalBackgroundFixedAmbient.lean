import SGPT.Foundations.Analysis.Pending.EndpointMixedMassGeneralConvexCombination
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone
import SGPT.Foundations.Analysis.Pending.MixedSummandCapacityDomination
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.MinimalBackgroundFixedAmbient

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open RelativeEnergy GlobalNonPluripolar GlobalDiagonalScaling GlobalMultilinearExpansion
open MixedMass MixedMassProductCalculus ThetaPshConvexCombination
open EndpointMixedMassConvexCombination EndpointMixedMassGeneralConvexCombination
open GlobalMixedMassMonotone SingularMinimalCanonicalRay MixedSummandCapacityDomination
open SingularCanonicalSingularityDistance SingularCanonicalSingularityMassComparison ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- An actual independent-slot positive selector, obtained from the complete
mixed-mass expansion. No target mixed-mass inequality is supplied. -/
theorem mixedMass_convexComb_first_lower (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M} {u v : Fin n → M → EReal}
    (hu : ∀ k, IsThetaPshPotential (θ k).val (u k))
    (hv : ∀ k, IsThetaPshPotential (θ k).val (v k))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ n * (globalMixedMass θ u (fun k => (hu k).1)).toReal ≤
      (globalMixedMass θ (fun k => convexComb s (u k) (v k))
        (fun k => (isThetaPshPotential_convexComb_closed
          (hu k) (hv k) hs0 hs1).1)).toReal := by
  classical
  let c : Fin n → Fin n × Bool → ℝ := fun k b =>
    if b.1 = k then (if b.2 then s else 1 - s) else 0
  let α : Fin n × Bool → ClosedRealOneOneForm n M := fun b => θ b.1
  let pots : Fin n × Bool → M → EReal := fun b => if b.2 then u b.1 else v b.1
  have hpots (b : Fin n × Bool) : IsThetaPshPotential (α b).val (pots b) := by
    dsimp [α, pots]
    split_ifs <;> first | exact hu _ | exact hv _
  have hc (k : Fin n) (b : Fin n × Bool) : 0 ≤ c k b := by
    dsimp [c]
    split_ifs <;> first | exact hs0 | exact sub_nonneg.mpr hs1 | exact le_rfl
  have hF : (fun k => sumForm Finset.univ (c k) α) = θ := by
    funext k
    simp [sumForm, Fintype.sum_prod_type, c, α,
      ← add_smul, show s + (1 - s) = 1 by ring]
  have hQ : (fun k => sumPot Finset.univ (c k) pots) =
      fun k => convexComb s (u k) (v k) := by
    funext k x
    simp [sumPot, Fintype.sum_prod_type, c, pots, apply_ite, ite_mul, convexComb]
  have h := globalMixedMass_sumPot_expand_toReal omega hc hpots
  unfold globalMixedMass at h
  rw [globalMixedMeasure_congr hF hQ _
    (fun k => (isThetaPshPotential_convexComb_closed (hu k) (hv k) hs0 hs1).1)] at h
  let g₀ : Fin n → Fin n × Bool := fun k => (k, true)
  have hterm : (∏ k, c k (g₀ k)) *
      (globalMixedMass (fun k => α (g₀ k)) (fun k => pots (g₀ k))
        (fun k => (hpots (g₀ k)).1)).toReal =
      s ^ n * (globalMixedMass θ u (fun k => (hu k).1)).toReal := by
    simp [c, α, pots, g₀]
  have hsingle : (∏ k, c k (g₀ k)) *
      (globalMixedMass (fun k => α (g₀ k)) (fun k => pots (g₀ k))
        (fun k => (hpots (g₀ k)).1)).toReal ≤
      ∑ g : Fin n → Fin n × Bool, (∏ k, c k (g k)) *
        (globalMixedMass (fun k => α (g k)) (fun k => pots (g k))
          (fun k => (hpots (g k)).1)).toReal := by
    exact Finset.single_le_sum
      (f := fun g : Fin n → Fin n × Bool => (∏ k, c k (g k)) *
        (globalMixedMass (fun k => α (g k)) (fun k => pots (g k))
          (fun k => (hpots (g k)).1)).toReal)
      (fun g _ => mul_nonneg (Finset.prod_nonneg fun k _ => hc k (g k))
        ENNReal.toReal_nonneg) (Finset.mem_univ g₀)
  rw [hterm] at hsingle
  exact hsingle.trans_eq h.symm

/-- Fixed-reference endpoint masses retain their all-first positive term.
The power n is sufficient for the fixed-ambient squeeze, including n=0. -/
theorem endpointMixedMass_convexComb_first_lower (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u v p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hp : IsThetaPshPotential θ.val p)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (j : Fin (n + 1)) :
    s ^ n * (endpointMixedMass θ p u hp hu j).toReal ≤
      (endpointMixedMass θ p (convexComb s u v) hp
        (isThetaPshPotential_convexComb_closed hu hv hs0.le hs1.le) j).toReal := by
  let U := endpointMixedPotential j u p
  let V := endpointMixedPotential j v p
  have hU (k : Fin n) : IsThetaPshPotential θ.val (U k) := by
    dsimp only [U, endpointMixedPotential]
    split_ifs <;> first | exact hu | exact hp
  have hV (k : Fin n) : IsThetaPshPotential θ.val (V k) := by
    dsimp only [V, endpointMixedPotential]
    split_ifs <;> first | exact hv | exact hp
  have htuple : (fun k => convexComb s (U k) (V k)) =
      endpointMixedPotential j (convexComb s u v) p := by
    funext k
    dsimp only [U, V, endpointMixedPotential]
    split_ifs
    · rfl
    · exact ThetaCapacity.convexComb_self hs0 hs1 p
  have h := mixedMass_convexComb_first_lower omega hU hV hs0.le hs1.le
  have hm := UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple htuple
    (fun k => (isThetaPshPotential_convexComb_closed (hU k) (hV k) hs0.le hs1.le).1)
    (endpointMixedPotential_thetaPlurisubharmonic θ j _ p
      (isThetaPshPotential_convexComb_closed hu hv hs0.le hs1.le) hp)
  have he := congrArg (fun μ : Measure M => (μ univ).toReal) hm
  exact h.trans_eq he

omit [MeasurableSpace M] [BorelSpace M] in
/-- The actual big current, smooth compact domination and Bott--Chern
transport supply a strict potential in the original representative. -/
theorem exists_normalized_strict_potential (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ψ : M → EReal,
      IsThetaPshPotential (θ - δ • omega.form).val ψ ∧ ψ ≤ 0 := by
  obtain ⟨T⟩ := hbig
  obtain ⟨A, hA, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul T.lowerBound (-omega.form)
  have hδ : 0 < A⁻¹ := inv_pos.mpr hA
  have hdiff : (T.lowerBound.form - A⁻¹ • omega.form).val.IsSemipositive := by
    have heq : T.lowerBound.form - A⁻¹ • omega.form =
        A⁻¹ • (-omega.form + A • T.lowerBound.form) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hA.ne', one_smul, smul_neg]
      abel
    rw [heq]
    intro e z hz
    exact coefficientSemipositive_smul hδ.le (hsemi e z hz)
  have hpsh := LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh hdiff
  have hform : T.representative - T.lowerBound.form +
      (T.lowerBound.form - A⁻¹ • omega.form) = T.representative - A⁻¹ • omega.form := by abel
  rw [hform] at hpsh
  have htrans := bigWithRespectToViaPotentials_of_bottChernRel omega
    ((RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents)
    (show BigWithRespectToViaPotentials omega T.representative from ⟨A⁻¹, hδ, T.potential, hpsh⟩)
  obtain ⟨δ, hδ, ψ₀, hψ₀⟩ := htrans
  by_cases hM : Nonempty M
  · let _ := hM
    obtain ⟨C, hC⟩ := hψ₀.exists_global_upper_bound
    exact ⟨δ, hδ, fun x => ψ₀ x - (C : EReal), hψ₀.sub_const C,
      sub_const_nonpositive_of_le hC⟩
  · exact ⟨δ, hδ, ψ₀, hψ₀, fun x => (hM ⟨x⟩).elim⟩

variable [ConnectedSpace M]

/-- The SAME strict potential makes a true θ-psh combination of every
positive-background minimal potential, bounded by the original Vθ. -/
theorem exists_minimal_add_convex_barrier (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ψ : M → EReal,
      IsThetaPshPotential (θ - δ • omega.form).val ψ ∧ ψ ≤ 0 ∧
      ∀ ε : ℝ, 0 < ε →
        IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form)) ∧
        IsThetaPshPotential θ.val
          (convexComb (δ / (δ + ε)) (thetaPshSupremum (θ + ε • omega.form).val) ψ) ∧
        convexComb (δ / (δ + ε)) (thetaPshSupremum (θ + ε • omega.form).val) ψ ≤
          thetaPshSupremum θ.val := by
  obtain ⟨δ, hδ, ψ, hψ, hψ0⟩ := exists_normalized_strict_potential omega θ hbig
  refine ⟨δ, hδ, ψ, hψ, hψ0, fun ε hε => ?_⟩
  have hplus : IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form)) := by
    refine ⟨{
      representative := θ + ε • omega.form
      represents := rfl
      potential := ψ
      lowerBound := KahlerBackground.smul (add_pos hδ hε) omega
      strictlyPsh := ?_ }⟩
    have he : θ + ε • omega.form - (δ + ε) • omega.form = θ - δ • omega.form := by module
    simpa only [KahlerBackground.smul_form, he] using hψ
  let s : ℝ := δ / (δ + ε)
  have hs0 : 0 < s := div_pos hδ (add_pos hδ hε)
  have hs1 : s < 1 := (div_lt_one (add_pos hδ hε)).mpr (by linarith)
  let α : Bool → ClosedRealOneOneForm n M :=
    fun b => if b then θ + ε • omega.form else θ - δ • omega.form
  let f : Bool → M → EReal :=
    fun b => if b then thetaPshSupremum (θ + ε • omega.form).val else ψ
  let w : Bool → ℝ := fun b => if b then s else 1 - s
  have hw (b : Bool) : 0 < w b := by
    cases b <;> simp only [w, Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hs0 | exact sub_pos.mpr hs1
  have hf (b : Bool) : IsThetaPshPotential (α b).val (f b) := by
    cases b
    · exact hψ
    · exact (isModelPotential_thetaPshSupremum omega (θ + ε • omega.form) hplus).plurisubharmonic
  have hcoeff : s * ε - (1 - s) * δ = 0 := by
    dsimp [s]
    field_simp
    ring
  have hα : sumForm Finset.univ w α = θ := by
    simp only [sumForm, Fintype.sum_bool]
    change s • (θ + ε • omega.form) + (1 - s) • (θ - δ • omega.form) = θ
    calc
      _ = (s + (1 - s)) • θ + (s * ε - (1 - s) * δ) • omega.form := by module
      _ = θ := by rw [hcoeff]; simp
  have hq := isThetaPshPotential_sumPot Finset.univ_nonempty hw hf
  rw [hα] at hq
  have hread : sumPot Finset.univ w f =
      convexComb s (thetaPshSupremum (θ + ε • omega.form).val) ψ := by
    funext x
    simp only [sumPot, Fintype.sum_bool, w, f, Bool.false_eq_true, ↓reduceIte, convexComb]
  rw [hread] at hq
  have hq0 : convexComb s (thetaPshSupremum (θ + ε • omega.form).val) ψ ≤ 0 := by
    intro x
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr hs0.le)
        (thetaPshSupremum_le_zero _ x))
      (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (sub_nonneg.mpr hs1.le))
        (hψ0 x))
  exact ⟨hplus, hq, le_thetaPshSupremum hq hq0⟩

omit [ConnectedSpace M] in
/-- Actual fixed-reference mixed-mass monotonicity follows slotwise from
the SAME original pointwise comparison. -/
theorem endpointMixedMass_toReal_mono (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u v p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (hp : IsThetaPshPotential θ.val p) (huv : u ≤ v) (j : Fin (n + 1)) :
    (endpointMixedMass θ p u hp hu j).toReal ≤
      (endpointMixedMass θ p v hp hv j).toReal := by
  have hU (k : Fin n) : IsThetaPshPotential θ.val (endpointMixedPotential j u p k) := by
    dsimp only [endpointMixedPotential]
    split_ifs <;> first | exact hu | exact hp
  have hV (k : Fin n) : IsThetaPshPotential θ.val (endpointMixedPotential j v p k) := by
    dsimp only [endpointMixedPotential]
    split_ifs <;> first | exact hv | exact hp
  have horder (k : Fin n) : MoreSingularOn (endpointMixedPotential j u p k)
      (endpointMixedPotential j v p k) univ := by
    apply MoreSingularOn.of_le
    intro x _
    dsimp only [endpointMixedPotential]
    split_ifs
    · exact huv x
    · exact le_rfl
  have h := globalMixedMass_mono_of_isThetaPshPotential omega hU hV horder
  exact ENNReal.toReal_mono (globalMixedMass_lt_top omega (fun k => (hV k).1)).ne h

/-- Internally produced strict geometry gives two exact endpoint-mass
bounds in the FIXED ambient θ+ω. This is stronger than a moving-background
distance estimate and does not assume any volume continuity. -/
theorem exists_fixedAmbient_positive_endpoint_bounds (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      ∃ _hplus : IsBigClass (RealBottChern.ofRepresentative (θ + ε • omega.form)),
      ∃ hE : IsThetaPshPotential (θ + omega.form).val
          (thetaPshSupremum (θ + ε • omega.form).val),
      ∃ h0 : IsThetaPshPotential (θ + omega.form).val (thetaPshSupremum θ.val),
      ∀ (p : M → EReal) (hp : IsThetaPshPotential (θ + omega.form).val p)
        (j : Fin (n + 1)),
        (endpointMixedMass (θ + omega.form) p (thetaPshSupremum θ.val) hp h0 j).toReal ≤
          (endpointMixedMass (θ + omega.form) p
            (thetaPshSupremum (θ + ε • omega.form).val) hp hE j).toReal ∧
        (δ / (δ + ε)) ^ n * (endpointMixedMass (θ + omega.form) p
            (thetaPshSupremum (θ + ε • omega.form).val) hp hE j).toReal ≤
          (endpointMixedMass (θ + omega.form) p (thetaPshSupremum θ.val) hp h0 j).toReal := by
  obtain ⟨δ, hδ, ψ, hψ, _hψ0, hbar⟩ := exists_minimal_add_convex_barrier omega θ hbig
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  obtain ⟨hplus, _hq, hqle⟩ := hbar ε hε.1
  have hV := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have h0 : IsThetaPshPotential (θ + omega.form).val (thetaPshSupremum θ.val) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hV omega.isSemipositive
  have hE : IsThetaPshPotential (θ + omega.form).val
      (thetaPshSupremum (θ + ε • omega.form).val) := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive
      (isModelPotential_thetaPshSupremum omega (θ + ε • omega.form) hplus).plurisubharmonic
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hε.2.le))
    have he : θ + ε • omega.form + (1 - ε) • omega.form = θ + omega.form := by module
    simpa only [he] using h
  have hψA : IsThetaPshPotential (θ + omega.form).val ψ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hψ
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (by positivity : 0 ≤ δ + 1))
    have he : θ - δ • omega.form + (δ + 1) • omega.form = θ + omega.form := by module
    simpa only [he] using h
  have hVplus := LocalPotentials.isThetaPshPotential_add_of_semipositive hV
    (KahlerDomination.isSemipositive_smul omega.isSemipositive hε.1.le)
  have hVle : thetaPshSupremum θ.val ≤ thetaPshSupremum (θ + ε • omega.form).val :=
    le_thetaPshSupremum hVplus (thetaPshSupremum_le_zero θ.val)
  refine ⟨hplus, hE, h0, fun p hp j => ⟨?_, ?_⟩⟩
  · exact endpointMixedMass_toReal_mono omega h0 hE hp hVle j
  · have hs0 : 0 < δ / (δ + ε) := div_pos hδ (add_pos hδ hε.1)
    have hs1 : δ / (δ + ε) < 1 := (div_lt_one (add_pos hδ hε.1)).mpr (by linarith [hε.1])
    have hsel := endpointMixedMass_convexComb_first_lower omega hE hψA hp hs0 hs1 j
    exact hsel.trans (endpointMixedMass_toReal_mono omega
      (isThetaPshPotential_convexComb_closed hE hψA hs0.le hs1.le) h0 hp hqle j)

/-- The fixed ambient endpoint mass converges by an actual scalar squeeze.
Both original PSH memberships are produced before forming the mass readers. -/
theorem exists_tendsto_fixedAmbient_positive_endpoint_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (ε : I → Ioo (0 : ℝ) 1)
    (hε : Tendsto (fun i => (ε i).val) F (𝓝 0)) :
    ∃ h0 : IsThetaPshPotential (θ + omega.form).val (thetaPshSupremum θ.val),
    ∃ hE : ∀ i, IsThetaPshPotential (θ + omega.form).val
        (thetaPshSupremum (θ + (ε i).val • omega.form).val),
    ∀ (p : M → EReal) (hp : IsThetaPshPotential (θ + omega.form).val p)
      (j : Fin (n + 1)),
      Tendsto (fun i => (endpointMixedMass (θ + omega.form) p
        (thetaPshSupremum (θ + (ε i).val • omega.form).val) hp (hE i) j).toReal) F
        (𝓝 (endpointMixedMass (θ + omega.form) p (thetaPshSupremum θ.val) hp h0 j).toReal) := by
  obtain ⟨δ, hδ, hbound⟩ := exists_fixedAmbient_positive_endpoint_bounds omega θ hbig
  let hB (i : I) := hbound (ε i).val (ε i).property
  let hE (i : I) := (hB i).choose_spec.choose
  have h0 := LocalPotentials.isThetaPshPotential_add_of_semipositive
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic omega.isSemipositive
  refine ⟨h0, hE, fun p hp j => ?_⟩
  let m0 := (endpointMixedMass (θ + omega.form) p (thetaPshSupremum θ.val) hp h0 j).toReal
  let m (i : I) := (endpointMixedMass (θ + omega.form) p
    (thetaPshSupremum (θ + (ε i).val • omega.form).val) hp (hE i) j).toReal
  have hm (i : I) : m0 ≤ m i ∧ (δ / (δ + (ε i).val)) ^ n * m i ≤ m0 :=
    (hB i).choose_spec.choose_spec.choose_spec p hp j
  have hδlim : Tendsto (fun _ : I => δ) F (𝓝 δ) := tendsto_const_nhds
  have hdenlim : Tendsto (fun i => δ + (ε i).val) F (𝓝 δ) := by
    simpa only [add_zero] using hδlim.add hε
  have hs : Tendsto (fun i => δ / (δ + (ε i).val)) F (𝓝 (1 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_inv_cancel₀ hδ.ne'] using
      hδlim.mul (hdenlim.inv₀ hδ.ne')
  have hupper : Tendsto (fun i => m0 / ((δ / (δ + (ε i).val)) ^ n)) F (𝓝 m0) := by
    simpa only [div_eq_mul_inv, one_pow, inv_one, mul_one] using
      ((hs.pow n).inv₀ (by simp)).const_mul m0
  have hle (i : I) : m i ≤ m0 / ((δ / (δ + (ε i).val)) ^ n) := by
    have hpos : 0 < (δ / (δ + (ε i).val)) ^ n :=
      pow_pos (div_pos hδ (add_pos hδ (ε i).property.1)) n
    exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using (hm i).2)
  have hdiff : Tendsto (fun i => m i - m0) F (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun i => sub_nonneg.mpr (hm i).1)
      (fun i => sub_le_sub_right (hle i) m0)
      (by simpa only [sub_self] using hupper.sub_const m0)
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const m0

/-- The actual positive-background minimal potentials converge in the
FIXED θ+ω metric. All common-ambient PSH membership and bigness are outputs. -/
theorem exists_tendsto_fixedAmbient_positive_minimal
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (ε : I → Ioo (0 : ℝ) 1)
    (hε : Tendsto (fun i => (ε i).val) F (𝓝 0)) :
    ∃ hA : IsBigClass (RealBottChern.ofRepresentative (θ + omega.form)),
    ∃ h0 : IsThetaPshPotential (θ + omega.form).val (thetaPshSupremum θ.val),
    ∃ hE : ∀ i, IsThetaPshPotential (θ + omega.form).val
        (thetaPshSupremum (θ + (ε i).val • omega.form).val),
      Tendsto (fun i => (⟨thetaPshSupremum (θ + (ε i).val • omega.form).val,
        hE i⟩ : ThetaPshL1 (θ + omega.form).val)) F
        (@nhds (ThetaPshL1 (θ + omega.form).val)
          (singularityPseudoMetricSpace omega (θ + omega.form) hA).toUniformSpace.toTopologicalSpace
          ⟨thetaPshSupremum θ.val, h0⟩) := by
  have hA : IsBigClass (RealBottChern.ofRepresentative (θ + omega.form)) := by
    obtain ⟨δ, hδ, ψ, hψ, _⟩ := exists_normalized_strict_potential omega θ hbig
    refine ⟨{
      representative := θ + omega.form
      represents := rfl
      potential := ψ
      lowerBound := KahlerBackground.smul (by positivity : 0 < δ + 1) omega
      strictlyPsh := ?_ }⟩
    have he : θ + omega.form - (δ + 1) • omega.form = θ - δ • omega.form := by module
    simpa only [KahlerBackground.smul_form, he] using hψ
  obtain ⟨h0, hE, hmass⟩ := exists_tendsto_fixedAmbient_positive_endpoint_mass omega θ hbig F ε hε
  refine ⟨hA, h0, hE, ?_⟩
  let W : I → ThetaPshL1 (θ + omega.form).val := fun i =>
    ⟨thetaPshSupremum (θ + (ε i).val • omega.form).val, hE i⟩
  let _nativeMetric : PseudoMetricSpace (ThetaPshL1 (θ + omega.form).val) :=
    singularityPseudoMetricSpace omega (θ + omega.form) hA
  let _nativeTopology : TopologicalSpace (ThetaPshL1 (θ + omega.form).val) :=
    (singularityPseudoMetricSpace omega (θ + omega.form) hA).toUniformSpace.toTopologicalSpace
  have hVle (i : I) : thetaPshSupremum θ.val ≤ (W i).val := by
    have hVplus := LocalPotentials.isThetaPshPotential_add_of_semipositive
      (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (ε i).property.1.le)
    exact le_thetaPshSupremum hVplus (thetaPshSupremum_le_zero θ.val)
  have hmax (i : I) : (fun x => max ((W i).val x) (thetaPshSupremum θ.val x)) =
      (W i).val := funext fun x => max_eq_left (hVle i x)
  have hR := (isModelPotential_thetaPshSupremum omega (θ + omega.form) hA).plurisubharmonic
  have hreal : Tendsto (fun i => (singularityDistance omega (θ + omega.form) hA
      (W i).val (thetaPshSupremum θ.val)).toReal) F (𝓝 (0 : ℝ)) := by
    apply (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega
      (θ + omega.form) hA F (fun i => (W i).property) h0).mpr
    intro j
    refine ⟨hmass (thetaPshSupremum (θ + omega.form).val) hR j, ?_⟩
    simpa only [hmax] using hmass (thetaPshSupremum (θ + omega.form).val) hR j
  have hdist : Tendsto (fun i => dist (W i)
      (⟨thetaPshSupremum θ.val, h0⟩ : ThetaPshL1 (θ + omega.form).val)) F
      (𝓝 (0 : ℝ)) := hreal.congr' (Eventually.of_forall fun i =>
        (dist_eq_singularityDistance_toReal omega (θ + omega.form) hA (W i)
          ⟨thetaPshSupremum θ.val, h0⟩).symm)
  change Tendsto W F (𝓝 (⟨thetaPshSupremum θ.val, h0⟩ : ThetaPshL1 (θ + omega.form).val))
  exact tendsto_iff_dist_tendsto_zero.mpr hdist

/-- Genuine smaller-class minimal potentials are squeezed above an actual
convex strict-potential barrier and below the same original Vθ. -/
theorem exists_minimal_sub_convex_barrier (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ψ : M → EReal,
      IsThetaPshPotential (θ - δ • omega.form).val ψ ∧ ψ ≤ 0 ∧
      ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) δ →
        IsBigClass (RealBottChern.ofRepresentative (θ - ε • omega.form)) ∧
        IsThetaPshPotential θ.val (thetaPshSupremum (θ - ε • omega.form).val) ∧
        convexComb (ε / δ) ψ (thetaPshSupremum θ.val) ≤
          thetaPshSupremum (θ - ε • omega.form).val ∧
        thetaPshSupremum (θ - ε • omega.form).val ≤ thetaPshSupremum θ.val := by
  obtain ⟨δ, hδ, ψ, hψ, hψ0⟩ := exists_normalized_strict_potential omega θ hbig
  have hψθ : IsThetaPshPotential θ.val ψ := by
    simpa only [sub_add_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      hψ (KahlerDomination.isSemipositive_smul omega.isSemipositive hδ.le)
  have hV := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  refine ⟨δ, hδ, ψ, hψ, hψ0, fun ε hε => ?_⟩
  have ha0 : 0 < ε / δ := div_pos hε.1 hδ
  have ha1 : ε / δ < 1 := (div_lt_one hδ).mpr hε.2
  have hsmall : IsBigClass (RealBottChern.ofRepresentative (θ - ε • omega.form)) := by
    refine ⟨{
      representative := θ - ε • omega.form
      represents := rfl
      potential := ψ
      lowerBound := KahlerBackground.smul (sub_pos.mpr hε.2) omega
      strictlyPsh := ?_ }⟩
    have he : θ - ε • omega.form - (δ - ε) • omega.form = θ - δ • omega.form := by module
    simpa only [KahlerBackground.smul_form, he] using hψ
  have hsmallV := (isModelPotential_thetaPshSupremum omega
    (θ - ε • omega.form) hsmall).plurisubharmonic
  have hE : IsThetaPshPotential θ.val (thetaPshSupremum (θ - ε • omega.form).val) := by
    simpa only [sub_add_cancel] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      hsmallV (KahlerDomination.isSemipositive_smul omega.isSemipositive hε.1.le)
  have hqθ := isThetaPshPotential_convexComb_closed hψθ hV ha0.le ha1.le
  have hqsmall : IsThetaPshPotential (θ - ε • omega.form).val
      (convexComb (ε / δ) ψ (thetaPshSupremum θ.val)) := by
    refine ⟨?_, hqθ.2⟩
    have h := GlobalDiagonalScaling.thetaPlurisubharmonic_add_smul ha0 (sub_pos.mpr ha1)
      hψ.1 hV.1
    have he : (ε / δ) • (θ - δ • omega.form) + (1 - ε / δ) • θ =
        θ - ε • omega.form := by
      rw [smul_sub, smul_smul, div_mul_cancel₀ ε hδ.ne']
      module
    rw [he] at h
    exact h
  have hq0 : convexComb (ε / δ) ψ (thetaPshSupremum θ.val) ≤ 0 := by
    intro x
    exact add_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr ha0.le) (hψ0 x))
      (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (sub_nonneg.mpr ha1.le))
        (thetaPshSupremum_le_zero θ.val x))
  exact ⟨hsmall, hE, le_thetaPshSupremum hqsmall hq0,
    le_thetaPshSupremum hE (thetaPshSupremum_le_zero _)⟩

/-- Both-sided work uses the SAME fixed θ+ω background. The negative-side
limit here is supplied by actual barrier masses and no continuity certificate. -/
theorem exists_tendsto_fixedAmbient_negative_minimal
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {I : Type*} (F : Filter I) (ε : I → Ioo (0 : ℝ) δ),
      Tendsto (fun i => (ε i).val) F (𝓝 0) →
      ∃ hA : IsBigClass (RealBottChern.ofRepresentative (θ + omega.form)),
      ∃ h0 : IsThetaPshPotential (θ + omega.form).val (thetaPshSupremum θ.val),
      ∃ hE : ∀ i, IsThetaPshPotential (θ + omega.form).val
          (thetaPshSupremum (θ - (ε i).val • omega.form).val),
      ∃ _hsmall : ∀ i, IsBigClass (RealBottChern.ofRepresentative (θ - (ε i).val • omega.form)),
        Tendsto (fun i => (⟨thetaPshSupremum (θ - (ε i).val • omega.form).val,
          hE i⟩ : ThetaPshL1 (θ + omega.form).val)) F
          (@nhds (ThetaPshL1 (θ + omega.form).val)
            (singularityPseudoMetricSpace omega (θ + omega.form) hA).toUniformSpace.toTopologicalSpace
            ⟨thetaPshSupremum θ.val, h0⟩) := by
  obtain ⟨δ, hδ, ψ, hψ, _hψ0, hbar⟩ := exists_minimal_sub_convex_barrier omega θ hbig
  refine ⟨δ, hδ, fun {I} F ε hε => ?_⟩
  have hA : IsBigClass (RealBottChern.ofRepresentative (θ + omega.form)) := by
    refine ⟨{
      representative := θ + omega.form
      represents := rfl
      potential := ψ
      lowerBound := KahlerBackground.smul (by positivity : 0 < δ + 1) omega
      strictlyPsh := ?_ }⟩
    have he : θ + omega.form - (δ + 1) • omega.form = θ - δ • omega.form := by module
    simpa only [KahlerBackground.smul_form, he] using hψ
  have hV := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have h0 := LocalPotentials.isThetaPshPotential_add_of_semipositive hV omega.isSemipositive
  have hE (i : I) := LocalPotentials.isThetaPshPotential_add_of_semipositive
    (hbar (ε i).val (ε i).property).2.1 omega.isSemipositive
  have hsmall (i : I) := (hbar (ε i).val (ε i).property).1
  refine ⟨hA, h0, hE, hsmall, ?_⟩
  have hψA : IsThetaPshPotential (θ + omega.form).val ψ := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hψ
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (by positivity : 0 ≤ δ + 1))
    have he : θ - δ • omega.form + (δ + 1) • omega.form = θ + omega.form := by module
    simpa only [he] using h
  let t : I → Ioo (0 : ℝ) 1 := fun i =>
    ⟨(ε i).val / δ, div_pos (ε i).property.1 hδ, (div_lt_one hδ).mpr (ε i).property.2⟩
  have ht : Tendsto (fun i => (t i).val) F (𝓝 0) := by
    simpa only [zero_div] using hε.div_const δ
  let W : I → ThetaPshL1 (θ + omega.form).val := fun i =>
    ⟨thetaPshSupremum (θ - (ε i).val • omega.form).val, hE i⟩
  let _nativeMetric : PseudoMetricSpace (ThetaPshL1 (θ + omega.form).val) :=
    singularityPseudoMetricSpace omega (θ + omega.form) hA
  let _nativeTopology : TopologicalSpace (ThetaPshL1 (θ + omega.form).val) :=
    (singularityPseudoMetricSpace omega (θ + omega.form) hA).toUniformSpace.toTopologicalSpace
  have hR := (isModelPotential_thetaPshSupremum omega (θ + omega.form) hA).plurisubharmonic
  have hmass (j : Fin (n + 1)) :
      Tendsto (fun i => (endpointMixedMass (θ + omega.form)
        (thetaPshSupremum (θ + omega.form).val) (W i).val hR (W i).property j).toReal) F
        (𝓝 (endpointMixedMass (θ + omega.form)
          (thetaPshSupremum (θ + omega.form).val) (thetaPshSupremum θ.val) hR h0 j).toReal) := by
    let R := thetaPshSupremum (θ + omega.form).val
    let m0 := (endpointMixedMass (θ + omega.form) R (thetaPshSupremum θ.val) hR h0 j).toReal
    let m (i : I) := (endpointMixedMass (θ + omega.form) R (W i).val hR (W i).property j).toReal
    have hlow := tendsto_toReal_endpointMixedMass_general_convexComb_zero omega hψA h0 hR F t ht j
    have hle (i : I) : m i ≤ m0 := endpointMixedMass_toReal_mono omega
      (W i).property h0 hR (hbar (ε i).val (ε i).property).2.2.2 j
    have hge (i : I) : (endpointMixedMass (θ + omega.form) R
        (convexComb (t i).val ψ (thetaPshSupremum θ.val)) hR
        (isThetaPshPotential_convexComb_closed hψA h0 (t i).property.1.le
          (t i).property.2.le) j).toReal ≤ m i :=
      endpointMixedMass_toReal_mono omega
        (isThetaPshPotential_convexComb_closed hψA h0 (t i).property.1.le
          (t i).property.2.le) (W i).property hR
        (hbar (ε i).val (ε i).property).2.2.1 j
    have hdiff : Tendsto (fun i => m0 - m i) F (𝓝 (0 : ℝ)) :=
      squeeze_zero (fun i => sub_nonneg.mpr (hle i))
        (fun i => sub_le_sub_left (hge i) m0)
        (by simpa only [m0, R, sub_self] using hlow.const_sub m0)
    simpa only [sub_sub_cancel, sub_zero] using hdiff.const_sub m0
  have hmax (i : I) : (fun x => max ((W i).val x) (thetaPshSupremum θ.val x)) =
      thetaPshSupremum θ.val := funext fun x =>
    max_eq_right ((hbar (ε i).val (ε i).property).2.2.2 x)
  have hreal : Tendsto (fun i => (singularityDistance omega (θ + omega.form) hA
      (W i).val (thetaPshSupremum θ.val)).toReal) F (𝓝 (0 : ℝ)) := by
    apply (tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass omega
      (θ + omega.form) hA F (fun i => (W i).property) h0).mpr
    intro j
    refine ⟨hmass j, ?_⟩
    simpa only [hmax] using (tendsto_const_nhds : Tendsto
      (fun _ : I => (endpointMixedMass (θ + omega.form)
        (thetaPshSupremum (θ + omega.form).val) (thetaPshSupremum θ.val) hR h0 j).toReal) F
      (𝓝 (endpointMixedMass (θ + omega.form)
        (thetaPshSupremum (θ + omega.form).val) (thetaPshSupremum θ.val) hR h0 j).toReal))
  have hdist : Tendsto (fun i => dist (W i)
      (⟨thetaPshSupremum θ.val, h0⟩ : ThetaPshL1 (θ + omega.form).val)) F
      (𝓝 (0 : ℝ)) := hreal.congr' (Eventually.of_forall fun i =>
        (dist_eq_singularityDistance_toReal omega (θ + omega.form) hA (W i)
          ⟨thetaPshSupremum θ.val, h0⟩).symm)
  change Tendsto W F (𝓝 (⟨thetaPshSupremum θ.val, h0⟩ : ThetaPshL1 (θ + omega.form).val))
  exact tendsto_iff_dist_tendsto_zero.mpr hdist

/-- The source's stronger negative-side convention is recovered on the
ORIGINAL θ carrier, using the same produced functions and genuine background
independence. No smaller-class membership or target limit is input. -/
theorem exists_tendsto_original_negative_minimal
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {I : Type*} (F : Filter I) (ε : I → Ioo (0 : ℝ) δ),
      Tendsto (fun i => (ε i).val) F (𝓝 0) →
      ∃ hE : ∀ i, IsThetaPshPotential θ.val
          (thetaPshSupremum (θ - (ε i).val • omega.form).val),
      ∃ _hsmall : ∀ i, IsBigClass (RealBottChern.ofRepresentative (θ - (ε i).val • omega.form)),
        Tendsto (fun i => (⟨thetaPshSupremum (θ - (ε i).val • omega.form).val,
          hE i⟩ : ThetaPshL1 θ.val)) F
          (@nhds (ThetaPshL1 θ.val)
            (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
            ⟨thetaPshSupremum θ.val,
              (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic⟩) := by
  obtain ⟨δ, hδ, hnegative⟩ := exists_tendsto_fixedAmbient_negative_minimal omega θ hbig
  refine ⟨δ, hδ, fun {I} F ε hε => ?_⟩
  obtain ⟨hA, h0A, hEA, hsmall, hnA⟩ := hnegative F ε hε
  have h0 := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have hE (i : I) : IsThetaPshPotential θ.val
      (thetaPshSupremum (θ - (ε i).val • omega.form).val) := by
    have h := LocalPotentials.isThetaPshPotential_add_of_semipositive
      (isModelPotential_thetaPshSupremum omega (θ - (ε i).val • omega.form)
        (hsmall i)).plurisubharmonic
      (KahlerDomination.isSemipositive_smul omega.isSemipositive (ε i).property.1.le)
    simpa only [sub_add_cancel] using h
  refine ⟨hE, hsmall, ?_⟩
  exact (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
    omega θ (θ + omega.form) hbig hA F hE h0 hEA h0A).mpr hnA

end

end SGPT.Foundations.Analysis.Pending.MinimalBackgroundFixedAmbient
