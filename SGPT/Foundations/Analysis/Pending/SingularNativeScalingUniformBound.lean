import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderedMixedMassDistance
import SGPT.Foundations.Analysis.Pending.ActualPartialBackgroundMassPolynomial
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

set_option autoImplicit false

/-! # A uniform actual linear bound for admissible scaling

SGPT PDF0232--0233 Lemma 6.2.3. Actual positive finite mixed expansion,
genuine mass monotonicity and produced compact smooth domination yield a
constant chosen before the potential. The eventual Kähler-current
admissibility is internally produced from its actual lower background.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularNativeScalingUniformBound

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  RelativeEnergy GlobalNonPluripolar MixedMass GlobalMixedMassMonotone
  GlobalMultilinearExpansion MixedMassProductCalculus MixedMassBoundedDifference GlobalDiagonalScaling
  CanonicalBackgroundPolynomial AmbientMassBackgroundMonotone
  SingularMinimalCanonicalRay SingularCanonicalSingularityDistance
  SingularCanonicalOrderedMixedMassDistance ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private def scalingWeight {d : ℕ} (ε : ℝ) (k : Fin d) (b : Fin d × Bool) : ℝ :=
  if b.1 = k then (if b.2 then ε else 1 - ε) else 0

private theorem scalingWeight_bounds {d : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (k : Fin d) (b : Fin d × Bool) :
    0 ≤ scalingWeight ε k b ∧ scalingWeight ε k b ≤ 1 := by
  unfold scalingWeight
  split_ifs <;> constructor <;> linarith

private theorem prod_scalingWeight_le {d : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {g : Fin d → Fin d × Bool} (hne : g ≠ fun k => (k, false)) :
    (∏ k, scalingWeight ε k (g k)) ≤ ε := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
  have hck : scalingWeight ε k (g k) ≤ ε := by
    by_cases htag : (g k).1 = k
    · have hb : (g k).2 = true := by
        cases hbool : (g k).2
        · exact (hk (Prod.ext htag hbool)).elim
        · rfl
      simp only [scalingWeight, htag, hb, ↓reduceIte, le_refl]
    · simp only [scalingWeight, htag, ↓reduceIte]
      exact hε0.le
  have hrest : (∏ l ∈ Finset.univ.erase k, scalingWeight ε l (g l)) ≤ 1 :=
    Finset.prod_le_one (fun l _ => (scalingWeight_bounds hε0 hε1 l (g l)).1)
      (fun l _ => (scalingWeight_bounds hε0 hε1 l (g l)).2)
  rw [← Finset.mul_prod_erase Finset.univ (fun l => scalingWeight ε l (g l)) (Finset.mem_univ k)]
  exact (mul_le_of_le_one_right (scalingWeight_bounds hε0 hε1 k (g k)).1 hrest).trans hck

omit [ConnectedSpace M] in
private theorem mixedMass_toReal_le_add_kahler
    (omega η : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    {u : Fin n → M → EReal} (hu : ∀ k, IsThetaPshPotential (θ k).val (u k))
    {a : ℝ} (ha : 0 ≤ a) :
    (globalMixedMass θ u (fun k => (hu k).1)).toReal ≤
      (globalMixedMass (fun k => θ k + a • η.form) u
        (fun k => (LocalPotentials.isThetaPshPotential_add_of_semipositive (hu k)
          (KahlerDomination.isSemipositive_smul η.isSemipositive ha)).1)).toReal := by
  classical
  let c : Fin n → Option (Fin n) → ℝ := fun k o =>
    match o with
    | none => a
    | some l => if l = k then 1 else 0
  have hc (k : Fin n) (o : Option (Fin n)) : 0 ≤ c k o := by
    cases o <;> dsimp [c]
    · exact ha
    · split_ifs <;> norm_num
  have hpots (o : Option (Fin n)) :
      IsThetaPshPotential (optForm η θ o).val (optPot u o) := by
    cases o
    · exact (LocalPotentials.isThetaPshPotential_zero_iff η.form).mpr η.isSemipositive
    · exact hu _
  have hF : (fun k => sumForm Finset.univ (c k) (optForm η θ)) =
      fun k => θ k + a • η.form := by
    funext k
    simp [sumForm, Fintype.sum_option, c, optForm, ite_smul, add_comm]
  have hQ : (fun k => sumPot Finset.univ (c k) (optPot u)) = u := by
    funext k x
    simp [sumPot, Fintype.sum_option, c, optPot, apply_ite, ite_mul]
  have h := globalMixedMass_sumPot_expand_toReal omega hc hpots
  unfold globalMixedMass at h
  rw [globalMixedMeasure_congr hF hQ _
    (fun k => (LocalPotentials.isThetaPshPotential_add_of_semipositive (hu k)
      (KahlerDomination.isSemipositive_smul η.isSemipositive ha)).1)] at h
  let g₀ : Fin n → Option (Fin n) := fun k => some k
  have hterm : (∏ k, c k (g₀ k)) *
      (globalMixedMass (fun k => optForm η θ (g₀ k)) (fun k => optPot u (g₀ k))
        (fun k => (hpots (g₀ k)).1)).toReal =
      (globalMixedMass θ u (fun k => (hu k).1)).toReal := by
    simp [g₀, c, optForm, optPot]
  rw [← hterm]
  exact (Finset.single_le_sum (fun g _ => mul_nonneg
    (Finset.prod_nonneg fun k _ => hc k (g k)) ENNReal.toReal_nonneg)
    (Finset.mem_univ g₀)).trans_eq h.symm

private def scalingForm (θ : ClosedRealOneOneForm n M) (κ : KahlerBackground n M)
    (b : Fin n × Bool) : ClosedRealOneOneForm n M := if b.2 then κ.form else θ

private def scalingPotential (j : Fin (n + 1)) (u p : M → EReal)
    (b : Fin n × Bool) : M → EReal :=
  if b.2 then (if b.1.val < j.val then 0 else p) else endpointMixedPotential j u p b.1

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem scalingPotential_genuine {θ : ClosedRealOneOneForm n M}
    (κ : KahlerBackground n M) {u p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    (hpκ : IsThetaPshPotential κ.form.val p) (j : Fin (n + 1)) (b : Fin n × Bool) :
    IsThetaPshPotential (scalingForm θ κ b).val (scalingPotential j u p b) := by
  rcases b with ⟨k, b⟩
  cases b
  · dsimp [scalingForm, scalingPotential, endpointMixedPotential]
    split_ifs <;> first | exact hu | exact hp
  · dsimp [scalingForm, scalingPotential]
    split_ifs
    · exact (LocalPotentials.isThetaPshPotential_zero_iff κ.form).mpr κ.isSemipositive
    · exact hpκ

private def referenceSelectorMass (θ : ClosedRealOneOneForm n M)
    (κ : KahlerBackground n M) (p : M → EReal)
    (hp : IsThetaPshPotential θ.val p) (hpκ : IsThetaPshPotential κ.form.val p)
    (j : Fin (n + 1)) (g : Fin n → Fin n × Bool) : ℝ :=
  (globalMixedMass (fun k => scalingForm θ κ (g k))
    (fun k => scalingPotential j p p (g k))
    (fun k => (scalingPotential_genuine κ hp hp hpκ j (g k)).1)).toReal

private theorem ereal_scale_self {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (z : EReal) :
    (ε : EReal) * z + ((1 - ε : ℝ) : EReal) * z = z := by
  induction z using EReal.rec with
  | bot => simp only [EReal.coe_mul_bot_of_pos hε0,
      EReal.coe_mul_bot_of_pos (sub_pos.mpr hε1), EReal.bot_add]
  | top => simp only [EReal.coe_mul_top_of_pos hε0,
      EReal.coe_mul_top_of_pos (sub_pos.mpr hε1), EReal.top_add_top]
  | coe r =>
    simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring

omit [ConnectedSpace M] in
private theorem endpoint_enlarged_scaled_eq_sum
    (omega κ η : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hκ : κ.form = θ + η.form) {u p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    (hpκ : IsThetaPshPotential κ.form.val p)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsu : IsThetaPshPotential θ.val (fun x => ((1 - ε : ℝ) : EReal) * u x))
    (j : Fin (n + 1)) :
    let hpγ := LocalPotentials.isThetaPshPotential_add_of_semipositive hp
      (KahlerDomination.isSemipositive_smul η.isSemipositive hε0.le)
    let huγ := LocalPotentials.isThetaPshPotential_add_of_semipositive hsu
      (KahlerDomination.isSemipositive_smul η.isSemipositive hε0.le)
    (endpointMixedMass (θ + ε • η.form) p (fun x => ((1 - ε : ℝ) : EReal) * u x)
      hpγ huγ j).toReal =
      ∑ g : Fin n → Fin n × Bool, (∏ k, scalingWeight ε k (g k)) *
        (globalMixedMass (fun k => scalingForm θ κ (g k))
          (fun k => scalingPotential j u p (g k))
          (fun k => (scalingPotential_genuine κ hu hp hpκ j (g k)).1)).toReal := by
  classical
  have hc (k : Fin n) (b : Fin n × Bool) : 0 ≤ scalingWeight ε k b :=
    (scalingWeight_bounds hε0 hε1 k b).1
  have hf (b : Fin n × Bool) := scalingPotential_genuine κ hu hp hpκ j b
  have hF : (fun k => sumForm Finset.univ (scalingWeight ε k) (scalingForm θ κ)) =
      fun _ : Fin n => θ + ε • η.form := by
    funext k
    simp only [sumForm, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single k]
    · simp only [Fintype.sum_bool, scalingWeight, scalingForm, Bool.false_eq_true, ↓reduceIte]
      rw [hκ]
      module
    · intro l _ hl
      simp only [Fintype.sum_bool, scalingWeight, hl, ↓reduceIte, zero_smul, zero_add]
    · simp
  have hQ : (fun k => sumPot Finset.univ (scalingWeight ε k) (scalingPotential j u p)) =
      endpointMixedPotential j (fun x => ((1 - ε : ℝ) : EReal) * u x) p := by
    funext k x
    simp only [sumPot, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single k]
    · by_cases hk : k.val < j.val
      · simp only [Fintype.sum_bool, scalingWeight, scalingPotential, Bool.false_eq_true,
          endpointMixedPotential, ↓reduceIte, hk, Pi.zero_apply, mul_zero, zero_add]
      · simpa only [Fintype.sum_bool, scalingWeight, scalingPotential, Bool.false_eq_true,
          endpointMixedPotential, ↓reduceIte, hk] using ereal_scale_self hε0 hε1 (p x)
    · intro l _ hl
      simp only [Fintype.sum_bool, scalingWeight, hl, ↓reduceIte, EReal.coe_zero,
        zero_mul, zero_add]
    · simp
  have h := globalMixedMass_sumPot_expand_toReal omega hc hf
  unfold globalMixedMass at h
  rw [globalMixedMeasure_congr hF hQ _
    (endpointMixedPotential_thetaPlurisubharmonic (θ + ε • η.form) j _ p
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hsu
        (KahlerDomination.isSemipositive_smul η.isSemipositive hε0.le))
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hp
        (KahlerDomination.isSemipositive_smul η.isSemipositive hε0.le)))] at h
  exact h

omit [ConnectedSpace M] in
private theorem endpoint_scaled_sub_le
    (omega κ η : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hκ : κ.form = θ + η.form) {u p : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hp : IsThetaPshPotential θ.val p)
    (hpκ : IsThetaPshPotential κ.form.val p) (hup : u ≤ p)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsu : IsThetaPshPotential θ.val (fun x => ((1 - ε : ℝ) : EReal) * u x))
    (j : Fin (n + 1)) :
    (endpointMixedMass θ p (fun x => ((1 - ε : ℝ) : EReal) * u x) hp hsu j).toReal -
      (endpointMixedMass θ p u hp hu j).toReal ≤
      ε * ∑ g ∈ Finset.univ.erase (fun k : Fin n => (k, false)),
        referenceSelectorMass θ κ p hp hpκ j g := by
  classical
  let g₀ : Fin n → Fin n × Bool := fun k => (k, false)
  let A : (Fin n → Fin n × Bool) → ℝ := fun g =>
    (globalMixedMass (fun k => scalingForm θ κ (g k))
      (fun k => scalingPotential j u p (g k))
      (fun k => (scalingPotential_genuine κ hu hp hpκ j (g k)).1)).toReal
  let B := referenceSelectorMass θ κ p hp hpκ j
  have hA0 (g) : 0 ≤ A g := ENNReal.toReal_nonneg
  have hAB (g) : A g ≤ B g := by
    have hpot (b : Fin n × Bool) : scalingPotential j u p b ≤ scalingPotential j p p b := by
      rcases b with ⟨k, b⟩
      cases b
      · dsimp [scalingPotential, endpointMixedPotential]
        split_ifs <;> first | exact hup | exact le_rfl
      · rfl
    have h := globalMixedMass_mono_of_isThetaPshPotential omega
      (fun k => scalingPotential_genuine κ hu hp hpκ j (g k))
      (fun k => scalingPotential_genuine κ hp hp hpκ j (g k))
      (fun k => MoreSingularOn.of_le fun x _ => hpot (g k) x)
    exact ENNReal.toReal_mono (globalMixedMass_lt_top omega
      (fun k => (scalingPotential_genuine κ hp hp hpκ j (g k)).1)).ne h
  have hbase : A g₀ = (endpointMixedMass θ p u hp hu j).toReal := by
    simp only [A, g₀, scalingForm, scalingPotential, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hprod1 (g : Fin n → Fin n × Bool) : (∏ k, scalingWeight ε k (g k)) ≤ 1 :=
    Finset.prod_le_one (fun k _ => (scalingWeight_bounds hε0 hε1 k (g k)).1)
      (fun k _ => (scalingWeight_bounds hε0 hε1 k (g k)).2)
  have hother : (∑ g ∈ Finset.univ.erase g₀, (∏ k, scalingWeight ε k (g k)) * A g) ≤
      ε * ∑ g ∈ Finset.univ.erase g₀, B g := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro g hg
    have hg0 : g ≠ fun k => (k, false) := (Finset.mem_erase.mp hg).1
    exact (mul_le_mul_of_nonneg_right (prod_scalingWeight_le hε0 hε1 hg0) (hA0 g)).trans
      (mul_le_mul_of_nonneg_left (hAB g) hε0.le)
  have hstar : (∏ k, scalingWeight ε k (g₀ k)) * A g₀ ≤
      (endpointMixedMass θ p u hp hu j).toReal :=
    (mul_le_of_le_one_left (hA0 g₀) (hprod1 g₀)).trans_eq hbase
  have htu (k : Fin n) : IsThetaPshPotential θ.val
      (endpointMixedPotential j (fun x => ((1 - ε : ℝ) : EReal) * u x) p k) := by
    by_cases hk : k.val < j.val
    · simpa only [endpointMixedPotential, hk, ↓reduceIte] using hsu
    · simpa only [endpointMixedPotential, hk, ↓reduceIte] using hp
  have hbg := mixedMass_toReal_le_add_kahler omega η htu hε0.le
  have hexpand := endpoint_enlarged_scaled_eq_sum omega κ η θ hκ hu hp hpκ hε0 hε1 hsu j
  have htotal : (endpointMixedMass θ p (fun x => ((1 - ε : ℝ) : EReal) * u x) hp hsu j).toReal ≤
      ε * ∑ g ∈ Finset.univ.erase g₀, B g + (endpointMixedMass θ p u hp hu j).toReal := by
    calc
      _ ≤ _ := hbg
      _ = ∑ g : Fin n → Fin n × Bool, (∏ k, scalingWeight ε k (g k)) * A g := hexpand
      _ = (∑ g ∈ Finset.univ.erase g₀, (∏ k, scalingWeight ε k (g k)) * A g) +
          (∏ k, scalingWeight ε k (g₀ k)) * A g₀ :=
        (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ g₀)).symm
      _ ≤ _ := add_le_add hother hstar
  exact sub_le_iff_le_add.mpr htotal

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M] in
private theorem scale_sub_const {c : ℝ} (hc : 0 < c) (u : M → EReal) (b : ℝ) :
    (fun x => (c : EReal) * (u x - (b : EReal))) =
      fun x => (c : EReal) * u x - ((c * b : ℝ) : EReal) := by
  funext x
  simpa only [EReal.coe_neg, sub_eq_add_neg, mul_neg] using
    ThetaPshConvexCombination.coe_mul_add_coe hc (u x) (-b)

/-- The finite actual reference selector masses give a positive constant
chosen before every potential and every admissible parameter. -/
theorem exists_uniform_singularityDistance_admissible_scaling_bound
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → EReal) (_hu : IsThetaPshPotential θ.val u)
      (ε : ℝ) (_hε : ε ∈ Ioo (0 : ℝ) 1)
      (_hsu : IsThetaPshPotential θ.val (fun x => ((1 - ε : ℝ) : EReal) * u x)),
      0 ≤ (singularityDistance omega θ hbig
        (fun x => ((1 - ε : ℝ) : EReal) * u x) u).toReal ∧
      (singularityDistance omega θ hbig
        (fun x => ((1 - ε : ℝ) : EReal) * u x) u).toReal ≤ C * ε ∧
      singularityDistance omega θ hbig
        (fun x => ((1 - ε : ℝ) : EReal) * u x) u ≤ ((C * ε : ℝ) : EReal) := by
  classical
  obtain ⟨A, hA, hη⟩ := KahlerDomination.exists_pos_isKahler_add_smul omega (-θ)
  let κ := KahlerBackground.smul hA omega
  let η : KahlerBackground n M := ⟨-θ + A • omega.form, hη⟩
  have hκ : κ.form = θ + η.form := by
    dsimp [κ, η, KahlerBackground.smul]
    abel
  let p := thetaPshSupremum θ.val
  have hp : IsThetaPshPotential θ.val p :=
    (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have hpκ : IsThetaPshPotential κ.form.val p := by
    rw [hκ]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive hp η.isSemipositive
  let B : Fin (n + 1) → ℝ := fun j =>
    ∑ g ∈ Finset.univ.erase (fun k : Fin n => (k, false)), referenceSelectorMass θ κ p hp hpκ j g
  have hB (j : Fin (n + 1)) : 0 ≤ B j := Finset.sum_nonneg fun g _ => ENNReal.toReal_nonneg
  let C₀ : ℝ := (∑ j : Fin (n + 1), B j) / (n + 1 : ℝ)
  have hC₀ : 0 ≤ C₀ := div_nonneg (Finset.sum_nonneg fun j _ => hB j) (by positivity)
  refine ⟨1 + C₀, by positivity, fun u hu ε hε hsu => ?_⟩
  obtain ⟨b, hb⟩ := hu.exists_global_upper_bound
  let v : M → EReal := fun x => u x - (b : EReal)
  have hv : IsThetaPshPotential θ.val v := hu.sub_const b
  have hv0 : v ≤ 0 := sub_const_nonpositive_of_le hb
  have hvp : v ≤ p := le_thetaPshSupremum hv hv0
  let sv : M → EReal := fun x => ((1 - ε : ℝ) : EReal) * v x
  have hs : 0 < 1 - ε := sub_pos.mpr hε.2
  have hshift : sv = fun x => ((1 - ε : ℝ) : EReal) * u x - (((1 - ε) * b : ℝ) : EReal) :=
    scale_sub_const hs u b
  have hsv : IsThetaPshPotential θ.val sv := by
    rw [hshift]
    exact hsu.sub_const ((1 - ε) * b)
  have horder : v ≤ sv := by
    intro x
    change v x ≤ ((1 - ε : ℝ) : EReal) * v x
    have h0 : v x ≤ (0 : EReal) := hv0 x
    induction hx : v x using EReal.rec with
    | bot => simp only [EReal.coe_mul_bot_of_pos hs, le_refl]
    | top => rw [hx] at h0; simp at h0
    | coe r =>
      rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
      have hr : r ≤ 0 := by rw [hx] at h0; exact_mod_cast h0
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hε.1.le hr]
  have hD : singularityDistance omega θ hbig sv v =
      singularityDistance omega θ hbig (fun x => ((1 - ε : ℝ) : EReal) * u x) u := by
    rw [hshift]
    unfold singularityDistance
    rw [canonicalRay_sub_const_eq θ hsu ((1 - ε) * b), canonicalRay_sub_const_eq θ hu b]
  have he (j : Fin (n + 1)) :
      (endpointMixedMass θ p sv hp hsv j).toReal - (endpointMixedMass θ p v hp hv j).toReal ≤ ε * B j :=
    endpoint_scaled_sub_le omega κ η θ hκ hv hp hpκ hvp hε.1 hε.2 hsv j
  have hf := singularityDistance_eq_mixedMass_sub_of_le omega θ hbig hv hsv horder
  change singularityDistance omega θ hbig v sv =
    ((((∑ j : Fin (n + 1), ((endpointMixedMass θ p sv hp hsv j).toReal -
      (endpointMixedMass θ p v hp hv j).toReal)) / (n + 1 : ℝ)) : ℝ) : EReal) at hf
  let : PseudoMetricSpace (ThetaPshL1 θ.val) := singularityPseudoMetricSpace omega θ hbig
  have hcomm : (singularityDistance omega θ hbig sv v).toReal =
      (singularityDistance omega θ hbig v sv).toReal := by
    rw [← dist_eq_singularityDistance_toReal omega θ hbig (⟨sv, hsv⟩ : ThetaPshL1 θ.val) ⟨v, hv⟩,
      ← dist_eq_singularityDistance_toReal omega θ hbig (⟨v, hv⟩ : ThetaPshL1 θ.val) ⟨sv, hsv⟩]
    exact dist_comm _ _
  have hreal : (singularityDistance omega θ hbig
      (fun x => ((1 - ε : ℝ) : EReal) * u x) u).toReal ≤ (1 + C₀) * ε := by
    rw [← hD, hcomm, hf, EReal.toReal_coe]
    calc
      _ ≤ (∑ j : Fin (n + 1), ε * B j) / (n + 1 : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => he j) (by positivity)
      _ = C₀ * ε := by rw [← Finset.mul_sum]; dsimp [C₀]; ring
      _ ≤ (1 + C₀) * ε := by nlinarith [hε.1]
  obtain ⟨d, hd0, _, _, hd⟩ := exists_tendsto_singularityDistance omega θ hbig hsu hu
  refine ⟨?_, hreal, ?_⟩
  · simpa only [hd, EReal.toReal_coe] using hd0
  · rw [hd]
    apply EReal.coe_le_coe_iff.mpr
    simpa only [hd, EReal.toReal_coe] using hreal

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
private theorem current_scaling_admissible_interval
    (θ : ClosedRealOneOneForm n M)
    (T : KahlerCurrent (RealBottChern.ofRepresentative θ))
    (hrep : T.representative = θ) :
    IsThetaPshPotential θ.val T.potential ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) r →
        IsThetaPshPotential θ.val (fun x => ((1 - ε : ℝ) : EReal) * T.potential x) := by
  have hstrict : IsThetaPshPotential (θ - T.lowerBound.form).val T.potential := by
    simpa only [hrep] using T.strictlyPsh
  have hu : IsThetaPshPotential θ.val T.potential := by
    simpa only [sub_add_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hstrict T.lowerBound.isSemipositive
  obtain ⟨B, hB, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul T.lowerBound θ
  have hBp : 0 < B + 1 := by positivity
  let r : ℝ := min 1 (1 / (B + 1))
  have hr : 0 < r := lt_min zero_lt_one (div_pos zero_lt_one hBp)
  refine ⟨hu, r, hr, min_le_left _ _, fun ε hε => ?_⟩
  have he1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
  have heB : ε < 1 / (B + 1) := hε.2.trans_le (min_le_right _ _)
  have hcoef : 0 ≤ 1 - (B + 1) * ε := by
    have hmul := (lt_div_iff₀ hBp).mp heB
    nlinarith
  let βε : ClosedRealOneOneForm n M :=
    ε • (θ + B • T.lowerBound.form) + (1 - (B + 1) * ε) • T.lowerBound.form
  have hβε : βε.val.IsSemipositive :=
    UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul hsemi hε.1.le)
      (KahlerDomination.isSemipositive_smul T.lowerBound.isSemipositive hcoef)
  have hscaled := RestrictedApproximantComparison.isThetaPshPotential_smul
    hstrict (sub_pos.mpr he1)
  have hform : (1 - ε) • (θ - T.lowerBound.form) + βε = θ := by
    dsimp [βε]
    module
  simpa only [hform] using
    LocalPotentials.isThetaPshPotential_add_of_semipositive hscaled hβε

/-- The same constant is chosen before every genuine Kähler current;
its actual lower background produces eventual admissibility internally. -/
theorem exists_uniform_singularityDistance_current_scaling_bound
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : KahlerCurrent (RealBottChern.ofRepresentative θ))
        (_hrep : T.representative = θ),
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
          IsThetaPshPotential θ.val (fun x => ((1 - ε : ℝ) : EReal) * T.potential x) ∧
          0 ≤ (singularityDistance omega θ hbig
            (fun x => ((1 - ε : ℝ) : EReal) * T.potential x) T.potential).toReal ∧
          (singularityDistance omega θ hbig
            (fun x => ((1 - ε : ℝ) : EReal) * T.potential x) T.potential).toReal ≤ C * ε ∧
          singularityDistance omega θ hbig
            (fun x => ((1 - ε : ℝ) : EReal) * T.potential x) T.potential ≤
              ((C * ε : ℝ) : EReal) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_singularityDistance_admissible_scaling_bound omega θ hbig
  refine ⟨C, hC, fun T hrep => ?_⟩
  obtain ⟨hu, r, hr, hr1, hadm⟩ := current_scaling_admissible_interval θ T hrep
  have hgt : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hlt : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [hgt, hlt] with ε hε0 hεr
  have hscaled := hadm ε ⟨hε0, hεr⟩
  exact ⟨hscaled, hbound T.potential hu ε ⟨hε0, hεr.trans_le hr1⟩ hscaled⟩

end
end SGPT.Foundations.Analysis.Pending.SingularNativeScalingUniformBound
