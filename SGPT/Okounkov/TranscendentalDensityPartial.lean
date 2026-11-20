import SGPT.Okounkov.TranscendentalDensity

/-!
# Partial Okounkov bodies via currents with analytic singularities

Source: blueprint node `tok:partial-analytic` (DRWNXZ Lemma 5.3), chapter
`claude-okounkov-transcendental`: for a Kähler current `R = θ + dd^c u` with analytic
singularities, `Δ(ξ; R) = closure ν(Ω(ξ; R)) = closure ν(𝒜(ξ; R))`.

The results take Skoda's theorem (`ManifoldSkodaStatement`) as the hypothesis `hS`; it is
discharged in `TranscendentalDensityTheorem.lean` (`partialAnalyticStatement`).

## Proof

Let `G = θ + dd^c φ ∈ 𝒜(ξ; R)`, i.e. `φ` has analytic singularities and `φ ≤ u + O(1)`.

1. `(1 - t)φ + tu` (`t ∈ ℚ ∩ (0, 1]`) is a Kähler potential in `𝒜(ξ; R)` with valuation
   `(1 - t)ν(G) + tν(R)`; so one may assume `θ + dd^c φ ≥ κ`.
2. For small `δ ∈ ℚ_{>0}` (`δ A ≤ 1/2`, `-θ + Aκ ≥ 0`), `φ₂ = φ + δu` satisfies
   `θ + dd^c φ₂ ≥ κ/2`, has analytic singularities, valuation `ν(G) + δν(R)` and
   `φ₂ ⪯ (1 + δ)u`.
3. Clearing denominators (`Φ = Nφ₂`), `exists_gentle_approximant_near` gives `v ∈ Ω(Nθ)` with
   `ν(v)` close to `ν(Φ)` and `v ≤ aΦ + O(1)`, `a ≥ 1/(1 + δ)`. Then `v/N ∈ Ω(θ)` and
   `v/N ⪯ aφ₂ ⪯ a(1 + δ)u ⪯ u` because `u` is bounded above (`singularityLE_smul_self`).

(The blueprint's normalization `u_ε = (1+ε)u`, `φ_ε = φ + εu` is step 2; the inclusion
`𝓘(Kφ_ε) ⊆ 𝓘(Ku_ε) = J^k𝓘(mu_ε)` of the source is replaced by the singularity type of the
approximants, `v ≤ (k/K)Φ + O(1)`, which already comes out of `tok:density`.)
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalDensity

open Set Filter
open scoped Topology NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSkoda

/-- `p (q z) = (p q) z` in `EReal` for real `p`, `q`. -/
theorem ereal_coe_mul_coe_mul (p q : ℝ) (z : EReal) :
    (p : EReal) * ((q : EReal) * z) = ((p * q : ℝ) : EReal) * z := by
  rw [← mul_assoc, ← EReal.coe_mul]

/-- `(1 - t) z + t z = z` and `z + δ z = (1 + δ) z` in `EReal`. -/
theorem ereal_add_smul_self {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (z : EReal) :
    (p : EReal) * z + (q : EReal) * z = ((p + q : ℝ) : EReal) * z := by
  rw [EReal.coe_add, EReal.right_distrib_of_nonneg (EReal.coe_nonneg.mpr hp)
    (EReal.coe_nonneg.mpr hq)]

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok:partial-analytic` for Kähler currents** (conditional on Skoda's theorem): if
`θ + dd^c φ ≥ κ`, `φ` has analytic singularities, `φ ⪯ u` and `u` is `θ`-psh with analytic
singularities, then `ν(φ) ∈ closure ν(Ω(θ; u))`. -/
theorem flagValuation_mem_closure_below_of_kahler (hS : ManifoldSkodaStatement.{u})
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {κ : KahlerBackground (m + 1) F.carrier}
    {φ uR : F.carrier → EReal} (hφ : IsThetaPshPotential (θ - κ.form).val φ)
    (hφA : HasManifoldAnalyticSingularityType (n := m + 1) φ) (hφu : SingularityLE φ uR)
    (hu : uR ∈ analyticCurrents θ) :
    flagValuation F φ ∈ closure (flagValuation F '' gentleKahlerCurrentsBelow θ uR) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨A, hA, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-θ)
  set L := ‖flagValuation F uR‖ with hL
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * A + 2 * (L + 1) / ε)
  set δ : ℚ := ((N₀ : ℚ) + 1)⁻¹ with hδ
  have hδ0 : (0 : ℚ) < δ := by positivity
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hN1 : (0 : ℝ) < (N₀ : ℝ) + 1 := by positivity
  have hδeq : (δ : ℝ) = ((N₀ : ℝ) + 1)⁻¹ := by rw [hδ]; push_cast; ring
  have hLε : 2 * (L + 1) / ε < (N₀ : ℝ) + 1 := by
    have : 0 ≤ 2 * A := by positivity
    linarith
  have hδA : (δ : ℝ) * A ≤ 1 / 2 := by
    rw [hδeq, inv_mul_eq_div, div_le_iff₀ hN1]
    have : 0 ≤ 2 * (L + 1) / ε := by positivity
    linarith
  have hδL : (δ : ℝ) * (L + 1) < ε / 2 := by
    rw [div_lt_iff₀ hε] at hLε
    rw [hδeq, inv_mul_eq_div, div_lt_iff₀ hN1]
    linarith
  -- the perturbation `φ₂ = φ + δ u`
  set φ₂ : F.carrier → EReal :=
    fun x => (((1 : ℚ) : ℝ) : EReal) * φ x + (((δ : ℚ) : ℝ) : EReal) * uR x with hφ₂
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hφ₂psh : IsThetaPshPotential (θ - (KahlerBackground.smul hhalf κ).form).val φ₂ := by
    have h := isThetaPshPotential_add_from_positive_sum
      (isThetaPshPotential_nonneg_smul hφ (by norm_num : (0 : ℝ) ≤ ((1 : ℚ) : ℝ)))
      (isThetaPshPotential_nonneg_smul hu.1 hδR.le)
    refine TranscendentalBody.isThetaPshPotential_of_le h ?_
    have heq : θ - (KahlerBackground.smul hhalf κ).form -
        ((((1 : ℚ) : ℝ)) • (θ - κ.form) + ((δ : ℚ) : ℝ) • θ) =
        ((δ : ℚ) : ℝ) • (-θ + A • κ.form) + (1 / 2 - (δ : ℝ) * A) • κ.form := by
      rw [KahlerBackground.smul_form]
      push_cast
      module
    rw [heq]
    exact UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul hdom hδR.le)
      (KahlerDomination.isSemipositive_smul κ.isSemipositive (by linarith))
  have hφ₂A : HasManifoldAnalyticSingularityType (n := m + 1) φ₂ :=
    hasManifoldAnalyticSingularityType_add
      (hasManifoldAnalyticSingularityType_nonneg_rat_smul hφA zero_le_one)
      (hasManifoldAnalyticSingularityType_nonneg_rat_smul hu.2 hδ0.le)
  have hφθ : IsThetaPshPotential (θ - κ.form).val φ := hφ
  have hνφ₂ : flagValuation F φ₂ =
      ((1 : ℚ) : ℝ) • flagValuation F φ + ((δ : ℚ) : ℝ) • flagValuation F uR :=
    flagValuation_add_smul hφθ hu.1 (by norm_num) hδR.le
  -- `φ₂ ⪯ (1 + δ) u`
  have hφ₂u : SingularityLE φ₂ (fun x => (((1 : ℚ) + (δ : ℚ) : ℚ) : ℝ) * uR x) := by
    refine singularityLE_trans
      (singularityLE_add (singularityLE_smul hφu (by norm_num : (0 : ℝ) ≤ ((1 : ℚ) : ℝ)))
        (singularityLE_refl (fun x => (((δ : ℚ) : ℝ) : EReal) * uR x)))
      (singularityLE_of_eq fun x => ?_)
    rw [ereal_add_smul_self (by norm_num) hδR.le]
    push_cast
    rfl
  -- clearing denominators
  obtain ⟨N, hN, hpres⟩ := exists_nat_unitLogPresentedAt hφ₂A
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set κ₂ := KahlerBackground.smul hhalf κ
  have hΦ : IsThetaPshPotential ((N : ℝ) • θ - (KahlerBackground.smul hNR κ₂).form).val
      (fun y => ((N : ℝ) : EReal) * φ₂ y) := by
    have h := isThetaPshPotential_nonneg_smul hφ₂psh hNR.le
    have hform : (N : ℝ) • (θ - κ₂.form) = (N : ℝ) • θ - (KahlerBackground.smul hNR κ₂).form := by
      simp only [KahlerBackground.smul_form, smul_sub]
    rwa [hform] at h
  have hνΦ : flagValuation F (fun y => ((N : ℝ) : EReal) * φ₂ y) =
      (N : ℝ) • flagValuation F φ₂ := flagValuation_smul hφ₂psh hNR.le
  set ε' : ℝ := min (N * ε / 2) ((δ : ℝ) / (1 + δ)) with hε'
  have hε'0 : 0 < ε' := lt_min (by positivity) (by positivity)
  obtain ⟨v, hv, hdist, a, ha1, ha2, C, hC⟩ :=
    exists_gentle_approximant_near F hS (Nat.succ_pos m) hΦ hpres hε'0
  have hNQ : (0 : ℚ) < ((N : ℚ))⁻¹ := by positivity
  have hv' := smul_mem_gentleKahlerCurrents hv hNQ
  have hform : (((N : ℚ)⁻¹ : ℚ) : ℝ) • ((N : ℝ) • θ) = θ := by
    rw [smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hNR.ne', one_smul]
  rw [hform] at hv'
  have hNinv : (((N : ℚ)⁻¹ : ℚ) : ℝ) = ((N : ℝ))⁻¹ := by push_cast; ring
  -- `v / N ⪯ u`
  have ha0 : 0 ≤ a := by
    have : ε' ≤ (δ : ℝ) / (1 + δ) := min_le_right _ _
    have : (δ : ℝ) / (1 + δ) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  have hs : 1 ≤ a * (((1 : ℚ) + (δ : ℚ) : ℚ) : ℝ) := by
    have h1 : ε' ≤ (δ : ℝ) / (1 + δ) := min_le_right _ _
    have h2 : 1 - (δ : ℝ) / (1 + δ) ≤ a := by linarith
    have h3 : 1 - (δ : ℝ) / (1 + δ) = 1 / (1 + δ) := by field_simp; ring
    rw [h3, div_le_iff₀ (by positivity)] at h2
    push_cast
    linarith
  obtain ⟨M, hM⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hu.1
  have hbelow : SingularityLE (fun x => ((((N : ℚ)⁻¹ : ℚ) : ℝ) : EReal) * v x) uR := by
    have h1 : SingularityLE v (fun y => (a : EReal) * (((N : ℝ) : EReal) * φ₂ y)) :=
      ⟨C, fun y _ => hC y⟩
    have h2 := singularityLE_smul h1 (show (0 : ℝ) ≤ (((N : ℚ)⁻¹ : ℚ) : ℝ) by positivity)
    refine singularityLE_trans h2 (singularityLE_trans (singularityLE_of_eq fun y => ?_)
      (singularityLE_trans (singularityLE_smul hφ₂u ha0) (singularityLE_trans
        (singularityLE_of_eq fun y => ereal_coe_mul_coe_mul _ _ _)
        (singularityLE_smul_self hM hs))))
    · show ((((N : ℚ)⁻¹ : ℚ) : ℝ) : EReal) * ((a : EReal) * (((N : ℝ) : EReal) * φ₂ y)) =
        (a : EReal) * φ₂ y
      rw [ereal_coe_mul_coe_mul, ereal_coe_mul_coe_mul, hNinv]
      congr 2
      field_simp
  refine ⟨_, ⟨_, ⟨hv', hbelow⟩, rfl⟩, ?_⟩
  -- the valuation estimate
  have hvθ : IsThetaPshPotential ((N : ℝ) • θ).val v := hv.1.1
  have hd1 : dist (flagValuation F φ₂)
      (flagValuation F fun x => ((((N : ℚ)⁻¹ : ℚ) : ℝ) : EReal) * v x) < ε / 2 := by
    rw [flagValuation_smul hvθ (by positivity), dist_comm, dist_eq_norm]
    have hsub : ((((N : ℚ)⁻¹ : ℚ) : ℝ)) • flagValuation F v - flagValuation F φ₂ =
        ((N : ℝ))⁻¹ •
          (flagValuation F v - flagValuation F (fun y => ((N : ℝ) : EReal) * φ₂ y)) := by
      rw [hνΦ, smul_sub, smul_smul, inv_mul_cancel₀ hNR.ne', one_smul, hNinv]
    rw [hsub, norm_smul, Real.norm_of_nonneg (by positivity), ← dist_eq_norm]
    calc ((N : ℝ))⁻¹ * dist (flagValuation F v) (flagValuation F fun y => ((N : ℝ) : EReal) * φ₂ y)
        < ((N : ℝ))⁻¹ * (N * ε / 2) :=
          mul_lt_mul_of_pos_left (hdist.trans_le (min_le_left _ _)) (by positivity)
      _ = ε / 2 := by field_simp
  have hd2 : dist (flagValuation F φ) (flagValuation F φ₂) < ε / 2 := by
    rw [dist_comm, dist_eq_norm, hνφ₂]
    have : ((1 : ℚ) : ℝ) • flagValuation F φ + ((δ : ℚ) : ℝ) • flagValuation F uR -
        flagValuation F φ = ((δ : ℚ) : ℝ) • flagValuation F uR := by
      push_cast
      module
    rw [this, norm_smul, Real.norm_of_nonneg hδR.le, ← hL]
    nlinarith [norm_nonneg (flagValuation F uR)]
  calc dist (flagValuation F φ) _ ≤ dist (flagValuation F φ) (flagValuation F φ₂) +
        dist (flagValuation F φ₂) _ := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hd2 hd1
    _ = ε := add_halves ε

/-- **`tok:partial-analytic`, pointwise** (conditional on Skoda's theorem): for a Kähler current
`R = θ + dd^c u ∈ 𝒜(ξ)` and `G ∈ 𝒜(ξ; R)`, `ν(G) ∈ closure ν(Ω(ξ; R))`. -/
theorem flagValuation_mem_closure_below (hS : ManifoldSkodaStatement.{u})
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {uR : F.carrier → EReal}
    (hu : IsKahlerCurrentPotential θ uR) (huA : uR ∈ analyticCurrents θ)
    {φ : F.carrier → EReal} (hφ : φ ∈ analyticCurrentsBelow θ uR) :
    flagValuation F φ ∈ closure (flagValuation F '' gentleKahlerCurrentsBelow θ uR) := by
  obtain ⟨⟨hφpsh, hφA⟩, hφu⟩ := hφ
  obtain ⟨κ, hκ⟩ := hu
  rw [Metric.mem_closure_iff]
  intro ε hε
  set L := ‖flagValuation F uR - flagValuation F φ‖ with hL
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * (L + 1) / ε)
  set t : ℚ := ((N₀ : ℚ) + 1)⁻¹ with ht
  have ht0 : (0 : ℚ) < t := by positivity
  have ht0R : (0 : ℝ) < t := by exact_mod_cast ht0
  have hN1 : (0 : ℝ) < (N₀ : ℝ) + 1 := by positivity
  have hteq : (t : ℝ) = ((N₀ : ℝ) + 1)⁻¹ := by rw [ht]; push_cast; ring
  have ht1 : (t : ℝ) ≤ 1 := by
    rw [hteq, inv_le_one₀ hN1]
    linarith [(N₀.cast_nonneg : (0 : ℝ) ≤ N₀)]
  have ht1Q : (0 : ℚ) ≤ 1 - t := by
    have : ((1 - t : ℚ) : ℝ) ≥ 0 := by push_cast; linarith
    exact_mod_cast this
  have htL : (t : ℝ) * (L + 1) < ε / 2 := by
    have h2 : 2 * (L + 1) / ε < (N₀ : ℝ) + 1 := hN₀.trans (lt_add_one _)
    rw [div_lt_iff₀ hε] at h2
    rw [hteq, inv_mul_eq_div, div_lt_iff₀ hN1]
    linarith
  -- the Kähler convex combination `(1 - t)φ + t u`
  set φt : F.carrier → EReal :=
    fun x => ((1 - (t : ℝ) : ℝ) : EReal) * φ x + ((t : ℝ) : EReal) * uR x with hφt
  have hφtpsh := isThetaPshPotential_convex_kahler F hφpsh hκ ht0R ht1
  have hφtA : HasManifoldAnalyticSingularityType (n := m + 1) φt := by
    have h := hasManifoldAnalyticSingularityType_add
      (hasManifoldAnalyticSingularityType_nonneg_rat_smul hφA ht1Q)
      (hasManifoldAnalyticSingularityType_nonneg_rat_smul huA.2 ht0.le)
    have hfun : (fun x => (((1 - t : ℚ) : ℝ) : EReal) * φ x + ((t : ℝ) : EReal) * uR x) = φt := by
      funext x
      simp [hφt]
    rwa [hfun] at h
  have hφtu : SingularityLE φt uR := by
    refine singularityLE_trans
      (singularityLE_add (singularityLE_smul hφu (by linarith : (0 : ℝ) ≤ 1 - (t : ℝ)))
        (singularityLE_refl (fun x => ((t : ℝ) : EReal) * uR x)))
      (singularityLE_of_eq fun x => ?_)
    rw [ereal_add_smul_self (by linarith) ht0R.le, sub_add_cancel, EReal.coe_one, one_mul]
  have hνt : flagValuation F φt =
      (1 - (t : ℝ)) • flagValuation F φ + (t : ℝ) • flagValuation F uR :=
    flagValuation_add_smul hφpsh huA.1 (by linarith) ht0R.le
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp
    (flagValuation_mem_closure_below_of_kahler F hS hφtpsh hφtA hφtu huA) (ε / 2) (by positivity)
  refine ⟨b, hb, ?_⟩
  have hd1 : dist (flagValuation F φ) (flagValuation F φt) < ε / 2 := by
    rw [dist_comm, dist_eq_norm, hνt]
    have : (1 - (t : ℝ)) • flagValuation F φ + (t : ℝ) • flagValuation F uR - flagValuation F φ =
        (t : ℝ) • (flagValuation F uR - flagValuation F φ) := by module
    rw [this, norm_smul, Real.norm_of_nonneg ht0R.le, ← hL]
    nlinarith [norm_nonneg (flagValuation F uR - flagValuation F φ)]
  calc dist (flagValuation F φ) b ≤ dist (flagValuation F φ) (flagValuation F φt) +
        dist (flagValuation F φt) b := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hd1 hdist
    _ = ε := add_halves ε

/-- **`tok:partial-analytic`** (DRWNXZ Lemma 5.3; conditional on Skoda's theorem
`ManifoldSkodaStatement`): for a Kähler current `R = θ + dd^c u` with analytic singularities,
`Δ(ξ; R) = closure ν(Ω(ξ; R)) = closure ν(𝒜(ξ; R))`. -/
theorem closure_gentleKahlerCurrentsBelow_eq (hS : ManifoldSkodaStatement.{u})
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {uR : F.carrier → EReal}
    (hu : IsKahlerCurrentPotential θ uR) (huA : uR ∈ analyticCurrents θ) :
    closure (flagValuation F '' gentleKahlerCurrentsBelow θ uR) =
      closure (flagValuation F '' analyticCurrentsBelow θ uR) := by
  refine le_antisymm (closure_mono (image_mono fun φ hφ => ⟨?_, hφ.2⟩)) ?_
  · exact gentleCurrents_subset_analyticCurrents θ hφ.1.1
  · refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨φ, hφ, rfl⟩
    exact flagValuation_mem_closure_below F hS hu huA hφ

/-- `tok:partial-analytic`, as the published statement (conditional on Skoda's theorem). -/
theorem partialAnalyticStatement_of_manifoldSkoda (hS : ManifoldSkodaStatement.{u}) :
    PartialAnalyticStatement.{u} :=
  fun _ F _ _ hu huA => closure_gentleKahlerCurrentsBelow_eq F hS hu huA

end SGPT.Okounkov.TranscendentalDensity
