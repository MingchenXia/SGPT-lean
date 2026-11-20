import SGPT.GAGA.OkoCloseBig
import SGPT.Okounkov.SourceSliceCorrection
import SGPT.Okounkov.ValuativeSliceBounded
import SGPT.Okounkov.MultiplierCancellation
import SGPT.Okounkov.SourceLexminTranslatedBody

/-!
# Perturbations of partial Okounkov bodies of currents

Lane OKO-NS, blueprint `claude-oko-ns.tex`. Transcendental input for the book's `prop:Deltapert`
and `lma:Hausconvbetato0` (chapter *The theory of Okounkov bodies*, Section *Algebraic partial
Okounkov bodies*), stated for the partial Okounkov body `Δ_{Y•}(θ + dd^c φ)` of a current
(`PartialBody.generalPartialBody`, the book's `def:generalPOB`) on an arbitrary flag geometry.
The algebraic statements (`SGPT.Okounkov.OkoNS` in `OkoNSAlgebraic`) identify the algebraic
bodies with these ones (`cor:transalgPOB`).

* `exists_hausdorffDist_le_of_antitone`: a decreasing family of compact sets `K_t` (`t ↓ 0`) with
  nonempty intersection `K₀` converges to `K₀` in the Hausdorff metric.
* `generalPartialBody_subset_of_semipositive`: `θ ≤ θ'` gives `Δ(θ; φ) ⊆ Δ(θ'; φ)`.
* `iInter_generalPartialBody_add_kahler`: `⋂_j Δ(θ + j⁻¹ ω; φ) = Δ(θ; φ)` for any Kähler `ω`.
* `exists_hausdorffDist_add_kahler_le`: `Δ(θ + t ω; φ) → Δ(θ; φ)` in the Hausdorff metric as
  `t ↓ 0` (Euclidean copies).
* `exists_one_sub_smul_bounds`, `exists_hausdorffDist_one_sub_smul_le`: if `θ + dd^c φ` is a
  Kähler current, there are `c ∈ ℕ_{>0}`, `x₀`, `y₀` with
  `Δ((1-β)θ; φ) + β x₀ ⊆ Δ(θ; φ)` and `(1 - cβ) Δ(θ; φ) + β y₀ ⊆ Δ((1-β)θ; φ)` for rational
  `0 < β < 1/c`; hence `d_Haus(Δ((1-β)θ; φ), Δ(θ; φ)) ≤ K β`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.OkoNS

open Set Filter MeasureTheory Metric
open scoped Pointwise Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody

/-! ### Decreasing families of compact sets -/

/-- **Hausdorff convergence of a decreasing family of compact sets**: if `K_t` (`t > 0`) is
increasing in `t`, contains `K₀`, consists of compact sets and `⋂_j K_{(j+1)⁻¹} = K₀`, then
`d_Haus(K_t, K₀) ≤ ε` for all small `t > 0`. -/
theorem exists_hausdorffDist_le_of_antitone {α : Type*} [MetricSpace α]
    (K : ℝ → Set α) (K₀ : Set α)
    (hmono : ∀ s t : ℝ, 0 < s → s ≤ t → K s ⊆ K t)
    (hsub : ∀ t : ℝ, 0 < t → K₀ ⊆ K t)
    (hcpt : ∀ t : ℝ, 0 < t → IsCompact (K t))
    (hinter : ⋂ j : ℕ, K ((j : ℝ) + 1)⁻¹ = K₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → hausdorffDist (K t) K₀ ≤ ε := by
  have hV : Directed (· ⊇ ·) (fun j : ℕ => K ((j : ℝ) + 1)⁻¹) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact hmono _ _ (by positivity)
        (inv_anti₀ (by positivity) (by gcongr; exact_mod_cast le_max_left i j))
    · exact hmono _ _ (by positivity)
        (inv_anti₀ (by positivity) (by gcongr; exact_mod_cast le_max_right i j))
  obtain ⟨J, hJ⟩ := exists_subset_nhds_of_isCompact' hV (fun j => hcpt _ (by positivity))
    (fun j => (hcpt _ (by positivity)).isClosed) (U := thickening ε K₀) (fun x hx => by
      have hx' : x ∈ K₀ := by rw [← hinter]; exact hx
      exact isOpen_thickening.mem_nhds (self_subset_thickening hε _ hx'))
  refine ⟨((J : ℝ) + 1)⁻¹, by positivity, fun t ht htJ => ?_⟩
  refine hausdorffDist_le_of_mem_dist hε.le (fun x hx => ?_)
    (fun x hx => ⟨x, hsub t ht hx, by rw [dist_self]; exact hε.le⟩)
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp (hJ (hmono t _ ht htJ hx))
  exact ⟨y, hy, hxy.le⟩

/-! ### Extended-real arithmetic -/

/-- `a x + b x = x` for `a, b > 0`, `a + b = 1`, on all of `EReal`. -/
theorem ereal_coe_mul_add_coe_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (x : EReal) : (a : EReal) * x + (b : EReal) * x = x := by
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ha, EReal.coe_mul_bot_of_pos hb, EReal.bot_add]
  | top => rw [EReal.coe_mul_top_of_pos ha, EReal.coe_mul_top_of_pos hb, EReal.top_add_top]
  | coe x => rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← add_mul, hab, one_mul]

/-- `x + β x ≤ x + β M` for `β ≥ 0` and `x ≤ M`. -/
theorem ereal_add_mul_le {β M : ℝ} (hβ : 0 ≤ β) {x : EReal} (hx : x ≤ (M : EReal)) :
    x + (β : EReal) * x ≤ x + ((β * M : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => simp
  | top => exact absurd hx (not_le.mpr (EReal.coe_lt_top M))
  | coe r =>
    rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hr : r ≤ M := EReal.coe_le_coe_iff.mp hx
    nlinarith

/-! ### Monotonicity and continuity in the class -/

section Flag

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)}

/-- `θ ≤ θ'` (i.e. `θ' - θ` semipositive) gives `Δ_{Y•}(θ + dd^c φ) ⊆ Δ_{Y•}(θ' + dd^c φ)`. -/
theorem generalPartialBody_subset_of_semipositive {θ θ' : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hle : (θ' - θ).val.IsSemipositive) :
    generalPartialBody F θ φ ⊆ generalPartialBody F θ' φ := by
  refine iInter_mono fun j => kahlerPartialBody_subset_of_le
    (isKahlerCurrentPotential_add_smul hφ F.omega (by positivity)) ?_
  have heq : θ' + ((j : ℝ) + 1)⁻¹ • F.omega.form - (θ + ((j : ℝ) + 1)⁻¹ • F.omega.form) =
      θ' - θ := by abel
  rwa [heq]

/-- `Δ_{Y•}(θ + dd^c φ) ⊆ Δ_{Y•}(θ + t ω + dd^c φ)` for a semipositive `ω` and `t ≥ 0`. -/
theorem generalPartialBody_subset_add_smul {θ ω : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) (hω : ω.val.IsSemipositive)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    generalPartialBody F (θ + s • ω) φ ⊆ generalPartialBody F (θ + t • ω) φ := by
  have hφs : IsThetaPshPotential (θ + s • ω).val φ := by
    refine TranscendentalBody.isThetaPshPotential_of_le hφ ?_
    rw [add_sub_cancel_left]
    exact KahlerDomination.isSemipositive_smul hω hs
  refine generalPartialBody_subset_of_semipositive hφs ?_
  have heq : θ + t • ω - (θ + s • ω) = (t - s) • ω := by module
  rw [heq]
  exact KahlerDomination.isSemipositive_smul hω (by linarith)

/-- `⋂_j Δ_{Y•}(θ + (j+1)⁻¹ ω + dd^c φ) = Δ_{Y•}(θ + dd^c φ)` for every Kähler form `ω`
(`def:generalPOB`, independence of the Kähler form). -/
theorem iInter_generalPartialBody_add_kahler {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (κ : KahlerBackground (m + 1) F.carrier) :
    ⋂ j : ℕ, generalPartialBody F (θ + ((j : ℝ) + 1)⁻¹ • κ.form) φ =
      generalPartialBody F θ φ := by
  rw [generalPartialBody_eq_of_kahler hφ κ]
  refine iInter_congr fun j => ?_
  exact generalPartialBody_eq_kahlerPartialBody
    (isKahlerCurrentPotential_add_smul hφ κ (by positivity))

/-- The Euclidean copy of a set. -/
theorem euclideanImage_def {k : ℕ} (A : Set (Fin k → ℝ)) :
    TranscendentalMain.euclideanImage A = (EuclideanSpace.equiv (Fin k) ℝ).symm '' A := rfl

/-- **Hausdorff continuity of `t ↦ Δ_{Y•}(θ + t ω + dd^c φ)` at `t = 0`** (Euclidean copies):
for every `ε > 0` there is `t₀ > 0` with
`d_Haus(Δ_{Y•}(θ + t ω + dd^c φ), Δ_{Y•}(θ + dd^c φ)) ≤ ε` for `0 < t ≤ t₀`. -/
theorem exists_hausdorffDist_add_kahler_le {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (κ : KahlerBackground (m + 1) F.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      hausdorffDist (TranscendentalMain.euclideanImage (generalPartialBody F (θ + t • κ.form) φ))
        (TranscendentalMain.euclideanImage (generalPartialBody F θ φ)) ≤ ε := by
  have hθ0 : θ + (0 : ℝ) • κ.form = θ := by rw [zero_smul, add_zero]
  refine exists_hausdorffDist_le_of_antitone
    (fun t => TranscendentalMain.euclideanImage (generalPartialBody F (θ + t • κ.form) φ))
    (TranscendentalMain.euclideanImage (generalPartialBody F θ φ))
    (fun s t hs hst => image_mono
      (generalPartialBody_subset_add_smul hφ κ.isSemipositive hs.le hst))
    (fun t ht => image_mono (by
      have h := generalPartialBody_subset_add_smul (F := F) hφ κ.isSemipositive le_rfl ht.le
      rwa [hθ0] at h))
    (fun t ht => ?_) ?_ hε
  · have hφt : IsThetaPshPotential (θ + t • κ.form).val φ := by
      refine TranscendentalBody.isThetaPshPotential_of_le hφ ?_
      rw [add_sub_cancel_left]
      exact KahlerDomination.isSemipositive_smul κ.isSemipositive ht.le
    exact (convex_isCompact_generalPartialBody (F := F) hφt).2.image
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous
  · simp only [euclideanImage_def]
    rw [← image_iInter (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.bijective,
      iInter_generalPartialBody_add_kahler hφ κ]

/-! ### Shrinking the class: `Δ((1 - β)θ; φ) → Δ(θ; φ)` -/

/-- **The two inclusions behind `lma:Hausconvbetato0`**: if `θ + dd^c φ` is a Kähler current,
there are `c ∈ ℕ_{>0}`, `x₀ ∈ Δ(θ; φ)` and `y₀` such that for every rational `β > 0` with
`c β < 1`: `φ ∈ PSH(X, (1 - β)θ)`, `Δ((1-β)θ; φ) + β x₀ ⊆ Δ(θ; φ)` and
`(1 - cβ) Δ(θ; φ) + β y₀ ⊆ Δ((1-β)θ; φ)`. -/
theorem exists_one_sub_smul_bounds {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    ∃ c : ℕ, 0 < c ∧ ∃ x₀ y₀ : Fin (m + 1) → ℝ, x₀ ∈ generalPartialBody F θ φ ∧
      ∀ β : ℚ, 0 < β → (c : ℚ) * β < 1 →
        IsThetaPshPotential ((1 - (β : ℝ)) • θ).val φ ∧
        (∀ z ∈ generalPartialBody F ((1 - (β : ℝ)) • θ) φ,
          z + (β : ℝ) • x₀ ∈ generalPartialBody F θ φ) ∧
        (∀ x ∈ generalPartialBody F θ φ,
          (1 - (c : ℝ) * β) • x + (β : ℝ) • y₀ ∈ generalPartialBody F ((1 - (β : ℝ)) • θ) φ) := by
  have : Nonempty F.carrier := PartialBody.nonempty_carrier F
  have hφθ : IsThetaPshPotential θ.val φ := isThetaPshPotential_of_isKahlerCurrentPotential hφ
  obtain ⟨κ, hκ⟩ := hφ
  obtain ⟨A, -, hAθ⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-θ)
  set c : ℕ := ⌈A⌉₊ + 1 with hc
  have hcA : A ≤ (c : ℝ) := by
    rw [hc]
    push_cast
    linarith [Nat.le_ceil A]
  have hcpos : 0 < c := by omega
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  -- `c φ ∈ PSH(X, (c - 1) θ)`
  have hcφ : IsThetaPshPotential (((c : ℝ) - 1) • θ).val (fun x => ((c : ℝ) : EReal) * φ x) := by
    refine TranscendentalBody.isThetaPshPotential_of_le
      (isThetaPshPotential_nonneg_smul hκ hcR.le) ?_
    have heq : ((c : ℝ) - 1) • θ - (c : ℝ) • (θ - κ.form) = -θ + (c : ℝ) • κ.form := by module
    rw [heq]
    exact KahlerDomination.isSemipositive_add_smul_mono κ.isSemipositive hcA hAθ
  obtain ⟨y₀, hy₀⟩ := nonempty_generalPartialBody (F := F) hcφ
  obtain ⟨x₀, hx₀⟩ := nonempty_generalPartialBody (F := F) hφθ
  obtain ⟨M, hM⟩ := hφθ.exists_global_upper_bound
  refine ⟨c, hcpos, x₀, y₀, hx₀, fun β hβ hcβ => ?_⟩
  have hβR : (0 : ℝ) < β := by exact_mod_cast hβ
  set t : ℚ := 1 - c * β with ht
  have htpos : 0 < t := by rw [ht]; linarith
  have htR : ((t : ℚ) : ℝ) = 1 - (c : ℝ) * β := by rw [ht]; push_cast; ring
  have htR' : (0 : ℝ) < t := by exact_mod_cast htpos
  -- lower inclusion: `Δ(tθ; tφ) + Δ((c-1)βθ; cβφ) ⊆ Δ((1-β)θ; φ)`
  have hφt : IsThetaPshPotential ((t : ℝ) • θ).val (fun x => ((t : ℝ) : EReal) * φ x) :=
    isThetaPshPotential_nonneg_smul hφθ htR'.le
  have hφβ : IsThetaPshPotential ((β : ℝ) • (((c : ℝ) - 1) • θ)).val
      (fun x => ((β : ℝ) : EReal) * (((c : ℝ) : EReal) * φ x)) :=
    isThetaPshPotential_nonneg_smul hcφ hβR.le
  have hform : (t : ℝ) • θ + (β : ℝ) • (((c : ℝ) - 1) • θ) = (1 - (β : ℝ)) • θ := by
    rw [htR, smul_smul, ← add_smul]
    congr 1
    ring
  have hfun : (fun x => ((t : ℝ) : EReal) * φ x +
      ((β : ℝ) : EReal) * (((c : ℝ) : EReal) * φ x)) = φ := by
    funext x
    rw [← mul_assoc, ← EReal.coe_mul]
    exact ereal_coe_mul_add_coe_mul htR' (mul_pos hβR hcR) (by rw [htR]; ring) (φ x)
  have hsum := isThetaPshPotential_add_from_positive_sum hφt hφβ
  rw [hform, hfun] at hsum
  have hlow := generalPartialBody_add_subset (F := F) hφt hφβ
  rw [hform, hfun, SGPT.GAGA.OkoClose.generalPartialBody_rat_smul hφθ htpos,
    SGPT.GAGA.OkoClose.generalPartialBody_rat_smul hcφ hβ] at hlow
  -- upper inclusion: `Δ((1-β)θ; φ) + Δ(βθ; βφ) ⊆ Δ(θ; φ + βφ) ⊆ Δ(θ; φ)`
  have hβφ : IsThetaPshPotential ((β : ℝ) • θ).val (fun x => ((β : ℝ) : EReal) * φ x) :=
    isThetaPshPotential_nonneg_smul hφθ hβR.le
  have hform2 : (1 - (β : ℝ)) • θ + (β : ℝ) • θ = θ := by
    rw [← add_smul, sub_add_cancel, one_smul]
  have hup := generalPartialBody_add_subset (F := F) hsum hβφ
  rw [hform2, SGPT.GAGA.OkoClose.generalPartialBody_rat_smul hφθ hβ] at hup
  have hsum2 := isThetaPshPotential_add_from_positive_sum hsum hβφ
  rw [hform2] at hsum2
  have hI : IOrderOnManifold (n := m + 1) (fun x => φ x + ((β : ℝ) : EReal) * φ x) φ :=
    iOrderOnManifold_of_le_add (C := (β : ℝ) * M) hφθ.1.quasiPlurisubharmonic
      (fun x => ereal_add_mul_le hβR.le (hM x))
  have hmono := Valuative.generalPartialBody_mono_of_iOrder hsum2 hφθ hI
  refine ⟨hsum, fun z hz => hmono (hup (add_mem_add hz (smul_mem_smul_set hx₀))),
    fun x hx => ?_⟩
  have h := hlow (add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy₀))
  rwa [htR] at h

/-- **`lma:Hausconvbetato0`, transcendental form**: if `θ + dd^c φ` is a Kähler current, there are
`c ∈ ℕ_{>0}` and `K ≥ 0` such that for every rational `β > 0` with `c β < 1`,
`φ ∈ PSH(X, (1 - β)θ)`, `vol Δ_{Y•}((1-β)θ + dd^c φ) > 0` and
`d_Haus(Δ_{Y•}((1-β)θ + dd^c φ), Δ_{Y•}(θ + dd^c φ)) ≤ K β` (Euclidean copies). -/
theorem exists_hausdorffDist_one_sub_smul_le {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    ∃ c : ℕ, 0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ β : ℚ, 0 < β → (c : ℚ) * β < 1 →
      IsThetaPshPotential ((1 - (β : ℝ)) • θ).val φ ∧
      0 < volume.real (generalPartialBody F ((1 - (β : ℝ)) • θ) φ) ∧
      hausdorffDist
        (TranscendentalMain.euclideanImage (generalPartialBody F ((1 - (β : ℝ)) • θ) φ))
        (TranscendentalMain.euclideanImage (generalPartialBody F θ φ)) ≤ K * β := by
  let e := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
  have hφθ : IsThetaPshPotential θ.val φ := isThetaPshPotential_of_isKahlerCurrentPotential hφ
  obtain ⟨c, hcpos, x₀, y₀, hx₀, hbd⟩ := exists_one_sub_smul_bounds (F := F) hφ
  have hcpt := (convex_isCompact_generalPartialBody (F := F) hφθ).2
  obtain ⟨R, hR⟩ := (hcpt.image e.continuous).isBounded.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR _ ⟨x₀, hx₀, rfl⟩)
  -- positive volume of `Δ(θ; φ)`
  have hvol : 0 < volume.real (generalPartialBody F θ φ) := by
    have hint := SourceLexmin.interior_generalPartialBody_nonempty_of_kahler F hφ
    have hne := MeasureTheory.Measure.measure_pos_of_nonempty_interior volume hint
    rw [measureReal_def]
    exact ENNReal.toReal_pos hne.ne' hcpt.measure_lt_top.ne
  refine ⟨c, hcpos, max ‖e x₀‖ ((c : ℝ) * R + ‖e y₀‖), le_max_of_le_left (norm_nonneg _),
    fun β hβ hcβ => ?_⟩
  obtain ⟨hφβ, hup, hlow⟩ := hbd β hβ hcβ
  have hβR : (0 : ℝ) < β := by exact_mod_cast hβ
  have hcβR : (c : ℝ) * β < 1 := by exact_mod_cast hcβ
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  refine ⟨hφβ, ?_, ?_⟩
  · -- `(1 - cβ) Δ(θ; φ) + β y₀ ⊆ Δ((1-β)θ; φ)`
    have hcpt' := (convex_isCompact_generalPartialBody (F := F) hφβ).2
    have hsub : (fun x => (1 - (c : ℝ) * β) • x + (β : ℝ) • y₀) '' generalPartialBody F θ φ ⊆
        generalPartialBody F ((1 - (β : ℝ)) • θ) φ := by
      rintro _ ⟨x, hx, rfl⟩
      exact hlow x hx
    have himg : (fun x => (1 - (c : ℝ) * β) • x + (β : ℝ) • y₀) '' generalPartialBody F θ φ =
        (fun x => x + (β : ℝ) • y₀) '' ((1 - (c : ℝ) * β) • generalPartialBody F θ φ) := by
      rw [← image_smul, image_image]
    have hvol' : volume ((fun x => (1 - (c : ℝ) * β) • x + (β : ℝ) • y₀) ''
        generalPartialBody F θ φ) =
        ENNReal.ofReal |(1 - (c : ℝ) * β) ^ (m + 1)| * volume (generalPartialBody F θ φ) := by
      rw [himg, image_add_right, measure_preimage_add_right, Measure.addHaar_smul,
        Module.finrank_fin_fun]
    have hvol0 : volume (generalPartialBody F θ φ) ≠ 0 := by
      intro h
      rw [measureReal_def, h, ENNReal.toReal_zero] at hvol
      exact lt_irrefl _ hvol
    rw [measureReal_def]
    refine ENNReal.toReal_pos ?_ (hcpt'.measure_lt_top.ne)
    refine (lt_of_lt_of_le ?_ (measure_mono hsub)).ne'
    rw [hvol']
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (abs_pos.mpr (pow_ne_zero _ (sub_pos.mpr hcβR).ne'))).ne' hvol0
  · refine hausdorffDist_le_of_mem_dist (by positivity) ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨e (z + (β : ℝ) • x₀), ⟨_, hup z hz, rfl⟩, ?_⟩
      rw [dist_eq_norm, map_add, sub_add_cancel_left, norm_neg, map_smul, norm_smul,
        Real.norm_of_nonneg hβR.le]
      exact (mul_comm (β : ℝ) ‖e x₀‖).trans_le
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hβR.le)
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨e ((1 - (c : ℝ) * β) • x + (β : ℝ) • y₀), ⟨_, hlow x hx, rfl⟩, ?_⟩
      have hxR : ‖e x‖ ≤ R := hR _ ⟨x, hx, rfl⟩
      have heq : e x - e ((1 - (c : ℝ) * β) • x + (β : ℝ) • y₀) =
          ((c : ℝ) * β) • e x - (β : ℝ) • e y₀ := by
        rw [map_add, map_smul, map_smul, sub_smul, one_smul]
        abel
      rw [dist_eq_norm, heq]
      calc ‖((c : ℝ) * β) • e x - (β : ℝ) • e y₀‖
          ≤ ‖((c : ℝ) * β) • e x‖ + ‖(β : ℝ) • e y₀‖ := norm_sub_le _ _
        _ = (c : ℝ) * β * ‖e x‖ + β * ‖e y₀‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
              Real.norm_of_nonneg hβR.le]
        _ ≤ (c : ℝ) * β * R + β * ‖e y₀‖ := by gcongr
        _ = ((c : ℝ) * R + ‖e y₀‖) * β := by ring
        _ ≤ max ‖e x₀‖ ((c : ℝ) * R + ‖e y₀‖) * β :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hβR.le

end Flag

end SGPT.Okounkov.OkoNS
