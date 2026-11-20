import SGPT.Okounkov.TranscendentalSlice
import SGPT.Okounkov.TranscendentalCoreGentleSum
import SGPT.Okounkov.TranscendentalBodyBasic

/-!
# The range of the first coordinate and the density of slices

Source: blueprint nodes `tok:nu1-closure` (DRWNXZ Lemma 7.1) and `tok:slice-density` (DRWNXZ
Lemma 7.4) of chapter `claude-okounkov-transcendental`; Darvas--Reboulet--Witt
Nyström--Xia--Zhang, *Transcendental Okounkov bodies*.

Let `X` be a connected compact Kähler manifold of dimension `m + 1` with a smooth flag and
`ξ = {θ}` a big class. Put `ν_min = inf_{T ∈ Ω(ξ)} ν(T, Y₁)` and
`ν_max = sup_{T ∈ Ω(ξ)} ν(T, Y₁)` (`firstValuationMin`, `firstValuationMax`).

* `firstValuationMin_lt_firstValuationMax` and `image_first_tradOkounkovBody_eq_Icc`
  (**`tok:nu1-closure`**): `ν_min < ν_max`, and the projection of `Δ(ξ)` to the first
  coordinate is `[ν_min, ν_max]`. For the strict inequality, a gentle Kähler current
  `T = θ + dd^c φ ≥ ω'` is also a Kähler current in `ξ - ε{Y₁}` for small rational `ε > 0`,
  and `T + ε[Y₁] ∈ 𝒜(ξ)` has first coordinate `ν(T, Y₁) + ε`; by `tok:density` this value is at
  most `ν_max`. (This replaces the Siu-decomposition argument of DRWNXZ; no subtraction of
  divisors is needed.)
* `slice_eq_closure_fixedFirst` (**`tok:slice-density`**): for rational
  `t ∈ (ν_min, ν_max)`, `{t} × Δ_t(ξ) = closure ν(Ω_t) = closure ν(𝒜_t)`, where `Ω_t`, `𝒜_t`
  are the currents with `ν(T, Y₁) = t`: a current `T ∈ Ω` with `ν(T)` close to `(t, a)` is
  combined, with rational coefficients, with a current `S ∈ Ω` whose first coordinate lies on
  the other side of `t` (`tok:gentle-sum`, `tok:valuation-analytic`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalSlice

open Set Filter Metric
open scoped Topology Manifold ContDiff NNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The first coordinates `ν(T, Y₁)` of the gentle Kähler currents `T ∈ Ω(ξ)`. -/
def firstValuations (θ : ClosedRealOneOneForm (m + 1) F.carrier) : Set ℝ :=
  (fun φ => flagValuation F φ 0) '' gentleKahlerCurrents θ

/-- `ν_min(ξ) = inf_{T ∈ Ω(ξ)} ν(T, Y₁)` (DRWNXZ §7). -/
def firstValuationMin (θ : ClosedRealOneOneForm (m + 1) F.carrier) : ℝ :=
  sInf (firstValuations F θ)

/-- `ν_max(ξ) = sup_{T ∈ Ω(ξ)} ν(T, Y₁)` (DRWNXZ §7). -/
def firstValuationMax (θ : ClosedRealOneOneForm (m + 1) F.carrier) : ℝ :=
  sSup (firstValuations F θ)

variable {F}

theorem firstValuations_nonempty {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    (firstValuations F θ).Nonempty :=
  (SGPT.Okounkov.TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig).image _

theorem bddBelow_firstValuations (θ : ClosedRealOneOneForm (m + 1) F.carrier) :
    BddBelow (firstValuations F θ) :=
  ⟨0, by rintro _ ⟨φ, -, rfl⟩; exact flagValuation_nonneg φ 0⟩

theorem bddAbove_firstValuations (θ : ClosedRealOneOneForm (m + 1) F.carrier) :
    BddAbove (firstValuations F θ) := by
  obtain ⟨C, -, hC⟩ := SGPT.Okounkov.TranscendentalBody.exists_flagValuation_le (F := F) θ
  exact ⟨C, by rintro _ ⟨φ, hφ, rfl⟩; exact hC φ hφ.1.1 0⟩

/-- The projection of `Δ(ξ)` to the first coordinate is the closure of the first coordinates
of `ν(Ω(ξ))`. -/
theorem image_first_tradOkounkovBody_eq_closure {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    (fun x : Fin (m + 1) → ℝ => x 0) '' tradOkounkovBody F θ = closure (firstValuations F θ) := by
  have hΔ := SGPT.Okounkov.TranscendentalDensity.tradOkounkovBody_eq_closure_gentleKahlerCurrents
    hbig
  have hcont : Continuous fun x : Fin (m + 1) → ℝ => x 0 := continuous_apply 0
  have himg : (fun x : Fin (m + 1) → ℝ => x 0) '' (flagValuation F '' gentleKahlerCurrents θ) =
      firstValuations F θ := by
    rw [image_image]; rfl
  apply Subset.antisymm
  · rw [hΔ, ← himg]
    exact image_closure_subset_closure_image hcont
  · have hcpt : IsCompact ((fun x : Fin (m + 1) → ℝ => x 0) '' tradOkounkovBody F θ) :=
      (SGPT.Okounkov.TranscendentalBody.isCompact_tradOkounkovBody θ).image hcont
    refine closure_minimal ?_ hcpt.isClosed
    rw [← himg]
    exact image_mono (image_gentleKahlerCurrents_subset_tradOkounkovBody θ)

/-- **Blueprint `tok:nu1-closure`, second part** (DRWNXZ Lemma 7.1): the projection of `Δ(ξ)`
to the first coordinate is `[ν_min, ν_max]`. -/
theorem image_first_tradOkounkovBody_eq_Icc {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    (fun x : Fin (m + 1) → ℝ => x 0) '' tradOkounkovBody F θ =
      Icc (firstValuationMin F θ) (firstValuationMax F θ) := by
  have hne := firstValuations_nonempty hbig
  have hb := bddBelow_firstValuations (F := F) θ
  have ha := bddAbove_firstValuations (F := F) θ
  set P := (fun x : Fin (m + 1) → ℝ => x 0) '' tradOkounkovBody F θ with hPdef
  have hP : P = closure (firstValuations F θ) := image_first_tradOkounkovBody_eq_closure hbig
  apply Subset.antisymm
  · rw [hP]
    refine closure_minimal (fun a ha' => ⟨csInf_le hb ha', le_csSup ha ha'⟩) isClosed_Icc
  · have hconv : Convex ℝ P := by
      rw [hPdef]
      exact (SGPT.Okounkov.TranscendentalBody.convex_tradOkounkovBody θ).linear_image
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) 0)
    have hmin : firstValuationMin F θ ∈ P := hP ▸ csInf_mem_closure hne hb
    have hmax : firstValuationMax F θ ∈ P := hP ▸ csSup_mem_closure hne ha
    exact hconv.ordConnected.out hmin hmax

/-- **Blueprint `tok:nu1-closure`, first part** (DRWNXZ Lemma 7.1): `ν_min < ν_max`. -/
theorem firstValuationMin_lt_firstValuationMax {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    firstValuationMin F θ < firstValuationMax F θ := by
  obtain ⟨φ, hφ⟩ :=
    SGPT.Okounkov.TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig
  obtain ⟨D, hDI, E, hEW, hmetric, -, -⟩ :=
    SGPT.Okounkov.exists_normalized_smooth_divisor_residual_generic_zero hφ.1.1 F.firstDivisor
  have hE : TranscendentalMain.IsFirstDivisorUnitMetric F E := ⟨D, hDI, hEW, hmetric⟩
  obtain ⟨ω', hω'⟩ := hφ.2
  obtain ⟨t₀, ht₀, hkah⟩ := exists_pos_forall_kahler_sub ω' E.curvature
  obtain ⟨ε, hε0, hεt⟩ := exists_rat_btwn ht₀
  have hε0' : (0 : ℚ) < ε := by exact_mod_cast hε0
  obtain ⟨κ, hκ⟩ := hkah ε ⟨hε0, hεt⟩
  -- `φ` is a gentle Kähler current in `ξ - ε{Y₁}`
  have hφε : φ ∈ analyticCurrents (θ - (ε : ℝ) • E.curvature) := by
    have hpsh : IsThetaPshPotential ((θ - (ε : ℝ) • E.curvature) - κ.form).val φ := by
      have : (θ - (ε : ℝ) • E.curvature) - κ.form = θ - ω'.form := by rw [hκ]; abel
      rw [this]; exact hω'
    refine gentleCurrents_subset_analyticCurrents _ ⟨?_, hφ.1.2⟩
    refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hpsh ?_
    rw [sub_sub_cancel]
    exact κ.isSemipositive
  -- `φ + ε ψ_E ∈ 𝒜(ξ)` with first coordinate `ν(φ, Y₁) + ε`
  have hΦ := add_smul_mem_analyticCurrents hφε (weight_mem_analyticCurrents hE)
    (a := 1) (b := ε) zero_le_one hε0'.le
  simp only [Rat.cast_one, one_smul, sub_add_cancel, EReal.coe_one, one_mul] at hΦ
  have hν := flagValuation_add_smul (F := F) hφε.1 (weight_mem_analyticCurrents hE).1
    (a := (1 : ℝ)) (b := (ε : ℝ)) zero_le_one hε0.le
  rw [flagValuation_weight hE] at hν
  simp only [EReal.coe_one, one_mul, one_smul] at hν
  have hν0 : flagValuation F (fun x => φ x + ((ε : ℝ) : EReal) * E.weight x) 0 =
      flagValuation F φ 0 + ε := by
    rw [hν]; simp
  have hmem := SGPT.Okounkov.TranscendentalDensity.densityStatement (m + 1) F θ ⟨φ, hφ⟩ _ hΦ
  have hmem0 : flagValuation F (fun x => φ x + ((ε : ℝ) : EReal) * E.weight x) 0 ∈
      closure (firstValuations F θ) := by
    have h := image_closure_subset_closure_image (continuous_apply (0 : Fin (m + 1)))
      (mem_image_of_mem _ hmem)
    rwa [image_image] at h
  have hle : flagValuation F φ 0 + ε ≤ firstValuationMax F θ := by
    rw [← hν0]
    exact closure_minimal (fun a ha => le_csSup (bddAbove_firstValuations θ) ha) isClosed_Iic
      hmem0
  have hmin : firstValuationMin F θ ≤ flagValuation F φ 0 :=
    csInf_le (bddBelow_firstValuations θ) ⟨φ, hφ, rfl⟩
  linarith

/-- A convex combination `λ u + μ v` (`λ + μ = 1`, `λ, μ ≥ 0`) is at distance at most
`d(u, x) + μ d(v, x)` from `x`. -/
theorem dist_combo_le {n : ℕ} (x u v : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : dist (a • u + b • v) x ≤ dist u x + b * dist v x := by
  have heq : a • u + b • v - x = a • (u - x) + b • (v - x) := by
    have : x = (a + b) • x := by rw [hab, one_smul]
    conv_lhs => rw [this]
    simp only [smul_sub, add_smul]
    abel
  rw [dist_eq_norm, heq, dist_eq_norm, dist_eq_norm]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have ha1 : a ≤ 1 := by linarith
  have := norm_nonneg (u - x)
  nlinarith

/-- **Moving the first coordinate to `t`**: if `T, P ∈ Ω(ξ)` have rational first coordinates
`q`, `p` on opposite sides of the rational `t` (or `q = t`), a rational convex combination
`S ∈ Ω(ξ)` of `T` and `P` has first coordinate `t` and
`d(ν(S), x) ≤ d(ν(T), x) + |q - t| / |t - p| · d(ν(P), x)`. -/
theorem exists_mem_fixedFirst_near {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {T P : F.carrier → EReal} (hT : T ∈ gentleKahlerCurrents θ)
    (hP : P ∈ gentleKahlerCurrents θ) {q p t : ℚ} (hq : flagValuation F T 0 = q)
    (hp : flagValuation F P 0 = p) (hside : (p < t ∧ t ≤ q) ∨ (q < t ∧ t < p))
    (x : Fin (m + 1) → ℝ) :
    ∃ S ∈ gentleKahlerCurrents θ, flagValuation F S 0 = t ∧
      dist (flagValuation F S) x ≤
        dist (flagValuation F T) x + |(q : ℝ) - t| / |(t : ℝ) - p| * dist (flagValuation F P) x := by
  have hqp : q - p ≠ 0 := by rcases hside with h | h <;> intro h0 <;> linarith [h.1, h.2]
  set a : ℚ := (t - p) / (q - p) with ha_def
  set b : ℚ := (q - t) / (q - p) with hb_def
  have hab : a + b = 1 := by rw [ha_def, hb_def, ← add_div]; field_simp; ring
  have ha : 0 < a := by
    rcases hside with h | h
    · exact div_pos (by linarith [h.1]) (by linarith [h.1, h.2])
    · exact div_pos_of_neg_of_neg (by linarith [h.2]) (by linarith [h.1, h.2])
  have hb : 0 ≤ b := by
    rcases hside with h | h
    · exact div_nonneg (by linarith [h.2]) (by linarith [h.1, h.2])
    · exact div_nonneg_of_nonpos (by linarith [h.1]) (by linarith [h.1, h.2])
  have hS := add_smul_mem_gentleKahlerCurrents hT (gentleKahlerCurrents_subset_gentleCurrents hP)
    ha hb
  have hform : (a : ℝ) • θ + (b : ℝ) • θ = θ := by
    have h1 : (a : ℝ) + b = 1 := by exact_mod_cast hab
    rw [← add_smul, h1, one_smul]
  rw [hform] at hS
  have hν := flagValuation_add_smul (F := F) hT.1.1 hP.1.1 (a := (a : ℝ)) (b := (b : ℝ))
    (by exact_mod_cast ha.le) (by exact_mod_cast hb)
  refine ⟨_, hS, ?_, ?_⟩
  · rw [hν]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq, hp]
    have : (a : ℝ) * q + (b : ℝ) * p = t := by
      have h : a * q + b * p = t := by
        rw [ha_def, hb_def]; field_simp; ring
      exact_mod_cast h
    exact this
  · rw [hν]
    refine (dist_combo_le x _ _ (by exact_mod_cast ha.le) (by exact_mod_cast hb)
      (by exact_mod_cast hab)).trans ?_
    gcongr
    have hb' : (b : ℝ) = ((q : ℝ) - t) / ((q : ℝ) - p) := by rw [hb_def]; push_cast; ring
    rw [hb']
    rcases hside with h | h
    · have h1 : (p : ℝ) < t := by exact_mod_cast h.1
      have h2 : (t : ℝ) ≤ q := by exact_mod_cast h.2
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ q - t), abs_of_pos (by linarith : (0 : ℝ) < t - p)]
      exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
    · have h1 : (q : ℝ) < t := by exact_mod_cast h.1
      have h2 : (t : ℝ) < p := by exact_mod_cast h.2
      rw [abs_of_neg (by linarith : (q : ℝ) - t < 0), abs_of_neg (by linarith : (t : ℝ) - p < 0)]
      rw [show ((q : ℝ) - t) / (q - p) = (t - q) / (p - q) by
        rw [← neg_sub (t : ℝ) q, ← neg_sub (p : ℝ) q, neg_div_neg_eq]]
      rw [neg_sub, neg_sub]
      exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)

/-- **Blueprint `tok:slice-density`** (DRWNXZ Lemma 7.4): for a big class `ξ = {θ}` and a
rational `t ∈ (ν_min, ν_max)`, `{t} × Δ_t(ξ) = closure ν(Ω_t) = closure ν(𝒜_t)`, where
`{t} × Δ_t(ξ) = {x ∈ Δ(ξ) : x₀ = t}` and `Ω_t`, `𝒜_t` are the currents of `Ω(ξ)`, `𝒜(ξ)` with
`ν(T, Y₁) = t`. -/
theorem slice_eq_closure_fixedFirst {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) {t : ℚ}
    (h₁ : firstValuationMin F θ < t) (h₂ : (t : ℝ) < firstValuationMax F θ) :
    {x ∈ tradOkounkovBody F θ | x 0 = t} =
        closure (flagValuation F '' {φ ∈ gentleKahlerCurrents θ | flagValuation F φ 0 = t}) ∧
      {x ∈ tradOkounkovBody F θ | x 0 = t} =
        closure (flagValuation F '' {φ ∈ analyticCurrents θ | flagValuation F φ 0 = t}) := by
  have hΔ := SGPT.Okounkov.TranscendentalDensity.tradOkounkovBody_eq_closure_gentleKahlerCurrents
    hbig
  have hΩne := SGPT.Okounkov.TranscendentalBody.exists_mem_gentleKahlerCurrents_of_isBig hbig
  have hclosed : IsClosed {x ∈ tradOkounkovBody F θ | x 0 = (t : ℝ)} :=
    (isClosed_tradOkounkovBody θ).inter (isClosed_eq (continuous_apply 0) continuous_const)
  have hΩA : ∀ {φ}, φ ∈ gentleKahlerCurrents θ → φ ∈ analyticCurrents θ := fun hφ =>
    gentleCurrents_subset_analyticCurrents _ (gentleKahlerCurrents_subset_gentleCurrents hφ)
  have hsub1 : closure (flagValuation F '' {φ ∈ gentleKahlerCurrents θ | flagValuation F φ 0 = t})
      ⊆ closure (flagValuation F '' {φ ∈ analyticCurrents θ | flagValuation F φ 0 = t}) :=
    closure_mono (image_mono fun φ hφ => ⟨hΩA hφ.1, hφ.2⟩)
  have hsub2 : closure (flagValuation F '' {φ ∈ analyticCurrents θ | flagValuation F φ 0 = t})
      ⊆ {x ∈ tradOkounkovBody F θ | x 0 = t} := by
    refine closure_minimal ?_ hclosed
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨?_, hφ.2⟩
    rw [hΔ]
    exact SGPT.Okounkov.TranscendentalDensity.densityStatement (m + 1) F θ hΩne φ hφ.1
  have hsub3 : {x ∈ tradOkounkovBody F θ | x 0 = t} ⊆
      closure (flagValuation F '' {φ ∈ gentleKahlerCurrents θ | flagValuation F φ 0 = t}) := by
    rintro x ⟨hxΔ, hx0⟩
    obtain ⟨_, ⟨S, hS, rfl⟩, hSt⟩ :=
      exists_lt_of_csInf_lt (firstValuations_nonempty hbig) h₁
    obtain ⟨_, ⟨G, hG, rfl⟩, hGt⟩ :=
      exists_lt_of_lt_csSup (firstValuations_nonempty hbig) h₂
    obtain ⟨ss, -, hss⟩ := flagValuation_rational_of_analytic _ F θ S (hΩA hS) 0
    obtain ⟨gg, -, hgg⟩ := flagValuation_rational_of_analytic _ F θ G (hΩA hG) 0
    simp only [hss] at hSt
    simp only [hgg] at hGt
    set d : ℝ := min ((t : ℝ) - ss) ((gg : ℝ) - t) with hd_def
    have hd : 0 < d := lt_min (by linarith) (by linarith)
    set K : ℝ := dist (flagValuation F S) x + dist (flagValuation F G) x with hK_def
    have hK : 0 ≤ K := add_nonneg dist_nonneg dist_nonneg
    have hpos : 0 < 1 + K / d := by positivity
    rw [Metric.mem_closure_iff]
    intro ε hε
    rw [hΔ] at hxΔ
    obtain ⟨_, ⟨T, hT, rfl⟩, hTx⟩ := Metric.mem_closure_iff.mp hxΔ (ε / (1 + K / d))
      (div_pos hε hpos)
    obtain ⟨qq, -, hqq⟩ := flagValuation_rational_of_analytic _ F θ T (hΩA hT) 0
    have hqt : |(qq : ℝ) - t| ≤ dist (flagValuation F T) x := by
      have := dist_le_pi_dist (flagValuation F T) x 0
      rwa [Real.dist_eq, hqq, hx0] at this
    have hfin : dist (flagValuation F T) x * (1 + K / d) < ε := by
      rw [dist_comm] at hTx
      exact (lt_div_iff₀ hpos).mp hTx
    have hbound : ∀ (P : F.carrier → EReal) (p : ℚ), d ≤ |(t : ℝ) - p| →
        dist (flagValuation F P) x ≤ K →
        dist (flagValuation F T) x + |(qq : ℝ) - t| / |(t : ℝ) - p| * dist (flagValuation F P) x
          < ε := by
      intro P p hdp hPK
      have e1 : |(qq : ℝ) - t| / |(t : ℝ) - p| ≤ dist (flagValuation F T) x / d :=
        div_le_div₀ dist_nonneg hqt hd hdp
      have e2 := mul_le_mul e1 hPK dist_nonneg (div_nonneg dist_nonneg hd.le)
      calc dist (flagValuation F T) x + |(qq : ℝ) - t| / |(t : ℝ) - p| * dist (flagValuation F P) x
          ≤ dist (flagValuation F T) x + dist (flagValuation F T) x / d * K := by linarith
        _ = dist (flagValuation F T) x * (1 + K / d) := by ring
        _ < ε := hfin
    by_cases hc : (t : ℝ) ≤ qq
    · obtain ⟨S', hS', hS'0, hS'd⟩ := exists_mem_fixedFirst_near hT hS hqq hss
        (Or.inl ⟨by exact_mod_cast hSt, by exact_mod_cast hc⟩) x
      refine ⟨_, ⟨S', ⟨hS', hS'0⟩, rfl⟩, ?_⟩
      rw [dist_comm]
      refine hS'd.trans_lt (hbound S ss ?_ (le_add_of_nonneg_right dist_nonneg))
      rw [abs_of_pos (by linarith)]
      exact min_le_left _ _
    · push Not at hc
      obtain ⟨S', hS', hS'0, hS'd⟩ := exists_mem_fixedFirst_near hT hG hqq hgg
        (Or.inr ⟨by exact_mod_cast hc, by exact_mod_cast hGt⟩) x
      refine ⟨_, ⟨S', ⟨hS', hS'0⟩, rfl⟩, ?_⟩
      rw [dist_comm]
      refine hS'd.trans_lt (hbound G gg ?_ (le_add_of_nonneg_left dist_nonneg))
      rw [abs_of_neg (by linarith), neg_sub]
      exact min_le_right _ _
  exact ⟨Subset.antisymm hsub3 (hsub1.trans hsub2), Subset.antisymm (hsub3.trans hsub1) hsub2⟩

end SGPT.Okounkov.TranscendentalSlice
