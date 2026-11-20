import SGPT.Unibranch.FNLLine

/-!
# FN80 Lemma 5.1: lifting along the universal covering of the punctured disc

Source: `[FN80]` Lemma 5.1, proof (the Puiseux parametrization of the branches of
`π⁻¹(L)` at the points over a branch point).

Over the punctured disc `0 < |τ| < ρ` of a line `z₀ + τ e` meeting `{δ = 0}` only at `z₀`,
`X` is a finite covering (`isCoveringMap_lineProj`).  Pulling it back along the universal
covering `exp : {Re w < log ρ} → {0 < |τ| < ρ}` (a simply connected half plane) it becomes
trivial: there are `λ` continuous lifts `w ↦ L x w`, one through each point `x` of a reference
fibre, which enumerate all fibres (`exists_periodic_lifts`).  The deck translation
`w ↦ w + 2πi` permutes the lifts (monodromy); a power `M` of the monodromy permutation is the
identity, so every lift is `2πiM`-periodic.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace Complex
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n k : ℕ}
variable {X : Set (ComplexModel n)} {π : ComplexModel n →L[ℂ] ComplexModel k}
  {D : Set (ComplexModel k)} {deg : ℕ} {δ : ComplexModel k → ℂ}

/-- The half plane `Re w < log ρ`; `exp` maps it onto the punctured disc of radius `ρ`. -/
def halfPlane (ρ : ℝ) : Set ℂ := {w | w.re < Real.log ρ}

theorem isOpen_halfPlane (ρ : ℝ) : IsOpen (halfPlane ρ) :=
  isOpen_lt Complex.continuous_re continuous_const

theorem add_mem_halfPlane {ρ : ℝ} {w : ℂ} (hw : w ∈ halfPlane ρ) (t : ℝ) :
    w + t * I ∈ halfPlane ρ := by
  simpa [halfPlane] using hw

instance contractibleSpace_halfPlane (ρ : ℝ) : ContractibleSpace (halfPlane ρ) :=
  (convex_halfSpace_re_lt (r := Real.log ρ)).contractibleSpace
    ⟨((Real.log ρ - 1 : ℝ) : ℂ), by simp⟩

instance locallyPathConnectedSpace_halfPlane (ρ : ℝ) :
    LocallyPathConnectedSpace (halfPlane ρ) :=
  (isOpen_halfPlane ρ).locallyPathConnectedSpace

theorem exp_mem_punctured {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : w ∈ halfPlane ρ) :
    exp w ∈ punctured ρ :=
  ⟨exp_ne_zero w, by rw [norm_exp]; exact (Real.lt_log_iff_exp_lt hρ).mp hw⟩

/-- The universal covering `exp` of the punctured disc. -/
def expMap {ρ : ℝ} (hρ : 0 < ρ) : C(halfPlane ρ, punctured ρ) :=
  ⟨fun w => ⟨exp w.val, exp_mem_punctured hρ w.property⟩,
    (continuous_exp.comp continuous_subtype_val).subtype_mk _⟩

theorem exp_add_two_pi_I_mul_int (w : ℂ) (j : ℤ) : exp (w + 2 * Real.pi * I * j) = exp w := by
  rw [exp_add, show 2 * Real.pi * I * j = (j : ℂ) * (2 * Real.pi * I) by ring,
    exp_int_mul_two_pi_mul_I, mul_one]

/-- A logarithm, continuous near a given nonzero point. -/
theorem exists_local_log {s₁ : ℂ} (hs₁ : s₁ ≠ 0) :
    ∃ ℓ : ℂ → ℂ, ContinuousAt ℓ s₁ ∧ ∀ᶠ s in 𝓝 s₁, exp (ℓ s) = s := by
  have hne : ∀ᶠ s in 𝓝 s₁, s ≠ 0 := isOpen_ne.mem_nhds hs₁
  rcases mem_slitPlane_or_neg_mem_slitPlane hs₁ with h | h
  · exact ⟨log, continuousAt_clog h, hne.mono fun s hs => exp_log hs⟩
  · refine ⟨fun s => log (-s) + Real.pi * I, ?_, ?_⟩
    · exact (ContinuousAt.comp (f := fun s : ℂ => -s) (continuousAt_clog h)
        continuousAt_neg).add continuousAt_const
    · filter_upwards [hne] with s hs
      rw [exp_add, exp_log (neg_ne_zero.mpr hs), exp_pi_mul_I]
      ring

namespace IsBranchedCovering

variable (hX : IsBranchedCovering X π D deg δ)
include hX

section line

variable {z₀ e : ComplexModel k} {ρ : ℝ}
  (hline : ∀ τ : ℂ, ‖τ‖ ≤ ρ → z₀ + τ • e ∈ D)
  (hgen : ∀ τ : ℂ, τ ≠ 0 → ‖τ‖ ≤ ρ → δ (z₀ + τ • e) ≠ 0)

include hline hgen in
/-- Continuous lifts of `exp` through the covering over the punctured line, one through each
point of the fibre over `exp w₀`, with uniqueness. -/
theorem exists_lifts (hρ : 0 < ρ) (w₀ : ℂ) (hw₀ : w₀ ∈ halfPlane ρ) :
    ∃ L : ComplexModel n → ℂ → ComplexModel n,
      (∀ x ∈ fibre X π (z₀ + exp w₀ • e), L x w₀ = x) ∧
      (∀ x ∈ fibre X π (z₀ + exp w₀ • e), ContinuousOn (L x) (halfPlane ρ)) ∧
      (∀ x ∈ fibre X π (z₀ + exp w₀ • e), ∀ w ∈ halfPlane ρ,
        L x w ∈ fibre X π (z₀ + exp w • e)) ∧
      ∀ x ∈ fibre X π (z₀ + exp w₀ • e), ∀ Φ : ℂ → ComplexModel n,
        ContinuousOn Φ (halfPlane ρ) → (∀ w ∈ halfPlane ρ, Φ w ∈ fibre X π (z₀ + exp w • e)) →
        ∀ w₁ ∈ halfPlane ρ, Φ w₁ = L x w₁ → ∀ w ∈ halfPlane ρ, Φ w = L x w := by
  classical
  have cov := hX.isCoveringMap_lineProj hline hgen
  set F₀ := fibre X π (z₀ + exp w₀ • e) with hF₀def
  let pt : ∀ x ∈ F₀, lineTotal X π z₀ e ρ := fun x hx =>
    ⟨(exp w₀, x), exp_mem_punctured hρ hw₀, hx.1, hx.2⟩
  have hex : ∀ x (hx : x ∈ F₀), ∃ F : C(halfPlane ρ, lineTotal X π z₀ e ρ),
      F ⟨w₀, hw₀⟩ = pt x hx ∧ lineProj X π z₀ e ρ ∘ F = expMap hρ := fun x hx =>
    (cov.existsUnique_continuousMap_lifts (expMap hρ) ⟨w₀, hw₀⟩ (pt x hx) rfl).exists
  choose Fl hFl using hex
  have hfst : ∀ x (hx : x ∈ F₀) (w : halfPlane ρ), (Fl x hx w).val.1 = exp w.val := by
    intro x hx w
    have h := congrFun (hFl x hx).2 w
    exact congrArg Subtype.val h
  let L : ComplexModel n → ℂ → ComplexModel n := fun x w =>
    if hx : x ∈ F₀ then (if hw : w ∈ halfPlane ρ then (Fl x hx ⟨w, hw⟩).val.2 else 0) else 0
  have hL : ∀ x (hx : x ∈ F₀) w (hw : w ∈ halfPlane ρ), L x w = (Fl x hx ⟨w, hw⟩).val.2 := by
    intro x hx w hw
    simp only [L, dif_pos hx, dif_pos hw]
  -- the uniqueness of lifts, for maps given by their second coordinate
  have huniq : ∀ x (hx : x ∈ F₀), ∀ Φ : ℂ → ComplexModel n,
      ContinuousOn Φ (halfPlane ρ) → (∀ w ∈ halfPlane ρ, Φ w ∈ fibre X π (z₀ + exp w • e)) →
      ∀ w₁ ∈ halfPlane ρ, Φ w₁ = L x w₁ → ∀ w ∈ halfPlane ρ, Φ w = L x w := by
    intro x hx Φ hΦc hΦm w₁ hw₁ hΦw₁ w hw
    let Φ' : C(halfPlane ρ, lineTotal X π z₀ e ρ) :=
      ⟨fun w => ⟨(exp w.val, Φ w.val), exp_mem_punctured hρ w.property, (hΦm w.val w.property).1,
        (hΦm w.val w.property).2⟩, by
          apply Continuous.subtype_mk
          exact (continuous_exp.comp continuous_subtype_val).prodMk
            (continuousOn_iff_continuous_domRestrict.mp hΦc)⟩
    have hcomp : lineProj X π z₀ e ρ ∘ Φ' = lineProj X π z₀ e ρ ∘ Fl x hx := by
      rw [(hFl x hx).2]
      rfl
    have hat : Φ' ⟨w₁, hw₁⟩ = Fl x hx ⟨w₁, hw₁⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · exact (hfst x hx ⟨w₁, hw₁⟩).symm
      · change Φ w₁ = (Fl x hx ⟨w₁, hw₁⟩).val.2
        rw [hΦw₁, hL x hx w₁ hw₁]
    have heq := cov.eq_of_comp_eq Φ'.continuous (Fl x hx).continuous hcomp ⟨w₁, hw₁⟩ hat
    have := congrArg (fun F : halfPlane ρ → lineTotal X π z₀ e ρ => (F ⟨w, hw⟩).val.2) heq
    rw [hL x hx w hw]
    exact this
  refine ⟨L, fun x hx => ?_, fun x hx => ?_, fun x hx w hw => ?_, huniq⟩
  · rw [hL x hx w₀ hw₀, (hFl x hx).1]
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (halfPlane ρ).domRestrict (L x) = fun w : halfPlane ρ => (Fl x hx w).val.2 := by
      funext w
      exact hL x hx w.val w.property
    rw [this]
    exact continuous_snd.comp (continuous_subtype_val.comp (Fl x hx).continuous)
  · rw [hL x hx w hw]
    refine ⟨(Fl x hx ⟨w, hw⟩).property.2.1, ?_⟩
    have h := (Fl x hx ⟨w, hw⟩).property.2.2
    rw [hfst x hx ⟨w, hw⟩] at h
    exact h

include hline hgen in
/-- **Monodromy**: the lifts of `exp` enumerate all fibres and, for a suitable `M ≥ 1`, are
`2πiM`-periodic. -/
theorem exists_periodic_lifts (hρ : 0 < ρ) :
    ∃ (M : ℕ) (F₀ : Set (ComplexModel n)) (L : ComplexModel n → ℂ → ComplexModel n),
      0 < M ∧ F₀.Finite ∧
      (∀ x ∈ F₀, ContinuousOn (L x) (halfPlane ρ)) ∧
      (∀ w ∈ halfPlane ρ, BijOn (fun x => L x w) F₀ (fibre X π (z₀ + exp w • e))) ∧
      ∀ x ∈ F₀, ∀ w ∈ halfPlane ρ, ∀ j : ℤ,
        L x (w + 2 * Real.pi * I * (M : ℂ) * (j : ℂ)) = L x w := by
  classical
  set w₀ : ℂ := ((Real.log ρ - 1 : ℝ) : ℂ) with hw₀def
  have hw₀ : w₀ ∈ halfPlane ρ := by simp [halfPlane, hw₀def]
  obtain ⟨L, hL0, hLc, hLm, hLu⟩ := hX.exists_lifts hline hgen hρ w₀ hw₀
  set F₀ := fibre X π (z₀ + exp w₀ • e) with hF₀def
  have hgenw : ∀ w ∈ halfPlane ρ, z₀ + exp w • e ∈ D ∧ δ (z₀ + exp w • e) ≠ 0 := by
    intro w hw
    have h := exp_mem_punctured hρ hw
    exact ⟨hline _ h.2.le, hgen _ h.1 h.2.le⟩
  have hF₀ : F₀.Finite := hX.finite_fibre _ (hgenw w₀ hw₀).1
  -- bijectivity on every fibre
  have hinj : ∀ w ∈ halfPlane ρ, InjOn (fun x => L x w) F₀ := by
    intro w hw x hx x' hx' h
    have := hLu x hx (L x') (hLc x' hx') (hLm x' hx') w hw h.symm w₀ hw₀
    rw [hL0 x hx, hL0 x' hx'] at this
    exact this.symm
  have hbij : ∀ w ∈ halfPlane ρ, BijOn (fun x => L x w) F₀ (fibre X π (z₀ + exp w • e)) := by
    intro w hw
    have hmaps : MapsTo (fun x => L x w) F₀ (fibre X π (z₀ + exp w • e)) :=
      fun x hx => hLm x hx w hw
    refine ⟨hmaps, hinj w hw, ?_⟩
    have himg : (fun x => L x w) '' F₀ = fibre X π (z₀ + exp w • e) := by
      refine Set.eq_of_subset_of_ncard_le hmaps.image_subset ?_
        (hX.finite_fibre _ (hgenw w hw).1)
      rw [(hinj w hw).ncard_image, hX.ncard_fibre _ (hgenw w hw).1 (hgenw w hw).2,
        hX.ncard_fibre _ (hgenw w₀ hw₀).1 (hgenw w₀ hw₀).2]
    rw [← himg]
    exact surjOn_image _ _
  -- the shift by `2πi`
  have h2π : ∀ w : ℂ, w + 2 * Real.pi * I = w + ((2 * Real.pi : ℝ) : ℂ) * I := by
    intro w; push_cast; ring
  have hshift_mem : ∀ w ∈ halfPlane ρ, w + 2 * Real.pi * I ∈ halfPlane ρ := by
    intro w hw
    rw [h2π]
    exact add_mem_halfPlane hw _
  have hexp_shift : ∀ w : ℂ, exp (w + 2 * Real.pi * I) = exp w := fun w => by
    simpa using exp_add_two_pi_I_mul_int w 1
  set σ : ComplexModel n → ComplexModel n := fun x => L x (w₀ + 2 * Real.pi * I) with hσdef
  have hσF : ∀ x ∈ F₀, σ x ∈ F₀ := by
    intro x hx
    have h := hLm x hx _ (hshift_mem w₀ hw₀)
    rwa [hexp_shift] at h
  have hshift : ∀ x ∈ F₀, ∀ w ∈ halfPlane ρ, L x (w + 2 * Real.pi * I) = L (σ x) w := by
    intro x hx
    have hc : ContinuousOn (fun w => L x (w + 2 * Real.pi * I)) (halfPlane ρ) :=
      (hLc x hx).comp (continuous_id.add continuous_const).continuousOn
        (fun w hw => hshift_mem w hw)
    have hm : ∀ w ∈ halfPlane ρ, L x (w + 2 * Real.pi * I) ∈ fibre X π (z₀ + exp w • e) := by
      intro w hw
      have h := hLm x hx _ (hshift_mem w hw)
      rwa [hexp_shift] at h
    exact hLu (σ x) (hσF x hx) _ hc hm w₀ hw₀ (hL0 (σ x) (hσF x hx)).symm
  have hσinj : InjOn σ F₀ := by
    intro x hx x' hx' h
    have hw' : w₀ - 2 * Real.pi * I ∈ halfPlane ρ := by
      have : w₀ - 2 * Real.pi * I = w₀ + ((-(2 * Real.pi) : ℝ) : ℂ) * I := by push_cast; ring
      rw [this]
      exact add_mem_halfPlane hw₀ _
    have h1 := hshift x hx _ hw'
    have h2 := hshift x' hx' _ hw'
    rw [sub_add_cancel] at h1 h2
    rw [hL0 x hx] at h1
    rw [hL0 x' hx'] at h2
    rw [h1, h2, h]
  -- the monodromy permutation of the reference fibre
  have : Finite F₀ := hF₀.to_subtype
  let σ' : F₀ → F₀ := fun x => ⟨σ x.val, hσF x.val x.property⟩
  have hσ'inj : Function.Injective σ' := fun x x' h =>
    Subtype.ext (hσinj x.property x'.property (congrArg Subtype.val h))
  let P : Equiv.Perm F₀ := Equiv.ofBijective σ' (Finite.injective_iff_bijective.mp hσ'inj)
  have hP : ∀ x : F₀, (P x).val = σ x.val := fun _ => rfl
  have hiter : ∀ j : ℕ, ∀ x : F₀, ∀ w ∈ halfPlane ρ,
      L x.val (w + 2 * Real.pi * I * (j : ℂ)) = L ((P ^ j) x).val w := by
    intro j
    induction j with
    | zero => intro x w _; simp
    | succ j ih =>
      intro x w hw
      have hw' := hshift_mem w hw
      have h1 := ih x _ hw'
      have h2 : w + 2 * Real.pi * I + 2 * Real.pi * I * (j : ℂ) =
          w + 2 * Real.pi * I * ((j + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [h2] at h1
      rw [h1, hshift _ ((P ^ j) x).property w hw, pow_succ', Equiv.Perm.mul_apply, hP]
  set M := orderOf P with hMdef
  have hM : 0 < M := orderOf_pos P
  have hperM : ∀ x ∈ F₀, ∀ w ∈ halfPlane ρ, L x (w + 2 * Real.pi * I * (M : ℂ)) = L x w := by
    intro x hx w hw
    have h := hiter M ⟨x, hx⟩ w hw
    rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at h
    exact h
  have hmem : ∀ w ∈ halfPlane ρ, ∀ t : ℝ, w + 2 * Real.pi * I * (M : ℂ) * (t : ℂ) ∈ halfPlane ρ := by
    intro w hw t
    have : w + 2 * Real.pi * I * (M : ℂ) * (t : ℂ) = w + ((2 * Real.pi * M * t : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this]
    exact add_mem_halfPlane hw _
  have hnat : ∀ x ∈ F₀, ∀ m : ℕ, ∀ w ∈ halfPlane ρ,
      L x (w + 2 * Real.pi * I * (M : ℂ) * (m : ℂ)) = L x w := by
    intro x hx m
    induction m with
    | zero => intro w _; simp
    | succ m ih =>
      intro w hw
      have hw' : w + 2 * Real.pi * I * (M : ℂ) * (m : ℂ) ∈ halfPlane ρ := by
        simpa using hmem w hw m
      have h1 := hperM x hx _ hw'
      have h2 : w + 2 * Real.pi * I * (M : ℂ) * (m : ℂ) + 2 * Real.pi * I * (M : ℂ) =
          w + 2 * Real.pi * I * (M : ℂ) * ((m + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [h2] at h1
      rw [h1, ih w hw]
  refine ⟨M, F₀, L, hM, hF₀, hLc, hbij, fun x hx w hw j => ?_⟩
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · simpa using hnat x hx m w hw
  · have hw' : w + 2 * Real.pi * I * (M : ℂ) * (((-(m : ℤ)) : ℤ) : ℂ) ∈ halfPlane ρ := by
      simpa using hmem w hw (-(m : ℝ))
    have h := hnat x hx m _ hw'
    have h2 : w + 2 * Real.pi * I * (M : ℂ) * (((-(m : ℤ)) : ℤ) : ℂ) +
        2 * Real.pi * I * (M : ℂ) * (m : ℂ) = w := by push_cast; ring
    rw [h2] at h
    exact h.symm

include hline hgen in
/-- **Puiseux discs** (`[FN80]` Lemma 5.1, proof): there are `M ≥ 1`, `r > 0` and holomorphic
discs `G x : Δ_r → X`, one for each point `x` of a reference fibre, such that for `s ≠ 0` the
points `G x s` are exactly the (distinct) points of the generic fibre over `z₀ + s^M e`, and
`G x 0` lies over `z₀`. -/
theorem exists_puiseux_discs (hρ : 0 < ρ) :
    ∃ (M : ℕ) (r : ℝ) (F₀ : Finset (ComplexModel n)) (G : ComplexModel n → ℂ → ComplexModel n),
      0 < M ∧ 0 < r ∧
      (∀ x ∈ F₀, DifferentiableOn ℂ (G x) (ball 0 r)) ∧
      (∀ x ∈ F₀, ∀ s ∈ ball (0 : ℂ) r, G x s ∈ X) ∧
      (∀ x ∈ F₀, G x 0 ∈ fibre X π z₀) ∧
      (∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → z₀ + s ^ M • e ∈ D ∧ δ (z₀ + s ^ M • e) ≠ 0) ∧
      ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 →
        BijOn (fun x => G x s) (F₀ : Set (ComplexModel n)) (fibre X π (z₀ + s ^ M • e)) := by
  classical
  obtain ⟨M, F₀s, L, hM, hF₀, hLc, hbij, hper⟩ := hX.exists_periodic_lifts hline hgen hρ
  set r : ℝ := min 1 ρ with hrdef
  have hr : 0 < r := lt_min one_pos hρ
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrρ : r ≤ ρ := min_le_right _ _
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  -- the domain of the `M`-th root parametrization
  have hmemH : ∀ s : ℂ, s ≠ 0 → ‖s‖ < r → (M : ℂ) * log s ∈ halfPlane ρ := by
    intro s hs hsr
    have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs
    have hlog0 : Real.log ‖s‖ < 0 := Real.log_neg hpos (by linarith)
    have hlogρ : Real.log ‖s‖ < Real.log ρ := Real.log_lt_log hpos (by linarith)
    simp only [halfPlane, mem_ofPred_eq, mul_re, natCast_re, natCast_im, log_re, zero_mul,
      sub_zero]
    nlinarith
  have hexpM : ∀ s : ℂ, s ≠ 0 → exp ((M : ℂ) * log s) = s ^ M := by
    intro s hs
    rw [exp_nat_mul, exp_log hs]
  have hnormM : ∀ s : ℂ, ‖s‖ < r → ‖s ^ M‖ < r := by
    intro s hsr
    rw [norm_pow]
    calc ‖s‖ ^ M ≤ ‖s‖ := pow_le_of_le_one (norm_nonneg _) (by linarith) hM.ne'
      _ < r := hsr
  have hgen' : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → z₀ + s ^ M • e ∈ D ∧ δ (z₀ + s ^ M • e) ≠ 0 := by
    intro s hs hs0
    have h := hnormM s (mem_ball_zero_iff.mp hs)
    exact ⟨hline _ (by linarith), hgen _ (pow_ne_zero _ hs0) (by linarith)⟩
  set G₀ : ComplexModel n → ℂ → ComplexModel n := fun x s => L x ((M : ℂ) * log s) with hG₀def
  have hbij₀ : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 →
      BijOn (fun x => G₀ x s) F₀s (fibre X π (z₀ + s ^ M • e)) := by
    intro s hs hs0
    have h := hbij _ (hmemH s hs0 (mem_ball_zero_iff.mp hs))
    rwa [hexpM s hs0] at h
  -- independence of the logarithm
  have hlogind : ∀ x ∈ F₀s, ∀ s : ℂ, s ≠ 0 → ‖s‖ < r → ∀ ℓ : ℂ, exp ℓ = s →
      L x ((M : ℂ) * ℓ) = G₀ x s := by
    intro x hx s hs hsr ℓ hℓ
    rw [← exp_log hs, exp_eq_exp_iff_exists_int] at hℓ
    obtain ⟨j, hj⟩ := hℓ
    have h := hper x hx _ (hmemH s hs hsr) j
    show L x ((M : ℂ) * ℓ) = L x ((M : ℂ) * log s)
    rw [← h, hj]
    congr 1
    ring
  have hℓmem : ∀ s : ℂ, s ≠ 0 → ‖s‖ < r → ∀ ℓ : ℂ, exp ℓ = s → (M : ℂ) * ℓ ∈ halfPlane ρ := by
    intro s hs hsr ℓ hℓ
    rw [← exp_log hs, exp_eq_exp_iff_exists_int] at hℓ
    obtain ⟨j, hj⟩ := hℓ
    have : (M : ℂ) * ℓ = (M : ℂ) * log s + ((2 * Real.pi * M * j : ℝ) : ℂ) * I := by
      rw [hj]; push_cast; ring
    rw [this]
    exact add_mem_halfPlane (hmemH s hs hsr) _
  -- continuity on the punctured disc
  have hcont₀ : ∀ x ∈ F₀s, ∀ s₁ : ℂ, s₁ ≠ 0 → ‖s₁‖ < r → ContinuousAt (G₀ x) s₁ := by
    intro x hx s₁ hs₁ hs₁r
    obtain ⟨ℓ, hℓc, hℓe⟩ := exists_local_log hs₁
    have hc : ContinuousAt (fun s => L x ((M : ℂ) * ℓ s)) s₁ := by
      have hin : (M : ℂ) * ℓ s₁ ∈ halfPlane ρ := hℓmem s₁ hs₁ hs₁r _ hℓe.self_of_nhds
      exact ContinuousAt.comp (f := fun s => (M : ℂ) * ℓ s)
        ((hLc x hx).continuousAt ((isOpen_halfPlane ρ).mem_nhds hin))
        (continuousAt_const.mul hℓc)
    refine hc.congr ?_
    have hr' : ∀ᶠ s in 𝓝 s₁, ‖s‖ < r :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hs₁r
    filter_upwards [hℓe, isOpen_ne.mem_nhds hs₁, hr'] with s hs hs0 hsr
    exact hlogind x hx s hs0 hsr (ℓ s) hs
  -- holomorphy on the punctured disc
  have hdiff₀ : ∀ x ∈ F₀s, ∀ s₁ : ℂ, s₁ ≠ 0 → ‖s₁‖ < r → DifferentiableAt ℂ (G₀ x) s₁ := by
    intro x hx s₁ hs₁ hs₁r
    have hs₁b : s₁ ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr hs₁r
    have hy₁ := (hbij₀ s₁ hs₁b hs₁).1 hx
    obtain ⟨hgD, hgδ⟩ := hgen' s₁ hs₁b hs₁
    have hπy₁ : π (G₀ x s₁) = z₀ + s₁ ^ M • e := hy₁.2
    obtain ⟨U, V, g, hU, hV, hy₁U, hy₁V, -, hgd, -, huniq⟩ :=
      hX.local_graph (G₀ x s₁) hy₁.1 (by rw [hπy₁]; exact hgδ)
    rw [hπy₁] at hy₁U
    have hd : DifferentiableAt ℂ (fun s : ℂ => g (z₀ + s ^ M • e)) s₁ := by
      have hpoly : DifferentiableAt ℂ (fun s : ℂ => z₀ + s ^ M • e) s₁ := by fun_prop
      exact (hgd.differentiableAt (hU.mem_nhds hy₁U)).comp s₁ hpoly
    refine hd.congr_of_eventuallyEq ?_
    have hV' : ∀ᶠ s in 𝓝 s₁, G₀ x s ∈ V := (hcont₀ x hx s₁ hs₁ hs₁r).preimage_mem_nhds
      (hV.mem_nhds hy₁V)
    have hr' : ∀ᶠ s in 𝓝 s₁, ‖s‖ < r :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hs₁r
    filter_upwards [hV', isOpen_ne.mem_nhds hs₁, hr'] with s hsV hs0 hsr
    have hys := (hbij₀ s (mem_ball_zero_iff.mpr hsr) hs0).1 hx
    have h := (huniq (G₀ x s) ⟨hys.1, hsV⟩).2
    have hπ : π (G₀ x s) = z₀ + s ^ M • e := hys.2
    rw [hπ] at h
    exact h.symm
  -- boundedness
  set Λ : ℂ → ComplexModel k := fun τ => z₀ + τ • e with hΛdef
  set K := X ∩ π ⁻¹' (Λ '' closedBall 0 ρ) with hKdef
  have hK : IsCompact K := by
    refine hX.isCompact_inter_preimage _ ?_ ((isCompact_closedBall 0 ρ).image (by fun_prop))
    rintro _ ⟨τ, hτ, rfl⟩
    exact hline τ (mem_closedBall_zero_iff.mp hτ)
  have hGK : ∀ x ∈ F₀s, ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → G₀ x s ∈ K := by
    intro x hx s hs hs0
    have hys := (hbij₀ s hs hs0).1 hx
    refine ⟨hys.1, s ^ M, ?_, hys.2.symm⟩
    rw [mem_closedBall_zero_iff]
    linarith [hnormM s (mem_ball_zero_iff.mp hs)]
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  -- the removable singularity
  set G : ComplexModel n → ℂ → ComplexModel n :=
    fun x => Function.update (G₀ x) 0 (limUnder (𝓝[≠] (0 : ℂ)) (G₀ x)) with hGdef
  have hGd : ∀ x ∈ F₀s, DifferentiableOn ℂ (G x) (ball 0 r) := by
    intro x hx
    apply Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 hr)
    · intro s hs
      have hs0 : s ≠ 0 := hs.2
      exact (hdiff₀ x hx s hs0 (mem_ball_zero_iff.mp hs.1)).differentiableWithinAt
    · refine ⟨C, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      exact hC _ (hGK x hx s hs.1 hs.2)
  have hGne : ∀ x, ∀ s : ℂ, s ≠ 0 → G x s = G₀ x s := fun x s hs => by
    simp only [hGdef]
    exact Function.update_of_ne hs _ _
  have hG0 : ∀ x ∈ F₀s, G x 0 ∈ fibre X π z₀ := by
    intro x hx
    have hc : ContinuousAt (G x) 0 :=
      ((hGd x hx).differentiableAt (ball_mem_nhds 0 hr)).continuousAt
    have ht : Tendsto (G x) (𝓝[≠] (0 : ℂ)) (𝓝 (G x 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), G x s ∈ K ∧ π (G x s) = z₀ + s ^ M • e := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hr)] with s hs0 hsr
      rw [hGne x s hs0]
      exact ⟨hGK x hx s hsr hs0, ((hbij₀ s hsr hs0).1 hx).2⟩
    have hGK0 : G x 0 ∈ K := hK.isClosed.mem_of_tendsto ht (hev.mono fun s hs => hs.1)
    refine ⟨hGK0.1, ?_⟩
    have h1 : Tendsto (fun s => π (G x s)) (𝓝[≠] (0 : ℂ)) (𝓝 (π (G x 0))) :=
      (π.continuous.tendsto _).comp ht
    have h2 : Tendsto (fun s : ℂ => z₀ + s ^ M • e) (𝓝[≠] (0 : ℂ)) (𝓝 z₀) := by
      have : Continuous (fun s : ℂ => z₀ + s ^ M • e) := by fun_prop
      have h := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
      simpa [zero_pow hM.ne'] using h
    exact tendsto_nhds_unique (h1.congr' (hev.mono fun s hs => hs.2)) h2
  refine ⟨M, r, hF₀.toFinset, G, hM, hr, fun x hx => hGd x ((hF₀.mem_toFinset).mp hx),
    fun x hx s hs => ?_, fun x hx => hG0 x ((hF₀.mem_toFinset).mp hx), hgen', fun s hs hs0 => ?_⟩
  · by_cases hs0 : s = 0
    · rw [hs0]
      exact (hG0 x ((hF₀.mem_toFinset).mp hx)).1
    · rw [hGne x s hs0]
      exact ((hbij₀ s hs hs0).1 ((hF₀.mem_toFinset).mp hx)).1
  · rw [hF₀.coe_toFinset]
    have h := hbij₀ s hs hs0
    refine h.congr ?_
    intro x _
    exact (hGne x s hs0).symm

end line

end IsBranchedCovering

end SGPT.Unibranch.FNL
