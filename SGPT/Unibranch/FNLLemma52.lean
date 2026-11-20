import SGPT.Unibranch.FNLRunge

/-!
# FN80 Lemma 5.2 (for `λ` sheets): the theorem

See `SGPT.Unibranch.FNLRunge` for the statement, the formalization conventions and the proof
outline (`[FN80]` Lemma 5.2, Fornæss–Narasimhan, Math. Ann. 248 (1980)).
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Unibranch.E2Nov16FNPolynomialPolyhedron SGPT.Unibranch.FNR

variable {n k : ℕ}

theorem IsWeaklyStrictlyPSHOn.ne_top {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    (hφ : IsWeaklyStrictlyPSHOn X φ) {x : ComplexModel n} (hx : x ∈ X) : φ x ≠ ⊤ := by
  obtain ⟨U, -, hxU, -, -, h, -⟩ := hφ.local hx
  exact h.ne_top x ⟨hx, hxU⟩

theorem IsWeaklyStrictlyPSHOn.upperSemicontinuousOn {X : Set (ComplexModel n)}
    {φ : ComplexModel n → EReal} (hφ : IsWeaklyStrictlyPSHOn X φ) : UpperSemicontinuousOn φ X := by
  intro x hx y hy
  obtain ⟨U, hU, hxU, -, -, h, -⟩ := hφ.local hx
  have h1 := h.upperSemicontinuousOn x ⟨hx, hxU⟩ y hy
  rwa [nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds (hU.mem_nhds hxU))] at h1

theorem EReal.coe_finset_sum' {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add, ih]

theorem EReal.add_neg_toReal_lt {x y : EReal} (hyt : y ≠ ⊤) (hyb : y ≠ ⊥) (h : x < y) :
    x + ((-y.toReal : ℝ) : EReal) < 0 := by
  rcases eq_or_ne x ⊥ with rfl | hxb
  · simp
  have hxt : x ≠ ⊤ := ne_top_of_lt h
  have hx : x = (x.toReal : EReal) := (EReal.coe_toReal hxt hxb).symm
  have hy : y = (y.toReal : EReal) := (EReal.coe_toReal hyt hyb).symm
  rw [hx, hy, EReal.coe_lt_coe_iff] at h
  rw [hx, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_lt_coe_iff]
  linarith

/-- **`[FN80]` Lemma 5.2** (for every number `λ` of sheets). Let `X ⊆ Δ(a, r)` be a closed analytic
subset of a polydisc of `ℂⁿ` (local holomorphic equations on `Δ(a, r)`) such that the projection
`π` to the first `k` coordinates makes `X` a finite `λ`-sheeted branched covering of an open set
`D ⊇ π(Δ(a, r))` (this includes that `X` is of pure dimension `k`), and let `φ ∈ WSP(X)`. Then
`{φ < 0}` is Runge in `X`: the polynomially convex hull of every compact `K ⊆ X ∩ {φ < 0}` is
contained in `{φ < 0}` (and in `X`). -/
theorem runge_sublevel (hk : k ≤ n) (m : ℕ) {X : Set (ComplexModel n)}
    {D : Set (ComplexModel k)} {δ : ComplexModel k → ℂ} {a : ComplexModel n} {r : Fin n → ℝ}
    (hX : IsBranchedCovering X (coordinateProjection n k) D m δ)
    (hπΔ : MapsTo (coordinateProjection n k) (pdisc a r) D) (hXΔ : X ⊆ pdisc a r)
    (hXeq : HasLocalEquationsOn X (pdisc a r)) {φ : ComplexModel n → EReal}
    (hφ : IsWeaklyStrictlyPSHOn X φ) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKX : K ⊆ X) (hKφ : ∀ x ∈ K, φ x < 0) : polyHull K ⊆ {x | φ x < 0} := by
  induction m using Nat.strong_induction_on generalizing X D δ a r φ K with
  | _ m IH =>
  classical
  set π := coordinateProjection n k with hπdef
  set H := polyHull K with hHdef
  have hKΔ : ∀ x ∈ K, ∀ i, ‖x i - a i‖ < r i := fun x hx => hXΔ (hKX hx)
  have hHX : H ⊆ X ∩ pdisc a r := polyHull_subset_of_localEquations_polydisc hXeq hK hKX hKΔ
  have hHc : IsCompact H := isCompact_polyHull hK
  by_contra hfail
  obtain ⟨p, hpH, hp⟩ := not_subset.mp hfail
  have hp0 : 0 ≤ φ p := not_lt.mp hp
  have hKne : K.Nonempty := by
    by_contra hKe
    rw [not_nonempty_iff_eq_empty] at hKe
    rw [hHdef, hKe, polyHull_empty] at hpH
    exact hpH
  have husc := hφ.upperSemicontinuousOn
  -- a real gap below zero on `K`
  obtain ⟨k₀, hk₀K, hk₀max⟩ := (husc.mono hKX).exists_isMaxOn hKne hK
  obtain ⟨s, hk₀s, hs0⟩ := EReal.exists_between_coe_real (hKφ k₀ hk₀K)
  have hs : s < 0 := by exact_mod_cast hs0
  have hKs : ∀ x ∈ K, φ x < s := fun x hx => lt_of_le_of_lt (hk₀max hx) hk₀s
  have hpdisc_self : ∀ (c : ComplexModel n) (r' : Fin n → ℝ), (∀ i, 0 < r' i) → c ∈ pdisc c r' :=
    fun c r' hr' i => by simpa using hr' i
  have hdisjK : ∀ p₀ ∉ K, ∃ ρ₂ > 0, Disjoint K (closedBall p₀ ρ₂) := by
    intro p₀ hp₀
    obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl p₀ hp₀
    refine ⟨ρ / 2, by positivity, Set.disjoint_left.mpr fun x hxK hxb => ?_⟩
    exact hρK (closedBall_subset_ball (by linarith) hxb) hxK
  ------------------------------------------------------------------
  -- The local step (Rossi + fewer sheets near a non-collapsed point)
  ------------------------------------------------------------------
  have hlocal : ∀ (χ : ComplexModel n → EReal) (p₀ : ComplexModel n) (U : Set (ComplexModel n)),
      IsOpen U → p₀ ∈ U → p₀ ∈ H → (∃ q ∈ fibre X π (π p₀), q ≠ p₀) →
      IsWeaklyStrictlyPSHOn (X ∩ U) χ → χ p₀ ≠ ⊤ → χ p₀ ≠ ⊥ →
      (∀ q ∈ H, q ≠ p₀ → χ q < χ p₀) → p₀ ∉ K → False := by
    intro χ p₀ U hU hp₀U hp₀H hq₀ hχ hχt hχb hmax hp₀K
    obtain ⟨q, hq, hqp⟩ := hq₀
    have hp₀X : p₀ ∈ X := (hHX hp₀H).1
    obtain ⟨r', hr', hsub, D', hπD', hX'⟩ :=
      hX.exists_restrict_pdisc hk hp₀X (hU.inter (isOpen_pdisc a r)) ⟨hp₀U, (hHX hp₀H).2⟩
    have hlt : sheetNumber X π δ p₀ < m := by
      have hz := hX.mem_base hp₀X
      have hsum := hX.sum_sheetNumber hz
      have hfin := hX.finite_fibre (π p₀) hz
      have hsub2 : ({p₀, q} : Finset (ComplexModel n)) ⊆ hfin.toFinset := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (hfin.mem_toFinset).mpr ⟨hp₀X, rfl⟩
        · exact (hfin.mem_toFinset).mpr hq
      have h2 := Finset.sum_le_sum_of_subset (f := fun x => sheetNumber X π δ x) hsub2
      rw [Finset.sum_pair (Ne.symm hqp), hsum] at h2
      have h3 := hX.one_le_sheetNumber hq.1
      omega
    obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.isOpen_iff.mp (isOpen_pdisc p₀ r') p₀
      (hpdisc_self p₀ r' hr')
    obtain ⟨ρ₂, hρ₂, hρ₂K⟩ := hdisjK p₀ hp₀K
    set ρ := min (ρ₁ / 2) ρ₂ with hρdef
    have hρ : 0 < ρ := lt_min (by positivity) hρ₂
    have hρK : Disjoint K (closedBall p₀ ρ) :=
      hρ₂K.mono_right (closedBall_subset_closedBall (min_le_right _ _))
    obtain ⟨hFc, hFX, hp₀F, -⟩ := rossi_step_polydisc hXeq hK hKX hKΔ hp₀H hρ hρK
    have hFsub : polyHull K ∩ sphere p₀ ρ ⊆ X ∩ pdisc p₀ r' := by
      intro y hy
      refine ⟨(hFX hy).1, hρ₁sub ?_⟩
      have h1 := hy.2
      rw [mem_sphere] at h1
      rw [mem_ball]
      linarith [min_le_left (ρ₁ / 2) ρ₂]
    set χ' : ComplexModel n → EReal := fun y => χ y + ((-(χ p₀).toReal : ℝ) : EReal) with hχ'def
    have hχ' : IsWeaklyStrictlyPSHOn (X ∩ pdisc p₀ r') χ' :=
      (hχ.mono (fun y hy => ⟨hy.1, (hsub hy.2).1⟩)).add_const _
    have hχ'F : ∀ y ∈ polyHull K ∩ sphere p₀ ρ, χ' y < 0 := by
      intro y hy
      have hne : y ≠ p₀ := by
        intro h
        have h1 := hy.2
        rw [h, mem_sphere, dist_self] at h1
        linarith
      exact EReal.add_neg_toReal_lt hχt hχb (hmax y hy.1 hne)
    have hres := IH (sheetNumber X π δ p₀) hlt hX' hπD' inter_subset_right
      (hasLocalEquationsOn_inter hXeq (isOpen_pdisc p₀ r') (fun y hy => (hsub hy).2)) hχ' hFc
      hFsub hχ'F hp₀F
    have hval : χ' p₀ = 0 := by
      simp only [hχ'def]
      rw [← EReal.coe_toReal hχt hχb, ← EReal.coe_add]
      simp
    rw [mem_ofPred_eq, hval] at hres
    exact lt_irrefl _ hres
  ------------------------------------------------------------------
  -- First claim: off the collapsed points, `φ ≤ s` on the hull
  ------------------------------------------------------------------
  have hclaim : ∀ p ∈ H, (∃ q ∈ fibre X π (π p), q ≠ p) → φ p ≤ s := by
    intro p hpH hq₀
    obtain ⟨q, hq, hqp⟩ := hq₀
    by_contra hgt
    push Not at hgt
    have hpX := (hHX hpH).1
    set R : ℝ := 2 * ∑ i, r i with hRdef
    have hR : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ R := by
      intro x hx y hy
      have hx' := hXΔ hx
      have hy' := hXΔ hy
      calc ‖x - y‖ ≤ ∑ i, ‖(x - y) i‖ := norm_le_sum_apply _
        _ ≤ ∑ i, (‖x i - a i‖ + ‖y i - a i‖) := Finset.sum_le_sum fun i _ => by
            have : (x - y) i = (x i - a i) - (y i - a i) := by simp
            rw [this]
            exact norm_sub_le _ _
        _ ≤ ∑ i, (r i + r i) := Finset.sum_le_sum fun i _ => add_le_add (hx' i).le (hy' i).le
        _ = R := by rw [hRdef, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    set B : ℝ := Real.log (m ^ 2 * R ^ 2 + 1) with hBdef
    set ℓ : ℝ := Real.log (‖p - q‖ ^ 2 / 4) with hℓdef
    have hpt : φ p ≠ ⊤ := hφ.ne_top hpX
    have hpb : φ p ≠ ⊥ := ne_bot_of_gt hgt
    set d : ℝ := (φ p).toReal - s with hddef
    have hφp : φ p = (((φ p).toReal : ℝ) : EReal) := (EReal.coe_toReal hpt hpb).symm
    have hd : 0 < d := by
      rw [hφp, EReal.coe_lt_coe_iff] at hgt
      linarith
    set ε : ℝ := d / (2 * (|B - ℓ| + 1)) with hεdef
    have hε : 0 < ε := by positivity
    have hεd : ε * (B - ℓ) < d := by
      have h1 : ε * (B - ℓ) ≤ ε * |B - ℓ| := mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
      have h2 : ε * |B - ℓ| < d := by
        rw [hεdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (B - ℓ)]
      linarith
    have hLpsh : PlurisubharmonicOn (fun y => collapse X π δ ε (π y)) (pdisc a r) :=
      HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (isOpen_pdisc a r)
        π.differentiable.differentiableOn hπΔ (hX.plurisubharmonicOn_collapse hε hR)
    set L : ComplexModel n → EReal :=
      fun y => collapse X π δ ε (π y) + ((-(ε * B) : ℝ) : EReal) with hLdef
    have hLwp : IsWeaklyPSHOn X L :=
      (IsWeaklyPSHOn.of_plurisubharmonicOn hLpsh hXΔ).add_const _
    set ψ : ComplexModel n → EReal := fun y => φ y + L y with hψdef
    have hψ : IsWeaklyStrictlyPSHOn X ψ := hφ.add hLwp
    have hLle : ∀ y ∈ X, L y ≤ 0 := by
      intro y hy
      have h := hX.collapse_le hε hR (hX.mem_base hy)
      calc L y ≤ ((ε * B : ℝ) : EReal) + ((-(ε * B) : ℝ) : EReal) :=
            add_le_add_left h _
        _ = 0 := by rw [← EReal.coe_add]; simp
    have hψle : ∀ y ∈ X, ψ y ≤ φ y := fun y hy => add_le_of_nonpos_right (hLle y hy)
    have hψp : ((s : ℝ) : EReal) < ψ p := by
      have h1 := hX.le_collapse hε hpX hq hqp
      have h2 : ((ε * ℓ + -(ε * B) : ℝ) : EReal) ≤ L p := by
        rw [EReal.coe_add]
        exact add_le_add_left h1 _
      calc ((s : ℝ) : EReal) < (((φ p).toReal + (ε * ℓ + -(ε * B)) : ℝ) : EReal) := by
            rw [EReal.coe_lt_coe_iff]
            nlinarith
        _ = φ p + ((ε * ℓ + -(ε * B) : ℝ) : EReal) := by rw [EReal.coe_add, ← hφp]
        _ ≤ ψ p := add_le_add_right h2 _
    have hHne : H.Nonempty := ⟨p, hpH⟩
    obtain ⟨p₁, hp₁H, hp₁max⟩ :=
      (hψ.upperSemicontinuousOn.mono fun y hy => (hHX hy).1).exists_isMaxOn hHne hHc
    have hp₁X : p₁ ∈ X := (hHX hp₁H).1
    have hψp₁ : ((s : ℝ) : EReal) < ψ p₁ := lt_of_lt_of_le hψp (hp₁max hpH)
    have hp₁b : ψ p₁ ≠ ⊥ := ne_bot_of_gt hψp₁
    have hp₁t : ψ p₁ ≠ ⊤ := hψ.ne_top hp₁X
    have hp₁not : ∃ q₁ ∈ fibre X π (π p₁), q₁ ≠ p₁ := by
      by_contra hno
      push Not at hno
      have hY : fibre X π (π p₁) = {p₁} := by
        ext x
        constructor
        · intro hx; exact mem_singleton_iff.mpr (hno x hx)
        · intro hx; rw [mem_singleton_iff.mp hx]; exact ⟨hp₁X, rfl⟩
      have hbot := hX.collapse_eq_bot hε hp₁X hY
      apply hp₁b
      simp only [hψdef, hLdef, hbot, EReal.bot_add, EReal.add_bot]
    have hp₁K : p₁ ∉ K := by
      intro hp₁K
      have := lt_of_le_of_lt (hψle p₁ hp₁X) (hKs p₁ hp₁K)
      exact lt_asymm hψp₁ this
    obtain ⟨U₁, hU₁, hp₁U₁, c₁, hc₁, -, hstrict⟩ := hψ.local hp₁X
    set ψ₁ : ComplexModel n → EReal :=
      fun y => ψ y + (((-(c₁ / 2 * ‖y - p₁‖ ^ 2)) : ℝ) : EReal) with hψ₁def
    have hψ₁ := hstrict (c₁ / 2) p₁ (by positivity) le_rfl
    have hψ₁p₁ : ψ₁ p₁ = ψ p₁ := by simp [hψ₁def]
    refine hlocal ψ₁ p₁ U₁ hU₁ hp₁U₁ hp₁H hp₁not hψ₁ (by rw [hψ₁p₁]; exact hp₁t)
      (by rw [hψ₁p₁]; exact hp₁b) (fun y hy hyp => ?_) hp₁K
    rw [hψ₁p₁]
    rcases eq_or_ne (ψ y) ⊥ with hb | hb
    · simp only [hψ₁def, hb, EReal.bot_add]
      exact bot_lt_iff_ne_bot.mpr hp₁b
    · have hpos : 0 < c₁ / 2 * ‖y - p₁‖ ^ 2 := by
        have : 0 < ‖y - p₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyp)
        positivity
      exact lt_of_lt_of_le (EReal.add_neg_coe_lt hb (hψ.ne_top (hHX hy).1) hpos) (hp₁max hy)
  ------------------------------------------------------------------
  -- The maximum point of `φ` on the hull is a collapsed point
  ------------------------------------------------------------------
  have hHne : H.Nonempty := ⟨p, hpH⟩
  obtain ⟨ps, hpsH, hpsmax⟩ := (husc.mono fun y hy => (hHX hy).1).exists_isMaxOn hHne hHc
  have hpsX : ps ∈ X := (hHX hpsH).1
  have hφps : 0 ≤ φ ps := hp0.trans (hpsmax hpH)
  have hpst : φ ps ≠ ⊤ := hφ.ne_top hpsX
  have hpsb : φ ps ≠ ⊥ := fun h => by rw [h] at hφps; exact absurd hφps (by simp)
  set M : ℝ := (φ ps).toReal with hMdef
  have hφM : φ ps = (M : EReal) := (EReal.coe_toReal hpst hpsb).symm
  have hM0 : 0 ≤ M := by rw [hφM] at hφps; exact_mod_cast hφps
  have hY : ∀ q ∈ fibre X π (π ps), q = ps := by
    by_contra hno
    push Not at hno
    have h := hclaim ps hpsH hno
    have : (0 : EReal) ≤ ((s : ℝ) : EReal) := hφps.trans h
    exact absurd (EReal.coe_nonneg.mp this) (not_le.mpr hs)
  have hpsK : ps ∉ K := fun h => absurd (hKφ ps h) (not_lt.mpr hφps)
  obtain ⟨U₁, hU₁, hpsU₁, c₁, hc₁, -, hstrict⟩ := hφ.local hpsX
  set φ₁ : ComplexModel n → EReal :=
    fun y => φ y + (((-(c₁ / 2 * ‖y - ps‖ ^ 2)) : ℝ) : EReal) with hφ₁def
  have hφ₁ : IsWeaklyStrictlyPSHOn (X ∩ U₁) φ₁ := hstrict (c₁ / 2) ps (by positivity) le_rfl
  obtain ⟨U₂, hU₂, hpsU₂, -, -, hφ₁wp, -⟩ := hφ₁.local ⟨hpsX, hpsU₁⟩
  set φ₂ : ComplexModel n → EReal := fun y => φ₁ y + ((-M : ℝ) : EReal) with hφ₂def
  have hφ₂ : IsWeaklyPSHOn (X ∩ U₁ ∩ U₂) φ₂ := hφ₁wp.add_const _
  have hφ₂ps : φ₂ ps = 0 := by
    simp only [hφ₂def, hφ₁def, sub_self, norm_zero]
    rw [hφM]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero,
      EReal.coe_zero, add_zero]
    rw [← EReal.coe_add]
    simp
  have hφ₂le : ∀ y, φ₂ y ≤ φ y := by
    intro y
    simp only [hφ₂def, hφ₁def]
    refine (add_le_of_nonpos_right (EReal.coe_nonpos.mpr (by linarith))).trans
      (add_le_of_nonpos_right (EReal.coe_nonpos.mpr ?_))
    have : 0 ≤ c₁ / 2 * ‖y - ps‖ ^ 2 := by positivity
    linarith
  have hφ₂neg : ∀ y ∈ H, y ≠ ps → φ₂ y < 0 := by
    intro y hy hyp
    rcases eq_or_ne (φ y) ⊥ with hb | hb
    · simp [hφ₂def, hφ₁def, hb]
    · have hyt : φ y ≠ ⊤ := hφ.ne_top (hHX hy).1
      have hle : φ y ≤ (M : EReal) := hφM ▸ hpsmax hy
      have hyv : φ y = ((φ y).toReal : EReal) := (EReal.coe_toReal hyt hb).symm
      rw [hyv, EReal.coe_le_coe_iff] at hle
      have hpos : 0 < c₁ / 2 * ‖y - ps‖ ^ 2 := by
        have : 0 < ‖y - ps‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyp)
        positivity
      simp only [hφ₂def, hφ₁def]
      rw [hyv, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_lt_coe_iff]
      linarith
  ------------------------------------------------------------------
  -- The trace on a small polydisc around the collapsed maximum point
  ------------------------------------------------------------------
  obtain ⟨r'', hr'', hsub'', D'', hπD'', hX''⟩ := hX.exists_restrict_pdisc hk hpsX
    ((hU₁.inter hU₂).inter (isOpen_pdisc a r)) ⟨⟨hpsU₁, hpsU₂⟩, (hHX hpsH).2⟩
  set X'' := X ∩ pdisc ps r'' with hX''def
  set m'' := sheetNumber X π δ ps with hm''def
  have hX''sub : X'' ⊆ X ∩ U₁ ∩ U₂ := fun y hy => ⟨⟨hy.1, (hsub'' hy.2).1.1⟩, (hsub'' hy.2).1.2⟩
  have hφ₂'' : IsWeaklyPSHOn X'' φ₂ := hφ₂.mono hX''sub
  have hm''1 : 1 ≤ m'' := hX.one_le_sheetNumber hpsX
  have hpsX'' : ps ∈ X'' := ⟨hpsX, hpdisc_self ps r'' hr''⟩
  have htr := hX''.discPshOn_trace hφ₂''
  set ρ : ComplexModel n → EReal := fun y => trace X'' π δ φ₂ (π y) with hρdef
  have hρ : PlurisubharmonicOn ρ (pdisc ps r'') :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic (isOpen_pdisc ps r'')
      π.differentiable.differentiableOn hπD'' (htr.plurisubharmonicOn hX''.isOpen_base)
  have hfib'' : ∀ z, fibre X'' π z ⊆ fibre X π z := fun z y hy => ⟨hy.1.1, hy.2⟩
  have hfibps : fibre X'' π (π ps) = {ps} := by
    ext y
    constructor
    · intro hy; exact mem_singleton_iff.mpr (hY y (hfib'' _ hy))
    · intro hy; rw [mem_singleton_iff.mp hy]; exact ⟨hpsX'', rfl⟩
  have hρps : ρ ps = 0 := by
    simp only [hρdef, trace, hfibps, finsum_mem_singleton, hφ₂ps, smul_zero]
  -- a neighbourhood where all other fibre points have `φ₂ < β`
  set β : ℝ := -s / (2 * m'') with hβdef
  have hβ : 0 < β := by
    rw [hβdef]
    have : (0 : ℝ) < m'' := by exact_mod_cast hm''1
    exact div_pos (by linarith) (by positivity)
  have hβm : (m'' : ℝ) * β = -s / 2 := by
    rw [hβdef]
    have : (m'' : ℝ) ≠ 0 := by exact_mod_cast (by omega : m'' ≠ 0)
    field_simp
  obtain ⟨ε₁, hε₁, hε₁h⟩ : ∃ ε₁ > 0, ∀ y ∈ X'', dist y ps < ε₁ → φ₂ y < β := by
    have h := hφ₂''.upperSemicontinuousOn ps hpsX'' β (by
      show φ₂ ps < (β : EReal)
      rw [hφ₂ps]; exact_mod_cast hβ)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ε₁, hε₁, h⟩ := h
    exact ⟨ε₁, hε₁, fun y hy hd => h hd hy⟩
  have hD''ps : π ps ∈ D'' := hπD'' (hpdisc_self ps r'' hr'')
  obtain ⟨r₀, hr₀, hr₀h⟩ : ∃ r₀ > 0, ∀ y, dist y ps < r₀ → fibre X'' π (π y) ⊆ ball ps ε₁ := by
    have h := hX''.eventually_fibre_subset hD''ps hε₁
    rw [hfibps] at h
    have h2 := π.continuous.continuousAt.preimage_mem_nhds h
    obtain ⟨r₀, hr₀, hsub⟩ := Metric.mem_nhds_iff.mp h2
    refine ⟨r₀, hr₀, fun y hy x hx => ?_⟩
    have := hsub hy hx
    simpa using this
  have hneg : ∀ y ∈ H, y ∈ pdisc ps r'' → dist y ps < r₀ → y ≠ ps → ρ y < 0 := by
    intro y hyH hyΔ hyd hyp
    have hyX'' : y ∈ X'' := ⟨(hHX hyH).1, hyΔ⟩
    have hzD'' : π y ∈ D'' := hX''.mem_base hyX''
    have hFy := hX''.finite_fibre (π y) hzD''
    have hyF : y ∈ hFy.toFinset := (hFy.mem_toFinset).mpr ⟨hyX'', rfl⟩
    simp only [hρdef, trace]
    rw [finsum_mem_eq_finite_toFinset_sum _ hFy]
    by_cases hA : ∀ q ∈ fibre X'' π (π y), q = y
    · have hset : hFy.toFinset = {y} := by
        ext x
        simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
        exact ⟨fun hx => hA x hx, fun hx => by rw [hx]; exact ⟨hyX'', rfl⟩⟩
      rw [hset, Finset.sum_singleton]
      exact EReal.nsmul_neg (hφ₂neg y hyH hyp) (hX''.one_le_sheetNumber hyX'')
    · push Not at hA
      obtain ⟨q, hq, hqy⟩ := hA
      have hgap : φ₂ y ≤ s := (hφ₂le y).trans (hclaim y hyH ⟨q, hfib'' _ hq, hqy⟩)
      set b : ComplexModel n → ℝ := fun x => (if x = y then s else 0) + β with hbdef
      have hterm : ∀ x ∈ hFy.toFinset, sheetNumber X'' π δ x • φ₂ x ≤
          sheetNumber X'' π δ x • ((b x : ℝ) : EReal) := by
        intro x hx
        apply nsmul_le_nsmul_right
        by_cases hxy : x = y
        · rw [hxy]
          show φ₂ y ≤ ((((if y = y then s else 0) + β) : ℝ) : EReal)
          rw [if_pos rfl]
          exact hgap.trans (EReal.coe_le_coe_iff.mpr (by linarith))
        · have hxF := (hFy.mem_toFinset).mp hx
          have hxb : x ∈ ball ps ε₁ := hr₀h y hyd hxF
          have := hε₁h x hxF.1 hxb
          rw [hbdef]
          simp only [if_neg hxy, zero_add]
          exact this.le
      have hsumb : ∑ x ∈ hFy.toFinset, sheetNumber X'' π δ x • ((b x : ℝ) : EReal) =
          ((sheetNumber X'' π δ y * s + m'' * β : ℝ) : EReal) := by
        have h1 : ∀ x ∈ hFy.toFinset, sheetNumber X'' π δ x • ((b x : ℝ) : EReal) =
            (((sheetNumber X'' π δ x : ℝ) * b x : ℝ) : EReal) := fun x _ => by
          rw [← EReal.coe_nsmul, nsmul_eq_mul]
        rw [Finset.sum_congr rfl h1, ← EReal.coe_finset_sum']
        congr 1
        simp only [hbdef, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
          Finset.sum_ite_eq', if_pos hyF]
        rw [← Finset.sum_mul]
        have hsum := hX''.sum_sheetNumber hzD''
        have : (∑ x ∈ hFy.toFinset, (sheetNumber X'' π δ x : ℝ)) = m'' := by
          rw [← Nat.cast_sum]
          exact_mod_cast hsum
        rw [this]
      calc ∑ x ∈ hFy.toFinset, sheetNumber X'' π δ x • φ₂ x
          ≤ ∑ x ∈ hFy.toFinset, sheetNumber X'' π δ x • ((b x : ℝ) : EReal) :=
            Finset.sum_le_sum hterm
        _ = ((sheetNumber X'' π δ y * s + m'' * β : ℝ) : EReal) := hsumb
        _ < 0 := by
            rw [← EReal.coe_zero, EReal.coe_lt_coe_iff, hβm]
            have h1 : (1 : ℝ) ≤ sheetNumber X'' π δ y := by
              exact_mod_cast hX''.one_le_sheetNumber hyX''
            nlinarith
  ------------------------------------------------------------------
  -- Rossi at the maximum point and the Runge property of `{ρ < 0}`
  ------------------------------------------------------------------
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.isOpen_iff.mp (isOpen_pdisc ps r'') ps
    (hpdisc_self ps r'' hr'')
  obtain ⟨ρ₂, hρ₂, hρ₂K⟩ := hdisjK ps hpsK
  set ρR := min (min (ρ₁ / 2) ρ₂) (r₀ / 2) with hρRdef
  have hρR : 0 < ρR := lt_min (lt_min (by positivity) hρ₂) (by positivity)
  have hρRK : Disjoint K (closedBall ps ρR) :=
    hρ₂K.mono_right (closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_right _ _)))
  obtain ⟨hEc, -, hpsE, -⟩ := rossi_step_polydisc hXeq hK hKX hKΔ hpsH hρR hρRK
  have hEsub : polyHull K ∩ sphere ps ρR ⊆ pdisc ps r'' := by
    intro y hy
    apply hρ₁sub
    have h1 := hy.2
    rw [mem_sphere] at h1
    rw [mem_ball]
    linarith [min_le_left (min (ρ₁ / 2) ρ₂) (r₀ / 2), min_le_left (ρ₁ / 2) ρ₂]
  have hEneg : ∀ y ∈ polyHull K ∩ sphere ps ρR, ρ y < 0 := by
    intro y hy
    have h1 := hy.2
    rw [mem_sphere] at h1
    refine hneg y hy.1 (hEsub hy) ?_ ?_
    · rw [h1]; linarith [min_le_right (min (ρ₁ / 2) ρ₂) (r₀ / 2)]
    · intro h
      rw [h, dist_self] at h1
      linarith
  have hfin := polydisc_sublevel_runge hρ hEc hEsub hEneg hpsE
  have := hfin.2
  rw [mem_ofPred_eq, hρps] at this
  exact lt_irrefl _ this

end SGPT.Unibranch.FNL

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Unibranch.E2Nov16FNPolynomialPolyhedron SGPT.Unibranch.FNR

variable {n k : ℕ}

/-- **Sublevel sets of weakly psh functions on a branched covering are Runge** (`[FN80]`
Theorem 5.3.1, the Runge step on a branched covering, and Theorem 5.4 for it): with the
hypotheses of `runge_sublevel`, for `ψ ∈ WP(X)` (not necessarily strongly) and `K ⊆ X` compact
with `ψ < 0` on `K`, the polynomial hull of `K` lies in `{ψ < 0}`.  (`ψ + ε‖·‖²` is in `WSP(X)`
and still negative on `K` for small `ε`.) -/
theorem runge_sublevel_of_isWeaklyPSHOn (hk : k ≤ n) (m : ℕ) {X : Set (ComplexModel n)}
    {D : Set (ComplexModel k)} {δ : ComplexModel k → ℂ} {a : ComplexModel n} {r : Fin n → ℝ}
    (hX : IsBranchedCovering X (coordinateProjection n k) D m δ)
    (hπΔ : MapsTo (coordinateProjection n k) (pdisc a r) D) (hXΔ : X ⊆ pdisc a r)
    (hXeq : HasLocalEquationsOn X (pdisc a r)) {ψ : ComplexModel n → EReal}
    (hψ : IsWeaklyPSHOn X ψ) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKX : K ⊆ X) (hKψ : ∀ x ∈ K, ψ x < 0) : polyHull K ⊆ {x | ψ x < 0} := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe, polyHull_empty]; exact empty_subset _
  obtain ⟨k₀, hk₀K, hk₀max⟩ := (hψ.upperSemicontinuousOn.mono hKX).exists_isMaxOn hKne hK
  obtain ⟨s, hk₀s, hs0⟩ := EReal.exists_between_coe_real (hKψ k₀ hk₀K)
  have hs : s < 0 := by exact_mod_cast hs0
  obtain ⟨C₀, hC₀⟩ := hK.isBounded.exists_norm_le
  set C : ℝ := C₀ ^ 2 with hCdef
  have hC : 0 ≤ C := sq_nonneg _
  set ε : ℝ := -s / (2 * (C + 1)) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hεC : ε * C ≤ -s / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set φ₁ : ComplexModel n → EReal := fun x => ψ x + ((ε * ‖x‖ ^ 2 : ℝ) : EReal) with hφ₁def
  have hφ₁ : IsWeaklyStrictlyPSHOn X φ₁ := by
    intro x _
    refine ⟨univ, isOpen_univ, mem_univ x, ε / 2, by positivity, ?_⟩
    refine ((hψ.mono inter_subset_left).add (IsWeaklyPSHOn.of_plurisubharmonicOn
      (plurisubharmonicOn_quadratic (a := ε / 2) (by positivity) 0 0) (subset_univ _))).congr ?_
    intro y _
    simp only [hφ₁def, sub_zero, add_zero]
    rw [add_assoc, ← EReal.coe_add]
    congr 2
    ring
  have hφ₁K : ∀ x ∈ K, φ₁ x < 0 := by
    intro x hx
    have h1 : ψ x < (s : EReal) := lt_of_le_of_lt (hk₀max hx) hk₀s
    have h2 : ε * ‖x‖ ^ 2 ≤ ε * C := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      rw [hCdef]
      exact pow_le_pow_left₀ (norm_nonneg _) (hC₀ x hx) 2
    calc φ₁ x < ((s : ℝ) : EReal) + ((ε * ‖x‖ ^ 2 : ℝ) : EReal) :=
          EReal.add_lt_add_right_coe h1 _
      _ = ((s + ε * ‖x‖ ^ 2 : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ < 0 := by
          rw [← EReal.coe_zero, EReal.coe_lt_coe_iff]
          linarith
  intro z hz
  have h := runge_sublevel hk m hX hπΔ hXΔ hXeq hφ₁ hK hKX hφ₁K hz
  have hle : ψ z ≤ φ₁ z := le_add_of_nonneg_right (EReal.coe_nonneg.mpr (by positivity))
  exact lt_of_le_of_lt hle h

end SGPT.Unibranch.FNL
