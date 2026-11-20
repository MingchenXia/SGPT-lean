import SGPT.Unibranch.FNSEwE

/-!
# The Stein neighbourhood step of `[FN80, Thm. 5.3.1]`

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), proof of Theorem 5.3.1 (`[FN80]`): "By a theorem of Siu [17], there exists
a Stein open set `V ⊆ Δⁿ × ℂ` such that `V ∩ (X × ℂ) = Ω`." Used for `thm:FN` (2) ⇒ (1)
(`appendix_unibranch.tex`).

We prove what is needed of Siu's theorem directly. Let `Y = {x : z(x) ∈ X ∩ O}` with
`X ∩ O = {h = 0}` (`h` holomorphic on the open `O ⊆ ℂⁿ`), and let `Ω ⊆ Y` be **Runge in `Y`**:
`K̂ ∩ Y ⊆ Ω` for every compact `K ⊆ Ω` (`K̂` the polynomial hull in `ℂ^{n+1}`).

* `polyHull_union_inter_subset` (**good lemma**): if `A` is polynomially convex, `A ⊆ int A'`,
  `A'` compact with `A' ∩ Y ⊆ Ω`, then `(A ∪ K)^ ∩ Y ⊆ Ω` for every compact `K ⊆ Ω`. This is the
  point where increasing unions of neighbourhoods are kept from meeting `Y` outside `Ω`. Proof:
  for `p ∈ Y ∖ Ω` the Runge property gives a polynomial `g` with `|g(p)| > 1 > |g|` on
  `(A' ∩ Y) ∪ K`; the extension estimate (`FNSEwE.exists_extension_estimate`) corrects `g^m` by
  `∑ hₗ Qₗ` to make it small on `A`; Oka–Weil approximation of the `Qₗ` and `hₗ` by polynomials
  gives a polynomial separating `p` from `A ∪ K`.
* `exists_nested_monoPoly`: an increasing sequence of monomial polyhedra `P_j` with `K_j ⊆ P_j`
  and `P_j ∩ Y ⊆ Ω`, for a sequence of compact rotation invariant `K_j ⊆ Ω` (Siu's Stein
  neighbourhood `V = ⋃ P_j`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNS

open E2Nov16FNPolynomialPolyhedron E2Nov16FNPolynomialGraphBox E2Nov16FNOkaWeil
  E2Nov16FNHolomorphicHullMaximum FNR

variable {n r : ℕ}

/-! ### Polydiscs in `z` -/

/-- The closed polydisc `{z : |zᵢ - x₀ᵢ| ≤ ρ}` in `ℂⁿ`. -/
def zpoly (x₀ : ComplexModel n) (ρ : ℝ) : Set (ComplexModel n) :=
  {z | ∀ i, ‖z i - x₀ i‖ ≤ ρ}

/-- The cylinder `{(w, z) : z ∈ zpoly x₀ ρ}` in `ℂ^{n+1}`. -/
def zcyl (x₀ : ComplexModel n) (ρ : ℝ) : Set (ComplexModel (n + 1)) :=
  zpart ⁻¹' zpoly x₀ ρ

theorem isClosed_zpoly (x₀ : ComplexModel n) (ρ : ℝ) : IsClosed (zpoly x₀ ρ) := by
  have h : zpoly x₀ ρ = ⋂ i, {z : ComplexModel n | ‖z i - x₀ i‖ ≤ ρ} := by
    ext z; simp [zpoly]
  rw [h]
  exact isClosed_iInter fun i => isClosed_le
    (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.sub continuous_const).norm) continuous_const

theorem isClosed_zcyl (x₀ : ComplexModel n) (ρ : ℝ) : IsClosed (zcyl x₀ ρ) :=
  (isClosed_zpoly x₀ ρ).preimage continuous_zpart

theorem zpoly_mono {x₀ : ComplexModel n} {ρ ρ' : ℝ} (h : ρ ≤ ρ') : zpoly x₀ ρ ⊆ zpoly x₀ ρ' :=
  fun _ hz i => (hz i).trans h

theorem zcyl_mono {x₀ : ComplexModel n} {ρ ρ' : ℝ} (h : ρ ≤ ρ') : zcyl x₀ ρ ⊆ zcyl x₀ ρ' :=
  fun _ hz => zpoly_mono h hz

/-- Cylinders over polydiscs are polynomially convex. -/
theorem polyHull_subset_zcyl {x₀ : ComplexModel n} {ρ : ℝ} {K : Set (ComplexModel (n + 1))}
    (hK : K ⊆ zcyl x₀ ρ) : polyHull K ⊆ zcyl x₀ ρ := by
  intro x hx i
  have h := hx (MvPolynomial.X i.succ - MvPolynomial.C (x₀ i)) ρ fun y hy => by
    rw [polyEval_X_sub_C]; exact hK hy i
  rw [polyEval_X_sub_C] at h
  simpa [zcyl, zpoly] using h

theorem isOpen_zcylLt (x₀ : ComplexModel n) (ρ : ℝ) :
    IsOpen {x : ComplexModel (n + 1) | ∀ i, ‖zpart x i - x₀ i‖ < ρ} := by
  have h : {x : ComplexModel (n + 1) | ∀ i, ‖zpart x i - x₀ i‖ < ρ} =
      ⋂ i, {x | ‖zpart x i - x₀ i‖ < ρ} := by ext x; simp
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_lt
    ((((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp continuous_zpart).sub
      continuous_const).norm) continuous_const

/-- `X ∩ zpoly x₀ ρ` is closed when `zpoly x₀ ρ ⊆ O` and `X ∩ O = {h = 0}`. -/
theorem isClosed_inter_zpoly {X O : Set (ComplexModel n)} {h : Fin r → ComplexModel n → ℂ}
    (hh : ∀ l, ContinuousOn (h l) O) (hXO : ∀ z ∈ O, z ∈ X ↔ ∀ l, h l z = 0)
    {x₀ : ComplexModel n} {ρ : ℝ} (hρO : zpoly x₀ ρ ⊆ O) : IsClosed (X ∩ zpoly x₀ ρ) := by
  have hset : X ∩ zpoly x₀ ρ = zpoly x₀ ρ ∩ ⋂ l, (zpoly x₀ ρ ∩ h l ⁻¹' {0}) := by
    ext z
    simp only [mem_inter_iff, mem_iInter, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hzX, hz⟩
      exact ⟨hz, fun l => ⟨hz, ((hXO z (hρO hz)).mp hzX) l⟩⟩
    · rintro ⟨hz, hl⟩
      exact ⟨(hXO z (hρO hz)).mpr fun l => (hl l).2, hz⟩
  rw [hset]
  exact (isClosed_zpoly x₀ ρ).inter (isClosed_iInter fun l =>
    ((hh l).mono hρO).preimage_isClosed_of_isClosed (isClosed_zpoly x₀ ρ) isClosed_singleton)

/-! ### Small arithmetic helpers -/

theorem mul_one_div_eight_le {a : ℝ} (ha : 0 ≤ a) : a * (1 / (8 * (a + 1))) ≤ 1 / 8 := by
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem norm_sum_le_card_mul {ι : Type*} [Fintype ι] (f : ι → ℂ) {c : ℝ} (hc : ∀ i, ‖f i‖ ≤ c) :
    ‖∑ i, f i‖ ≤ Fintype.card ι * c := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hc i).trans ?_
  simp

/-- A finite family of functions continuous on a compact set has a common bound. -/
theorem exists_common_bound {ι : Type*} [Fintype ι] {s : Set (ComplexModel (n + 1))}
    (hs : IsCompact s) {f : ι → ComplexModel (n + 1) → ℂ} (hf : ∀ i, ContinuousOn (f i) s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ s, ‖f i x‖ ≤ M := by
  choose M hM using fun i => hs.exists_bound_of_continuousOn (hf i)
  refine ⟨∑ i, |M i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i x hx => ?_⟩
  refine (hM i x hx).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun i => |M i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)

/-! ### The good lemma -/

/-- **Good lemma.** Let `Ω ⊆ Y = z⁻¹(X ∩ O)` be Runge in `Y`. If `A` is polynomially convex,
`A ⊆ int A'` with `A'` compact over a polydisc in `O` and `A' ∩ Y ⊆ Ω`, then
`(A ∪ K)^ ∩ Y ⊆ Ω` for every compact `K ⊆ Ω` over that polydisc. -/
theorem polyHull_union_inter_subset {X O : Set (ComplexModel n)} (hO : IsOpen O)
    {h : Fin r → ComplexModel n → ℂ} (hh : ∀ l, DifferentiableOn ℂ (h l) O)
    (hXO : ∀ z ∈ O, z ∈ X ↔ ∀ l, h l z = 0)
    {Ω : Set (ComplexModel (n + 1))} (hΩY : Ω ⊆ zpart ⁻¹' (X ∩ O))
    (hR : ∀ K, IsCompact K → K ⊆ Ω → polyHull K ∩ zpart ⁻¹' (X ∩ O) ⊆ Ω)
    {x₀ : ComplexModel n} {ρ : ℝ} (hρO : zpoly x₀ ρ ⊆ O)
    {A A' K : Set (ComplexModel (n + 1))} (hA : IsCompact A) (hAc : polyHull A = A)
    (hA' : IsCompact A') (hAA' : A ⊆ interior A') (hA'Ω : A' ∩ zpart ⁻¹' (X ∩ O) ⊆ Ω)
    (hA'ρ : A' ⊆ zcyl x₀ ρ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hKρ : K ⊆ zcyl x₀ ρ) :
    polyHull (A ∪ K) ∩ zpart ⁻¹' (X ∩ O) ⊆ Ω := by
  classical
  rintro p ⟨hp, hpY⟩
  by_contra hpΩ
  set Y : Set (ComplexModel (n + 1)) := zpart ⁻¹' (X ∩ O) with hYdef
  -- the compact set `T = (A' ∩ Y) ∪ K ⊆ Ω`
  have hA'Y : A' ∩ Y = A' ∩ zpart ⁻¹' (X ∩ zpoly x₀ ρ) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, hYdef]
    constructor
    · rintro ⟨hx, hxX, -⟩; exact ⟨hx, hxX, hA'ρ hx⟩
    · rintro ⟨hx, hxX, hxρ⟩; exact ⟨hx, hxX, hρO hxρ⟩
  have hYc : IsCompact (A' ∩ Y) := by
    rw [hA'Y]
    exact hA'.inter_right ((isClosed_inter_zpoly (fun l => (hh l).continuousOn) hXO hρO).preimage
      continuous_zpart)
  set T : Set (ComplexModel (n + 1)) := (A' ∩ Y) ∪ K with hTdef
  have hT : IsCompact T := hYc.union hK
  have hTΩ : T ⊆ Ω := union_subset hA'Ω hKΩ
  have hpT : p ∉ polyHull T := fun h' => hpΩ (hR T hT hTΩ ⟨h', hpY⟩)
  obtain ⟨G, hG1, hG2⟩ := exists_normalized_separator hpT
  set g : ComplexModel (n + 1) → ℂ := polyEval G with hgdef
  -- the bound `θ' < 1` of `g` on `T`
  obtain ⟨θ', hθ'0, hθ'1, hθ'⟩ : ∃ θ' : ℝ, 0 ≤ θ' ∧ θ' < 1 ∧ ∀ x ∈ T, ‖g x‖ ≤ θ' := by
    rcases T.eq_empty_or_nonempty with he | hne
    · exact ⟨0, le_rfl, one_pos, by simp [he]⟩
    · obtain ⟨x₁, hx₁, hmax⟩ := hT.exists_isMaxOn hne (continuous_polyEval G).norm.continuousOn
      exact ⟨‖g x₁‖, norm_nonneg _, hG1 x₁ (subset_polyHull T hx₁), fun x hx => hmax hx⟩
  set θ : ℝ := (θ' + 1) / 2 with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hθ1 : θ < 1 := by rw [hθdef]; linarith
  have hθ'θ : θ' < θ := by rw [hθdef]; linarith
  -- a polynomial polyhedron around `A` inside `int A'`
  set OE : Set (ComplexModel (n + 1)) := zpart ⁻¹' O with hOEdef
  have hOE : IsOpen OE := hO.preimage continuous_zpart
  have hAOE : A ⊆ OE := fun x hx => hρO (hA'ρ (interior_subset (hAA' hx)))
  obtain ⟨R, -, q, pp, hApb, hpbU⟩ := exists_polynomial_graph_box hA
    (isOpen_interior.inter hOE) (by rw [hAc]; exact fun x hx => ⟨hAA' hx, hAOE hx⟩)
  rw [slice_graphBox_eq_pbox] at hApb hpbU
  rw [hAc] at hApb
  -- the extension estimate
  have hhE : ∀ l, DifferentiableOn ℂ (fun x => h l (zpart x)) OE := fun l =>
    (hh l).comp differentiable_zpart.differentiableOn fun _ hx => hx
  obtain ⟨U₁, hU₁, hpbU₁, C, hC⟩ := exists_extension_estimate hOE hhE (g := g)
    (differentiable_polyEval G).differentiableOn (fun x hx => (hpbU hx).2) hθ0 (by
      intro x hx hx0
      have hxO : zpart x ∈ O := (hpbU hx).2
      have hxX : zpart x ∈ X := (hXO _ hxO).mpr hx0
      have hxA' : x ∈ A' := interior_subset (hpbU hx).1
      exact (hθ' x (Or.inl ⟨hxA', hxX, hxO⟩)).trans_lt hθ'θ)
  -- the power `m`
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m : ℕ, C * θ ^ m ≤ 1 / 4 ∧ θ' ^ m ≤ 1 / 4 ∧ 2 ≤ ‖g p‖ ^ m := by
    have t1 : Tendsto (fun m : ℕ => C * θ ^ m) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).const_mul C
    have t2 : Tendsto (fun m : ℕ => θ' ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hθ'0 hθ'1
    have t3 : Tendsto (fun m : ℕ => ‖g p‖ ^ m) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hG2
    obtain ⟨m, hm⟩ := ((t1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
      ((t2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
        (t3.eventually (eventually_ge_atTop 2)))).exists
    exact ⟨m, hm.1, hm.2.1, hm.2.2⟩
  obtain ⟨Q, hQd, hQ⟩ := hC m
  -- bounds for `h` on `A`
  obtain ⟨Mh, hMh0, hMh⟩ := exists_common_bound hA (f := fun l x => h l (zpart x))
    fun l => (hhE l).continuousOn.mono hAOE
  set ε₁ : ℝ := 1 / (8 * (r * Mh + 1)) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  choose Q' hQ' using fun l => exists_polynomial_approx_on_hull hA hU₁
    (by rw [hAc]; exact hApb.trans hpbU₁) (Q l) (hQd l) hε₁
  rw [hAc] at hQ'
  -- bounds for `Q'` on the hull of `A ∪ K`
  have hAK : IsCompact (A ∪ K) := hA.union hK
  have hHull : polyHull (A ∪ K) ⊆ OE := fun x hx =>
    hρO (polyHull_subset_zcyl (union_subset (fun y hy => hA'ρ (interior_subset (hAA' hy))) hKρ) hx)
  obtain ⟨MQ, hMQ0, hMQ⟩ := exists_common_bound (isCompact_polyHull hAK)
    (f := fun l x => polyEval (Q' l) x) fun l => (continuous_polyEval _).continuousOn
  set ε₂ : ℝ := 1 / (8 * (r * MQ + 1)) with hε₂def
  have hε₂ : 0 < ε₂ := by positivity
  choose H hH using fun l => exists_polynomial_approx_on_hull hAK hOE hHull
    (fun x => h l (zpart x)) (hhE l) hε₂
  -- the separating polynomial
  set F : Poly (n + 1) := G ^ m - ∑ l, H l * Q' l with hFdef
  have hFeval : ∀ x, polyEval F x = g x ^ m - ∑ l, polyEval (H l) x * polyEval (Q' l) x := by
    intro x
    simp [hFdef, hgdef, polyEval, map_sum]
  have hsum2 : ∀ x ∈ polyHull (A ∪ K),
      ‖∑ l, (h l (zpart x) - polyEval (H l) x) * polyEval (Q' l) x‖ ≤ 1 / 8 := by
    intro x hx
    refine (norm_sum_le_card_mul _ (c := ε₂ * MQ) fun l => ?_).trans ?_
    · rw [norm_mul]
      exact mul_le_mul (hH l x hx).le (hMQ l x hx) (norm_nonneg _) hε₂.le
    · rw [Fintype.card_fin, ← mul_assoc, mul_comm (r : ℝ) ε₂, mul_assoc, mul_comm ε₂]
      exact mul_one_div_eight_le (by positivity)
  have hzero : ∀ x ∈ Y, ∀ l, h l (zpart x) = 0 := fun x hx =>
    (hXO _ hx.2).mp hx.1
  have hY_eval : ∀ x ∈ Y, polyEval F x =
      g x ^ m + ∑ l, (h l (zpart x) - polyEval (H l) x) * polyEval (Q' l) x := by
    intro x hx
    rw [hFeval]
    simp only [hzero x hx, zero_sub, neg_mul, Finset.sum_neg_distrib]
    ring
  have hFbound : ∀ x ∈ A ∪ K, ‖polyEval F x‖ ≤ 1 / 2 := by
    rintro x (hxA | hxK)
    · have hdec : polyEval F x = (g x ^ m - ∑ l, h l (zpart x) * Q l x) +
          ∑ l, h l (zpart x) * (Q l x - polyEval (Q' l) x) +
          ∑ l, (h l (zpart x) - polyEval (H l) x) * polyEval (Q' l) x := by
        rw [hFeval]
        simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
        ring
      have h1 : ‖g x ^ m - ∑ l, h l (zpart x) * Q l x‖ ≤ 1 / 4 := (hQ x (hApb hxA)).trans hm1
      have h2 : ‖∑ l, h l (zpart x) * (Q l x - polyEval (Q' l) x)‖ ≤ 1 / 8 := by
        refine (norm_sum_le_card_mul _ (c := Mh * ε₁) fun l => ?_).trans ?_
        · rw [norm_mul]
          exact mul_le_mul (hMh l x hxA) (hQ' l x hxA).le (norm_nonneg _) hMh0
        · rw [Fintype.card_fin, ← mul_assoc]
          exact mul_one_div_eight_le (by positivity)
      have h3 := hsum2 x (subset_polyHull _ (Or.inl hxA))
      rw [hdec]
      calc _ ≤ ‖g x ^ m - ∑ l, h l (zpart x) * Q l x‖ +
              ‖∑ l, h l (zpart x) * (Q l x - polyEval (Q' l) x)‖ +
              ‖∑ l, (h l (zpart x) - polyEval (H l) x) * polyEval (Q' l) x‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ 1 / 4 + 1 / 8 + 1 / 8 := by linarith
        _ = 1 / 2 := by norm_num
    · have hxY : x ∈ Y := (hΩY (hKΩ hxK))
      rw [hY_eval x hxY]
      have h1 : ‖g x ^ m‖ ≤ 1 / 4 := by
        rw [norm_pow]
        exact (pow_le_pow_left₀ (norm_nonneg _) (hθ' x (Or.inr hxK)) m).trans hm2
      have h3 := hsum2 x (subset_polyHull _ (Or.inr hxK))
      calc _ ≤ ‖g x ^ m‖ + ‖∑ l, (h l (zpart x) - polyEval (H l) x) * polyEval (Q' l) x‖ :=
            norm_add_le _ _
        _ ≤ 1 / 2 := by linarith
  have hFp : 1 / 2 < ‖polyEval F p‖ := by
    rw [hY_eval p hpY]
    have h3 := hsum2 p hp
    have h4 : ‖g p ^ m‖ = ‖g p‖ ^ m := norm_pow _ _
    have h5 := norm_sub_norm_le (g p ^ m)
      (-(∑ l, (h l (zpart p) - polyEval (H l) p) * polyEval (Q' l) p))
    rw [norm_neg, sub_neg_eq_add] at h5
    linarith
  exact absurd (hp F (1 / 2) hFbound) (not_le.mpr hFp)

/-! ### The nested monomial polyhedra -/

/-- **One step of the construction.** From a good pair `A ⊆ int A'` and a compact `K ⊆ Ω`,
a monomial polyhedron `P ⊇ (A ∪ K)^` together with a new good compact `A'' ⊇ P̄` over a slightly
larger polydisc. -/
theorem exists_step {X O : Set (ComplexModel n)} (hO : IsOpen O)
    {h : Fin r → ComplexModel n → ℂ} (hh : ∀ l, DifferentiableOn ℂ (h l) O)
    (hXO : ∀ z ∈ O, z ∈ X ↔ ∀ l, h l z = 0)
    {Ω : Set (ComplexModel (n + 1))} (hΩY : Ω ⊆ zpart ⁻¹' (X ∩ O))
    (hR : ∀ K, IsCompact K → K ⊆ Ω → polyHull K ∩ zpart ⁻¹' (X ∩ O) ⊆ Ω)
    {G : Set (ComplexModel (n + 1))} (hG : IsOpen G) (hΩG : Ω = G ∩ zpart ⁻¹' (X ∩ O))
    {x₀ : ComplexModel n} {ρ ρ' : ℝ} (hρρ' : ρ < ρ') (hρ'O : zpoly x₀ ρ' ⊆ O)
    {A A' K : Set (ComplexModel (n + 1))} (hA : IsCompact A) (hAc : polyHull A = A)
    (hAr : IsRotationInvariant A)
    (hA' : IsCompact A') (hAA' : A ⊆ interior A') (hA'Ω : A' ∩ zpart ⁻¹' (X ∩ O) ⊆ Ω)
    (hA'ρ : A' ⊆ zcyl x₀ ρ) (hK : IsCompact K) (hKr : IsRotationInvariant K) (hKΩ : K ⊆ Ω)
    (hKρ : K ⊆ zcyl x₀ ρ) :
    ∃ S : Finset (Poly n × ℕ), polyHull (A ∪ K) ⊆ monoPoly S ∧ IsCompact (monoPolyClosed S) ∧
      ∃ A'' : Set (ComplexModel (n + 1)), IsCompact A'' ∧ monoPolyClosed S ⊆ interior A'' ∧
        A'' ∩ zpart ⁻¹' (X ∩ O) ⊆ Ω ∧ A'' ⊆ zcyl x₀ ρ' := by
  set Y : Set (ComplexModel (n + 1)) := zpart ⁻¹' (X ∩ O) with hYdef
  have hρO : zpoly x₀ ρ ⊆ O := (zpoly_mono hρρ'.le).trans hρ'O
  set B := polyHull (A ∪ K) with hBdef
  have hB : IsCompact B := isCompact_polyHull (hA.union hK)
  have hBr : IsRotationInvariant B := (hAr.union hKr).polyHull
  have hBρ : B ⊆ zcyl x₀ ρ :=
    polyHull_subset_zcyl (union_subset (fun x hx => hA'ρ (interior_subset (hAA' hx))) hKρ)
  have hBΩ : B ∩ Y ⊆ Ω := polyHull_union_inter_subset hO hh hXO hΩY hR hρO hA hAc hA' hAA'
    hA'Ω hA'ρ hK hKΩ hKρ
  -- the closed set `F = (Y ∖ Ω)` over the polydisc of radius `ρ'`
  set F : Set (ComplexModel (n + 1)) := zpart ⁻¹' (X ∩ zpoly x₀ ρ') ∩ Gᶜ with hFdef
  have hF : IsClosed F :=
    ((isClosed_inter_zpoly (fun l => (hh l).continuousOn) hXO hρ'O).preimage
      continuous_zpart).inter hG.isClosed_compl
  set W : Set (ComplexModel (n + 1)) := Fᶜ ∩ {x | ∀ i, ‖zpart x i - x₀ i‖ < ρ'} with hWdef
  have hW : IsOpen W := hF.isOpen_compl.inter (isOpen_zcylLt x₀ ρ')
  have hYF : ∀ x, x ∈ Y → zpart x ∈ zpoly x₀ ρ' → x ∉ F → x ∈ Ω := by
    intro x hxY hxρ hxF
    rw [hΩG]
    refine ⟨?_, hxY⟩
    by_contra hxG
    exact hxF ⟨⟨hxY.1, hxρ⟩, hxG⟩
  have hBW : B ⊆ W := by
    intro x hx
    refine ⟨fun hxF => ?_, fun i => (hBρ hx i).trans_lt hρρ'⟩
    have hxY : x ∈ Y := ⟨hxF.1.1, hρO (hBρ hx)⟩
    have hxΩ := hBΩ ⟨hx, hxY⟩
    rw [hΩG] at hxΩ
    exact hxF.2 hxΩ.1
  obtain ⟨δ, hδ, hδW⟩ := hB.exists_cthickening_subset_open hW hBW
  obtain ⟨S, hS1, hS2, hS3⟩ := exists_monoPoly_nhds hB hBr isOpen_thickening
    (by rw [hBdef, polyHull_polyHull]; exact self_subset_thickening hδ _)
  refine ⟨S, (subset_polyHull B).trans hS1, hS3, cthickening δ B, hB.cthickening,
    hS2.trans (isOpen_thickening.subset_interior_iff.mpr (thickening_subset_cthickening δ B)), ?_, ?_⟩
  · rintro x ⟨hx, hxY⟩
    have hxW := hδW hx
    exact hYF x hxY (fun i => (hxW.2 i).le) hxW.1
  · intro x hx i
    exact ((hδW hx).2 i).le

/-- **Siu's Stein neighbourhood, special case.** For a sequence of compact rotation invariant
`K_j ⊆ Ω` over the polydisc of radius `ρ` there is an increasing sequence of monomial polyhedra
`P_j ⊇ K_j` with `P_j ∩ Y ⊆ Ω`. -/
theorem exists_nested_monoPoly {X O : Set (ComplexModel n)} (hO : IsOpen O)
    {h : Fin r → ComplexModel n → ℂ} (hh : ∀ l, DifferentiableOn ℂ (h l) O)
    (hXO : ∀ z ∈ O, z ∈ X ↔ ∀ l, h l z = 0)
    {Ω : Set (ComplexModel (n + 1))} (hΩY : Ω ⊆ zpart ⁻¹' (X ∩ O))
    (hR : ∀ K, IsCompact K → K ⊆ Ω → polyHull K ∩ zpart ⁻¹' (X ∩ O) ⊆ Ω)
    {G : Set (ComplexModel (n + 1))} (hG : IsOpen G) (hΩG : Ω = G ∩ zpart ⁻¹' (X ∩ O))
    {x₀ : ComplexModel n} {ρ : ℝ} (hρ : 0 < ρ) (h2ρO : zpoly x₀ (2 * ρ) ⊆ O)
    {K : ℕ → Set (ComplexModel (n + 1))} (hK : ∀ j, IsCompact (K j))
    (hKr : ∀ j, IsRotationInvariant (K j)) (hKΩ : ∀ j, K j ⊆ Ω)
    (hKρ : ∀ j, K j ⊆ zcyl x₀ ρ) :
    ∃ S : ℕ → Finset (Poly n × ℕ), (∀ j, monoPoly (S j) ⊆ monoPoly (S (j + 1))) ∧
      (∀ j, K j ⊆ monoPoly (S j)) ∧ ∀ j, monoPoly (S j) ∩ zpart ⁻¹' (X ∩ O) ⊆ Ω := by
  classical
  set Y : Set (ComplexModel (n + 1)) := zpart ⁻¹' (X ∩ O) with hYdef
  set rad : ℕ → ℝ := fun j => 2 * ρ - ρ / ((j : ℝ) + 2) with hraddef
  have hrad_lt : ∀ j, rad j < rad (j + 1) := by
    intro j
    simp only [hraddef, Nat.cast_add, Nat.cast_one]
    have h1 : ρ / ((j : ℝ) + 1 + 2) < ρ / ((j : ℝ) + 2) :=
      div_lt_div_of_pos_left hρ (by positivity) (by linarith)
    linarith
  have hrad_le : ∀ j, rad j ≤ 2 * ρ := by
    intro j
    simp only [hraddef]
    have : 0 ≤ ρ / ((j : ℝ) + 2) := by positivity
    linarith
  have hρrad : ∀ j, ρ ≤ rad j := by
    intro j
    simp only [hraddef]
    have : ρ / ((j : ℝ) + 2) ≤ ρ / 2 :=
      div_le_div_of_nonneg_left hρ.le (by norm_num) (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
    linarith
  have hradO : ∀ j, zpoly x₀ (rad j) ⊆ O := fun j => (zpoly_mono (hrad_le j)).trans h2ρO
  let Inv : ℕ → Finset (Poly n × ℕ) → Set (ComplexModel (n + 1)) → Prop := fun j S A' =>
    IsCompact (monoPolyClosed S) ∧ IsCompact A' ∧ monoPolyClosed S ⊆ interior A' ∧
      A' ∩ Y ⊆ Ω ∧ A' ⊆ zcyl x₀ (rad j)
  have step : ∀ j (S : Finset (Poly n × ℕ)) (A' : Set (ComplexModel (n + 1))), Inv j S A' →
      ∃ (S' : Finset (Poly n × ℕ)) (A'' : Set (ComplexModel (n + 1))), Inv (j + 1) S' A'' ∧
        monoPolyClosed S ⊆ monoPoly S' ∧ K (j + 1) ⊆ monoPoly S' := by
    rintro j S A' ⟨hSc, hA', hSA', hA'Ω, hA'ρ⟩
    obtain ⟨S', hS'1, hS'2, A'', hA''1, hA''2, hA''3, hA''4⟩ :=
      exists_step hO hh hXO hΩY hR hG hΩG (hrad_lt j) (hradO (j + 1)) hSc
        (polyHull_monoPolyClosed S) (isCircular_monoPolyClosed S).isRotationInvariant hA' hSA'
        hA'Ω hA'ρ (hK (j + 1)) (hKr (j + 1)) (hKΩ (j + 1))
        ((hKρ (j + 1)).trans (zcyl_mono (hρrad j)))
    exact ⟨S', A'', ⟨hS'2, hA''1, hA''2, hA''3, hA''4⟩,
      fun x hx => hS'1 (subset_polyHull _ (Or.inl hx)),
      fun x hx => hS'1 (subset_polyHull _ (Or.inr hx))⟩
  have base : ∃ (S : Finset (Poly n × ℕ)) (A' : Set (ComplexModel (n + 1))), Inv 0 S A' ∧
      K 0 ⊆ monoPoly S := by
    have hrad0 : ρ < rad 0 := by
      simp only [hraddef, Nat.cast_zero, zero_add]; linarith
    obtain ⟨S, hS1, hS2, A'', hA''1, hA''2, hA''3, hA''4⟩ :=
      exists_step (A := ∅) (A' := ∅) hO hh hXO hΩY hR hG hΩG hrad0 (hradO 0) isCompact_empty
        polyHull_empty (fun x hx => absurd hx (notMem_empty x)) isCompact_empty
        (empty_subset _) (by simp) (empty_subset _) (hK 0) (hKr 0) (hKΩ 0) (hKρ 0)
    refine ⟨S, A'', ⟨hS2, hA''1, hA''2, hA''3, hA''4⟩, ?_⟩
    rw [empty_union] at hS1
    exact (subset_polyHull _).trans hS1
  choose! fS fA hf using step
  obtain ⟨S₀, A₀, h0, hK0⟩ := base
  let seq : ℕ → Finset (Poly n × ℕ) × Set (ComplexModel (n + 1)) := fun j =>
    Nat.rec (S₀, A₀) (fun j q => (fS j q.1 q.2, fA j q.1 q.2)) j
  have hseq : ∀ j, seq (j + 1) = (fS j (seq j).1 (seq j).2, fA j (seq j).1 (seq j).2) :=
    fun j => rfl
  have hInv : ∀ j, Inv j (seq j).1 (seq j).2 := by
    intro j
    induction j with
    | zero => exact h0
    | succ j ih => rw [hseq]; exact (hf j _ _ ih).1
  refine ⟨fun j => (seq j).1, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · have := (hf j _ _ (hInv j)).2.1
    show monoPoly (seq j).1 ⊆ monoPoly (seq (j + 1)).1
    rw [hseq]
    exact (monoPoly_subset_monoPolyClosed _).trans this
  · cases j with
    | zero => exact hK0
    | succ j =>
      show K (j + 1) ⊆ monoPoly (seq (j + 1)).1
      rw [hseq]; exact (hf j _ _ (hInv j)).2.2
  · obtain ⟨-, -, hSA', hA'Ω, -⟩ := hInv j
    rintro x ⟨hx, hxY⟩
    exact hA'Ω ⟨interior_subset (hSA' (monoPoly_subset_monoPolyClosed _ hx)), hxY⟩

end SGPT.Unibranch.FNS
