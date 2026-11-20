import SGPT.Unibranch.FNSAdapter

/-!
# Runge property of Hartogs domains over unions

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), proof of Theorem 5.3.1 (`[FN80]`), for `thm:FN` (2) ⇒ (1)
(`appendix_unibranch.tex`).

`[FN80]` prove the Runge property of `Ω_φ = {φ(z) + log |w| < 0}` only over each union `S_j` of
the `j`-dimensional irreducible components of `X` (Lemma 5.2 needs a branched covering of fixed
sheet number), and conclude that `Ω_φ` is Stein through its normalization. Our Siu step
(`FNS.exists_ambient_psh_of_hartogsRunge`) uses the Runge property over all of `X`. This file
closes the gap without normalizations:

* `hartogsRunge_union`: if `X₁`, `X₂` are cut out by holomorphic functions on an open polydisc
  `Δ` and `Ω_φ` is Runge over `X₁ ∩ Δ` and over `X₂ ∩ Δ`, then it is Runge over `(X₁ ∪ X₂) ∩ Δ`.

Proof: for `p ∈ (X₁ × ℂ) ∖ Ω_φ` in the hull of `K = K₁ ∪ K₂` (`Kⱼ = K ∩ (Xⱼ × ℂ)`), the hull
`K̂₂` lies in `X₂ × ℂ`, so `K̂₂ ∩ (X₁ × ℂ) ⊆ Ω_φ` by the Runge property over `X₂`; the Runge property
over `X₁` then gives a polynomial `g` with `|g(p)| > 1 > |g|` on `K₁ ∪ (K̂₂ ∩ (X₁ × ℂ))`, and the
extension estimate (`FNSEwE`) with the equations of `X₁` corrects `g^m` to be small on `K̂₂`
(`false_of_separation`, the separation argument of the good lemma `FNSSiu`).
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

/-- `X ∩ C` is closed for `C ⊆ O` closed and `X ∩ O = {h = 0}`. -/
theorem isClosed_inter_of_subset {X O C : Set (ComplexModel n)} {h : Fin r → ComplexModel n → ℂ}
    (hh : ∀ l, ContinuousOn (h l) O) (hXO : ∀ z ∈ O, z ∈ X ↔ ∀ l, h l z = 0)
    (hC : IsClosed C) (hCO : C ⊆ O) : IsClosed (X ∩ C) := by
  have hset : X ∩ C = C ∩ ⋂ l, (C ∩ h l ⁻¹' {0}) := by
    ext z
    simp only [mem_inter_iff, mem_iInter, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hzX, hz⟩
      exact ⟨hz, fun l => ⟨hz, ((hXO z (hCO hz)).mp hzX) l⟩⟩
    · rintro ⟨hz, hl⟩
      exact ⟨(hXO z (hCO hz)).mpr fun l => (hl l).2, hz⟩
  rw [hset]
  exact hC.inter (isClosed_iInter fun l =>
    ((hh l).mono hCO).preimage_isClosed_of_isClosed hC isClosed_singleton)

theorem isClosed_closedPolydisc (a : ComplexModel n) (s : Fin n → ℝ) :
    IsClosed (FNA.closedPolydisc a s) := by
  have h : FNA.closedPolydisc a s = ⋂ i, {z : ComplexModel n | ‖z i - a i‖ ≤ s i} := by
    ext z; simp [FNA.closedPolydisc]
  rw [h]
  exact isClosed_iInter fun i => isClosed_le
    (((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.sub continuous_const).norm) continuous_const

/-- Cylinders over closed polydiscs are polynomially convex. -/
theorem polyHull_subset_cyl {a : ComplexModel n} {s : Fin n → ℝ} {K : Set (ComplexModel (n + 1))}
    (hK : K ⊆ zpart ⁻¹' FNA.closedPolydisc a s) :
    polyHull K ⊆ zpart ⁻¹' FNA.closedPolydisc a s := by
  intro x hx i
  have h := hx (MvPolynomial.X i.succ - MvPolynomial.C (a i)) (s i) fun y hy => by
    rw [polyEval_X_sub_C]; exact hK hy i
  rw [polyEval_X_sub_C] at h
  simpa using h

/-- **Separation.** Let `Y = z⁻¹(X ∩ O)` with `X ∩ O = {h = 0}`, `A` compact polynomially convex
over `C₀ ⊆ int C₁ ⊆ C₁ ⊆ O`, `B ⊆ Y` compact, `p ∈ Y`, and `g` a polynomial with `|g(p)| > 1`,
`|g| < 1` on `B` and on `A ∩ Y`. Then `p ∉ (A ∪ B)^`. -/
theorem false_of_separation {X O : Set (ComplexModel n)} (hO : IsOpen O)
    {h : Fin r → ComplexModel n → ℂ} (hh : ∀ l, DifferentiableOn ℂ (h l) O)
    (hXO : ∀ z ∈ O, z ∈ X ↔ ∀ l, h l z = 0) {C₀ C₁ : Set (ComplexModel n)} (hC₁ : IsClosed C₁)
    (hC₁O : C₁ ⊆ O) (hC₀₁ : C₀ ⊆ interior C₁) {A B : Set (ComplexModel (n + 1))}
    (hA : IsCompact A) (hAc : polyHull A = A) (hAC : A ⊆ zpart ⁻¹' C₀) (hB : IsCompact B)
    (hBY : B ⊆ zpart ⁻¹' (X ∩ O)) (hHC : polyHull (A ∪ B) ⊆ zpart ⁻¹' C₁)
    {p : ComplexModel (n + 1)} (hpY : p ∈ zpart ⁻¹' (X ∩ O)) {G : Poly (n + 1)}
    (hGp : 1 < ‖polyEval G p‖) (hGB : ∀ x ∈ B, ‖polyEval G x‖ < 1)
    (hGA : ∀ x ∈ A, zpart x ∈ X → ‖polyEval G x‖ < 1) (hp : p ∈ polyHull (A ∪ B)) : False := by
  classical
  set Y : Set (ComplexModel (n + 1)) := zpart ⁻¹' (X ∩ O) with hYdef
  set g : ComplexModel (n + 1) → ℂ := polyEval G with hgdef
  have hXC₁ : IsClosed (X ∩ C₁) :=
    isClosed_inter_of_subset (fun l => (hh l).continuousOn) hXO hC₁ hC₁O
  have hAC₁ : A ⊆ zpart ⁻¹' C₁ := fun x hx => interior_subset (s := C₁) (hC₀₁ (hAC hx))
  set T : Set (ComplexModel (n + 1)) := (A ∩ zpart ⁻¹' (X ∩ C₁)) ∪ B with hTdef
  have hT : IsCompact T := (hA.inter_right (hXC₁.preimage continuous_zpart)).union hB
  have hTg : ∀ x ∈ T, ‖g x‖ < 1 := by
    rintro x (⟨hxA, hxX, -⟩ | hxB)
    · exact hGA x hxA hxX
    · exact hGB x hxB
  obtain ⟨θ', hθ'0, hθ'1, hθ'⟩ : ∃ θ' : ℝ, 0 ≤ θ' ∧ θ' < 1 ∧ ∀ x ∈ T, ‖g x‖ ≤ θ' := by
    rcases T.eq_empty_or_nonempty with he | hne
    · exact ⟨0, le_rfl, one_pos, by simp [he]⟩
    · obtain ⟨x₁, hx₁, hmax⟩ := hT.exists_isMaxOn hne (continuous_polyEval G).norm.continuousOn
      exact ⟨‖g x₁‖, norm_nonneg _, hTg x₁ hx₁, fun x hx => hmax hx⟩
  set θ : ℝ := (θ' + 1) / 2 with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hθ1 : θ < 1 := by rw [hθdef]; linarith
  have hθ'θ : θ' < θ := by rw [hθdef]; linarith
  -- the closed set where `|g| ≥ θ` over `X ∩ C₁`, and an open neighbourhood of `A` avoiding it
  set F' : Set (ComplexModel (n + 1)) := zpart ⁻¹' (X ∩ C₁) ∩ {x | θ ≤ ‖g x‖} with hF'def
  have hF' : IsClosed F' := (hXC₁.preimage continuous_zpart).inter
    (isClosed_le continuous_const (continuous_polyEval G).norm)
  set OE : Set (ComplexModel (n + 1)) := zpart ⁻¹' O with hOEdef
  have hOE : IsOpen OE := hO.preimage continuous_zpart
  set U₀ : Set (ComplexModel (n + 1)) := F'ᶜ ∩ zpart ⁻¹' interior C₁ with hU₀def
  have hU₀ : IsOpen U₀ := hF'.isOpen_compl.inter (isOpen_interior.preimage continuous_zpart)
  have hAU₀ : polyHull A ⊆ U₀ := by
    rw [hAc]
    intro x hx
    refine ⟨fun hxF => ?_, hC₀₁ (hAC hx)⟩
    have h1 := hθ' x (Or.inl ⟨hx, hxF.1⟩)
    have h2 : θ ≤ ‖g x‖ := hxF.2
    linarith
  obtain ⟨R, -, q, pp, hApb, hpbU⟩ := exists_polynomial_graph_box hA hU₀ hAU₀
  rw [slice_graphBox_eq_pbox] at hApb hpbU
  rw [hAc] at hApb
  have hpbO : pbox R pp ⊆ OE := fun x hx => hC₁O (interior_subset (hpbU hx).2)
  have hhE : ∀ l, DifferentiableOn ℂ (fun x => h l (zpart x)) OE := fun l =>
    (hh l).comp differentiable_zpart.differentiableOn fun _ hx => hx
  obtain ⟨U₁, hU₁, hpbU₁, C, hC⟩ := exists_extension_estimate hOE hhE (g := g)
    (differentiable_polyEval G).differentiableOn hpbO hθ0 (by
      intro x hx hx0
      have hxC : zpart x ∈ C₁ := interior_subset (hpbU hx).2
      have hxX : zpart x ∈ X := (hXO _ (hC₁O hxC)).mpr hx0
      by_contra hge
      exact (hpbU hx).1 ⟨⟨hxX, hxC⟩, not_lt.mp hge⟩)
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m : ℕ, C * θ ^ m ≤ 1 / 4 ∧ θ' ^ m ≤ 1 / 4 ∧ 2 ≤ ‖g p‖ ^ m := by
    have t1 : Tendsto (fun m : ℕ => C * θ ^ m) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).const_mul C
    have t2 : Tendsto (fun m : ℕ => θ' ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hθ'0 hθ'1
    have t3 : Tendsto (fun m : ℕ => ‖g p‖ ^ m) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hGp
    obtain ⟨m, hm⟩ := ((t1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
      ((t2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
        (t3.eventually (eventually_ge_atTop 2)))).exists
    exact ⟨m, hm.1, hm.2.1, hm.2.2⟩
  obtain ⟨Q, hQd, hQ⟩ := hC m
  have hAOE : A ⊆ OE := fun x hx => hC₁O (hAC₁ hx)
  obtain ⟨Mh, hMh0, hMh⟩ := exists_common_bound hA (f := fun l x => h l (zpart x))
    fun l => (hhE l).continuousOn.mono hAOE
  set ε₁ : ℝ := 1 / (8 * (r * Mh + 1)) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  choose Q' hQ' using fun l => exists_polynomial_approx_on_hull hA hU₁
    (by rw [hAc]; exact hApb.trans hpbU₁) (Q l) (hQd l) hε₁
  rw [hAc] at hQ'
  have hAB : IsCompact (A ∪ B) := hA.union hB
  have hHull : polyHull (A ∪ B) ⊆ OE := fun x hx => hC₁O (hHC hx)
  obtain ⟨MQ, hMQ0, hMQ⟩ := exists_common_bound (isCompact_polyHull hAB)
    (f := fun l x => polyEval (Q' l) x) fun l => (continuous_polyEval _).continuousOn
  set ε₂ : ℝ := 1 / (8 * (r * MQ + 1)) with hε₂def
  have hε₂ : 0 < ε₂ := by positivity
  choose H hH using fun l => exists_polynomial_approx_on_hull hAB hOE hHull
    (fun x => h l (zpart x)) (hhE l) hε₂
  set F : Poly (n + 1) := G ^ m - ∑ l, H l * Q' l with hFdef
  have hFeval : ∀ x, polyEval F x = g x ^ m - ∑ l, polyEval (H l) x * polyEval (Q' l) x := by
    intro x
    simp [hFdef, hgdef, polyEval, map_sum]
  have hsum2 : ∀ x ∈ polyHull (A ∪ B),
      ‖∑ l, (h l (zpart x) - polyEval (H l) x) * polyEval (Q' l) x‖ ≤ 1 / 8 := by
    intro x hx
    refine (norm_sum_le_card_mul _ (c := ε₂ * MQ) fun l => ?_).trans ?_
    · rw [norm_mul]
      exact mul_le_mul (hH l x hx).le (hMQ l x hx) (norm_nonneg _) hε₂.le
    · rw [Fintype.card_fin, ← mul_assoc, mul_comm (r : ℝ) ε₂, mul_assoc, mul_comm ε₂]
      exact mul_one_div_eight_le (by positivity)
  have hzero : ∀ x ∈ Y, ∀ l, h l (zpart x) = 0 := fun x hx => (hXO _ hx.2).mp hx.1
  have hY_eval : ∀ x ∈ Y, polyEval F x =
      g x ^ m + ∑ l, (h l (zpart x) - polyEval (H l) x) * polyEval (Q' l) x := by
    intro x hx
    rw [hFeval]
    simp only [hzero x hx, zero_sub, neg_mul, Finset.sum_neg_distrib]
    ring
  have hFbound : ∀ x ∈ A ∪ B, ‖polyEval F x‖ ≤ 1 / 2 := by
    rintro x (hxA | hxB)
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
    · rw [hY_eval x (hBY hxB)]
      have h1 : ‖g x ^ m‖ ≤ 1 / 4 := by
        rw [norm_pow]
        exact (pow_le_pow_left₀ (norm_nonneg _) (hθ' x (Or.inr hxB)) m).trans hm2
      have h3 := hsum2 x (subset_polyHull _ (Or.inr hxB))
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

/-- One half of the union argument: points of `(X₁ × ℂ) ∖ Ω_φ` are not in the hull of compact
subsets of `Ω_φ` over `X₁ ∪ X₂`. -/
theorem mem_hartogsDomain_of_mem_left {X₁ X₂ : Set (ComplexModel n)} {a : ComplexModel n}
    {ρ : Fin n → ℝ} {r₁ r₂ : ℕ} {h₁ : Fin r₁ → ComplexModel n → ℂ} {h₂ : Fin r₂ → ComplexModel n → ℂ}
    (hh₁ : ∀ l, DifferentiableOn ℂ (h₁ l) (FNA.polydisc a ρ))
    (hh₂ : ∀ l, DifferentiableOn ℂ (h₂ l) (FNA.polydisc a ρ))
    (hX₁ : ∀ z ∈ FNA.polydisc a ρ, z ∈ X₁ ↔ ∀ l, h₁ l z = 0)
    (hX₂ : ∀ z ∈ FNA.polydisc a ρ, z ∈ X₂ ↔ ∀ l, h₂ l z = 0)
    {φ : ComplexModel n → EReal} (hR₁ : HartogsRunge (X₁ ∩ FNA.polydisc a ρ) φ)
    (hR₂ : HartogsRunge (X₂ ∩ FNA.polydisc a ρ) φ)
    {K : Set (ComplexModel (n + 1))} (hK : IsCompact K)
    (hKΩ : K ⊆ hartogsDomain ((X₁ ∪ X₂) ∩ FNA.polydisc a ρ) φ)
    {p : ComplexModel (n + 1)} (hp : p ∈ polyHull K)
    (hpY : p ∈ zpart ⁻¹' (X₁ ∩ FNA.polydisc a ρ)) :
    p ∈ hartogsDomain ((X₁ ∪ X₂) ∩ FNA.polydisc a ρ) φ := by
  classical
  set O := FNA.polydisc a ρ with hOdef
  have hO : IsOpen O := FNA.isOpen_polydisc a ρ
  set Ω := hartogsDomain ((X₁ ∪ X₂) ∩ O) φ with hΩdef
  set Ω₁ := hartogsDomain (X₁ ∩ O) φ
  set Ω₂ := hartogsDomain (X₂ ∩ O) φ
  have hΩ₁ : Ω₁ ⊆ Ω := fun x ⟨hx, c, hc⟩ => ⟨⟨Or.inl hx.1, hx.2⟩, c, hc⟩
  have hΩ₂ : Ω₂ ⊆ Ω := fun x ⟨hx, c, hc⟩ => ⟨⟨Or.inr hx.1, hx.2⟩, c, hc⟩
  have hΩj : ∀ {Xj : Set (ComplexModel n)} {x}, x ∈ Ω → zpart x ∈ Xj ∩ O →
      x ∈ hartogsDomain (Xj ∩ O) φ := fun ⟨_, c, hc⟩ hxj => ⟨hxj, c, hc⟩
  by_contra hpΩ
  -- a closed polydisc `C₀` over `K` inside `O`, and `C₁` between `C₀` and `O`
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe, polyHull_empty] at hp; exact hp
  have hcoord : ∀ i : Fin n, ∃ s : ℝ, s < ρ i ∧ ∀ x ∈ K, ‖zpart x i - a i‖ ≤ s := by
    intro i
    obtain ⟨x₁, hx₁, hmax⟩ := hK.exists_isMaxOn hKne
      ((((EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp continuous_zpart).sub
        continuous_const).norm).continuousOn
    exact ⟨‖zpart x₁ i - a i‖, (hKΩ hx₁).1.2 i, fun x hx => hmax hx⟩
  choose s hsρ hsK using hcoord
  set s' : Fin n → ℝ := fun i => (s i + ρ i) / 2 with hs'def
  set C₀ := FNA.closedPolydisc a s
  set C₁ := FNA.closedPolydisc a s'
  have hC₁ : IsClosed C₁ := isClosed_closedPolydisc a s'
  have hC₁O : C₁ ⊆ O := fun z hz i => (hz i).trans_lt (by simp only [hs'def]; linarith [hsρ i])
  have hC₀₁ : C₀ ⊆ interior C₁ := by
    have hopen : IsOpen (FNA.polydisc a s') := FNA.isOpen_polydisc a s'
    refine fun z hz => interior_mono (FNA.polydisc_subset_closedPolydisc a s')
      (hopen.interior_eq.symm ▸ fun i => (hz i).trans_lt ?_)
    simp only [hs'def]; linarith [hsρ i]
  have hC₀O : C₀ ⊆ O := fun z hz => hC₁O (interior_subset (hC₀₁ hz))
  have hKC₀ : K ⊆ zpart ⁻¹' C₀ := fun x hx i => hsK i x hx
  have hXC₀ : ∀ {Xj : Set (ComplexModel n)} {rj : ℕ} {hj : Fin rj → ComplexModel n → ℂ},
      (∀ l, DifferentiableOn ℂ (hj l) O) → (∀ z ∈ O, z ∈ Xj ↔ ∀ l, hj l z = 0) →
      IsClosed (Xj ∩ C₀) := fun hhj hXj =>
    isClosed_inter_of_subset (fun l => (hhj l).continuousOn) hXj
      (isClosed_closedPolydisc a s) hC₀O
  -- the pieces `K₁`, `K₂`
  set K₁ := K ∩ zpart ⁻¹' (X₁ ∩ C₀)
  set K₂ := K ∩ zpart ⁻¹' (X₂ ∩ C₀)
  have hK₁ : IsCompact K₁ := hK.inter_right ((hXC₀ hh₁ hX₁).preimage continuous_zpart)
  have hK₂ : IsCompact K₂ := hK.inter_right ((hXC₀ hh₂ hX₂).preimage continuous_zpart)
  have hKsplit : K ⊆ K₁ ∪ K₂ := by
    intro x hx
    rcases (hKΩ hx).1.1 with h1 | h2
    · exact Or.inl ⟨hx, h1, hKC₀ hx⟩
    · exact Or.inr ⟨hx, h2, hKC₀ hx⟩
  have hK₂Ω : K₂ ⊆ Ω₂ := fun x hx => hΩj (hKΩ hx.1) ⟨hx.2.1, hC₀O hx.2.2⟩
  -- the hull of `K₂` lies over `X₂`
  have hH₂C₀ : polyHull K₂ ⊆ zpart ⁻¹' C₀ := polyHull_subset_cyl fun x hx => hx.2.2
  have hH₂Y₂ : polyHull K₂ ⊆ zpart ⁻¹' (X₂ ∩ O) := by
    have hW : IsOpen (zpart ⁻¹' O) := hO.preimage continuous_zpart
    have h := polyHull_subset_zeroLocus hK₂ hW (fun x hx => hC₀O (hH₂C₀ hx))
      (f := fun l x => h₂ l (zpart x))
      (fun l => (hh₂ l).comp differentiable_zpart.differentiableOn fun _ hx => hx)
      (fun x hx l => (hX₂ _ (hC₀O hx.2.2)).mp hx.2.1 l)
    intro x hx
    obtain ⟨hxO, hx0⟩ := h hx
    exact ⟨(hX₂ _ hxO).mpr hx0, hxO⟩
  have hH₂Ω : polyHull K₂ ⊆ Ω := fun x hx => hΩ₂ (hR₂ K₂ hK₂ hK₂Ω ⟨hx, hH₂Y₂ hx⟩)
  -- the compact `B₁ = K₁ ∪ (K̂₂ over X₁)` inside `Ω₁`
  set B₁ := K₁ ∪ (polyHull K₂ ∩ zpart ⁻¹' (X₁ ∩ C₀))
  have hB₁ : IsCompact B₁ :=
    hK₁.union ((isCompact_polyHull hK₂).inter_right ((hXC₀ hh₁ hX₁).preimage continuous_zpart))
  have hB₁Ω : B₁ ⊆ Ω₁ := by
    rintro x (hx | ⟨hx, hxX, hxC⟩)
    · exact hΩj (hKΩ hx.1) ⟨hx.2.1, hC₀O hx.2.2⟩
    · exact hΩj (hH₂Ω hx) ⟨hxX, hC₀O hxC⟩
  have hpB : p ∉ polyHull B₁ := fun hpB => hpΩ (hΩ₁ (hR₁ B₁ hB₁ hB₁Ω ⟨hpB, hpY⟩))
  obtain ⟨G, hG1, hG2⟩ := exists_normalized_separator hpB
  -- separation
  refine false_of_separation (X := X₁) hO hh₁ hX₁ hC₁ hC₁O hC₀₁ (isCompact_polyHull hK₂)
    (polyHull_polyHull K₂) hH₂C₀ hK₁ (fun x hx => ⟨hx.2.1, hC₀O hx.2.2⟩) ?_ hpY hG2
    (fun x hx => hG1 x (subset_polyHull _ (Or.inl hx)))
    (fun x hx hxX => hG1 x (subset_polyHull _ (Or.inr ⟨hx, hxX, hH₂C₀ hx⟩)))
    (polyHull_mono (hKsplit.trans (union_subset (subset_union_right)
      ((subset_polyHull K₂).trans subset_union_left))) hp)
  refine (polyHull_subset_cyl (a := a) (s := s') ?_)
  rintro x (hx | hx)
  · exact fun i => (hH₂C₀ hx i).trans (by simp only [hs'def]; linarith [hsρ i])
  · exact fun i => (hx.2.2 i).trans (by simp only [hs'def]; linarith [hsρ i])

/-- **Union lemma.** If `X₁`, `X₂` are cut out by holomorphic functions on an open polydisc `Δ`
and `Ω_φ` is Runge over `X₁ ∩ Δ` and over `X₂ ∩ Δ`, then `Ω_φ` is Runge over `(X₁ ∪ X₂) ∩ Δ`. -/
theorem hartogsRunge_union {X₁ X₂ : Set (ComplexModel n)} {a : ComplexModel n}
    {ρ : Fin n → ℝ} {r₁ r₂ : ℕ} {h₁ : Fin r₁ → ComplexModel n → ℂ} {h₂ : Fin r₂ → ComplexModel n → ℂ}
    (hh₁ : ∀ l, DifferentiableOn ℂ (h₁ l) (FNA.polydisc a ρ))
    (hh₂ : ∀ l, DifferentiableOn ℂ (h₂ l) (FNA.polydisc a ρ))
    (hX₁ : ∀ z ∈ FNA.polydisc a ρ, z ∈ X₁ ↔ ∀ l, h₁ l z = 0)
    (hX₂ : ∀ z ∈ FNA.polydisc a ρ, z ∈ X₂ ↔ ∀ l, h₂ l z = 0)
    {φ : ComplexModel n → EReal} (hR₁ : HartogsRunge (X₁ ∩ FNA.polydisc a ρ) φ)
    (hR₂ : HartogsRunge (X₂ ∩ FNA.polydisc a ρ) φ) :
    HartogsRunge ((X₁ ∪ X₂) ∩ FNA.polydisc a ρ) φ := by
  intro K hK hKΩ p ⟨hp, hpY⟩
  rcases hpY.1 with h1 | h2
  · exact mem_hartogsDomain_of_mem_left hh₁ hh₂ hX₁ hX₂ hR₁ hR₂ hK hKΩ hp ⟨h1, hpY.2⟩
  · have hKΩ' : K ⊆ hartogsDomain ((X₂ ∪ X₁) ∩ FNA.polydisc a ρ) φ := by
      rw [union_comm]; exact hKΩ
    have := mem_hartogsDomain_of_mem_left hh₂ hh₁ hX₂ hX₁ hR₂ hR₁ hK hKΩ' hp ⟨h2, hpY.2⟩
    rwa [union_comm] at this

end SGPT.Unibranch.FNS
