import SGPT.Unibranch.E2Nov16FNHolomorphicHullMaximum

/-!
# Polynomial hulls: elementary facts for the Fornæss–Narasimhan programme

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), §5 (Lemma 5.2, Theorems 5.3.1 and 5.4), used for `thm:FN` (2) ⇒ (1)
(`appendix_unibranch.tex`). There, for a closed subvariety `X` of a polydisc `Δⁿ`, the hull of a
compact `K ⊆ X` is "the polynomially convex hull of `K` (= hull in `X`)". This file makes that
identification precise with the polynomial hull `polyHull` of `E2Nov16FNPolynomialPolyhedron`:

* `polyHull_mono`, `polyHull_polyHull`: monotonicity and idempotence.
* `polyHull_subset_closedBall`, `polyHull_subset_ball`, `polyHull_subset_closedPolydisc`,
  `polyHull_subset_polydisc`: balls and polydiscs are polynomially convex.
* `eq_zero_on_polyHull`, `polyHull_subset_zeroLocus`: a holomorphic function on a neighbourhood
  of `K̂` vanishing on `K` vanishes on `K̂` (Oka–Weil); hence the hull of a compact subset of an
  analytic set cut out by holomorphic functions on a neighbourhood of the hull stays in it.
* `holHull`, `holHull_eq_polyHull`: the hull with respect to all holomorphic functions on an
  open `D ⊇ K̂` equals `K̂`; `inter_holHull_eq_polyHull` is FN80's "(= hull in `X`)" for
  `X ⊆ Δⁿ` cut out by holomorphic functions on `Δⁿ`.
* `image_polyHull_subset`, `polyHull_mapsTo_of_mapsTo`, `diagScale_mem_polyHull`: polynomial
  maps send hulls into hulls; hulls of sets invariant under the diagonal maps
  `z ↦ (λᵢ zᵢ)` (e.g. circular or Hartogs-complete sets) are invariant.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNR

open E2Nov16FNPolynomialPolyhedron E2Nov16FNHolomorphicHullMaximum

variable {n : ℕ}

theorem mem_polyHull_iff {K : Set (ComplexModel n)} {z : ComplexModel n} :
    z ∈ polyHull K ↔
      ∀ (p : Poly n) (C : ℝ), (∀ x ∈ K, ‖polyEval p x‖ ≤ C) → ‖polyEval p z‖ ≤ C :=
  Iff.rfl

/-- The polynomial hull is monotone. -/
theorem polyHull_mono {K L : Set (ComplexModel n)} (h : K ⊆ L) : polyHull K ⊆ polyHull L :=
  fun _ hz p C hC => hz p C fun x hx => hC x (h hx)

/-- The polynomial hull is idempotent. -/
theorem polyHull_polyHull (K : Set (ComplexModel n)) : polyHull (polyHull K) = polyHull K := by
  refine Subset.antisymm ?_ (subset_polyHull _)
  intro z hz p C hC
  exact hz p C fun x hx => hx p C hC

theorem polyEval_X_sub_C (i : Fin n) (a : ℂ) (z : ComplexModel n) :
    polyEval (MvPolynomial.X i - MvPolynomial.C a) z = z i - a := by
  simp [polyEval]

/-- The linear polynomial `x ↦ ⟪v, x - a⟫`. -/
def innerPoly (v a : ComplexModel n) : Poly n :=
  ∑ i, MvPolynomial.C ((starRingEnd ℂ) (v i)) * (MvPolynomial.X i - MvPolynomial.C (a i))

theorem polyEval_innerPoly (v a x : ComplexModel n) :
    polyEval (innerPoly v a) x = inner ℂ v (x - a) := by
  simp only [innerPoly, polyEval, map_sum, map_mul, MvPolynomial.eval_C, map_sub,
    MvPolynomial.eval_X, PiLp.inner_apply, RCLike.inner_apply, PiLp.sub_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Closed balls are polynomially convex. -/
theorem polyHull_subset_closedBall {K : Set (ComplexModel n)} {a : ComplexModel n} {r : ℝ}
    (hK : K ⊆ closedBall a r) : polyHull K ⊆ closedBall a r := by
  intro z hz
  rw [mem_closedBall, dist_eq_norm]
  set v := z - a
  have hbound : ∀ x ∈ K, ‖polyEval (innerPoly v a) x‖ ≤ ‖v‖ * r := by
    intro x hx
    rw [polyEval_innerPoly]
    refine (norm_inner_le_norm v (x - a)).trans ?_
    gcongr
    simpa [dist_eq_norm] using hK hx
  have hz' := hz _ _ hbound
  rw [polyEval_innerPoly, inner_self_eq_norm_sq_to_K] at hz'
  replace hz' : ‖v‖ ^ 2 ≤ ‖v‖ * r := by simpa [norm_pow] using hz'
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0]
    by_contra hr
    push Not at hr
    -- `r < 0` makes `K` empty, hence the hull empty
    have hKe : K = ∅ := by
      ext x
      simp only [mem_empty_iff_false, iff_false]
      intro hx
      have := hK hx
      rw [mem_closedBall] at this
      linarith [dist_nonneg (x := x) (y := a)]
    rw [hKe, polyHull_empty] at hz
    exact hz
  · nlinarith

/-- The coordinate polynomials: closed polydiscs are polynomially convex. -/
theorem polyHull_subset_closedPolydisc {K : Set (ComplexModel n)} {a : ComplexModel n}
    {r : Fin n → ℝ} (hK : ∀ x ∈ K, ∀ i, ‖x i - a i‖ ≤ r i) :
    polyHull K ⊆ {z | ∀ i, ‖z i - a i‖ ≤ r i} := by
  intro z hz i
  have h := hz (MvPolynomial.X i - MvPolynomial.C (a i)) (r i) fun x hx => by
    rw [polyEval_X_sub_C]; exact hK x hx i
  rwa [polyEval_X_sub_C] at h

/-- Open polydiscs are polynomially convex (for compact sets). -/
theorem polyHull_subset_polydisc {K : Set (ComplexModel n)} (hK : IsCompact K)
    {a : ComplexModel n} {r : Fin n → ℝ} (hKr : ∀ x ∈ K, ∀ i, ‖x i - a i‖ < r i) :
    polyHull K ⊆ {z | ∀ i, ‖z i - a i‖ < r i} := by
  rcases K.eq_empty_or_nonempty with hKe | hne
  · rw [hKe, polyHull_empty]; exact empty_subset _
  have hmax (i : Fin n) : ∃ s : ℝ, s < r i ∧ ∀ x ∈ K, ‖x i - a i‖ ≤ s := by
    have hc : ContinuousOn (fun x : ComplexModel n => ‖x i - a i‖) K :=
      (((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous.sub
        continuous_const).norm).continuousOn
    obtain ⟨x₀, hx₀, hx₀max⟩ := hK.exists_isMaxOn hne hc
    exact ⟨_, hKr x₀ hx₀ i, fun x hx => hx₀max hx⟩
  choose s hs hsK using hmax
  intro z hz i
  exact lt_of_le_of_lt (polyHull_subset_closedPolydisc (r := s) (fun x hx i => hsK i x hx) hz i)
    (hs i)

/-- The open polydisc `Δ(a, r) = {z : |zᵢ - aᵢ| < rᵢ}`. -/
theorem isOpen_polydisc (a : ComplexModel n) (r : Fin n → ℝ) :
    IsOpen {z : ComplexModel n | ∀ i, ‖z i - a i‖ < r i} := by
  have : {z : ComplexModel n | ∀ i, ‖z i - a i‖ < r i} =
      ⋂ i, {z : ComplexModel n | ‖z i - a i‖ < r i} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).continuous.sub
      continuous_const).norm) continuous_const

/-- Open balls are polynomially convex (for compact sets). -/
theorem polyHull_subset_ball {K : Set (ComplexModel n)} (hK : IsCompact K)
    {a : ComplexModel n} {r : ℝ} (hKr : K ⊆ ball a r) : polyHull K ⊆ ball a r := by
  rcases K.eq_empty_or_nonempty with hKe | hne
  · rw [hKe, polyHull_empty]; exact empty_subset _
  obtain ⟨x₀, hx₀, hx₀max⟩ := hK.exists_isMaxOn hne
    (continuous_id.dist (continuous_const (y := a))).continuousOn
  refine (polyHull_subset_closedBall (a := a) (r := dist x₀ a) fun x hx => ?_).trans
    (closedBall_subset_ball (mem_ball.mp (hKr hx₀)))
  exact mem_closedBall.mpr (hx₀max hx)

/-- A function holomorphic on an open neighbourhood of `K̂` and vanishing on `K` vanishes on
`K̂` (Oka–Weil). -/
theorem eq_zero_on_polyHull {K W : Set (ComplexModel n)} (hK : IsCompact K) (hW : IsOpen W)
    (hKW : polyHull K ⊆ W) {f : ComplexModel n → ℂ} (hf : DifferentiableOn ℂ f W)
    (h0 : ∀ x ∈ K, f x = 0) : ∀ z ∈ polyHull K, f z = 0 := by
  intro z hz
  have h := norm_le_on_polyHull hK hW hKW f hf 0 (fun x hx => by simp [h0 x hx]) z hz
  exact norm_le_zero_iff.mp h

/-- The hull of a compact subset of the common zero set of a family of functions holomorphic on
an open neighbourhood `W` of the hull stays in that zero set. -/
theorem polyHull_subset_zeroLocus {ι : Type*} {K W : Set (ComplexModel n)} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : polyHull K ⊆ W) {f : ι → ComplexModel n → ℂ}
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) (hKf : ∀ x ∈ K, ∀ i, f i x = 0) :
    polyHull K ⊆ {z | z ∈ W ∧ ∀ i, f i z = 0} :=
  fun z hz => ⟨hKW hz, fun i => eq_zero_on_polyHull hK hW hKW (hf i) (fun x hx => hKf x hx i) z hz⟩

/-- The hull of `K` with respect to all functions holomorphic on `D`. -/
def holHull (D K : Set (ComplexModel n)) : Set (ComplexModel n) :=
  {z | z ∈ D ∧ ∀ f : ComplexModel n → ℂ, DifferentiableOn ℂ f D →
    ∀ C : ℝ, (∀ x ∈ K, ‖f x‖ ≤ C) → ‖f z‖ ≤ C}

/-- If `K̂ ⊆ D` (`D` open), the `𝒪(D)`-hull of `K` is the polynomial hull. -/
theorem holHull_eq_polyHull {K D : Set (ComplexModel n)} (hK : IsCompact K) (hD : IsOpen D)
    (hKD : polyHull K ⊆ D) : holHull D K = polyHull K := by
  apply Subset.antisymm
  · intro z hz p C hC
    exact hz.2 (polyEval p) (E2Nov16FNPolynomialGraphBox.differentiable_polyEval p).differentiableOn
      C hC
  · intro z hz
    exact ⟨hKD hz, fun f hf C hC => norm_le_on_polyHull hK hD hKD f hf C hC z hz⟩

/-- FN80's "polynomially convex hull (= hull in `X`)": for `X ⊆ D` the common zero set in the
open set `D ⊇ K̂` of functions holomorphic on `D` (e.g. a closed subvariety of a polydisc
`D = Δⁿ` given by global equations) and `K ⊆ X` compact, the hull of `K` in `X` with respect to
the restrictions to `X` of `𝒪(D)` is the polynomial hull of `K`, and it lies in `X`. -/
theorem inter_holHull_eq_polyHull {ι : Type*} {K D : Set (ComplexModel n)} (hK : IsCompact K)
    (hD : IsOpen D) (hKD : polyHull K ⊆ D) {f : ι → ComplexModel n → ℂ}
    (hf : ∀ i, DifferentiableOn ℂ (f i) D) (hKX : ∀ x ∈ K, ∀ i, f i x = 0) :
    {z | z ∈ D ∧ ∀ i, f i z = 0} ∩ holHull D K = polyHull K := by
  rw [holHull_eq_polyHull hK hD hKD]
  exact inter_eq_right.mpr (polyHull_subset_zeroLocus hK hD hKD hf hKX)

/-! ### Polynomial maps -/

/-- The polynomial map `ℂⁿ → ℂᵐ` with components `φ i`. -/
def polyMap {m : ℕ} (φ : Fin m → Poly n) (z : ComplexModel n) : ComplexModel m :=
  WithLp.toLp 2 fun i => polyEval (φ i) z

theorem polyEval_bind₁ {m : ℕ} (φ : Fin m → Poly n) (p : Poly m) (z : ComplexModel n) :
    polyEval (MvPolynomial.bind₁ φ p) z = polyEval p (polyMap φ z) := by
  show MvPolynomial.eval₂Hom (RingHom.id ℂ) _ (MvPolynomial.bind₁ φ p) =
    MvPolynomial.eval₂Hom (RingHom.id ℂ) _ p
  rw [MvPolynomial.eval₂Hom_bind₁]
  rfl

/-- Polynomial maps send hulls into hulls. -/
theorem image_polyHull_subset {m : ℕ} (φ : Fin m → Poly n) (K : Set (ComplexModel n)) :
    polyMap φ '' polyHull K ⊆ polyHull (polyMap φ '' K) := by
  rintro _ ⟨z, hz, rfl⟩ p C hC
  have h := hz (MvPolynomial.bind₁ φ p) C fun x hx => by
    rw [polyEval_bind₁]; exact hC _ ⟨x, hx, rfl⟩
  rwa [polyEval_bind₁] at h

/-- A compact set mapped into itself by a polynomial self-map has its hull mapped into itself. -/
theorem polyHull_mapsTo_of_mapsTo (φ : Fin n → Poly n) {K : Set (ComplexModel n)}
    (hK : MapsTo (polyMap φ) K K) : MapsTo (polyMap φ) (polyHull K) (polyHull K) := by
  intro z hz
  exact polyHull_mono (image_subset_iff.mpr hK) (image_polyHull_subset φ K ⟨z, hz, rfl⟩)

/-- Diagonal scaling `z ↦ (λᵢ zᵢ)`. -/
def diagScale (c : Fin n → ℂ) (z : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 fun i => c i * z i

theorem diagScale_eq_polyMap (c : Fin n → ℂ) :
    diagScale c = polyMap fun i => MvPolynomial.C (c i) * MvPolynomial.X i := by
  funext z
  simp [diagScale, polyMap, polyEval]

/-- The hull of a set invariant under a diagonal scaling is invariant. With
`λ = (1, …, 1, e^{iθ})` for all `θ` this says that the hull of a circular set is circular; with
`|λₙ| ≤ 1` it says that the hull of a Hartogs-complete set is Hartogs-complete. -/
theorem diagScale_mem_polyHull (c : Fin n → ℂ) {K : Set (ComplexModel n)}
    (hK : ∀ x ∈ K, diagScale c x ∈ K) {z : ComplexModel n} (hz : z ∈ polyHull K) :
    diagScale c z ∈ polyHull K := by
  rw [diagScale_eq_polyMap] at hK ⊢
  exact polyHull_mapsTo_of_mapsTo _ (fun x hx => hK x hx) hz

end SGPT.Unibranch.FNR
