import SGPT.Convex.AffineMinorant

/-!
# Affine minorants and Legendre duality

Source: SGPT Appendix A, `thm:Legendredual` and `prop:Legnonconvex`.
The algebraic minorant results work for arbitrary pairings; reverse duality
uses the full real dual and geometric separation. Closure-dependent consumers
belong here rather than in `Duality`, which `Semicontinuity` already imports.
-/

namespace SGPT.Convex

open Set

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Subtraction from a finite real value is an order-reversing involution on `EReal`. -/
theorem real_sub_le_iff_comm (a : ℝ) (b c : EReal) :
    (a : EReal) - b ≤ c ↔ (a : EReal) - c ≤ b := by
  cases b using EReal.rec <;> cases c using EReal.rec <;>
    simp [← EReal.coe_sub, EReal.coe_le_coe_iff]
  constructor <;> intro h <;> linarith

/-- A finite upper bound on the conjugate is exactly an affine minorant. -/
theorem conjugate_le_coe_iff (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal)
    (y : W) (c : ℝ) :
    conjugate B f y ≤ (c : EReal) ↔ ∀ x, ((B x y - c : ℝ) : EReal) ≤ f x := by
  simp only [conjugate, iSup_le_iff]
  exact forall_congr' fun x ↦ by
    simpa only [EReal.coe_sub] using real_sub_le_iff_comm (B x y) (f x) (c : EReal)

/-- The second conjugate with reversed pairing lies below the original obstacle. -/
theorem biconjugate_le (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal) :
    conjugate B.flip (conjugate B f) ≤ f := by
  intro x
  apply iSup_le
  intro y
  apply (real_sub_le_iff_comm (B x y) (conjugate B f y) (f x)).mpr
  exact le_iSup (fun z ↦ (B z y : EReal) - f z) x

/-- The Legendre transform already ignores convexification of any obstacle.
Closure invariance completes the source `prop:Legnonconvex` in a separate consumer. -/
theorem conjugate_lowerConvexEnvelope (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal) :
    conjugate B (lowerConvexEnvelope f) = conjugate B f := by
  funext y
  have hbound (c : ℝ) (hc : conjugate B f y ≤ (c : EReal)) :
      conjugate B (lowerConvexEnvelope f) y ≤ (c : EReal) := by
    apply (conjugate_le_coe_iff B (lowerConvexEnvelope f) y c).mpr
    have ha : IsConvex (fun x ↦ ((B x y - c : ℝ) : EReal)) := by
      simpa only [LinearMap.flip_apply, sub_eq_add_neg] using
        isConvex_affine (B.flip y) (-c)
    exact le_lowerConvexEnvelope ha ((conjugate_le_coe_iff B f y c).mp hc)
  apply le_antisymm _ (conjugate_antitone B (lowerConvexEnvelope_le f) y)
  cases hfy : conjugate B f y using EReal.rec with
  | bot =>
    apply le_bot_iff.mpr
    apply (EReal.eq_bot_iff_forall_lt _).mpr
    intro c
    have hb := hbound (c - 1) (by rw [hfy]; exact bot_le)
    exact hb.trans_lt (EReal.coe_lt_coe (by linarith : c - 1 < c))
  | coe c => exact hbound c (le_of_eq hfy)
  | top => exact le_top

/-- One bottom value forces the entire conjugate to be top. -/
theorem conjugate_eq_top_of_exists_bot (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal)
    (hf : ∃ x, f x = ⊥) : conjugate B f = (fun _ ↦ ⊤) := by
  obtain ⟨x, hx⟩ := hf
  funext y
  apply top_le_iff.mp
  simpa [conjugate, hx] using le_iSup (fun z ↦ (B z y : EReal) - f z) x

/-- Properness reflects through conjugation for every convex obstacle and pairing. -/
theorem isProper_of_isProper_conjugate (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) {f : V → EReal}
    (hf : IsConvex f) (hg : IsProper (conjugate B f)) : IsProper f := by
  classical
  obtain ⟨y, hy⟩ := hg.2.1
  have hnobot : ∀ x, f x ≠ ⊥ := by
    intro x hx
    have ht := congrFun (conjugate_eq_top_of_exists_bot B f ⟨x, hx⟩) y
    exact (ne_of_lt hy) ht
  have hne : ∃ x, f x ≠ ⊤ := by
    by_contra h
    have htop : f = (fun _ ↦ ⊤) := by
      funext x
      by_contra hx
      exact h ⟨x, hx⟩
    have hb : conjugate B f 0 = ⊥ := by simp [htop, conjugate]
    exact hg.2.2 0 hb
  obtain ⟨x, hx⟩ := hne
  exact ⟨hf, ⟨x, lt_top_iff_ne_top.mpr hx⟩, hnobot⟩

section ClosedProper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A linear functional on the product splits into a horizontal functional and height term. -/
theorem functional_prod_decomposition (L : (E × ℝ) →L[ℝ] ℝ) (z : E) (s : ℝ) :
    L (z, s) = L (z, 0) + s * L (0, 1) := by
  have hp : (z, s) = (z, (0 : ℝ)) + s • ((0 : E), (1 : ℝ)) := by
    ext <;> simp
  rw [hp, map_add, map_smul]
  rfl

/-- Closed proper epigraph separation produces an actual affine minorant. -/
theorem exists_affine_minorant_of_isProper_lowerSemicontinuous {f : E → EReal}
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    ∃ (m : Module.Dual ℝ E) (b : ℝ), ∀ z, ((m z + b : ℝ) : EReal) ≤ f z := by
  obtain ⟨x₀, hx₀⟩ := hf.2.1
  let q := (f x₀).toReal
  have hqx : f x₀ = (q : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx₀) (hf.2.2 x₀)).symm
  have hnot : (x₀, q - 1) ∉ epigraph f := by
    change ¬f x₀ ≤ ((q - 1 : ℝ) : EReal)
    rw [hqx, EReal.coe_le_coe_iff]
    linarith
  obtain ⟨L, u, hpoint, hepi⟩ := geometric_hahn_banach_point_closed hf.1
    (isClosed_epigraph_iff_lowerSemicontinuous.mpr hlsc) hnot
  let a : ℝ := L (0, 1)
  have hqepi : (x₀, q) ∈ epigraph f := by
    change f x₀ ≤ (q : EReal)
    exact hqx.le
  have ha : 0 < a := by
    have hhigh := hepi (x₀, q) hqepi
    rw [functional_prod_decomposition, functional_prod_decomposition] at hpoint hhigh
    dsimp [a]
    nlinarith
  let ℓ : Module.Dual ℝ E := L.toLinearMap.comp (LinearMap.inl ℝ E ℝ)
  let m : Module.Dual ℝ E := (-a⁻¹) • ℓ
  let b : ℝ := u / a
  have hvalue (z : E) : m z + b = (u - L (z, 0)) / a := by
    simp only [m, b, ℓ, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.inl_apply, smul_eq_mul, div_eq_mul_inv]
    change (-a⁻¹) * L (z, 0) + u * a⁻¹ = (u - L (z, 0)) * a⁻¹
    ring
  refine ⟨m, b, ?_⟩
  intro z
  cases hz : f z using EReal.rec with
  | bot => exact False.elim (hf.2.2 z hz)
  | top => exact le_top
  | coe c =>
    have hzc : (z, c) ∈ epigraph f := by
      change f z ≤ (c : EReal)
      exact hz.le
    have hsep := hepi (z, c) hzc
    rw [functional_prod_decomposition] at hsep
    rw [hvalue, EReal.coe_le_coe_iff]
    apply (div_le_iff₀ ha).mpr
    change u - L (z, 0) ≤ c * a
    dsimp [a]
    linarith

/-- For a closed proper obstacle, an actual affine minorant gives a finite
conjugate value; hence the full-dual conjugate is proper. -/
theorem isProper_conjugate_dual_of_isProper_lowerSemicontinuous {f : E → EReal}
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    IsProper (conjugate (Module.Dual.eval ℝ E) f) := by
  obtain ⟨m, b, hminor⟩ := exists_affine_minorant_of_isProper_lowerSemicontinuous hf hlsc
  have hbound : conjugate (Module.Dual.eval ℝ E) f m ≤ ((-b : ℝ) : EReal) := by
    apply (conjugate_le_coe_iff _ f m (-b)).mpr
    simpa only [Module.Dual.eval_apply, sub_neg_eq_add] using hminor
  obtain ⟨x, hx⟩ := hf.2.1
  exact ⟨isConvex_conjugate _ f, ⟨m, hbound.trans_lt (EReal.coe_lt_top _)⟩,
    conjugate_ne_bot_of_exists_ne_top _ f ⟨x, ne_of_lt hx⟩⟩

/-- Every point strictly below a closed proper function is strictly below an
actual affine minorant. Horizontal separators are tilted using a previously
constructed affine minorant, rather than assumed to have positive height. -/
theorem exists_affine_minorant_above_of_isProper_lowerSemicontinuous {f : E → EReal}
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) (x : E) (r : ℝ)
    (hr : (r : EReal) < f x) :
    ∃ (m : Module.Dual ℝ E) (b : ℝ),
      r < m x + b ∧ ∀ z, ((m z + b : ℝ) : EReal) ≤ f z := by
  have hnot : (x, r) ∉ epigraph f := by
    change ¬ f x ≤ (r : EReal)
    exact not_le.mpr hr
  obtain ⟨L, u, hpoint, hepi⟩ := geometric_hahn_banach_point_closed hf.1
    (isClosed_epigraph_iff_lowerSemicontinuous.mpr hlsc) hnot
  let a : ℝ := L (0, 1)
  let ℓ : Module.Dual ℝ E := L.toLinearMap.comp (LinearMap.inl ℝ E ℝ)
  have hell (z : E) : ℓ z = L (z, 0) := rfl
  have ha : 0 ≤ a := by
    by_contra hn
    have hn : a < 0 := lt_of_not_ge hn
    obtain ⟨z, hz⟩ := hf.2.1
    let q : ℝ := (f z).toReal
    have hq : f z = (q : EReal) :=
      (EReal.coe_toReal (ne_of_lt hz) (hf.2.2 z)).symm
    obtain ⟨t, ht, hlarge⟩ := exists_pos_lt_mul (neg_pos.mpr hn) (L (z, q) - u)
    have hzt : (z, q + t) ∈ epigraph f := by
      change f z ≤ ((q + t : ℝ) : EReal)
      rw [hq, EReal.coe_le_coe_iff]
      linarith
    have hsep := hepi (z, q + t) hzt
    rw [functional_prod_decomposition] at hsep hlarge
    dsimp [a] at hn hlarge
    nlinarith
  rcases ha.eq_or_lt with ha | ha
  · have ha : a = 0 := ha.symm
    obtain ⟨m₀, b₀, hbase⟩ := exists_affine_minorant_of_isProper_lowerSemicontinuous hf hlsc
    have hx : L (x, 0) < u := by
      rw [functional_prod_decomposition] at hpoint
      change L (x, 0) + r * a < u at hpoint
      simpa [ha] using hpoint
    obtain ⟨t, ht, hlarge⟩ := exists_pos_lt_mul (sub_pos.mpr hx) (r - (m₀ x + b₀))
    refine ⟨m₀ - t • ℓ, b₀ + t * u, ?_, ?_⟩
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hell]
      nlinarith
    · intro z
      cases hz : f z using EReal.rec with
      | bot => exact False.elim (hf.2.2 z hz)
      | top => exact le_top
      | coe c =>
        have hzc : (z, c) ∈ epigraph f := by
          change f z ≤ (c : EReal)
          exact hz.le
        have hsep := hepi (z, c) hzc
        rw [functional_prod_decomposition] at hsep
        change u < L (z, 0) + c * a at hsep
        have hzbase := hbase z
        rw [hz, EReal.coe_le_coe_iff] at hzbase
        rw [EReal.coe_le_coe_iff]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hell]
        rw [ha, mul_zero, add_zero] at hsep
        nlinarith
  · let m : Module.Dual ℝ E := (-a⁻¹) • ℓ
    let b : ℝ := u / a
    have hvalue (z : E) : m z + b = (u - L (z, 0)) / a := by
      simp only [m, b, LinearMap.smul_apply, smul_eq_mul, hell, div_eq_mul_inv]
      ring
    refine ⟨m, b, ?_, ?_⟩
    · rw [hvalue, lt_div_iff₀ ha]
      rw [functional_prod_decomposition] at hpoint
      change L (x, 0) + r * a < u at hpoint
      linarith
    · intro z
      cases hz : f z using EReal.rec with
      | bot => exact False.elim (hf.2.2 z hz)
      | top => exact le_top
      | coe c =>
        have hzc : (z, c) ∈ epigraph f := by
          change f z ≤ (c : EReal)
          exact hz.le
        have hsep := hepi (z, c) hzc
        rw [functional_prod_decomposition] at hsep
        rw [hvalue, EReal.coe_le_coe_iff, div_le_iff₀ ha]
        change u - L (z, 0) ≤ c * a
        change u < L (z, 0) + c * a at hsep
        linarith

/-- Fenchel--Moreau duality for a closed proper function, using the actual full
real dual and actual geometric separation of its epigraph. -/
theorem biconjugate_eq_of_isProper_lowerSemicontinuous {f : E → EReal}
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) :
    conjugate (Module.Dual.eval ℝ E).flip
      (conjugate (Module.Dual.eval ℝ E) f) = f := by
  funext x
  apply le_antisymm (biconjugate_le _ f x)
  by_contra h
  obtain ⟨r, hr₁, hr₂⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  obtain ⟨m, b, hr, hminor⟩ :=
    exists_affine_minorant_above_of_isProper_lowerSemicontinuous hf hlsc x r hr₂
  have hc : conjugate (Module.Dual.eval ℝ E) f m ≤ ((-b : ℝ) : EReal) := by
    apply (conjugate_le_coe_iff _ f m (-b)).mpr
    simpa only [Module.Dual.eval_apply, sub_neg_eq_add] using hminor
  have hterm : ((m x + b : ℝ) : EReal) ≤
      (m x : EReal) - conjugate (Module.Dual.eval ℝ E) f m := by
    simpa only [← EReal.coe_sub, sub_neg_eq_add] using
      EReal.sub_le_sub (le_refl (m x : EReal)) hc
  have hsup := le_iSup
    (fun y ↦ (((Module.Dual.eval ℝ E).flip y x : ℝ) : EReal) -
      conjugate (Module.Dual.eval ℝ E) f y) m
  exact (not_lt_of_ge (hterm.trans hsup))
    (hr₁.trans (EReal.coe_lt_coe hr))

/-- The pointwise supremum of all actual real affine minorants. -/
noncomputable def affineEnvelope (f : E → EReal) (x : E) : EReal :=
  ⨆ (m : Module.Dual ℝ E) (b : ℝ) (_ : ∀ z, ((m z + b : ℝ) : EReal) ≤ f z),
    ((m x + b : ℝ) : EReal)

theorem affineEnvelope_le (f : E → EReal) : affineEnvelope f ≤ f := by
  intro x
  apply iSup_le
  intro m
  apply iSup_le
  intro b
  exact iSup_le fun h ↦ h x

/-- The source's affine representation, with actual minorants rather than an
assumed supremum certificate, including both infinite constant branches. -/
theorem affineEnvelope_eq_of_isClosedConvex {f : E → EReal}
    (hf : IsClosedConvex f) : affineEnvelope f = f := by
  funext x
  apply le_antisymm (affineEnvelope_le f x)
  rcases hf with hb | ht | hp
  · rw [hb]
    exact bot_le
  · by_contra h
    obtain ⟨r, hr₁, hr₂⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
    have hminor : ∀ z, (((0 : Module.Dual ℝ E) z + (r + 1) : ℝ) : EReal) ≤ f z := by
      intro z
      rw [ht]
      exact le_top
    have hsup : ((r + 1 : ℝ) : EReal) ≤ affineEnvelope f x := by
      unfold affineEnvelope
      apply le_iSup_of_le (0 : Module.Dual ℝ E)
      apply le_iSup_of_le (r + 1)
      exact le_iSup_of_le hminor (by simp)
    exact not_lt_of_ge hsup (hr₁.trans (EReal.coe_lt_coe (by linarith : r < r + 1)))
  · by_contra h
    obtain ⟨r, hr₁, hr₂⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
    obtain ⟨m, b, hr, hminor⟩ :=
      exists_affine_minorant_above_of_isProper_lowerSemicontinuous hp.1 hp.2 x r hr₂
    have hsup : ((m x + b : ℝ) : EReal) ≤ affineEnvelope f x :=
      le_iSup_of_le m (le_iSup_of_le b (le_iSup_of_le hminor le_rfl))
    exact not_lt_of_ge hsup (hr₁.trans (EReal.coe_lt_coe hr))

/-- Biconjugation for the full source classification of closed convex functions. -/
theorem biconjugate_eq_of_isClosedConvex {f : E → EReal} (hf : IsClosedConvex f) :
    conjugate (Module.Dual.eval ℝ E).flip
      (conjugate (Module.Dual.eval ℝ E) f) = f := by
  rcases hf with hb | ht | hp
  · rw [hb]
    funext x
    simp [conjugate]
  · rw [ht]
    funext x
    simp [conjugate]
  · exact biconjugate_eq_of_isProper_lowerSemicontinuous hp.1 hp.2

end ClosedProper

section ClosureInvariance

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [T2Space V] [FiniteDimensional ℝ V]

/-- Source closure does not change the conjugate. Finite dimension ensures every
linear summand is continuous; no convexity of the original obstacle is needed. -/
theorem conjugate_convexClosure (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal) :
    conjugate B (convexClosure f) = conjugate B f := by
  classical
  by_cases hb : ∃ x, f x = ⊥
  · rw [convexClosure_of_exists_bot hb, conjugate_eq_top_of_exists_bot B f hb]
    funext y
    simp [conjugate]
  have hnobot : ∀ x, f x ≠ ⊥ := by simpa only [not_exists] using hb
  rw [convexClosure_of_forall_ne_bot hnobot]
  funext y
  have hbound (c : ℝ) (hc : conjugate B f y ≤ (c : EReal)) :
      conjugate B (regularization f) y ≤ (c : EReal) := by
    apply (conjugate_le_coe_iff B (regularization f) y c).mpr
    have hlsc : LowerSemicontinuous (fun x ↦ ((B x y - c : ℝ) : EReal)) := by
      apply isClosed_epigraph_iff_lowerSemicontinuous.mp
      simpa only [LinearMap.flip_apply, EReal.coe_sub] using
        isClosed_epigraph_linear_sub (B.flip y) (c : EReal)
    exact le_regularization_of_lowerSemicontinuous_le hlsc
      ((conjugate_le_coe_iff B f y c).mp hc)
  apply le_antisymm _ (conjugate_antitone B (regularization_le f) y)
  cases hfy : conjugate B f y using EReal.rec with
  | bot =>
    apply le_bot_iff.mpr
    apply (EReal.eq_bot_iff_forall_lt _).mpr
    intro c
    exact (hbound (c - 1) (by rw [hfy]; exact bot_le)).trans_lt
      (EReal.coe_lt_coe (by linarith : c - 1 < c))
  | coe c => exact hbound c (le_of_eq hfy)
  | top => exact le_top

/-- Full source `prop:Legnonconvex`: convexification followed by closure leaves
the actual full-domain Legendre transform unchanged. -/
theorem conjugate_convexClosure_lowerConvexEnvelope (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (f : V → EReal) :
    conjugate B (convexClosure (lowerConvexEnvelope f)) = conjugate B f := by
  rw [conjugate_convexClosure, conjugate_lowerConvexEnvelope]

end ClosureInvariance

section FiniteClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The exact source biconjugate/closure consumer after a genuine continuous
real minorant has been produced. Unconditional minorant existence for a proper
nonclosed obstacle remains a separate finite-dimensional producer. -/
theorem biconjugate_eq_convexClosure_of_continuous_minorant {f : E → EReal}
    (hf : IsProper f) (g : E → ℝ) (hg : Continuous g)
    (hgf : (fun x ↦ (g x : EReal)) ≤ f) :
    conjugate (Module.Dual.eval ℝ E).flip
      (conjugate (Module.Dual.eval ℝ E) f) = convexClosure f := by
  rw [← conjugate_convexClosure (Module.Dual.eval ℝ E) f]
  exact biconjugate_eq_of_isClosedConvex
    (isClosedConvex_convexClosure_of_continuous_minorant hf g hg hgf)

/-- The unconditional properness clause of source `thm:closurepropconv`.
The continuous minorant is constructed from the actual proper epigraph. -/
theorem isProper_convexClosure_of_isProper {f : E → EReal} (hf : IsProper f) :
    IsProper (convexClosure f) := by
  obtain ⟨m, b, hminor⟩ := exists_continuous_affine_minorant_of_isProper hf
  exact isProper_convexClosure_of_continuous_minorant hf (fun z ↦ m z + b)
    (m.continuous.add continuous_const) hminor

/-- Proper convex obstacles have proper source-closed convex closure. -/
theorem isClosedConvex_convexClosure_of_isProper {f : E → EReal} (hf : IsProper f) :
    IsClosedConvex (convexClosure f) :=
  Or.inr (Or.inr ⟨isProper_convexClosure_of_isProper hf,
    lowerSemicontinuous_convexClosure f⟩)

/-- Full source Legendre properness equivalence in finite dimension. -/
theorem isProper_conjugate_dual_iff {f : E → EReal} (hf : IsConvex f) :
    IsProper (conjugate (Module.Dual.eval ℝ E) f) ↔ IsProper f := by
  constructor
  · exact isProper_of_isProper_conjugate _ hf
  · intro hp
    obtain ⟨m, b, hminor⟩ := exists_continuous_affine_minorant_of_isProper hp
    have hbound : conjugate (Module.Dual.eval ℝ E) f m.toLinearMap ≤ ((-b : ℝ) : EReal) := by
      apply (conjugate_le_coe_iff _ f m.toLinearMap (-b)).mpr
      simpa only [Module.Dual.eval_apply, sub_neg_eq_add,
        ContinuousLinearMap.coe_coe] using hminor
    obtain ⟨x, hx⟩ := hp.2.1
    exact ⟨isConvex_conjugate _ f,
      ⟨m.toLinearMap, hbound.trans_lt (EReal.coe_lt_top _)⟩,
      conjugate_ne_bot_of_exists_ne_top _ f ⟨x, ne_of_lt hx⟩⟩

/-- Full source biconjugation, including nonclosed proper obstacles and both
exceptional improper cases, using the actual closure construction. -/
theorem biconjugate_eq_convexClosure {f : E → EReal} (hf : IsConvex f) :
    conjugate (Module.Dual.eval ℝ E).flip
      (conjugate (Module.Dual.eval ℝ E) f) = convexClosure f := by
  classical
  by_cases hb : ∃ x, f x = ⊥
  · rw [convexClosure_of_exists_bot hb, conjugate_eq_top_of_exists_bot _ f hb]
    funext x
    simp [conjugate]
  have hnobot : ∀ x, f x ≠ ⊥ := by simpa only [not_exists] using hb
  by_cases ht : f = (fun _ ↦ ⊤)
  · have hc : IsClosedConvex f := Or.inr (Or.inl ht)
    rw [biconjugate_eq_of_isClosedConvex hc, convexClosure_eq_self_of_isClosedConvex hc]
  have hdomain : ∃ x, f x ≠ ⊤ := by
    by_contra hn
    apply ht
    funext x
    by_contra hx
    exact hn ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hdomain
  have hp : IsProper f := ⟨hf, ⟨x, lt_top_iff_ne_top.mpr hx⟩, hnobot⟩
  obtain ⟨m, b, hminor⟩ := exists_continuous_affine_minorant_of_isProper hp
  exact biconjugate_eq_convexClosure_of_continuous_minorant hp (fun z ↦ m z + b)
    (m.continuous.add continuous_const) hminor

end FiniteClosure

end SGPT.Convex
