import SGPT.LineBundle.SectionFiltration
import SGPT.IGood.DXLow2Mul
import SGPT.IGood.KBigDXMain

/-!
# Filtrations of section rings, abstractly and on compact Kähler manifolds

Source `def:testcurve:L1134` (chapter *Test curves*), in the book's setting of a connected compact
Kähler manifold `X` (not necessarily projective). Blueprint `claude-k-filt`, nodes
`claude-k-filt:graded`, `claude-k-filt:ring`, `claude-k-filt:def`.

The book's definition only uses the graded pieces `H⁰(X, L^k)` of the section ring
`R(X, L) = ⊕_k H⁰(X, L^k)` and the products `H⁰(X, L^k) × H⁰(X, L^{k'}) → H⁰(X, L^{k+k'})`.
We therefore state it once for an abstract graded family `S : ℕ → Type` of complex vector spaces
with a product `mul k k' : S k → S k' → S (k + k')` (`GradedFiltration`), prove the theory of the
jumping numbers there, and instantiate it twice:

* for the scheme sections of the projective formalization, `GradedFiltration.ofScheme` is an
  equivalence with `SGPT.LineBundle.SectionFiltration` preserving `τ_k` and `τ(𝓕)`;
* for the **analytic section ring** of a Hermitian holomorphic line bundle `L` on a complex
  manifold, `H⁰(X, L^k) = twistedSections L unit k` (all holomorphic sections of `L^{⊗k} ⊗ 𝒪_X`,
  the convention of `thm:DXmain1` and `cor:volbigL`), with the product
  `sectionMul` defined in **every** bidegree, including degree `0` (`mulZeroSection`); the tensor
  metric is multiplicative (`norm_sectionMul`) and on a connected manifold products of nonzero
  sections are nonzero (`sectionMul_ne_zero`). `AnalyticSectionFiltration L` is the book's notion
  of a filtration on `R(X, L)`.

## Main results

* `GradedFiltration.piece_ne_bot_iff`: `𝓕^μ_k ≠ 0 ↔ μ ≤ τ_k(𝓕)` (finite dimension).
* `GradedFiltration.jump_add_le`: `τ_k + τ_{k'} ≤ τ_{k+k'}` (products of nonzero elements are
  nonzero).
* `GradedFiltration.tendsto_jump_div_slope`: Fekete's lemma `τ_k/k → τ(𝓕) = sup_k τ_k/k`;
  `GradedFiltration.slope_le_bound`: `τ(𝓕) ≤ C`.
* `AnalyticSectionFiltration.tendsto_jump_div_slope_of_kahlerCurrent`: on a connected compact
  Kähler manifold, for `L` big (`c₁(L, h)` contains a Kähler current, equivalently `h⁰(L^k)` grows
  like `kⁿ`, `SGPT.IGood.KBig.sectionGrowth_iff_exists_kahlerCurrent`), `τ(𝓕)` is the limit
  `lim τ_k(𝓕)/k`, it is finite and `≤ C`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.KFilt

open Filter Set
open scoped Topology

/-! ### Filtrations of an abstract graded ring -/

section Graded

universe u

variable {S : ℕ → Type u} [∀ k, AddCommGroup (S k)] [∀ k, Module ℂ (S k)]
  (mul : ∀ k k' : ℕ, S k → S k' → S (k + k'))

/-- Source `def:testcurve:L1134`, for the graded ring `⊕_k S k` with homogeneous product `mul`:
a *filtration* is a family `(𝓕^μ)_{μ ∈ ℝ}` of graded linear subspaces `𝓕^μ = ⊕_k 𝓕^μ_k`,
`𝓕^μ_k ⊆ S k`, which is decreasing in `μ`, left-continuous (`𝓕^μ = ⋂_{μ' < μ} 𝓕^{μ'}`),
multiplicative (`𝓕^μ_k · 𝓕^{μ'}_{k'} ⊆ 𝓕^{μ+μ'}_{k+k'}`) and linearly bounded (an integer
`C > 0` with `𝓕^{Cm}_m = 0`, `𝓕^{-Cm}_m = S m` for `m > 0`). -/
structure GradedFiltration where
  /-- The graded piece `𝓕^μ_k ⊆ S k`. -/
  piece : ℝ → ∀ k : ℕ, Submodule ℂ (S k)
  antitone_piece : ∀ k : ℕ, Antitone fun μ : ℝ => piece μ k
  leftContinuous : ∀ (μ : ℝ) (k : ℕ), piece μ k = ⨅ (μ' : ℝ) (_ : μ' < μ), piece μ' k
  mul_mem : ∀ (μ μ' : ℝ) (k k' : ℕ) (s : S k) (t : S k'),
    s ∈ piece μ k → t ∈ piece μ' k' → mul k k' s t ∈ piece (μ + μ') (k + k')
  linearlyBounded : ∃ C : ℕ, 0 < C ∧ ∀ m : ℕ, 0 < m →
    piece ((C : ℝ) * m) m = ⊥ ∧ piece (-((C : ℝ) * m)) m = ⊤

namespace GradedFiltration

variable {mul} (F : GradedFiltration mul)

/-- The jumping number `τ_k(𝓕) = sup {μ ∈ ℝ : 𝓕^μ_k ≠ 0} ∈ [-∞, ∞]`. -/
def jump (k : ℕ) : EReal := ⨆ (μ : ℝ) (_ : F.piece μ k ≠ ⊥), (μ : EReal)

/-- `τ(𝓕) = sup_{k ∈ ℤ_{>0}} τ_k(𝓕)/k` (by Fekete's lemma also the limit,
`tendsto_jump_div_slope`). -/
def slope : EReal := ⨆ (k : ℕ) (_ : 0 < k), F.jump k / ((k : ℝ) : EReal)

/-- A choice of the integer `C` of the linear boundedness condition `eq:Flinearlybdd`. -/
def bound : ℕ := F.linearlyBounded.choose

theorem bound_pos : 0 < F.bound := F.linearlyBounded.choose_spec.1

theorem piece_bound_eq_bot {m : ℕ} (hm : 0 < m) : F.piece ((F.bound : ℝ) * m) m = ⊥ :=
  (F.linearlyBounded.choose_spec.2 m hm).1

theorem piece_neg_bound_eq_top {m : ℕ} (hm : 0 < m) : F.piece (-((F.bound : ℝ) * m)) m = ⊤ :=
  (F.linearlyBounded.choose_spec.2 m hm).2

theorem piece_anti {μ μ' : ℝ} (h : μ ≤ μ') (k : ℕ) : F.piece μ' k ≤ F.piece μ k :=
  F.antitone_piece k h

theorem piece_eq_bot_of_le {m : ℕ} (hm : 0 < m) {μ : ℝ} (hμ : (F.bound : ℝ) * m ≤ μ) :
    F.piece μ m = ⊥ :=
  le_bot_iff.mp ((F.piece_anti hμ m).trans (F.piece_bound_eq_bot hm).le)

theorem piece_eq_top_of_le {m : ℕ} (hm : 0 < m) {μ : ℝ} (hμ : μ ≤ -((F.bound : ℝ) * m)) :
    F.piece μ m = ⊤ :=
  top_le_iff.mp ((F.piece_neg_bound_eq_top hm).symm.le.trans (F.piece_anti hμ m))

theorem le_jump {μ : ℝ} {k : ℕ} (h : F.piece μ k ≠ ⊥) : (μ : EReal) ≤ F.jump k :=
  le_iSup₂ (f := fun (μ : ℝ) (_ : F.piece μ k ≠ ⊥) => (μ : EReal)) μ h

theorem piece_ne_bot_of_lt_jump {μ : ℝ} {k : ℕ} (h : (μ : EReal) < F.jump k) :
    F.piece μ k ≠ ⊥ := by
  obtain ⟨μ', hμ'⟩ := lt_iSup_iff.mp h
  obtain ⟨hne, hlt⟩ := lt_iSup_iff.mp hμ'
  intro hbot
  apply hne
  exact le_bot_iff.mp ((F.piece_anti (EReal.coe_lt_coe_iff.mp hlt).le k).trans hbot.le)

/-- `τ_k(𝓕) ≤ C k` in positive degree. -/
theorem jump_le_bound {k : ℕ} (hk : 0 < k) : F.jump k ≤ (((F.bound : ℝ) * k : ℝ) : EReal) := by
  refine iSup₂_le fun μ hμ => EReal.coe_le_coe_iff.mpr ?_
  by_contra h
  exact hμ (F.piece_eq_bot_of_le hk (not_le.mp h).le)

/-- `τ_k(𝓕) ≥ -C k` when `S k ≠ 0`, `k > 0`. -/
theorem neg_bound_le_jump {k : ℕ} (hk : 0 < k) [Nontrivial (S k)] :
    ((-((F.bound : ℝ) * k) : ℝ) : EReal) ≤ F.jump k := by
  apply F.le_jump
  rw [F.piece_neg_bound_eq_top hk]
  exact top_ne_bot

/-- `τ_k(𝓕) = -∞` exactly when `S k = 0` (for `k > 0`). -/
theorem jump_eq_bot_iff {k : ℕ} (hk : 0 < k) : F.jump k = ⊥ ↔ ¬ Nontrivial (S k) := by
  constructor
  · intro h hn
    have := F.neg_bound_le_jump hk
    rw [h, le_bot_iff] at this
    exact EReal.coe_ne_bot _ this
  · intro hn
    have : Subsingleton (S k) := not_nontrivial_iff_subsingleton.mp hn
    exact le_bot_iff.mp (iSup₂_le fun μ hμ => absurd (Subsingleton.elim _ _) hμ)

/-- The supremum defining `τ_k(𝓕)` is attained (left-continuity and `dim S k < ∞`). -/
theorem piece_ne_bot_of_jump_eq {k : ℕ} [FiniteDimensional ℂ (S k)] {τ : ℝ}
    (hτ : F.jump k = τ) : F.piece τ k ≠ ⊥ := by
  have hlt : ∀ μ : ℝ, μ < τ → F.piece μ k ≠ ⊥ := fun μ hμ =>
    F.piece_ne_bot_of_lt_jump (by rw [hτ]; exact EReal.coe_lt_coe_iff.mpr hμ)
  let g : ℝ → ℕ := fun μ => Module.finrank ℂ (F.piece μ k)
  have hne : (g '' Iio τ).Nonempty := ⟨g (τ - 1), τ - 1, by simp, rfl⟩
  obtain ⟨μ₀, hμ₀, hgμ₀⟩ := Nat.sInf_mem hne
  have hmin : ∀ μ : ℝ, μ < τ → g μ₀ ≤ g μ := fun μ hμ => by
    rw [hgμ₀]
    exact Nat.sInf_le ⟨μ, hμ, rfl⟩
  have hle : ∀ μ : ℝ, μ < τ → F.piece μ₀ k ≤ F.piece μ k := by
    intro μ hμ
    rcases le_total μ μ₀ with h | h
    · exact F.piece_anti h k
    · have hsub : F.piece μ k ≤ F.piece μ₀ k := F.piece_anti h k
      exact (Submodule.eq_of_le_of_finrank_le hsub (hmin μ hμ)).symm.le
  rw [F.leftContinuous τ k]
  intro hbot
  apply hlt μ₀ hμ₀
  rw [eq_bot_iff, ← hbot]
  exact le_iInf₂ fun μ hμ => hle μ hμ

/-- `𝓕^μ_k ≠ 0 ↔ μ ≤ τ_k(𝓕)`; in particular (source `ex:RWN`) `𝓕^{kτ}_k ≠ 0` whenever
`kτ ≤ τ_k(𝓕)`. -/
theorem piece_ne_bot_iff {k : ℕ} [FiniteDimensional ℂ (S k)] (μ : ℝ) :
    F.piece μ k ≠ ⊥ ↔ (μ : EReal) ≤ F.jump k := by
  refine ⟨F.le_jump, fun h => ?_⟩
  rcases h.lt_or_eq with h | h
  · exact F.piece_ne_bot_of_lt_jump h
  · exact F.piece_ne_bot_of_jump_eq h.symm

/-- Superadditivity of the jumping numbers, `τ_k(𝓕) + τ_{k'}(𝓕) ≤ τ_{k+k'}(𝓕)`, when products
of nonzero homogeneous elements are nonzero. -/
theorem jump_add_le (hmul : ∀ (k k' : ℕ) (s : S k) (t : S k'), s ≠ 0 → t ≠ 0 → mul k k' s t ≠ 0)
    (k k' : ℕ) : F.jump k + F.jump k' ≤ F.jump (k + k') := by
  apply EReal.add_le_of_forall_lt
  intro x hx y hy
  obtain ⟨μ, hμ⟩ := lt_iSup_iff.mp hx
  obtain ⟨hμne, hxμ⟩ := lt_iSup_iff.mp hμ
  obtain ⟨μ', hμ'⟩ := lt_iSup_iff.mp hy
  obtain ⟨hμ'ne, hyμ'⟩ := lt_iSup_iff.mp hμ'
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμne
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ'ne
  have hst := F.mul_mem μ μ' k k' s t hs ht
  have hne : F.piece (μ + μ') (k + k') ≠ ⊥ := fun hbot => by
    rw [hbot, Submodule.mem_bot] at hst
    exact hmul k k' s t hs0 ht0 hst
  calc x + y ≤ (μ : EReal) + (μ' : EReal) := add_le_add hxμ.le hyμ'.le
    _ = ((μ + μ' : ℝ) : EReal) := (EReal.coe_add μ μ').symm
    _ ≤ F.jump (k + k') := F.le_jump hne

/-- The remark after `def:testcurve:L1134`: `τ(𝓕) ≤ C`. -/
theorem slope_le_bound : F.slope ≤ ((F.bound : ℝ) : EReal) :=
  SGPT.LineBundle.EReal.iSup_div_le_of_le F.jump (F.bound : ℝ) fun _ hk => F.jump_le_bound hk

/-- If `S k ≠ 0` for some `k > 0`, then `τ(𝓕) > -∞`. -/
theorem slope_ne_bot {k : ℕ} (hk : 0 < k) [Nontrivial (S k)] : F.slope ≠ ⊥ :=
  SGPT.LineBundle.EReal.iSup_div_ne_bot F.jump hk
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (F.neg_bound_le_jump hk))

theorem slope_ne_top : F.slope ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) F.slope_le_bound

/-- Source `def:testcurve:L1134` (Fekete's lemma): if `S k ≠ 0` in all large degrees, then
`τ(𝓕) = lim_{k → ∞} τ_k(𝓕)/k = sup_{k > 0} τ_k(𝓕)/k`. -/
theorem tendsto_jump_div_slope
    (hmul : ∀ (k k' : ℕ) (s : S k) (t : S k'), s ≠ 0 → t ≠ 0 → mul k k' s t ≠ 0)
    (hne : ∀ᶠ k : ℕ in atTop, Nontrivial (S k)) :
    Tendsto (fun k : ℕ => F.jump k / ((k : ℝ) : EReal)) atTop (𝓝 F.slope) := by
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp hne
  refine SGPT.LineBundle.EReal.tendsto_div_iSup_of_superadditive F.jump (F.bound : ℝ) (k₁ + 1)
    (fun m k _ _ => F.jump_add_le hmul m k) (fun k hk => F.jump_le_bound hk) ?_ ?_ (by omega)
  · intro k hk hbot
    have : Nontrivial (S k) := by
      by_contra hn
      exact hbot ((F.jump_eq_bot_iff hk).mpr hn)
    have h := F.neg_bound_le_jump hk
    rwa [← neg_mul] at h
  · intro k hk hbot
    have := hk₁ k (by omega)
    exact ((F.jump_eq_bot_iff (by omega)).mp hbot) this

/-- Fekete's lemma together with the finiteness of `τ(𝓕)`: if `S k ≠ 0` in all large degrees,
`τ_k(𝓕)/k → τ(𝓕)`, `τ(𝓕) ≠ -∞` and `τ(𝓕) ≤ C`. -/
theorem tendsto_jump_div_slope_and_finite
    (hmul : ∀ (k k' : ℕ) (s : S k) (t : S k'), s ≠ 0 → t ≠ 0 → mul k k' s t ≠ 0)
    (hne : ∀ᶠ k : ℕ in atTop, Nontrivial (S k)) :
    Tendsto (fun k : ℕ => F.jump k / ((k : ℝ) : EReal)) atTop (𝓝 F.slope) ∧
      F.slope ≠ ⊥ ∧ F.slope ≤ ((F.bound : ℝ) : EReal) := by
  refine ⟨F.tendsto_jump_div_slope hmul hne, ?_, F.slope_le_bound⟩
  obtain ⟨k, hk⟩ := (hne.and (eventually_ge_atTop 1)).exists
  have := hk.1
  exact F.slope_ne_bot (k := k) (by omega)

end GradedFiltration

end Graded

/-! ### The projective instance: scheme sections -/

section Scheme

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) {L : X.Modules} (a : LineBundleAtlas L)

/-- The section product of `R(X, L)` for a line bundle on a scheme, as a family of maps. -/
abbrev schemeMul (k k' : ℕ) (s : SGPT.LineBundle.SectionSpace f L k)
    (t : SGPT.LineBundle.SectionSpace f L k') : SGPT.LineBundle.SectionSpace f L (k + k') :=
  SGPT.LineBundle.SectionSpace.mul f a k k' s t

/-- The filtrations of `def:testcurve:L1134` on the section ring of a line bundle on a complex
scheme (`SGPT.LineBundle.SectionFiltration`, used by the projective formalization) are exactly
the graded filtrations of the graded ring `⊕_k H⁰(X, L^k)` with its section product. -/
def GradedFiltration.ofScheme :
    SGPT.LineBundle.SectionFiltration f a ≃
      GradedFiltration (S := SGPT.LineBundle.SectionSpace f L)
        (schemeMul f a) where
  toFun F := ⟨F.piece, F.antitone_piece, F.leftContinuous, F.mul_mem, F.linearlyBounded⟩
  invFun F := ⟨F.piece, F.antitone_piece, F.leftContinuous, F.mul_mem, F.linearlyBounded⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {f a}

@[simp] theorem GradedFiltration.ofScheme_piece (F : SGPT.LineBundle.SectionFiltration f a) :
    (GradedFiltration.ofScheme f a F).piece = F.piece := rfl

/-- The bridge preserves the jumping numbers `τ_k(𝓕)`. -/
theorem GradedFiltration.ofScheme_jump (F : SGPT.LineBundle.SectionFiltration f a) (k : ℕ) :
    (GradedFiltration.ofScheme f a F).jump k = F.jump k := rfl

/-- The bridge preserves `τ(𝓕)`. -/
theorem GradedFiltration.ofScheme_slope (F : SGPT.LineBundle.SectionFiltration f a) :
    (GradedFiltration.ofScheme f a F).slope = F.slope := rfl

end Scheme

/-! ### The analytic section ring of a Hermitian holomorphic line bundle -/

section Analytic

open Bundle TensorProduct
open scoped Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.IGood.DXLow2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

variable {L : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- Transport of a section of `L^{⊗k} ⊗ 𝒪` along an equality of degrees `k = k'`. -/
def degreeCast {k k' : ℕ} (h : k = k') (s : twistedSections L unit k) :
    twistedSections L unit k' :=
  h ▸ s

theorem norm_degreeCast {k k' : ℕ} (h : k = k') (s : twistedSections L unit k) (x : X) :
    ‖degreeCast h s x‖ = ‖s x‖ := by
  subst h
  rfl

theorem degreeCast_eq_zero_iff {k k' : ℕ} (h : k = k') (s : twistedSections L unit k) :
    degreeCast h s = 0 ↔ s = 0 := by
  subst h
  rfl

/-- The scalar function `X → ℂ` of a degree-zero section `s ∈ H⁰(X, 𝒪 ⊗ 𝒪)` (the canonical
isometry `𝒪 ⊗ 𝒪 ≅ 𝒪`). -/
def zeroScalar (s : twistedSections L unit 0) (x : X) : ℂ :=
  zeroTwistFiberIsometry (unit (n := n) (M := X)) x (s x)

theorem norm_zeroScalar (s : twistedSections L unit 0) (x : X) : ‖zeroScalar s x‖ = ‖s x‖ :=
  (zeroTwistFiberIsometry (unit (n := n) (M := X)) x).norm_map (s x)

/-- The coordinate of a degree-zero section in the global frame is its scalar function. -/
theorem frameCoord_zeroScalar (e : AtlasFrame L) (s : twistedSections L unit 0) (x : X) :
    frameCoord (twistedPowerAtlasFrame e (unitAtlasFrame (n := n) (M := X)) 0) x (s x) =
      zeroScalar s x := by
  have h := frameCoord_zeroTwist (T := unit (n := n) (M := X))
    (unitAtlasFrame (n := n) (M := X)) (Set.mem_univ x) (s x)
  exact h.trans (frameCoord_unit x _)

/-- The product of a degree-zero section `s ∈ H⁰(X, 𝒪)` with `t ∈ H⁰(X, L^{⊗m} ⊗ 𝒪)`. -/
def mulZeroSection {m : ℕ} (s : twistedSections L unit 0) (t : twistedSections L unit m) :
    twistedSections L unit m where
  toFun x := zeroScalar s x • t x
  contMDiff_toFun := by
    intro x₀
    let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x₀, inferInstance⟩
    have he : x₀ ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x₀
    let F := twistedPowerAtlasFrame e (unitAtlasFrame (n := n) (M := X)) m
    let S := twistedPowerAtlasFrame e (unitAtlasFrame (n := n) (M := X)) 0
    let := F.property
    let := S.property
    have hF : ∀ y ∈ e.val.baseSet, y ∈ F.val.baseSet := fun y hy =>
      twistedPowerAtlasFrame_mem e unitAtlasFrame hy (Set.mem_univ y) _
    have hS : ∀ y : X, y ∈ S.val.baseSet := fun y => ⟨Set.mem_univ y, Set.mem_univ y⟩
    apply (F.val.contMDiffAt_section_iff (hF x₀ he)).mpr
    have hs := (S.val.contMDiffAt_section_iff (hS x₀)).mp (s.contMDiff x₀)
    have ht := (F.val.contMDiffAt_section_iff (hF x₀ he)).mp (t.contMDiff x₀)
    apply (hs.mul ht).congr_of_eventuallyEq
    filter_upwards [e.val.open_baseSet.mem_nhds he] with y hy
    calc (F.val ⟨y, zeroScalar s y • t y⟩).2 = frameCoord F y (zeroScalar s y • t y) :=
          (frameCoord_apply F (hF y hy) _).symm
      _ = zeroScalar s y * frameCoord F y (t y) := by rw [map_smul, smul_eq_mul]
      _ = frameCoord S y (s y) * frameCoord F y (t y) := by rw [frameCoord_zeroScalar]
      _ = (S.val ⟨y, s y⟩).2 * (F.val ⟨y, t y⟩).2 := by
          rw [frameCoord_apply S (hS y), frameCoord_apply F (hF y hy)]

theorem mulZeroSection_apply {m : ℕ} (s : twistedSections L unit 0) (t : twistedSections L unit m)
    (x : X) : mulZeroSection s t x = zeroScalar s x • t x := rfl

theorem norm_mulZeroSection {m : ℕ} (s : twistedSections L unit 0) (t : twistedSections L unit m)
    (x : X) : ‖mulZeroSection s t x‖ = ‖s x‖ * ‖t x‖ := by
  rw [mulZeroSection_apply, norm_smul, norm_zeroScalar]

/-- **The product of the analytic section ring** `R(X, L) = ⊕_k H⁰(X, L^k)`,
`H⁰(X, L^k) × H⁰(X, L^{k'}) → H⁰(X, L^{k+k'})` in every bidegree (degree zero included):
in left degree `0` it is multiplication by the holomorphic function `s`, in left degree `p + 1`
the tensor product of sections `SGPT.IGood.DXLow2.mulSection`. -/
def sectionMul : ∀ (k k' : ℕ), twistedSections L unit k → twistedSections L unit k' →
    twistedSections L unit (k + k')
  | 0, k', s, t => degreeCast (Nat.zero_add k').symm (mulZeroSection s t)
  | p + 1, k', s, t => degreeCast (by omega) (mulSection s t)

/-- **The tensor metric is multiplicative**: `|s · t|_{h^{k+k'}} = |s|_{h^k} |t|_{h^{k'}}`. -/
theorem norm_sectionMul (k k' : ℕ) (s : twistedSections L unit k) (t : twistedSections L unit k')
    (x : X) : ‖sectionMul k k' s t x‖ = ‖s x‖ * ‖t x‖ := by
  cases k with
  | zero => exact (norm_degreeCast _ _ x).trans (norm_mulZeroSection s t x)
  | succ p => exact (norm_degreeCast _ _ x).trans (norm_mulSection s t x)

/-- On a connected manifold, a section whose norm is the product of the norms of two sections
vanishes only if one of them does (identity theorem). -/
theorem eq_zero_of_norm_eq_mul [ConnectedSpace X] {k k' k'' : ℕ}
    {s : twistedSections L unit k} {t : twistedSections L unit k'}
    {u : twistedSections L unit k''} (hnorm : ∀ y, ‖u y‖ = ‖s y‖ * ‖t y‖) (hs : s ≠ 0)
    (hu : u = 0) : t = 0 := by
  by_contra ht
  have hZs := sectionZeroSet_isComplexAnalytic (twistedPower L unit k).Fiber s
  have hZt := sectionZeroSet_isComplexAnalytic (twistedPower L unit k').Fiber t
  have hit := Pending.PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ
    hZt (sectionZeroSet_ne_univ _ t ht)
  have his := Pending.PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ
    hZs (sectionZeroSet_ne_univ _ s hs)
  have hunion : sectionZeroSet (twistedPower L unit k).Fiber s ∪
      sectionZeroSet (twistedPower L unit k').Fiber t = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    have h0 : ‖s y‖ * ‖t y‖ = 0 := by rw [← hnorm y, hu]; simp
    rw [mul_eq_zero, norm_eq_zero, norm_eq_zero] at h0
    exact h0
  have hint := interior_union_isClosed_of_interior_empty hZs.isClosed hit
  rw [hunion, interior_univ, his] at hint
  obtain ⟨y, -⟩ : ∃ y, s y ≠ 0 := by
    by_contra h
    exact hs (ContMDiffSection.ext fun y => not_not.mp fun hy => h ⟨y, hy⟩)
  exact (Set.eq_empty_iff_forall_notMem.mp hint) y (Set.mem_univ y)

/-- **The analytic section ring is a domain**: on a connected manifold the product of nonzero
sections is nonzero. -/
theorem sectionMul_ne_zero [ConnectedSpace X] (k k' : ℕ) (s : twistedSections L unit k)
    (t : twistedSections L unit k') (hs : s ≠ 0) (ht : t ≠ 0) : sectionMul k k' s t ≠ 0 :=
  fun h => ht (eq_zero_of_norm_eq_mul (norm_sectionMul k k' s t) hs h)

/-- **Source `def:testcurve:L1134`, compact Kähler setting**: a filtration on the analytic
section ring `R(X, L) = ⊕_{k ≥ 0} H⁰(X, L^k)` of a Hermitian holomorphic line bundle `L`
(`H⁰(X, L^k)` = all holomorphic sections of `L^{⊗k} ⊗ 𝒪_X`, product `sectionMul`). -/
abbrev AnalyticSectionFiltration (L : HermitianHolomorphicLineBundle.{0, 0} n X) :=
  GradedFiltration (S := twistedSections L unit) (sectionMul (L := L))

namespace AnalyticSectionFiltration

variable (F : AnalyticSectionFiltration L)

/-- `𝓕^μ_k ≠ 0 ↔ μ ≤ τ_k(𝓕)` on a compact manifold. -/
theorem piece_ne_bot_iff [CompactSpace X] {k : ℕ} (μ : ℝ) :
    F.piece μ k ≠ ⊥ ↔ (μ : EReal) ≤ F.jump k := by
  have := twistedSections_finiteDimensional L unit k
  exact GradedFiltration.piece_ne_bot_iff F μ

/-- `τ_k(𝓕) + τ_{k'}(𝓕) ≤ τ_{k+k'}(𝓕)` on a connected manifold. -/
theorem jump_add_le [ConnectedSpace X] (k k' : ℕ) : F.jump k + F.jump k' ≤ F.jump (k + k') :=
  GradedFiltration.jump_add_le F sectionMul_ne_zero k k'

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- A big line bundle (`c₁(L, h)` contains a Kähler current) has nonzero sections in all large
degrees (the section growth `h⁰(X, L^k) ≥ c kⁿ`). -/
theorem eventually_nontrivial_of_kahlerCurrent (ωb : PositiveClasses.KahlerBackground n X)
    (hL : SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric L)
    (hbig : ∃ ψ : X → EReal, AnalyticGluingData.IsKahlerCurrentPotential
      (SGPT.Bergman.NativeHermitianMetric.sourceNativeFirstChernForm L hL) ψ) :
    ∀ᶠ k : ℕ in atTop, Nontrivial (twistedSections L unit k) := by
  obtain ⟨c, hc, hev⟩ := (SGPT.IGood.KBig.sectionGrowth_iff_exists_kahlerCurrent ωb hL).mpr hbig
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  have hpos : (0 : ℝ) < c * (k : ℝ) ^ n := by positivity
  have hr : 0 < Module.finrank ℂ (twistedSections L unit k) := by
    exact_mod_cast hpos.trans_le hk
  exact Module.nontrivial_of_finrank_pos hr

/-- **Source `def:testcurve:L1134`, compact Kähler setting (Fekete's lemma)**: for a big line
bundle `L` (`c₁(L, h)` contains a Kähler current; by
`SGPT.IGood.KBig.sectionGrowth_iff_exists_kahlerCurrent` equivalently `h⁰(X, L^k) ≥ c kⁿ` for
large `k`) on a connected compact Kähler manifold and a filtration `𝓕` of `R(X, L)`, the limit
`τ(𝓕) = lim_k τ_k(𝓕)/k = sup_{k > 0} τ_k(𝓕)/k` exists, `τ(𝓕) > -∞` and `τ(𝓕) ≤ C`. -/
theorem tendsto_jump_div_slope_of_kahlerCurrent (ωb : PositiveClasses.KahlerBackground n X)
    (hL : SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric L)
    (hbig : ∃ ψ : X → EReal, AnalyticGluingData.IsKahlerCurrentPotential
      (SGPT.Bergman.NativeHermitianMetric.sourceNativeFirstChernForm L hL) ψ) :
    Tendsto (fun k : ℕ => F.jump k / ((k : ℝ) : EReal)) atTop (𝓝 F.slope) ∧
      F.slope ≠ ⊥ ∧ F.slope ≤ ((F.bound : ℝ) : EReal) :=
  GradedFiltration.tendsto_jump_div_slope_and_finite F sectionMul_ne_zero
    (eventually_nontrivial_of_kahlerCurrent ωb hL hbig)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
/-- The same statement for `L` big in the sense of section growth (`h⁰(X, L^k) ≥ c kⁿ` for all
large `k`, the shape of `SGPT.LineBundle.IsBig`). -/
theorem tendsto_jump_div_slope_of_sectionGrowth {c : ℝ} (hc : 0 < c)
    (hgrowth : ∀ᶠ k : ℕ in atTop,
      c * (k : ℝ) ^ n ≤ (Module.finrank ℂ (twistedSections L unit k) : ℝ)) :
    Tendsto (fun k : ℕ => F.jump k / ((k : ℝ) : EReal)) atTop (𝓝 F.slope) ∧
      F.slope ≠ ⊥ ∧ F.slope ≤ ((F.bound : ℝ) : EReal) := by
  refine GradedFiltration.tendsto_jump_div_slope_and_finite F sectionMul_ne_zero ?_
  filter_upwards [hgrowth, eventually_gt_atTop 0] with k hk hk0
  have hpos : (0 : ℝ) < c * (k : ℝ) ^ n := by positivity
  have hr : 0 < Module.finrank ℂ (twistedSections L unit k) := by
    exact_mod_cast hpos.trans_le hk
  exact Module.nontrivial_of_finrank_pos hr

end AnalyticSectionFiltration

end Analytic

end SGPT.TestCurve.KFilt
