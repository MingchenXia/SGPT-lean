import SGPT.Unibranch.FNABridge

/-!
# The Fornæss--Narasimhan theorem on complex spaces

Source `thm:FN` (`appendix_unibranch.tex`): for a function `φ : X → [-∞, ∞)` on a complex space
`X`, not identically `-∞` on any irreducible component of `X`, the following are equivalent:

1. `φ` is plurisubharmonic (`def:unibranch:L105`);
2. `φ` is upper semicontinuous and, for every morphism `f : Δ → X` from the open unit disc with
   `f^*φ ≢ -∞`, the pull-back `f^*φ` is subharmonic.

The book cites [FN80]. (1) ⇒ (2) is `IsPSH.fornaessNarasimhan_forward`. For (2) ⇒ (1) we follow
[FN80, Thm. 5.3.1]: "the theorem is local, so we may suppose that `X` is a closed complex
subvariety of `Δⁿ`". At a point `x` of `X` take a local embedding `e` of a neighbourhood of `x`
into an open `Ω ⊆ ℂ^N` and a polydisc `Δ ⊆ Ω` centred at the image `a` of `x`;
`C ∩ Δ` (`C` the carrier of `e`) is a closed analytic subset of `Δ` and `φ` read on it is in
`WP(C ∩ Δ)` (`isWeaklyPSHOn_carrierFunction`). The local [FN80] theorem `LocalFNExtension`
 gives an ambient function `ψ` near `a` satisfying the disc criterion with `ψ = φ` on
`C`; `isLocallyAmbientPSHAt_of_extension` turns it into condition 2 of `def:unibranch:L105`, and
condition 1 is the hypothesis of `thm:FN`.

Main results (all with the local theorem `LocalFNExtension` as hypothesis `hFN`):

* `isLocallyAmbientPSHAt_of_disc`: [FN80] `WP(X) ⊆ P(X)` on complex spaces: an upper
  semicontinuous `φ < +∞` whose disc pull-backs are subharmonic whenever `≢ -∞` satisfies
  condition 2 of `def:unibranch:L105` at every point (no condition on components needed).
* `isPSH_of_disc`: `thm:FN`, (2) ⇒ (1).
* `fornaessNarasimhan`: `thm:FN`, (1) ⇔ (2), on every complex space.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace CategoryTheory
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNA

open SourceReducedComplexSpace

variable {X : SourceReducedComplexSpace}

/-- A small polydisc centred at `a` lies in the ball `B(a, ρ)`. -/
theorem polydisc_subset_ball {n : ℕ} (a : ComplexModel n) {ρ : ℝ} (hρ : 0 < ρ) :
    polydisc a (fun _ => ρ / (n + 1)) ⊆ ball a ρ := by
  intro z hz
  have hs : ∀ i, ‖(z - a) i‖ ^ 2 ≤ (ρ / (n + 1)) ^ 2 := fun i => by
    have h := hz i
    rw [PiLp.sub_apply]
    exact pow_le_pow_left₀ (norm_nonneg _) h.le 2
  have hsum : ∑ i, ‖(z - a) i‖ ^ 2 ≤ n * (ρ / (n + 1)) ^ 2 := by
    calc ∑ i, ‖(z - a) i‖ ^ 2 ≤ ∑ _i : Fin n, (ρ / (n + 1)) ^ 2 :=
          Finset.sum_le_sum fun i _ => hs i
      _ = n * (ρ / (n + 1)) ^ 2 := by simp
  have hn : (n : ℝ) * (ρ / (n + 1)) ^ 2 < ρ ^ 2 := by
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    rw [div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)]
    have hρ2 : 0 < ρ ^ 2 := by positivity
    have hnn : (n : ℝ) < (n + 1) ^ 2 := by nlinarith
    nlinarith
  rw [mem_ball, dist_eq_norm, EuclideanSpace.norm_eq, Real.sqrt_lt' hρ]
  exact lt_of_le_of_lt hsum hn

/-- Local equations restrict to an open subset. -/
theorem hasLocalEquationsOn_inter {n : ℕ} {Y Ω Δ : Set (ComplexModel n)}
    (hY : FNR.HasLocalEquationsOn Y Ω) (hΔ : IsOpen Δ) (hΔΩ : Δ ⊆ Ω) :
    FNR.HasLocalEquationsOn (Y ∩ Δ) Δ := by
  intro x hx
  obtain ⟨W, hW, hxW, N, g, hg, hY'⟩ := hY x (hΔΩ hx)
  refine ⟨W ∩ Δ, hW.inter hΔ, ⟨hxW, hx⟩, N, g, fun i => (hg i).mono inter_subset_left, ?_⟩
  intro y hy
  rw [← hY' y hy.1]
  exact ⟨fun h => h.1, fun h => ⟨h, hy.2⟩⟩

/-- **[FN80] Theorem 5.3.1 on complex spaces: `WP(X) ⊆ P(X)`.** Given the local [FN80]
theorem, an upper semicontinuous `φ : X → [-∞, ∞)` whose pull-back by every holomorphic disc
`f : Δ → X` with `f^*φ ≢ -∞` is subharmonic satisfies condition 2 of `def:unibranch:L105` at
every point: near every point it is the restriction of a plurisubharmonic function on a domain,
for a closed immersion of a neighbourhood. -/
theorem isLocallyAmbientPSHAt_of_disc (hFN : LocalFNExtension) {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤) (husc : UpperSemicontinuous φ)
    (hdisc : ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
      SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1))
    (x : X.obj.left) : X.IsLocallyAmbientPSHAt φ x := by
  set e := LocalEmbedding.ofPoint X x
  obtain ⟨c, hc⟩ := LocalEmbedding.mem_range_ofPoint X x
  rw [← hc]
  have hWP := isWeaklyPSHOn_carrierFunction e hne_top husc hdisc
  obtain ⟨ρ, hρ, hballρ⟩ := Metric.isOpen_iff.mp e.ambient.isOpen c.val.val c.val.property
  set a : ComplexModel e.dim := c.val.val
  set r : Fin e.dim → ℝ := fun _ => ρ / (e.dim + 1)
  have hr : ∀ i, 0 < r i := fun _ => by positivity
  have hΔΩ : polydisc a r ⊆ (e.ambient : Set (ComplexModel e.dim)) :=
    (polydisc_subset_ball a hρ).trans hballρ
  have haΔ : a ∈ polydisc a r := fun i => by simpa using hr i
  obtain ⟨W, hW, haW, ψ, hψ, hψφ⟩ := hFN e.dim (carrierSet e ∩ polydisc a r) a r
    (carrierFunction e φ) hr inter_subset_right
    (hasLocalEquationsOn_inter (hasLocalEquationsOn_carrierSet e) (isOpen_polydisc a r) hΔΩ)
    ⟨val_mem_carrierSet e c, haΔ⟩ (hWP.mono inter_subset_left)
  refine isLocallyAmbientPSHAt_of_extension e c (hW.inter (isOpen_polydisc a r)) ⟨haW, haΔ⟩
    (hψ.mono inter_subset_left) ?_
  intro z hz
  rw [hψφ z.val.val ⟨⟨val_mem_carrierSet e z, hz.2⟩, hz.1⟩, carrierFunction_apply]

/-- **Source `thm:FN`, (2) ⇒ (1), on every complex space** (given the local [FN80] theorem).
An upper semicontinuous `φ : X → [-∞, ∞)`, not identically `-∞` on any irreducible component of
`X`, whose pull-back `f^*φ` by every morphism `f : Δ → X` with `f^*φ ≢ -∞` is subharmonic, is
plurisubharmonic. -/
theorem isPSH_of_disc (hFN : LocalFNExtension) {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤)
    (hcomp : ∀ Z : Set X.obj.left, X.IsIrreducibleComponent Z → ∃ z ∈ Z, φ z ≠ ⊥)
    (husc : UpperSemicontinuous φ)
    (hdisc : ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
      SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) :
    X.IsPSH φ :=
  ⟨hcomp, isLocallyAmbientPSHAt_of_disc hFN hne_top husc hdisc⟩

/-- **Source `thm:FN` (Fornæss--Narasimhan), on every complex space** (given the local [FN80]
theorem `LocalFNExtension`). Let `φ : X → [-∞, ∞)` be not identically `-∞` on any irreducible
component of `X`. Then `φ` is plurisubharmonic if and only if `φ` is upper semicontinuous and,
for every morphism `f : Δ → X` from the open unit disc with `f^*φ ≢ -∞`, the pull-back `f^*φ` is
subharmonic. -/
theorem fornaessNarasimhan (hFN : LocalFNExtension) {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤)
    (hcomp : ∀ Z : Set X.obj.left, X.IsIrreducibleComponent Z → ∃ z ∈ Z, φ z ≠ ⊥) :
    X.IsPSH φ ↔
      (UpperSemicontinuous φ ∧
        ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
          SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) :=
  ⟨fun h => h.fornaessNarasimhan_forward,
    fun h => isPSH_of_disc hFN hne_top hcomp h.1 h.2⟩

end SGPT.Unibranch.FNA
