import SGPT.Convex.TimeProductPairing
import SGPT.Convex.GrowthSum

/-! Actual two-sided source bounds imply the genuine closed-strip effective
domain and finiteness of the literal product conjugate. No common endpoint
conjugate-domain witness or preexisting strip certificate is assumed. -/

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem coe_chord_le_of_le {a b : ℝ} {v : EReal}
    (ha : (a : EReal) ≤ v) (hb : (b : EReal) ≤ v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (((1 - t) * a + t * b : ℝ) : EReal) ≤ v := by
  cases v using EReal.rec with
  | bot => exact False.elim ((EReal.bot_lt_coe a).not_ge ha)
  | top => exact le_top
  | coe r =>
    rw [EReal.coe_le_coe_iff] at ha hb ⊢
    calc
      (1 - t) * a + t * b ≤ (1 - t) * r + t * r := by
        exact add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left hb ht.1)
      _ = r := by ring

/-- The original source lower bound yields the genuine finite primal chord
bound, including the two boundary slices and every infinite dual value. -/
theorem timeConjugate_le_chord
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f₀ f₁ : E → ℝ) (Ψ : F × ℝ → EReal)
    (hlower : ∀ (m : F) (s : ℝ), max (conjugate B (fun x => (f₀ x : EReal)) m)
      (conjugate B (fun x => (f₁ x : EReal)) m + (s : EReal)) ≤ Ψ (m, s))
    (x : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    conjugate (timeProductPairing B).flip Ψ (x, t) ≤
      (((1 - t) * f₀ x + t * f₁ x : ℝ) : EReal) := by
  apply (conjugate_le_coe_iff (timeProductPairing B).flip Ψ (x, t) _).mpr
  rintro ⟨m, s⟩
  have hc₀ : ((B x m - f₀ x : ℝ) : EReal) ≤
      conjugate B (fun z => (f₀ z : EReal)) m := by
    simpa only [conjugate, ← EReal.coe_sub] using
      (le_iSup (fun z => (B z m : EReal) - (f₀ z : EReal)) x)
  have hc₁ : ((B x m - f₁ x : ℝ) : EReal) ≤
      conjugate B (fun z => (f₁ z : EReal)) m := by
    simpa only [conjugate, ← EReal.coe_sub] using
      (le_iSup (fun z => (B z m : EReal) - (f₁ z : EReal)) x)
  have h₀ : ((B x m - f₀ x : ℝ) : EReal) ≤ Ψ (m, s) :=
    hc₀.trans ((le_max_left _ _).trans (hlower m s))
  have h₁ : ((B x m - f₁ x + s : ℝ) : EReal) ≤ Ψ (m, s) := by
    rw [EReal.coe_add]
    exact (add_le_add hc₁ le_rfl).trans ((le_max_right _ _).trans (hlower m s))
  have hh := coe_chord_le_of_le h₀ h₁ ht
  change ((B x m + t * s - ((1 - t) * f₀ x + t * f₁ x) : ℝ) : EReal) ≤ Ψ (m, s)
  have heq : B x m + t * s - ((1 - t) * f₀ x + t * f₁ x) =
      (1 - t) * (B x m - f₀ x) + t * (B x m - f₁ x + s) := by ring
  rw [heq]
  exact hh

/-- Restriction to the actual zero time-dual slice gives the spatial conjugate
as a genuine lower bound, with no finite-domain assumption on the input point. -/
theorem spatialConjugate_le_timeConjugate
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (Ψ : F × ℝ → EReal) (G : F → EReal)
    (hupper : ∀ m s, Ψ (m, s) ≤ G m + ((max s 0 : ℝ) : EReal))
    (x : E) (t : ℝ) :
    conjugate B.flip G x ≤ conjugate (timeProductPairing B).flip Ψ (x, t) := by
  apply iSup_le
  intro m
  have hu : Ψ (m, 0) ≤ G m := by simpa using hupper m 0
  have hh := EReal.sub_le_sub (le_refl (B x m : EReal)) hu
  exact hh.trans (by
    simpa only [conjugate, LinearMap.flip_apply, timeProductPairing_apply, mul_zero, add_zero] using
      (le_iSup (fun y : F × ℝ => ((timeProductPairing B).flip y (x, t) : EReal) - Ψ y) (m, 0)))

/-- The actual source upper bound forces +∞ at every point off the closed
strip, by one true finite point of G and unbounded real time-dual slopes. -/
theorem timeConjugate_eq_top_of_not_mem_Icc
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (Ψ : F × ℝ → EReal) (G : F → EReal)
    (hG : IsProper G)
    (hupper : ∀ m s, Ψ (m, s) ≤ G m + ((max s 0 : ℝ) : EReal))
    (x : E) {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    conjugate (timeProductPairing B).flip Ψ (x, t) = ⊤ := by
  obtain ⟨m, hm⟩ := hG.2.1
  have hgm : G m = ((G m).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hm) (hG.2.2 m)).symm
  let c := B x m - (G m).toReal
  have hcost (s : ℝ) : ((c + t * s - max s 0 : ℝ) : EReal) ≤
      conjugate (timeProductPairing B).flip Ψ (x, t) := by
    have hu := hupper m s
    rw [hgm, ← EReal.coe_add] at hu
    have hh := EReal.sub_le_sub (le_refl ((B x m + t * s : ℝ) : EReal)) hu
    have hc : B x m + t * s - ((G m).toReal + max s 0) = c + t * s - max s 0 := by
      dsimp [c]
      ring
    rw [← EReal.coe_sub, hc] at hh
    exact hh.trans (by
      simpa only [conjugate, LinearMap.flip_apply, timeProductPairing_apply] using
        (le_iSup (fun y : F × ℝ => ((timeProductPairing B).flip y (x, t) : EReal) - Ψ y) (m, s)))
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro R
  let A : ℝ := |R - c| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : R < c + A := by dsimp [A]; linarith [le_abs_self (R - c)]
  have htime : t < 0 ∨ 1 < t := by
    by_cases h : t < 0
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge (fun ht1 => ht ⟨le_of_not_gt h, ht1⟩))
  rcases htime with hneg | hpos
  · let s : ℝ := A / t
    have hs : s < 0 := div_neg_of_pos_of_neg hA hneg
    have hprod : t * s = A := by dsimp [s]; exact mul_div_cancel₀ _ hneg.ne
    have hh := hcost s
    rw [max_eq_right hs.le, hprod, sub_zero] at hh
    exact (EReal.coe_lt_coe_iff.mpr hR).trans_le hh
  · let s : ℝ := A / (t - 1)
    have hs : 0 < s := div_pos hA (by linarith)
    have hprod : (t - 1) * s = A := by
      dsimp [s]
      exact mul_div_cancel₀ _ (by linarith)
    have heq : c + t * s - max s 0 = c + A := by
      rw [max_eq_left hs.le]
      nlinarith [hprod]
    rw [← heq] at hR
    exact (EReal.coe_lt_coe_iff.mpr hR).trans_le (hcost s)

/-- Literal source dual bounds, not an incoming primal presentation, produce
the exact closed-strip effective domain of the actual conjugate. -/
theorem effectiveDomain_timeConjugate_eq_closedStrip
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (f₀ f₁ : E → ℝ) (Ψ : F × ℝ → EReal) (G : F → EReal)
    (hG : IsProper G)
    (hlower : ∀ (m : F) (s : ℝ), max (conjugate B (fun x => (f₀ x : EReal)) m)
      (conjugate B (fun x => (f₁ x : EReal)) m + (s : EReal)) ≤ Ψ (m, s))
    (hupper : ∀ m s, Ψ (m, s) ≤ G m + ((max s 0 : ℝ) : EReal)) :
    effectiveDomain (conjugate (timeProductPairing B).flip Ψ) =
      univ ×ˢ Icc (0 : ℝ) 1 := by
  ext p
  by_cases hp : p.2 ∈ Icc (0 : ℝ) 1
  · exact iff_of_true
      ((timeConjugate_le_chord B f₀ f₁ Ψ hlower p.1 hp).trans_lt (EReal.coe_lt_top _))
      ⟨mem_univ _, hp⟩
  · change conjugate (timeProductPairing B).flip Ψ p < ⊤ ↔ _
    change conjugate (timeProductPairing B).flip Ψ (p.1, p.2) < ⊤ ↔ _
    rw [timeConjugate_eq_top_of_not_mem_Icc B Ψ G hG hupper p.1 hp]
    simp only [lt_self_iff_false, false_iff]
    exact fun h => hp h.2

end SGPT.Convex
