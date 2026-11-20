import SGPT.Okounkov.NativeFlagGermLexSum

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

theorem originalFlagGermLexVector_one {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) : originalFlagGermLexVector F x 1 one_ne_zero = 0 := by
  change (fun i => (originalFlagGermVector F x 1 one_ne_zero i : ℤ)) = 0
  rw [originalFlagGermVector_one]
  rfl

theorem originalFlagGermLexVector_mul {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f g : NativeHolGerm n F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    originalFlagGermLexVector F x (f * g) (mul_ne_zero hf hg) =
      originalFlagGermLexVector F x f hf + originalFlagGermLexVector F x g hg := by
  change (fun i => (originalFlagGermVector F x (f * g) (mul_ne_zero hf hg) i : ℤ)) =
    (fun i => (originalFlagGermVector F x f hf i : ℤ)) +
      (fun i => (originalFlagGermVector F x g hg i : ℤ))
  rw [originalFlagGermVector_mul]
  ext i
  exact Nat.cast_add _ _

private def germValue {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f : NativeHolGerm n F.carrier x.1) :
    WithTop (Lex (Fin n → ℤ)) := by
  classical
  exact if hf : f = 0 then ⊤ else
    (originalFlagGermLexVector F x f hf : WithTop (Lex (Fin n → ℤ)))

private theorem germValue_of_ne_zero {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0) :
    germValue F x f = (originalFlagGermLexVector F x f hf : WithTop (Lex (Fin n → ℤ))) := by
  simp only [germValue, dif_neg hf]

private theorem germValue_zero {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) : germValue F x 0 = ⊤ := by
  simp [germValue]

/-- The genuine full original local lexicographic AddValuation. Every
nonzero value is manufactured by successive division and literal ORIGINAL
tail restriction, with the SAME fixed original equation at every level. -/
def originalFlagGermValuation {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) :
    AddValuation (NativeHolGerm n F.carrier x.1) (WithTop (Lex (Fin n → ℤ))) :=
  AddValuation.of (germValue F x) (germValue_zero F x)
    (by rw [germValue_of_ne_zero F x 1 one_ne_zero, originalFlagGermLexVector_one]; rfl)
    (by
      intro f g
      by_cases hs : f + g = 0
      · rw [hs, germValue_zero]
        exact le_top
      by_cases hf : f = 0
      · subst f
        simp only [zero_add, germValue_zero, min_top_left, le_refl]
      by_cases hg : g = 0
      · subst g
        simp only [add_zero, germValue_zero, min_top_right, le_refl]
      rw [germValue_of_ne_zero F x f hf, germValue_of_ne_zero F x g hg,
        germValue_of_ne_zero F x (f + g) hs]
      exact_mod_cast originalFlagGermLexVector_min_le_add F x f g hf hg hs)
    (by
      intro f g
      by_cases hf : f = 0
      · subst f
        simp only [zero_mul, germValue_zero, top_add]
      by_cases hg : g = 0
      · subst g
        simp only [mul_zero, germValue_zero, add_top]
      rw [germValue_of_ne_zero F x f hf, germValue_of_ne_zero F x g hg,
        germValue_of_ne_zero F x (f * g) (mul_ne_zero hf hg), originalFlagGermLexVector_mul]
      rfl)

theorem originalFlagGermValuation_apply_of_ne_zero {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (f : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0) :
    originalFlagGermValuation F x f =
      (originalFlagGermLexVector F x f hf : WithTop (Lex (Fin n → ℤ))) :=
  germValue_of_ne_zero F x f hf

theorem originalFlagGermValuation_eq_top_iff {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (f : NativeHolGerm n F.carrier x.1) : originalFlagGermValuation F x f = ⊤ ↔ f = 0 := by
  by_cases hf : f = 0
  · subst f
    exact ⟨fun _ => rfl, fun _ => (originalFlagGermValuation F x).map_zero⟩
  · rw [originalFlagGermValuation_apply_of_ne_zero F x f hf]
    simp only [WithTop.coe_ne_top, hf]

end SGPT.Okounkov
