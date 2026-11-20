import SGPT.Okounkov.NativeFlagGermVector

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

theorem originalFlagGermLexVector_cons {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : OriginalFlagGermPoint F)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    originalFlagGermLexVector F x f hf = toLex
      (Fin.cons (originalFirstFlagGermOrderNat F (OriginalFlagGermPoint.first F x) f : ℤ)
        (ofLex (originalFlagGermLexVector F.tail (OriginalFlagGermPoint.tail F x)
          (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) f hf)
          (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) f hf)))) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem lexVector_congr {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f g : NativeHolGerm n F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (h : f = g) :
    originalFlagGermLexVector F x f hf = originalFlagGermLexVector F x g hg := by
  subst g
  rfl

private theorem lexCons_le {m : ℕ} {a b : ℤ} {v w : Lex (Fin m → ℤ)}
    (hab : a = b) (hvw : v ≤ w) :
    toLex (Fin.cons (α := fun _ : Fin (m + 1) => ℤ) a (ofLex v)) ≤
      toLex (Fin.cons (α := fun _ : Fin (m + 1) => ℤ) b (ofLex w)) := by
  rcases hvw.lt_or_eq with hlt | heq
  · apply le_of_lt
    change Pi.Lex (· < ·) (· < ·)
      (Fin.cons (α := fun _ : Fin (m + 1) => ℤ) a (ofLex v))
      (Fin.cons (α := fun _ : Fin (m + 1) => ℤ) b (ofLex w))
    exact (Fin.pi_lex_lt_cons_cons (s := (· < ·))).mpr (Or.inr ⟨hab, hlt⟩)
  · subst b
    subst w
    exact le_rfl

private theorem lexVector_le_of_head_lt {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : OriginalFlagGermPoint F)
    (f g : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) (hg : g ≠ 0)
    (h : originalFirstFlagGermOrderNat F (OriginalFlagGermPoint.first F x) f <
      originalFirstFlagGermOrderNat F (OriginalFlagGermPoint.first F x) g) :
    originalFlagGermLexVector F x f hf ≤ originalFlagGermLexVector F x g hg := by
  rw [originalFlagGermLexVector_cons, originalFlagGermLexVector_cons]
  apply le_of_lt
  change Pi.Lex (· < ·) (· < ·) _ _
  apply (Fin.pi_lex_lt_cons_cons (s := (· < ·))).mpr
  exact Or.inl (by exact_mod_cast h)

private theorem lexVector_add_eq_of_head_lt {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : OriginalFlagGermPoint F)
    (f g : NativeHolGerm (m + 1) F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (hs : f + g ≠ 0)
    (h : originalFirstFlagGermOrderNat F (OriginalFlagGermPoint.first F x) f <
      originalFirstFlagGermOrderNat F (OriginalFlagGermPoint.first F x) g) :
    originalFlagGermLexVector F x (f + g) hs = originalFlagGermLexVector F x f hf := by
  obtain ⟨_, hhead, _, htail⟩ := exists_originalFirstFlagGermResidual_add_of_lt F
    (OriginalFlagGermPoint.first F x) f g hf hg h
  rw [originalFlagGermLexVector_cons, originalFlagGermLexVector_cons]
  have ht := lexVector_congr F.tail (OriginalFlagGermPoint.tail F x) _ _
    (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) (f + g) hs)
    (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) f hf) htail
  apply congrArg toLex
  funext i
  exact Fin.cases (congrArg Int.ofNat hhead) (fun j => congrFun ht j) i

/-- All actual original first-order sum branches, followed by induction on
the SAME nonzero literal original tail residuals, produce the full
lexicographic ultrametric inequality. -/
theorem originalFlagGermLexVector_min_le_add {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (f g : NativeHolGerm n F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (hs : f + g ≠ 0) :
    min (originalFlagGermLexVector F x f hf) (originalFlagGermLexVector F x g hg) ≤
      originalFlagGermLexVector F x (f + g) hs := by
  induction n with
  | zero =>
      have h : originalFlagGermLexVector F x f hf =
          originalFlagGermLexVector F x (f + g) hs := by
        apply congrArg toLex
        funext i
        exact Fin.elim0 i
      exact (min_le_left _ _).trans h.le
  | succ m ih =>
      let y := OriginalFlagGermPoint.first F x
      rcases lt_trichotomy (originalFirstFlagGermOrderNat F y f)
          (originalFirstFlagGermOrderNat F y g) with hlt | heq | hgt
      · rw [lexVector_add_eq_of_head_lt F x f g hf hg hs hlt]
        exact min_le_left _ _
      · have hhead := originalFirstFlagGermOrderNat_le_add_of_eq F y f g hf hg hs heq
        rcases hhead.lt_or_eq with hstrict | hsame
        · exact (min_le_left _ _).trans (lexVector_le_of_head_lt F x f (f + g) hf hs hstrict)
        · have hres := originalFirstFlagGermResidual_add_of_eq F y f g hf hg hs heq hsame.symm
          have hresNe : originalFirstFlagGermResidual F y f hf +
              originalFirstFlagGermResidual F y g hg ≠ 0 := by
            rw [← hres]
            exact originalFirstFlagGermResidual_ne_zero F y (f + g) hs
          have ht := ih F.tail (OriginalFlagGermPoint.tail F x)
            (originalFirstFlagGermResidual F y f hf)
            (originalFirstFlagGermResidual F y g hg)
            (originalFirstFlagGermResidual_ne_zero F y f hf)
            (originalFirstFlagGermResidual_ne_zero F y g hg) hresNe
          have ht := ht.trans (lexVector_congr F.tail (OriginalFlagGermPoint.tail F x) _ _
            (originalFirstFlagGermResidual_ne_zero F y (f + g) hs) hresNe hres).symm.le
          rcases le_total
              (originalFlagGermLexVector F.tail (OriginalFlagGermPoint.tail F x)
                (originalFirstFlagGermResidual F y f hf)
                (originalFirstFlagGermResidual_ne_zero F y f hf))
              (originalFlagGermLexVector F.tail (OriginalFlagGermPoint.tail F x)
                (originalFirstFlagGermResidual F y g hg)
                (originalFirstFlagGermResidual_ne_zero F y g hg)) with hfg | hgf
          · rw [min_eq_left hfg] at ht
            apply (min_le_left _ _).trans
            rw [originalFlagGermLexVector_cons, originalFlagGermLexVector_cons]
            exact lexCons_le (congrArg Int.ofNat hsame) ht
          · rw [min_eq_right hgf] at ht
            apply (min_le_right _ _).trans
            rw [originalFlagGermLexVector_cons, originalFlagGermLexVector_cons]
            exact lexCons_le (congrArg Int.ofNat (heq.symm.trans hsame)) ht
      · have hswap : g + f ≠ 0 := by simpa only [add_comm] using hs
        have hvalue := lexVector_add_eq_of_head_lt F x g f hg hf hswap hgt
        have hread := lexVector_congr F x (g + f) (f + g) hswap hs (add_comm _ _)
        rw [← hread, hvalue]
        exact min_le_right _ _

end SGPT.Okounkov
