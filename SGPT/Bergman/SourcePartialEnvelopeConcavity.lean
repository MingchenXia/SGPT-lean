import SGPT.Bergman.SourcePartialEnvelopes
import SGPT.Envelopes.SourceOrdinaryEnvelopeAlgebra
import SGPT.Foundations.Analysis.Pending.ActualIEnvelopePositiveScaling
import SGPT.Foundations.Analysis.Pending.ActualMultiplierOrderAddition
import SGPT.Envelopes.SourceGlobalPRelativeEnvelope
import SGPT.PSH.SourceIEnvelopeMonotonicity
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds
import SGPT.PSH.SourceThetaPSHCompactness

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.PartialEnvelopeConcavity

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.PSH.ConnectedThetaPSHCompactness
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Classical

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Actual local PSH nondegeneracy prevents every nonempty original open set
from being pluripolar. This also retains dimension zero. -/
theorem nonPluripolar_open (A : VariableComplexAtlas X) {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) : A.NonPluripolar U := by
  obtain ⟨x, hx⟩ := hne
  intro hbad
  obtain ⟨V, hV, hxV, w, hw, hpole⟩ := hbad x
  obtain ⟨y, hy, hfin⟩ := hw.locallyNondegenerate hV x hxV U hU hx
  exact hfin (hpole y ⟨hy.2, hy.1⟩)

/-- A genuine original theta-PSH input internally manufactures an actual
non-pluripolar finite lower-level set; no lower-set certificate is supplied. -/
theorem exists_nonPluripolar_lower_level [Nonempty X]
    {A : VariableComplexAtlas X} {θ : AtlasClosedRealOneOneForm A} {v : X → EReal}
    (hv : A.IsThetaPSH θ v) :
    ∃ m : ℕ, A.NonPluripolar {x | ((-(m : ℝ) : ℝ) : EReal) ≤ v x} := by
  have hwhole : A.NonPluripolar univ := nonPluripolar_open A isOpen_univ univ_nonempty
  by_contra hbad
  have hlevel (m : ℕ) :
      A.LocallyPluripolar {x | ((-(m : ℝ) : ℝ) : EReal) ≤ v x} := by
    by_contra hm
    exact hbad ⟨m, hm⟩
  let S : ℕ → Set X := fun j =>
    if j = 0 then {x | v x = ⊥} else {x | ((-((j - 1 : ℕ) : ℝ) : ℝ) : EReal) ≤ v x}
  have hS (j : ℕ) : A.LocallyPluripolar (S j) := by
    by_cases hj : j = 0
    · simpa only [S, if_pos hj] using source_poles_locallyPluripolar hv
    · simpa only [S, if_neg hj] using hlevel (j - 1)
  apply hwhole
  apply (VariableComplexAtlas.LocallyPluripolar.iUnion hS).mono
  intro x _hx
  by_cases hx : v x = ⊥
  · exact mem_iUnion.mpr ⟨0, by simpa only [S, if_pos rfl, mem_ofPred_eq] using hx⟩
  · obtain ⟨r, _hr, hrv⟩ := EReal.lt_iff_exists_real_btwn.mp (bot_lt_iff_ne_bot.mpr hx)
    obtain ⟨m, hm⟩ := exists_nat_gt (-r)
    have hmv : ((-(m : ℝ) : ℝ) : EReal) ≤ v x :=
      (EReal.coe_lt_coe_iff.mpr (by linarith : -(m : ℝ) < r)).le.trans hrv.le
    exact mem_iUnion.mpr ⟨m + 1, by
      simpa only [S, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
        Nat.add_sub_cancel, mem_ofPred_eq] using hmv⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- A single non-top value of the actual upper regularization produces one
finite global bound for the ENTIRE genuine input family. No desired bound,
output PSH predicate, non-pluripolar set or geometric certificate is an input. -/
theorem exists_uniform_bound_of_uscSup_ne_top {I : Type*}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : I → M → EReal}
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH θ (v i))
    {x₀ : M} (hx₀ : uscSup v x₀ ≠ ⊤) :
    ∃ C : ℝ, ∀ i x, v i x ≤ (C : EReal) := by
  obtain ⟨B, hB, _hBt⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr hx₀)
  let V : Set M := {x | uscSup v x < (B : EReal)}
  have hV : IsOpen V := (upperSemicontinuous_uscRegularization _).isOpen_preimage (B : EReal)
  have hVnp : (ofFixedModel n M).NonPluripolar V :=
    nonPluripolar_open (ofFixedModel n M) hV ⟨x₀, hB⟩
  obtain ⟨C, hC⟩ := source_nonpluripolar_uniform_sup (ofFixedModel n M) x₀ θ V hVnp B
  refine ⟨C, fun i x => ?_⟩
  have hsup := hC ⟨v i, hv i⟩ (fun y hy => ?_)
  · obtain ⟨c, hc, _⟩ := native_exists_real_sup
      ((isThetaPSH_iff_nativeThetaPotential θ (v i)).mp (hv i))
    rw [hc, EReal.toReal_coe] at hsup
    exact (le_iSup (v i) x).trans (hc.trans_le (EReal.coe_le_coe_iff.mpr hsup))
  · exact ((le_iSup (fun j => v j y) i).trans
      (le_uscRegularization (fun z => ⨆ j, v j z) y)).trans hy.le

/-- Genuine original nonempty theta-PSH families have an ACTUAL top-or-PSH
dichotomy, with both the input and output finite bounds produced internally. -/
theorem uscSup_top_or_genuine {I : Type*} [Nonempty I]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : I → M → EReal}
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH θ (v i)) :
    (uscSup v = fun _ => ⊤) ∨
      ∃ C : ℝ, (∀ i x, v i x ≤ (C : EReal)) ∧
        (uscSup v ≤ fun _ => (C : EReal)) ∧
        (ofFixedModel n M).IsThetaPSH θ (uscSup v) := by
  by_cases htop : ∀ x, uscSup v x = ⊤
  · exact Or.inl (funext htop)
  · push Not at htop
    obtain ⟨x, hx⟩ := htop
    obtain ⟨C, hC⟩ := exists_uniform_bound_of_uscSup_ne_top hv hx
    refine Or.inr ⟨C, hC, ?_, ?_⟩
    · exact uscRegularization_le upperSemicontinuous_const (fun y => iSup_le fun i => hC i y)
    · exact isThetaPSH_uscSup_of_majorant hv upperSemicontinuous_const
        (fun _ => EReal.coe_ne_top C) hC

/-- Entire actual-family trichotomy, including genuinely empty indices and
the literal bottom upper regularization, without an output-status premise. -/
theorem uscSup_bottom_top_or_genuine {I : Type*}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : I → M → EReal}
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH θ (v i)) :
    (uscSup v = fun _ => ⊥) ∨ (uscSup v = fun _ => ⊤) ∨
      ∃ C : ℝ, (∀ i x, v i x ≤ (C : EReal)) ∧
        (uscSup v ≤ fun _ => (C : EReal)) ∧
        (ofFixedModel n M).IsThetaPSH θ (uscSup v) := by
  by_cases hi : Nonempty I
  · let := hi
    exact Or.inr (uscSup_top_or_genuine hv)
  · let : IsEmpty I := ⟨fun i => hi ⟨i⟩⟩
    left
    simp only [uscSup, iSup_of_empty, uscRegularization_const]

end SGPT.Bergman.PartialEnvelopeConcavity

namespace SGPT.Bergman.PartialEnvelopeConcavityConsumer

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.PSH.ConnectedThetaPSHCompactness
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeConcavity
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open scoped Topology Classical

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem theta_convexComb
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (ofFixedModel n M).IsThetaPSH θ (convexComb t u v) :=
  (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (isThetaPshPotential_convexComb ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) ht0 ht1)

private theorem ereal_convex_self {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a : EReal) :
    (t : EReal) * a + ((1 - t : ℝ) : EReal) * a = a := by
  induction a with
  | bot => simp only [EReal.coe_mul_bot_of_pos ht0,
      EReal.coe_mul_bot_of_pos (sub_pos.mpr ht1), EReal.bot_add]
  | top => simp only [EReal.coe_mul_top_of_pos ht0,
      EReal.coe_mul_top_of_pos (sub_pos.mpr ht1), EReal.top_add_top]
  | coe a =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

private theorem ereal_left_bound {t C L : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {a b : EReal} (hat : a ≠ ⊤) (hbt : b ≠ ⊤) (hL : (L : EReal) ≤ b)
    (h : (t : EReal) * a + ((1 - t : ℝ) : EReal) * b ≤ (C : EReal)) :
    a ≤ (((C - (1 - t) * L) / t : ℝ) : EReal) := by
  by_cases hab : a = ⊥
  · rw [hab]
    exact bot_le
  have hbb : b ≠ ⊥ := ne_of_gt ((bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot L)).trans_le hL)
  have ha := EReal.coe_toReal hat hab
  have hb := EReal.coe_toReal hbt hbb
  rw [← ha, ← hb, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h
  rw [← hb, EReal.coe_le_coe_iff] at hL
  rw [← ha]
  apply EReal.coe_le_coe_iff.mpr
  apply (le_div_iff₀ ht0).mpr
  have hm := mul_le_mul_of_nonneg_left hL (sub_pos.mpr ht1).le
  linarith

private theorem raw_convex_sup_le {I J : Type*} {a : I → EReal} {b : J → EReal}
    {t C D : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ha : ∀ i, a i ≤ (C : EReal)) (hb : ∀ j, b j ≤ (D : EReal))
    {H : EReal} (hp : ∀ i j, (t : EReal) * a i + ((1 - t : ℝ) : EReal) * b j ≤ H) :
    (t : EReal) * (⨆ i, a i) + ((1 - t : ℝ) : EReal) * (⨆ j, b j) ≤ H := by
  let e := sourcePositiveERealOrderIso t ht0
  let g := sourcePositiveERealOrderIso (1 - t) (sub_pos.mpr ht1)
  by_cases hgb : ((1 - t : ℝ) : EReal) * (⨆ j, b j) = ⊥
  · rw [hgb, EReal.add_bot]
    exact bot_le
  have hgt : ((1 - t : ℝ) : EReal) * (⨆ j, b j) ≠ ⊤ := by
    apply ne_of_lt
    calc
      ((1 - t : ℝ) : EReal) * (⨆ j, b j) ≤ ((1 - t : ℝ) : EReal) * (D : EReal) :=
        mul_le_mul_of_nonneg_left (iSup_le hb) (EReal.coe_nonneg.mpr (sub_pos.mpr ht1).le)
      _ = (((1 - t) * D : ℝ) : EReal) := (EReal.coe_mul _ _).symm
      _ < ⊤ := lt_top_iff_ne_top.mpr (EReal.coe_ne_top _)
  have hg := EReal.coe_toReal hgt hgb
  change e (⨆ i, a i) + ((1 - t : ℝ) : EReal) * (⨆ j, b j) ≤ H
  rw [_root_.map_iSup, ← hg, ← iSup_add_coe]
  apply iSup_le
  intro i
  change (t : EReal) * a i +
    ((((1 - t : ℝ) : EReal) * (⨆ j, b j)).toReal : EReal) ≤ H
  rw [hg]
  by_cases hai : a i = ⊥
  · rw [hai, EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]
    exact bot_le
  have hat : a i ≠ ⊤ := ne_of_lt ((ha i).trans_lt (lt_top_iff_ne_top.mpr (EReal.coe_ne_top C)))
  have har := EReal.coe_toReal hat hai
  have hscale : (t : EReal) * a i = ((t * (a i).toReal : ℝ) : EReal) := by
    rw [← har, ← EReal.coe_mul, EReal.toReal_coe]
  rw [hscale, add_comm]
  change g (⨆ j, b j) + ((t * (a i).toReal : ℝ) : EReal) ≤ H
  rw [_root_.map_iSup, ← iSup_add_coe]
  apply iSup_le
  intro j
  change ((1 - t : ℝ) : EReal) * b j + ((t * (a i).toReal : ℝ) : EReal) ≤ H
  rw [add_comm, ← hscale]
  exact hp i j

variable [CompactSpace M] [ConnectedSpace M]

private theorem uniform_bound_left_of_pair_bound {I J : Type*} [Nonempty J]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : I → M → EReal} {v : J → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH θ (u i))
    (hv : ∀ j, (ofFixedModel n M).IsThetaPSH θ (v j))
    {t C : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hp : ∀ i j x, convexComb t (u i) (v j) x ≤ (C : EReal)) :
    ∃ A : ℝ, ∀ i x, u i x ≤ (A : EReal) := by
  let j₀ : J := Classical.arbitrary J
  obtain ⟨m, hm⟩ := exists_nonPluripolar_lower_level (hv j₀)
  let L : Set M := {x | ((-(m : ℝ) : ℝ) : EReal) ≤ v j₀ x}
  let D : ℝ := (C - (1 - t) * (-(m : ℝ))) / t
  obtain ⟨A, hA⟩ := source_nonpluripolar_uniform_sup (ofFixedModel n M)
    (Classical.arbitrary M) θ L hm D
  refine ⟨A, fun i x => ?_⟩
  have hsup := hA ⟨u i, hu i⟩ (fun y hy =>
    ereal_left_bound ht0 ht1 ((hu i).1 y) ((hv j₀).1 y) hy (hp i j₀ y))
  obtain ⟨c, hc, _⟩ := native_exists_real_sup
    ((isThetaPSH_iff_nativeThetaPotential θ (u i)).mp (hu i))
  rw [hc, EReal.toReal_coe] at hsup
  exact (le_iSup (u i) x).trans (hc.trans_le (EReal.coe_le_coe_iff.mpr hsup))

/-- A genuine two-family original convex USC-sup inequality, with every
empty/bottom/top case and every required output status manufactured inside. -/
theorem convexComb_uscSup_le_pair_uscSup {I J : Type*}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : I → M → EReal} {v : J → M → EReal}
    (hu : ∀ i, (ofFixedModel n M).IsThetaPSH θ (u i))
    (hv : ∀ j, (ofFixedModel n M).IsThetaPSH θ (v j))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (uscSup u) (uscSup v) ≤
      uscSup (fun p : I × J => convexComb t (u p.1) (v p.2)) := by
  by_cases hi : Nonempty I
  · let := hi
    by_cases hj : Nonempty J
    · let := hj
      let w : I × J → M → EReal := fun p => convexComb t (u p.1) (v p.2)
      have hw (p : I × J) : (ofFixedModel n M).IsThetaPSH θ (w p) :=
        theta_convexComb (hu p.1) (hv p.2) ht0 ht1
      change convexComb t (uscSup u) (uscSup v) ≤ uscSup w
      rcases uscSup_top_or_genuine hw with htop | ⟨C, hC, _hHbound, hH⟩
      · rw [htop]
        exact fun _ => le_top
      obtain ⟨A, hA⟩ := uniform_bound_left_of_pair_bound hu hv ht0 ht1
        (fun i j x => hC (i, j) x)
      have hswap (j : J) (i : I) (x : M) :
          convexComb (1 - t) (v j) (u i) x ≤ (C : EReal) := by
        simp only [convexComb, show (1 : ℝ) - (1 - t) = t by ring]
        rw [add_comm]
        exact hC (i, j) x
      obtain ⟨B, hB⟩ := uniform_bound_left_of_pair_bound hv hu (sub_pos.mpr ht1)
        (by linarith : 1 - t < 1) hswap
      have hU : (ofFixedModel n M).IsThetaPSH θ (uscSup u) :=
        isThetaPSH_uscSup_of_majorant hu upperSemicontinuous_const
          (fun _ => EReal.coe_ne_top A) hA
      have hV : (ofFixedModel n M).IsThetaPSH θ (uscSup v) :=
        isThetaPSH_uscSup_of_majorant hv upperSemicontinuous_const
          (fun _ => EReal.coe_ne_top B) hB
      have hUeq : SourceQuasiEverywhere (n := n) (fun x => uscSup u x = ⨆ i, u i x) := by
        apply (source_theta_sup_exceptional hu hA).mono
        intro x hx
        change (⨆ i, u i x) < uscSup u x
        change ¬uscSup u x = ⨆ i, u i x at hx
        apply lt_of_not_ge
        intro hback
        exact hx (le_antisymm hback (le_uscRegularization (fun y => ⨆ i, u i y) x))
      have hVeq : SourceQuasiEverywhere (n := n) (fun x => uscSup v x = ⨆ j, v j x) := by
        apply (source_theta_sup_exceptional hv hB).mono
        intro x hx
        change (⨆ j, v j x) < uscSup v x
        change ¬uscSup v x = ⨆ j, v j x at hx
        apply lt_of_not_ge
        intro hback
        exact hx (le_antisymm hback (le_uscRegularization (fun y => ⨆ j, v j y) x))
      have hq : SourceQuasiEverywhere (n := n)
          (fun x => convexComb t (uscSup u) (uscSup v) x ≤ uscSup w x) := by
        apply (sourceQuasiEverywhere_iff_native _).mpr
        apply (quasiEverywhere_and ((sourceQuasiEverywhere_iff_native _).mp hUeq)
          ((sourceQuasiEverywhere_iff_native _).mp hVeq)).mono
        intro x hx
        simp only [convexComb, hx.1, hx.2]
        apply raw_convex_sup_le ht0 ht1 (fun i => hA i x) (fun j => hB j x)
        intro i j
        exact (le_iSup (fun p : I × J => w p x) (i, j)).trans
          (le_uscRegularization (fun y => ⨆ p : I × J, w p y) x)
      exact (sourceQuasiEverywhere_le_iff (theta_convexComb hU hV ht0 ht1) hH).mp hq
    · let : IsEmpty J := ⟨fun j => hj ⟨j⟩⟩
      have he : uscSup v = fun _ => ⊥ := by simp only [uscSup, iSup_of_empty, uscRegularization_const]
      intro x
      simp only [convexComb, he, EReal.coe_mul_bot_of_pos (sub_pos.mpr ht1), EReal.add_bot]
      exact bot_le
  · let : IsEmpty I := ⟨fun i => hi ⟨i⟩⟩
    have he : uscSup u = fun _ => ⊥ := by simp only [uscSup, iSup_of_empty, uscRegularization_const]
    intro x
    simp only [convexComb, he, EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]
    exact bot_le

omit [CompactSpace M] [ConnectedSpace M] in
private theorem partialObstacle_convexComb {K : Set M} {f : K → EReal} {u v : M → EReal}
    (hu : partialObstacle (n := n) K f u) (hv : partialObstacle (n := n) K f v)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    partialObstacle (n := n) K f (convexComb t u v) := by
  apply (sourceQuasiEverywhere_iff_native _).mpr
  apply (quasiEverywhere_and ((sourceQuasiEverywhere_iff_native _).mp hu)
    ((sourceQuasiEverywhere_iff_native _).mp hv)).mono
  intro x hx hxK
  exact (add_le_add
    (mul_le_mul_of_nonneg_left (hx.1 hxK) (EReal.coe_nonneg.mpr ht0.le))
    (mul_le_mul_of_nonneg_left (hx.2 hxK) (EReal.coe_nonneg.mpr (sub_pos.mpr ht1).le))).trans_eq
      (ereal_convex_self ht0 ht1 (f ⟨x, hxK⟩))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] in
private theorem singularityLE_convexComb {u v φ ψ : M → EReal}
    (hu : SGPT.PSH.SingularityLE u φ) (hv : SGPT.PSH.SingularityLE v ψ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    SGPT.PSH.SingularityLE (convexComb t u v) (convexComb t φ ψ) := by
  obtain ⟨C, hC⟩ := (singularityLE_iff_exists_real u φ).mp hu
  obtain ⟨D, hD⟩ := (singularityLE_iff_exists_real v ψ).mp hv
  apply (singularityLE_iff_exists_real _ _).mpr
  refine ⟨t * C + (1 - t) * D, fun x => ?_⟩
  exact (convexComb_mono ht0.le ht1.le hC hD x).trans_eq
    (congrFun (POrderAffineRooftop.convexComb_add_const ht0 ht1 φ ψ C D) x)

omit [CompactSpace M] [ConnectedSpace M] in
private theorem sourceIOrder_convexComb
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v φ ψ : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    (huφ : sourceIOrder (ofFixedModel n M) u φ) (hvψ : sourceIOrder (ofFixedModel n M) v ψ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    sourceIOrder (ofFixedModel n M) (convexComb t u v) (convexComb t φ ψ) := by
  have hun := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hvn := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  have hφn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  have hψn := (isThetaPSH_iff_nativeThetaPotential θ ψ).mp hψ
  have hIu := (sourceIOrder_iff_native ⟨θ, hu⟩ ⟨θ, hφ⟩).mp huφ
  have hIv := (sourceIOrder_iff_native ⟨θ, hv⟩ ⟨θ, hψ⟩).mp hvψ
  apply (sourceIOrder_iff_native ⟨θ, theta_convexComb hu hv ht0 ht1⟩
    ⟨θ, theta_convexComb hφ hψ ht0 ht1⟩).mpr
  exact ActualMultiplierOrderAddition.iOrderOnManifold_add
    (RestrictedApproximantComparison.isThetaPshPotential_smul hun ht0)
    (RestrictedApproximantComparison.isThetaPshPotential_smul hvn (sub_pos.mpr ht1))
    (RestrictedApproximantComparison.isThetaPshPotential_smul hφn ht0)
    (RestrictedApproximantComparison.isThetaPshPotential_smul hψn (sub_pos.mpr ht1))
    (ActualIEnvelopePositiveScaling.iOrderOnManifold_smul hIu ht0)
    (ActualIEnvelopePositiveScaling.iOrderOnManifold_smul hIv (sub_pos.mpr ht1))

/-- BOTH full original prop:partial_env clause5 inequalities for the original
arbitrary subtype obstacle. No output regularity/boundedness or nonempty
competitor certificate is supplied; all empty and top branches are genuine. -/
theorem partialEnvelopes_convexComb
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ ψ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    (K : Set M) (f : K → EReal) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (partialEnvelope θ φ K f) (partialEnvelope θ ψ K f) ≤
        partialEnvelope θ (convexComb t φ ψ) K f ∧
      convexComb t (partialIEnvelope θ φ K f) (partialIEnvelope θ ψ K f) ≤
        partialIEnvelope θ (convexComb t φ ψ) K f := by
  constructor
  · have h := convexComb_uscSup_le_pair_uscSup
      (fun u : partialCompetitors θ φ K f => u.property.1)
      (fun v : partialCompetitors θ ψ K f => v.property.1) ht0 ht1
    apply h.trans
    apply uscRegularization_le (upperSemicontinuous_partialEnvelope θ (convexComb t φ ψ) K f)
    intro x
    apply iSup_le
    intro p
    exact le_partialEnvelope (theta_convexComb p.1.property.1 p.2.property.1 ht0 ht1)
      (partialObstacle_convexComb p.1.property.2.1 p.2.property.2.1 ht0 ht1)
      (singularityLE_convexComb p.1.property.2.2 p.2.property.2.2 ht0 ht1) x
  · have h := convexComb_uscSup_le_pair_uscSup
      (fun u : partialICompetitors θ φ K f => u.property.1)
      (fun v : partialICompetitors θ ψ K f => v.property.1) ht0 ht1
    apply h.trans
    apply uscRegularization_le (upperSemicontinuous_partialIEnvelope θ (convexComb t φ ψ) K f)
    intro x
    apply iSup_le
    intro p
    exact le_partialIEnvelope (theta_convexComb p.1.property.1 p.2.property.1 ht0 ht1)
      (partialObstacle_convexComb p.1.property.2.1 p.2.property.2.1 ht0 ht1)
      (sourceIOrder_convexComb p.1.property.1 p.2.property.1 hφ hψ
        p.1.property.2.2 p.2.property.2.2 ht0 ht1) x

end SGPT.Bergman.PartialEnvelopeConcavityConsumer
