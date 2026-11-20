import SGPT.Okounkov.FlagValuationEndpointCenter

/-!
# Positive native flag prefixes and the actual analytic flag ideals

The local-ring criterion uses the original recursive division and literal
restriction to the original tail. No flag-member/valuation-centre equality
is assumed. Algebraic generic-point identification is a separate next step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- Vanishing on a nested original carrier is unchanged by literal subtype
restriction; the ambient neighborhood is produced from the subtype one. -/
theorem eventually_vanish_subtype_iff {M : Type*} [TopologicalSpace M]
    {N C : Set M} (hCN : C ⊆ N) (x : N) (f : M → ℂ) :
    (∀ᶠ y in 𝓝 x, y.1 ∈ C → f y.1 = 0) ↔
      ∀ᶠ y in 𝓝 x.1, y ∈ C → f y = 0 := by
  constructor
  · intro h
    obtain ⟨V, hV, hsub⟩ := (mem_nhds_subtype N x _).mp h
    filter_upwards [hV] with y hy
    intro hyC
    exact hsub (show (⟨y, hCN hyC⟩ : N) ∈ Subtype.val ⁻¹' V from hy) hyC
  · intro h
    filter_upwards [continuous_subtype_val.continuousAt.eventually h] with y hy
    exact hy

/-- The actual restriction kernel is the actual first analytic flag ideal,
on every original holomorphic representative. -/
theorem originalFirstFlagRestriction_mk_eq_zero_iff {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : F.carrier → ℂ) (hf : HolomorphicAt (m + 1) f x.1) :
    originalFirstFlagGermRestriction F x (NativeHolGerm.mk f hf) = 0 ↔
      (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).mem x.1 f := by
  have hres : originalFirstFlagGermRestriction F x (NativeHolGerm.mk f hf) = 0 ↔
      (fun y : F.tail.carrier => f y.1) =ᶠ[𝓝 x] 0 := by
    rw [Subtype.ext_iff]
    change ((fun y : F.tail.carrier => f y.1) : Germ (𝓝 x) ℂ) =
      ((0 : F.tail.carrier → ℂ) : Germ (𝓝 x) ℂ) ↔ _
    exact Germ.coe_eq
  rw [hres]
  constructor
  · intro h
    refine ⟨hf, ?_⟩
    apply (eventually_vanish_subtype_iff (Subset.rfl) x f).mp
    exact h.mono fun y hy _ => hy
  · intro h
    filter_upwards [continuous_subtype_val.continuousAt.eventually h.2] with y hy
    exact hy y.property

private theorem mk_eq_zero_of_vanishing_univ {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) {x : F.carrier} (f : F.carrier → ℂ)
    (hf : HolomorphicAt n f x) (hv : (vanishingIdeal (n := n) (univ : Set F.carrier)).mem x f) :
    NativeHolGerm.mk f hf = 0 := by
  change NativeHolGerm.mk f hf = NativeHolGerm.mk 0 (holomorphicAt_const 0)
  apply NativeHolGerm.mk_eq_mk_iff.mpr
  exact hv.2.mono fun y hy => hy (mem_univ y)

private theorem nativeFlagVector_congr {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (a b : NativeHolGerm n F.carrier x.1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a = b) :
    originalFlagGermVector F x a ha = originalFlagGermVector F x b hb := by
  subst b
  rfl

/-- On nonzero native germs, a positive coordinate among the actual first
`k` entries is exactly vanishing on the literal original `k`th member. -/
theorem originalFlagGermVector_prefix_pos_iff :
    ∀ {n : ℕ} (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
      (k : ℕ) (hk : k ≤ n) (f : F.carrier → ℂ) (hf : HolomorphicAt n f x.1)
      (hne : NativeHolGerm.mk f hf ≠ 0),
      (∃ i : Fin k, 0 < originalFlagGermVector F x (NativeHolGerm.mk f hf) hne
          (Fin.castLE hk i)) ↔
        (vanishingIdeal (n := n) (F.flag ⟨k, Nat.lt_succ_of_le hk⟩)).mem x.1 f := by
  intro n
  induction n with
  | zero =>
    intro F x k hk f hf hne
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    constructor
    · rintro ⟨i, _⟩; exact Fin.elim0 i
    · intro hv
      apply False.elim
      apply hne
      apply mk_eq_zero_of_vanishing_univ F f hf
      simpa only [show (⟨0, Nat.lt_succ_of_le hk⟩ : Fin 1) = 0 from rfl, F.smooth.1] using hv
  | succ m ih =>
    intro F x k hk f hf hne
    cases k with
    | zero =>
      constructor
      · rintro ⟨i, _⟩; exact Fin.elim0 i
      · intro hv
        apply False.elim
        apply hne
        apply mk_eq_zero_of_vanishing_univ F f hf
        simpa only [show (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (m + 2)) = 0 from rfl,
          F.smooth.1] using hv
    | succ k =>
      let y := OriginalFlagGermPoint.first F x
      let z := OriginalFlagGermPoint.tail F x
      let g := NativeHolGerm.mk f hf
      let R := originalFirstFlagGermResidual F y g hne
      have hR : R ≠ 0 := originalFirstFlagGermResidual_ne_zero F y g hne
      have hk' : k ≤ m := Nat.le_of_succ_le_succ hk
      by_cases hhead : originalFirstFlagGermOrderNat F y g = 0
      · have hq : originalFirstFlagGermQuotient F y g hne = g := by
          have hfac := (originalFirstFlagGermQuotient_spec F y g hne).1
          simpa only [hhead, pow_zero, one_mul] using hfac.symm
        have hres : R = originalFirstFlagGermRestriction F y g := by
          change originalFirstFlagGermRestriction F y (originalFirstFlagGermQuotient F y g hne) = _
          rw [hq]
        obtain ⟨r, hr, hrr⟩ := NativeHolGerm.exists_eq_mk R
        have hfr : (fun q : F.tail.carrier => f q.1) =ᶠ[𝓝 y] r := by
          apply Germ.coe_eq.mp
          exact congrArg Subtype.val (hres.symm.trans hrr)
        have hind := ih F.tail z k hk' r hr (by rw [← hrr]; exact hR)
        have htailCarrier : F.tail.flag ⟨k, Nat.lt_succ_of_le hk'⟩ =
            Subtype.val ⁻¹' F.flag ⟨k + 1, Nat.lt_succ_of_le hk⟩ := rfl
        have hCN : F.flag ⟨k + 1, Nat.lt_succ_of_le hk⟩ ⊆
            F.flag (1 : Fin (m + 2)) := F.smooth.2.1 (by change 1 ≤ k + 1; omega)
        have hvan : (vanishingIdeal (n := m) (F.tail.flag ⟨k, Nat.lt_succ_of_le hk'⟩)).mem z.1 r ↔
            (vanishingIdeal (n := m + 1) (F.flag ⟨k + 1, Nat.lt_succ_of_le hk⟩)).mem x.1 f := by
          constructor
          · intro hv
            refine ⟨hf, (eventually_vanish_subtype_iff hCN y f).mp ?_⟩
            filter_upwards [hv.2, hfr] with q hq heq
            intro hqF
            exact heq.trans (hq (by change q ∈ F.tail.flag _; rw [htailCarrier]; exact hqF))
          · intro hv
            refine ⟨hr, ?_⟩
            have hh := (eventually_vanish_subtype_iff hCN y f).mpr hv.2
            filter_upwards [hh, hfr] with q hq heq
            intro hqF
            exact heq.symm.trans (hq (by change q ∈ Subtype.val ⁻¹' _; rw [← htailCarrier]; exact hqF))
        have hvec : (∃ i : Fin (k + 1), 0 < originalFlagGermVector F x g hne (Fin.castLE hk i)) ↔
            ∃ i : Fin k, 0 < originalFlagGermVector F.tail z R hR (Fin.castLE hk' i) := by
          constructor
          · rintro ⟨i, hi⟩
            cases i using Fin.cases with
            | zero =>
              change 0 < originalFirstFlagGermOrderNat F y g at hi
              omega
            | succ i => exact ⟨i, hi⟩
          · rintro ⟨i, hi⟩
            exact ⟨i.succ, hi⟩
        rw [nativeFlagVector_congr F.tail z R (NativeHolGerm.mk r hr) hR
          (by rw [← hrr]; exact hR) hrr] at hvec
        exact hvec.trans (hind.trans hvan)
      · have hres0 : originalFirstFlagGermRestriction F y g = 0 := by
          by_contra hnot
          have horder := (originalFirstFlagGermOrder_eq_zero_iff F y g).mpr hnot
          rw [originalFirstFlagGermOrderNat_spec F y g hne] at horder
          exact hhead (ENat.natCast_inj.mp horder)
        have hvfirst := (originalFirstFlagRestriction_mk_eq_zero_iff F y f hf).mp hres0
        have hv : (vanishingIdeal (n := m + 1) (F.flag ⟨k + 1, Nat.lt_succ_of_le hk⟩)).mem x.1 f :=
          ⟨hf, hvfirst.2.mono fun q hq hqF =>
            hq (F.smooth.2.1 (by change 1 ≤ k + 1; omega) hqF)⟩
        have hp : ∃ i : Fin (k + 1), 0 < originalFlagGermVector F x g hne (Fin.castLE hk i) :=
          ⟨0, Nat.pos_of_ne_zero hhead⟩
        exact ⟨fun _ => hv, fun _ => hp⟩

private theorem natLex_nonneg {k : ℕ} (a : Fin k → ℕ) :
    (0 : Lex (Fin k → ℤ)) ≤ toLex (fun i => (a i : ℤ)) := by
  by_contra h
  have hlt := lt_of_not_ge h
  change toLex (fun i => (a i : ℤ)) < toLex (0 : Fin k → ℤ) at hlt
  obtain ⟨i, _, hi⟩ := ValCurr.toLex_lt_toLex_iff.mp hlt
  exact not_lt_of_ge (Nat.cast_nonneg (a i)) hi

private theorem natLex_pos_iff {k : ℕ} (a : Fin k → ℕ) :
    (0 : Lex (Fin k → ℤ)) < toLex (fun i => (a i : ℤ)) ↔ ∃ i, 0 < a i := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := ValCurr.toLex_lt_toLex_iff.mp h
    exact ⟨i, by exact_mod_cast hi⟩
  · rintro ⟨i, hi⟩
    apply lt_of_le_of_ne (natLex_nonneg a)
    intro hzero
    have hz : (0 : ℤ) = (a i : ℤ) := congrArg (fun z : Lex (Fin k → ℤ) => ofLex z i) hzero
    exact (Nat.ne_of_gt hi) (by exact_mod_cast hz.symm)

/-- The positive ideal of every ACTUAL prefix coarsening is precisely the
actual analytic flag-member ideal on original holomorphic representatives,
including the zero germ and the zero-length prefix. -/
theorem originalFlagPrefixValuation_pos_iff_vanishingIdeal {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (k : ℕ) (hk : k ≤ n) (f : F.carrier → ℂ) (hf : HolomorphicAt n f x.1) :
    0 < ValCurr.prefixValuation hk (originalFlagGermValuation F x) (NativeHolGerm.mk f hf) ↔
      (vanishingIdeal (n := n) (F.flag ⟨k, Nat.lt_succ_of_le hk⟩)).mem x.1 f := by
  by_cases hne : NativeHolGerm.mk f hf = 0
  · have heq : f =ᶠ[𝓝 x.1] (0 : F.carrier → ℂ) :=
      (NativeHolGerm.mk_eq_mk_iff (hg := holomorphicAt_const 0)).mp hne
    constructor
    · intro _
      exact ⟨hf, heq.mono fun q hq _ => hq⟩
    · intro _
      rw [hne, (ValCurr.prefixValuation hk (originalFlagGermValuation F x)).map_zero]
      exact WithTop.coe_lt_top 0
  · have hv := originalFlagGermValuation_apply_of_ne_zero F x (NativeHolGerm.mk f hf) hne
    change 0 < ValCurr.prefixWithTopHom hk
      (originalFlagGermValuation F x (NativeHolGerm.mk f hf)) ↔ _
    rw [hv]
    let v : Lex (Fin k → ℤ) := toLex (fun i : Fin k =>
      (originalFlagGermVector F x (NativeHolGerm.mk f hf) hne (Fin.castLE hk i) : ℤ))
    change ((0 : Lex (Fin k → ℤ)) : WithTop (Lex (Fin k → ℤ))) <
      (v : WithTop (Lex (Fin k → ℤ))) ↔ _
    rw [WithTop.coe_lt_coe]
    exact (natLex_pos_iff _).trans (originalFlagGermVector_prefix_pos_iff F x k hk f hf hne)

end SGPT.Okounkov
