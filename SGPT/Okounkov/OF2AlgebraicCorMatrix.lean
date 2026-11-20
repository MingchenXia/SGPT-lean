import SGPT.Okounkov.OF2ModificationFlagValuation
import SGPT.Okounkov.NativeFlagGermCartier
import SGPT.Okounkov.FlagCorrectionMatrix
import SGPT.Okounkov.FlagCorrectionRow
import SGPT.Okounkov.EffectiveDivisorPotentialCompatibility
import SGPT.Okounkov.ValCurrCorrectionUnitriangular
import SGPT.Foundations.Analysis.Pending.GermIdealPullbackCalculus
import SGPT.Foundations.Analysis.Pending.RelativePrincipalizationSpan
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition

/-!
# The algebraic form of `prop:cormatrix`

Source: chapter *The theory of Okounkov bodies*, `def:lifting` and `prop:cormatrix`, used in
`rmk:valcurr` ("passing to a common resolution and applying `prop:cormatrix`, `prop:cormult`").

Let `π : W → F` be a lifting of a smooth flag `F•` to a smooth flag `W•` (`IsFlagLifting`), with
correction matrix `cor(F•, π)` (`flagLiftingCorrectionMatrix`). For holomorphic germs this file
proves the germ-level form of `prop:cormatrix`:

`ν_{W•}(π^* h) = ν_{F•}(h) · cor(F•, π)`  (`originalFlagGermLexVector_comap_eq`).

The proof is the induction of the book: write `h = t^a q` with `t` the local equation of `F₁` and
`q|_{F₁} ≠ 0`; then `π^* t = t' e` with `t'` the local equation of `W₁` and
`ν_{W•}(π^* t) = (1, row)` (the correction row is the flag vector of the residual divisor
`(π^*F₁ - W₁)|_{W₁}`: Cartier uniqueness), and
`ν_{W•}(π^* q) = (0, ν_{W_{≥1}}((π|_{W₁})^* (q|_{F₁})))`
(restriction commutes with pull-back), to which induction applies.

Consequently, for valuations of `ℂ(X)` induced by flags on modifications of an integral smooth
projective complex scheme `X` (`OF2.modificationFlagValuation`): if `π : X' → X(ℂ)` is a
modification, `F•` a flag on `X'`, and `p : X'' → X'` lifts `F•` to `W•`, then
`ν_{W•} ∘ (π p)^* = (ν_{F•} ∘ π^*) · cor(F•, p)` (`modificationFlagValuation_lifting`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF2

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff Matrix

universe u

/-! ### Germ-level preliminaries -/

section GermLemmas

variable {n : ℕ}

theorem originalFlagGermVector_congr (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    {f g : NativeHolGerm n F.carrier x.1} (hf : f ≠ 0) (hg : g ≠ 0) (h : f = g) :
    originalFlagGermVector F x f hf = originalFlagGermVector F x g hg := by
  subst h
  rfl

theorem nativeHolGerm_comap_mk_eq {k : ℕ} {M N : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [TopologicalSpace N] [ChartedSpace (ComplexModel k) N]
    [IsComplexManifold n M] [IsComplexManifold k N]
    (b : N → M) (hb : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ b) (y : N)
    (f : M → ℂ) (hf : HolomorphicAt n f (b y)) (hfb : HolomorphicAt k (f ∘ b) y) :
    NativeHolGerm.comap b hb y (NativeHolGerm.mk f hf) = NativeHolGerm.mk (f ∘ b) hfb :=
  Subtype.ext (NativeHolGerm.comap_mk b hb y f hf)

end GermLemmas

/-! ### The first step: the pull-back of the local equation of `F₁` -/

section FirstStep

variable {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}

/-- The total transform of the reduced divisor `F₁` is generated at the flag point of `W` by the
pull-back of the local equation of `F₁`. -/
theorem totalTransform_mem_iff_span (hπ : IsFlagLifting F W π)
    (D : EffectiveDivisor (m + 1) F.carrier)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))))
    (x : OriginalFlagGermPoint W) (hy : π x.1 ∈ F.flag (Fin.last (m + 1))) (f : W.carrier → ℂ) :
    (GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1.1
        hπ.interior_exceptional_eq_empty D).ideal.mem x.1 f ↔
      ∃ hf : HolomorphicAt (m + 1) f x.1, NativeHolGerm.mk f hf ∈ Ideal.span
        {NativeHolGerm.comap π hπ.1.1 x.1 (originalFirstFlagGermParameter F
          (OriginalFlagGermPoint.first F ⟨π x.1, hy⟩))} := by
  set y : OriginalFlagGermPoint F := ⟨π x.1, hy⟩ with hydef
  set t := originalFirstFlagGermParameter F (OriginalFlagGermPoint.first F y) with htdef
  obtain ⟨T, hT, htT⟩ := NativeHolGerm.exists_eq_mk t
  have hTπ : HolomorphicAt (m + 1) (T ∘ π) x.1 :=
    HolomorphicAt.comp_contMDiff (f := π) (y := x.1) hT
      (Eventually.of_forall fun z => hπ.1.1.contMDiffAt)
  have hcomapt : NativeHolGerm.comap π hπ.1.1 x.1 t = NativeHolGerm.mk (T ∘ π) hTπ := by
    rw [htT]
    exact nativeHolGerm_comap_mk_eq π hπ.1.1 x.1 T hT hTπ
  have hker := (originalFirstFlagGermParameter_spec F (OriginalFlagGermPoint.first F y)).2.2
  -- generator property of the vanishing ideal of `F₁` at `π x`
  have hvan : ∀ a : F.carrier → ℂ,
      (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).mem (π x.1) a →
        IsInSpanAt (n := m + 1) (· = T) (π x.1) a := by
    intro a ha
    have hahol : HolomorphicAt (m + 1) a (π x.1) := ha.1
    have hmem : NativeHolGerm.mk a hahol ∈
        RingHom.ker (originalFirstFlagGermRestriction F (OriginalFlagGermPoint.first F y)) := by
      rw [RingHom.mem_ker]
      exact (originalFirstFlagGermRestriction_mk_eq_zero_iff F _ a hahol).mpr ha
    rw [hker, ← htdef, htT] at hmem
    exact (NativeHolGerm.mem_span_singleton_mk_iff a T hahol hT).mp hmem
  have hTvan : (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).mem (π x.1) T := by
    have hmem : t ∈
        RingHom.ker (originalFirstFlagGermRestriction F (OriginalFlagGermPoint.first F y)) := by
      rw [hker]
      exact Ideal.subset_span (mem_singleton _)
    rw [htT, RingHom.mem_ker] at hmem
    exact (originalFirstFlagGermRestriction_mk_eq_zero_iff F _ T hT).mp hmem
  rw [hcomapt]
  change (GermIdeal.pullback (m := m + 1) π D.ideal).mem x.1 f ↔ _
  rw [hDI]
  change IsInSpanAt (n := m + 1) (fun s => ∃ a, (vanishingIdeal (n := m + 1)
    (F.flag (1 : Fin (m + 2)))).mem (π x.1) a ∧ s = a ∘ π) x.1 f ↔ _
  constructor
  · intro hspan
    refine ⟨hspan.1, (NativeHolGerm.mem_span_singleton_mk_iff f (T ∘ π) hspan.1 hTπ).mpr ?_⟩
    refine RelativePrincipalizationSpan.IsInSpanAt.trans ?_ hspan
    rintro s ⟨a, ha, rfl⟩
    refine IsInSpanAt.mono ?_ (GermIdealPullbackCalculus.isInSpanAt_comp hπ.1.1 (hvan a ha))
    rintro _ ⟨b, rfl, rfl⟩
    rfl
  · rintro ⟨hf, hmem⟩
    have hspan := (NativeHolGerm.mem_span_singleton_mk_iff f (T ∘ π) hf hTπ).mp hmem
    refine IsInSpanAt.mono ?_ hspan
    rintro _ rfl
    exact ⟨T, hTvan, rfl⟩

/-- **The flag vector of the pulled-back equation of `F₁`** is `(1, row)`, `row` the correction row
of the lifting. -/
theorem originalFlagGermVector_comap_parameter (hπ : IsFlagLifting F W π)
    (x : OriginalFlagGermPoint W) (hy : π x.1 ∈ F.flag (Fin.last (m + 1)))
    (hne : NativeHolGerm.comap π hπ.1.1 x.1 (originalFirstFlagGermParameter F
      (OriginalFlagGermPoint.first F ⟨π x.1, hy⟩)) ≠ 0) :
    (fun i => (originalFlagGermVector W x _ hne i : ℤ)) =
      Fin.cons 1 (flagLiftingCorrectionRow hπ) := by
  obtain ⟨D, hDI, Dtail, hstep, ν, hν, hrow⟩ := flagLiftingCorrectionRow_spec hπ
  have hcons : OriginalCartierFlagValuation (m + 1) W
      (GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1.1
        hπ.interior_exceptional_eq_empty D) (Fin.cons 1 ν) := by
    refine ⟨Dtail, ?_, ?_⟩
    · exact hstep
    · simpa only [Fin.cons_succ] using hν
  have hnative := originalCartierFlagValuation_of_native_generator (m + 1) W x
    (GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1.1
      hπ.interior_exceptional_eq_empty D) _ hne
    (fun f => totalTransform_mem_iff_span hπ D hDI x hy f)
  have heq := originalCartierFlagValuation_unique W _ hnative hcons
  rw [heq, hrow]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

end FirstStep

/-! ### Restriction commutes with pull-back -/

theorem restriction_comap_eq {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) (x : W.tail.carrier)
    (g : NativeHolGerm (m + 1) F.carrier (π x.1)) :
    originalFirstFlagGermRestriction W x (NativeHolGerm.comap π hπ.1.1 x.1 g) =
      NativeHolGerm.comap hπ.tailMap hπ.tailMap_isFlagLifting.1.1 x
        (originalFirstFlagGermRestriction F (hπ.tailMap x) g) := by
  obtain ⟨G, hG, rfl⟩ := NativeHolGerm.exists_eq_mk g
  apply Subtype.ext
  rfl

/-- One step of the correction on a vector `(a, V)`: `(a, a • row + g(V))`. -/
theorem integerCorrectionStep_cons {m : ℕ} (c : Fin m → ℤ)
    (g : Lex (Fin m → ℤ) ≃+o Lex (Fin m → ℤ)) (a : ℤ) (V : Fin m → ℤ) :
    ofLex (integerCorrectionStep c g (toLex (Fin.cons a V : Fin (m + 1) → ℤ))) =
      Fin.cons a (a • c + ofLex (g (toLex V))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · show integerCorrectionStepEquiv c g (toLex (Fin.cons a V : Fin (m + 1) → ℤ)) 0 = _
    rw [integerCorrectionStepEquiv_apply_zero]
    rfl
  · show integerCorrectionStepEquiv c g (toLex (Fin.cons a V : Fin (m + 1) → ℤ)) j.succ = _
    rw [integerCorrectionStepEquiv_apply_succ]
    have hV : (fun k : Fin m => (toLex (Fin.cons a V : Fin (m + 1) → ℤ)) k.succ) = V := by
      funext k
      rfl
    have h0 : (toLex (Fin.cons a V : Fin (m + 1) → ℤ)) 0 = a := rfl
    rw [hV, h0]
    simp only [Fin.cons_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-! ### The germ-level `prop:cormatrix` -/

/-- **Germ-level `prop:cormatrix`.** For a lifting `π` of `F•` to `W•` and a nonzero holomorphic
germ `h` at the flag point of `F`, `ν_{W•}(π^* h) = cor(F•, π)(ν_{F•}(h))`. -/
theorem originalFlagGermVector_comap_eq :
    ∀ (n : ℕ) (F W : OriginalFlagGeometry.{u} n) (π : W.carrier → F.carrier)
      (hπ : IsFlagLifting F W π) (x : OriginalFlagGermPoint W)
      (hy : π x.1 ∈ F.flag (Fin.last n)) (h : NativeHolGerm n F.carrier (π x.1)) (hh : h ≠ 0)
      (hh' : NativeHolGerm.comap π hπ.1.1 x.1 h ≠ 0),
      (fun i => (originalFlagGermVector W x _ hh' i : ℤ)) =
        ofLex (flagLiftingCorrection n F W π hπ
          (toLex fun i => (originalFlagGermVector F ⟨π x.1, hy⟩ h hh i : ℤ))) := by
  intro n
  induction n with
  | zero =>
    intro F W π hπ x hy h hh hh'
    funext i
    exact Fin.elim0 i
  | succ m ih =>
    intro F W π hπ x hy h hh hh'
    set y : OriginalFlagGermPoint F := ⟨π x.1, hy⟩ with hydef
    set y1 := OriginalFlagGermPoint.first F y with hy1def
    set t := originalFirstFlagGermParameter F y1 with htdef
    set a := originalFirstFlagGermOrderNat F y1 h with hadef
    set q := originalFirstFlagGermQuotient F y1 h hh with hqdef
    have hfac : h = t ^ a * q := (originalFirstFlagGermQuotient_spec F y1 h hh).1
    have hqres : originalFirstFlagGermRestriction F y1 q ≠ 0 :=
      (originalFirstFlagGermQuotient_spec F y1 h hh).2
    have hinj := nativeHolGerm_comap_injective hπ.1 x.1
    have ht0 : t ≠ 0 := (originalFirstFlagGermParameter_spec F y1).1.ne_zero
    have hq0 : q ≠ 0 := by
      intro h0
      apply hqres
      rw [h0, map_zero]
    have hct : NativeHolGerm.comap π hπ.1.1 x.1 t ≠ 0 :=
      fun h0 => ht0 (hinj (h0.trans (map_zero _).symm))
    have hcq : NativeHolGerm.comap π hπ.1.1 x.1 q ≠ 0 :=
      fun h0 => hq0 (hinj (h0.trans (map_zero _).symm))
    -- the vector of `π^* h`
    have hsplit : NativeHolGerm.comap π hπ.1.1 x.1 h =
        NativeHolGerm.comap π hπ.1.1 x.1 t ^ a * NativeHolGerm.comap π hπ.1.1 x.1 q := by
      rw [hfac, map_mul, map_pow]
    have hvec : originalFlagGermVector W x _ hh' =
        a • originalFlagGermVector W x _ hct + originalFlagGermVector W x _ hcq := by
      rw [originalFlagGermVector_congr W x hh' (mul_ne_zero (pow_ne_zero a hct) hcq) hsplit,
        originalFlagGermVector_mul W x _ _ (pow_ne_zero a hct) hcq,
        originalFlagGermVector_pow W x _ hct a]
    -- the first step
    have hB := originalFlagGermVector_comap_parameter hπ x hy hct
    -- the quotient: restriction commutes with pull-back
    set x1 := OriginalFlagGermPoint.first W x with hx1def
    have hrc := restriction_comap_eq hπ x1 q
    have htailinj := nativeHolGerm_comap_injective hπ.tailMap_isFlagLifting.1 x1
    have hres' :
        originalFirstFlagGermRestriction W x1 (NativeHolGerm.comap π hπ.1.1 x.1 q) ≠ 0 := by
      intro h0
      have h1 := hrc.symm.trans h0
      exact hqres (htailinj (h1.trans (map_zero _).symm))
    have hA := originalFlagGermVector_cons_zero_of_restriction_ne_zero W x _ hcq hres'
    -- induction on the tails
    have hytail : hπ.tailMap (OriginalFlagGermPoint.tail W x).1 ∈
        F.tail.flag (Fin.last m) := (OriginalFlagGermPoint.tail F y).property
    have hrne : originalFirstFlagGermRestriction F y1 q ≠ 0 := hqres
    have hrc' : originalFirstFlagGermRestriction W x1 (NativeHolGerm.comap π hπ.1.1 x.1 q) =
        NativeHolGerm.comap hπ.tailMap hπ.tailMap_isFlagLifting.1.1
          (OriginalFlagGermPoint.tail W x).1 (originalFirstFlagGermRestriction F y1 q) := hrc
    have hIH := ih F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting
      (OriginalFlagGermPoint.tail W x) hytail (originalFirstFlagGermRestriction F y1 q) hrne
      (by rw [← hrc']; exact hres')
    -- the vector of `h`
    have hhvec : originalFlagGermVector F y h hh = Fin.cons a
        (originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F y)
          (originalFirstFlagGermResidual F y1 h hh)
          (originalFirstFlagGermResidual_ne_zero F y1 h hh)) := rfl
    -- integer vectors
    have hAz : (fun i => (originalFlagGermVector W x _ hcq i : ℤ)) =
        Fin.cons 0 (fun j => (originalFlagGermVector W.tail (OriginalFlagGermPoint.tail W x)
          _ hres' j : ℤ)) := by
      rw [hA]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.cons_succ]
        rfl
    have hVW : (fun i => (originalFlagGermVector W x _ hh' i : ℤ)) =
        (a : ℤ) • (fun i => (originalFlagGermVector W x _ hct i : ℤ)) +
          (fun i => (originalFlagGermVector W x _ hcq i : ℤ)) := by
      rw [hvec]
      funext i
      simp
    have hVF : (fun i => (originalFlagGermVector F y h hh i : ℤ)) =
        Fin.cons (a : ℤ) (fun j => (originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F y)
          (originalFirstFlagGermRestriction F y1 q) hrne j : ℤ)) := by
      rw [hhvec]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.cons_succ]
        rfl
    have hIH' : (fun j => (originalFlagGermVector W.tail (OriginalFlagGermPoint.tail W x)
          (originalFirstFlagGermRestriction W x1 (NativeHolGerm.comap π hπ.1.1 x.1 q)) hres' j :
            ℤ)) =
        ofLex (flagLiftingCorrection m F.tail W.tail hπ.tailMap hπ.tailMap_isFlagLifting
          (toLex fun j => (originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F y)
            (originalFirstFlagGermRestriction F y1 q) hrne j : ℤ))) := by
      rw [originalFlagGermVector_congr W.tail (OriginalFlagGermPoint.tail W x) hres'
        (by rw [← hrc']; exact hres') hrc']
      exact hIH
    rw [hVW, hB, hAz, hVF, flagLiftingCorrection_succ, integerCorrectionStep_cons, ← hIH']
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      try ring

/-- Matrix form of the germ-level `prop:cormatrix`. -/
theorem originalFlagGermLexVector_comap_eq {n : ℕ} {F W : OriginalFlagGeometry.{u} n}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) (x : OriginalFlagGermPoint W)
    (hy : π x.1 ∈ F.flag (Fin.last n)) (h : NativeHolGerm n F.carrier (π x.1)) (hh : h ≠ 0)
    (hh' : NativeHolGerm.comap π hπ.1.1 x.1 h ≠ 0) :
    originalFlagGermLexVector W x _ hh' =
      toLex (ofLex (originalFlagGermLexVector F ⟨π x.1, hy⟩ h hh) ᵥ*
        flagLiftingCorrectionMatrix n F W π hπ) := by
  rw [flagLiftingCorrectionMatrix_vecMul_int, toLex_ofLex]
  exact originalFlagGermVector_comap_eq n F W π hπ x hy h hh hh'

/-! ### Valuations of `ℂ(X)` induced on modifications -/

section FunctionField

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance of2CorTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of2CorCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance of2CorManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

omit [IsIntegral X] in
/-- Pull-back of germs along a composite. -/
theorem nativeHolGerm_comap_comp' {F W : OriginalFlagGeometry.{0} n}
    (π : F.carrier → SchemeComplexPoint f)
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ π)
    (p : W.carrier → F.carrier) (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ p)
    (z : W.carrier) (g : NativeHolGerm n (SchemeComplexPoint f) (π (p z))) :
    NativeHolGerm.comap (π ∘ p) (hπ.comp hp) z g =
      NativeHolGerm.comap p hp z (NativeHolGerm.comap π hπ (p z) g) := by
  obtain ⟨G, hG, rfl⟩ := NativeHolGerm.exists_eq_mk g
  apply Subtype.ext
  rfl

/-- The flag point is unique, so the induced valuation may be read at any point of the last flag
member. -/
theorem modificationFlagValuation_eq_at (F : OriginalFlagGeometry.{0} n)
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π)
    (y : OriginalFlagGermPoint F) :
    modificationFlagValuation f F hπ =
      (originalFlagGermFractionValuation F y).comap
        ((modificationGermFractionMap f F hπ y.1).comp
          (schemeNativeFunctionFieldGerm f n (π y.1))) := by
  have : Subsingleton (OriginalFlagGermPoint F) := by
    obtain ⟨z, hz⟩ := F.smooth.last_eq_singleton
    constructor
    intro a b
    apply Subtype.ext
    have ha := a.property
    have hb := b.property
    change a.1 ∈ F.flag (Fin.last n) at ha
    change b.1 ∈ F.flag (Fin.last n) at hb
    rw [hz] at ha hb
    exact ha.trans hb.symm
  have hpt : modificationFlagPoint n F = y := Subsingleton.elim _ _
  have key : ∀ z₁ z₂ : OriginalFlagGermPoint F, z₁ = z₂ →
      (originalFlagGermFractionValuation F z₁).comap
          ((modificationGermFractionMap f F hπ z₁.1).comp
            (schemeNativeFunctionFieldGerm f n (π z₁.1))) =
        (originalFlagGermFractionValuation F z₂).comap
          ((modificationGermFractionMap f F hπ z₂.1).comp
            (schemeNativeFunctionFieldGerm f n (π z₂.1))) := by
    rintro z₁ _ rfl
    rfl
  exact key _ _ hpt

/-- Stalk formula at any point of the last flag member. -/
theorem modificationFlagValuation_stalk_at (F : OriginalFlagGeometry.{0} n)
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π)
    (y : OriginalFlagGermPoint F)
    (g : X.presheaf.stalk (schemeComplexPointImage f (π y.1))) :
    modificationFlagValuation f F hπ (algebraMap _ X.functionField g) =
      originalFlagGermValuation F y
        (NativeHolGerm.comap π hπ.1 _ (schemeNativeStalkGerm f n (π y.1) g)) := by
  rw [modificationFlagValuation_eq_at f F hπ y]
  change originalFlagGermFractionValuation F y
      (modificationGermFractionMap f F hπ y.1
        (schemeNativeFunctionFieldGerm f n (π y.1) (algebraMap _ X.functionField g))) = _
  rw [schemeNativeFunctionFieldGerm_stalk, modificationGermFractionMap_algebraMap,
    originalFlagGermFractionValuation_algebraMap]

/-- **Algebraic `prop:cormatrix`.** If `p : X'' → X'` lifts the flag `F•` on the modification
`π : X' → X(ℂ)` to the flag `W•`, then the valuation of `ℂ(X)` induced by `W•` on `π ∘ p` is the
one induced by `F•` on `π`, times the correction matrix `cor(F•, p)`. -/
theorem modificationFlagValuation_lifting {F W : OriginalFlagGeometry.{0} n}
    {π : F.carrier → SchemeComplexPoint f} (hπ : IsAnalyticModification (n := n) π)
    {p : W.carrier → F.carrier} (hp : IsFlagLifting F W p) :
    modificationFlagValuation f W
        (AnalyticModificationComposition.isAnalyticModification_comp hπ hp.1) =
      lexMapValuation (flagLiftingCorrectionMatrix n F W p hp)
        (isUnitUpperTriangular_flagLiftingCorrectionMatrix n F W p hp)
        (modificationFlagValuation f F hπ) := by
  set x := modificationFlagPoint n W with hxdef
  have hy : p x.1 ∈ F.flag (Fin.last n) := (hp.2 (Fin.last n)).1 x.property
  set y : OriginalFlagGermPoint F := ⟨p x.1, hy⟩ with hydef
  set hπp := AnalyticModificationComposition.isAnalyticModification_comp hπ hp.1 with hπpdef
  set M := flagLiftingCorrectionMatrix n F W p hp with hMdef
  have hM := isUnitUpperTriangular_flagLiftingCorrectionMatrix n F W p hp
  -- agreement on the stalk at `c = π (p x)`
  have hstalk : ∀ g : X.presheaf.stalk (schemeComplexPointImage f (π (p x.1))),
      modificationFlagValuation f W hπp (algebraMap _ X.functionField g) =
        lexMapValuation M hM (modificationFlagValuation f F hπ)
          (algebraMap _ X.functionField g) := by
    intro g
    rw [lexMapValuation_apply, modificationFlagValuation_stalk_at f F hπ y g]
    refine (modificationFlagValuation_stalk_at f W hπp x g).trans ?_
    change originalFlagGermValuation W x (NativeHolGerm.comap (π ∘ p) hπp.1 x.1
      (schemeNativeStalkGerm f n (π (p x.1)) g)) = _
    by_cases hg : g = 0
    · subst hg
      simp only [map_zero, AddValuation.map_zero]
      rfl
    have hG : schemeNativeStalkGerm f n (π (p x.1)) g ≠ 0 := fun h0 =>
      hg (schemeNativeStalkGerm_injective f n _ (h0.trans (map_zero _).symm))
    have hcG : NativeHolGerm.comap π hπ.1 (p x.1) (schemeNativeStalkGerm f n (π (p x.1)) g) ≠ 0 :=
      fun h0 => hG (nativeHolGerm_comap_injective hπ (p x.1) (h0.trans (map_zero _).symm))
    have hcomp := nativeHolGerm_comap_comp' f π hπ.1 p hp.1.1 x.1
      (schemeNativeStalkGerm f n (π (p x.1)) g)
    have hppG : NativeHolGerm.comap p hp.1.1 x.1
        (NativeHolGerm.comap π hπ.1 (p x.1) (schemeNativeStalkGerm f n (π (p x.1)) g)) ≠ 0 :=
      fun h0 => hcG (nativeHolGerm_comap_injective hp.1 x.1 (h0.trans (map_zero _).symm))
    have hcomp' : NativeHolGerm.comap (π ∘ p) hπp.1 x.1 (schemeNativeStalkGerm f n (π (p x.1)) g) =
        NativeHolGerm.comap p hp.1.1 x.1
          (NativeHolGerm.comap π hπ.1 (p x.1) (schemeNativeStalkGerm f n (π (p x.1)) g)) := hcomp
    have hne : NativeHolGerm.comap (π ∘ p) hπp.1 x.1
        (schemeNativeStalkGerm f n (π (p x.1)) g) ≠ 0 := by
      rw [hcomp']
      exact hppG
    rw [originalFlagGermValuation_apply_of_ne_zero W x _ hne,
      originalFlagGermValuation_apply_of_ne_zero F y _ hcG, lexWithTopHom_coe]
    congr 1
    have hvec := originalFlagGermLexVector_comap_eq hp x hy _ hcG hppG
    rw [← hvec]
    change toLex (fun i => (originalFlagGermVector W x _ hne i : ℤ)) =
      toLex (fun i => (originalFlagGermVector W x _ hppG i : ℤ))
    rw [originalFlagGermVector_congr W x hne hppG hcomp']
  apply AddValuation.ext
  intro q
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective (A := X.presheaf.stalk (schemeComplexPointImage f (π (p x.1)))) q
  rw [AddValuation.map_div, AddValuation.map_div, hstalk a, hstalk b]

end FunctionField

end SGPT.Okounkov.OF2
