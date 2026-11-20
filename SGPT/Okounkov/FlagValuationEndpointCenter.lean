import SGPT.Okounkov.ValuationCoarseningCenters
import SGPT.Okounkov.SchemeOriginalFunctionFieldValuation

/-!
# The actual original flag endpoint is its valuation centre

The native germ recursion is proved to dominate the original holomorphic
local ring. The genuine algebraic-stalk embedding then identifies the actual
centre of the function-field flag valuation, without a centre certificate.
This identifies endpoints, not the intermediate flag carriers or arbitrary
flag presentations on resolutions.

Blueprint: `source-flag-valuation-endpoint-centre.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes IsLocalRing
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

private theorem eval_firstFlag_restriction {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) :
    NativeHolGerm.eval (originalFirstFlagGermRestriction F x f) = NativeHolGerm.eval f :=
  NativeHolGerm.eval_comap _ _ _ f

/-- A zero actual recursive tuple forces a nonzero residue at the original
endpoint, by literal restriction and induction on the genuine tail. -/
theorem originalFlagGermVector_zero_implies_eval_ne_zero :
    ∀ {n : ℕ} (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
      (f : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0),
      originalFlagGermVector F x f hf = 0 → NativeHolGerm.eval f ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro F x f hf _ hzero
    apply hf
    apply NativeHolGerm.zeroDimensionEval_injective
    simpa only [map_zero] using hzero
  | succ m ih =>
    intro F x f hf hzero
    let y := OriginalFlagGermPoint.first F x
    let z := OriginalFlagGermPoint.tail F x
    have hhead : originalFirstFlagGermOrderNat F y f = 0 := congrFun hzero 0
    have htail : originalFlagGermVector F.tail z
        (originalFirstFlagGermResidual F y f hf)
        (originalFirstFlagGermResidual_ne_zero F y f hf) = 0 := by
      funext i
      exact congrFun hzero i.succ
    have hq : originalFirstFlagGermQuotient F y f hf = f := by
      have hfac := (originalFirstFlagGermQuotient_spec F y f hf).1
      simpa only [hhead, pow_zero, one_mul] using hfac.symm
    have hres : NativeHolGerm.eval (originalFirstFlagGermResidual F y f hf) =
        NativeHolGerm.eval f := by
      unfold originalFirstFlagGermResidual
      exact (eval_firstFlag_restriction F y _).trans (congrArg NativeHolGerm.eval hq)
    have h := ih F.tail z (originalFirstFlagGermResidual F y f hf)
      (originalFirstFlagGermResidual_ne_zero F y f hf) htail
    exact fun hz => h (hres.trans hz)

theorem originalFlagGermValuation_nonneg {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f : NativeHolGerm n F.carrier x.1) :
    0 ≤ originalFlagGermValuation F x f := by
  by_cases hf : f = 0
  · subst f
    rw [(originalFlagGermValuation F x).map_zero]
    exact le_top
  rw [originalFlagGermValuation_apply_of_ne_zero F x f hf]
  apply WithTop.coe_le_coe.mpr
  by_contra hneg
  have hlt := lt_of_not_ge hneg
  change toLex (fun i => (originalFlagGermVector F x f hf i : ℤ)) <
    toLex (0 : Fin n → ℤ) at hlt
  obtain ⟨i, _, hi⟩ := ValCurr.toLex_lt_toLex_iff.mp hlt
  exact not_lt_of_ge (Nat.cast_nonneg (originalFlagGermVector F x f hf i)) hi

/-- Strict positivity on the actual maximal ideal is a proved consequence
of the original recursion, not a valuation-centre assumption. -/
theorem originalFlagGermValuation_pos_of_mem_maximalIdeal {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (f : NativeHolGerm n F.carrier x.1)
    (hfM : f ∈ maximalIdeal (NativeHolGerm n F.carrier x.1)) :
    0 < originalFlagGermValuation F x f := by
  apply lt_of_le_of_ne (originalFlagGermValuation_nonneg F x f)
  intro hzero
  have hvzero : originalFlagGermValuation F x f = 0 := hzero.symm
  by_cases hf : f = 0
  · subst f
    rw [(originalFlagGermValuation F x).map_zero] at hvzero
    exact WithTop.top_ne_zero hvzero
  rw [originalFlagGermValuation_apply_of_ne_zero F x f hf] at hvzero
  have hlex : originalFlagGermLexVector F x f hf = 0 := WithTop.coe_injective hvzero
  have hvec : originalFlagGermVector F x f hf = 0 := by
    funext i
    have hi := congrArg (fun v : Lex (Fin n → ℤ) => ofLex v i) hlex
    change (originalFlagGermVector F x f hf i : ℤ) = 0 at hi
    exact_mod_cast hi
  have heval := originalFlagGermVector_zero_implies_eval_ne_zero F x f hf hvec
  exact (show ¬IsUnit f from hfM) ((NativeHolGerm.isUnit_iff_eval_ne_zero f).mpr heval)

private theorem fullPrefixValuation_eq {R : Type*} [Ring R] {n : ℕ}
    (v : AddValuation R (WithTop (Lex (Fin n → ℤ)))) :
    ValCurr.prefixValuation (Nat.le_refl n) v = v := by
  ext r
  change ValCurr.prefixWithTopHom (Nat.le_refl n) (v r) = v r
  induction v r using WithTop.recTopCoe with
  | top => rfl
  | coe x =>
    change (ValCurr.prefixHom (Nat.le_refl n) x : WithTop (Lex (Fin n → ℤ))) =
      (x : WithTop (Lex (Fin n → ℤ)))
    apply congrArg (fun z : Lex (Fin n → ℤ) => (z : WithTop (Lex (Fin n → ℤ))))
    apply ofLex.injective
    funext i
    rfl

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance endpointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance endpointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance endpointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The actual endpoint scheme point is a centre of the actual global
function-field valuation of the same original flag. -/
theorem schemeOriginalFlagFunctionFieldValuation_isCenter (e : ClosedProjectiveEmbedding f)
    (omega : KahlerBackground n (SchemeComplexPoint f))
    (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    AlgebraicValuation.IsValuationCenter
      (schemeOriginalFlagFunctionFieldValuation f n e omega Y hY)
      (schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e omega Y hY).val) := by
  constructor
  · intro a
    rw [schemeOriginalFlagFunctionFieldValuation_stalk]
    exact originalFlagGermValuation_nonneg _ _ _
  · intro a ha
    rw [schemeOriginalFlagFunctionFieldValuation_stalk]
    apply originalFlagGermValuation_pos_of_mem_maximalIdeal
    exact map_nonunit
      (schemeNativeStalkGerm f n (schemeProjectiveOriginalFlagPoint f n e omega Y hY).val) a ha

/-- Equivalent actual original function-field valuations have the SAME
geometric endpoint scheme point, by their produced centres and separatedness. -/
theorem schemeOriginalFlagEndpoint_eq_of_lexEquivalent (e : ClosedProjectiveEmbedding f)
    (omega omega' : KahlerBackground n (SchemeComplexPoint f))
    (Y Z : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) (hZ : IsSmoothFlag Z)
    (h : ValCurr.ValuationsLexEquivalent
      (schemeOriginalFlagFunctionFieldValuation f n e omega Y hY)
      (schemeOriginalFlagFunctionFieldValuation f n e omega' Z hZ)) :
    schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e omega Y hY).val =
      schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e omega' Z hZ).val := by
  have hc := schemeOriginalFlagFunctionFieldValuation_isCenter f n e omega Y hY
  have hiff := ValCurr.isValuationCenter_prefix_iff_of_lexEquivalent (Nat.le_refl n) h
    (schemeComplexPointImage f (schemeProjectiveOriginalFlagPoint f n e omega Y hY).val)
  rw [fullPrefixValuation_eq, fullPrefixValuation_eq] at hiff
  exact (hiff.mp hc).unique f
    (schemeOriginalFlagFunctionFieldValuation_isCenter f n e omega' Z hZ)

end Scheme

end SGPT.Okounkov
