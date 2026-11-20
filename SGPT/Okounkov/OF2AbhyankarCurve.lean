import SGPT.Okounkov.OF2AbhyankarFlagExample
import SGPT.Projective.AlgebraicCurveClosedPoint
import SGPT.NAPotential.AlgPrimes2Normal
import SGPT.GAGA.OkoCloseDXMain
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.FactorizationDomain
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# `rmk:Abhyankar` in dimension `≤ 1`

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar`: *if a valuation has value group
identified with `ℤⁿ_lex` and maximal rational rank `n`, then [CFKLRS17, Thm 2.9] shows that it is
equivalent to … a valuation induced by an admissible flag on a modification of `X`.*

We prove the cited statement in dimension `n ≤ 1`, where it holds with **equality** and without
modification:

* `n = 0`: there is only one valuation `ℂ(X)^× → ℤ⁰` (`addValuation_fin_zero_eq`).
* `n = 1` (`exists_isSmoothFlag_eq_flagValuation_of_curve`): on an integral smooth projective
  complex curve `X`, every surjective valuation `ν : ℂ(X)^× → ℤ` (trivial on `ℂ^×`
  automatically) is the flag valuation `ν_{Y•}` of the flag `X ⊇ {p}`, `p` a point of `X`.

The proof of the case `n = 1`: the centre of `ν` specializes to a closed point `x`, so `ν ≥ 0` on
`𝒪_{X,x}`, a discrete valuation ring (`X` is a smooth curve); `x` is a complex point `p`, and the
flag valuation of `X ⊇ {p}` is surjective and nonnegative on `𝒪_{X,x}` too. Two surjective
`ℤ`-valued valuations of the fraction field of a DVR which are nonnegative on it coincide
(`eq_of_nonneg_of_isDiscreteValuationRing`): both are `k ↦ k` on `u ϖᵏ`.

The case `n ≥ 2` of [CFKLRS17, Thm 2.9] (realization of divisorial valuations on blow-up towers,
Abhyankar's inequality, induction on the residue field) is not formalized.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF2

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Okounkov SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences

/-! ### Dimension zero -/

/-- There is only one valuation with values in `ℤ⁰ ∪ {∞}`. -/
theorem addValuation_fin_zero_eq {K : Type*} [Field K]
    (v w : AddValuation K (WithTop (Lex (Fin 0 → ℤ)))) : v = w := by
  apply AddValuation.ext
  intro x
  by_cases hx : x = 0
  · rw [hx, v.map_zero, w.map_zero]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hx)
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp ((w.ne_top_iff).mpr hx)
  rw [← ha, ← hb]
  congr 1
  apply ofLex.injective
  funext i
  exact Fin.elim0 i

/-! ### Discrete valuation rings -/

section DVR

/-- An element of `ℤ¹_lex` is determined by its coordinate. -/
theorem lex_fin_one_ext {y z : Lex (Fin 1 → ℤ)} (h : ofLex y 0 = ofLex z 0) : y = z := by
  apply ofLex.injective
  funext i
  rw [Fin.fin_one_eq_zero i]
  exact h

/-- A lexicographically nonnegative vector has nonnegative first coordinate. -/
theorem ofLex_zero_nonneg_of_nonneg {m : ℕ} {y : Lex (Fin (m + 1) → ℤ)} (hy : 0 ≤ y) :
    0 ≤ ofLex y 0 := by
  rcases eq_or_lt_of_le hy with heq | hlt
  · rw [← heq]
    exact le_of_eq rfl
  · obtain ⟨i, hbefore, hi⟩ := (toLex_lt_toLex_iff (x := (0 : Fin (m + 1) → ℤ))
      (y := ofLex y)).mp hlt
    by_cases hi0 : i = 0
    · subst hi0
      exact le_of_lt hi
    · have h0i : (0 : Fin (m + 1)) < i := lt_of_le_of_ne (Fin.zero_le i) (Ne.symm hi0)
      rw [← hbefore 0 h0i]
      exact le_of_eq rfl

variable {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- A valuation nonnegative on `A` vanishes on the units of `A`. -/
theorem val_unit_eq_zero (v : AddValuation K (WithTop (Lex (Fin 1 → ℤ))))
    (hvA : ∀ a : A, 0 ≤ v (algebraMap A K a)) (u : Aˣ) : v (algebraMap A K (u : A)) = 0 := by
  have h1 : v (algebraMap A K (u : A)) + v (algebraMap A K ((u⁻¹ : Aˣ) : A)) = 0 := by
    rw [← v.map_mul, ← map_mul, Units.mul_inv, map_one, v.map_one]
  exact ((add_eq_zero_iff_of_nonneg (hvA _) (hvA _)).mp h1).1

omit [IsFractionRing A K] in
/-- `a = u ϖᵏ`: every valuation nonnegative on `A` takes the value `k v(ϖ)` on `a`. -/
theorem exists_pow_val {ϖ : A} (hϖ : Irreducible ϖ) {a : A} (ha : a ≠ 0) :
    ∃ k : ℕ, ∀ v : AddValuation K (WithTop (Lex (Fin 1 → ℤ))),
      (∀ b : A, 0 ≤ v (algebraMap A K b)) →
        v (algebraMap A K a) = k • v (algebraMap A K ϖ) := by
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨k, fun v hv => ?_⟩
  rw [map_mul, v.map_mul, val_unit_eq_zero v hv u, zero_add, map_pow, v.map_pow]

/-- A surjective valuation nonnegative on `A` takes the value `1` on a uniformizer. -/
theorem val_uniformizer {ϖ : A} (hϖ : Irreducible ϖ)
    (v : AddValuation K (WithTop (Lex (Fin 1 → ℤ)))) (hv : Function.Surjective v)
    (hvA : ∀ a : A, 0 ≤ v (algebraMap A K a)) :
    v (algebraMap A K ϖ) = ((toLex (fun _ => (1 : ℤ)) : Lex (Fin 1 → ℤ)) :
      WithTop (Lex (Fin 1 → ℤ))) := by
  have hϖ0 : algebraMap A K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hϖ.ne_zero
  obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hϖ0)
  obtain ⟨x, hx⟩ := hv ((toLex (fun _ => (1 : ℤ)) : Lex (Fin 1 → ℤ)) :
    WithTop (Lex (Fin 1 → ℤ)))
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, v.map_zero] at hx
    exact WithTop.top_ne_coe hx
  obtain ⟨k, hk⟩ := exists_pow_val (K := K) hϖ ha0
  obtain ⟨l, hl⟩ := exists_pow_val (K := K) hϖ hb0
  have hsplit : v (algebraMap A K a) =
      v (algebraMap A K a / algebraMap A K b) + v (algebraMap A K b) := by
    rw [← v.map_mul, div_mul_cancel₀ _ hbK]
  rw [hx, hk v hvA, hl v hvA, ← hp] at hsplit
  have hcoe : ((k • p : Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) =
      ((toLex (fun _ => (1 : ℤ)) + l • p : Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) := by
    rw [WithTop.coe_add, WithTop.coe_nsmul, WithTop.coe_nsmul]
    exact hsplit
  have h0 := congrArg (fun y : Lex (Fin 1 → ℤ) => ofLex y 0) (WithTop.coe_injective hcoe)
  change (k : ℤ) * ofLex p 0 = 1 + (l : ℤ) * ofLex p 0 at h0
  have hp0 : 0 ≤ ofLex p 0 := by
    apply ofLex_zero_nonneg_of_nonneg (m := 0)
    have := hvA ϖ
    rw [← hp] at this
    exact WithTop.coe_le_coe.mp this
  have hmul : ofLex p 0 * ((k : ℤ) - l) = 1 := by linarith
  have hone : ofLex p 0 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hmul with h | h
    · exact h
    · omega
  rw [← hp]
  congr 1
  exact lex_fin_one_ext hone

/-- **Two surjective valuations `K^× → ℤ` nonnegative on a DVR `A` with fraction field `K`
coincide.** -/
theorem eq_of_nonneg_of_isDiscreteValuationRing
    (v w : AddValuation K (WithTop (Lex (Fin 1 → ℤ))))
    (hv : Function.Surjective v) (hw : Function.Surjective w)
    (hvA : ∀ a : A, 0 ≤ v (algebraMap A K a)) (hwA : ∀ a : A, 0 ≤ w (algebraMap A K a)) :
    v = w := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hvϖ := val_uniformizer hϖ v hv hvA
  have hwϖ := val_uniformizer hϖ w hw hwA
  set P : Lex (Fin 1 → ℤ) := toLex (fun _ => (1 : ℤ)) with hP
  apply AddValuation.ext
  intro x
  by_cases hx : x = 0
  · rw [hx, v.map_zero, w.map_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hx
    exact hx rfl
  obtain ⟨k, hk⟩ := exists_pow_val (K := K) hϖ ha0
  obtain ⟨l, hl⟩ := exists_pow_val (K := K) hϖ hb0
  have key : ∀ u : AddValuation K (WithTop (Lex (Fin 1 → ℤ))),
      (∀ c : A, 0 ≤ u (algebraMap A K c)) →
      u (algebraMap A K ϖ) = (P : WithTop (Lex (Fin 1 → ℤ))) →
      u (algebraMap A K a / algebraMap A K b) =
        ((k • P - l • P : Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) := by
    intro u hu huϖ
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp ((u.ne_top_iff).mpr hx)
    have hsplit : u (algebraMap A K a) =
        u (algebraMap A K a / algebraMap A K b) + u (algebraMap A K b) := by
      rw [← u.map_mul, div_mul_cancel₀ _ hbK]
    rw [hk u hu, hl u hu, huϖ, ← hy] at hsplit
    have hcoe : ((k • P : Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) =
        ((y + l • P : Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) := by
      rw [WithTop.coe_add, WithTop.coe_nsmul, WithTop.coe_nsmul]
      exact hsplit
    have hyeq : y = k • P - l • P := by
      have := WithTop.coe_injective hcoe
      rw [this]
      abel
    rw [← hy, hyeq]
  rw [key v hvA hvϖ, key w hwA hwϖ]

end DVR

/-! ### Smooth projective curves -/

section Curve

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 f]

local instance of2CurveTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of2CurveCharts : ChartedSpace (ComplexModel 1) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 1
local instance of2CurveManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold 1 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 1

/-- The flag `X(ℂ) ⊇ {p}` of a curve. -/
def pointFlag (p : SchemeComplexPoint f) : Fin (1 + 1) → Set (SchemeComplexPoint f) :=
  fun i => if i = 0 then univ else {p}

/-- `X(ℂ) ⊇ {p}` is a smooth flag. -/
theorem isSmoothFlag_pointFlag (E : ClosedProjectiveEmbedding f) (p : SchemeComplexPoint f) :
    letI := E.isSeparated
    letI := E.quasiCompact
    IsSmoothFlag (pointFlag f p) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : Nonempty (SchemeComplexPoint f) := ⟨p⟩
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 1
  refine ⟨by simp [pointFlag], ?_, fun i => ?_⟩
  · intro i j hij
    by_cases hj : j = 0
    · have hi : i = 0 := le_antisymm (hj ▸ hij) (Fin.zero_le i)
      subst hi; subst hj
      exact le_rfl
    · by_cases hi : i = 0
      · simp [pointFlag, hi]
      · simp [pointFlag, hi, hj]
  · by_cases hi : i = 0
    · subst hi
      simpa [pointFlag] using
        (FactorizationDomain.isClosedConnectedSubmanifold_univ (n := 1)
          (M := SchemeComplexPoint f))
    · have hi1 : (i : ℕ) = 1 := by
        have := i.isLt
        have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
        omega
      simp only [pointFlag, if_neg hi, hi1]
      exact DominationLogResolution.isClosedConnectedSubmanifold_singleton p

/-- **`rmk:Abhyankar` in dimension `1`.** On an integral smooth projective complex curve `X`,
every surjective valuation `ν : ℂ(X)^× → ℤ` is the flag valuation of a flag `X ⊇ {p}`
(equality, on `X` itself). -/
theorem exists_isSmoothFlag_eq_flagValuation_of_curve (E : ClosedProjectiveEmbedding f)
    (v : AddValuation X.functionField (WithTop (Lex (Fin 1 → ℤ))))
    (hv : Function.Surjective v) :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∃ (Y : Fin (1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
      v = schemeFubiniStudyFunctionFieldValuation f 1 E Y hY := by
  let := E.isSeparated
  let := E.quasiCompact
  let := E.isProper
  let := E.locallyOfFiniteType
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  -- a closed point `x` specializing the centre `z` of `v`
  set z := valuationCenter f v with hz
  have hzc := isValuationCenter_valuationCenter f v
  obtain ⟨x, hxz, hx⟩ := (isClosed_closure (s := ({z} : Set X))).exists_closed_singleton
    ⟨z, subset_closure (mem_singleton z)⟩
  have hsp : z ⤳ x := specializes_iff_mem_closure.mpr hxz
  -- `v ≥ 0` on `𝒪_{X,x}`
  have hvx : ∀ g : X.presheaf.stalk x, 0 ≤ v (algebraMap _ X.functionField g) := by
    intro g
    have hcomp : algebraMap (X.presheaf.stalk z) X.functionField
        ((X.presheaf.stalkSpecializes hsp).hom g) = algebraMap _ X.functionField g := by
      change ((X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
        ((X.presheaf.stalkSpecializes hsp).hom g)) = _
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    rw [← hcomp]
    exact hzc.1 _
  -- the complex point over `x` and its flag
  let p : SchemeComplexPoint f := ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩
  have hpx : schemeComplexPointImage f p = x := pointOfClosedPoint_apply f x hx _
  have hY := isSmoothFlag_pointFlag f E p
  refine ⟨pointFlag f p, hY, ?_⟩
  -- the flag point is `p`
  have hpt : (schemeProjectiveOriginalFlagPoint f 1 E
      (schemeProjectiveTNKahlerBackground f 1 E) (pointFlag f p) hY).val = p := by
    have hmem := (schemeProjectiveOriginalFlagPoint f 1 E
      (schemeProjectiveTNKahlerBackground f 1 E) (pointFlag f p) hY).property
    change _ ∈ pointFlag f p (Fin.last 1) at hmem
    have hlast : pointFlag f p (Fin.last 1) = {p} := by
      simp only [pointFlag]
      rw [if_neg (by decide)]
    rw [hlast] at hmem
    exact hmem
  have hcen := schemeOriginalFlagFunctionFieldValuation_isCenter f 1 E
    (schemeProjectiveTNKahlerBackground f 1 E) (pointFlag f p) hY
  rw [hpt, hpx] at hcen
  -- the DVR `𝒪_{X,x}`
  have : AlgebraicGeometry.IsNoetherian X := E.isNoetherian
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    SGPT.NAPotential.AlgPrimes2.isDiscreteValuationRing_stalk f 1
      (SGPT.Projective.NumEq.AlgebraicCurveDegree.closedPoint_coheight_eq_one f x hx)
  have hsurj : Function.Surjective (schemeFubiniStudyFunctionFieldValuation f 1 E (pointFlag f p) hY) :=
    surjective_schemeFubiniStudyFunctionFieldValuation (m := 0) f E (pointFlag f p) hY
  exact eq_of_nonneg_of_isDiscreteValuationRing (A := X.presheaf.stalk x) v _ hv hsurj hvx hcen.1

end Curve

end SGPT.Okounkov.OF2
