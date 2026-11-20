import SGPT.Checks.Comparison.SourceRationalPromotion
import SGPT.Checks.Comparison.BJCanonicalModuleTopology

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-!
# `thm:BJappseq`: statement and reduction to countable selection

Source: `chapter_NApotential.tex`, `thm:BJappseq` (citing Boucksom–Jonsson, *Global
pluripotential theory over a trivially valued field*, Corollary 12.18). Let `X` be an
irreducible complex projective variety, `S` an ample line bundle on `X` and
`φ ∈ PSH(L^An)`. Then there are rationals `ε_i ↘ 0` and a decreasing sequence
`φ_i ∈ 𝓗^gf_ℚ((L + ε_i S)^An)` converging pointwise to `φ`.

The psh metrics are those of the recalled definition `def:BJpshmetric`
(`SGPT.NAPotential.BJ.Printed.IsModuleTopologyPSH`): pointwise limits on all of `X^An` of
decreasing nets of rational generically finite Fubini–Study functions whose numerical classes
converge to `c₁(L)`. `𝓗^gf_ℚ((L + ε S)^An)` is `SGPT.NAPotential.BJ.Printed.IsRationalGF` at the *rational Picard
class* `L + ε [S]` (not only at its numerical class).

## Main definitions

* `SGPT.NAPotential.ThinApprox.BJ.AppSeq.ApproximatingSequence`: the conclusion of `thm:BJappseq` for given `S, L, φ`.
* `SGPT.NAPotential.ThinApprox.BJ.AppSeq.BJAppSeqStatement`: the statement of `thm:BJappseq`.
* `SGPT.NAPotential.ThinApprox.BJ.AppSeq.DecreasingNetSelection`: every decreasing net defining a psh metric has an
  increasing sequence of indices along which it still converges to the same metric. This is
  Boucksom–Jonsson's Theorem 12.17 (`thm:moncount`) for the defining nets.

## Main results

* `SGPT.NAPotential.ThinApprox.BJ.AppSeq.exists_package_picardClass_of_ample_gap`: a rational GF function whose class lies
  below a rational Picard class `T` by an ample gap is a rational GF function *of the rational
  Picard class `T`* (exact Picard class, not only numerical class).
* `SGPT.NAPotential.ThinApprox.BJ.AppSeq.approximatingSequence_of_selection`: a sequence of indices along which a defining net
  converges gives the conclusion of `thm:BJappseq` (with `ε_i = 1/(i+1)`).
* `SGPT.NAPotential.ThinApprox.BJ.AppSeq.bjAppSeq_of_selection`: `DecreasingNetSelection → BJAppSeqStatement`.

The converse and the characterization by countable infima of continuous functions are in
`SGPT.Checks.Comparison.BJAppSeqDini`. The selection principle itself is *not* proved here: Boucksom and
Jonsson derive it from the energy theory of their §§6–12.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
open SGPT.NAPotential.BJ.AppSeq

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Filter Topology
open Scheme.Modules SGPT.Foundations.Schemes
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.NativeNumericalFubiniStudy
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.ThinApprox.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed SGPT.NAPotential.ThinApprox.BJ.Printed

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {X : Scheme.{0}}

/-! ### Rational Picard classes of the canonical tensor powers -/

/-- The skeleton class of the canonical tensor power `M^{⊗n}` used by the Fubini–Study data
of `SGPT.Foundations.Envelope` is the `n`-th power of the class of `M`. -/
theorem toSkeleton_canonicalPower (M : X.Modules) (n : ℕ) :
    toSkeleton (CanonicalGeometry.bundleTensorPower M n) = (toSkeleton M) ^ n := by
  induction n with
  | zero => exact toSkeleton_unitObj
  | succ n ih =>
    change toSkeleton (CanonicalGeometry.bundleTensor
      (CanonicalGeometry.bundleTensorPower M n) M) = _
    have he : CanonicalGeometry.bundleTensor (CanonicalGeometry.bundleTensorPower M n) M =
        Scheme.Modules.tensorObj (CanonicalGeometry.bundleTensorPower M n) M := rfl
    rw [he, toSkeleton_tensorObj_eq, ih, pow_succ]

/-- The rational Picard class of `M^{⊗n}` (canonical tensor power) is `n [M]`, for any atlases. -/
theorem rationalPicardClass_canonicalPower {M : X.Modules} (a : LineBundleAtlas M) (n : ℕ)
    (b : LineBundleAtlas (CanonicalGeometry.bundleTensorPower M n)) :
    rationalPicardClass b = n • rationalPicardClass a := by
  have h : linePicardClass b = (linePicardClass a) ^ n := by
    apply Units.ext
    rw [linePicardClass_val, Units.val_pow_eq_pow_val, linePicardClass_val,
      toSkeleton_canonicalPower]
  unfold rationalPicardClass
  rw [h]
  exact (rationalizePicard X).map_nsmul _ _

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-! ### Promotion into an exact rational Picard class -/

/-- **Promotion into an exact rational Picard class.** If the numerical class of a rational GF
package `D` lies below the numerical class of a rational Picard class `T` by an ample class,
then the function of `D` is a rational GF function *of the rational Picard class `T`*: the
sections of `D` are multiplied by base-point-free sections of the ample difference
(`SGPT.NAPotential.BJ.SourceRationalPromotion.exists_rationalRay_of_numerical_ampleGap`), and the class of the resulting
package is computed in `Pic(X) ⊗ ℚ`. -/
theorem exists_package_picardClass_of_ample_gap [IsIntegral X] (D : RationalGFPackage X)
    (T : RationalPicardSpace X)
    (hgap : SGPT.NAPotential.BJ.NativePicard.numericalClass p T - D.numericalClass p ∈
      NativeRealNumericalClasses.ampleCone p) :
    ∃ E : RationalGFPackage X, E.picardClass = T ∧ ∀ v : BerkovichPoint p,
      E.eval p v = D.eval p v := by
  obtain ⟨M, a, m, hm, hrep⟩ := exists_actual_line_presentation T
  let hM := isInvertible_of_atlas a
  have hclass : SGPT.NAPotential.BJ.NativePicard.numericalClass p T =
      (m : ℝ)⁻¹ • NativeRealNumericalClasses.lineClass p M hM := by
    rw [hrep, SGPT.NAPotential.BJ.NativePicard.numericalClass_rat_smul, SGPT.NAPotential.BJ.NativePicard.numericalClass_line,
      ← Rat.cast_smul_eq_qsmul ℝ (1 / (m : ℚ))]
    simp only [one_div, Rat.cast_inv, Rat.cast_natCast]
  have hGap : (((m : ℚ)⁻¹ : ℚ) : ℝ) • NativeRealNumericalClasses.lineClass p M hM -
      D.toNative.numericalClass p ∈ NativeRealNumericalClasses.ampleCone p := by
    rw [Rat.cast_inv, Rat.cast_natCast, ← hclass, D.toNative_numericalClass]
    exact hgap
  obtain ⟨R, hRat, hNZ, hEval⟩ := SGPT.NAPotential.BJ.SourceRationalPromotion.exists_rationalRay_of_numerical_ampleGap p
    D.toNative D.toNative_nonzero D.toNative_isRational M hM (m : ℚ)⁻¹
    (inv_nonneg.mpr (Nat.cast_nonneg m)) hGap
  let N := FSData.ofRay M hM R
  let E := SGPT.NAPotential.BJ.NativeGF.ofNativeRational N hNZ hRat
  refine ⟨E, ?_, ?_⟩
  · have hb : rationalPicardClass (atlasOfInvertible N.invertible) =
        R.deg • rationalPicardClass a :=
      rationalPicardClass_canonicalPower a R.deg (atlasOfInvertible N.invertible)
    change (((1 : ℕ) : ℚ) / (R.m : ℚ)) • rationalPicardClass (atlasOfInvertible N.invertible) = T
    rw [hb, hrep, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
    congr 1
    have hdeg : (R.deg : ℚ) = R.m * (m : ℚ)⁻¹ := R.deg_eq
    have hRm : (R.m : ℚ) ≠ 0 := by exact_mod_cast R.m_pos.ne'
    rw [hdeg, Nat.cast_one]
    field_simp
  · intro v
    rw [SGPT.NAPotential.BJ.NativeGF.ofNativeRational_eval, FSData.ofRay_eval, hEval, D.toNative_eval]

/-! ### The statement -/

/-- The conclusion of `thm:BJappseq` for an invertible sheaf `S`, a rational Picard class `L`
and a function `φ` on `X^An`: rationals `ε_i > 0` decreasing to `0` and functions
`φ_i ∈ 𝓗^gf_ℚ((L + ε_i S)^An)`, decreasing in `i` at every point of `X^An`, with pointwise limit
`φ` on all of `X^An`. -/
def ApproximatingSequence {S : X.Modules} (hS : IsInvertible S) (L : RationalPicardSpace X)
    (φ : BerkovichPoint p → EReal) : Prop :=
  ∃ (ε : ℕ → ℚ) (ψ : ℕ → BerkovichPoint p → EReal),
    (∀ i, 0 < ε i) ∧ StrictAnti ε ∧ Tendsto (fun i => (ε i : ℝ)) atTop (𝓝 0) ∧
    (∀ i, IsRationalGF p (L + ε i • rationalPicardClass (atlasOfInvertible hS)) (ψ i)) ∧
    (∀ v, Antitone fun i => ψ i v) ∧
    ∀ v, Tendsto (fun i => ψ i v) atTop (𝓝 (φ v))

/-- **`thm:BJappseq`** ([BJ22, Corollary 12.18]), as a proposition: for every ample line bundle
`S` on `X`, every rational Picard class `L` and every `φ ∈ PSH(L^An)` (the recalled definition
`def:BJpshmetric`, nets indexed in universe `u`), the conclusion `ApproximatingSequence` holds. -/
def BJAppSeqStatement : Prop :=
  ∀ (S : X.Modules) (hS : SchemeLineAmpleness.IsAmple p S) (L : RationalPicardSpace X)
    (φ : BerkovichPoint p → EReal), IsModuleTopologyPSH.{u} p L φ →
      ApproximatingSequence p hS.isInvertible L φ

/-- **Countable selection for the defining nets** (Boucksom–Jonsson, Theorem 12.17, for the
decreasing nets of the definition of psh metrics): if a decreasing net of rational GF functions,
with numerical classes converging to that of `L`, converges pointwise to a function `φ ≢ -∞`,
then it converges to `φ` along some increasing sequence of indices. -/
def DecreasingNetSelection : Prop :=
  ∀ (L : RationalPicardSpace X) (φ : BerkovichPoint p → EReal) (D : DecreasingGFNet.{u} p),
    (∃ v, φ v ≠ ⊥) →
    Tendsto (fun i => (D.term i).numericalClass p) atTop
      (@nhds _ (numericalModuleTopology p) (SGPT.NAPotential.BJ.NativePicard.numericalClass p L)) →
    (∀ v, Tendsto (fun i => (D.term i).eval p v) atTop (𝓝 (φ v))) →
    ∃ j : ℕ → D.I, Monotone j ∧ ∀ v, Tendsto (fun n => (D.term (j n)).eval p v) atTop (𝓝 (φ v))

/-! ### From a selection to the approximating sequence -/

/-- The perturbation coefficients `ε_i = 1/(i+1)`. -/
def coeff (i : ℕ) : ℚ := 1 / ((i : ℚ) + 1)

theorem coeff_pos (i : ℕ) : 0 < coeff i := by
  unfold coeff
  positivity

theorem coeff_strictAnti : StrictAnti coeff := by
  intro i j hij
  unfold coeff
  apply one_div_lt_one_div_of_lt (by positivity)
  exact_mod_cast Nat.add_lt_add_right hij 1

theorem tendsto_coeff : Tendsto (fun i => (coeff i : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine h.congr fun i => ?_
  unfold coeff
  push_cast
  rfl

/-- A monotone sequence in a directed preorder can be pushed above any sequence of thresholds. -/
theorem exists_monotone_ge {I : Type*} [Preorder I] [IsDirectedOrder I]
    (a b : ℕ → I) : ∃ k : ℕ → I, Monotone k ∧ ∀ n, a n ≤ k n ∧ b n ≤ k n := by
  choose ub hub1 hub2 using fun x y : I => directed_of (· ≤ ·) x y
  let k : ℕ → I := fun n => Nat.rec (ub (a 0) (b 0))
    (fun n kn => ub kn (ub (a (n + 1)) (b (n + 1)))) n
  have hk0 : k 0 = ub (a 0) (b 0) := rfl
  have hks (n : ℕ) : k (n + 1) = ub (k n) (ub (a (n + 1)) (b (n + 1))) := rfl
  refine ⟨k, monotone_nat_of_le_succ fun n => ?_, fun n => ?_⟩
  · rw [hks]
    exact hub1 _ _
  · cases n with
    | zero => rw [hk0]; exact ⟨hub1 _ _, hub2 _ _⟩
    | succ n =>
      rw [hks]
      exact ⟨(hub1 _ _).trans (hub2 _ _), (hub2 _ _).trans (hub2 _ _)⟩

variable [IsIntegral X]

/-- **Reduction of `thm:BJappseq` to a selection.** Let `D` be a decreasing net of rational GF
functions whose numerical classes converge to that of `L` and which converges pointwise to `φ`.
If `D` converges to `φ` along some sequence of indices `j` (monotonicity of `j` is not needed),
then the conclusion of
`thm:BJappseq` holds for every ample `S`, with `ε_i = 1/(i+1)`: push `j` up so that the class of
the `i`-th term lies below `L + ε_i S` by an ample class, and promote the term into the exact
rational Picard class `L + ε_i S`. -/
theorem approximatingSequence_of_selection {S : X.Modules} (hS : SchemeLineAmpleness.IsAmple p S)
    (L : RationalPicardSpace X) {φ : BerkovichPoint p → EReal} (D : DecreasingGFNet.{u} p)
    (hclass : Tendsto (fun i => (D.term i).numericalClass p) atTop
      (@nhds _ (numericalModuleTopology p) (SGPT.NAPotential.BJ.NativePicard.numericalClass p L)))
    (hlim : ∀ v, Tendsto (fun i => (D.term i).eval p v) atTop (𝓝 (φ v)))
    (j : ℕ → D.I)
    (hjlim : ∀ v, Tendsto (fun n => (D.term (j n)).eval p v) atTop (𝓝 (φ v))) :
    ApproximatingSequence p hS.isInvertible L φ := by
  let s : RationalPicardSpace X := rationalPicardClass (atlasOfInvertible hS.isInvertible)
  let η := NativeRealNumericalClasses.lineClass p S hS.isInvertible
  have hη : η ∈ NativeRealNumericalClasses.ampleCone p :=
    NativeRealNumericalClasses.ampleLineClass_mem_ampleCone p S hS
  let target : ℕ → RationalPicardSpace X := fun n => L + coeff n • s
  have hTarget (n : ℕ) : SGPT.NAPotential.BJ.NativePicard.numericalClass p (target n) =
      SGPT.NAPotential.BJ.NativePicard.numericalClass p L + (coeff n : ℝ) • η := by
    change SGPT.NAPotential.BJ.NativePicard.numericalClass p (L + coeff n • s) = _
    rw [map_add, SGPT.NAPotential.BJ.NativePicard.numericalClass_rat_smul, SGPT.NAPotential.BJ.NativePicard.numericalClass_line,
      ← Rat.cast_smul_eq_qsmul ℝ]
  have hAmp (n : ℕ) : (coeff n : ℝ) • η ∈ NativeRealNumericalClasses.ampleCone p :=
    (NativeRealNumericalClasses.ampleCone p).smul_mem (by exact_mod_cast coeff_pos n) hη
  have hDamp := ampleTendsto_of_moduleTopology p hclass
  choose iN hiN using fun n => eventually_atTop.mp (hDamp.eventually_sub_mem (hAmp n))
  obtain ⟨k, hk, hkjN⟩ := exists_monotone_ge j iN
  have hkj (n : ℕ) : j n ≤ k n := (hkjN n).1
  have hkN (n : ℕ) : iN n ≤ k n := (hkjN n).2
  have hgap (n : ℕ) : SGPT.NAPotential.BJ.NativePicard.numericalClass p (target n) -
      (D.term (k n)).numericalClass p ∈ NativeRealNumericalClasses.ampleCone p := by
    rw [hTarget]
    exact hiN n (k n) (hkN n)
  choose E hEclass hEeval using fun n =>
    exists_package_picardClass_of_ample_gap p (D.term (k n)) (target n) (hgap n)
  have hφle (n : ℕ) (v : BerkovichPoint p) : φ v ≤ (D.term (k n)).eval p v := by
    rw [congrFun (D.eq_limit_of_tendsto p hlim) v]
    exact D.limit_le p (k n) v
  refine ⟨coeff, fun n => (E n).eval p, coeff_pos, coeff_strictAnti, tendsto_coeff,
    fun n => ⟨E n, hEclass n, rfl⟩, ?_, ?_⟩
  · intro v n m hnm
    change (E m).eval p v ≤ (E n).eval p v
    rw [hEeval n v, hEeval m v]
    exact D.decreasing v (hk hnm)
  · intro v
    have hval (n : ℕ) : (E n).eval p v = (D.term (k n)).eval p v := hEeval n v
    simp only [hval]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hjlim v)
      (fun n => hφle n v) (fun n => D.decreasing v (hkj n))

/-- **`thm:BJappseq` follows from countable selection** (`DecreasingNetSelection`, i.e.
Boucksom–Jonsson's Theorem 12.17 for the defining nets). -/
theorem bjAppSeq_of_selection (h : DecreasingNetSelection.{u} p) : BJAppSeqStatement.{u} p := by
  intro S hS L φ hφ
  obtain ⟨hne, D, hclass, hlim⟩ := hφ
  obtain ⟨j, -, hjlim⟩ := h L φ D hne hclass hlim
  exact approximatingSequence_of_selection p hS L D hclass hlim j hjlim

end SGPT.NAPotential.ThinApprox.BJ.AppSeq
