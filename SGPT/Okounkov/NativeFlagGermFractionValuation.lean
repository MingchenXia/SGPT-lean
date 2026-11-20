import SGPT.Okounkov.NativeFlagGermRange
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff nonZeroDivisors
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- Every actual fraction-field denominator has a finite value under the
genuine original local flag valuation. -/
theorem originalFlagGermFractionDenominators_nonvanishing {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F) :
    (NativeHolGerm n F.carrier x.1)⁰ ≤
      (originalFlagGermValuation F x).toValuation.supp.primeCompl := by
  intro f hf
  change originalFlagGermValuation F x f ≠ ⊤
  exact mt (originalFlagGermValuation_eq_top_iff F x f).mp (nonZeroDivisors.ne_zero hf)

/-- The actual valuation on the fraction field of the SAME original germ
ring. This is a local meromorphic-germ field, with no global K(X) assertion. -/
def originalFlagGermFractionValuation {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F) :
    AddValuation (FractionRing (NativeHolGerm n F.carrier x.1))
      (WithTop (Lex (Fin n → ℤ))) :=
  (originalFlagGermValuation F x).toValuation.extendToLocalization
    (originalFlagGermFractionDenominators_nonvanishing F x)
    (FractionRing (NativeHolGerm n F.carrier x.1))

/-- Whole restriction along the actual original germ-ring injection. -/
theorem originalFlagGermFractionValuation_algebraMap {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (f : NativeHolGerm n F.carrier x.1) :
    originalFlagGermFractionValuation F x
      (algebraMap (NativeHolGerm n F.carrier x.1)
        (FractionRing (NativeHolGerm n F.carrier x.1)) f) = originalFlagGermValuation F x f :=
  Valuation.extendToLocalization_apply_map_apply (originalFlagGermValuation F x).toValuation
    (originalFlagGermFractionDenominators_nonvanishing F x)
    (FractionRing (NativeHolGerm n F.carrier x.1)) f

/-- The exact value of an actual original fraction is the difference of
the WHOLE internally manufactured original flag tuples. -/
theorem originalFlagGermFractionValuation_div {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (f g : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0) (hg : g ≠ 0) :
    originalFlagGermFractionValuation F x
      (algebraMap _ (FractionRing (NativeHolGerm n F.carrier x.1)) f /
        algebraMap _ (FractionRing (NativeHolGerm n F.carrier x.1)) g) =
      ((originalFlagGermLexVector F x f hf - originalFlagGermLexVector F x g hg :
        Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
  rw [(originalFlagGermFractionValuation F x).map_div,
    originalFlagGermFractionValuation_algebraMap, originalFlagGermFractionValuation_algebraMap,
    originalFlagGermValuation_apply_of_ne_zero F x f hf,
    originalFlagGermValuation_apply_of_ne_zero F x g hg]
  rfl

theorem originalFlagGermFractionValuation_eq_top_iff {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (f : FractionRing (NativeHolGerm n F.carrier x.1)) :
    originalFlagGermFractionValuation F x f = ⊤ ↔ f = 0 :=
  (originalFlagGermFractionValuation F x).top_iff

/-- Actual original germs attaining the positive and negative natural
parts manufacture a NONZERO fraction attaining any entire integer tuple. -/
theorem originalFlagGermFractionValuation_integer_surjective {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F) (b : Lex (Fin n → ℤ)) :
    ∃ q : FractionRing (NativeHolGerm n F.carrier x.1),
      q ≠ 0 ∧ originalFlagGermFractionValuation F x q =
        (b : WithTop (Lex (Fin n → ℤ))) := by
  obtain ⟨f, hf, hpos⟩ := originalFlagGermVector_nat_surjective F x (fun i => (ofLex b i).toNat)
  obtain ⟨g, hg, hneg⟩ := originalFlagGermVector_nat_surjective F x (fun i => (-ofLex b i).toNat)
  have hdiff : originalFlagGermLexVector F x f hf - originalFlagGermLexVector F x g hg = b := by
    change (fun i => (originalFlagGermVector F x f hf i : ℤ)) -
      (fun i => (originalFlagGermVector F x g hg i : ℤ)) = ofLex b
    rw [hpos, hneg]
    funext i
    change ((ofLex b i).toNat : ℤ) - ((-ofLex b i).toNat : ℤ) = ofLex b i
    omega
  let K := FractionRing (NativeHolGerm n F.carrier x.1)
  have hfK : algebraMap (NativeHolGerm n F.carrier x.1) K f ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hf
  have hgK : algebraMap (NativeHolGerm n F.carrier x.1) K g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hg
  refine ⟨algebraMap _ K f / algebraMap _ K g, div_ne_zero hfK hgK, ?_⟩
  rw [originalFlagGermFractionValuation_div F x f g hf hg, hdiff]

end SGPT.Okounkov
