import SGPT.Foundations.PublishedEnvelope.Global.Model
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The actual model field embeds into its native Gauss fraction field

The cached model-generation theorem supplies the fraction-field structure
of S inside K(T). The genuine constant-polynomial inclusion S -> S[t]
then extends to that SAME field. Restricting its coefficient algebra gives
the actual embedding K -> Frac(S[t]), with no equivalence assumed.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial

namespace SGPT.NAPotential.BJ.Divisorial.Native
open SGPT.Foundations.PublishedEnvelope

universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {r : ℕ}
  (M : MultiModel k K r)

/-- The literal original section algebra inside the native Gauss field. -/
def gaussBase : M.S →ₐ[k] FractionRing (Polynomial M.S) :=
  (IsScalarTower.toAlgHom k (Polynomial M.S) (FractionRing (Polynomial M.S))).comp
    (Polynomial.CAlgHom : M.S →ₐ[k] Polynomial M.S)

/-- Injectivity is derived from the actual polynomial and fraction maps. -/
theorem gaussBase_injective : Function.Injective (gaussBase M) :=
  (IsFractionRing.injective (Polynomial M.S) (FractionRing (Polynomial M.S))).comp
    Polynomial.C_injective

/-- The ACTUAL ambient model field K(T) embeds into the native Gauss field,
using the fully proved model-generation fraction-field theorem. -/
def ambientToGauss : FractionRing (MvPolynomial (Fin r) K) →ₐ[k]
    FractionRing (Polynomial M.S) := by
  let := M.isFractionRing_S
  exact IsFractionRing.liftAlgHom (g := gaussBase M) (gaussBase_injective M)

/-- The entire original coefficient field is mapped by the same actual
fraction-field embedding, rather than by an arbitrary field identification. -/
def modelFieldToGauss : K →ₐ[k] FractionRing (Polynomial M.S) :=
  (ambientToGauss M).comp
    (IsScalarTower.toAlgHom k K (FractionRing (MvPolynomial (Fin r) K)))

/-- The actual coefficient embedding is injective because its source is a field. -/
theorem modelFieldToGauss_injective : Function.Injective (modelFieldToGauss M) :=
  (modelFieldToGauss M).injective

/-- The extension retains every actual original section coefficient. -/
theorem ambientToGauss_coefficient (s : M.S) :
    ambientToGauss M (algebraMap M.S (FractionRing (MvPolynomial (Fin r) K)) s) =
      gaussBase M s := by
  let := M.isFractionRing_S
  exact IsFractionRing.lift_algebraMap (gaussBase_injective M) s

/-- Every same-degree homogeneous fraction retains its literal section
numerator and denominator inside the actual Gauss fraction field. Zero
numerators and zero denominators are both included. -/
theorem modelFieldToGauss_homogeneous_ratio {a : Fin r →₀ ℕ} {f g : K}
    (hf : f ∈ M.piece a) (hg : g ∈ M.piece a) :
    modelFieldToGauss M (f / g) = gaussBase M (M.ofPiece hf) / gaussBase M (M.ofPiece hg) := by
  let L := FractionRing (MvPolynomial (Fin r) K)
  let ι : MvPolynomial (Fin r) K →+* L := algebraMap (MvPolynomial (Fin r) K) L
  have hm (h : K) : ι (monomial a h) = ι (C h) * ι (monomial a 1) := by
    rw [← map_mul, C_mul_monomial, mul_one]
  have hm0 : ι (monomial a (1 : K)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin r) K) L)).mpr (by simp)
  have he : algebraMap K L (f / g) =
      algebraMap M.S L (M.ofPiece hf) / algebraMap M.S L (M.ofPiece hg) := by
    change ι (C (f / g)) = ι (monomial a f) / ι (monomial a g)
    rw [hm f, hm g, mul_div_mul_right _ _ hm0]
    exact map_div₀ (ι.comp C) f g
  change ambientToGauss M (algebraMap K L (f / g)) = _
  rw [he, map_div₀, ambientToGauss_coefficient, ambientToGauss_coefficient]

end SGPT.NAPotential.BJ.Divisorial.Native
