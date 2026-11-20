import SGPT.Foundations.Schemes.LineBundleSectionRing
import SGPT.Foundations.Schemes.SchemeGenericSections
import SGPT.Foundations.Schemes.NativeProjectiveGlobalSectionsFiniteness
import Mathlib.Algebra.DirectSum.Algebra

/-!
# The section ring of a line bundle as a graded `ℂ`-algebra

Source: the section ring `R(X, L) = ⊕_{k ≥ 0} H⁰(X, L^k)` of the definition
`def:testcurve:L1134` (chapter *Test curves*), also used for the section semigroups of the
chapter *The theory of Okounkov bodies*.

## Setting

`X` is a scheme over `ℂ` with structure morphism `f : X ⟶ Spec ℂ`, and `L : X.Modules` is a
line bundle with a rank-one atlas `a` (the setting of the existing scheme-side line-bundle
library `SGPT.Foundations.Schemes`). The `k`-th tensor power `L^k` is `bundleTensorPower L k` and its
global sections `H⁰(X, L^k)` are `bundlePowerGlobalSections L k`; the existing section product
`atlasPowerGlobalMul a` glues the products of the chart coefficients.

## Main definitions

* `SGPT.LineBundle.SectionSpace f L k`: the complex vector space `H⁰(X, L^k)`, the scalars
  acting through the structure morphism `f`.
* `SGPT.LineBundle.SectionSpace.mul a`: the multiplication
  `H⁰(X, L^m) × H⁰(X, L^k) → H⁰(X, L^{m+k})`, as a `ℂ`-bilinear map.
* `SGPT.LineBundle.sectionGCommRing a`, `SGPT.LineBundle.sectionGAlgebra a`: the graded
  commutative ring and graded `ℂ`-algebra structures on the family `k ↦ H⁰(X, L^k)`, so that
  `⨁ k, H⁰(X, L^k)` is a commutative `ℂ`-algebra (Mathlib's `DirectSum.instAlgebra`).

## Main results

* `SectionSpace.mul_atlas_independent`: the product does not depend on the atlas.
* `SectionSpace.mul_ne_zero`: on an integral scheme the product of nonzero sections is nonzero.
* `SectionSpace.mul_assoc'`, `SectionSpace.mul_comm'`, `SectionSpace.one_mul'`: the graded
  ring laws in degree-indexed form.
* `sectionRing_algebraMap_eq`: the algebra map of the graded algebra is the existing
  base-field map of the section ring `IntrinsicLineBundle.sectionRing`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.LineBundle

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- The complex vector space `H⁰(X, L^k)` of global sections of the `k`-th tensor power of `L`.
The underlying type is the existing section type `bundlePowerGlobalSections L k`; complex
scalars act through the constants of the structure morphism `f`. -/
def SectionSpace (_f : X ⟶ Spec (.of ℂ)) (L : X.Modules) (k : ℕ) : Type :=
  bundlePowerGlobalSections L k

namespace SectionSpace

variable {L : X.Modules}

instance (k : ℕ) : AddCommGroup (SectionSpace f L k) :=
  inferInstanceAs (AddCommGroup (bundlePowerGlobalSections L k))

instance (k : ℕ) : Module ℂ (SectionSpace f L k) :=
  schemeGlobalSectionModule f (bundleTensorPower L k)

/-- The identification of `SectionSpace f L k` with the existing section type, as a linear
equivalence for the scalar action of the structure morphism. -/
def equivSections (k : ℕ) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L k)
    SectionSpace f L k ≃ₗ[ℂ] bundlePowerGlobalSections L k :=
  letI := schemeGlobalSectionModule f (bundleTensorPower L k)
  LinearEquiv.refl ℂ (bundlePowerGlobalSections L k)

/-- Complex scalars act through the constant regular functions of the structure morphism. -/
theorem smul_def (k : ℕ) (c : ℂ) (s : SectionSpace f L k) :
    c • s = (show SectionSpace f L k from
      schemeGlobalConstants f c • (show bundlePowerGlobalSections L k from s)) := rfl

/-- On a projective scheme every `H⁰(X, L^k)` is finite dimensional. -/
theorem finiteDimensional (E : ClosedProjectiveEmbedding f) (a : LineBundleAtlas L) (k : ℕ) :
    FiniteDimensional ℂ (SectionSpace f L k) :=
  E.powerGlobalSections_finite a k

/-- The chart coefficients of `c • s` are the products of the constant `c` with those of `s`. -/
theorem atlasPowerGlobalCoefficients_smul_const (a : LineBundleAtlas L) (k : ℕ) (i : a.I)
    (c : ℂ) (s : SectionSpace f L k) :
    atlasPowerGlobalCoefficients a k i (c • s : SectionSpace f L k) =
      X.sheaf.obj.map (homOfLE le_top).op (schemeGlobalConstants f c) *
        atlasPowerGlobalCoefficients a k i s :=
  SGPT.Foundations.Schemes.atlasPowerGlobalCoefficients_smul a k i (schemeGlobalConstants f c) s

/-- The section product `H⁰(X, L^m) × H⁰(X, L^k) → H⁰(X, L^{m+k})`, `(s, t) ↦ s ⊗ t`, as a
`ℂ`-bilinear map (constructed by gluing the products of chart coefficients). -/
def mul (a : LineBundleAtlas L) (m k : ℕ) :
    SectionSpace f L m →ₗ[ℂ] SectionSpace f L k →ₗ[ℂ] SectionSpace f L (m + k) :=
  LinearMap.mk₂ ℂ (fun s t => atlasPowerGlobalMul a m k s t)
    (fun s s' t => atlasPowerGlobalMul_add_left a m k s s' t)
    (fun c s t => by
      apply atlasPowerGlobalCoefficients_ext a (m + k)
      intro i
      change atlasPowerGlobalCoefficients a (m + k) i (atlasPowerGlobalMul a m k (c • s) t) =
        atlasPowerGlobalCoefficients a (m + k) i
          (c • (show SectionSpace f L (m + k) from atlasPowerGlobalMul a m k s t))
      rw [atlasPowerGlobalCoefficients_smul_const, atlasPowerGlobalMul_coefficients,
        atlasPowerGlobalMul_coefficients, atlasPowerGlobalCoefficients_smul_const, mul_assoc])
    (fun s t t' => atlasPowerGlobalMul_add_right a m k s t t')
    (fun c s t => by
      apply atlasPowerGlobalCoefficients_ext a (m + k)
      intro i
      change atlasPowerGlobalCoefficients a (m + k) i (atlasPowerGlobalMul a m k s (c • t)) =
        atlasPowerGlobalCoefficients a (m + k) i
          (c • (show SectionSpace f L (m + k) from atlasPowerGlobalMul a m k s t))
      rw [atlasPowerGlobalCoefficients_smul_const, atlasPowerGlobalMul_coefficients,
        atlasPowerGlobalMul_coefficients, atlasPowerGlobalCoefficients_smul_const]
      ring)

theorem mul_apply (a : LineBundleAtlas L) (m k : ℕ) (s : SectionSpace f L m)
    (t : SectionSpace f L k) : mul f a m k s t = atlasPowerGlobalMul a m k s t := rfl

/-- The chart coefficients of a product are the products of the chart coefficients. -/
theorem coefficients_mul (a : LineBundleAtlas L) (m k : ℕ) (i : a.I) (s : SectionSpace f L m)
    (t : SectionSpace f L k) :
    atlasPowerGlobalCoefficients a (m + k) i (mul f a m k s t) =
      atlasPowerGlobalCoefficients a m i s * atlasPowerGlobalCoefficients a k i t :=
  atlasPowerGlobalMul_coefficients a m k s t i

/-- The section product does not depend on the atlas used to construct it. -/
theorem mul_atlas_independent (a b : LineBundleAtlas L) (m k : ℕ) :
    mul f a m k = mul f b m k := by
  ext s t
  change atlasPowerGlobalMul a m k s t = atlasPowerGlobalMul b m k s t
  apply atlasPowerGlobalCoefficients_ext b (m + k)
  intro j
  rw [atlasPowerGlobalMul_coefficients]
  apply TopCat.Presheaf.IsSheaf.section_ext X.sheaf.property
  intro x hx
  obtain ⟨i, hi⟩ := a.covers x
  refine ⟨a.opens i ⊓ b.opens j, inf_le_right, ⟨hi, hx⟩, ?_⟩
  let l : a.opens i ⊓ b.opens j ⟶ a.opens i := homOfLE inf_le_left
  let r : a.opens i ⊓ b.opens j ⟶ b.opens j := homOfLE inf_le_right
  let u : X.sheaf.obj.obj (op (a.opens i ⊓ b.opens j)) :=
    localBundleFrameTransition (a.frame i) (b.frame j) l r
  have htr (d : ℕ) (v : bundlePowerGlobalSections L d) :
      X.sheaf.obj.map r.op (atlasPowerGlobalCoefficients b d j v) =
        u ^ d * X.sheaf.obj.map l.op (atlasPowerGlobalCoefficients a d i v) :=
    LocalBundleFrame.global_coefficients_transition (a.frame i) (b.frame j) l r d v
  change X.sheaf.obj.map r.op
      (atlasPowerGlobalCoefficients b (m + k) j (atlasPowerGlobalMul a m k s t)) =
    X.sheaf.obj.map r.op
      (atlasPowerGlobalCoefficients b m j s * atlasPowerGlobalCoefficients b k j t)
  rw [htr, atlasPowerGlobalMul_coefficients, map_mul, map_mul, htr, htr, pow_add]
  ring

variable [IsIntegral X]

/-- Generic evaluation of a section of `L^d` in the `d`-th power of the generic frame. -/
private def genericValue (a : LineBundleAtlas L) (d : ℕ) (s : SectionSpace f L d) :
    X.functionField :=
  letI : Nonempty (a.opens a.genericIndex) := a.genericOpenNonempty
  globalSectionToFunctionField ((a.frame a.genericIndex).tensorPower d) s

private theorem genericValue_eq (a : LineBundleAtlas L) (d : ℕ) (s : SectionSpace f L d) :
    genericValue f a d s =
      X.germToFunctionField (a.opens a.genericIndex)
        (atlasPowerGlobalCoefficients a d a.genericIndex s) := rfl

private theorem genericValue_injective (a : LineBundleAtlas L) (d : ℕ) :
    Function.Injective (genericValue f a d) := by
  let : Nonempty (a.opens a.genericIndex) := a.genericOpenNonempty
  exact globalSectionToFunctionField_injective (a.tensorPower d)
    ((a.frame a.genericIndex).tensorPower d)

private theorem genericValue_zero (a : LineBundleAtlas L) (d : ℕ) :
    genericValue f a d 0 = 0 := by
  unfold genericValue
  exact map_zero _

/-- On an integral scheme the product of two nonzero sections is nonzero (the function field
has no zero divisors). -/
theorem mul_ne_zero (a : LineBundleAtlas L) {m k : ℕ} {s : SectionSpace f L m}
    {t : SectionSpace f L k} (hs : s ≠ 0) (ht : t ≠ 0) : mul f a m k s t ≠ 0 := by
  intro h
  have h0 : genericValue f a (m + k) (mul f a m k s t) = 0 := by
    rw [h]
    exact genericValue_zero f a _
  rw [genericValue_eq, coefficients_mul, map_mul] at h0
  rcases _root_.mul_eq_zero.mp h0 with h1 | h1
  · apply hs
    apply genericValue_injective f a m
    show genericValue f a m s = genericValue f a m 0
    rw [genericValue_zero, genericValue_eq, h1]
  · apply ht
    apply genericValue_injective f a k
    show genericValue f a k t = genericValue f a k 0
    rw [genericValue_zero, genericValue_eq, h1]

end SectionSpace

section Graded

variable {L : X.Modules}

/-- The graded commutative ring structure on `k ↦ H⁰(X, L^k)` (the existing coherence laws of
the section product). -/
@[instance_reducible]
def sectionGCommRing (a : LineBundleAtlas L) : DirectSum.GCommRing (SectionSpace f L) :=
  atlasPowerGradedCommRing a

/-- The graded `ℂ`-algebra structure: degree-zero sections are the constants, and multiplying
by a constant is the scalar action. -/
@[instance_reducible]
def sectionGAlgebra (a : LineBundleAtlas L) :
    letI := sectionGCommRing f a
    DirectSum.GAlgebra ℂ (SectionSpace f L) := by
  letI := sectionGCommRing f a
  exact {
    toFun := (schemeGlobalConstants f).toAddMonoidHom
    map_one := (schemeGlobalConstants f).map_one
    map_mul := fun r q => by
      refine Sigma.ext rfl (heq_of_eq ?_)
      change schemeGlobalConstants f (r * q) =
        atlasPowerGlobalMul a 0 0 (schemeGlobalConstants f r) (schemeGlobalConstants f q)
      rw [atlasPowerGlobalMul_degree_zero, map_mul]
    commutes := fun r x => mul_comm _ _
    smul_def := fun r x => by
      obtain ⟨k, s⟩ := x
      exact Sigma.ext (Nat.zero_add k).symm
        (atlasPowerGlobalMul_regular_scalar a k (schemeGlobalConstants f r) s).symm }

/-- The product of the graded ring is the section product. -/
theorem sectionGCommRing_mul (a : LineBundleAtlas L) {m k : ℕ} (s : SectionSpace f L m)
    (t : SectionSpace f L k) :
    letI := sectionGCommRing f a
    GradedMonoid.GMul.mul s t = SectionSpace.mul f a m k s t := rfl

/-- In the commutative `ℂ`-algebra `⨁ k, H⁰(X, L^k)` of the graded structure, the product of
homogeneous elements is the section product. -/
theorem sectionRing_of_mul_of (a : LineBundleAtlas L) {m k : ℕ} (s : SectionSpace f L m)
    (t : SectionSpace f L k) :
    letI := sectionGCommRing f a
    DirectSum.of (SectionSpace f L) m s * DirectSum.of (SectionSpace f L) k t =
      DirectSum.of (SectionSpace f L) (m + k) (SectionSpace.mul f a m k s t) := by
  let := sectionGCommRing f a
  exact DirectSum.of_mul_of s t

/-- The algebra map `ℂ → ⨁ k, H⁰(X, L^k)` of the graded `ℂ`-algebra is the existing base-field
map of the section ring `IntrinsicLineBundle.sectionRing` (constants in degree zero). -/
theorem sectionRing_algebraMap_eq (L : IntrinsicLineBundle X) (c : ℂ) :
    letI := sectionGCommRing f L.atlas
    letI := sectionGAlgebra f L.atlas
    (algebraMap ℂ (DirectSum (ℕ) (SectionSpace f L.sheaf)) c : L.sectionRing) =
      L.sectionRingBaseMap f c := rfl

/-- The scalar action of `ℂ` on `⨁ k, H⁰(X, L^k)` (componentwise) is multiplication by the
algebra map: `⨁ k, H⁰(X, L^k)` is a graded `ℂ`-algebra. -/
theorem sectionRing_smul_eq_mul (a : LineBundleAtlas L) (c : ℂ)
    (x : DirectSum ℕ (SectionSpace f L)) :
    letI := sectionGCommRing f a
    letI := sectionGAlgebra f a
    c • x = algebraMap ℂ (DirectSum ℕ (SectionSpace f L)) c * x := by
  let := sectionGCommRing f a
  let := sectionGAlgebra f a
  exact Algebra.smul_def c x

end Graded

namespace SectionSpace

variable {L : X.Modules}

/-- Associativity of the section product, in degree-indexed form. -/
theorem mul_assoc' (a : LineBundleAtlas L) (m k l : ℕ) (s : SectionSpace f L m)
    (t : SectionSpace f L k) (u : SectionSpace f L l) :
    HEq (mul f a (m + k) l (mul f a m k s t) u) (mul f a m (k + l) s (mul f a k l t u)) :=
  atlasPowerGlobalMul_assoc a m k l s t u

/-- Commutativity of the section product, in degree-indexed form. -/
theorem mul_comm' (a : LineBundleAtlas L) (m k : ℕ) (s : SectionSpace f L m)
    (t : SectionSpace f L k) : HEq (mul f a m k s t) (mul f a k m t s) :=
  atlasPowerGlobalMul_comm a m k s t

/-- The constant section `1 ∈ H⁰(X, L⁰)` is a unit for the section product. -/
theorem one_mul' (a : LineBundleAtlas L) (k : ℕ) (s : SectionSpace f L k) :
    HEq (mul f a 0 k (bundlePowerGlobalOne L) s) s :=
  atlasPowerGlobalMul_one_left a k s

/-- Multiplying by a degree-zero constant is the scalar action. -/
theorem const_mul (a : LineBundleAtlas L) (k : ℕ) (c : ℂ) (s : SectionSpace f L k) :
    HEq (mul f a 0 k (schemeGlobalConstants f c) s) (c • s) :=
  atlasPowerGlobalMul_regular_scalar a k (schemeGlobalConstants f c) s

end SectionSpace

end SGPT.LineBundle
