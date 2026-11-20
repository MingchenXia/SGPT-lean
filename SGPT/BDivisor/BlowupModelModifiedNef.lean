import SGPT.BDivisor.BlowupModelVolume
import SGPT.BDivisor.Modification3AugmentedNef

/-!
# Classes of nef b-divisors over the book's models are modified nef; augmented nef b-divisors

Source: `cor:mn_level_nefb`, implication (1) ⇒ (2): if `𝔻` is a nef b-divisor over `X`, then for
each modification `π : Y → X` the class `𝔻_Y` is modified nef (`def:mnclass`); and
`def:augmented_nefb` (augmented nef b-divisors `(𝔻, D)`).

The proof is the book's: a nef b-divisor is a limit of nef Cartier b-divisors, modified nefness is
a closed condition (`SGPT.Siu.classModifiedNef_of_tendsto`, which uses that `H^{1,1}(Y, ℝ)` is
finite-dimensional), and for a nef Cartier b-divisor realized by a nef class `α` on `Y₀` the class
on `Y` is `h_* g^* α` for a common dominating model `Y'`, which is modified nef by the push-forward
criterion `SGPT.Siu.classModifiedNefWithRespectTo_classPushforward_of_forall` (`prop:cones_modif`,
item 2).

On the book's models of a connected compact Kähler `X` every model is Kähler, so statement (2) is
formalized for **every** model and **every** Kähler form on it (modified nefness does not depend
on the Kähler form, `SGPT.Siu.classModifiedNefWithRespectTo_iff`).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame

namespace WeilBDivisorOn

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] {S : ModelSystem (m + 1) X} {hn : 0 < m + 1}

/-- **The classes of a nef Cartier b-divisor are modified nef** on every model of the system
carrying a Kähler form. -/
theorem IsNefCartier.classModifiedNef {𝔻 : WeilBDivisorOn S hn} (h𝔻 : 𝔻.IsNefCartier)
    (π : S.Model) (ωY : KahlerBackground (m + 1) π.1.carrier) :
    Siu.ClassModifiedNefWithRespectTo ωY (𝔻.onModel π) := by
  obtain ⟨π₀, α, hr, κ, hα⟩ := h𝔻
  obtain ⟨π', h₁, h₂⟩ := ModelSystem.Model.exists_le_le π π₀
  rw [← 𝔻.pushforward_onModel h₁, hr π' h₂]
  induction α using Quotient.inductionOn with
  | h θ =>
  change NefWithRespectTo κ θ at hα
  change Siu.ClassModifiedNefWithRespectTo ωY
    (classPushforward (Modification.contMDiff_homOfLE (show π.1 ≤ π'.1 from h₁))
      (canonicalBasis (m + 1)) hn
      (classPullback (Modification.contMDiff_homOfLE (show π₀.1 ≤ π'.1 from h₂))
        (RealBottChern.ofRepresentative θ)))
  rw [classPullback_ofRepresentative]
  exact Siu.classModifiedNefWithRespectTo_classPushforward_of_forall
    (Modification.Dominates.isAnalyticModification (show π.1 ≤ π'.1 from h₁)) ωY _ _
    (fun ε hε => Siu.exists_pullback_nef_potential
      (Modification.contMDiff_homOfLE (show π₀.1 ≤ π'.1 from h₂)) κ hα ε hε)

/-- **`cor:mn_level_nefb`, (1) ⇒ (2), over a model system**: the class of a nef b-divisor on a
model carrying a Kähler form is modified nef, provided `H^{1,1}` of the model is
finite-dimensional. -/
theorem IsNef.classModifiedNef {𝔻 : WeilBDivisorOn S hn} (h𝔻 : 𝔻.IsNef) (π : S.Model)
    [FiniteDimensional ℝ (RealBottChern (m + 1) π.1.carrier)]
    (ωY : KahlerBackground (m + 1) π.1.carrier) :
    Siu.ClassModifiedNefWithRespectTo ωY (𝔻.onModel π) := by
  obtain ⟨ι, _, _, _, D, hD, hconv⟩ := h𝔻
  exact Siu.classModifiedNef_of_tendsto ωY (fun i => (hD i).classModifiedNef π ωY) (hconv π)

/-- **`cor:mn_level_nefb`, (1) ⇒ (2), for nef Cartier b-divisors over the book's models**: for
`X` compact Kähler and a nef Cartier b-divisor `𝔻`, the class `𝔻_Y` on **every** blow-up model
`Y` is modified nef with respect to every Kähler form of `Y` (and `Y` carries one). -/
theorem IsNefCartier.classModifiedNef_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    {𝔻 : BlowupWeilBDivisor (m + 1) X hn} (h𝔻 : 𝔻.IsNefCartier)
    (π : (ModelSystem.blowup (m + 1) X).Model) :
    Nonempty (KahlerBackground (m + 1) π.1.carrier) ∧
      ∀ ωY : KahlerBackground (m + 1) π.1.carrier,
        Siu.ClassModifiedNefWithRespectTo ωY (𝔻.onModel π) :=
  ⟨ModelSystem.blowup_nonempty_kahlerBackground hK π, fun ωY => h𝔻.classModifiedNef π ωY⟩

/-- **`cor:mn_level_nefb`, (1) ⇒ (2), over the book's models**: for `X` compact Kähler and a nef
b-divisor `𝔻` (`def:nefb`), the class `𝔻_Y` on every blow-up model `Y` is modified nef with
respect to every Kähler form of `Y` (and `Y` carries one), provided `H^{1,1}(Y, ℝ)` is
finite-dimensional (Hodge theory, not formalized). -/
theorem IsNef.classModifiedNef_blowup (hK : Nonempty (KahlerBackground (m + 1) X))
    {𝔻 : BlowupWeilBDivisor (m + 1) X hn} (h𝔻 : 𝔻.IsNef)
    (π : (ModelSystem.blowup (m + 1) X).Model)
    [FiniteDimensional ℝ (RealBottChern (m + 1) π.1.carrier)] :
    Nonempty (KahlerBackground (m + 1) π.1.carrier) ∧
      ∀ ωY : KahlerBackground (m + 1) π.1.carrier,
        Siu.ClassModifiedNefWithRespectTo ωY (𝔻.onModel π) :=
  ⟨ModelSystem.blowup_nonempty_kahlerBackground hK π, fun ωY => h𝔻.classModifiedNef π ωY⟩

end WeilBDivisorOn

variable (m : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- **Augmented nef b-divisors** (`def:augmented_nefb`) over the book's models: a nef b-divisor `𝔻`
over the blow-up models of `X` together with a formal sum `D = ∑_E c_E E` over the prime divisors
of `X` with `c_E ≥ 0`, such that `∑_E c_E {E}` converges in `H^{1,1}(X, ℝ)`. -/
structure BlowupAugmentedNefBDivisor (hn : 0 < m + 1) where
  /-- The nef b-divisor `𝔻`. -/
  bdiv : BlowupWeilBDivisor (m + 1) X hn
  isNef : bdiv.IsNef
  /-- The coefficients `c_E` of the formal sum `D = ∑_E c_E E`. -/
  coeff : SGPT.PSH.GeometricPrimeCarrier (m + 1) X → ℝ
  coeff_nonneg : ∀ E, 0 ≤ coeff E
  /-- `∑_E c_E {E}` converges in `H^{1,1}(X, ℝ)`. -/
  summable : ∃ α, HasDivisorClassSum coeff α

namespace BlowupAugmentedNefBDivisor

variable {m X} {hn : 0 < m + 1}

/-- The sum `∑_E c_E {E} ∈ H^{1,1}(X, ℝ)`. -/
def divisorClass (A : BlowupAugmentedNefBDivisor m X hn) : RealBottChern (m + 1) X :=
  Classical.choose A.summable

theorem hasDivisorClassSum_divisorClass (A : BlowupAugmentedNefBDivisor m X hn) :
    HasDivisorClassSum A.coeff A.divisorClass :=
  Classical.choose_spec A.summable

/-- The sum is well defined (the Euclidean topology is Hausdorff). -/
theorem divisorClass_eq (A : BlowupAugmentedNefBDivisor m X hn) {α : RealBottChern (m + 1) X}
    (hα : HasDivisorClassSum A.coeff α) : A.divisorClass = α :=
  A.hasDivisorClassSum_divisorClass.unique hα

/-- The **cohomology class** `𝔻_X + ∑_E c_E {E}`. -/
def cohomologyClass (A : BlowupAugmentedNefBDivisor m X hn) : RealBottChern (m + 1) X :=
  A.bdiv.root + A.divisorClass

/-- The **volume** `vol (𝔻, D) = vol 𝔻`. -/
def vol [ConnectedSpace X] (A : BlowupAugmentedNefBDivisor m X hn) : ℝ≥0∞ :=
  A.bdiv.vol

end BlowupAugmentedNefBDivisor

end SGPT.BDivisor
