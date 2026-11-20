import SGPT.BDivisor.Modification3MnLevelNef
import SGPT.BDivisor.VolumeBDivisor
import SGPT.Siu.BookCurrentSiu

/-!
# Augmented nef b-divisors (`def:augmented_nefb`)

Source `def:augmented_nefb` (chapter *The theory of b-divisors*): an **augmented nef b-divisor**
over `X` is a pair `(𝔻, D)` of a nef b-divisor `𝔻` and a formal sum `D = ∑_E c_E E` over the prime
divisors `E` of `X` with `c_E ≥ 0`, such that `∑_E c_E {E}` converges in `H^{1,1}(X, ℝ)`. Its
cohomology class is `𝔻_X + ∑_E c_E {E}` and its volume is `vol 𝔻`.

* `SGPT.BDivisor.t2Space_euclideanTopology`: the Euclidean topology of a real vector space
  (`SGPT.BDivisor.euclideanTopology`, the coarsest topology making all linear functionals
  continuous) is Hausdorff, so sums in `H^{1,1}(X, ℝ)` are unique;
* `SGPT.BDivisor.primeDivisorClass`: the class `{E}` of a prime divisor (the class of the current
  of integration `[E]`, `SGPT.Siu.primeDivisorBookCurrent`);
* `SGPT.BDivisor.HasDivisorClassSum`: `∑_E c_E {E} = α` (unconditional convergence in the
  Euclidean topology, over all prime divisors of `X`);
* `SGPT.BDivisor.AugmentedNefBDivisor`, with `cohomologyClass` and `vol`.

The nefness of `𝔻` is `SGPT.BDivisor.WeilBDivisor.IsNef` (`def:nefb`), with its conventions: models
are all proper bimeromorphic maps from complex manifolds, and the Euclidean topology is described
intrinsically (it is the usual one when `H^{1,1}` is finite-dimensional).
-/

set_option autoImplicit false

noncomputable section

universe u

open Set Filter
open scoped Topology ENNReal

namespace SGPT.BDivisor

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- **The Euclidean topology of a real vector space is Hausdorff**: linear functionals separate
points. -/
theorem t2Space_euclideanTopology (V : Type*) [AddCommGroup V] [Module ℝ V] :
    @T2Space V (euclideanTopology V) := by
  let := euclideanTopology V
  have hc : Continuous (fun v : V => fun f : Module.Dual ℝ V => f v) :=
    continuous_pi fun f => continuous_euclideanTopology f
  refine T2Space.of_injective_continuous ?_ hc
  intro v w h
  apply Module.eval_apply_injective ℝ (V := V)
  ext f
  exact congrFun h f

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X]

/-- The class `{E} ∈ H^{1,1}(X, ℝ)` of a prime divisor `E`: the class of its current of
integration `[E]`. -/
def primeDivisorClass (E : SGPT.PSH.GeometricPrimeCarrier (m + 1) X) : RealBottChern (m + 1) X :=
  SGPT.PSH.BookCurrent.currentClass (SGPT.Siu.primeDivisorBookCurrent E)

/-- `∑_E c_E {E} = α`: the series of classes over all prime divisors of `X` converges
(unconditionally) to `α` in the Euclidean topology of `H^{1,1}(X, ℝ)`. -/
def HasDivisorClassSum (c : SGPT.PSH.GeometricPrimeCarrier (m + 1) X → ℝ)
    (α : RealBottChern (m + 1) X) : Prop :=
  letI := euclideanTopology (RealBottChern (m + 1) X)
  HasSum (fun E => c E • primeDivisorClass E) α

/-- The sum of a convergent series of divisor classes is unique. -/
theorem HasDivisorClassSum.unique
    {c : SGPT.PSH.GeometricPrimeCarrier (m + 1) X → ℝ} {α β : RealBottChern (m + 1) X}
    (hα : HasDivisorClassSum c α) (hβ : HasDivisorClassSum c β) : α = β := by
  let := euclideanTopology (RealBottChern (m + 1) X)
  have := t2Space_euclideanTopology (RealBottChern (m + 1) X)
  exact HasSum.unique hα hβ

variable (m X) in
/-- **Augmented nef b-divisors** (`def:augmented_nefb`): a nef b-divisor `𝔻` over `X` together
with a formal sum `D = ∑_E c_E E` over the prime divisors of `X` with `c_E ≥ 0`, such that
`∑_E c_E {E}` converges in `H^{1,1}(X, ℝ)`. -/
structure AugmentedNefBDivisor (hn : 0 < m + 1) where
  /-- The nef b-divisor `𝔻`. -/
  bdiv : WeilBDivisor (m + 1) X hn
  isNef : bdiv.IsNef
  /-- The coefficients `c_E` of the formal sum `D = ∑_E c_E E`. -/
  coeff : SGPT.PSH.GeometricPrimeCarrier (m + 1) X → ℝ
  coeff_nonneg : ∀ E, 0 ≤ coeff E
  /-- `∑_E c_E {E}` converges in `H^{1,1}(X, ℝ)`. -/
  summable : ∃ α, HasDivisorClassSum coeff α

namespace AugmentedNefBDivisor

variable {hn : 0 < m + 1}

/-- The sum `∑_E c_E {E} ∈ H^{1,1}(X, ℝ)`. -/
def divisorClass (A : AugmentedNefBDivisor m X hn) : RealBottChern (m + 1) X :=
  Classical.choose A.summable

theorem hasDivisorClassSum_divisorClass (A : AugmentedNefBDivisor m X hn) :
    HasDivisorClassSum A.coeff A.divisorClass :=
  Classical.choose_spec A.summable

theorem divisorClass_eq (A : AugmentedNefBDivisor m X hn) {α : RealBottChern (m + 1) X}
    (hα : HasDivisorClassSum A.coeff α) : A.divisorClass = α :=
  A.hasDivisorClassSum_divisorClass.unique hα

/-- The **cohomology class** `𝔻_X + ∑_E c_E {E}` of an augmented nef b-divisor. -/
def cohomologyClass (A : AugmentedNefBDivisor m X hn) : RealBottChern (m + 1) X :=
  A.bdiv.root + A.divisorClass

/-- The **volume** of an augmented nef b-divisor: `vol (𝔻, D) = vol 𝔻`. -/
def vol [ConnectedSpace X] (A : AugmentedNefBDivisor m X hn) : ℝ≥0∞ :=
  A.bdiv.vol

end AugmentedNefBDivisor

end SGPT.BDivisor
