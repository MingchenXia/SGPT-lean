import SGPT.Foundations.Schemes.InvariantHomogeneity
import SGPT.Foundations.Schemes.ValuationJumping
import SGPT.Foundations.Schemes.ValuationIdeals
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

/-! # Actual graded quotient colength

The degree action is the literal action on a finitely supported graded vector
sum. Homogeneity of a valuation threshold is derived from scalar invariance.
The resulting quotient decomposes into actual degree quotients. Identifying
this module with the global anticanonical section ring remains geometric work.
-/

open scoped BigOperators DirectSum Classical

namespace SGPT.Foundations.Schemes

section GradedModule

variable {K : Type*} [Field K] {V : ℕ → Type*}
  [∀ k, AddCommGroup (V k)] [∀ k, Module K (V k)]

/-- The literal degree scaling on the infinite direct sum. -/
noncomputable def gradedDegreeScaling (c : K) : (⨁ k, V k) →ₗ[K] ⨁ k, V k :=
  DFinsupp.mapRange.linearMap (fun k => c ^ k • (LinearMap.id : V k →ₗ[K] V k))

theorem gradedDegreeScaling_apply (c : K) (x : ⨁ k, V k) (k : ℕ) :
    gradedDegreeScaling c x k = c ^ k • x k := rfl

theorem graded_sum_components (x : ⨁ k, V k) :
    (∑ k ∈ x.support, DirectSum.lof K ℕ V k (x k)) = x := by
  change x.sum DFinsupp.single = x
  exact DFinsupp.sum_single

theorem gradedDegreeScaling_lof (c : K) (k : ℕ) (y : V k) :
    gradedDegreeScaling c (DirectSum.lof K ℕ V k y) =
      c ^ k • DirectSum.lof K ℕ V k y := by
  ext j
  rw [gradedDegreeScaling_apply, DFinsupp.smul_apply]
  change c ^ j • (DFinsupp.single k y) j = c ^ k • (DFinsupp.single k y) j
  by_cases h : k = j
  · subst j
    rfl
  · simp [DFinsupp.single_apply, h]

theorem gradedDegreeScaling_eq_sum (c : K) (x : ⨁ k, V k) :
    gradedDegreeScaling c x =
      ∑ k ∈ x.support, c ^ k • DirectSum.lof K ℕ V k (x k) := by
  conv_lhs => rw [← graded_sum_components (K := K) x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact gradedDegreeScaling_lof c k (x k)

/-- The concrete map to the finite product of degree quotients. -/
noncomputable def truncatedGradedQuotientMap (S : ∀ k, Submodule K (V k)) (B : ℕ) :
    (⨁ k, V k) →ₗ[K] ∀ k : Fin B, V k ⧸ S k :=
  LinearMap.pi (fun k : Fin B => (S k).mkQ.comp (DirectSum.component K ℕ V k))

theorem truncatedGradedQuotientMap_apply (S : ∀ k, Submodule K (V k)) (B : ℕ)
    (x : ⨁ k, V k) (k : Fin B) :
    truncatedGradedQuotientMap S B x k = (S k).mkQ (x k) := rfl

/-- Every finite list of actual quotient classes has a finitely supported
graded representative, constructed by summing its homogeneous lifts. -/
theorem truncatedGradedQuotientMap_surjective (S : ∀ k, Submodule K (V k)) (B : ℕ) :
    Function.Surjective (truncatedGradedQuotientMap S B) := by
  intro q
  have hchoose : ∀ k : Fin B, ∃ y : V k, (S k).mkQ y = q k := by
    intro k
    exact Submodule.mkQ_surjective (S k) (q k)
  choose y hy using hchoose
  let x : ⨁ k, V k := ∑ k : Fin B, DirectSum.lof K ℕ V k (y k)
  refine ⟨x, ?_⟩
  funext i
  rw [truncatedGradedQuotientMap_apply]
  have hcomponent : DirectSum.component K ℕ V i x = y i := by
    dsimp [x]
    rw [map_sum, Finset.sum_eq_single i]
    · exact DirectSum.component.lof_self (R := K) (ι := ℕ) (M := V) (i : ℕ) (y i)
    · intro j _ hji
      rw [DirectSum.component.of]
      have hval : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
      simp [hval]
    · simp
  change x (i : ℕ) = y i at hcomponent
  rw [hcomponent, hy]

variable {F : Type*} [Field F] [Algebra K F]

/-- Restrict an actual field-representative map to a single graded piece. -/
noncomputable def gradedPieceRepresentation (ι : (⨁ k, V k) →ₗ[K] F) (k : ℕ) :
    V k →ₗ[K] F := ι.comp (DirectSum.lof K ℕ V k)

/-- An invariant valuation threshold is homogeneous, proved from actual
character orbits rather than included as a filtration hypothesis. -/
theorem mem_graded_valuationFiltration_iff [Infinite K]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ c : K, c ≠ 0 → ∀ x : ⨁ k, V k,
      v (ι (gradedDegreeScaling c x)) = v (ι x))
    (a : ℝ) (x : ⨁ k, V k) :
    x ∈ valuationFiltration v ι htrivial a ↔
      ∀ k, x k ∈ valuationFiltration v (gradedPieceRepresentation ι k) htrivial a := by
  constructor
  · intro hx k
    by_cases hk : k ∈ x.support
    · have horbit : ∀ c : K, c ≠ 0 →
          (∑ j ∈ x.support, c ^ j • DirectSum.lof K ℕ V j (x j)) ∈
            valuationFiltration v ι htrivial a := by
        intro c hc
        rw [← gradedDegreeScaling_eq_sum]
        change (a : WithTop ℝ) ≤ v (ι (gradedDegreeScaling c x))
        rw [hinvariant c hc x]
        exact hx
      exact homogeneous_component_mem_of_scalar_orbit_mem
        (valuationFiltration v ι htrivial a) x.support
        (fun j => DirectSum.lof K ℕ V j (x j)) horbit hk
    · have hz : x k = 0 := DFinsupp.notMem_support_iff.mp hk
      rw [hz]
      exact Submodule.zero_mem _
  · intro hx
    change (a : WithTop ℝ) ≤ v (ι x)
    rw [← graded_sum_components (K := K) x, map_sum]
    exact v.map_le_sum (fun k _ => hx k)

/-- Injectivity of the global field representation gives injective genuine
degree representations, since each direct-sum inclusion has a projection. -/
theorem gradedPieceRepresentation_injective (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι) (k : ℕ) :
    Function.Injective (gradedPieceRepresentation ι k) := by
  intro x y h
  have h' : DirectSum.lof K ℕ V k x = DirectSum.lof K ℕ V k y := hι h
  simpa only [DirectSum.lof_apply] using congrArg (fun z : ⨁ k, V k => z k) h'

/-- The actual quotient map for valuation thresholds on the graded pieces. -/
noncomputable def gradedThresholdQuotientMap
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (a : ℝ) (B : ℕ) : (⨁ k, V k) →ₗ[K]
      ∀ k : Fin B, V k ⧸ valuationFiltration v (gradedPieceRepresentation ι k) htrivial a :=
  truncatedGradedQuotientMap
    (fun k => valuationFiltration v (gradedPieceRepresentation ι k) htrivial a) B

/-- Homogeneity derived from invariance identifies the exact kernel of the
finite degree-quotient map. The explicit tail threshold will be produced from
positive fiber weight below. -/
theorem gradedThresholdQuotientMap_ker [Infinite K]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ c : K, c ≠ 0 → ∀ x : ⨁ k, V k,
      v (ι (gradedDegreeScaling c x)) = v (ι x))
    (a : ℝ) (B : ℕ)
    (htail : ∀ k : ℕ, B ≤ k → ∀ y : V k,
      (a : WithTop ℝ) ≤ v (gradedPieceRepresentation ι k y)) :
    LinearMap.ker (gradedThresholdQuotientMap v ι htrivial a B) =
      valuationFiltration v ι htrivial a := by
  ext x
  rw [LinearMap.mem_ker, mem_graded_valuationFiltration_iff v ι htrivial hinvariant]
  constructor
  · intro hx k
    by_cases hk : k < B
    · have hz := congrFun hx (⟨k, hk⟩ : Fin B)
      change (Submodule.Quotient.mk (x k) :
        V k ⧸ valuationFiltration v (gradedPieceRepresentation ι k) htrivial a) = 0 at hz
      exact (Submodule.Quotient.mk_eq_zero _).mp hz
    · exact htail k (Nat.le_of_not_gt hk) (x k)
  · intro hx
    funext k
    change (Submodule.Quotient.mk (x k) :
      V k ⧸ valuationFiltration v (gradedPieceRepresentation ι k) htrivial a) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hx k)

/-- The true infinite graded quotient is linearly equivalent to the finite
product of its actual degree quotients, including degree zero. -/
noncomputable def gradedValuationQuotientEquiv [Infinite K]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ c : K, c ≠ 0 → ∀ x : ⨁ k, V k,
      v (ι (gradedDegreeScaling c x)) = v (ι x))
    (a : ℝ) (B : ℕ)
    (htail : ∀ k : ℕ, B ≤ k → ∀ y : V k,
      (a : WithTop ℝ) ≤ v (gradedPieceRepresentation ι k y)) :
    ((⨁ k, V k) ⧸ valuationFiltration v ι htrivial a) ≃ₗ[K]
      ∀ k : Fin B, V k ⧸ valuationFiltration v (gradedPieceRepresentation ι k) htrivial a := by
  rw [← gradedThresholdQuotientMap_ker v ι htrivial hinvariant a B htail]
  exact LinearMap.quotKerEquivOfSurjective (gradedThresholdQuotientMap v ι htrivial a B)
    (truncatedGradedQuotientMap_surjective _ B)

theorem gradedValuation_colength_eq_sum [Infinite K] [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ c : K, c ≠ 0 → ∀ x : ⨁ k, V k,
      v (ι (gradedDegreeScaling c x)) = v (ι x))
    (a : ℝ) (B : ℕ)
    (htail : ∀ k : ℕ, B ≤ k → ∀ y : V k,
      (a : WithTop ℝ) ≤ v (gradedPieceRepresentation ι k y)) :
    Module.finrank K ((⨁ k, V k) ⧸ valuationFiltration v ι htrivial a) =
      ∑ k : Fin B, Module.finrank K
        (V k ⧸ valuationFiltration v (gradedPieceRepresentation ι k) htrivial a) := by
  rw [(gradedValuationQuotientEquiv v ι htrivial hinvariant a B htail).finrank_eq]
  exact Module.finrank_pi_fintype K

/-- Finiteness of the actual global quotient is a consequence of the proved
linear equivalence, rather than an independent colength assumption. -/
theorem gradedValuation_quotient_finiteDimensional [Infinite K]
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ c : K, c ≠ 0 → ∀ x : ⨁ k, V k,
      v (ι (gradedDegreeScaling c x)) = v (ι x))
    (a : ℝ) (B : ℕ)
    (htail : ∀ k : ℕ, B ≤ k → ∀ y : V k,
      (a : WithTop ℝ) ≤ v (gradedPieceRepresentation ι k y)) :
    FiniteDimensional K ((⨁ k, V k) ⧸ valuationFiltration v ι htrivial a) :=
  (gradedValuationQuotientEquiv v ι htrivial hinvariant a B htail).symm.finiteDimensional

/-- The genuine adapted-basis weights of each graded piece. -/
noncomputable def gradedJumpingWeights [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0) (k : ℕ) :
    Fin (Module.finrank K (V k)) → ℝ :=
  valuationJumpingWeights v (gradedPieceRepresentation ι k)
    (gradedPieceRepresentation_injective ι hι k) htrivial

/-- Subtract the fiber contribution from the actual homogeneous weights. -/
noncomputable def gradedCoefficientJumpingWeights [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0) (c : ℝ) (k : ℕ) :
    Fin (Module.finrank K (V k)) → ℝ :=
  fun j => gradedJumpingWeights v ι hι htrivial k j - c * (k : ℝ)

theorem gradedJumpingWeights_eq_fiber_add_coefficient
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (c : ℝ) (k : ℕ) (j : Fin (Module.finrank K (V k))) :
    gradedJumpingWeights v ι hι htrivial k j = c * (k : ℝ) +
      gradedCoefficientJumpingWeights v ι hι htrivial c k j := by
  simp [gradedCoefficientJumpingWeights]

/-- The shifted weights are literally the coefficient valuations of the
proved adapted basis, when the homogeneous representation factors through
the actual fiber variable. -/
theorem coe_gradedCoefficientJumpingWeights_of_factorization
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (z : F) (c : ℝ) (hz : v z = (c : WithTop ℝ))
    (b : ∀ k, V k → F)
    (hfactor : ∀ k y, gradedPieceRepresentation ι k y = b k y * z ^ k)
    (k : ℕ) (j : Fin (Module.finrank K (V k))) :
    ((gradedCoefficientJumpingWeights v ι hι htrivial c k j : ℝ) : WithTop ℝ) =
      v (b k (valuationAdaptedBasis v (gradedPieceRepresentation ι k)
        (gradedPieceRepresentation_injective ι hι k) htrivial j)) := by
  apply WithTop.add_right_cancel (z := ((c * (k : ℝ) : ℝ) : WithTop ℝ))
    WithTop.coe_ne_top
  rw [← WithTop.coe_add]
  have hsum : gradedCoefficientJumpingWeights v ι hι htrivial c k j + c * (k : ℝ) =
      gradedJumpingWeights v ι hι htrivial k j := by
    simp [gradedCoefficientJumpingWeights]
  rw [hsum]
  change ((valuationJumpingWeights v (gradedPieceRepresentation ι k)
    (gradedPieceRepresentation_injective ι hι k) htrivial j : ℝ) : WithTop ℝ) = _
  rw [coe_valuationJumpingWeights, hfactor, v.map_mul, v.map_pow, hz,
    ← WithTop.coe_nsmul, nsmul_eq_mul, mul_comm (k : ℝ) c]

theorem gradedCoefficientJumpingWeights_nonneg_of_factorization
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (z : F) (c : ℝ) (hz : v z = (c : WithTop ℝ))
    (b : ∀ k, V k → F)
    (hfactor : ∀ k y, gradedPieceRepresentation ι k y = b k y * z ^ k)
    (hcenter : ∀ k y, (0 : WithTop ℝ) ≤ v (b k y))
    (k : ℕ) (j : Fin (Module.finrank K (V k))) :
    0 ≤ gradedCoefficientJumpingWeights v ι hι htrivial c k j := by
  apply WithTop.coe_le_coe.mp
  rw [coe_gradedCoefficientJumpingWeights_of_factorization v ι hι htrivial z c hz
    b hfactor]
  exact hcenter k _

/-- The derived graded quotient dimension counts actual jumping weights,
retaining multiplicities and the degree-zero summand. -/
theorem gradedValuation_colength_eq_count [Infinite K]
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ c : K, c ≠ 0 → ∀ x : ⨁ k, V k,
      v (ι (gradedDegreeScaling c x)) = v (ι x))
    (a : ℝ) (B : ℕ)
    (htail : ∀ k : ℕ, B ≤ k → ∀ y : V k,
      (a : WithTop ℝ) ≤ v (gradedPieceRepresentation ι k y)) :
    Module.finrank K ((⨁ k, V k) ⧸ valuationFiltration v ι htrivial a) =
      ∑ k : Fin B, (Finset.univ.filter
        (fun j => gradedJumpingWeights v ι hι htrivial k j < a)).card := by
  rw [gradedValuation_colength_eq_sum v ι htrivial hinvariant a B htail]
  apply Finset.sum_congr rfl
  intro k _
  exact valuationFiltration_quotient_finrank_eq_count v (gradedPieceRepresentation ι k)
    (gradedPieceRepresentation_injective ι hι k) htrivial a

/-- Multiplicativity supplies the degree lower bound from an actual fiber
factorization and nonnegative coefficient values. -/
theorem gradedPiece_lower_bound_of_factorization
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (z : F) (c : ℝ) (hz : v z = (c : WithTop ℝ))
    (b : ∀ k, V k → F)
    (hfactor : ∀ k y, gradedPieceRepresentation ι k y = b k y * z ^ k)
    (hcenter : ∀ k y, (0 : WithTop ℝ) ≤ v (b k y)) :
    ∀ (k : ℕ) (y : V k), ((c * (k : ℝ) : ℝ) : WithTop ℝ) ≤
      v (gradedPieceRepresentation ι k y) := by
  intro k y
  rw [hfactor, v.map_mul, v.map_pow, hz]
  have hpow : k • (c : WithTop ℝ) = ((c * (k : ℝ) : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_nsmul, nsmul_eq_mul, mul_comm]
  rw [hpow]
  exact le_add_of_nonneg_left (hcenter k y)

/-- Positive fiber weight makes all sufficiently high actual degree pieces
lie in the threshold, even when the threshold itself is nonpositive. -/
theorem graded_threshold_tail_of_positive_weight
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    {c : ℝ} (hc : 0 < c)
    (hdegree : ∀ (k : ℕ) (y : V k), ((c * (k : ℝ) : ℝ) : WithTop ℝ) ≤
      v (gradedPieceRepresentation ι k y)) (a : ℝ) :
    ∀ k : ℕ, Nat.ceil (a / c) ≤ k → ∀ y : V k,
      (a : WithTop ℝ) ≤ v (gradedPieceRepresentation ι k y) := by
  intro k hk y
  have hratio : a / c ≤ (k : ℝ) := Nat.ceil_le.mp hk
  have ha : a ≤ c * (k : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hc).mp hratio
  exact (WithTop.coe_le_coe.mpr ha).trans (hdegree k y)

theorem gradedJumpingWeights_degree_lower_bound
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (c : ℝ)
    (hdegree : ∀ (k : ℕ) (y : V k), ((c * (k : ℝ) : ℝ) : WithTop ℝ) ≤
      v (gradedPieceRepresentation ι k y))
    (k : ℕ) (j : Fin (Module.finrank K (V k))) :
    c * (k : ℝ) ≤ gradedJumpingWeights v ι hι htrivial k j := by
  apply WithTop.coe_le_coe.mp
  change ((c * (k : ℝ) : ℝ) : WithTop ℝ) ≤
    ((valuationJumpingWeights v (gradedPieceRepresentation ι k)
      (gradedPieceRepresentation_injective ι hι k) htrivial j : ℝ) : WithTop ℝ)
  rw [coe_valuationJumpingWeights]
  exact hdegree k _

/-- Counts in high degrees vanish because their actual values exceed the
threshold, not because finite support was supplied as data. -/
theorem gradedJumpingWeights_count_eq_zero_of_high_degree
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    {c : ℝ} (hc : 0 < c)
    (hdegree : ∀ (k : ℕ) (y : V k), ((c * (k : ℝ) : ℝ) : WithTop ℝ) ≤
      v (gradedPieceRepresentation ι k y)) (a : ℝ) (k : ℕ)
    (hk : Nat.ceil (a / c) ≤ k) :
    (Finset.univ.filter (fun j => gradedJumpingWeights v ι hι htrivial k j < a)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro j _ hj
  have ha : a ≤ c * (k : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hc).mp (Nat.ceil_le.mp hk)
  have hw := gradedJumpingWeights_degree_lower_bound v ι hι htrivial c hdegree k j
  exact (not_lt_of_ge (ha.trans hw)) hj

/-- Exact colength for the literal infinite graded representation. The
finite range is produced by the positive degree weight; no colength equality
or finite-support assertion is supplied as a hypothesis. -/
theorem gradedValuation_colength_eq_count_of_positive_weight [Infinite K]
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ c : K, c ≠ 0 → ∀ x : ⨁ k, V k,
      v (ι (gradedDegreeScaling c x)) = v (ι x))
    {c : ℝ} (hc : 0 < c)
    (hdegree : ∀ (k : ℕ) (y : V k), ((c * (k : ℝ) : ℝ) : WithTop ℝ) ≤
      v (gradedPieceRepresentation ι k y)) (a : ℝ) :
    Module.finrank K ((⨁ k, V k) ⧸ valuationFiltration v ι htrivial a) =
      ∑ k : Fin (Nat.ceil (a / c)), (Finset.univ.filter
        (fun j => gradedJumpingWeights v ι hι htrivial k j < a)).card :=
  gradedValuation_colength_eq_count v ι hι htrivial hinvariant a _
    (graded_threshold_tail_of_positive_weight v ι hc hdegree a)

/-- The equivalent all-degree sum converges because positive fiber weight
proves that its terms are zero outside a concrete finite range. -/
theorem gradedValuation_colength_eq_tsum_of_positive_weight [Infinite K]
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ c : K, c ≠ 0 → ∀ x : ⨁ k, V k,
      v (ι (gradedDegreeScaling c x)) = v (ι x))
    {c : ℝ} (hc : 0 < c)
    (hdegree : ∀ (k : ℕ) (y : V k), ((c * (k : ℝ) : ℝ) : WithTop ℝ) ≤
      v (gradedPieceRepresentation ι k y)) (a : ℝ) :
    Module.finrank K ((⨁ k, V k) ⧸ valuationFiltration v ι htrivial a) =
      ∑' k : ℕ, (Finset.univ.filter
        (fun j => gradedJumpingWeights v ι hι htrivial k j < a)).card := by
  rw [tsum_eq_sum (s := Finset.range (Nat.ceil (a / c))) (fun k hk =>
    gradedJumpingWeights_count_eq_zero_of_high_degree v ι hι htrivial hc hdegree a k
      (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)))]
  rw [gradedValuation_colength_eq_count_of_positive_weight v ι hι htrivial hinvariant
    hc hdegree a]
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (Finset.univ.filter
      (fun j => gradedJumpingWeights v ι hι htrivial k j < a)).card) _

/-- A source-facing factorization form: centered coefficient values and the
actual positive fiber value produce the finite colength count. -/
theorem gradedValuation_colength_eq_count_of_factorization [Infinite K]
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (ι : (⨁ k, V k) →ₗ[K] F)
    (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ c : K, c ≠ 0 → ∀ x : ⨁ k, V k,
      v (ι (gradedDegreeScaling c x)) = v (ι x))
    (z : F) {c : ℝ} (hc : 0 < c) (hz : v z = (c : WithTop ℝ))
    (b : ∀ k, V k → F)
    (hfactor : ∀ k y, gradedPieceRepresentation ι k y = b k y * z ^ k)
    (hcenter : ∀ k y, (0 : WithTop ℝ) ≤ v (b k y)) (a : ℝ) :
    Module.finrank K ((⨁ k, V k) ⧸ valuationFiltration v ι htrivial a) =
      ∑ k : Fin (Nat.ceil (a / c)), (Finset.univ.filter
        (fun j => gradedJumpingWeights v ι hι htrivial k j < a)).card :=
  gradedValuation_colength_eq_count_of_positive_weight v ι hι htrivial hinvariant hc
    (gradedPiece_lower_bound_of_factorization v ι z c hz b hfactor hcenter) a

section GradedRing

variable {R : Type*} [CommRing R] [Algebra K R]

/-- A genuine linear decomposition of a graded ring gives the actual
valuation-ideal quotient, by the first isomorphism theorem for its ordinary
quotient map. No quotient dimension is prescribed. -/
noncomputable def gradedRingValuationQuotientEquiv
    (v : AddValuation F (WithTop ℝ)) (f : R →ₐ[K] F)
    (E : (⨁ k, V k) ≃ₗ[K] R)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0) (a : ℝ) :
    ((⨁ k, V k) ⧸ valuationFiltration v (f.toLinearMap.comp E.toLinearMap) htrivial a)
      ≃ₗ[K] R ⧸ valuationIdeal v f.toRingHom hcenter a := by
  rw [← valuationPieceQuotientMap_ker v f hcenter htrivial E.toLinearMap a]
  apply LinearMap.quotKerEquivOfSurjective
  intro q
  obtain ⟨r, hr⟩ := Ideal.Quotient.mkₐ_surjective K
    (valuationIdeal v f.toRingHom hcenter a) q
  refine ⟨E.symm r, ?_⟩
  change (Ideal.Quotient.mkₐ K (valuationIdeal v f.toRingHom hcenter a))
    (E (E.symm r)) = q
  rw [E.apply_symm_apply]
  exact hr

/-- Exact colength of the actual ring valuation ideal. A literal graded
decomposition, degree scaling invariance and positive fiber factorization are
the representation hypotheses still to be produced for a geometric section
ring; homogeneous thresholds and the counting identity are proved here. -/
theorem gradedRingValuation_colength_eq_count_of_factorization [Infinite K]
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (f : R →ₐ[K] F)
    (E : (⨁ k, V k) ≃ₗ[K] R) (hf : Function.Injective f)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ t : K, t ≠ 0 → ∀ x : ⨁ k, V k,
      v (f (E (gradedDegreeScaling t x))) = v (f (E x)))
    (z : F) {c : ℝ} (hc : 0 < c) (hz : v z = (c : WithTop ℝ))
    (b : ∀ k, V k → F)
    (hfactor : ∀ k y,
      gradedPieceRepresentation (f.toLinearMap.comp E.toLinearMap) k y = b k y * z ^ k)
    (hbase : ∀ k y, (0 : WithTop ℝ) ≤ v (b k y)) (a : ℝ) :
    Module.finrank K (R ⧸ valuationIdeal v f.toRingHom hcenter a) =
      ∑ k : Fin (Nat.ceil (a / c)), (Finset.univ.filter (fun j =>
        gradedJumpingWeights v (f.toLinearMap.comp E.toLinearMap)
          (hf.comp E.injective) htrivial k j < a)).card := by
  rw [← (gradedRingValuationQuotientEquiv v f E hcenter htrivial a).finrank_eq]
  exact gradedValuation_colength_eq_count_of_factorization v
    (f.toLinearMap.comp E.toLinearMap) (hf.comp E.injective) htrivial
    hinvariant z hc hz b hfactor hbase a

/-- The source's coefficient-weight form `c*k + λ < a`, with `λ` proved above
to be the actual centered coefficient valuations of an adapted basis. -/
theorem gradedRingValuation_colength_eq_coefficient_count_of_factorization [Infinite K]
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (f : R →ₐ[K] F)
    (E : (⨁ k, V k) ≃ₗ[K] R) (hf : Function.Injective f)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ t : K, t ≠ 0 → ∀ x : ⨁ k, V k,
      v (f (E (gradedDegreeScaling t x))) = v (f (E x)))
    (z : F) {c : ℝ} (hc : 0 < c) (hz : v z = (c : WithTop ℝ))
    (b : ∀ k, V k → F)
    (hfactor : ∀ k y,
      gradedPieceRepresentation (f.toLinearMap.comp E.toLinearMap) k y = b k y * z ^ k)
    (hbase : ∀ k y, (0 : WithTop ℝ) ≤ v (b k y)) (a : ℝ) :
    Module.finrank K (R ⧸ valuationIdeal v f.toRingHom hcenter a) =
      ∑ k : Fin (Nat.ceil (a / c)), (Finset.univ.filter (fun j => c * (k : ℝ) +
        gradedCoefficientJumpingWeights v (f.toLinearMap.comp E.toLinearMap)
          (hf.comp E.injective) htrivial c k j < a)).card := by
  rw [gradedRingValuation_colength_eq_count_of_factorization v f E hf hcenter
    htrivial hinvariant z hc hz b hfactor hbase a]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.filter_congr
  intro j _
  rw [gradedJumpingWeights_eq_fiber_add_coefficient v
    (f.toLinearMap.comp E.toLinearMap) (hf.comp E.injective) htrivial c k j]

/-- The all-degree source identity for the actual ideal quotient. Its sum is
proved to have finite support by the positive fiber value. -/
theorem gradedRingValuation_colength_eq_coefficient_tsum_of_factorization [Infinite K]
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (f : R →ₐ[K] F)
    (E : (⨁ k, V k) ≃ₗ[K] R) (hf : Function.Injective f)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ t : K, t ≠ 0 → ∀ x : ⨁ k, V k,
      v (f (E (gradedDegreeScaling t x))) = v (f (E x)))
    (z : F) {c : ℝ} (hc : 0 < c) (hz : v z = (c : WithTop ℝ))
    (b : ∀ k, V k → F)
    (hfactor : ∀ k y,
      gradedPieceRepresentation (f.toLinearMap.comp E.toLinearMap) k y = b k y * z ^ k)
    (hbase : ∀ k y, (0 : WithTop ℝ) ≤ v (b k y)) (a : ℝ) :
    Module.finrank K (R ⧸ valuationIdeal v f.toRingHom hcenter a) =
      ∑' k : ℕ, (Finset.univ.filter (fun j => c * (k : ℝ) +
        gradedCoefficientJumpingWeights v (f.toLinearMap.comp E.toLinearMap)
          (hf.comp E.injective) htrivial c k j < a)).card := by
  rw [← (gradedRingValuationQuotientEquiv v f E hcenter htrivial a).finrank_eq]
  rw [gradedValuation_colength_eq_tsum_of_positive_weight v
    (f.toLinearMap.comp E.toLinearMap) (hf.comp E.injective) htrivial hinvariant hc
    (gradedPiece_lower_bound_of_factorization v (f.toLinearMap.comp E.toLinearMap)
      z c hz b hfactor hbase) a]
  apply tsum_congr
  intro k
  congr 1
  apply Finset.filter_congr
  intro j _
  rw [gradedJumpingWeights_eq_fiber_add_coefficient v
    (f.toLinearMap.comp E.toLinearMap) (hf.comp E.injective) htrivial c k j]

/-- In the same concrete ring setting, positive fiber value produces finite
dimensionality of the full ideal quotient. -/
theorem gradedRingValuation_quotient_finiteDimensional_of_factorization [Infinite K]
    [∀ k, FiniteDimensional K (V k)]
    (v : AddValuation F (WithTop ℝ)) (f : R →ₐ[K] F)
    (E : (⨁ k, V k) ≃ₗ[K] R)
    (hcenter : ∀ r : R, (0 : WithTop ℝ) ≤ v (f r))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hinvariant : ∀ t : K, t ≠ 0 → ∀ x : ⨁ k, V k,
      v (f (E (gradedDegreeScaling t x))) = v (f (E x)))
    (z : F) {c : ℝ} (hc : 0 < c) (hz : v z = (c : WithTop ℝ))
    (b : ∀ k, V k → F)
    (hfactor : ∀ k y,
      gradedPieceRepresentation (f.toLinearMap.comp E.toLinearMap) k y = b k y * z ^ k)
    (hbase : ∀ k y, (0 : WithTop ℝ) ≤ v (b k y)) (a : ℝ) :
    FiniteDimensional K (R ⧸ valuationIdeal v f.toRingHom hcenter a) := by
  let ι := f.toLinearMap.comp E.toLinearMap
  have hdegree := gradedPiece_lower_bound_of_factorization v ι z c hz b hfactor hbase
  let := gradedValuation_quotient_finiteDimensional v ι htrivial hinvariant a
    (Nat.ceil (a / c)) (graded_threshold_tail_of_positive_weight v ι hc hdegree a)
  exact (gradedRingValuationQuotientEquiv v f E hcenter htrivial a).finiteDimensional

end GradedRing

/-- The actual constant coefficient space contributes one dimension at a
positive threshold: its threshold subspace is zero by scalar triviality. -/
theorem constant_valuationFiltration_eq_bot
    (v : AddValuation F (WithTop ℝ))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    {a : ℝ} (ha : 0 < a) :
    valuationFiltration v (Algebra.linearMap K F) htrivial a = ⊥ := by
  ext x
  rw [Submodule.mem_bot]
  constructor
  · intro hx
    by_contra hxzero
    change (a : WithTop ℝ) ≤ v (algebraMap K F x) at hx
    rw [htrivial x hxzero] at hx
    exact (not_le.mpr ha) (WithTop.coe_le_coe.mp hx)
  · rintro rfl
    exact Submodule.zero_mem _

theorem constant_valuation_colength_eq_one
    (v : AddValuation F (WithTop ℝ))
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    {a : ℝ} (ha : 0 < a) :
    Module.finrank K (K ⧸ valuationFiltration v (Algebra.linearMap K F) htrivial a) = 1 := by
  rw [constant_valuationFiltration_eq_bot v htrivial ha]
  have h := Submodule.finrank_quotient_add_finrank (⊥ : Submodule K K)
  simpa using h

end GradedModule

end SGPT.Foundations.Schemes
