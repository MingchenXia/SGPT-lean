import SGPT.Toric.OriginalGuilleminInvariance
import SGPT.Toric.OriginalGuilleminTorusRestriction
import SGPT.Toric.ProjectiveToricReverse
import SGPT.Toric.RelativeThetaCriterion
import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.AdmissiblePresentationHolomorphicPullback

/-!
# The toric manifold of a Delzant lattice polytope

Source `chapter_toric_ample.tex`, section `sec:toricsetup` and the first part of
`sec:tpf`.  Throughout, `P = conv(γ)` is a full-dimensional smooth (Delzant) lattice
polytope in `M_ℝ = ℝ^n` (`latticePolytopeEdgeSmooth γ`; the character lattice is
identified with `ℤ^n`).  We package the existing compact complex manifold

* `X = PolytopeToricVariety γ hs`, the closure of the dense torus orbit of the
  monomial embedding by the lattice points `P ∩ M` (this is the projective toric
  variety `X_Σ` of the normal fan, embedded by the very ample `L = O(D_P)`);
* its torus embedding `ι : (ℂ^*)^n → X` and torus action;
* the Guillemin Kähler form `ω` extending `ddᶜ Trop^* F_0` (source: Guillemin's
  theorem, `F_0 = G_0^*`), as a native closed `(1,1)`-form, as a Kähler background,
  and as a source atlas form for `IsThetaPSH`;
* the set `PSH_tor(X, ω)` of `T_c`-invariant `ω`-psh functions;
* the profile `F_φ(x) = φ(ι(e^{x/2})) + F_0(x)` of a toric potential
  (source `eq:FvarphidefGdef`), on `N_ℝ = EuclideanSpace ℝ (Fin n)` with the
  standard pairing.

The main technical result of this file is the chart identity relating, in every
vertex chart, the corrected local potential of a torus-invariant function to the
tropical pullback of its profile, composed with the real lattice basis change.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff BigOperators Manifold

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- Source `sec:toricsetup`: the smooth projective toric variety `X = X_Σ` of the
Delzant lattice polytope `P = conv(γ)`, realised as the closure of the dense torus
orbit of the monomial map given by all lattice points of `P`, with its native
vertex-chart complex structure. -/
def PolytopeToricVariety (γ : K → Fin n → ℤ) (_hs : latticePolytopeEdgeSmooth γ) : Type :=
  originalPolytopeNativeSpace γ

variable (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)

instance : TopologicalSpace (PolytopeToricVariety γ hs) := originalPolytopeNativeTopology γ

instance : ChartedSpace (ComplexModel n) (PolytopeToricVariety γ hs) :=
  originalPolytopeNativeChartedSpace γ hs

instance : IsComplexManifold n (PolytopeToricVariety γ hs) :=
  originalPolytopeNativeIsComplexManifold γ hs

instance : CompactSpace (PolytopeToricVariety γ hs) := originalPolytopeNativeCompactSpace γ

instance : MeasurableSpace (PolytopeToricVariety γ hs) := borel _

instance : BorelSpace (PolytopeToricVariety γ hs) := ⟨rfl⟩

/-- Source `sec:toricsetup`: the canonical dense embedding `T(ℂ) = (ℂ^*)^n ⊆ X`. -/
def polytopeToricEmbedding (a : Fin n → ℂˣ) : PolytopeToricVariety γ hs :=
  originalPolytopeNativeOrbitMap γ a

instance : Nonempty (PolytopeToricVariety γ hs) := ⟨polytopeToricEmbedding γ hs 1⟩

/-- The action of the torus `T(ℂ)` on `X`. -/
def polytopeToricAction (a : Fin n → ℂˣ) :
    PolytopeToricVariety γ hs ≃ₜ PolytopeToricVariety γ hs :=
  originalPolytopeNativeAction γ a

/-- The toric boundary `X ∖ T(ℂ)`. -/
def polytopeToricBoundary : Set (PolytopeToricVariety γ hs) :=
  originalPolytopeNativeBoundary γ

/-- An element of the compact torus `T_c = (S^1)^n`. -/
def IsCompactTorusElement (a : Fin n → ℂˣ) : Prop := ∀ j, ‖(a j : ℂ)‖ = 1

/-- `T_c`-invariance of a function on `X`. -/
def PolytopeToricInvariant (u : PolytopeToricVariety γ hs → EReal) : Prop :=
  ∀ a : Fin n → ℂˣ, IsCompactTorusElement a → ∀ p, u (polytopeToricAction γ hs a p) = u p

/-- Source `sec:tpf`: the Guillemin Kähler form `ω` extending `ddᶜ Trop^* F_0`. -/
def polytopeToricKahlerForm : ClosedRealOneOneForm n (PolytopeToricVariety γ hs) :=
  originalGuilleminClosedForm γ hs

/-- The Guillemin form is Kähler. -/
def polytopeToricKahlerBackground : KahlerBackground n (PolytopeToricVariety γ hs) :=
  ⟨polytopeToricKahlerForm γ hs, isKahler_originalGuilleminClosedForm γ hs⟩

/-- The same form in the source atlas interface used by `IsThetaPSH`. -/
def polytopeToricOmega :
    AtlasClosedRealOneOneForm (ofFixedModel n (PolytopeToricVariety γ hs)) :=
  nativeClosedFormToAtlas (polytopeToricKahlerForm γ hs)

/-- Source `sec:tpf`: `PSH_tor(X, ω)`, the `T_c`-invariant `ω`-psh functions. -/
def PolytopeToricPSH : Set (PolytopeToricVariety γ hs → EReal) :=
  {u | (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) u ∧
    PolytopeToricInvariant γ hs u}

/-! ### Real coordinates -/

/-- Source `eq:log`: the tropicalization `Trop(a) = (log |a_j|^2)_j` of a torus point. -/
def unitTorusLog (a : Fin n → ℂˣ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (torusLogCoordinates (latticeTorusPoint a))

theorem unitTorusLog_apply (a : Fin n → ℂˣ) (j : Fin n) :
    unitTorusLog a j = 2 * Real.log ‖(a j : ℂ)‖ := rfl

/-- The positive real torus point `e^{x/2}` with `Trop(e^{x/2}) = x`. -/
def positiveTorusPoint (x : EuclideanSpace ℝ (Fin n)) : Fin n → ℂˣ :=
  fun j => Units.mk0 ((Real.exp (x j / 2) : ℝ) : ℂ)
    (by exact_mod_cast (Real.exp_pos (x j / 2)).ne')

theorem unitTorusLog_positiveTorusPoint (x : EuclideanSpace ℝ (Fin n)) :
    unitTorusLog (positiveTorusPoint x) = x := by
  ext j
  rw [unitTorusLog_apply]
  change 2 * Real.log ‖((Real.exp (x j / 2) : ℝ) : ℂ)‖ = x j
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp]
  ring

/-- The angular part of a torus point, an element of the compact torus. -/
def torusAngularPart (a : Fin n → ℂˣ) : Fin n → ℂˣ :=
  fun j => Units.mk0 ((a j : ℂ) / ((‖(a j : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero (Units.ne_zero _) (by exact_mod_cast (norm_pos_iff.mpr (Units.ne_zero (a j))).ne'))

theorem isCompactTorusElement_torusAngularPart (a : Fin n → ℂˣ) :
    IsCompactTorusElement (torusAngularPart a) := by
  intro j
  change ‖(a j : ℂ) / ((‖(a j : ℂ)‖ : ℝ) : ℂ)‖ = 1
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.mpr (Units.ne_zero _))]

/-- Polar decomposition `a = (a/|a|) · e^{Trop(a)/2}`. -/
theorem torusAngularPart_mul_positiveTorusPoint (a : Fin n → ℂˣ) :
    torusAngularPart a * positiveTorusPoint (unitTorusLog a) = a := by
  funext j
  apply Units.ext
  have hpos : 0 < ‖(a j : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hexp : Real.exp (unitTorusLog a j / 2) = ‖(a j : ℂ)‖ := by
    rw [unitTorusLog_apply, show 2 * Real.log ‖(a j : ℂ)‖ / 2 = Real.log ‖(a j : ℂ)‖ by ring,
      Real.exp_log hpos]
  change (a j : ℂ) / ((‖(a j : ℂ)‖ : ℝ) : ℂ) * ((Real.exp (unitTorusLog a j / 2) : ℝ) : ℂ) =
    (a j : ℂ)
  rw [hexp, div_mul_cancel₀]
  exact_mod_cast hpos.ne'

/-- Compact-torus multiplication does not change the tropicalization. -/
theorem unitTorusLog_compact_mul {a b : Fin n → ℂˣ} (ha : IsCompactTorusElement a) :
    unitTorusLog (a * b) = unitTorusLog b := by
  unfold unitTorusLog
  rw [torusLogCoordinates_compact_mul a b ha]

/-- The pairing `⟨m, x⟩` of an integral vector with a real one. -/
def latticeFunctional (m : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, (m i : ℝ) * x i
  map_add' x y := by
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem latticeFunctional_apply (m : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    latticeFunctional m x = ∑ i, (m i : ℝ) * x i := rfl

/-- Real logarithmic coordinates of the characters of a lattice basis:
`(B_b x)_j = ⟨b_j, x⟩`. -/
def latticeBasisLogMap (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => latticeFunctional (b j) x)
  map_add' x y := by
    ext j
    simp only [map_add]
    rfl
  map_smul' c x := by
    ext j
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    rfl

/-- The inverse real basis change, with coefficients `b.repr e_k`. -/
def latticeBasisLogInverse (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun y := (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun k => latticeFunctional (fun j => b.repr (Pi.single k 1) j) y)
  map_add' x y := by
    ext j
    simp only [map_add]
    rfl
  map_smul' c x := by
    ext j
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    rfl

theorem latticeBasisLogMap_apply (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    latticeBasisLogMap b x j = ∑ i, (b j i : ℝ) * x i := rfl

theorem latticeBasisLogInverse_apply (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (y : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    latticeBasisLogInverse b y k = ∑ j, (b.repr (Pi.single k 1) j : ℝ) * y j := rfl

/-- The inverse basis change is a left inverse of the logarithmic character map. -/
theorem latticeBasisLogInverse_logMap (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (x : EuclideanSpace ℝ (Fin n)) :
    latticeBasisLogInverse b (latticeBasisLogMap b x) = x := by
  ext k
  rw [latticeBasisLogInverse_apply]
  simp only [latticeBasisLogMap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hcoef (i : Fin n) :
      ∑ j, (b.repr (Pi.single k 1) j : ℝ) * (b j i : ℝ) =
        (((Pi.single k (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℝ) := by
    have h := congrFun (b.sum_repr (Pi.single k 1)) i
    rw [Finset.sum_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    exact_mod_cast h
  calc
    ∑ i, ∑ j, (b.repr (Pi.single k 1) j : ℝ) * ((b j i : ℝ) * x i)
        = ∑ i, (∑ j, (b.repr (Pi.single k 1) j : ℝ) * (b j i : ℝ)) * x i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, (((Pi.single k (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℝ) * x i := by simp only [hcoef]
    _ = x k := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro i _ hik
            simp [hik]
          · simp

/-! ### The reference potential and the moment polytope -/

/-- Source `eq:F0def`: `F_0 = G_0^*`, in the Euclidean model of `N_ℝ`. -/
def polytopeToricReference (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (originalCanonicalReference γ hs (EuclideanSpace.equiv (Fin n) ℝ x)).toReal

theorem polytopeToricReference_coe (x : EuclideanSpace ℝ (Fin n)) :
    (polytopeToricReference γ hs x : EReal) =
      originalCanonicalReference γ hs (EuclideanSpace.equiv (Fin n) ℝ x) := by
  obtain ⟨v, hv⟩ := nonempty_latticePolytopeVertices γ
  have hf := originalCanonicalReference_finite γ hs ⟨v, hv⟩ (EuclideanSpace.equiv (Fin n) ℝ x)
  exact EReal.coe_toReal hf.2 hf.1

/-- The moment polytope `P ⊆ M_ℝ`, in the Euclidean model. -/
def polytopeToricMomentPolytope : Set (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.equiv (Fin n) ℝ) ⁻¹' latticePolytope γ

omit [Nonempty K] in
theorem isCompact_polytopeToricMomentPolytope : IsCompact (polytopeToricMomentPolytope γ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isCompact_preimage.mpr (isCompact_latticePolytope γ)

omit [Fintype K] [Nonempty K] in
theorem convex_polytopeToricMomentPolytope : Convex ℝ (polytopeToricMomentPolytope γ) :=
  (convex_latticePolytope γ).linear_preimage
    (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toLinearMap

omit [Fintype K] in
theorem nonempty_polytopeToricMomentPolytope : (polytopeToricMomentPolytope γ).Nonempty := by
  obtain ⟨x, hx⟩ := nonempty_latticePolytope γ
  refine ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm x, ?_⟩
  change EuclideanSpace.equiv (Fin n) ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm x) ∈
    latticePolytope γ
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact hx

omit [Fintype K] [Nonempty K] in
/-- The support function of the Euclidean moment polytope is the original support function. -/
theorem support_polytopeToricMomentPolytope (y : EuclideanSpace ℝ (Fin n)) :
    support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (polytopeToricMomentPolytope γ) y =
      support (originalCoordinatePairing n) (latticePolytope γ)
        (EuclideanSpace.equiv (Fin n) ℝ y) := by
  have hpair (m : EuclideanSpace ℝ (Fin n)) :
      (innerₗ (EuclideanSpace ℝ (Fin n))).flip m y =
        originalCoordinatePairing n (EuclideanSpace.equiv (Fin n) ℝ m)
          (EuclideanSpace.equiv (Fin n) ℝ y) := by
    simp [originalCanonicalPairing_apply, innerₗ_apply_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  apply le_antisymm
  · refine iSup_le fun m => ?_
    have hm : EuclideanSpace.equiv (Fin n) ℝ m.val ∈ latticePolytope γ := m.property
    rw [hpair]
    exact le_iSup (fun x : latticePolytope γ =>
      ((originalCoordinatePairing n x (EuclideanSpace.equiv (Fin n) ℝ y) : ℝ) : EReal))
      ⟨_, hm⟩
  · refine iSup_le fun m => ?_
    have hm : (EuclideanSpace.equiv (Fin n) ℝ).symm m.val ∈ polytopeToricMomentPolytope γ := by
      change EuclideanSpace.equiv (Fin n) ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm m.val) ∈
        latticePolytope γ
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact m.property
    calc ((originalCoordinatePairing n m.val (EuclideanSpace.equiv (Fin n) ℝ y) : ℝ) : EReal)
        = (((innerₗ (EuclideanSpace ℝ (Fin n))).flip
            ((EuclideanSpace.equiv (Fin n) ℝ).symm m.val) y : ℝ) : EReal) := by
          rw [hpair, ContinuousLinearEquiv.apply_symm_apply]
      _ ≤ _ := le_iSup (fun x : polytopeToricMomentPolytope γ =>
          (((innerₗ (EuclideanSpace ℝ (Fin n))).flip x y : ℝ) : EReal)) ⟨_, hm⟩

/-- `F_0 ∼ Supp_P`: the reference has bounded support growth (source `eq:F0def`). -/
theorem polytopeToricReference_singularityEquiv_support :
    SGPT.PSH.SingularityEquiv (fun x => (polytopeToricReference γ hs x : EReal))
      (support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (polytopeToricMomentPolytope γ)) := by
  have h := (originalCanonicalReference_mem_boundedGrowthClass γ hs).2
  rw [LinearMap.flip_flip] at h
  obtain ⟨h1, h2⟩ := (SGPT.PSH.singularityEquiv_iff _ _).mp h
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp h1
  obtain ⟨D, hD⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp h2
  refine (SGPT.PSH.singularityEquiv_iff _ _).mpr
    ⟨(SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨C, fun x => ?_⟩,
      (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr ⟨D, fun x => ?_⟩⟩
  · rw [polytopeToricReference_coe, support_polytopeToricMomentPolytope]
    exact hC _
  · rw [polytopeToricReference_coe, support_polytopeToricMomentPolytope]
    exact hD _

/-! ### Charts, boundary and action -/

/-- Every source atlas chart of `X` is a vertex chart, with whole target. -/
theorem polytopeToric_chart_target
    (e : (ofFixedModel n (PolytopeToricVariety γ hs)).Index) :
    ((ofFixedModel n (PolytopeToricVariety γ hs)).chart e).target = univ :=
  originalPolytopeNativeComplexChart_target γ hs e

/-- The toric boundary has holomorphic equations in every chart. -/
theorem hasAnalyticChartEquations_polytopeToricBoundary :
    (ofFixedModel n (PolytopeToricVariety γ hs)).HasAnalyticChartEquations
      (polytopeToricBoundary γ hs) := by
  intro e z _
  refine ⟨univ, isOpen_univ, mem_univ z, (polytopeToric_chart_target γ hs e).symm.subset,
    1, fun _ => originalPolytopeNativeBoundaryPolynomial n,
    fun _ => (differentiable_originalPolytopeNativeBoundaryPolynomial n).differentiableOn, ?_⟩
  intro y _
  have h := originalPolytopeNativeBoundary_all_chart_iff γ hs e y
  exact h.trans ⟨fun h0 _ => h0, fun h1 => h1 0⟩

/-- The toric boundary has empty interior (the torus is dense). -/
theorem interior_polytopeToricBoundary : interior (polytopeToricBoundary γ hs) = ∅ :=
  interior_eq_empty_iff_dense_compl.mpr (dense_originalPolytopeNativeTorus γ)

theorem mem_polytopeToricBoundary_compl_iff (p : PolytopeToricVariety γ hs) :
    p ∈ (polytopeToricBoundary γ hs)ᶜ ↔ ∃ a, polytopeToricEmbedding γ hs a = p :=
  mem_originalPolytopeNativeTorus_iff γ p

theorem polytopeToricEmbedding_mem_compl (a : Fin n → ℂˣ) :
    polytopeToricEmbedding γ hs a ∈ (polytopeToricBoundary γ hs)ᶜ :=
  (mem_polytopeToricBoundary_compl_iff γ hs _).mpr ⟨a, rfl⟩

theorem polytopeToricAction_embedding (a b : Fin n → ℂˣ) :
    polytopeToricAction γ hs a (polytopeToricEmbedding γ hs b) =
      polytopeToricEmbedding γ hs (a * b) :=
  originalPolytopeNativeAction_orbit γ a b

theorem polytopeToricAction_mul (a b : Fin n → ℂˣ) (p : PolytopeToricVariety γ hs) :
    polytopeToricAction γ hs (a * b) p =
      polytopeToricAction γ hs a (polytopeToricAction γ hs b p) :=
  originalPolytopeNativeAction_mul γ a b p

theorem polytopeToricAction_one (p : PolytopeToricVariety γ hs) :
    polytopeToricAction γ hs 1 p = p :=
  originalPolytopeNativeAction_one γ p

theorem isCompactTorusElement_inv {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a) :
    IsCompactTorusElement a⁻¹ := by
  intro j
  simp [ha j]

/-- An invariant function takes the value of the positive point with the same
tropicalization. -/
theorem PolytopeToricInvariant.embedding_eq {u : PolytopeToricVariety γ hs → EReal}
    (hu : PolytopeToricInvariant γ hs u) (a : Fin n → ℂˣ) :
    u (polytopeToricEmbedding γ hs a) =
      u (polytopeToricEmbedding γ hs (positiveTorusPoint (unitTorusLog a))) := by
  conv_lhs => rw [← torusAngularPart_mul_positiveTorusPoint a]
  rw [← polytopeToricAction_embedding]
  exact hu _ (isCompactTorusElement_torusAngularPart a) _

/-- Holomorphic compact-torus pullback preserves `ω`-psh functions (`ω` is `T_c`-invariant). -/
theorem isThetaPSH_comp_polytopeToricAction {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) u)
    {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs)
      (fun p => u (polytopeToricAction γ hs a p)) := by
  have hn := (isThetaPSH_iff_nativeThetaPotential (polytopeToricOmega γ hs) u).mp hu
  apply (isThetaPSH_iff_nativeThetaPotential (polytopeToricOmega γ hs) _).mpr
  have hne : LocallyNondegenerate (fun p => u (polytopeToricAction γ hs a p)) :=
    Pending.AdmissiblePresentationHolomorphicPullback.locallyNondegenerate_comp_of_isOpenMap
      (polytopeToricAction γ hs a).isOpenMap hn.2
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (polytopeToricAction γ hs a : PolytopeToricVariety γ hs → PolytopeToricVariety γ hs) :=
    contMDiff_originalPolytopeNativeAction γ hs a ∞
  have hpull := Pending.GlobalPotentialPullback.isThetaPshPotential_comp hf hn.1 hne
  have heq : SmoothRealForm.pullback hf (polytopeToricKahlerForm γ hs).val =
      (polytopeToricKahlerForm γ hs).val :=
    originalGuilleminClosedForm_compact_pullback_eq γ hs a ha
  change IsThetaPshPotential (polytopeToricKahlerForm γ hs).val _
  rw [← heq]
  exact hpull

/-- Upper bound of an `ω`-psh function on the compact manifold `X`. -/
theorem exists_upper_bound_polytopeToricPSH {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) u) :
    ∃ C : ℝ, ∀ p, u p ≤ (C : EReal) :=
  exists_real_upper_bound_of_upperSemicontinuous hu.upperSemicontinuous hu.1

/-! ### The vertex charts on the torus -/

/-- The source chart index of a vertex chart. -/
def polytopeToricVertexChart (v : latticePolytopeVertices γ) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).Index :=
  originalPolytopeNativeComplexChart γ hs v

theorem polytopeToricVertexChart_chart (v : latticePolytopeVertices γ) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).chart (polytopeToricVertexChart γ hs v) =
      originalPolytopeNativeModelChart γ hs v := rfl

/-- In the vertex chart at `v`, the Guillemin weight is a global potential of `ω`. -/
theorem polytopeToricOmega_coeff_vertexChart (v : latticePolytopeVertices γ) :
    EqOn (smoothDDC (originalGuilleminGeometricNativeWeight γ hs v))
      ((polytopeToricOmega γ hs).coeff (polytopeToricVertexChart γ hs v))
      ((ofFixedModel n (PolytopeToricVariety γ hs)).chart
        (polytopeToricVertexChart γ hs v)).target :=
  fun z _ => (originalGuilleminClosedForm_native_coeff γ hs v z).symm

/-- `ω`-psh functions have psh corrected potentials in each whole vertex chart. -/
theorem plurisubharmonicOn_polytopeToric_vertexChart {u : PolytopeToricVariety γ hs → EReal}
    (hu : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH (polytopeToricOmega γ hs) u)
    (v : latticePolytopeVertices γ) :
    PlurisubharmonicOn (fun z => u ((originalPolytopeNativeModelChart γ hs v).symm z) +
      (originalGuilleminGeometricNativeWeight γ hs v z : EReal)) univ := by
  have h := hu.preferred_chart_corrected (polytopeToricVertexChart γ hs v)
    (contDiff_originalGuilleminGeometricNativeWeight γ hs v).contDiffOn
    (polytopeToricOmega_coeff_vertexChart γ hs v)
  rwa [polytopeToric_chart_target] at h

/-- The vertex chart of a torus point reads its tropicalization through the edge basis. -/
theorem tropicalization_polytopeToricVertexChart_embedding (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) :
    tropicalization (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) =
      latticeBasisLogMap (originalPolytopeNativeBasis γ hs v) (unitTorusLog a) := by
  ext j
  rw [latticeBasisLogMap_apply]
  have hj : (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) j =
      (latticeCharacter (originalPolytopeNativeBasis γ hs v j) a : ℂ) :=
    originalPolytopeNativePiChart_orbit γ hs v a j
  rw [tropicalization_apply_eq_log_norm_sq, hj, latticeCharacter_log_norm_sq]
  rfl

/-- The boundary polynomial does not vanish exactly on the coordinate torus. -/
theorem originalPolytopeNativeBoundaryPolynomial_ne_zero_iff (w : ComplexModel n) :
    originalPolytopeNativeBoundaryPolynomial n w ≠ 0 ↔ w ∈ complexTorus n := by
  unfold originalPolytopeNativeBoundaryPolynomial complexTorus
  rw [Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, true_imp_iff, mem_ofPred_eq]
  exact Iff.rfl

/-- Points of the torus in vertex coordinates. -/
theorem exists_polytopeToricEmbedding_eq_chart_symm (v : latticePolytopeVertices γ)
    {w : ComplexModel n} (hw : w ∈ complexTorus n) :
    ∃ a, polytopeToricEmbedding γ hs a = (originalPolytopeNativeModelChart γ hs v).symm w := by
  have hb : originalPolytopeNativeBoundaryPolynomial n w ≠ 0 :=
    (originalPolytopeNativeBoundaryPolynomial_ne_zero_iff w).mpr hw
  exact (mem_originalPolytopeNativeTorus_iff γ _).mp
    ((originalPolytopeNativeTorus_chart_symm_iff γ hs v w).mpr hb)

theorem polytopeToricVertexChart_symm_mem_compl_iff (v : latticePolytopeVertices γ)
    (w : ComplexModel n) :
    (originalPolytopeNativeModelChart γ hs v).symm w ∈ (polytopeToricBoundary γ hs)ᶜ ↔
      w ∈ complexTorus n := by
  change (originalPolytopeNativeModelChart γ hs v).symm w ∈ originalPolytopeNativeTorus γ ↔ _
  rw [originalPolytopeNativeTorus_chart_symm_iff]
  exact originalPolytopeNativeBoundaryPolynomial_ne_zero_iff w

/-- Source `eq:FvarphidefGdef`: the convex profile `F_φ = f + F_0` of a function `φ` on `X`,
where `φ|_T = Trop^* f`; it is evaluated at the positive torus points. -/
def polytopeToricProfile (u : PolytopeToricVariety γ hs → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  u (polytopeToricEmbedding γ hs (positiveTorusPoint x)) + (polytopeToricReference γ hs x : EReal)

/-- Source `eq:FvarphidefGdef`: `G_φ = F_φ^*`. -/
def polytopeToricLegendre (u : PolytopeToricVariety γ hs → EReal) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  conjugate (innerₗ (EuclideanSpace ℝ (Fin n))) (polytopeToricProfile γ hs u)

/-- The vertex potential of `ω` at a torus point is `F_0 - ⟨v, ·⟩`. -/
theorem originalGuilleminGeometricNativeWeight_chart_embedding (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) :
    originalGuilleminGeometricNativeWeight γ hs v
        (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a)) =
      polytopeToricReference γ hs (unitTorusLog a) - latticeFunctional v.val (unitTorusLog a) := by
  have hs' : polytopeToricEmbedding γ hs a ∈ (originalPolytopeNativeModelChart γ hs v).source := by
    rw [originalPolytopeNativeModelChart_source]
    exact originalPolytopeNativeOrbitMap_mem_chart_source γ hs v a
  change originalGuilleminVertexPotential γ hs v ((originalPolytopeNativeModelChart γ hs v).symm
    (originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a))) = _
  rw [(originalPolytopeNativeModelChart γ hs v).left_inv hs']
  exact originalGuilleminVertexPotential_orbit_eq_reference γ hs v a

/-- Core chart identity: in the vertex chart at `v`, on the torus, the corrected
local potential of a function with torus-invariant values is the tropical pullback
of its profile composed with the inverse basis change, minus `⟨v, ·⟩`. -/
theorem polytopeToric_vertexChart_corrected_eq {u : PolytopeToricVariety γ hs → EReal}
    (hu : ∀ a, u (polytopeToricEmbedding γ hs a) =
      u (polytopeToricEmbedding γ hs (positiveTorusPoint (unitTorusLog a))))
    (v : latticePolytopeVertices γ) {w : ComplexModel n} (hw : w ∈ complexTorus n) :
    u ((originalPolytopeNativeModelChart γ hs v).symm w) +
        (originalGuilleminGeometricNativeWeight γ hs v w : EReal) =
      tropicalPullback (fun y => polytopeToricProfile γ hs u
          (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) y) +
        ((-latticeFunctional v.val
          (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) y) : ℝ) : EReal)) w := by
  obtain ⟨a, ha⟩ := exists_polytopeToricEmbedding_eq_chart_symm γ hs v hw
  have hwt : w ∈ (originalPolytopeNativeModelChart γ hs v).target := by
    rw [originalPolytopeNativeModelChart_target]; exact mem_univ w
  have hwa : originalPolytopeNativeModelChart γ hs v (polytopeToricEmbedding γ hs a) = w := by
    rw [ha]; exact (originalPolytopeNativeModelChart γ hs v).right_inv hwt
  have hlog : latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) (tropicalization w) =
      unitTorusLog a := by
    rw [← hwa, tropicalization_polytopeToricVertexChart_embedding,
      latticeBasisLogInverse_logMap]
  change u ((originalPolytopeNativeModelChart γ hs v).symm w) +
      (originalGuilleminGeometricNativeWeight γ hs v w : EReal) =
    polytopeToricProfile γ hs u
        (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) (tropicalization w)) +
      ((-latticeFunctional v.val
        (latticeBasisLogInverse (originalPolytopeNativeBasis γ hs v) (tropicalization w)) : ℝ) :
          EReal)
  rw [hlog, ← ha, ← hwa, originalGuilleminGeometricNativeWeight_chart_embedding,
    polytopeToricProfile, hu a, add_assoc, ← EReal.coe_add, sub_eq_add_neg]

end SGPT.Toric
