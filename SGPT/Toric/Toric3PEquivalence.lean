import SGPT.Toric.BigToricConvexBodies
import SGPT.Toric.BigToricAmple
import SGPT.Toric.BigToric2MetricExistence
import SGPT.Toric.PolytopeToricNewtonBody
import SGPT.Convex.GrowthSum

/-!
# The `P`-order of toric potentials of arbitrary mass

Source `chapter_toric_big.tex`, `cor:PequivtorD` (equivalence (1) ⇔ (3) without the
positive-mass hypothesis) and `cor:bij_conv_torpsh` (well-definedness and injectivity of
`φ ↦ Δ(θ, φ)` on all `P`-equivalence classes).

The source proves the zero-mass case by perturbing `L` to `L + m⁻¹ H` with an ample toric
divisor `H` and using `lma:grad_img_sum`.  We use the same idea with `m = 1` and `H = D_P`
(the ample divisor of the Delzant polytope `P` defining the model `X = X_P`): the tensor
product of the metric `h` on `O(D)` with the Guillemin metric on `O(D_P)` is a `T_c`-invariant
metric `h ⊗ h_P` on `O(D + D_P)` with curvature `θ + ω` (`BigToricMetric.addGuillemin`).
Since `ω` is Kähler, every `φ ∈ PSH_tor(X, θ)` lies in `PSH_tor(X, θ + ω)` with positive mass,
its profile is `F_φ + F_0`, and by `lma:grad_img_sum`

`Δ(θ + ω, φ) = Δ(θ, φ) + P`.

The global `P`-order is computed in any positive background (`sourcePOrder_iff_positive_background`),
so `φ ≼_P ψ ⇔ Δ(θ, φ) + P ⊆ Δ(θ, ψ) + P ⇔ Δ(θ, φ) ⊆ Δ(θ, ψ)` (cancellation of the bounded
summand `P` in a Minkowski sum with a closed convex set, by separation).  No integrality issue
arises, so the rescaling by `m` of the source is not needed.

## Main results

* `BigToricMetric.addGuillemin`: the metric `h ⊗ h_P` on `O(D + D_P)`, curvature `θ + ω`;
* `BigToricMetric.newtonBody_addGuillemin`: `Δ(θ + ω, φ) = Δ(θ, φ) + P`;
* `subset_of_add_subset_add`: Minkowski cancellation `A + C ⊆ B + C ⇒ A ⊆ B`;
* `BigToricMetric.sourcePOrder_iff_newtonBody_subset_all`: source `cor:PequivtorD`, (1) ⇔ (3),
  for all `φ, ψ ∈ PSH_tor(X, θ)`;
* `BigToricMetric.sourcePEquivalent_iff_newtonBody_eq_all`: `φ ∼_P ψ ⇔ Δ(θ, φ) = Δ(θ, ψ)`
  (source `cor:bij_conv_torpsh`, well-definedness and injectivity on all classes).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators Pointwise

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Additivity of the lattice pairing in the character. -/
theorem latticeFunctional_add_apply (a b : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    latticeFunctional (a + b) x = latticeFunctional a x + latticeFunctional b x := by
  simp only [latticeFunctional_apply, Pi.add_apply, Int.cast_add, add_mul,
    Finset.sum_add_distrib]

/-- `P_D + P_E ⊆ P_{D+E}`. -/
theorem add_subset_toricDivisorPolytope_add (D E : ToricDivisor γ hs) :
    toricDivisorPolytope D + toricDivisorPolytope E ⊆ toricDivisorPolytope (D + E) := by
  rintro _ ⟨m, hm, m', hm', rfl⟩ ρ
  have h1 := hm ρ
  have h2 := hm' ρ
  simp only [Pi.add_apply, Int.cast_add, map_add]
  linarith

omit [Fintype K] [Nonempty K] in
/-- Minkowski cancellation: if `A + C ⊆ B + C` with `B` closed convex and `C` bounded and
nonempty, then `A ⊆ B`. -/
theorem subset_of_add_subset_add {A B C : Set (EuclideanSpace ℝ (Fin n))}
    (hB : IsClosed B) (hBc : Convex ℝ B) (hC : Bornology.IsBounded C) (hCne : C.Nonempty)
    (hsub : A + C ⊆ B + C) : A ⊆ B := by
  intro a ha
  by_contra haB
  obtain ⟨f, u, hfB, hfa⟩ := geometric_hahn_banach_closed_point hBc hB haB
  have hbdd : BddAbove (f '' C) := by
    obtain ⟨R, hR⟩ := hC.subset_closedBall 0
    refine ⟨‖f‖ * R, ?_⟩
    rintro _ ⟨c, hc, rfl⟩
    have hcR : ‖c‖ ≤ R := by simpa using hR hc
    calc f c ≤ ‖f c‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖c‖ := f.le_opNorm c
      _ ≤ ‖f‖ * R := by gcongr
  set s := sSup (f '' C)
  have hne : (f '' C).Nonempty := hCne.image f
  obtain ⟨_, ⟨c, hc, rfl⟩, hcs⟩ := exists_lt_of_lt_csSup hne
    (show s - (f a - u) < s by linarith)
  obtain ⟨b, hb, c', hc', hbc⟩ := hsub ⟨a, ha, c, hc, rfl⟩
  have hfc' : f c' ≤ s := le_csSup hbdd ⟨c', hc', rfl⟩
  change b + c' = a + c at hbc
  have hsum : f b + f c' = f a + f c := by rw [← map_add, ← map_add, hbc]
  linarith [hfB b hb]

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The tensor product `h ⊗ h_P` of the metric `h` on `O(D)` with the Guillemin metric on
`O(D_P)`: a `T_c`-invariant metric on `O(D + D_P)` with weights `ψ_v + ψ^P_v` and curvature
form `θ + ω`. -/
def addGuillemin : BigToricMetric (D + polytopeToricAmpleDivisor γ hs) where
  form := h.form + polytopeToricKahlerForm γ hs
  weight v z := h.weight v z + (guilleminBigToricMetric γ hs).weight v z
  smooth v := (h.smooth v).add ((guilleminBigToricMetric γ hs).smooth v)
  coeff v z := by
    change h.form.val.coeff (polytopeToricVertexChart γ hs v) z +
      (guilleminBigToricMetric γ hs).form.val.coeff (polytopeToricVertexChart γ hs v) z = _
    rw [h.coeff v z, (guilleminBigToricMetric γ hs).coeff v z]
    exact (smoothDDC_add isOpen_univ (h.smooth v).contDiffOn
      ((guilleminBigToricMetric γ hs).smooth v).contDiffOn (mem_univ z)).symm
  invariant v a ha z := by
    simp only [h.invariant v a ha z, (guilleminBigToricMetric γ hs).invariant v a ha z]
  transition v w a := by
    rw [toricCartierDatum_add, toricCartierDatum_add, latticeFunctional_add_apply,
      latticeFunctional_add_apply]
    linarith [h.transition v w a, (guilleminBigToricMetric γ hs).transition v w a]

theorem addGuillemin_form : h.addGuillemin.form = h.form + polytopeToricKahlerForm γ hs := rfl

/-- `F_{θ+ω} = F_θ + F_0`. -/
theorem addGuillemin_potential (x : EuclideanSpace ℝ (Fin n)) :
    h.addGuillemin.potential x = h.potential x + polytopeToricReference γ hs x := by
  rw [← guilleminBigToricMetric_potential γ hs]
  simp only [potential, addGuillemin, toricCartierDatum_add, latticeFunctional_add_apply]
  ring

/-- `PSH_tor(X, θ) ⊆ PSH_tor(X, θ + ω)`. -/
theorem mem_PSHTor_addGuillemin {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    u ∈ h.addGuillemin.PSHTor := by
  refine ⟨?_, hu.2⟩
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  exact Pending.LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1)
    (polytopeToricKahlerBackground γ hs).isSemipositive

/-- The profile in the background `θ + ω` is `F_φ + F_0`. -/
theorem addGuillemin_profile {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.addGuillemin.profile u =
      fun x => ((h.realProfile u x + polytopeToricReference γ hs x : ℝ) : EReal) := by
  funext x
  have hx := congrFun (h.realProfile_mem hu).2 x
  rw [profile] at hx ⊢
  rw [h.addGuillemin_potential, EReal.coe_add, ← add_assoc, hx, EReal.coe_add]

/-- The Newton body of the zero potential for the Guillemin metric: `closure ∇F_0(N_ℝ) = P`. -/
theorem closure_rawSubgradientImage_reference :
    closure (rawSubgradientImage (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun x => (polytopeToricReference γ hs x : EReal))) = polytopeToricMomentPolytope γ := by
  rw [← polytopeToricProfile_zero,
    ← polytopeToricNewtonBody_eq_closure_rawSubgradientImage γ hs (zero_mem_polytopeToricPSH γ hs),
    polytopeToricNewtonBody_zero]

/-- `F_0` is convex. -/
theorem convexOn_polytopeToricReference :
    ConvexOn ℝ univ (polytopeToricReference γ hs) := by
  have h0 := (guilleminBigToricMetric γ hs).realProfile_mem (zero_mem_polytopeToricPSH γ hs)
  have heq : (guilleminBigToricMetric γ hs).realProfile (fun _ => (0 : EReal)) =
      polytopeToricReference γ hs := by
    funext x
    simp [realProfile, guilleminBigToricMetric_profile, polytopeToricProfile_zero]
  rw [← heq]
  exact h0.1.1

variable (hP : (toricDivisorPolytope D).Nonempty)
include hP

/-- `Δ(θ + ω, φ) = Δ(θ, φ) + P` (source `lma:grad_img_sum`, used in the proof of
`cor:PequivtorD`). -/
theorem newtonBody_addGuillemin {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    h.addGuillemin.newtonBody u = h.newtonBody u + polytopeToricMomentPolytope γ := by
  have hf : ConvexOn ℝ univ (h.realProfile u) := (h.realProfile_mem hu).1.1
  have hbdd : Bornology.IsBounded (effectiveDomain (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun x => (h.realProfile u x : EReal)))) := by
    have hG := h.legendre_mem_closedProperOnBody hP hu
    have hleg : conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun x => (h.realProfile u x : EReal)) = h.legendre u := by
      rw [legendre, (h.realProfile_mem hu).2]
    rw [hleg]
    refine (isCompact_toricDivisorPolytope D).isBounded.subset fun m hm => ?_
    by_contra hmP
    exact (ne_of_lt hm) (hG.2.2 m hmP)
  rw [newtonBody, h.addGuillemin_profile hu,
    closure_rawSubgradientImage_add_coe _ hf convexOn_polytopeToricReference hbdd,
    closure_rawSubgradientImage_reference, newtonBody, (h.realProfile_mem hu).2]

/-- Source `cor:PequivtorD`, (1) ⇔ (3), for ALL `φ, ψ ∈ PSH_tor(X, θ)` (no mass hypothesis):
`φ ≼_P ψ ⇔ Δ(θ, φ) ⊆ Δ(θ, ψ)`. -/
theorem sourcePOrder_iff_newtonBody_subset_all {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) :
    GlobalPComparison.sourcePOrder (n := n) u v ↔ h.newtonBody u ⊆ h.newtonBody v := by
  have hP' : (toricDivisorPolytope (D + polytopeToricAmpleDivisor γ hs)).Nonempty := by
    obtain ⟨m, hm⟩ := hP
    obtain ⟨m', hm'⟩ := nonempty_polytopeToricMomentPolytope γ
    rw [← toricDivisorPolytope_ampleDivisor γ hs] at hm'
    exact ⟨m + m', add_subset_toricDivisorPolytope_add D _ ⟨m, hm, m', hm', rfl⟩⟩
  have hu' := h.mem_PSHTor_addGuillemin hu
  have hv' := h.mem_PSHTor_addGuillemin hv
  have hun : IsThetaPshPotential h.form.val u :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1
  have hvn : IsThetaPshPotential h.form.val v :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm v).mp hv.1
  have hupos : 0 < h.addGuillemin.MA hu' univ := by
    change Pending.DiagonalMass.HasPositivePotentialMass
      (h.form + (polytopeToricKahlerBackground γ hs).form) u _
    simpa only [one_smul] using
      Pending.SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul
        (polytopeToricKahlerBackground γ hs) hun zero_lt_one
  have hvpos : 0 < h.addGuillemin.MA hv' univ := by
    change Pending.DiagonalMass.HasPositivePotentialMass
      (h.form + (polytopeToricKahlerBackground γ hs).form) v _
    simpa only [one_smul] using
      Pending.SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul
        (polytopeToricKahlerBackground γ hs) hvn zero_lt_one
  rw [h.addGuillemin.sourcePOrder_iff_newtonBody_subset hP' hu' hv' hupos hvpos,
    h.newtonBody_addGuillemin hP hu, h.newtonBody_addGuillemin hP hv]
  obtain ⟨-, hcv, hconv, -⟩ := h.newtonBody_properties hP hv
  constructor
  · exact subset_of_add_subset_add hcv.isClosed hconv
      (isCompact_polytopeToricMomentPolytope γ).isBounded (nonempty_polytopeToricMomentPolytope γ)
  · intro hsub
    exact add_subset_add_right hsub

/-- Source `cor:PequivtorD` / `cor:bij_conv_torpsh` for ALL toric potentials:
`φ ∼_P ψ ⇔ Δ(θ, φ) = Δ(θ, ψ)`; i.e. `[φ]_P ↦ Δ(θ, φ)` is well defined and injective on
`PSH_tor(X, θ)/∼_P`. -/
theorem sourcePEquivalent_iff_newtonBody_eq_all {u v : PolytopeToricVariety γ hs → EReal}
    (hu : u ∈ h.PSHTor) (hv : v ∈ h.PSHTor) :
    GlobalPComparison.sourcePEquivalent (n := n) u v ↔ h.newtonBody u = h.newtonBody v := by
  change GlobalPComparison.sourcePOrder (n := n) u v ∧
    GlobalPComparison.sourcePOrder (n := n) v u ↔ _
  rw [h.sourcePOrder_iff_newtonBody_subset_all hP hu hv,
    h.sourcePOrder_iff_newtonBody_subset_all hP hv hu]
  exact ⟨fun h' => Subset.antisymm h'.1 h'.2, fun h' => ⟨h'.le, h'.ge⟩⟩

end BigToricMetric

end SGPT.Toric
