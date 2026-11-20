import SGPT.Okounkov.FlagValuationGenericCenters
import SGPT.Okounkov.FlagLifting
import SGPT.GAGA.SmoothFlagsScheme
import SGPT.Projective.Sections
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage

/-!
# Homogeneous equations are determined by their germ on an original flag member

The actual polynomial zero set is analytic on projective space. Its pullback
to the genuine connected smooth original flag member is analytic. The native
analytic identity theorem therefore upgrades germ vanishing to global
vanishing on that same member, without a resolution or irreducibility input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl

/-- A homogeneous projective equation vanishes independently of its literal
nonzero representative, including its normalized original affine lift. -/
theorem eval_rep_eq_zero_iff_genFun {M : Type*} {N d : ℕ}
    (Ψ : M → ComplexProjectiveSpace N) (i : Fin (N + 1))
    {p : M} (hp : Ψ p ∈ (affineChart i).source)
    {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous d) :
    MvPolynomial.eval (Ψ p).rep P = 0 ↔ genFun Ψ i P p = 0 := by
  have hre : Ψ p = mk (affineLift i (affineChart i (Ψ p))) (affineLift_ne_zero _ _) :=
    ((affineChart i).left_inv hp).symm
  obtain ⟨c, hc, hrep⟩ := rep_smul (Ψ p) (affineLift_ne_zero _ _) hre
  rw [hrep, eval_smul_of_isHomogeneous hP]
  change c ^ d * MvPolynomial.eval (affineLift i (affineChart i (Ψ p))) P = 0 ↔
    MvPolynomial.eval (affineLift i (affineChart i (Ψ p))) P = 0
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero d hc))

/-- The actual global homogeneous polynomial zero set is a genuine analytic
subset of the original projective manifold. -/
theorem isComplexAnalyticSubset_homogeneousPolynomialZeroSet {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous d) :
    IsComplexAnalyticSubset (n := N) {p : ComplexProjectiveSpace N | MvPolynomial.eval p.rep P = 0} := by
  intro p
  let i := chartIndex p
  refine ⟨{
    generatorCount := 1
    generator := fun _ z => MvPolynomial.eval (affineLift i z) P
    coordinateNeighborhood := (complexChartAt (n := N) p).val.target
    isOpen_coordinateNeighborhood := (complexChartAt (n := N) p).val.open_target
    center_mem_coordinateNeighborhood := (complexChartAt (n := N) p).val.map_source
      (mem_complexChartAt_source p)
    coordinateNeighborhood_subset_target := subset_rfl
    generator_holomorphic := fun _ =>
      (differentiable_chartGenerators i (fun _ : Fin 1 => P) 0).differentiableOn
    zeroLocus := ?_ }⟩
  intro q hq _
  have hiq : q ∈ (affineChart i).source := hq
  change MvPolynomial.eval q.rep P = 0 ↔
    ∀ _ : Fin 1, MvPolynomial.eval (affineLift i ((affineChart i) q)) P = 0
  have hh := eval_rep_eq_zero_iff_genFun (id : ComplexProjectiveSpace N → _) i hiq hP
  change MvPolynomial.eval q.rep P = 0 ↔
    MvPolynomial.eval (affineLift i ((affineChart i) q)) P = 0 at hh
  simpa only [Fin.forall_fin_one] using hh

/-- For every literal original connected smooth flag member, a homogeneous
equation vanishes globally if and only if its actual normalized Chow
function belongs to the original member ideal at the original endpoint. -/
theorem originalFlag_genFun_mem_iff_global_polynomial_zero {n N d : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (Ψ : F.carrier → ComplexProjectiveSpace N) (hΨ : IsHolomorphicEmbedding (n := n) Ψ)
    (k : ℕ) (hk : k ≤ n) (i : Fin (N + 1)) (hi : Ψ x.1 ∈ (affineChart i).source)
    {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous d) :
    (vanishingIdeal (n := n) (F.flag ⟨k, Nat.lt_succ_of_le hk⟩)).mem x.1 (genFun Ψ i P) ↔
      ∀ y ∈ F.flag ⟨k, Nat.lt_succ_of_le hk⟩, MvPolynomial.eval (Ψ y).rep P = 0 := by
  let j : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hx : x.1 ∈ F.flag j := F.smooth.2.1 (Fin.le_last j) x.property
  have hnear : ∀ᶠ y in 𝓝 x.1, Ψ y ∈ (affineChart i).source :=
    hΨ.continuous.continuousAt.eventually ((affineChart i).open_source.mem_nhds hi)
  constructor
  · intro hv
    let : ChartedSpace (ComplexModel (n - (j : ℕ))) (F.flag j) := F.componentCharts j
    have : IsComplexManifold (n - (j : ℕ)) (F.flag j) := F.componentComplex j
    have : ConnectedSpace (F.flag j) := isConnected_iff_connectedSpace.mp (F.smooth.2.2 j).2.1
    let xp : F.flag j := ⟨x.1, hx⟩
    let A : Set (F.flag j) := {y | MvPolynomial.eval (Ψ y.1).rep P = 0}
    have hinc : ContMDiff 𝓘(ℂ, ComplexModel (n - (j : ℕ))) 𝓘(ℂ, ComplexModel n) ∞
        (Subtype.val : F.flag j → F.carrier) :=
      SubmanifoldChartedSpace.contMDiff_val (Nat.sub_le n j) (F.smooth.2.2 j).2.2
    have hA : IsComplexAnalyticSubset (n := n - (j : ℕ)) A :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage
        ((SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding hΨ).comp hinc)
        (isComplexAnalyticSubset_homogeneousPolynomialZeroSet hP)
    have hxA : xp ∈ interior A := by
      apply mem_interior_iff_mem_nhds.mpr
      filter_upwards [continuous_subtype_val.continuousAt.eventually hv.2,
        continuous_subtype_val.continuousAt.eventually hnear] with y hy hyi
      exact (eval_rep_eq_zero_iff_genFun Ψ i hyi hP).mpr (hy y.property)
    have hAeq := hA.eq_univ_of_interior_nonempty ⟨xp, hxA⟩
    intro y hy
    have hmem : (⟨y, hy⟩ : F.flag j) ∈ A := by rw [hAeq]; exact mem_univ _
    exact hmem
  · intro hglobal
    refine ⟨holomorphicAt_genFun hΨ hi P, ?_⟩
    filter_upwards [hnear] with y hy
    intro hyF
    exact (eval_rep_eq_zero_iff_genFun Ψ i hy hP).mp (hglobal y hyF)

end SGPT.Okounkov
