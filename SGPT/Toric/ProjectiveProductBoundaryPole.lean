import SGPT.Toric.ProjectiveProductNativeGeometry
import SGPT.Toric.ProjectiveGlobalTropicalData
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped Topology ContDiff Manifold ProductComplexManifold
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
/-- The actual original coordinate torus in the compact projective product. -/
def projectiveProductTorus : (n : ℕ) → Set (projectiveProductSpace n)
  | 0 => univ
  | n + 1 => projectiveProductTorus n ×ˢ projectiveToricBoundaryᶜ

/-- The actual coordinate homeomorphism reads the original nonzero finite factors. -/
theorem projectiveProductTorus_coordinates : (n : ℕ) → (p : projectiveProductSpace n) →
    p ∈ projectiveProductTorus n ↔
      ∀ i : Fin n, projectiveProductCoordinates n p i ∉ projectiveToricBoundary
  | 0, _ => by simp [projectiveProductTorus]
  | n + 1, p => by
    change (p.1 ∈ projectiveProductTorus n ∧ p.2 ∉ projectiveToricBoundary) ↔
      ∀ i : Fin (n + 1), (Fin.snoc (projectiveProductCoordinates n p.1) p.2 :
        Fin (n + 1) → P1) i ∉ projectiveToricBoundary
    rw [projectiveProductTorus_coordinates n p.1]
    constructor
    · intro h i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using h.2
      · simpa only [Fin.snoc_castSucc] using h.1 j
    · intro h
      exact ⟨fun j => by simpa only [Fin.snoc_castSucc] using h j.castSucc,
        by simpa only [Fin.snoc_last] using h (Fin.last n)⟩

/-- Openness belongs to the actual quotient/product topology. -/
theorem isOpen_projectiveProductTorus : (n : ℕ) → IsOpen (projectiveProductTorus n)
  | 0 => isOpen_univ
  | n + 1 => (isOpen_projectiveProductTorus n).prod isClosed_projectiveToricBoundary.isOpen_compl

/-- Every actual original product neighborhood meets the coordinate torus. -/
theorem dense_projectiveProductTorus : (n : ℕ) → Dense (projectiveProductTorus n)
  | 0 => dense_univ
  | n + 1 => (dense_projectiveProductTorus n).prod
      (interior_eq_empty_iff_dense_compl.mp interior_projectiveToricBoundary)

private theorem complexTorus_split (n : ℕ) (z : ComplexModel (n + 1)) :
    z ∈ complexTorus (n + 1) ↔
      ((prodModelEquiv n 1).symm z).1 ∈ complexTorus n ∧
      ((prodModelEquiv n 1).symm z).2 ∈ complexTorus 1 := by
  constructor
  · intro h
    exact ⟨fun i => h i.castSucc, fun i => h (Fin.natAdd n i)⟩
  · intro h i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h.2 0
    · exact h.1 j

/-- The literal preferred affine chart restricted to the complex torus has
exactly the original coordinate-torus source. -/
theorem projectiveProductTorus_chart_source : (n : ℕ) →
    (projectiveProductNativeChart n (fun _ => false)).val.source ∩
      (projectiveProductNativeChart n (fun _ => false)).val ⁻¹' complexTorus n =
        projectiveProductTorus n
  | 0 => by
    ext z
    simp only [projectiveProductTorus, mem_univ, iff_true, mem_inter_iff, mem_preimage]
    refine ⟨?_, fun i => Fin.elim0 i⟩
    have hz : z = (0 : ComplexModel 0) := by ext i; exact Fin.elim0 i
    rw [hz]
    exact mem_complexChartAt_source (0 : ComplexModel 0)
  | n + 1 => by
    ext p
    change p ∈ (prodChart (projectiveProductNativeChart n (fun _ => false)).val
        (projectiveNativeChart false).val).source ∩
      (prodChart (projectiveProductNativeChart n (fun _ => false)).val
        (projectiveNativeChart false).val) ⁻¹' complexTorus (n + 1) ↔ _
    simp only [mem_inter_iff, mem_preimage, prodChart_source, mem_prod, prodChart_apply]
    rw [complexTorus_split, ContinuousLinearEquiv.symm_apply_apply]
    have hline : p.2 ∈ (projectiveNativeChart false).val.source ∧
        (projectiveNativeChart false).val p.2 ∈ complexTorus 1 ↔
        p.2 ∉ projectiveToricBoundary := by
      constructor
      · intro h
        have hf := (projectiveToricBoundary_chart_off_iff false _).mpr h.2
        change (projectiveNativeChart false).val.symm
          ((projectiveNativeChart false).val p.2) ∉ projectiveToricBoundary at hf
        rwa [(projectiveNativeChart false).val.left_inv h.1] at hf
      · intro h
        exact ⟨projectiveToricBoundary_compl_subset_finite_source h,
          projectiveFiniteCoordinate_mem_torus_of_off_boundary h⟩
    have hfirst : p.1 ∈ (projectiveProductNativeChart n (fun _ => false)).val.source ∧
        (projectiveProductNativeChart n (fun _ => false)).val p.1 ∈ complexTorus n ↔
        p.1 ∈ projectiveProductTorus n := by
      rw [← projectiveProductTorus_chart_source n]
      rfl
    change _ ↔ p.1 ∈ projectiveProductTorus n ∧ p.2 ∉ projectiveToricBoundary
    tauto

/-- This independent original section-pole sum has no dependence on a PSH input. -/
def projectiveProductBoundaryPole : (n : ℕ) → projectiveProductSpace n → EReal
  | 0, _ => 0
  | n + 1, p => projectiveProductBoundaryPole n p.1 + projectiveBoundaryPole p.2

private theorem projectiveBoundaryPole_ne_bot_iff (p : P1) :
    projectiveBoundaryPole p ≠ ⊥ ↔ p ∉ projectiveToricBoundary := by
  constructor
  · intro h hp
    rcases hp with hp | hp
    · subst p
      simp [projectiveBoundaryPole, projectiveLogSingularity_origin,
        projectiveOppositeLogSingularity_origin] at h
    · subst p
      simp [projectiveBoundaryPole, projectiveLogSingularity_infinity,
        projectiveOppositeLogSingularity_infinity] at h
  · intro h
    have hs := projectiveToricBoundary_compl_subset_finite_source h
    have hz := projectiveFiniteCoordinate_mem_torus_of_off_boundary h
    change (projectiveNativeChart false).val p ∈ complexTorus 1 at hz
    have hc := projectiveBoundaryPole_corrected_chart false ((projectiveNativeChart false).val p)
    rw [(projectiveNativeChart false).val.left_inv hs,
      logNormSq_of_ne_zero (hz 0)] at hc
    have hfin : projectiveBoundaryPole p +
        ((2 * projectiveFSPotential ((projectiveNativeChart false).val p) : ℝ) : EReal) ≠ ⊥ := by
      rw [hc]
      exact EReal.coe_ne_bot _
    exact (EReal.add_ne_bot_iff.mp hfin).1

private theorem projectiveProductBoundaryPole_ne_bot_iff : (n : ℕ) →
    (p : projectiveProductSpace n) →
    projectiveProductBoundaryPole n p ≠ ⊥ ↔ p ∈ projectiveProductTorus n
  | 0, _ => by simp [projectiveProductBoundaryPole, projectiveProductTorus]
  | n + 1, p => by
    rw [projectiveProductBoundaryPole, EReal.add_ne_bot_iff,
      projectiveProductBoundaryPole_ne_bot_iff n p.1, projectiveBoundaryPole_ne_bot_iff]
    rfl

private theorem quasiPlurisubharmonicAt_add {n : ℕ}
    {u v : ComplexModel n → EReal} {z : ComplexModel n}
    (hu : QuasiPlurisubharmonicAt u z) (hv : QuasiPlurisubharmonicAt v z) :
    QuasiPlurisubharmonicAt (fun y => u y + v y) z := by
  obtain ⟨p, h, hp, hh, hu⟩ := hu
  obtain ⟨q, k, hq, hk, hv⟩ := hv
  refine ⟨fun y => p y + q y, fun y => h y + k y, hp.add hq, ?_, ?_⟩
  · filter_upwards [hh, hk] with y hy ky
    exact hy.add ky
  · filter_upwards [hu, hv] with y uy vy
    rw [uy, vy, EReal.coe_add]
    ac_rfl

private theorem manifoldQuasi_projectiveProductBoundaryPole : (n : ℕ) →
    ManifoldQuasiPlurisubharmonic (n := n) (projectiveProductBoundaryPole n)
  | 0 => manifoldQuasiPlurisubharmonic_const 0
  | n + 1 => by
    have hfst := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
      (ProductComplexManifold.contMDiff_fst (n := n) (m := 1)
        (X := projectiveProductSpace n) (Y := P1))
      (manifoldQuasi_projectiveProductBoundaryPole n)
    have hsnd := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
      (ProductComplexManifold.contMDiff_snd (n := n) (m := 1)
        (X := projectiveProductSpace n) (Y := P1))
      isGlobalQuasiPshPotential_projectiveBoundaryPole.1
    intro e z hz
    exact quasiPlurisubharmonicAt_add (hfst e z hz) (hsnd e z hz)

/-- Genuine raw holomorphic pullback and local PSH/smooth addition are made
nondegenerate by the produced dense original coordinate torus. -/
theorem isGlobalQuasiPshPotential_projectiveProductBoundaryPole (n : ℕ) :
    IsGlobalQuasiPshPotential (n := n) (projectiveProductBoundaryPole n) := by
  refine ⟨manifoldQuasi_projectiveProductBoundaryPole n, ?_⟩
  intro x U hU hx
  obtain ⟨y, hyT, hyU⟩ := (dense_projectiveProductTorus n).exists_mem_open hU ⟨x, hx⟩
  exact ⟨y, hyU, (projectiveProductBoundaryPole_ne_bot_iff n y).mpr hyT⟩

/-- The literal extended correction preserves every original coordinate pole. -/
theorem projectiveProductBoundaryPole_corrected_chart : (n : ℕ) → (ε : Fin n → Bool) →
    (z : ComplexModel n) →
    projectiveProductBoundaryPole n ((projectiveProductNativeChart n ε).val.symm z) +
      ((2 * projectiveProductFSPotential n z : ℝ) : EReal) =
        ∑ i : Fin n, logNormSq (z i)
  | 0, _, _ => by simp [projectiveProductBoundaryPole, projectiveProductFSPotential]
  | n + 1, ε, z => by
    let a := ((prodModelEquiv n 1).symm z).1
    let b := ((prodModelEquiv n 1).symm z).2
    have hρ : projectiveProductFSPotential (n + 1) z =
        projectiveProductFSPotential n a + projectiveFSPotential b := by
      simp only [projectiveProductFSPotential, Fin.sum_univ_castSucc, projectiveFSPotential_eq]
      rfl
    have h2 : ((2 * (projectiveProductFSPotential n a + projectiveFSPotential b) : ℝ) : EReal) =
        ((2 * projectiveProductFSPotential n a : ℝ) : EReal) +
          ((2 * projectiveFSPotential b : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      ring
    change (projectiveProductBoundaryPole n
      ((projectiveProductNativeChart n (Fin.init ε)).val.symm a) +
        projectiveBoundaryPole ((projectiveNativeChart (ε (Fin.last n))).val.symm b)) + _ = _
    rw [hρ, h2]
    calc
      _ = (projectiveProductBoundaryPole n
          ((projectiveProductNativeChart n (Fin.init ε)).val.symm a) +
            ((2 * projectiveProductFSPotential n a : ℝ) : EReal)) +
          (projectiveBoundaryPole ((projectiveNativeChart (ε (Fin.last n))).val.symm b) +
            ((2 * projectiveFSPotential b : ℝ) : EReal)) := by ac_rfl
      _ = (∑ i : Fin n, logNormSq (a i)) + logNormSq (b 0) := by
        rw [projectiveProductBoundaryPole_corrected_chart n (Fin.init ε) a,
          projectiveBoundaryPole_corrected_chart]
      _ = ∑ i : Fin (n + 1), logNormSq (z i) := by
        rw [Fin.sum_univ_castSucc]
        rfl

/-- The actual independent pole locus is exactly the original torus boundary. -/
theorem projectiveProductBoundaryPole_poleLocus (n : ℕ) :
    {p | projectiveProductBoundaryPole n p = ⊥} = (projectiveProductTorus n)ᶜ := by
  ext p
  simpa only [mem_ofPred_eq, mem_compl_iff, not_not] using
    not_congr (projectiveProductBoundaryPole_ne_bot_iff n p)

/-- The true native NP construction gives zero mass to the actual original
product boundary for every genuine product-FS PSH potential. -/
theorem projectiveProductMixedMeasure_compl_torus {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u) :
    GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => (projectiveProductFSBackground n).form) (fun _ => u)
      (fun _ => hu.1) (projectiveProductTorus n)ᶜ = 0 := by
  rw [← projectiveProductBoundaryPole_poleLocus]
  exact GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_quasiPsh
    (fun _ => hu.1) (isGlobalQuasiPshPotential_projectiveProductBoundaryPole n)

end SGPT.Toric
