import SGPT.Toric.ProjectiveLineNativePotential
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
import SGPT.Foundations.Analysis.FirstPass.LocalPotentials

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.PSH
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped Topology ContDiff Manifold ProductComplexManifold
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The actual original product of `n` projective lines, starting with its genuine
zero-dimensional Euclidean point. -/
abbrev projectiveProductSpace : ℕ → Type
  | 0 => ComplexModel 0
  | n + 1 => projectiveProductSpace n × P1

instance projectiveProductTopologicalSpace : (n : ℕ) → TopologicalSpace (projectiveProductSpace n)
  | 0 => inferInstanceAs (TopologicalSpace (ComplexModel 0))
  | n + 1 => letI := projectiveProductTopologicalSpace n
    inferInstanceAs (TopologicalSpace (projectiveProductSpace n × P1))

instance projectiveProductChartedSpace : (n : ℕ) →
    ChartedSpace (ComplexModel n) (projectiveProductSpace n)
  | 0 => inferInstanceAs (ChartedSpace (ComplexModel 0) (ComplexModel 0))
  | n + 1 => letI := projectiveProductChartedSpace n
    ProductComplexManifold.chartedSpace (n := n) (m := 1)

instance projectiveProductComplexManifold : (n : ℕ) → IsComplexManifold n (projectiveProductSpace n)
  | 0 => inferInstanceAs (IsComplexManifold 0 (ComplexModel 0))
  | n + 1 => by
    have := projectiveProductComplexManifold n
    exact ProductComplexManifold.isComplexManifold (n := n) (m := 1)

instance projectiveProductMeasurableSpace : (n : ℕ) → MeasurableSpace (projectiveProductSpace n)
  | 0 => inferInstanceAs (MeasurableSpace (ComplexModel 0))
  | n + 1 => letI := projectiveProductMeasurableSpace n
    inferInstanceAs (MeasurableSpace (projectiveProductSpace n × P1))

instance projectiveProductBorelSpace : (n : ℕ) → BorelSpace (projectiveProductSpace n)
  | 0 => inferInstanceAs (BorelSpace (ComplexModel 0))
  | n + 1 => by
    have := projectiveProductBorelSpace n
    exact inferInstanceAs (BorelSpace (projectiveProductSpace n × P1))

instance projectiveProductCompactSpace : (n : ℕ) → CompactSpace (projectiveProductSpace n)
  | 0 => by
    have hz (z : ComplexModel 0) : z = 0 := by ext i; exact Fin.elim0 i
    have h : (univ : Set (ComplexModel 0)) = {0} := by ext z; simp [hz z]
    exact ⟨by rw [h]; exact isCompact_singleton⟩
  | n + 1 => by
    have := projectiveProductCompactSpace n
    exact inferInstanceAs (CompactSpace (projectiveProductSpace n × P1))

/-- Actual original coordinates identify this native recursive product with the
literal finite Cartesian product, through its genuine product topology. -/
def projectiveProductCoordinates : (n : ℕ) → projectiveProductSpace n ≃ₜ (Fin n → P1)
  | 0 => {
    toFun := fun _ i => Fin.elim0 i
    invFun := fun _ => (0 : ComplexModel 0)
    left_inv := fun z => by ext i; exact Fin.elim0 i
    right_inv := fun f => by funext i; exact Fin.elim0 i
    continuous_toFun := continuous_pi (fun i => Fin.elim0 i)
    continuous_invFun := continuous_const }
  | n + 1 => {
    toFun := fun p => Fin.snoc (projectiveProductCoordinates n p.1) p.2
    invFun := fun f => ((projectiveProductCoordinates n).symm (Fin.init f), f (Fin.last n))
    left_inv := fun p => by simp
    right_inv := fun f => by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.init]
    continuous_toFun := by
      apply continuous_pi
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using continuous_snd
      · have hc : Continuous (fun p : projectiveProductSpace n × P1 =>
            (projectiveProductCoordinates n p.1) j) :=
          (continuous_apply j).comp
            ((projectiveProductCoordinates n).continuous.comp continuous_fst)
        simpa only [Fin.snoc_castSucc, projectiveProductTopologicalSpace] using hc
    continuous_invFun := by
      apply Continuous.prodMk
      · apply (projectiveProductCoordinates n).symm.continuous.comp
        apply continuous_pi
        intro i
        exact continuous_apply i.castSucc
      · exact continuous_apply (Fin.last n) }

private def zeroDimensionalKahler : KahlerBackground 0 (ComplexModel 0) := by
  refine ⟨0, ?_⟩
  refine ⟨?_, ?_⟩
  · intro e z hz
    refine ⟨?_, ?_⟩
    · intro v w
      simp
    · intro v hv
      exact False.elim (hv (by ext i; exact Fin.elim0 i))
  · exact (0 : ClosedRealOneOneForm 0 (ComplexModel 0)).property.1

/-- The actual original product FS background is built from genuine holomorphic
projection pullbacks, with its zero-dimensional form and source scale unchanged. -/
def projectiveProductFSBackground : (n : ℕ) → KahlerBackground n (projectiveProductSpace n)
  | 0 => zeroDimensionalKahler
  | n + 1 => prodKahlerBackground (projectiveProductFSBackground n) projectiveNativeFSBackground
/-- Every original binary product chart is an actual member of the native atlas. -/
def projectiveProductNativeChart : (n : ℕ) → (Fin n → Bool) →
    ComplexChart n (projectiveProductSpace n)
  | 0, _ => complexChartAt (0 : ComplexModel 0)
  | n + 1, ε =>
    ⟨prodChart (projectiveProductNativeChart n (Fin.init ε)).val
      (projectiveNativeChart (ε (Fin.last n))).val,
      Set.mem_image2_of_mem (projectiveProductNativeChart n (Fin.init ε)).property
        (projectiveNativeChart (ε (Fin.last n))).property⟩

private theorem projectiveNativeChart_target_univ (b : Bool) :
    (projectiveNativeChart b).val.target = univ := by
  simp [projectiveNativeChart, projectiveModelChart, projectiveQuotientScalarChart_target]

/-- All original binary product charts retain the full Euclidean target. -/
theorem projectiveProductNativeChart_target : (n : ℕ) → (ε : Fin n → Bool) →
    (projectiveProductNativeChart n ε).val.target = univ
  | 0, _ => rfl
  | n + 1, ε => by
    simp only [projectiveProductNativeChart, prodChart_target,
      projectiveProductNativeChart_target n (Fin.init ε),
      projectiveNativeChart_target_univ, univ_prod_univ, preimage_univ]

/-- The literal original FS correction, including its empty coordinate sum. -/
def projectiveProductFSPotential (n : ℕ) (z : ComplexModel n) : ℝ :=
  ∑ i : Fin n, Real.log (1 + Complex.normSq (z i))

private theorem projectiveProductFSPotential_succ (n : ℕ) (z : ComplexModel (n + 1)) :
    projectiveProductFSPotential (n + 1) z =
      projectiveProductFSPotential n ((prodModelEquiv n 1).symm z).1 +
      projectiveFSPotential ((prodModelEquiv n 1).symm z).2 := by
  simp only [projectiveProductFSPotential, Fin.sum_univ_castSucc, projectiveFSPotential_eq]
  rfl

private theorem projectiveNativeFS_localPotential (b : Bool) :
    IsSmoothLocalPotential projectiveNativeFSBackground.form.val
      (projectiveNativeChart b) univ projectiveFSPotential := by
  refine ⟨isOpen_univ, ?_, contDiff_projectiveFSPotential.contDiffOn, ?_⟩
  · rw [projectiveNativeChart_target_univ]
  · intro z hz
    rfl

private theorem product_fst_potentialDomain (n : ℕ) (ε : Fin (n + 1) → Bool) :
    LocalPotentialPullback.potentialDomain Prod.fst
      (projectiveProductNativeChart (n + 1) ε)
      (projectiveProductNativeChart n (Fin.init ε)) univ = univ := by
  ext z
  constructor
  · intro _
    exact mem_univ z
  · intro _
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · rw [projectiveProductNativeChart_target]
      exact mem_univ z
    · change (projectiveProductNativeChart n (Fin.init ε)).val.symm
          ((prodModelEquiv n 1).symm z).1 ∈
        (projectiveProductNativeChart n (Fin.init ε)).val.source
      apply (projectiveProductNativeChart n (Fin.init ε)).val.map_target
      rw [projectiveProductNativeChart_target]
      exact mem_univ _

private theorem product_snd_potentialDomain (n : ℕ) (ε : Fin (n + 1) → Bool) :
    LocalPotentialPullback.potentialDomain Prod.snd
      (projectiveProductNativeChart (n + 1) ε)
      (projectiveNativeChart (ε (Fin.last n))) univ = univ := by
  ext z
  constructor
  · intro _
    exact mem_univ z
  · intro _
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · rw [projectiveProductNativeChart_target]
      exact mem_univ z
    · change (projectiveNativeChart (ε (Fin.last n))).val.symm
          ((prodModelEquiv n 1).symm z).2 ∈
        (projectiveNativeChart (ε (Fin.last n))).val.source
      apply (projectiveNativeChart (ε (Fin.last n))).val.map_target
      rw [projectiveNativeChart_target_univ]
      exact mem_univ _

private theorem product_fst_coordinateMap (n : ℕ) (ε : Fin (n + 1) → Bool) :
    coordinateMap Prod.fst (projectiveProductNativeChart (n + 1) ε)
      (projectiveProductNativeChart n (Fin.init ε)) =
      fun z => ((prodModelEquiv n 1).symm z).1 := by
  funext z
  change (projectiveProductNativeChart n (Fin.init ε)).val
      ((projectiveProductNativeChart n (Fin.init ε)).val.symm
        ((prodModelEquiv n 1).symm z).1) = _
  apply (projectiveProductNativeChart n (Fin.init ε)).val.right_inv
  rw [projectiveProductNativeChart_target]
  exact mem_univ _

private theorem product_snd_coordinateMap (n : ℕ) (ε : Fin (n + 1) → Bool) :
    coordinateMap Prod.snd (projectiveProductNativeChart (n + 1) ε)
      (projectiveNativeChart (ε (Fin.last n))) =
      fun z => ((prodModelEquiv n 1).symm z).2 := by
  funext z
  change (projectiveNativeChart (ε (Fin.last n))).val
      ((projectiveNativeChart (ε (Fin.last n))).val.symm
        ((prodModelEquiv n 1).symm z).2) = _
  apply (projectiveNativeChart (ε (Fin.last n))).val.right_inv
  rw [projectiveNativeChart_target_univ]
  exact mem_univ _

/-- The literal coordinate sum is a genuine smooth local potential for the
full original native FS two-form on every full binary chart target. -/
theorem projectiveProductFSPotential_localPotential : (n : ℕ) → (ε : Fin n → Bool) →
    IsSmoothLocalPotential (projectiveProductFSBackground n).form.val
      (projectiveProductNativeChart n ε) univ (projectiveProductFSPotential n)
  | 0, ε => by
    have hzero : projectiveProductFSPotential 0 = fun _ => 0 := by
      funext z
      simp [projectiveProductFSPotential]
    rw [hzero]
    exact LocalPotentials.localPotential_zero (projectiveProductNativeChart 0 ε) isOpen_univ
      (by rw [projectiveProductNativeChart_target])
  | n + 1, ε => by
    have hfst := LocalPotentialPullback.isSmoothLocalPotential_pullback
      (ProductComplexManifold.contMDiff_fst (n := n) (m := 1))
      (projectiveProductNativeChart (n + 1) ε)
      (projectiveProductFSPotential_localPotential n (Fin.init ε))
    have hsnd := LocalPotentialPullback.isSmoothLocalPotential_pullback
      (ProductComplexManifold.contMDiff_snd (n := n) (m := 1))
      (projectiveProductNativeChart (n + 1) ε)
      (projectiveNativeFS_localPotential (ε (Fin.last n)))
    rw [product_fst_potentialDomain, product_fst_coordinateMap] at hfst
    rw [product_snd_potentialDomain, product_snd_coordinateMap] at hsnd
    have hsum := LocalPotentials.localPotential_add
      (a := ClosedRealOneOneForm.pullback
        (ProductComplexManifold.contMDiff_fst (n := n) (m := 1))
        (projectiveProductFSBackground n).form)
      (b := ClosedRealOneOneForm.pullback
        (ProductComplexManifold.contMDiff_snd (n := n) (m := 1))
        projectiveNativeFSBackground.form) hfst hsnd
    have hfun : (fun z : ComplexModel (n + 1) =>
        projectiveProductFSPotential n ((prodModelEquiv n 1).symm z).1 +
          projectiveFSPotential ((prodModelEquiv n 1).symm z).2) =
        projectiveProductFSPotential (n + 1) :=
      funext (fun z => (projectiveProductFSPotential_succ n z).symm)
    change IsSmoothLocalPotential _ _ univ
      (fun z => projectiveProductFSPotential n ((prodModelEquiv n 1).symm z).1 +
        projectiveFSPotential ((prodModelEquiv n 1).symm z).2) at hsum
    rw [hfun] at hsum
    exact hsum

end SGPT.Toric
