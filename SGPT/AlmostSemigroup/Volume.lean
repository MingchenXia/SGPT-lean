import SGPT.AlmostSemigroup.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The lattice-subset volume and its Lipschitz estimate

SGPT Appendix C defines semigroup volume as the real limit superior of the
normalized slice cardinalities. On all lattice subsets of the source's fixed
cone this formula equals distance to the empty set. This produces the actual
volume inequality `lma:vollipapp`, continuity, and monotonicity without assuming
a volume comparison or an asymptotic counting limit. The Kaveh–Khovanskii
divisible-subsequence limit and the Lebesgue/Okounkov interpretation are separate.
-/

namespace SGPT.AlmostSemigroup.ConeSubset

open Filter

variable {n : ℕ} {C : AdmissibleCone n}

/-- The empty lattice subset of the fixed cone. -/
def empty : ConeSubset C := ⟨∅, Set.empty_subset _⟩

@[simp] theorem slices_empty (k : ℕ) : (empty : ConeSubset C).slices k = ∅ := by
  ext x
  rw [mem_slices]
  change (x, (k : ℤ)) ∈ (∅ : Set ((Fin n → ℤ) × ℤ)) ↔ x ∈ (∅ : Finset _)
  simp

/-- Source volume uses the cardinality of the actual finite degree slice. -/
noncomputable def normalizedCardinality (S : ConeSubset C) (k : ℕ) : ℝ :=
  (k : ℝ)⁻¹ ^ n * (S.slices k).card

/-- The limit-superior volume formula from Appendix C, extended to all cone subsets. -/
noncomputable def volume (S : ConeSubset C) : ℝ :=
  limsup S.normalizedCardinality atTop

/-- A normalized cardinality is exactly discrepancy from the empty slice. -/
theorem normalizedCardinality_eq_discrepancy_empty (S : ConeSubset C) :
    S.normalizedCardinality = normalizedDiscrepancy n S.slices
      (empty : ConeSubset C).slices := by
  funext k
  simp [normalizedCardinality, normalizedDiscrepancy, discrepancy, Finset.symmDiff_def]

/-- The counting formula is exactly the source pseudometric's distance to the empty set. -/
theorem volume_eq_distance_empty (S : ConeSubset C) :
    volume S = distance S (empty : ConeSubset C) := by
  rw [volume, normalizedCardinality_eq_discrepancy_empty]
  rfl

/-- SGPT `lma:vollipapp`, strengthened from additive semigroups to all cone subsets. -/
theorem abs_volume_sub_le_distance (S T : ConeSubset C) :
    |volume S - volume T| ≤ distance S T := by
  simpa only [volume_eq_distance_empty, dist_eq_distance] using
    abs_dist_sub_le S T (empty : ConeSubset C)

/-- The source volume formula is a genuine one-Lipschitz map on the actual pseudometric space. -/
theorem lipschitzWith_volume : LipschitzWith 1 (volume (C := C)) := by
  apply LipschitzWith.mk_one
  intro S T
  simpa only [Real.dist_eq, dist_eq_distance] using abs_volume_sub_le_distance S T

/-- The one-Lipschitz volume formula is continuous. -/
theorem continuous_volume : Continuous (volume (C := C)) :=
  lipschitzWith_volume.continuous

/-- Convergence of actual cone subsets implies convergence of their volumes. -/
theorem tendsto_volume {ι : Type*} {l : Filter ι} (S : ι → ConeSubset C) (S₀ : ConeSubset C)
    (hS : Tendsto S l (nhds S₀)) : Tendsto (fun i => volume (S i)) l (nhds (volume S₀)) :=
  continuous_volume.continuousAt.tendsto.comp hS

/-- The volume is nonnegative because it equals a pseudometric distance. -/
theorem volume_nonneg (S : ConeSubset C) : 0 ≤ volume S := by
  rw [volume_eq_distance_empty, ← dist_eq_distance]
  exact dist_nonneg

@[simp] theorem volume_empty : volume (empty : ConeSubset C) = 0 := by
  rw [volume_eq_distance_empty, ← dist_eq_distance]
  exact dist_self _

/-- Inclusion of lattice subsets gives inclusion of each actual finite slice. -/
theorem slices_subset_of_subset (S T : ConeSubset C) (hST : S.val ⊆ T.val) (k : ℕ) :
    S.slices k ⊆ T.slices k := by
  intro x hx
  exact (mem_slices T k x).mpr (hST ((mem_slices S k x).mp hx))

/-- The normalized slice-cardinality formula is monotone under lattice-subset inclusion. -/
theorem normalizedCardinality_mono (S T : ConeSubset C) (hST : S.val ⊆ T.val) (k : ℕ) :
    S.normalizedCardinality k ≤ T.normalizedCardinality k := by
  have hc : ((S.slices k).card : ℝ) ≤ (T.slices k).card := by
    exact_mod_cast Finset.card_le_card (slices_subset_of_subset S T hST k)
  exact mul_le_mul_of_nonneg_left hc
    (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) n)

/-- Actual normalized slice cardinalities are nonnegative. -/
theorem normalizedCardinality_nonneg (S : ConeSubset C) (k : ℕ) :
    0 ≤ S.normalizedCardinality k := by
  rw [normalizedCardinality_eq_discrepancy_empty]
  exact normalizedDiscrepancy_nonneg n _ _ k

/-- The original cone hypotheses bound the volume's actual normalized-cardinality sequence. -/
theorem bounded_normalizedCardinality (S : ConeSubset C) :
    IsBoundedUnder (· ≤ ·) atTop S.normalizedCardinality := by
  rw [normalizedCardinality_eq_discrepancy_empty]
  exact bounded_normalizedDiscrepancy_of_growth n _ _ S.hasPolynomialGrowth
    (empty : ConeSubset C).hasPolynomialGrowth

/-- Inclusion gives volume monotonicity on all cone subsets, including the source closure. -/
theorem volume_mono (S T : ConeSubset C) (hST : S.val ⊆ T.val) : volume S ≤ volume T := by
  exact limsup_le_limsup
    (Eventually.of_forall (normalizedCardinality_mono S T hST))
    (isCoboundedUnder_le_of_le atTop (normalizedCardinality_nonneg S))
    T.bounded_normalizedCardinality

/-- The actual semigroups inside the fixed cone, as a subset of its lattice-subset space. -/
def semigroupLocus (C : AdmissibleCone n) : Set (ConeSubset C) :=
  {S | ∀ x ∈ S.val, ∀ y ∈ S.val, x + y ∈ S.val}

/-- SGPT's closure of the semigroup locus in the actual discrepancy pseudometric topology. -/
def semigroupClosure (C : AdmissibleCone n) : Set (ConeSubset C) :=
  closure (semigroupLocus C)

/-- The explicit limit-superior formula already gives the source's Lipschitz extension.
The formula restricts to the original semigroup volume because that volume is
defined by the same limit superior. No divisible-subsequence limit is assumed. -/
theorem lipschitzOnWith_volume_semigroupClosure :
    LipschitzOnWith 1 (volume (C := C)) (semigroupClosure C) :=
  lipschitzWith_volume.lipschitzOnWith

/-- Uniqueness of the source extension on its closure, stated for ambient representatives.
Continuity on the closure and agreement on the semigroup locus are exactly the
extension conditions; density follows from the definition of the closure. -/
theorem eqOn_volume_semigroupClosure (g : ConeSubset C → ℝ)
    (hg : ContinuousOn g (semigroupClosure C))
    (heq : Set.EqOn g volume (semigroupLocus C)) :
    Set.EqOn g volume (semigroupClosure C) := by
  exact heq.of_subset_closure hg continuous_volume.continuousOn subset_closure (fun _ h => h)

/-- SGPT `lma:volcompaapp`, for the explicit continuous extension to semigroup closure. -/
theorem volume_mono_on_semigroupClosure (S T : semigroupClosure C)
    (hST : S.val.val ⊆ T.val.val) : volume S.val ≤ volume T.val :=
  volume_mono S.val T.val hST

/-- The inclusion of actual semigroups in their pseudometric closure. -/
def semigroupInclusion (C : AdmissibleCone n) : semigroupLocus C → semigroupClosure C :=
  Set.inclusion subset_closure

/-- Density needed for uniqueness is proved from the actual topological closure. -/
theorem denseRange_semigroupInclusion : DenseRange (semigroupInclusion C) :=
  (denseRange_inclusion_iff (show semigroupLocus C ⊆ semigroupClosure C from subset_closure)).mpr
    (fun _ h => h)

/-- The source volume extension as a map on the actual closure subtype. -/
noncomputable def closureVolume (S : semigroupClosure C) : ℝ := volume S.val

/-- The explicit closure-subtype extension is one-Lipschitz. -/
theorem lipschitzWith_closureVolume : LipschitzWith 1 (closureVolume (C := C)) := by
  apply LipschitzWith.mk_one
  intro S T
  change |volume S.val - volume T.val| ≤ distance S.val T.val
  exact abs_volume_sub_le_distance S.val T.val

/-- The extension agrees with the source semigroup volume on its original domain. -/
theorem closureVolume_semigroupInclusion (S : semigroupLocus C) :
    closureVolume (semigroupInclusion C S) = volume S.val := rfl

/-- The volume extension is unique among continuous maps on the actual closure subtype. -/
theorem closureVolume_unique (g : semigroupClosure C → ℝ) (hg : Continuous g)
    (heq : ∀ S : semigroupLocus C, g (semigroupInclusion C S) = volume S.val) :
    g = closureVolume := by
  apply denseRange_semigroupInclusion.equalizer hg lipschitzWith_closureVolume.continuous
  funext S
  exact heq S

/-- SGPT `eq:volexapp`: existence and uniqueness of the actual one-Lipschitz extension. -/
theorem existsUnique_lipschitz_volume_extension :
    ∃! g : semigroupClosure C → ℝ, LipschitzWith 1 g ∧
      ∀ S : semigroupLocus C, g (semigroupInclusion C S) = volume S.val := by
  refine ⟨closureVolume, ⟨lipschitzWith_closureVolume, closureVolume_semigroupInclusion⟩, ?_⟩
  intro g hg
  exact closureVolume_unique g hg.1.continuous hg.2

/-- SGPT `lma:volcompaapp` for the actual closure-subtype extension. -/
theorem closureVolume_mono (S T : semigroupClosure C) (hST : S.val.val ⊆ T.val.val) :
    closureVolume S ≤ closureVolume T :=
  volume_mono S.val T.val hST

end SGPT.AlmostSemigroup.ConeSubset
