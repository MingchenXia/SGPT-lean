import SGPT.Okounkov.TranscendentalPole
import SGPT.Okounkov.TranscendentalExtensionStatement
import SGPT.Foundations.Analysis.Pending.EmbeddedFromResolution

/-!
# The pole along a submanifold in the form used by the extension theorem

Source: DRWNXZ, proof of Theorem 6.1 (the pole `F` of the submanifold, quoted from
Demailly--Păun Lemma 2.1); Xia, *Foundations of pluripotential theory*,
`lem:global-normal-pole`. Blueprint node `tok:ext-pole`, consumed by `tok:ct-key` and
`tok:ct-extension` (package EXT).

The package EXT states its pole input as `TranscendentalExtension.NormalPoleStatement`
(`IsNormalPole`: quasi-psh, `-∞` exactly on `Y`, continuous off `Y`, analytic singularities in
the chart sense `HasManifoldAnalyticSingularityType`, and the normal lower bound
`|w|² ≤ C e^F` in every system of normal coordinates). We prove it
(`normalPoleStatement`) with the pole `F = log U` of a concentration partition:

* `hasManifoldAnalyticSingularityType_of_hasAnalyticSingularitiesOfType`: a global analytic type
  `(c, 𝔞)` gives the chart-local analytic type;
* `interior_eq_empty_of_lt`: a closed connected submanifold of dimension `k < n` has empty
  interior;
* the normal flat coordinates lie in `𝓘_Y`, hence `|w|² ≤ C U = C e^F`
  (`exists_generatorNormSq_le_weight_of_mem`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalPole

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldConcentrationPotential

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- A global analytic type `(c, 𝔞)` (`F = c log ∑ |g_i|² + O(1)` near every point) gives the
analytic singularity type in every holomorphic chart. -/
theorem hasManifoldAnalyticSingularityType_of_hasAnalyticSingularitiesOfType {u : X → EReal}
    {c : ℚ} {𝔞 : GermIdeal n X} (h : HasAnalyticSingularitiesOfType (n := n) u c 𝔞) :
    HasManifoldAnalyticSingularityType (n := n) u := by
  obtain ⟨hc, -, hloc⟩ := h
  intro e z hz
  obtain ⟨U, hU, hxU, N, g, hg, -, R, C, hRC, heq⟩ := hloc (e.val.symm z)
  have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) := e.val.isOpen_inter_preimage_symm hU
  have hzO : z ∈ e.val.target ∩ e.val.symm ⁻¹' U := ⟨hz, hxU⟩
  refine ⟨c, N, fun j w => g j (e.val.symm w), Rat.cast_pos.mpr hc,
    ⟨_, hO, hzO, fun j w hw => ?_⟩, fun w => R (e.val.symm w), ⟨|C|, abs_nonneg _, ?_⟩, ?_⟩
  · exact (mdifferentiableAt_iff_differentiableAt.mp
      (((hg j _ hw.2).mdifferentiableAt (hU.mem_nhds hw.2)).comp w
        (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ, ComplexModel n)) e.property hw.1))).differentiableWithinAt
  · filter_upwards [hO.mem_nhds hzO] with w hw
    exact (hRC _ hw.2).trans (le_abs_self C)
  · filter_upwards [hO.mem_nhds hzO] with w hw
    exact heq _ hw.2

/-- A closed connected submanifold of dimension `k < n` has empty interior. -/
theorem interior_eq_empty_of_lt {Y : Set X} {k : ℕ} (hY : IsClosedConnectedSubmanifold n Y k)
    (hk : k < n) : interior Y = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hfull := EmbeddedFromResolution.regularAtDim_of_mem_nhds (n := n)
    (mem_interior_iff_mem_nhds.mp hx)
  have heq := RegularPointDimension.eq_of_regularAtDim (hY.2.2 x (interior_subset hx)) hfull
  omega

omit [IsComplexManifold n X] in
theorem isClosedSubmanifold_of_isClosedConnectedSubmanifold {Y : Set X} {k : ℕ}
    (hY : IsClosedConnectedSubmanifold n Y k) : IsClosedSubmanifold n Y :=
  ⟨hY.1, fun x hx => ⟨k, hY.2.2 x hx⟩⟩

/-- **`tok:ext-pole` for a connected closed submanifold of dimension `k < n`** (e.g. a member of
a smooth flag other than `X`). -/
theorem exists_submanifold_pole_of_isClosedConnectedSubmanifold [CompactSpace X]
    (omega : KahlerBackground n X) {Y : Set X} {k : ℕ} (hY : IsClosedConnectedSubmanifold n Y k)
    (hk : k < n) : ∃ F : X → EReal, IsSubmanifoldPole omega Y F :=
  exists_submanifold_pole n X omega Y (isClosedSubmanifold_of_isClosedConnectedSubmanifold hY)
    (interior_eq_empty_of_lt hY hk)

omit [IsComplexManifold n X] in
theorem normalPart_apply (k : ℕ) (z : ComplexModel n) (i : Fin n) :
    TranscendentalExtension.normalPart n k z i = if k ≤ i.1 then z i else 0 := by
  simp only [TranscendentalExtension.normalPart, PiLp.sub_apply, coordinateInclusion,
    coordinateProjection]
  by_cases hik : k ≤ i.1
  · simp [hik, show ¬ i.1 < k by omega]
  · simp [hik, show i.1 < k by omega]

/-- The normal flat coordinates of a flattening `G` of `Y`, padded by `0`. -/
def normalCoords {Y : Set X} {k : ℕ} (G : SubmanifoldChartedSpace.FlatData n k X Y)
    (i : Fin n) (x : X) : ℂ :=
  if k ≤ i.1 then G.flat (G.amb.val x) i else 0

omit [IsComplexManifold n X] in
theorem norm_normalPart_sq {Y : Set X} {k : ℕ} (G : SubmanifoldChartedSpace.FlatData n k X Y)
    (x : X) :
    ‖TranscendentalExtension.normalPart n k (G.flat (G.amb.val x))‖ ^ 2 =
      generatorNormSq (normalCoords G) x := by
  rw [EuclideanSpace.norm_sq_eq, generatorNormSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [normalPart_apply, normalCoords]

theorem normalCoords_mem_vanishingIdeal {Y : Set X} {k : ℕ}
    (G : SubmanifoldChartedSpace.FlatData n k X Y) {q : X} (hq : q ∈ G.ambSource) (i : Fin n) :
    (vanishingIdeal (n := n) Y).mem q (normalCoords G i) := by
  by_cases hik : k ≤ i.1
  · have hfun : normalCoords G i = fun x => G.flat (G.amb.val x) i := by
      funext x; simp [normalCoords, hik]
    rw [hfun]
    refine ⟨?_, ?_⟩
    · filter_upwards [G.isOpen_ambSource.mem_nhds hq] with y hy
      have hd : DifferentiableAt ℂ (fun w => G.flat w i) (G.amb.val y) :=
        (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt.comp _
          (G.differentiableOn_flat.differentiableAt (G.flat.open_source.mem_nhds hy.2))
      exact hd.mdifferentiableAt.comp y
        (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) G.amb.property hy.1)
    · filter_upwards [G.isOpen_ambSource.mem_nhds hq] with y hy hyY
      exact (G.mem_iff y hy.1 hy.2).mp hyY i hik
  · have hfun : normalCoords G i = fun _ => 0 := by
      funext x; simp [normalCoords, hik]
    rw [hfun]
    exact ⟨holomorphicAt_const 0, Eventually.of_forall fun _ _ => rfl⟩

/-- **The pole input of the extension theorem** (`TranscendentalExtension.NormalPoleStatement`,
blueprint `tok:ext-pole`): every proper connected closed submanifold of a compact Kähler
manifold carries a normal pole. -/
theorem normalPoleStatement : TranscendentalExtension.NormalPoleStatement.{u} := by
  intro n X _ _ _ _ omega Y k hY hk
  have hYs := isClosedSubmanifold_of_isClosedConnectedSubmanifold hY
  have hYint := interior_eq_empty_of_lt hY hk
  obtain ⟨ι, _, ⟨P⟩⟩ :=
    exists_of_isCoherent (VanishingIdealCoherent.isCoherent_vanishingIdeal hYs)
  obtain ⟨A, hA, hpsh⟩ := exists_isThetaPshPotential_concentrationPole P hYs.1 hYint omega
  refine ⟨concentrationPole P,
    { thetaPsh := ⟨A, hA.le, hpsh⟩
      eq_bot_iff := concentrationPole_eq_bot_iff P hYs.1
      continuousOn := (continuous_concentrationPole P).continuousOn
      analytic := hasManifoldAnalyticSingularityType_of_hasAnalyticSingularitiesOfType
        (hasAnalyticSingularitiesOfType_concentrationPole P hYs)
      lower := fun G q _ hq => ?_ }⟩
  obtain ⟨C, hC, hCy⟩ :=
    exists_generatorNormSq_le_weight_of_mem P (normalCoords_mem_vanishingIdeal G hq)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCy] with x hx
  rw [norm_normalPart_sq, TranscendentalExtension.expPotential, exp_concentrationPole,
    ENNReal.toReal_ofReal (P.weight_nonneg x)]
  exact hx

end SGPT.Okounkov.TranscendentalPole
