import SGPT.Foundations.Analysis.Pending.IncreasingTruncationLimit
import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes
import Mathlib.Topology.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Layercake

set_option autoImplicit false

/-!
# Total non-pluripolar mass along increasing sequences

The diagonal non-pluripolar mass of the regularized limit of an increasing sequence
of theta-PSH potentials on a compact complex manifold is at most the supremum of the
masses of the sequence (`diagonalPotentialMass_le_iSup_of_monotone`; Xia,
Corollary 2.4.1, `xia-sgpt:page-0075`, in the inequality used for (3.6)).

The proof is local-to-global.  In a chart with a smooth local potential, the global
measures are the transported local truncation limits of the corrected potentials,
and the corrected sequence is increasing with regularized limit the corrected limit;
the local semicontinuity theorem of `Pending.IncreasingTruncationLimit` then
bounds the measure of the limit on open subsets of the chart.  A continuous partition
of unity, the layer-cake formula and Fatou's lemma turn local bounds on open sets
into the bound on total mass (`measure_univ_le_liminf_of_local`).  No Kähler
background, finiteness or regularity of the measures is used.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.IncreasingLimitMass

/-- In `ℝ≥0∞`, the lower limit is superadditive. -/
theorem ENNReal.liminf_add_liminf_le {a b : ℕ → ℝ≥0∞} :
    liminf a atTop + liminf b atTop ≤ liminf (fun j => a j + b j) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat]
  rw [ENNReal.iSup_add_iSup_of_monotone]
  · exact iSup_mono fun k => le_iInf₂ fun j hj =>
      add_le_add (iInf₂_le j hj) (iInf₂_le j hj)
  · exact fun k l hkl => iInf₂_mono' fun j hj => ⟨j, hkl.trans hj, le_rfl⟩
  · exact fun k l hkl => iInf₂_mono' fun j hj => ⟨j, hkl.trans hj, le_rfl⟩

theorem ENNReal.sum_liminf_le {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ≥0∞) :
    ∑ i ∈ s, liminf (a i) atTop ≤ liminf (fun j => ∑ i ∈ s, a i j) atTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans ENNReal.liminf_add_liminf_le

/-- If a measure is, on the open subsets of a neighborhood of every point, below
the lower limit of a sequence of measures, then so is its total mass.  The proof
uses a continuous partition of unity, the layer-cake formula and Fatou's lemma, so
no regularity or finiteness of the measures is needed. -/
theorem measure_univ_le_liminf_of_local {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (ν : ℕ → Measure X)
    (h : ∀ x : X, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧
      ∀ G : Set X, IsOpen G → G ⊆ O → μ G ≤ liminf (fun j => ν j G) atTop) :
    μ univ ≤ liminf (fun j => ν j univ) atTop := by
  classical
  choose O hO hxO hlsc using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun x _ => mem_iUnion.mpr ⟨x, hxO x⟩)
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : t => O i) (fun i => hO i) (by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩)
  have hsum : ∀ (ρ : Measure X), ρ univ = ∑ i : t, ∫⁻ x, ENNReal.ofReal (f i x) ∂ρ := by
    intro ρ
    rw [← lintegral_finsetSum _ (fun i _ =>
      (f i).continuous.measurable.ennreal_ofReal)]
    rw [← lintegral_one]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => f.nonneg i x)]
    have h1 := f.sum_eq_one (mem_univ x)
    rw [finsum_eq_sum_of_fintype] at h1
    rw [h1, ENNReal.ofReal_one]
  have hlayer : ∀ (ρ : Measure X) (i : t), ∫⁻ x, ENNReal.ofReal (f i x) ∂ρ =
      ∫⁻ s in Ioi (0 : ℝ), ρ {x | s < f i x} := fun ρ i =>
    lintegral_eq_lintegral_meas_lt ρ (ae_of_all _ (f.nonneg i))
      (f i).continuous.measurable.aemeasurable
  have hlocal : ∀ (i : t) (s : ℝ), 0 < s →
      μ {x | s < f i x} ≤ liminf (fun j => ν j {x | s < f i x}) atTop := by
    intro i s hs
    refine hlsc i _ (isOpen_lt continuous_const (f i).continuous) fun x hx => hf i ?_
    exact subset_tsupport _ (ne_of_gt (hs.trans hx))
  rw [hsum μ]
  calc ∑ i : t, ∫⁻ x, ENNReal.ofReal (f i x) ∂μ
      ≤ ∑ i : t, liminf (fun j => ∫⁻ x, ENNReal.ofReal (f i x) ∂(ν j)) atTop := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hlayer μ i]
        simp_rw [hlayer _ i]
        calc ∫⁻ s in Ioi (0 : ℝ), μ {x | s < f i x}
            ≤ ∫⁻ s in Ioi (0 : ℝ), liminf (fun j => ν j {x | s < f i x}) atTop :=
              setLIntegral_mono' measurableSet_Ioi fun s hs => hlocal i s hs
          _ ≤ liminf (fun j => ∫⁻ s in Ioi (0 : ℝ), ν j {x | s < f i x}) atTop :=
              lintegral_liminf_le' fun j => (Antitone.measurable (f := fun s : ℝ =>
                ν j {x | s < f i x}) fun a b hab =>
                measure_mono fun x hx => lt_of_le_of_lt hab hx).aemeasurable
    _ ≤ liminf (fun j => ∑ i : t, ∫⁻ x, ENNReal.ofReal (f i x) ∂(ν j)) atTop :=
        ENNReal.sum_liminf_le _ _
    _ = liminf (fun j => ν j univ) atTop := by simp_rw [← hsum]

section Manifold

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
open GlobalNonPluripolar DiagonalMass MixedNonPluripolar IncreasingTruncationLimit

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The diagonal patch of one potential over a fixed chart, domain and local
potential. -/
def diagonalPatch {theta : ClosedRealOneOneForm n M} {w : M → EReal}
    (hw : IsThetaPshPotential theta.val w) (e : ComplexChart n M)
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential theta.val e W ρ) :
    Patch (fun _ : Fin n => theta) (fun _ => w) where
  chart := e
  domain := ⟨W, hρ.1⟩
  domain_le_target := hρ.2.1
  potential := fun _ => ρ
  localPotential := fun _ => hρ
  plurisubharmonic := fun _ =>
    chartCorrectedFamily_plurisubharmonicOn (F := {w})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hw) e hρ _ ⟨w, mem_singleton _, rfl⟩

/-- Near every point, the diagonal measure of the regularized limit of an
increasing sequence of normalized potentials is, on open sets, below the lower
limit of the measures of the sequence. -/
theorem exists_nhds_diagonalPotentialMeasure_le_liminf
    {theta : ClosedRealOneOneForm n M} (u : ℕ → M → EReal)
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hmono : Monotone u)
    (hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, u j))) (x : M) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∀ G : Set M, IsOpen G → G ⊆ O →
      diagonalPotentialMeasure theta (uscRegularization (⨆ j, u j)) hU G ≤
        liminf (fun j => diagonalPotentialMeasure theta (u j) (hu j) G) atTop := by
  set U := uscRegularization (⨆ j, u j) with hUdef
  let e : ComplexChart n M := complexChartAt x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨W, ρ, hzW, hρ⟩ :=
    hU.1.hasSmoothLocalPotentials e (e.val x) (e.val.map_source hx)
  let PU := diagonalPatch hU e hρ
  refine ⟨PU.source, PU.source.isOpen, ⟨hx, hzW⟩, fun G hG hGO => ?_⟩
  have hρc : ∀ y ∈ W, ContinuousAt ρ y := fun y hy =>
    ((hρ.2.2.1 y hy).contDiffAt (hρ.1.mem_nhds hy)).continuousAt
  -- Global measures on `G` are local measures on the chart image.
  have hglobal : ∀ {w : M → EReal} (hw : IsThetaPshPotential theta.val w),
      diagonalPotentialMeasure theta w hw G =
        mixedTruncationLimitMeasure (diagonalPatch hw e hρ).domain
          (diagonalPatch hw e hρ).corrected (diagonalPatch hw e hρ).plurisubharmonic
          (e.val '' G) := by
    intro w hw
    have hGs : G ∩ ((diagonalPatch hw e hρ).source : Set M) = G :=
      inter_eq_left.mpr hGO
    calc diagonalPotentialMeasure theta w hw G
        = (diagonalPotentialMeasure theta w hw).restrict
            ((diagonalPatch hw e hρ).source : Set M) G := by
          rw [Measure.restrict_apply' (diagonalPatch hw e hρ).source.isOpen.measurableSet,
            hGs]
      _ = patchMeasure (diagonalPatch hw e hρ) G := by
          rw [diagonalPotentialMeasure, globalMixedMeasure_restrict_patch]
      _ = _ := by
          rw [patchMeasure, Patch.pushMeasure_apply_image, hGs]
          rfl
  rw [hglobal hU]
  simp_rw [hglobal (hu _)]
  let v : ℕ → ComplexModel n → EReal := fun j y => chartFunction (u j) e y + (ρ y : EReal)
  have hsup : (⨆ j, v j) = fun y => chartFunction (⨆ j, u j) e y + (ρ y : EReal) := by
    funext y
    simp only [iSup_apply, chartFunction, v]
    exact iSup_add_coe (fun j => u j (e.val.symm y)) (ρ y)
  have hpsh : ∀ {w : M → EReal}, IsThetaPshPotential theta.val w →
      PlurisubharmonicOn (fun y => chartFunction w e y + (ρ y : EReal)) W := fun {w} hw =>
    chartCorrectedFamily_plurisubharmonicOn (F := {w})
      (fun _ h => by rw [mem_singleton_iff.mp h]; exact hw) e hρ _ ⟨w, mem_singleton _, rfl⟩
  have hVeq : EqOn (fun y => chartFunction U e y + (ρ y : EReal))
      (uscRegularization (⨆ j, v j)) W := by
    intro y hy
    change chartFunction U e y + (ρ y : EReal) = _
    rw [hsup, uscRegularization_add_coe_continuousAt_apply _ (hρc y hy),
      uscRegularization_chartFunction_apply _ e (hρ.2.1 hy)]
  have hGimg : IsOpen (e.val '' G) :=
    e.val.isOpen_image_of_subset_source hG (hGO.trans PU.source_subset)
  have hGW : e.val '' G ⊆ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hGO hy).2
  exact mixedTruncationLimitMeasure_le_liminf_of_monotone (Ω := PU.domain) (v := v)
    (fun j => hpsh (hu j)) (fun y _ i j hij => add_le_add (hmono hij _) le_rfl)
    hVeq (hpsh hU) hGimg hGW

/-- The total diagonal non-pluripolar mass of the regularized limit of an increasing
sequence of theta-PSH potentials is at most the supremum of the masses of the
sequence (Xia, Corollary 2.4.1, the inequality used for (3.6)), from the local
theorem `truncationLimitMeasure_le_liminf_of_monotone`. -/
theorem diagonalPotentialMass_le_iSup_of_monotone
    {theta : ClosedRealOneOneForm n M} (u : ℕ → M → EReal)
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hmono : Monotone u)
    (hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, u j))) :
    diagonalPotentialMass theta (uscRegularization (⨆ j, u j)) hU ≤
      ⨆ j, diagonalPotentialMass theta (u j) (hu j) := by
  refine (measure_univ_le_liminf_of_local _ _
    (exists_nhds_diagonalPotentialMeasure_le_liminf u hu hmono hU)).trans ?_
  rw [liminf_eq_iSup_iInf_of_nat]
  exact iSup_mono fun k => iInf₂_le k le_rfl

end Manifold

end SGPT.Foundations.Analysis.Pending.IncreasingLimitMass
