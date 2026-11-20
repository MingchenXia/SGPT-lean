import SGPT.Foundations.Analysis.Pending.DistributionLocalDdcPotential
import SGPT.Foundations.Analysis.Pending.DistributionCutoffExtension
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrentPotentials
import SGPT.Foundations.Analysis.Pending.ChartPartition

set_option autoImplicit false

/-! Original signed closed (1,1) currents receive internally chosen full-chart
scalar distributions and a finite subordinate chart-smooth partition.
ENTIRE BP statements and proofs precede this source. Global scalar gluing and
the Bott--Chern smoothing theorem remain subsequent obligations. -/

noncomputable section
open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ClosedCurrentLocalPotentialPartition
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents LelongPoincareDivisor

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

/-- The scalar potential is an actual distribution on the full original domain;
both its smaller neighborhood and extension are internally produced. -/
theorem exists_ambient_scalar_potential (A : DistributionForm Ω 2)
    (hA : IsClosed A) (h11 : IsOneOne A) (x : ComplexModel n) (hx : x ∈ Ω) :
    ∃ (W : Opens (ComplexModel n)) (hW : W ≤ Ω) (R : 𝓓'(Ω, ℝ)),
      x ∈ W ∧ ddC (restrictDistribution R hW) = restrictForm A hW := by
  obtain ⟨U, hU, p, hxU, hp⟩ :=
    DistributionLocalDdcPotential.exists_local_scalar_potential A hA h11 x hx
  obtain ⟨W, hWU, R, hxW, hR⟩ :=
    DistributionCutoffExtension.exists_extension_near p hU x hxU
  refine ⟨W, hWU.trans hU, R, hxW, ?_⟩
  calc
    ddC (restrictDistribution R (hWU.trans hU)) =
        ddC (restrictDistribution p hWU) := congrArg ddC hR
    _ = restrictForm (ddC p) hWU := (restrictForm_ddC p hWU).symm
    _ = restrictForm (restrictForm A hU) hWU := congrArg (fun B => restrictForm B hWU) hp
    _ = restrictForm A (hWU.trans hU) := by
      ext v φ
      change restrictDistribution (restrictDistribution (A v) hU) hWU φ =
        restrictDistribution (A v) (hWU.trans hU) φ
      rw [restrictDistribution_trans]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))

/-- Original coefficient closedness and type internally supply a genuine atlas
chart, a coordinate neighborhood, and its full-chart scalar potential. -/
theorem exists_chart_scalar_potential (hn : 0 < n)
    (T : GlobalCurrent n M (degreeTwo hn))
    (hclosed : T.IsClosed b) (h11 : T.IsTypeOneOne b hn) (x : M) :
    ∃ (e : ComplexChart n M) (W : Opens (ComplexModel n)) (hW : W ≤ chartTarget e)
      (R : 𝓓'(chartTarget e, ℝ)), x ∈ e.val.source ∧ e.val x ∈ W ∧
        ddC (restrictDistribution R hW) = restrictForm (T.coefficients b e) hW := by
  let e : ComplexChart n M := complexChartAt x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨W, hW, R, hxW, hR⟩ := exists_ambient_scalar_potential
    (T.coefficients b e) (hclosed e) (h11 e) (e.val x) (e.val.map_source hx)
  exact ⟨e, W, hW, R, hx, hxW, hR⟩

/-- Compactness is used only to internally select a finite partition subordinate
to the genuine local-potential neighborhoods, including empty M. -/
theorem exists_local_potential_partition [CompactSpace M] (hn : 0 < n)
    (T : GlobalCurrent n M (degreeTwo hn))
    (hclosed : T.IsClosed b) (h11 : T.IsTypeOneOne b hn) :
    ∃ (m : ℕ) (e : Fin m → ComplexChart n M) (W : Fin m → Opens (ComplexModel n))
      (hW : ∀ a, W a ≤ chartTarget (e a))
      (R : ∀ a, 𝓓'(chartTarget (e a), ℝ)) (χ : Fin m → M → ℝ),
      (∀ a, ChartSmooth (n := n) (χ a)) ∧ (∀ a y, 0 ≤ χ a y) ∧
      (∀ a, tsupport (χ a) ⊆ {y | y ∈ (e a).val.source ∧ (e a).val y ∈ W a}) ∧
      (∀ a, IsCompact (tsupport (χ a))) ∧ (∀ y, ∑ a, χ a y = 1) ∧
      ∀ a, ddC (restrictDistribution (R a) (hW a)) =
        restrictForm (T.coefficients b (e a)) (hW a) := by
  classical
  choose e W hW R hxs hz hpot using
    fun x : M => exists_chart_scalar_potential b hn T hclosed h11 x
  let O : M → Opens M := fun x =>
    ⟨(e x).val.source ∩ (e x).val ⁻¹' (W x),
      (e x).val.isOpen_inter_preimage (W x).isOpen⟩
  obtain ⟨m, χ, idx, hsm, hnon, hsupp, hcompact, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n) O
      (fun x => ⟨x, hxs x, hz x⟩)
  exact ⟨m, (fun a => e (idx a)), (fun a => W (idx a)),
    (fun a => hW (idx a)), (fun a => R (idx a)), χ,
    hsm, hnon, hsupp, hcompact, hsum, (fun a => hpot (idx a))⟩

end SGPT.Foundations.Analysis.Pending.ClosedCurrentLocalPotentialPartition
