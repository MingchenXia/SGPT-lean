import SGPT.PSH.QuasiPSHIdentity
import SGPT.Trace.BertiniUniversalRegularOTStalk
import SGPT.Foundations.Analysis.Pending.MultiplierIdealProductComparison

/-! Exact RAW original book weight domain: connected raw qpsh is all-bot
or original globally nondegenerate, and the actual all-bot multiplier
stalk/restriction ideal equality is produced, including dimension zero. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Okounkov SGPT.PSH.IdealRestriction SGPT.PSH.OhsawaTakegoshi

section Raw
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [ConnectedSpace Y]

theorem raw_qpsh_eq_bot_or_original_global {φ : Y → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    (∀ y, φ y = ⊥) ∨ IsGlobalQuasiPshPotential (n := n) φ := by
  classical
  by_cases hbot : ∀ y, φ y = ⊥
  · exact Or.inl hbot
  · right
    refine ⟨hφ,?_⟩
    obtain ⟨y,hy⟩ := not_forall.mp hbot
    apply SGPT.PSH.locallyNondegenerate_of_component_nonbot_of_local_coordinate_quasiPSH
    · intro x
      let e := complexChartAt (n := n) x
      refine ⟨n,e.val,mem_complexChartAt_source x,?_⟩
      exact hφ e (e.val x) (e.val.map_source (mem_complexChartAt_source x))
    · intro x
      exact ⟨y,by simp,hy⟩
end Raw

section Germ
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]

private theorem bot_multiplier_mem_eventually_zero {c : ℝ} {x : Y} {g : Y → ℂ}
    (hg : (multiplierIdeal (n := n) c (⊥ : Y → EReal)).mem x g) : g =ᶠ[𝓝 x] 0 := by
  obtain ⟨_hhol,hc,U,hUo,hxU,hdiff,hmeas,hint⟩ := hg
  let e := complexChartAt (n := n) x
  have hae : ∀ᵐ z ∂(volume.restrict U), multiplierDensity
      (chartFunction (⊥ : Y → EReal) e) c (fun z => g (e.val.symm z)) z < ⊤ :=
    ae_lt_top' hmeas hint.ne
  have hae0 : (fun z => g (e.val.symm z)) =ᵐ[volume.restrict U] fun _ => (0 : ℂ) := by
    filter_upwards [hae] with z hz
    by_contra hne
    rw [multiplierDensity_eq_top_at_pole (φ := chartFunction (⊥ : Y → EReal) e)
      (f := fun z => g (e.val.symm z)) (x := z) hc rfl hne] at hz
    exact lt_irrefl _ hz
  have heq : EqOn (fun z => g (e.val.symm z)) (fun _ => (0 : ℂ)) U :=
    Measure.eqOn_open_of_ae_eq hae0 hUo hdiff.continuousOn continuousOn_const
  have hev : ∀ᶠ y in 𝓝 x, y ∈ e.val.source ∧ e.val y ∈ U :=
    Filter.Eventually.and (e.val.open_source.mem_nhds (mem_complexChartAt_source x))
      (e.val.continuousAt (mem_complexChartAt_source x) (hUo.mem_nhds hxU))
  filter_upwards [hev] with y hy
  have h := heq hy.2
  simp only at h
  rw [e.val.left_inv hy.1] at h
  exact h

theorem multiplierIdeal_bot_mem_iff_eventually_zero {c : ℝ} (hc : 0 < c) (x : Y) (g : Y → ℂ) :
    (multiplierIdeal (n := n) c (⊥ : Y → EReal)).mem x g ↔ g =ᶠ[𝓝 x] 0 := by
  constructor
  · exact bot_multiplier_mem_eventually_zero
  · intro hg
    have hzero : (multiplierIdeal (n := n) c (⊥ : Y → EReal)).mem x (0 : Y → ℂ) :=
      ⟨holomorphicAt_const 0,multiplierIntegrableAt_zero _ hc _ volume⟩
    exact MultiplierIdealProductComparison.mem_multiplierIdeal_congr hzero hg.symm

theorem multiplierIdeal_bot_stalkIdeal_eq_bot {c : ℝ} (hc : 0 < c) (x : Y) :
    stalkIdeal (multiplierIdeal (n := n) c (⊥ : Y → EReal)) x = ⊥ := by
  apply le_antisymm ?_ bot_le
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨g,hg,hmem,rfl⟩
  change NativeHolGerm.mk g hg = 0
  change NativeHolGerm.mk g hg = NativeHolGerm.mk (0 : Y → ℂ) (holomorphicAt_const 0)
  exact NativeHolGerm.mk_eq_mk_iff.mpr ((multiplierIdeal_bot_mem_iff_eventually_zero hc x g).mp hmem)
end Germ

section Regular
variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

theorem regular_bot_multiplierIdeal_book_restriction
    (hclosed : IsClosed W) (hk : m ≤ n)
    (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m) {c : ℝ} (hc : 0 < c) :
    let hC : IsClosedSubmanifold n W := ⟨hclosed,fun x hx => ⟨m,hreg x hx⟩⟩
    letI := chartedSpace hk hreg
    ∀ p : W,
      Ideal.comap (structureStalkEquiv hk hreg hC p)
        (stalkIdeal (multiplierIdeal (n := m) c (⊥ : W → EReal)) p) =
      restStalk (multiplierIdeal (n := n) c (⊥ : X → EReal)) (submanifoldSubspace hC) p.val := by
  intro hC
  let := chartedSpace hk hreg
  intro p
  have hWzero := multiplierIdeal_bot_stalkIdeal_eq_bot (n := m) hc p
  have hXzero := multiplierIdeal_bot_stalkIdeal_eq_bot (n := n) hc p.val
  rw [hWzero,restStalk,hXzero,Ideal.map_bot]
  apply le_antisymm ?_ bot_le
  intro a ha
  change structureStalkEquiv hk hreg hC p a = 0 at ha
  change a = 0
  apply (structureStalkEquiv hk hreg hC p).injective
  simpa only [map_zero] using ha
end Regular

end SGPT.Trace.BertiniUniversal
