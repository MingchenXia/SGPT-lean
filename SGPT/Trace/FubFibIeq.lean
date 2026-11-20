import SGPT.Trace.FubFibSlice

/-!
# The reverse Bertini theorem `lma:fibIeq`

Source: `chapter_trace.tex`, `lma:fibIeq` (lines 1166--1193); blueprint `claude-fubini-fib.tex`
(and `claude-coherent.tex` for the rigidity half).

*Let `X` be a complex manifold and `f : X → Δ*` a surjective projective morphism. Let `(L, h)`,
`(L, h')` be Hermitian pseudo-effective line bundles on `X` with the same underlying line bundle
`L`. Assume a biholomorphic `S¹`-action on `(X, L)` such that `f` is `S¹`-equivariant (`S¹` acting
on `Δ*` by rotation) and `h, h'` are `S¹`-invariant. If for quasi-every `z ∈ Δ*` the fibre `X_z`
is smooth and `h|_{X_z} ∼_𝓘 h'|_{X_z}`, then `h ∼_𝓘 h'`.*

Lane COHERENT reduced the lemma (`SGPT.Trace.CohFib.lma_fibIeq_of_ae`) to the
Lebesgue-almost-everywhere reverse inclusion `Rest_{X_z} 𝓘(cφ) ⊆ 𝓘(cφ|_{X_z})`
(`SGPT.Trace.CohFib.AEReverseInclusion`). This file proves it for every holomorphic submersion
(`aeReverseInclusion_of_submersion`): the local statement `exists_local_reverse` (Nadel
generators, adapted coordinates, Fubini, slice charts) holds near every point, `X` is
second countable, so countably many neighbourhoods cover `X`, and a countable union of null sets
of heights is null. Since a rotation-equivariant `f` is a submersion
(`SGPT.Trace.CohFib.surjective_chartDeriv_of_equivariant`), this gives `lma_fibIeq`, the formal
statement of `lma:fibIeq` with the reading of blueprint `claude-coherent:reading`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Trace.FubFib

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace SGPT.Foundations.Analysis.Pending.RankDegeneracy
  SGPT.Okounkov SGPT.PSH.IdealRestriction SGPT.PSH.OhsawaTakegoshi SGPT.GAGA.Coherent
  SGPT.Trace.DirectImg SGPT.Trace.CohFib SGPT.PSH.LineBundleMetric

/-! ### The almost-everywhere reverse inclusion -/

section AE

/-- **The almost-everywhere reverse inclusion, `dim X = b + 1`.** -/
theorem aeReverseInclusion_of_submersion_succ {b : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (b + 1)) X] [IsComplexManifold (b + 1) X] {f : X → puncturedDisc}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (b + 1)) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hD : ∀ x, Function.Surjective (chartDeriv (complexChartAt (n := b + 1) x)
      (complexChartAt (n := 1) (f x)) f x))
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := b + 1) φ) {c : ℝ} (hc : 0 < c) :
    AEReverseInclusion (n := b + 1) f hf.continuous φ c := by
  choose V hVo hxV N hN hrev using fun x => exists_local_reverse hf hφ hc (hD x)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hcover : ∀ y : X, ∃ x ∈ T, y ∈ V x := by
    intro y
    have hy : y ∈ ⋃ x ∈ T, V x := by
      rw [hTU]
      exact mem_iUnion.2 ⟨y, hxV y⟩
    simpa only [mem_iUnion, exists_prop] using hy
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun x _ =>
    volume_preimage_coord_sub_null (hN x) (coord f x))
  rintro w ⟨hw, hbad⟩
  by_contra hcon
  apply hbad
  intro k hk hsm q
  have hsm' : IsSmoothFibreOfDim (b + 1) 1 f ⟨w, hw⟩ b :=
    isSmoothFibreOfDim_of_forall_surjective_add hf fun y _ => hD y
  have hkb : k = b := RegularPointDimension.eq_of_regularAtDim (hsm.1 q.1 q.2) (hsm'.1 q.1 q.2)
  subst hkb
  obtain ⟨x, hxT, hqx⟩ := hcover q.1
  exact hrev x ⟨w, hw⟩ (fun hmem => hcon (mem_biUnion hxT hmem)) hsm.1 hk
    (hsm.isClosedSubmanifold f hf.continuous) q hqx

/-- **The almost-everywhere reverse inclusion** (blueprint `claude-coherent:ae-reverse`). Let
`f : X → Δ*` be a holomorphic submersion, `φ` quasi-psh on `X` and `c > 0`. For Lebesgue-almost
every `z ∈ Δ*`, at every point `q` of the fibre `X_z` (with any of its structures of a smooth
fibre), `(Rest_{X_z} 𝓘(cφ))_q ⊆ 𝓘(cφ|_{X_z})_q`. -/
theorem aeReverseInclusion_of_submersion {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {f : X → puncturedDisc}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ f)
    (hD : ∀ x, Function.Surjective (chartDeriv (complexChartAt (n := n) x)
      (complexChartAt (n := 1) (f x)) f x))
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} (hc : 0 < c) :
    AEReverseInclusion (n := n) f hf.continuous φ c := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · refine measure_mono_null (fun w hw => ?_) measure_empty
    obtain ⟨_, hbad⟩ := hw
    exact hbad fun k hk hsm q => (IsEmpty.false q.1).elim
  · obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 :=
      ⟨n - 1, (Nat.sub_add_cancel (le_of_surjective_chartDeriv (hD x₀))).symm⟩
    exact aeReverseInclusion_of_submersion_succ hf hD hφ hc

end AE

/-! ### `lma:fibIeq` -/

section Main

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {L : X → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L]
  [VectorBundle ℂ ℂ L] [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]

/-- **`lma:fibIeq`** (`chapter_trace.tex` lines 1166--1169), with the reading of blueprint
`claude-coherent:reading`. Let `X` be a complex manifold and `f : X → Δ*` a surjective projective
morphism; let `(L, h)`, `(L, h')` be Hermitian pseudo-effective with the same underlying line
bundle `L`, presented as `h = h₀ e^{-φ}`, `h' = h₀' e^{-φ'}`; let `σ` be a biholomorphic
`S¹`-action on `X` (`CircleAction`) with lifts `τ` to `L`, such that `f` is equivariant for the
rotations of `Δ*` and `h, h'` are invariant. If for quasi-every `z ∈ Δ*` the fibre `X_z` is smooth
and `h|_{X_z} ∼_𝓘 h'|_{X_z}` (`FibreIEquivalent`), then `h ∼_𝓘 h'`:
`𝓘(mφ) = 𝓘(mφ')` for every integer `m ≥ 1` (`prop:Iequivchar`). -/
theorem lma_fibIeq {f : X → puncturedDisc} (hf : IsProjectiveMorphism n 1 f)
    (hsurj : Function.Surjective f) (h h' : HermitianPseudoeffective n L)
    (σ : CircleAction n X) (τ : CircleActionLift σ L) (hequiv : IsRotationEquivariant σ f)
    (hinv : IsInvariantMetric τ h.metric) (hinv' : IsInvariantMetric τ h'.metric)
    {h₀ h₀' : HermitianMetric (n := n) L} {φ φ' : X → EReal}
    (hφ : IsPSHMetricWith h.metric h₀ φ) (hφ' : IsPSHMetricWith h'.metric h₀' φ')
    (hfib : (SGPT.PSH.VariableComplexAtlas.ofFixedModel 1 puncturedDisc).CoPluripolar
      {z | FibreIEquivalent (n := n) f φ φ' z})
    (m : ℕ) (hm : 0 < m) :
    multiplierIdeal (n := n) (m : ℝ) φ = multiplierIdeal (n := n) (m : ℝ) φ' := by
  have hn := pos_of_surjective (n := n) hsurj
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  have hD := surjective_chartDeriv_of_equivariant σ hf.1 hequiv
  have hq := manifoldQuasiPlurisubharmonic_of_isPSHMetricWith hφ
  have hq' := manifoldQuasiPlurisubharmonic_of_isPSHMetricWith hφ'
  exact lma_fibIeq_of_ae hf hsurj h h' σ τ hequiv hinv hinv' hφ hφ' hfib
    (fun k hk => aeReverseInclusion_of_submersion hf.1 hD hq (Nat.cast_pos.2 hk))
    (fun k hk => aeReverseInclusion_of_submersion hf.1 hD hq' (Nat.cast_pos.2 hk)) m hm

end Main

end SGPT.Trace.FubFib
