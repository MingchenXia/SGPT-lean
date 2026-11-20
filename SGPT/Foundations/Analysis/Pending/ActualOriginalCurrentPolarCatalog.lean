import SGPT.Foundations.Analysis.Pending.ActualOriginalPotentialOverlapSmoothDifference
import SGPT.Foundations.Analysis.Pending.ActualCompactAnalyticGlobalComponents

/-! Actual globally consistent polar locus and genuine finite components of
original weak analytic local potentials of a signed current. -/

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualOriginalCurrentPolarCatalog
open FirstPass FirstPass.HolomorphicMaps CanonicalCurrentFrame
open ActualWeakAnalyticCurrentPotentialAtlas ActualQuasiPshPotentialSmoothCompatibility
  ActualOriginalPotentialOverlapSmoothDifference
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Every genuine original coefficient-reading local potential has exactly
these manifold poles. This is an output property, not a supplied atlas. -/
def OriginalPolar
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) (A : Set M) : Prop :=
  ∀ (e : ComplexChart (m + 1) M) (Ω : Opens (ComplexModel (m + 1)))
    (_hΩ : Ω ≤ chartTarget e) (u : ComplexModel (m + 1) → EReal)
    (hu : LocalQuasiPshPotentialOn u Ω),
    (∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(Ω, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hu) w φ) →
    ∀ p ∈ e.val.source, e.val p ∈ Ω → (p ∈ A ↔ u (e.val p) = ⊥)

private theorem pole_agreement_at
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e f : ComplexChart (m + 1) M) {Ω P : Opens (ComplexModel (m + 1))}
    (hΩ : Ω ≤ chartTarget e) (hP : P ≤ chartTarget f)
    {u v : ComplexModel (m + 1) → EReal}
    (hu : LocalQuasiPshPotentialOn u Ω) (hv : LocalQuasiPshPotentialOn v P)
    (hreadu : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(Ω, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hu) w φ)
    (hreadv : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(P, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) f w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hv) w φ)
    {p : M} (hpe : p ∈ e.val.source) (hpf : p ∈ f.val.source)
    (hpu : e.val p ∈ Ω) (hpv : f.val p ∈ P) :
    u (e.val p) = ⊥ ↔ v (f.val p) = ⊥ := by
  let F := chartTransition e f
  have hcore : e.val p ∈ (Ω : Set _) ∩ (F.source ∩ F ⁻¹' P) := by
    refine ⟨hpu, ?_, ?_⟩
    · change e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' f.val.source
      refine ⟨e.val.map_source hpe, ?_⟩
      change e.val.symm (e.val p) ∈ f.val.source
      rwa [e.val.left_inv hpe]
    · change f.val (e.val.symm (e.val p)) ∈ P
      simpa only [e.val.left_inv hpe] using hpv
  obtain ⟨_huU, _hvF, _heq, hdiff⟩ :=
    exists_original_chart_smooth_difference T e f hΩ hP hu hv hreadu hreadv
  obtain ⟨W, _hWU, h, hxW, _hsm, _hh, heq, _hreg, _hlevi⟩ := hdiff (e.val p) hcore
  rw [heq hxW]
  change v (f.val (e.val.symm (e.val p))) + (h (e.val p) : EReal) = ⊥ ↔ _
  simp only [e.val.left_inv hpe, EReal.add_eq_bot_iff, EReal.coe_ne_bot, or_false]

/-- The actual original local potentials internally determine one analytic
polar subset, universally for every original reader, with no open polar piece. -/
theorem exists_original_polar_set
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : HasWeakAnalyticLocalPotentials T) :
    ∃ A : Set M, IsComplexAnalyticSubset (n := m + 1) A ∧ OriginalPolar T A ∧
      ∀ O : Set M, IsOpen O → O.Nonempty → ¬ O ⊆ A := by
  classical
  choose e Ω hΩ u hu hsrc hmem han hread using hT
  let A : Set M := {p | u p ((e p).val p) = ⊥}
  have hpolar : OriginalPolar T A := by
    intro f P hP v hv hr p hpf hpv
    exact pole_agreement_at T (e p) f (hΩ p) hP (hu p) hv
      (hread p) hr (hsrc p) hpf (hmem p) hpv
  refine ⟨A, ?_, hpolar, ?_⟩
  · intro p
    let E := complexChartAt (n := m + 1) p
    let F := chartTransition E (e p)
    obtain ⟨c, N, f, hc, ⟨B, hBo, hpB, hf⟩, b, _hb, _hsm, heq⟩ := han p
    obtain ⟨t, htp, hto, hpt⟩ := _root_.eventually_nhds_iff.mp heq
    let Z : Set (ComplexModel (m + 1)) := Ω p ∩ (B ∩ t)
    let R : Set (ComplexModel (m + 1)) := F.source ∩ F ⁻¹' Z
    have hRo : IsOpen R := F.isOpen_inter_preimage ((Ω p).isOpen.inter (hBo.inter hto))
    have hpE : p ∈ E.val.source := mem_complexChartAt_source p
    have hcenter : E.val p ∈ R := by
      refine ⟨?_, ?_⟩
      · change E.val p ∈ E.val.target ∩ E.val.symm ⁻¹' (e p).val.source
        refine ⟨E.val.map_source hpE, ?_⟩
        change E.val.symm (E.val p) ∈ (e p).val.source
        rw [E.val.left_inv hpE]
        exact hsrc p
      · change (e p).val (E.val.symm (E.val p)) ∈ Z
        rw [E.val.left_inv hpE]
        exact ⟨hmem p, hpB, hpt⟩
    have hFhol : DifferentiableOn ℂ F R := fun z hz =>
      (chartTransition_contDiffAt E (e p) hz.1).differentiableAt (by simp) |>.differentiableWithinAt
    refine ⟨{
      generatorCount := N
      generator := fun j z => f j (F z)
      coordinateNeighborhood := R
      isOpen_coordinateNeighborhood := hRo
      center_mem_coordinateNeighborhood := hcenter
      coordinateNeighborhood_subset_target := fun z hz => hz.1.1
      generator_holomorphic := fun j => (hf j).comp hFhol (fun z hz => hz.2.2.1)
      zeroLocus := ?_ }⟩
    intro y hys hyR
    have hyg : y ∈ (e p).val.source := by
      have hy := hyR.1.2
      change E.val.symm (E.val y) ∈ (e p).val.source at hy
      rwa [E.val.left_inv hys] at hy
    have hFval : F (E.val y) = (e p).val y := by
      change (e p).val (E.val.symm (E.val y)) = _
      rw [E.val.left_inv hys]
    have hZ : (e p).val y ∈ Z := by
      have hz := hyR.2
      change F (E.val y) ∈ Z at hz
      rwa [hFval] at hz
    have hreader := hpolar (e p) (Ω p) (hΩ p) (u p) (hu p) (hread p) y hyg hZ.1
    rw [hreader, htp ((e p).val y) hZ.2.2]
    change (c : EReal) * generatorLog f ((e p).val y) + (b ((e p).val y) : EReal) = ⊥ ↔
      ∀ j, f j (F (E.val y)) = 0
    rw [hFval]
    exact scaled_generatorLog_add_eq_bot_iff f ((e p).val y) hc (b ((e p).val y))
  · intro O hO ⟨p, hpO⟩ hsub
    let E := e p
    let B : Set (ComplexModel (m + 1)) := (Ω p : Set _) ∩
      (E.val.target ∩ E.val.symm ⁻¹' O)
    have hBo : IsOpen B := (Ω p).isOpen.inter (E.val.symm.isOpen_inter_preimage hO)
    have hpB : E.val p ∈ B := by
      refine ⟨hmem p, E.val.map_source (hsrc p), ?_⟩
      change E.val.symm (E.val p) ∈ O
      rwa [E.val.left_inv (hsrc p)]
    obtain ⟨z, hz, hne⟩ := (hu p).2.2 (E.val p) (hmem p) B hBo hpB
    have hzΩ : z ∈ Ω p := hz.1
    have hzT : z ∈ E.val.target := hz.2.2.1
    have hyO : E.val.symm z ∈ O := hz.2.2.2
    have hbot := (hpolar E (Ω p) (hΩ p) (u p) (hu p) (hread p)
      (E.val.symm z) (E.val.map_target hzT) (by rwa [E.val.right_inv hzT])).mp (hsub hyO)
    exact hne (by simpa only [E.val.right_inv hzT] using hbot)

omit [IsComplexManifold (m + 1) M] in
private theorem regular_dimension_lt_of_no_open_piece {A B : Set M}
    (hopen : ∀ O : Set M, IsOpen O → O.Nonempty → ¬ O ⊆ A)
    (hBA : B ⊆ A) {x : M} {k : ℕ}
    (hk : RegularAtDim (n := m + 1) B x k) : k < m + 1 := by
  have hkn := hk.1
  have hne : k ≠ m + 1 := by
    intro heq
    subst k
    let e := complexChartAt (n := m + 1) x
    obtain ⟨Φ, _hsub, _hcenter, hflat⟩ := hk.2.2
    let O : Set M := e.val.source ∩ e.val ⁻¹' Φ.source
    have hOo : IsOpen O := e.val.isOpen_inter_preimage Φ.isOpen_source
    have hxO : x ∈ O := ⟨mem_complexChartAt_source x, Φ.center_mem_source⟩
    apply hopen O hOo ⟨x, hxO⟩
    intro y hy
    apply hBA
    apply (hflat hy.1 hy.2).mpr
    intro i hi
    exact (not_le_of_gt i.isLt hi).elim
  omega

/-- Compactness internally produces the finite exact catalogue of genuine
polar components of the original signed current, with strict dimension bounds. -/
theorem exists_finite_original_polar_catalog [CompactSpace M]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : HasWeakAnalyticLocalPotentials T) :
    ∃ (A : Set M) (N : ℕ) (V : Fin N → ClosedIrreducibleAnalyticSubvariety (m + 1) M),
      IsComplexAnalyticSubset (n := m + 1) A ∧ OriginalPolar T A ∧
      Function.Injective (fun j => (V j).carrier) ∧
      range (fun j => (V j).carrier) = GlobalComponents.globalComponents (n := m + 1) A ∧
      (∀ j, (V j).carrier ⊆ A ∧ (V j).dim < m + 1) ∧
      (⋃ j, (V j).carrier) = A := by
  classical
  obtain ⟨A, hA, hpolar, hopen⟩ := exists_original_polar_set T hT
  obtain ⟨N, B, hinj, hrange, hB, hunion⟩ :=
    ActualCompactAnalyticGlobalComponents.exists_finite_exact_global_components hA
  have hregular : ∀ j, ∃ x k, RegularAtDim (n := m + 1) (B j) x k := by
    intro j
    obtain ⟨y, hy⟩ := (hB j).2.2
    obtain ⟨x, _hx, k, hk⟩ := RegularLocusDense.exists_regularAtDim_mem_of_isOpen
      (hB j).1.analytic isOpen_univ hy (mem_univ y)
    exact ⟨x, k, hk⟩
  choose x k hk using hregular
  let V : Fin N → ClosedIrreducibleAnalyticSubvariety (m + 1) M := fun j =>
    { carrier := B j
      isClosed_carrier := (hB j).1.analytic.isClosed
      irreducible_carrier := (hB j).1
      dim := k j
      dim_le := (hk j).1
      regularLocus_nonempty := ⟨x j, hk j⟩ }
  refine ⟨A, N, V, hA, hpolar, hinj, hrange, ?_, hunion⟩
  intro j
  exact ⟨(hB j).2.1, regular_dimension_lt_of_no_open_piece hopen (hB j).2.1 (hk j)⟩

end SGPT.Foundations.Analysis.Pending.ActualOriginalCurrentPolarCatalog
