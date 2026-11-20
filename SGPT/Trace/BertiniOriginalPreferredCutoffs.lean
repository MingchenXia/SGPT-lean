import SGPT.Trace.BertiniOriginalSliceSourceOpenness
import SGPT.Trace.BertiniMovingFiberCutoffs

/-! Actual FULL affine original incidence and produced preferred-slice ambient cutoffs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Set Filter Metric
open scoped Manifold ContDiff Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open ProductComplexManifold
open scoped ProductComplexManifold

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)

private def actualAffineEquation (i j : Fin (N + 1)) (q : ComplexModel N × X) : ℂ :=
  pairing (affineLift i q.1) (affineLift j (affineChart j (p q.2)))

omit [IsComplexManifold n X] in
private theorem actualAffineEquation_zero_iff (i j : Fin (N + 1)) {q : ComplexModel N × X}
    (hq : p q.2 ∈ (affineChart j).source) :
    q.2 ∈ member p (affinePoint i q.1) ↔ actualAffineEquation p i j q = 0 := by
  change IsIncident (mk (affineLift i q.1) (affineLift_ne_zero i _)) (p q.2) ↔ _
  conv_lhs => rw [eq_mk_affineLift_affineChart j hq]
  exact isIncident_mk_mk_iff (affineLift_ne_zero i _) (affineLift_ne_zero j _)

omit [IsComplexManifold n X] in
theorem isClosed_originalAffineIncidence (i : Fin (N + 1)) :
    IsClosed {q : ComplexModel N × X | q.2 ∈ member p (affinePoint i q.1)} := by
  rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
  intro q hq
  let j := chartIndex (p q.2)
  have hqj : p q.2 ∈ (affineChart j).source := mem_affineChart_chartIndex _
  have hW := ((affineChart j).open_source.preimage (p.contMDiff.continuous.comp continuous_snd)).mem_nhds hqj
  have hF : ContinuousAt (actualAffineEquation p i j) q := by
    change ContinuousAt (fun y : ComplexModel N × X => ∑ k,
      affineLift i y.1 k * affineLift j (affineChart j (p y.2)) k) q
    apply tendsto_finsetSum Finset.univ
    intro k _
    have hl := (differentiable_affineLift_apply i k q.1).continuousAt.comp
      (f := fun y : ComplexModel N × X => y.1) (x := q) continuous_fst.continuousAt
    have hr := (holomorphicAt_affineLift_affineChart_comp p p.contMDiff j k hqj).self_of_nhds.continuousAt.comp
      (f := fun y : ComplexModel N × X => y.2) (x := q) continuous_snd.continuousAt
    exact hl.mul hr
  have hne : actualAffineEquation p i j q ≠ 0 := fun hz =>
    hq ((actualAffineEquation_zero_iff p i j hqj).mpr hz)
  filter_upwards [hW,hF.eventually_ne hne] with y hy hFy
  intro hym
  exact hFy ((actualAffineEquation_zero_iff p i j hy).mp hym)

variable {d : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y] [CompactSpace Y]
  (f : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) Y (ComplexProjectiveSpace N) ∞)
  {φ : Y → EReal}

theorem exists_originalPreferredSliceCutoffs
    (hφ : ManifoldQuasiPlurisubharmonic (n := d + 1) φ) (ℓ₀ : HyperplaneSpace N)
    (hsm₀ : IsSmoothHypersurfaceMember (d + 1) f ℓ₀) :
    ∃ (k : ℕ) (c : Fin k → SliceChart (d + 1) (f : Y → ComplexProjectiveSpace N) φ)
      (a : Fin k → Y) (V : TopologicalSpace.Opens (ComplexModel N)) (β : Fin k → C(Y,ℝ)),
      affineChart (chartIndex ℓ₀) ℓ₀ ∈ V ∧
      (∀ j, (c j).i = chartIndex ℓ₀ ∧ (c j).e = complexChartAt (n := d + 1) (a j) ∧
        (c j).ζ₀ = affineChart (chartIndex ℓ₀) ℓ₀ ∧ a j ∈ member f ℓ₀) ∧
      (∀ ζ ∈ V, IsSmoothHypersurfaceMember (d + 1) f (affinePoint (chartIndex ℓ₀) ζ)) ∧
      (∀ ζ ∈ V, ∀ j, ζ ∈ ball (c j).ζ₀ (c j).r) ∧
      (∀ j x, 0 ≤ β j x ∧ β j x ≤ 1) ∧ (∀ j, HasCompactSupport (β j)) ∧
      (∀ ζ ∈ V, ∀ j, tsupport (β j) ⊆ (c j).originalSliceAmbientSource ζ) ∧
      ∀ ζ ∈ V, ∀ x ∈ member f (affinePoint (chartIndex ℓ₀) ζ), (∑ j, β j x) = 1 := by
  classical
  let i := chartIndex ℓ₀
  let b := affineChart i ℓ₀
  have hℓ : affinePoint i b = ℓ₀ := by
    exact (affineChart i).left_inv (mem_affineChart_chartIndex ℓ₀)
  let K := member f ℓ₀
  have hex (x : K) := exists_preferred_sliceChart_originalSource f hφ (q₀ := (ℓ₀,x.val)) x.property
    ((isSmoothHypersurfaceMember_iff f f.contMDiff ℓ₀).mp hsm₀ x.val)
  let C (x : K) := (hex x).choose
  have hC (x : K) := (hex x).choose_spec
  let O : K → Set Y := fun x => (C x).originalSliceAmbientSource b
  have hO (x : K) : IsOpen (O x) := (C x).originalSliceAmbientSource b |>.isOpen
  have hc : K ⊆ ⋃ x, O x := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x,hx⟩,?_⟩
    change x ∈ (C ⟨x,hx⟩).originalSliceAmbientSource b
    have hb : (C ⟨x,hx⟩).ζ₀ = b := (hC ⟨x,hx⟩).2.2.1
    rw [← hb]
    exact (hC ⟨x,hx⟩).2.2.2
  obtain ⟨A,hA⟩ := (isClosed_member f f.contMDiff.continuous ℓ₀).isCompact.elim_finite_subcover O hO hc
  let aj : Fin A.card → K := fun j => (A.equivFin.symm j).val
  let cs : Fin A.card → SliceChart (d + 1) (f : Y → ComplexProjectiveSpace N) φ := fun j => C (aj j)
  have hcover : ∀ x, (b,x) ∈ {q : ComplexModel N × Y | q.2 ∈ member f (affinePoint i q.1)} →
      ∃ j, (b,x) ∈ (cs j).originalSliceJointSource := by
    intro x hx
    have hxK : x ∈ K := by
      change x ∈ member f (affinePoint i b) at hx
      change x ∈ member f ℓ₀
      rw [hℓ] at hx
      exact hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hA hxK)
    let j := A.equivFin ⟨y,hy⟩
    have hcs : cs j = C y := by simp only [cs,aj,j,Equiv.symm_apply_apply]
    refine ⟨j,?_⟩
    change b ∈ ball (cs j).ζ₀ (cs j).r ∧ x ∈ (cs j).originalSliceAmbientSource b
    rw [hcs]
    refine ⟨?_,hxy⟩
    rw [(hC y).2.2.1]
    exact mem_ball_self (C y).r_pos
  obtain ⟨V₀,β,hV₀,hβ,hβc,hβsub,hβone⟩ :=
    SGPT.Trace.MovingFiberCutoffs.exists_fixed_ambient_fiber_cutoffs
      (isClosed_originalAffineIncidence f i) b A.card (fun j => ((cs j).originalSliceJointSource : Set _))
      (fun j => (cs j).originalSliceJointSource.isOpen) hcover
  let W : TopologicalSpace.Opens (ComplexModel N) :=
    ⟨{ζ | IsSmoothHypersurfaceMember (d + 1) f (affinePoint i ζ)},
      (BertiniPencilFamily.isOpen_smoothMemberSet f f.contMDiff).preimage (continuous_affinePoint i)⟩
  let V : TopologicalSpace.Opens (ComplexModel N) :=
    ⟨(V₀ : Set _) ∩ W ∩ ⋂ j, ball (cs j).ζ₀ (cs j).r,
      (V₀.isOpen.inter W.isOpen).inter (isOpen_iInter_of_finite fun _ => isOpen_ball)⟩
  refine ⟨A.card,cs,(fun j => (aj j).val),V,β,?_,?_,?_,?_,hβ,hβc,?_,?_⟩
  · refine ⟨⟨hV₀,?_⟩,mem_iInter.mpr fun j => ?_⟩
    · change IsSmoothHypersurfaceMember (d + 1) f (affinePoint i b)
      rw [hℓ]
      exact hsm₀
    · rw [(hC (aj j)).2.2.1]
      exact mem_ball_self (cs j).r_pos
  · intro j
    exact ⟨(hC (aj j)).1,(hC (aj j)).2.1,(hC (aj j)).2.2.1,(aj j).property⟩
  · intro ζ hζ
    exact hζ.1.2
  · intro ζ hζ j
    exact mem_iInter.mp hζ.2 j
  · intro ζ hζ j x hx
    exact (hβsub ζ hζ.1.1 j hx).2
  · intro ζ hζ x hx
    exact hβone ζ hζ.1.1 x hx

end SGPT.Trace.Bertini
