import SGPT.PSH.Pluripolar
import SGPT.PSH.Components
import SGPT.Foundations.Analysis.Pending.FlatComplexTorus
import SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity
import SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure

set_option autoImplicit false

/-!
Countable pluripolar unions in the original variable-dimensional atlas.
Only an auxiliary flat torus is compact Kähler. Original neighborhoods and
all pole witnesses retain their actual source domains.
-/

namespace SGPT.PSH

open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure
open scoped Topology

noncomputable section

/-- A compact chart support transports actual local pole witnesses to every
chart of the auxiliary manifold, including the boundary of the support. -/
theorem manifoldLocallyPluripolar_chartImage {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (e : ComplexChart n M)
    {K s : Set (ComplexModel n)} (hK : IsCompact K) (hKe : K ⊆ e.val.target)
    (hs : ∀ z ∈ K, LocallyPluripolarAt s z) :
    ManifoldLocallyPluripolar (n := n) (e.val.symm '' (s ∩ K)) := by
  let C := e.val.symm '' K
  have hC : IsClosed C :=
    (hK.image_of_continuousOn (e.val.continuousOn_symm.mono hKe)).isClosed
  have hsub : e.val.symm '' (s ∩ K) ⊆ C := image_mono inter_subset_right
  intro f z hz
  by_cases hp : f.val.symm z ∈ C
  · obtain ⟨q, hqK, hqp⟩ := hp
    let F := chartTransition f e
    have hzF : z ∈ F.source := by
      refine ⟨hz, ?_⟩
      change f.val.symm z ∈ e.val.source
      rw [← hqp]
      exact e.val.map_target (hKe hqK)
    have hFq : F z = q := by
      change e.val (f.val.symm z) = q
      rw [← hqp, e.val.right_inv (hKe hqK)]
    have hq : LocallyPluripolarAt s (F z) := hFq.symm ▸ hs q hqK
    have hpre := locallyPluripolarAt_preimage
      (RegularPatchNeighborhood.differentiableOn_chartTransition f e) hzF hq
    apply locallyPluripolarAt_of_inter_subset hpre (F.open_source.mem_nhds hzF)
    intro y hy
    refine ⟨hy.2, ?_⟩
    obtain ⟨t, ht, hty⟩ := hy.1.2
    change e.val (f.val.symm y) ∈ s
    rw [← hty, e.val.right_inv (hKe ht.2)]
    exact ht.1
  · let W := f.val.target ∩ f.val.symm ⁻¹' Cᶜ
    have hW : W ∈ 𝓝 z :=
      (f.val.isOpen_inter_preimage_symm hC.isOpen_compl).mem_nhds ⟨hz, hp⟩
    have hempty : LocallyPluripolarAt (∅ : Set (ComplexModel n)) z := by
      simpa only [FirstPass.pluripolarChartSet, preimage_empty, inter_empty] using
        (manifoldLocallyPluripolar_empty (n := n) (M := M) f z hz)
    apply locallyPluripolarAt_of_inter_subset hempty hW
    intro y hy
    exact False.elim (hy.2.2 (hsub hy.1.2))

/-- Countable closure on arbitrary actual open model domains. Compactness and
the Kähler metric are supplied only by an auxiliary flat complex torus. -/
theorem locallyPluripolarOn_iUnion {n : ℕ} {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) {S : ℕ → Set (ComplexModel n)}
    (hS : ∀ j, LocallyPluripolarOn (S j) Ω) :
    LocallyPluripolarOn (⋃ j, S j) Ω := by
  intro x hx
  let M := SGPT.Foundations.Analysis.Pending.FlatComplexTorus.Torus n
  let e := complexChartAt (n := n) (0 : M)
  let z₀ := e.val (0 : M)
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source (mem_complexChartAt_source (0 : M))
  let c := z₀ - x
  let τ := (Homeomorph.addRight c).toOpenPartialHomeomorph
  have hτs : τ.source = univ := rfl
  have hτx : τ x = z₀ := by change x + (z₀ - x) = z₀; abel
  have hτ : DifferentiableOn ℂ τ τ.source := by
    change DifferentiableOn ℂ (fun y : ComplexModel n ↦ y + c) univ
    exact differentiableOn_id.add_const c
  have hτinv : DifferentiableOn ℂ τ.symm τ.symm.source := by
    change DifferentiableOn ℂ (fun y : ComplexModel n ↦ y + -c) univ
    exact differentiableOn_id.add_const (-c)
  have hτinvx : τ.symm z₀ = x := by
    rw [← hτx]
    exact τ.left_inv (by rw [hτs]; exact mem_univ _)
  let O := e.val.target ∩ τ.symm ⁻¹' Ω
  have hO : IsOpen O := e.val.open_target.inter
    ((Homeomorph.addRight c).symm.continuous.isOpen_preimage Ω hΩ)
  have hzO : z₀ ∈ O := ⟨hz₀, by change τ.symm z₀ ∈ Ω; rwa [hτinvx]⟩
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hO z₀ hzO
  let K := closedBall z₀ (r / 2)
  have hKO : K ⊆ O := by
    intro y hy
    apply hb
    exact lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith)
  have hKe : K ⊆ e.val.target := fun _ hy ↦ (hKO hy).1
  let S' : ℕ → Set (ComplexModel n) := fun j ↦ τ.symm ⁻¹' S j
  have hS' : ∀ j y, y ∈ K → LocallyPluripolarAt (S' j) y := by
    intro j y hy
    have hpre := locallyPluripolarAt_preimage hτinv
      (by change y ∈ (univ : Set (ComplexModel n)); exact mem_univ _)
      (hS j _ (hKO hy).2)
    change LocallyPluripolarAt (univ ∩ S' j) y at hpre
    simpa only [univ_inter] using hpre
  let E : ℕ → Set M := fun j ↦ e.val.symm '' (S' j ∩ K)
  have hE : ∀ j, ManifoldLocallyPluripolar (n := n) (E j) := fun j ↦
    manifoldLocallyPluripolar_chartImage e (isCompact_closedBall _ _) hKe (hS' j)
  have hUnion := SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity.countablyStablePluripolar
    (SGPT.Foundations.Analysis.Pending.FlatComplexTorus.flatKahlerBackground n) E hE
  have hB : ball z₀ (r / 4) ⊆ K := by
    intro y hy
    exact mem_closedBall.mpr ((mem_ball.mp hy).le.trans (by linarith))
  have hlocal : LocallyPluripolarAt (⋃ j, S' j) z₀ := by
    apply locallyPluripolarAt_of_inter_subset (hUnion e z₀ hz₀)
      (isOpen_ball.mem_nhds (mem_ball_self (by linarith : 0 < r / 4)))
    intro y hy
    refine ⟨hKe (hB hy.2), ?_⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy.1
    exact mem_iUnion.mpr ⟨j, y, ⟨hj, hB hy.2⟩, rfl⟩
  have hpre := locallyPluripolarAt_preimage hτ
    (by rw [hτs]; exact mem_univ x) (hτx.symm ▸ hlocal)
  have heq : τ.source ∩ τ ⁻¹' (⋃ j, S' j) = ⋃ j, S j := by
    ext y
    simp only [hτs, univ_inter, mem_preimage, mem_iUnion, S']
    rw [τ.left_inv (by rw [hτs]; exact mem_univ y)]
  rwa [heq] at hpre

namespace VariableComplexAtlas

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Genuine coordinate pole witnesses reconstruct original neighborhood PSH
witnesses. The connected ball remains inside the original chart target. -/
theorem locallyPluripolar_of_in_chart {S : Set X}
    (hS : ∀ i, SGPT.Foundations.Analysis.LocallyPluripolarOn
      (A.pluripolarChartSet S i) (A.chart i).target) : A.LocallyPluripolar S := by
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  obtain ⟨V, u, hV, hxV, hcV, hu, hnu, hp⟩ :=
    hS i (A.chart i x) ((A.chart i).map_source hi)
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (hV.inter (A.chart i).open_target)
    (A.chart i x) ⟨hxV, (A.chart i).map_source hi⟩
  let B := ball (A.chart i x) r
  have hBT : B ⊆ (A.chart i).target := fun _ hz ↦ (hb hz).2
  have hBpsh : PSHOn u B :=
    ⟨hu.discPshOn.mono (fun _ hz ↦ (hb hz).1),
      exists_ne_bot_of_isOpen_subset hu hcV hnu isOpen_ball
        ⟨A.chart i x, mem_ball_self hr⟩ (fun _ hz ↦ (hb hz).1)⟩
  let U := (A.chart i).source ∩ (A.chart i) ⁻¹' B
  let w : X → EReal := u ∘ A.chart i
  have hU : IsOpen U := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hxU : x ∈ U := ⟨hi, mem_ball_self hr⟩
  have hBU : B ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U := by
    intro z hz
    have hzT := hBT hz
    refine ⟨hzT, (A.chart i).map_target hzT, ?_⟩
    change A.chart i ((A.chart i).symm z) ∈ B
    rwa [(A.chart i).right_inv hzT]
  have heq : EqOn u (A.coordinate w i) B := by
    intro z hz
    change u z = u (A.chart i ((A.chart i).symm z))
    rw [(A.chart i).right_inv (hBT hz)]
  have hw : A.IsPSHOn w U := by
    intro y hy
    obtain ⟨a, ha, hna⟩ := hBpsh.nontrivial
    refine ⟨i, hy.1, B, isOpen_ball, isConnected_ball hr, hBU, hy.2,
      hBpsh.disc.congr heq, a, ha, ?_⟩
    rwa [← heq ha]
  refine ⟨U, hU, hxU, w, hw, ?_⟩
  intro y hy
  apply hp (A.chart i y) (hb hy.2.2).1
  refine ⟨(A.chart i).map_source hy.2.1, ?_⟩
  change (A.chart i).symm (A.chart i y) ∈ S
  simpa only [(A.chart i).left_inv hy.2.1] using hy.1

/-- SGPT `prop:pluripolarunion`: every countable union of original local
pluripolar sets is locally pluripolar on the whole original manifold. -/
theorem LocallyPluripolar.iUnion {S : ℕ → Set X}
    (hS : ∀ j, A.LocallyPluripolar (S j)) : A.LocallyPluripolar (⋃ j, S j) := by
  apply locallyPluripolar_of_in_chart
  intro i
  have h := locallyPluripolarOn_iUnion (A.chart i).open_target
    (fun j ↦ (hS j).in_chart i)
  have heq : (⋃ j, A.pluripolarChartSet (S j) i) = A.pluripolarChartSet (⋃ j, S j) i := by
    ext z
    simp only [pluripolarChartSet, mem_iUnion, mem_inter_iff, mem_preimage]
    exact exists_and_left
  rwa [heq] at h

end VariableComplexAtlas

end

end SGPT.PSH
