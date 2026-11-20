import SGPT.Unibranch.NativeNov16FiniteFibreChartWindows
import SGPT.Unibranch.ComplexSpaceUnibranchComponents
import SGPT.Foundations.Analysis.LeviForm

/-! ONE actual local potential over a WHOLE finite-fibre base window.
Blueprint FIRST: native-nov16-finite-fibre-local-potential.tex.
No incoming smooth, positive, PSH or Kahler potential certificate.
-/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.NativeNov16FiniteFibreLocalPotential

private def chartSquare {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y)
    (y : Y.obj.left) (hy : y ∈ range e.toPoint) : ℝ :=
  ‖(Classical.choose hy).val.val‖ ^ 2

private theorem chartSquare_readback {Y : SourceReducedComplexSpace}
    (e : LocalEmbedding Y) (c : e.carrier)
    (h : e.toPoint c ∈ range e.toPoint) :
    chartSquare e (e.toPoint c) h = ‖c.val.val‖ ^ 2 := by
  have hc : Classical.choose h = c := e.toPoint_injective (Classical.choose_spec h)
  simp only [chartSquare,hc]

private def patch {Y : SourceReducedComplexSpace} {ι : Type}
    (e : ι → LocalEmbedding Y) (O : ι → Opens Y.obj.left)
    (hsub : ∀ i, (O i : Set Y.obj.left) ⊆ range (e i).toPoint)
    (y : Y.obj.left) : ℝ := by
  classical
  exact if h : ∃ i, y ∈ O i then
    chartSquare (e (Classical.choose h)) y (hsub _ (Classical.choose_spec h))
  else 0

private theorem patch_nonneg {Y : SourceReducedComplexSpace} {ι : Type}
    (e : ι → LocalEmbedding Y) (O : ι → Opens Y.obj.left)
    (hsub : ∀ i, (O i : Set Y.obj.left) ⊆ range (e i).toPoint)
    (y : Y.obj.left) : 0 ≤ patch e O hsub y := by
  classical
  unfold patch
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

private theorem patch_readback {Y : SourceReducedComplexSpace} {ι : Type}
    (e : ι → LocalEmbedding Y) (O : ι → Opens Y.obj.left)
    (hsub : ∀ i, (O i : Set Y.obj.left) ⊆ range (e i).toPoint)
    (hpair : Pairwise fun i j => Disjoint (O i : Set Y.obj.left) (O j : Set Y.obj.left))
    (i : ι) (c : (e i).carrier) (hc : (e i).toPoint c ∈ O i) :
    patch e O hsub ((e i).toPoint c) = ‖c.val.val‖ ^ 2 := by
  classical
  unfold patch
  split_ifs with h
  · have hi : Classical.choose h = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hpair hne) (Classical.choose_spec h) hc
    have htransport (j : ι) (hji : j = i)
        (hj : (e i).toPoint c ∈ range (e j).toPoint) :
        chartSquare (e j) ((e i).toPoint c) hj = ‖c.val.val‖ ^ 2 := by
      subst j
      exact chartSquare_readback (e i) c hj
    exact htransport (Classical.choose h) hi _
  · exact (h ⟨i,hc⟩).elim

theorem exists_window_potential {X Y : SourceReducedComplexSpace}
    (p : Y ⟶ X) (hp : IsProperMap p.hom.left.base)
    (x : X.obj.left) (hf : (p.hom.left.base ⁻¹' {x}).Finite) :
    ∃ (V : Opens X.obj.left), x ∈ V ∧
      ∃ rho : Y.obj.left → ℝ, (∀ y, 0 ≤ rho y) ∧
      ∀ y : Y.obj.left, p.hom.left.base y ∈ V →
        ∃ e : LocalEmbedding Y,
          y ∈ range e.toPoint ∧
          range e.toPoint ⊆ p.hom.left.base ⁻¹' (V : Set X.obj.left) ∧
          ContDiffOn ℝ ∞ (fun z : ComplexModel e.dim => ‖z‖ ^ 2) e.ambient ∧
          (∀ z ∈ e.ambient, ∀ v : ComplexModel e.dim, v ≠ 0 →
            0 < leviForm (fun w : ComplexModel e.dim => ‖w‖ ^ 2) z v) ∧
          ∀ c : e.carrier, rho (e.toPoint c) = ‖c.val.val‖ ^ 2 := by
  classical
  obtain ⟨V,O,hx,_hmem,hpair,hsub,hcover⟩ :=
    NativeNov16FiniteFibreChartWindows.exists_disjoint_chart_windows p hp x hf
  let e : (p.hom.left.base ⁻¹' {x}) → LocalEmbedding Y := fun q => LocalEmbedding.ofPoint Y q.val
  let rho : Y.obj.left → ℝ := patch e O hsub
  refine ⟨V,hx,rho,patch_nonneg e O hsub,?_⟩
  intro y hy
  obtain ⟨q,hq,_hunique⟩ := hcover y hy
  obtain ⟨c,hcy⟩ := hsub q hq
  let N : Set Y.obj.left := (O q : Set Y.obj.left) ∩ p.hom.left.base ⁻¹' (V : Set X.obj.left)
  have hN : IsOpen N := (O q).isOpen.inter (V.isOpen.preimage hp.continuous)
  have hcN : (e q).toPoint c ∈ N := by
    rw [hcy]
    exact ⟨hq,hy⟩
  obtain ⟨T,hT,he,hRange⟩ := (e q).exists_restrict_to_open c hN hcN
  refine ⟨(e q).restrict T hT,?_,?_,(contDiff_norm_sq ℝ).contDiffOn,?_,?_⟩
  · rwa [hcy] at he
  · intro z hz
    exact (hRange hz).2
  · intro z _hz v hv
    exact leviForm_norm_sq_pos z hv
  · intro a
    let a' : (e q).carrier := ⟨Opens.inclusion hT a.val,a.property⟩
    have hPoint : ((e q).restrict T hT).toPoint a = (e q).toPoint a' := rfl
    have ha : (e q).toPoint a' ∈ O q := by
      rw [← hPoint]
      exact (hRange (mem_range_self a)).1
    rw [hPoint]
    exact patch_readback e O hsub hpair q a' ha

theorem normalization_window_potential (X : SourceReducedComplexSpace)
    (x : X.obj.left) :
    let N := NativeNov16NormalizationSpace.source X
    let p := NativeNov16NormalizationSpace.projection X
    ∃ (V : Opens X.obj.left), x ∈ V ∧
      ∃ rho : N.obj.left → ℝ, (∀ y, 0 ≤ rho y) ∧
      ∀ y : N.obj.left, p.hom.left.base y ∈ V →
        ∃ e : LocalEmbedding N,
          y ∈ range e.toPoint ∧
          range e.toPoint ⊆ p.hom.left.base ⁻¹' (V : Set X.obj.left) ∧
          ContDiffOn ℝ ∞ (fun z : ComplexModel e.dim => ‖z‖ ^ 2) e.ambient ∧
          (∀ z ∈ e.ambient, ∀ v : ComplexModel e.dim, v ≠ 0 →
            0 < leviForm (fun w : ComplexModel e.dim => ‖w‖ ^ 2) z v) ∧
          ∀ c : e.carrier, rho (e.toPoint c) = ‖c.val.val‖ ^ 2 := by
  exact exists_window_potential (NativeNov16NormalizationSpace.projection X)
    (NativeNov16NormalizationSpace.normal_proper_finite_surjective X).2.1 x
    ((NativeNov16NormalizationSpace.normal_proper_finite_surjective X).2.2.1 x)

end SGPT.Unibranch.NativeNov16FiniteFibreLocalPotential
