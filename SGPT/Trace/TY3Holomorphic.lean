import SGPT.Trace.TYCorPSH
import SGPT.Unibranch.KS2KahlerSpace
import SGPT.Foundations.Analysis.Pending.HironakaG10ChowRiemannExtension

/-!
# The lifts `ν : V → Ỹ` of resolutions are holomorphic

Source: `chapter_trace.tex`, `def:traceop` and its footnote (the trace operator takes values in
`QPSH(Ỹ)`, `Ỹ` the normalization of `Y`; `d_S` on `Ỹ` is read on resolutions of `Ỹ`), and
Appendix B (`appendix_unibranch.tex`, `def:unibranch:L105`: smooth functions and forms on a complex
space are locally restrictions of ambient ones under local embeddings).

The trace predicate on `Ỹ` (`TildeY.IsTrace`, lane TY) quantifies over all resolutions
`ν : V → Ỹ` of `Ỹ` (`TildeY.Resolution`), which only come with a *continuous* lift `ν` of the
resolution `ι : V → X` of `Y`. This file proves that for the normalization `Ỹ` every such lift is
holomorphic in the local embeddings of `Ỹ`, and hence that smooth functions on `Ỹ` pull back to
smooth functions on `V`:

* `LocalEmbedding.coord`: the ambient coordinates `Ỹ ⊇ E(C) → C ⊆ ℂ^N` of a local embedding
  (continuous on the image, `continuousAt_coord`);
* `LocalEmbedding.mdifferentiableAt_coord_comp_morphism`: for a morphism of complex spaces
  `F : (V, 𝒪_V) → X` from a manifold, the coordinates of `F` in every local embedding of `X` are
  holomorphic (local holomorphic lifts of morphisms);
* `Normalization.mdifferentiableAt_coord_comp_ν`: **for every resolution `ν : V → Ỹ` of the
  normalization, the coordinates of `ν` in every local embedding of `Ỹ` are holomorphic.**
  Proof: `ν` and the canonical resolution morphism `F : (V₀, 𝒪) → Ỹ` (`TYCorPSH`) are dominated by
  a common resolution `V₃` with modifications `p₀ : V₃ → V₀`, `p : V₃ → V` and `ν ∘ p = F ∘ p₀`;
  off the thin analytic set `B ⊆ V` over which `p` has a holomorphic inverse `s`, `ν = F ∘ p₀ ∘ s`
  is holomorphic; `ν` is continuous, hence holomorphic everywhere by the Riemann extension theorem
  (`HironakaG10ChowRiemannExtension.mdifferentiableAt_of_continuousOn`);
* `Normalization.chartSmooth_comp_ν`: for every smooth function `ρ` on `Ỹ`
  (`SourceReducedComplexSpace.IsSmoothFunction`), `ρ ∘ ν` is smooth on `V`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.LocalEmbedding

open SGPT.Foundations.Analysis.FirstPass OriginalNativeModification

variable {X : SourceReducedComplexSpace}

/-- The ambient coordinates of a point of `X` in the local embedding `E` (the inverse of the open
embedding `C → X`, followed by `C ⊆ Ω ⊆ ℂ^N`; `0` off the image of `E`). -/
def coord (E : LocalEmbedding X) (x : X.obj.left) : ComplexModel E.dim := by
  classical
  exact if h : x ∈ range E.toPoint then (Classical.choose h).val.val else 0

theorem coord_toPoint (E : LocalEmbedding X) (c : E.carrier) :
    E.coord (E.toPoint c) = c.val.val := by
  classical
  have h : E.toPoint c ∈ range E.toPoint := ⟨c, rfl⟩
  unfold coord
  rw [dif_pos h, E.toPoint_injective (Classical.choose_spec h)]

/-- The coordinates are continuous on the (open) image of the local embedding. -/
theorem continuousAt_coord (E : LocalEmbedding X) {x : X.obj.left} (hx : x ∈ range E.toPoint) :
    ContinuousAt E.coord x := by
  obtain ⟨c, rfl⟩ := hx
  have h1 : E.coord ∘ E.toPoint = fun c => c.val.val := funext E.coord_toPoint
  have hc : Continuous (fun c : E.carrier => (c.val.val : ComplexModel E.dim)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have h2 : Tendsto (E.coord ∘ E.toPoint) (𝓝 c) (𝓝 (E.coord (E.toPoint c))) := by
    rw [h1, E.coord_toPoint]
    exact hc.continuousAt
  unfold ContinuousAt
  rw [← E.isOpenEmbedding_toPoint.map_nhds_eq c]
  exact tendsto_map'_iff.mpr h2

/-- **Morphisms from manifolds are holomorphic in local embeddings.** For a morphism of complex
spaces `F : (V, 𝒪_V) → X` from a complex manifold and a local embedding `E` of `X`, the ambient
coordinates of `F` in `E` are holomorphic near every point mapped into the image of `E`. -/
theorem mdifferentiableAt_coord_comp_morphism {m : ℕ} {V : Type} [TopologicalSpace V]
    [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V] (F : wholeModel (n := m) V ⟶ X)
    (E : LocalEmbedding X) {v : V} (hv : F.hom.left.base ⟨v, mem_univ v⟩ ∈ range E.toPoint) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel E.dim)
      (fun w => E.coord (F.hom.left.base ⟨w, mem_univ w⟩)) v := by
  set e := complexChartAt (n := m) v with he
  have hvs : v ∈ e.val.source := mem_complexChartAt_source v
  have hz : e.val v ∈ e.val.target := e.val.map_source hvs
  have hsymm : e.val.symm (e.val v) = v := e.val.left_inv hvs
  have hv' : F.hom.left.base ⟨e.val.symm (e.val v), mem_univ _⟩ ∈ range E.toPoint := by
    have hpt : (⟨e.val.symm (e.val v), mem_univ _⟩ : (wholeModel (n := m) V).obj.left) =
        ⟨v, mem_univ v⟩ := Subtype.ext hsymm
    rw [hpt]
    exact hv
  obtain ⟨A, hA⟩ := SpaceForm.morphismChartLift_cover F E ⟨e.val.symm (e.val v), mem_univ _⟩ hv'
  obtain ⟨W, hW, hzW, hWU, G, hG, hGmaps, hfac⟩ :=
    KSManifoldForm.exists_chartInverse_factor e A.source hz hA
  -- in the chart, the coordinates of `F` are `A.lift ∘ G`
  have hloc : ∀ y ∈ W, ∀ w : V, e.val.symm y = w →
      E.coord (F.hom.left.base ⟨w, mem_univ w⟩) = A.lift (G y) := by
    intro y hy w hw
    have hyT : y ∈ (KSManifoldForm.chartTarget e : Set (ComplexModel m)) := hWU hy
    obtain ⟨b, hb, hbp⟩ := hfac ⟨⟨y, hyT⟩, trivial⟩ hy
    obtain ⟨b', hb', hb'p⟩ := A.factor b
    have hpt : (KSManifoldForm.chartInverse e).hom.left.base ⟨⟨y, hyT⟩, trivial⟩ =
        ⟨w, mem_univ w⟩ := Subtype.ext ((KSManifoldForm.chartInverse_base e _).trans hw)
    rw [← hpt, ← hbp, ← hb'p, E.coord_toPoint, hb', hb]
  have hGd : DifferentiableAt ℂ G (e.val v) :=
    (hG.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hzW)
  have hLd : DifferentiableAt ℂ A.lift (G (e.val v)) :=
    (A.holomorphic.differentiableOn (by simp)).differentiableAt
      (A.source.ambient.isOpen.mem_nhds (hGmaps hzW))
  have hφ : MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel E.dim)
      (fun y => A.lift (G y)) (extChartAt 𝓘(ℂ, ComplexModel m) v v) :=
    (hLd.comp (e.val v) hGd).mdifferentiableAt
  have hchart := mdifferentiableAt_extChartAt (I := 𝓘(ℂ, ComplexModel m))
    (mem_chart_source (ComplexModel m) v)
  have hcomp := hφ.comp v hchart
  refine hcomp.congr_of_eventuallyEq ?_
  have hnhds : e.val.source ∩ e.val ⁻¹' W ∈ 𝓝 v :=
    e.val.continuousAt hvs |>.preimage_mem_nhds (hW.mem_nhds hzW) |> inter_mem
      (e.val.open_source.mem_nhds hvs)
  filter_upwards [hnhds] with w hw
  have hext : extChartAt 𝓘(ℂ, ComplexModel m) v w = e.val w := rfl
  simp only [Function.comp_apply, hext]
  exact hloc (e.val w) hw.2 w (e.val.left_inv hw.1)

end SGPT.Unibranch.LocalEmbedding

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
  SGPT.Unibranch.OriginalNativeModification

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

namespace Normalization

/-- **The lift of every resolution to the normalization is holomorphic.** Let `ν : V → Ỹ` be a
resolution of the normalization `Ỹ` of `Y` (`TildeY.Resolution`: a continuous lift of a resolution
`ι : V → X` of `Y`) and `E` a local embedding of `Ỹ`. Then the ambient coordinates of `ν` in `E`
are holomorphic near every point of `ν⁻¹(E)`. -/
theorem mdifferentiableAt_coord_comp_ν (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (N : (normalizationTildeY omega Y).Resolution)
    (E : LocalEmbedding (normalizationTildeY omega Y).space) {v : N.R.V}
    (hv : N.ν v ∈ range E.toPoint) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel E.dim)
      (fun w => E.coord (N.ν w)) v := by
  obtain ⟨N₀, F, -, hFN⟩ := exists_resolution_morphism omega Y
  obtain ⟨N₃, p₀, p, hp₀, hp, -, -, hν₀, hν⟩ := TildeY.Resolution.exists_common N₀ N
  obtain ⟨-, -, A, B, s, -, -, -, hBc, hBa, hBi, -, hs, hps, -⟩ := hp
  have hO : IsOpen (N.ν ⁻¹' range E.toPoint) := E.isOpen_range_toPoint.preimage N.continuous
  have hcont : ContinuousOn (fun w => E.coord (N.ν w)) (N.ν ⁻¹' range E.toPoint) :=
    fun w hw => ((E.continuousAt_coord hw).comp N.continuous.continuousAt).continuousWithinAt
  refine HironakaG10ChowRiemannExtension.mdifferentiableAt_of_continuousOn hO hcont hBa hBc hBi
    ?_ hv
  intro w hwO hwB
  -- off `B`, `ν = F ∘ p₀ ∘ s`
  have heq : ∀ w' ∉ B, N.ν w' = F.hom.left.base ⟨p₀ (s w'), mem_univ _⟩ := by
    intro w' hw'
    have h1 : N.ν (p (s w')) = N₃.ν (s w') := by rw [hν]; rfl
    rw [hps w' hw'] at h1
    rw [h1, hν₀, Function.comp_apply, hFN]
  have hF0 : F.hom.left.base ⟨p₀ (s w), mem_univ _⟩ ∈ range E.toPoint := by
    rw [← heq w hwB]
    exact hwO
  have hmF := LocalEmbedding.mdifferentiableAt_coord_comp_morphism F E hF0
  have hsw : MDifferentiableAt 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel Y.dim) s w :=
    ((hs w hwB).contMDiffAt (hBc.isOpen_compl.mem_nhds hwB)).mdifferentiableAt (by simp)
  have hp₀w : MDifferentiableAt 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel Y.dim) p₀ (s w) :=
    hp₀.1.mdifferentiableAt (by simp)
  have hcomp : MDifferentiableAt 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel E.dim)
      (fun w' => E.coord (F.hom.left.base ⟨p₀ (s w'), mem_univ _⟩)) w :=
    hmF.comp w (hp₀w.comp w hsw)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hBc.isOpen_compl.mem_nhds hwB] with w' hw'
  rw [heq w' hw']

/-- **Smooth functions on `Ỹ` pull back to smooth functions on every resolution of `Ỹ`.** -/
theorem chartSmooth_comp_ν (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) (N : (normalizationTildeY omega Y).Resolution)
    {ρ : (normalizationTildeY omega Y).space.obj.left → ℝ}
    (hρ : (normalizationTildeY omega Y).space.IsSmoothFunction ρ) :
    ChartSmooth (n := Y.dim) (fun v => ρ (N.ν v)) := by
  intro e z hz
  obtain ⟨E, ⟨c, hc⟩, g, hg, hgeq⟩ := hρ (N.ν (e.val.symm z))
  have hO : IsOpen (N.ν ⁻¹' range E.toPoint) := E.isOpen_range_toPoint.preimage N.continuous
  have hW' : IsOpen (e.val.target ∩ e.val.symm ⁻¹' (N.ν ⁻¹' range E.toPoint)) :=
    e.val.isOpen_inter_preimage_symm hO
  have hzW' : z ∈ e.val.target ∩ e.val.symm ⁻¹' (N.ν ⁻¹' range E.toPoint) := ⟨hz, ⟨c, hc⟩⟩
  have hd : DifferentiableOn ℂ (fun y => E.coord (N.ν (e.val.symm y)))
      (e.val.target ∩ e.val.symm ⁻¹' (N.ν ⁻¹' range E.toPoint)) := by
    intro y hy
    have h1 := mdifferentiableAt_coord_comp_ν omega Y N E hy.2
    have h2' : ContMDiffOn 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel Y.dim) ∞ e.val.symm
        e.val.target :=
      contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property)
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel Y.dim) 𝓘(ℂ, ComplexModel Y.dim) e.val.symm y :=
      ((h2' y hy.1).contMDiffAt (e.val.open_target.mem_nhds hy.1)).mdifferentiableAt (by simp)
    exact (h1.comp y h2).differentiableAt.differentiableWithinAt
  have hcd := contDiffOn_of_differentiableOn_complex hd hW'
  have hΦ : ContDiffAt ℝ ∞ (fun y => E.coord (N.ν (e.val.symm y))) z :=
    ((hcd z hzW').contDiffAt (hW'.mem_nhds hzW')).restrict_scalars ℝ
  have hgz : ContDiffAt ℝ ∞ g (E.coord (N.ν (e.val.symm z))) := by
    rw [← hc, E.coord_toPoint]
    exact hg.contDiffAt (E.ambient.isOpen.mem_nhds c.val.property)
  have hcomp : ContDiffAt ℝ ∞ (fun y => g (E.coord (N.ν (e.val.symm y)))) z := hgz.comp z hΦ
  show ContDiffWithinAt ℝ ∞ (fun y => ρ (N.ν (e.val.symm y))) e.val.target z
  refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hW'.mem_nhds hzW'] with y hy
  obtain ⟨c', hc'⟩ := hy.2
  rw [← hc', E.coord_toPoint, hgeq]

end Normalization

end SGPT.Trace.TY
