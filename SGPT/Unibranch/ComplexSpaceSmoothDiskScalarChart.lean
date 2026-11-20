import SGPT.Unibranch.ComplexSpaceDiskSmoothGerm
import SGPT.Unibranch.ComplexSpaceSmoothPSHMaximum
import SGPT.Foundations.Analysis.Pending.RegularDirection

/-! Actual scalar-chart and regular-line extraction for the SAME original
disk germ. Blueprint: complex-space-smooth-disk-scalar-chart.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch
open SourceReducedComplexSpace

/-- Primitive actual original smooth chart and genuine scalar readback only. -/
structure SmoothDiskScalarChart {T : SourceReducedComplexSpace}
    (a : T ⟶ unitDisc) (t : T.obj.left) where
  dim : ℕ
  ambient : Opens (ComplexModel dim)
  map : (modelOver ambient (univ : Set ambient)).left ⟶ T.obj.left
  isOpenImmersion : LocallyRingedSpace.IsOpenImmersion map
  overPoint : map ≫ T.obj.hom = (modelOver ambient (univ : Set ambient)).hom
  point : (univ : Set ambient)
  pointImage : map.base point = t
  window : Opens (ComplexModel dim)
  window_subset : window ≤ ambient
  mem_window : point.val.val ∈ window
  scalar : ComplexModel dim → ℂ
  holomorphic : ContDiffOn ℂ ∞ scalar window
  readback : ∀ c : (univ : Set ambient),c.val.val ∈ window →
    scalar c.val.val = (a.hom.left.base (map.base c)).val.val 0

/-- ORIGINAL varying-dimension smoothness produces actual scalar coordinates
of the SAME original morphism, with no incoming analytic-chart certificate. -/
theorem exists_smoothDiskScalarChart {T : SourceReducedComplexSpace}
    (hT : T.IsSmooth) (a : T ⟶ unitDisc) (t : T.obj.left) :
    Nonempty (SmoothDiskScalarChart a t) := by
  obtain ⟨d,U,F,hFI,hFp,_hconn,⟨c,hc⟩,_hsub⟩ :=
    hT.hasDomainCharts t univ isOpen_univ trivial
  let e := LocalEmbedding.model unitDiscOpens (univ : Set unitDiscOpens) isComplexAnalyticSubset_univ
  have hp : (F ≫ a.hom.left) ≫ unitDisc.obj.hom = (modelOver U (univ : Set U)).hom := by
    rw [Category.assoc,Over.w a.hom,hFp]
  have he : (F ≫ a.hom.left).base c ∈ range e.toPoint := ⟨_,rfl⟩
  obtain ⟨W,hW,hcW,hWU,G,hG,_hGmaps,hfac⟩ :=
    LocalEmbedding.exists_contDiffOn_factor (F ≫ a.hom.left) hp e c he
  refine ⟨⟨d,U,F,hFI,hFp,c,hc,⟨W,hW⟩,hWU,hcW,fun z => G z 0,?_,?_⟩⟩
  · exact (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contDiff.comp_contDiffOn hG
  · intro z hz
    obtain ⟨b,hb,hpb⟩ := hfac z hz
    change b = a.hom.left.base (F.base z) at hpb
    exact (congrArg (fun v : ComplexModel 1 => v 0) hb).symm.trans
      (congrArg (fun v : (univ : Set unitDiscOpens) => v.val.val 0) hpb)

namespace SmoothDiskScalarChart
variable {T : SourceReducedComplexSpace} {a : T ⟶ unitDisc} {t : T.obj.left}

/-- The original nonconstant disk germ internally gives an actual regular
complex line and a POSITIVE finite order with actual analytic unit. -/
theorem exists_regular_direction (C : SmoothDiskScalarChart a t)
    (hat : a.hom.left.base t = zeroDiscPoint)
    (hnot : ¬ ∀ᶠ q in 𝓝 t,(a.hom.left.base q).val.val 0 = 0) :
    ∃ (v : ComplexModel C.dim) (k : ℕ) (u : ℂ → ℂ),
      0 < k ∧ AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ),C.point.val.val+s • v ∈ C.window ∧
        C.scalar (C.point.val.val+s • v) = s^k*u s := by
  let c := C.point.val.val
  let H : ComplexModel C.dim → ℂ := fun z => C.scalar (z+c)
  have h0 : H 0 = 0 := by
    change C.scalar (0+c) = 0
    rw [zero_add,C.readback C.point C.mem_window,C.pointImage,hat]
    rfl
  have hW : ∀ᶠ z in 𝓝 (0 : ComplexModel C.dim),z+c ∈ C.window := by
    have hcont : Continuous (fun z : ComplexModel C.dim => z+c) := by fun_prop
    have ht : Tendsto (fun z : ComplexModel C.dim => z+c) (𝓝 0) (𝓝 c) := by
      simpa only [zero_add] using hcont.tendsto 0
    exact ht.eventually (C.window.isOpen.mem_nhds C.mem_window)
  have hdiff : ∀ᶠ z in 𝓝 (0 : ComplexModel C.dim),DifferentiableAt ℂ H z := by
    filter_upwards [hW] with z hz
    exact ((C.holomorphic.contDiffAt (C.window.isOpen.mem_nhds hz)).differentiableAt
      (by simp)).comp z (differentiableAt_id.add_const c)
  have hne : ¬ H =ᶠ[𝓝 (0 : ComplexModel C.dim)] 0 := by
    intro hzero
    have hcoords : Continuous (fun q : (univ : Set C.ambient) => q.val.val) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hsub : Filter.Tendsto (fun q : (univ : Set C.ambient) => q.val.val-c)
        (𝓝 C.point) (𝓝 (0 : ComplexModel C.dim)) := by
      have hcsub : Continuous (fun q : (univ : Set C.ambient) => q.val.val-c) :=
        hcoords.sub continuous_const
      simpa only [c,sub_self] using (hcsub.continuousAt (x := C.point)).tendsto
    have hqzero := hsub.eventually hzero
    have hqW := hcoords.continuousAt (x := C.point) |>.eventually
      (C.window.isOpen.mem_nhds C.mem_window)
    have hlocal : ∀ᶠ q in 𝓝 C.point,(a.hom.left.base (C.map.base q)).val.val 0 = 0 := by
      filter_upwards [hqzero,hqW] with q hq hzW
      rw [← C.readback q hzW]
      change H (q.val.val-c) = 0 at hq
      simpa only [H,sub_add_cancel] using hq
    apply hnot
    have hmap := C.isOpenImmersion.base_open.map_nhds_eq C.point
    change Filter.map C.map.base (𝓝 C.point) = 𝓝 (C.map.base C.point) at hmap
    rw [C.pointImage] at hmap
    rw [← hmap]
    exact eventually_map.mpr hlocal
  have he : ∃ e : ComplexModel C.dim,e ≠ 0 := by
    by_contra hall
    have hz : ∀ z : ComplexModel C.dim,z = 0 := by simpa only [not_exists,not_not] using hall
    apply hne
    exact Filter.Eventually.of_forall (fun z => by rw [hz z];exact h0)
  obtain ⟨e,he⟩ := he
  obtain ⟨L,k,u,hu,hu0,hfactor⟩ := exists_regular_continuousLinearEquiv hdiff hne he
  have hk : 0 < k := by
    by_contra hkn
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hkn
    have hf := hfactor.self_of_nhds
    simp only [hk0,zero_smul,map_zero,pow_zero,one_mul] at hf
    exact hu0 (hf.symm.trans h0)
  have hline : Continuous (fun s : ℂ => c+s • L e) := by fun_prop
  have hmem : ∀ᶠ s in 𝓝 (0 : ℂ),c+s • L e ∈ C.window := by
    have ht : Tendsto (fun s : ℂ => c+s • L e) (𝓝 0) (𝓝 c) := by
      simpa only [zero_smul,add_zero] using hline.tendsto 0
    exact ht.eventually (C.window.isOpen.mem_nhds C.mem_window)
  refine ⟨L e,k,u,hk,hu,hu0,?_⟩
  filter_upwards [hfactor,hmem] with s hs hm
  refine ⟨hm,?_⟩
  simpa only [H,map_smul,add_comm] using hs

end SmoothDiskScalarChart

/-- ONLY original proper disk data internally manufacture the actual smooth
source, scalar chart and positive regular direction, with the SAME point square. -/
theorem exists_regular_disk_germ {X Y : SourceReducedComplexSpace}
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (f : unitDisc ⟶ X) :
    ∃ (T : SourceReducedComplexSpace) (a : T ⟶ unitDisc) (b : T ⟶ Y) (t : T.obj.left),
      T.IsSmooth ∧ a.hom.left.base t = zeroDiscPoint ∧
      (∀ q : T.obj.left,π.hom.left.base (b.hom.left.base q) = f.hom.left.base (a.hom.left.base q)) ∧
      ∃ (C : SmoothDiskScalarChart a t) (v : ComplexModel C.dim) (k : ℕ) (u : ℂ → ℂ),
        0 < k ∧ AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        ∀ᶠ s in 𝓝 (0 : ℂ),C.point.val.val+s • v ∈ C.window ∧
          C.scalar (C.point.val.val+s • v) = s^k*u s := by
  obtain ⟨T,a,b,t,hT,hat,_hcl,hnot,hsquare⟩ := exists_smooth_disk_nonzero_germ π hπ f
  obtain ⟨C⟩ := exists_smoothDiskScalarChart hT a t
  obtain ⟨v,k,u,hk,hu,hu0,hline⟩ := C.exists_regular_direction hat hnot
  exact ⟨T,a,b,t,hT,hat,hsquare,C,v,k,u,hk,hu,hu0,hline⟩

end SGPT.Unibranch
