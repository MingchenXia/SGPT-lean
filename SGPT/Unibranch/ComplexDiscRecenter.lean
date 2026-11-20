import SGPT.Unibranch.ComplexSpaceFornaessNarasimhan
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal

/-! Actual original disk affine recentering and genuine all-center assembly.
Blueprint: complex-disc-recenter.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.SourceReducedComplexSpace

private theorem recenter_maps (s : ℂ) (d : ℝ) (hd : 0 < d) (hwindow : ‖s‖+d ≤ 1)
    {z : ComplexModel 1} (hz : z ∈ unitDiscOpens) :
    discCoordinate (s+(d : ℂ)*z 0) ∈ unitDiscOpens := by
  change discCoordinate (s+(d : ℂ)*z 0) ∈ ball 0 1
  rw [mem_ball_zero_iff,norm_discCoordinate]
  calc
    ‖s+(d : ℂ)*z 0‖ ≤ ‖s‖+‖(d : ℂ)*z 0‖ := norm_add_le _ _
    _ = ‖s‖+d*‖z 0‖ := by rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hd.le]
    _ < ‖s‖+d := by nlinarith [norm_le_of_mem_unitDiscOpens hz]
    _ ≤ 1 := hwindow

/-- The ACTUAL original affine disk morphism with its genuine sheaf map. -/
def recenterMorphism (s : ℂ) (d : ℝ) (hd : 0 < d) (hwindow : ‖s‖+d ≤ 1) : unitDisc ⟶ unitDisc :=
  discMorphism unitDiscOpens (fun z => discCoordinate (s+(d : ℂ)*z 0))
    (discCoordinate.contDiff.comp (contDiff_const.add (contDiff_const.mul
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contDiff)))
    (fun _ hz => recenter_maps s d hd hwindow hz)

/-- Literal actual affine point-map readback. -/
@[simp] theorem recenterMorphism_apply (s : ℂ) (d : ℝ) (hd : 0 < d) (hw : ‖s‖+d ≤ 1)
    (c : (univ : Set unitDiscOpens)) :
    ((recenterMorphism s d hd hw).hom.left.base c).val.val =
      discCoordinate (s+(d : ℂ)*c.val.val 0) := rfl

/-- SAME original reader and actual composed-disk morphism at every actual parameter. -/
theorem discPullback_comp_recenter {X : SourceReducedComplexSpace}
    (f : unitDisc ⟶ X) (φ : X.obj.left → EReal)
    (s : ℂ) (d : ℝ) (hd : 0 < d) (hw : ‖s‖+d ≤ 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    discPullback (recenterMorphism s d hd hw ≫ f) φ z = discPullback f φ (s+(d : ℂ)*z) := by
  have hzD := discCoordinate_mem_unitDiscOpens hz
  have haD : discCoordinate (s+(d : ℂ)*z) ∈ unitDiscOpens := by
    simpa only [discCoordinate_apply_zero] using recenter_maps s d hd hw hzD
  unfold discPullback modelPullback
  rw [dif_pos hzD,dif_pos haD]
  change φ (f.hom.left.base ((recenterMorphism s d hd hw).hom.left.base
      ⟨⟨discCoordinate z,hzD⟩,trivial⟩)) =
    φ (f.hom.left.base ⟨⟨discCoordinate (s+(d : ℂ)*z),haD⟩,trivial⟩)
  apply congrArg φ
  apply congrArg f.hom.left.base
  apply Subtype.ext
  apply Subtype.ext
  rw [recenterMorphism_apply,discCoordinate_apply_zero]

/-- A genuine native recentered germ returns to its SAME actual center
using the actual continuous-linear inverse, not a supplied inverse certificate. -/
theorem plurisubharmonicAt_of_recentered {u : ℂ → EReal} (s : ℂ) (d : ℝ) (hd : d ≠ 0)
    (hu : PlurisubharmonicAt (fun z : ℂ => u (s+(d : ℂ)*z)) 0) :
    PlurisubharmonicAt u s := by
  let L : ℂ →L[ℂ] ℂ := (ContinuousLinearMap.id ℂ ℂ).smulRight (d : ℂ)⁻¹
  let b : ℂ := -(s/(d : ℂ))
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hzero : b+L s = 0 := by dsimp [b,L];field_simp;ring
  have hz : PlurisubharmonicAt (fun z : ℂ => u (s+(d : ℂ)*z)) (b+L s) := hzero ▸ hu
  have h := PlurisubharmonicAt.comp_affine L b hz
  have heq : (fun y : ℂ => u (s+(d : ℂ)*(b+L y))) = u := by
    funext y
    congr 1
    dsimp [b,L]
    field_simp [hdC]
    ring
  simpa only [heq] using h

/-- The actual all-disk zero-germ family yields genuine PSH germs at EVERY
actual scalar center. Proper descent manufactures this family internally. -/
theorem plurisubharmonicOn_discPullback_of_zero_germs {X : SourceReducedComplexSpace}
    (φ : X.obj.left → EReal)
    (hzero : ∀ g : unitDisc ⟶ X,PlurisubharmonicAt (discPullback g φ) (0 : ℂ))
    (f : unitDisc ⟶ X) : PlurisubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1) := by
  intro s hs
  have hsNorm : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
  let d : ℝ := (1-‖s‖)/2
  have hd : 0 < d := by dsimp [d];linarith
  have hw : ‖s‖+d ≤ 1 := by dsimp [d];linarith
  let g := recenterMorphism s d hd hw ≫ f
  obtain ⟨Ω,hΩ,hΩ0,hraw⟩ := hzero g
  have hshift : PlurisubharmonicAt (fun z : ℂ => discPullback f φ (s+(d : ℂ)*z)) 0 := by
    refine ⟨Ω ∩ ball (0 : ℂ) 1,hΩ.inter isOpen_ball,⟨hΩ0,mem_ball_self zero_lt_one⟩,?_⟩
    apply (hraw.mono inter_subset_left).congr
    intro z hz
    exact discPullback_comp_recenter f φ s d hd hw hz.2
  exact plurisubharmonicAt_of_recentered s d (ne_of_gt hd) hshift

end SGPT.Unibranch.SourceReducedComplexSpace
