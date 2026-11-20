import SGPT.Unibranch.ComplexSpaceFormPullbackPotentials

/-! Actual domain functoriality and literal fiber-gauge vanishing for
ORIGINAL singular-space forms. Blueprint:
complex-space-form-constant-fiber.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.SpaceForm

/-- Actual positive-degree form pullback along an actually constant
original domain morphism is zero, with the lift manufactured internally. -/
theorem pullbackToDomain_eq_zero_of_constant {X : SourceReducedComplexSpace}
    {k m : ℕ} (θ : SpaceForm X (k+1)) {U : Opens (ComplexModel m)}
    (F : domainSpace U ⟶ X) (x : X.obj.left)
    (hF : ∀ c : (univ : Set U),F.hom.left.base c = x)
    {z : ComplexModel m} (hz : z ∈ U) : pullbackToDomain θ F z = 0 := by
  let A := Classical.choice (domainLift_nonempty θ F ⟨z,hz⟩)
  obtain ⟨a,ha,hpa⟩ := A.factor ⟨⟨z,hz⟩,trivial⟩ A.mem
  have heq : A.lift =ᶠ[𝓝 z] (fun _ => a.val.val) := by
    filter_upwards [A.isOpen.mem_nhds A.mem] with w hw
    obtain ⟨b,hb,hpb⟩ := A.factor ⟨⟨w,A.subset hw⟩,trivial⟩ hw
    have hba : b = a := (θ.chart A.chart).toPoint_injective
      ((hpb.trans (hF _)).trans (hpa.trans (hF _)).symm)
    rw [← hb,hba]
  have hder : fderiv ℝ A.lift z = 0 := by
    rw [heq.fderiv_eq]
    exact fderiv_const_apply _
  rw [pullbackToDomain_eq θ F A A.mem]
  simp only [pullbackForm,hder]
  ext v
  simp

/-- Genuine original form pullback is functorial when read on EVERY actual
source domain. Neither desired tensor identity nor a supplied lift is input. -/
theorem pullbackToDomain_pullback {X Y : SourceReducedComplexSpace} {k m : ℕ}
    (θ : SpaceForm X k) (π : Y ⟶ X) {U : Opens (ComplexModel m)}
    (F : domainSpace U ⟶ Y)
    {z : ComplexModel m} (hz : z ∈ U) :
    pullbackToDomain (pullback θ π) F z = pullbackToDomain θ (F ≫ π) z := by
  let A := Classical.choice (domainLift_nonempty (pullback θ π) F ⟨z,hz⟩)
  let B := Classical.choice (domainLift_nonempty θ (F ≫ π) ⟨z,hz⟩)
  let D : Set (ComplexModel m) := A.window ∩ B.window
  have hD : IsOpen D := A.isOpen.inter B.isOpen
  have hzD : z ∈ D := ⟨A.mem,B.mem⟩
  have hG : DifferentiableOn ℂ (A.chart.lift ∘ A.lift) D :=
    ((A.chart.holomorphic.differentiableOn (by simp)).comp
      (A.holomorphic.differentiableOn (by simp)) A.maps).mono inter_subset_left
  have hB : DifferentiableOn ℂ B.lift D :=
    (B.holomorphic.differentiableOn (by simp)).mono inter_subset_right
  have hpoints : ∀ w ∈ D,∃ (a : (θ.chart A.chart.chart).carrier) (b : (θ.chart B.chart).carrier),
      a.val.val = (A.chart.lift ∘ A.lift) w ∧ b.val.val = B.lift w ∧
        (θ.chart A.chart.chart).toPoint a = (θ.chart B.chart).toPoint b := by
    intro w hw
    let c : (univ : Set U) := ⟨⟨w,A.subset hw.1⟩,trivial⟩
    obtain ⟨a,ha,hpa⟩ := A.factor c hw.1
    obtain ⟨b,hb,hpb⟩ := A.chart.factor a
    obtain ⟨d,hd,hpd⟩ := B.factor c hw.2
    refine ⟨b,d,?_,hd,?_⟩
    · simpa only [ha,Function.comp_apply] using hb
    · exact hpb.trans ((congrArg π.hom.left.base hpa).trans hpd.symm)
  have hcore := pullback_eq_of_compatible_points θ A.chart.chart B.chart hD hG hB hpoints hzD
  have hAr : DifferentiableAt ℝ A.lift z :=
    ((A.holomorphic.differentiableOn (by simp)).differentiableAt
      (A.isOpen.mem_nhds A.mem)).restrictScalars ℝ
  have hPr : DifferentiableAt ℝ A.chart.lift (A.lift z) :=
    ((A.chart.holomorphic.differentiableOn (by simp)).differentiableAt
      (A.chart.source.ambient.isOpen.mem_nhds (A.maps A.mem))).restrictScalars ℝ
  have hleft := pullbackToDomain_eq (pullback θ π) F A A.mem
  change pullbackToDomain (pullback θ π) F z =
    pullbackForm A.lift (pullbackForm A.chart.lift (θ.rep A.chart.chart)) z at hleft
  exact hleft.trans ((pullbackForm_comp hAr hPr (θ.rep A.chart.chart)).trans
    (hcore.trans (pullbackToDomain_eq θ (F ≫ π) B B.mem).symm))

/-- Literal zero along ANY constant composite into the original base. -/
theorem pullbackToDomain_pullback_eq_zero_of_constant
    {X Y : SourceReducedComplexSpace} {k m : ℕ} (θ : SpaceForm X (k+1)) (π : Y ⟶ X)
    {U : Opens (ComplexModel m)} (F : domainSpace U ⟶ Y)
    (x : X.obj.left) (hF : ∀ c : (univ : Set U),π.hom.left.base (F.hom.left.base c) = x)
    {z : ComplexModel m} (hz : z ∈ U) : pullbackToDomain (pullback θ π) F z = 0 := by
  rw [pullbackToDomain_pullback θ π F hz]
  exact pullbackToDomain_eq_zero_of_constant θ (F ≫ π) x hF hz

/-- ANY original ambient representative is recovered along ANY genuine
coordinate lift of the SAME original domain morphism. -/
theorem pullbackToDomain_eq_of_restrictsTo {X : SourceReducedComplexSpace}
    {k m : ℕ} (θ : SpaceForm X k) {U : Opens (ComplexModel m)}
    (F : domainSpace U ⟶ X) {e : LocalEmbedding X} {v : AmbientForm e.dim k}
    (hv : θ.RestrictsTo e v) {D : Set (ComplexModel m)} (hD : IsOpen D) (hDU : D ⊆ U)
    {G : ComplexModel m → ComplexModel e.dim} (hG : DifferentiableOn ℂ G D)
    (hfac : ∀ c : (univ : Set U),c.val.val ∈ D →
      ∃ b : e.carrier,b.val.val = G c.val.val ∧ e.toPoint b = F.hom.left.base c)
    {z : ComplexModel m} (hz : z ∈ D) :
    pullbackToDomain θ F z = pullbackForm G v z := by
  let A := Classical.choice (domainLift_nonempty θ F ⟨z,hDU hz⟩)
  let W : Set (ComplexModel m) := D ∩ A.window
  have hW : IsOpen W := hD.inter A.isOpen
  have hpoints : ∀ w ∈ W,∃ (a : e.carrier) (b : (θ.chart A.chart).carrier),
      a.val.val = G w ∧ b.val.val = A.lift w ∧ e.toPoint a = (θ.chart A.chart).toPoint b := by
    intro w hw
    let c : (univ : Set U) := ⟨⟨w,hDU hw.1⟩,trivial⟩
    obtain ⟨a,ha,hpa⟩ := hfac c hw.1
    obtain ⟨b,hb,hpb⟩ := A.factor c hw.2
    exact ⟨a,b,ha,hb,hpa.trans hpb.symm⟩
  have hcore := pullback_eq_of_restrictsTo θ hv A.chart hW
    (hG.mono inter_subset_left)
    ((A.holomorphic.differentiableOn (by simp)).mono inter_subset_right)
    hpoints ⟨hz,A.mem⟩
  exact (pullbackToDomain_eq θ F A A.mem).trans hcore.symm

/-- The actual gauge of the SAME pulled-back form has zero ddc on
holomorphic domain probes whose ORIGINAL composite to the base is constant.
Zero ddc and pluriharmonicity are outputs, never supplied certificates. -/
theorem smoothDDC_comp_eq_zero_of_constant {X Y : SourceReducedComplexSpace} {m : ℕ}
    (θ : SpaceForm X 2) (π : Y ⟶ X) {e : LocalEmbedding Y} {g : ComplexModel e.dim → ℝ}
    (hg : ContDiffOn ℝ ∞ g e.ambient) (hv : (pullback θ π).RestrictsTo e (smoothDDC g))
    {U : Opens (ComplexModel m)} (F : domainSpace U ⟶ Y) (x : X.obj.left)
    (hF : ∀ c : (univ : Set U),π.hom.left.base (F.hom.left.base c) = x)
    {D : Set (ComplexModel m)} (hD : IsOpen D) (hDU : D ⊆ U)
    {G : ComplexModel m → ComplexModel e.dim} (hG : ContDiffOn ℂ ∞ G D)
    (hfac : ∀ c : (univ : Set U),c.val.val ∈ D →
      ∃ b : e.carrier,b.val.val = G c.val.val ∧ e.toPoint b = F.hom.left.base c)
    {z : ComplexModel m} (hz : z ∈ D) : smoothDDC (g ∘ G) z = 0 := by
  have hmaps : MapsTo G D e.ambient := by
    intro w hw
    obtain ⟨b,hb,-⟩ := hfac ⟨⟨w,hDU hw⟩,trivial⟩ hw
    rw [← hb]
    exact b.val.property
  have hread := pullbackToDomain_eq_of_restrictsTo (pullback θ π) F hv hD hDU
    (hG.differentiableOn (by simp)) hfac hz
  have hzero := pullbackToDomain_pullback_eq_zero_of_constant θ π F x hF (hDU hz)
  have hnat := HolomorphicDDC.smoothDDC_comp hD e.ambient.isOpen hG hg hmaps hz
  exact hnat.trans (hread.symm.trans hzero)

end SGPT.Unibranch.SpaceForm
