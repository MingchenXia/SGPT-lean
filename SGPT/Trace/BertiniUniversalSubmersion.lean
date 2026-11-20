import SGPT.Trace.BertiniUniversalGeometry

/-! Actual universal q local holomorphic sections and native submersion,
manufactured by the SAME original nonzero p(x) coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily
open scoped ProductComplexManifold

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i j : Fin (N + 1))

def parameterCoefficient (m : Fin N) (x : X) : ℂ :=
  affineLift j (affineChart j (p x)) (i.succAbove m)

def correctedParameter (m : Fin N) (ζ : ComplexModel N) (x : X) : ComplexModel N :=
  ζ - (localEquation p i j (ζ,x) / parameterCoefficient p i j m x) • EuclideanSpace.single m 1

omit [IsComplexManifold n X] in
theorem correctedParameter_equation_zero (m : Fin N) (ζ : ComplexModel N) (x : X)
    (hm : parameterCoefficient p i j m x ≠ 0) :
    localEquation p i j (correctedParameter p i j m ζ x,x) = 0 := by
  unfold correctedParameter localEquation
  rw [pairing_affineLift_sub_smul_single]
  change localEquation p i j (ζ,x) - parameterCoefficient p i j m x *
    (localEquation p i j (ζ,x) / parameterCoefficient p i j m x) = 0
  field_simp
  ring

omit [IsComplexManifold n X] in
theorem correctedParameter_eq_self (m : Fin N) (ζ : ComplexModel N) (x : X)
    (hzero : localEquation p i j (ζ,x) = 0) : correctedParameter p i j m ζ x = ζ := by
  simp only [correctedParameter,hzero,zero_div,zero_smul,sub_zero]

variable {j}

theorem exists_local_holomorphic_X_section (q₀ : affineIncidence p i) :
    letI := affineChartedSpace p i
    letI := affineComplex p i
    ∃ g : X → affineIncidence p i,
      g q₀.val.2 = q₀ ∧
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (N + n - 1)) ∞ g q₀.val.2 ∧
      ((nativeXMap p i : affineIncidence p i → X) ∘ g) =ᶠ[𝓝 q₀.val.2] id := by
  classical
  let := affineChartedSpace p i
  let := affineComplex p i
  let j := chartIndex (p q₀.val.2)
  have hj : p q₀.val.2 ∈ (affineChart j).source := mem_affineChart_chartIndex (p q₀.val.2)
  have hzero := (mem_affineIncidence_iff_localEquation p i j hj).mp q₀.property
  obtain ⟨m,hm⟩ := exists_succAbove_ne_zero_of_pairing_eq_zero (affineLift_ne_zero j _) hzero
  have hc : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (parameterCoefficient p i j m) q₀.val.2 :=
    contMDiffAt_of_eventually_mdifferentiableAt
      (holomorphicAt_affineLift_affineChart_comp p p.contMDiff j (i.succAbove m) hj)
  have hjoint : ContMDiffAt 𝓘(ℂ, ComplexModel (N + n)) 𝓘(ℂ, ℂ) ∞
      (localEquation p i j) q₀.val :=
    contMDiffAt_of_eventually_mdifferentiableAt (holomorphicAt_localEquation p i j hj)
  have hinc : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (N + n)) ∞
      (fun x : X => (q₀.val.1,x)) := contMDiff_prodMk contMDiff_const contMDiff_id
  have hF : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun x => localEquation p i j (q₀.val.1,x)) q₀.val.2 :=
    ContMDiffAt.comp (f := fun x : X => (q₀.val.1,x)) (g := localEquation p i j)
      q₀.val.2 hjoint hinc.contMDiffAt
  have hparam : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
      (correctedParameter p i j m q₀.val.1) q₀.val.2 :=
    contMDiffAt_const.sub ((hF.mul (hc.inv₀ hm)).smul contMDiffAt_const)
  have hnearj : ∀ᶠ x in 𝓝 q₀.val.2, p x ∈ (affineChart j).source :=
    p.contMDiff.continuous.continuousAt.eventually ((affineChart j).open_source.mem_nhds hj)
  have hnearc : ∀ᶠ x in 𝓝 q₀.val.2, parameterCoefficient p i j m x ≠ 0 := hc.continuousAt.eventually_ne hm
  obtain ⟨W,hW,hWo,hxW⟩ := eventually_nhds_iff.mp (hnearj.and hnearc)
  let g : X → affineIncidence p i := fun x => if hx : x ∈ W then
    ⟨(correctedParameter p i j m q₀.val.1 x,x),
      (mem_affineIncidence_iff_localEquation p i j (hW x hx).1).mpr
        (correctedParameter_equation_zero p i j m q₀.val.1 x (hW x hx).2)⟩ else q₀
  refine ⟨g,?_,?_,?_⟩
  · apply Subtype.ext
    simp only [g,dif_pos hxW]
    exact Prod.ext (correctedParameter_eq_self p i j m q₀.val.1 q₀.val.2 hzero) rfl
  · apply contMDiffAt_affineIncidence_of_val p i
    have hraw := contMDiffAt_nativePair (X := X) hparam contMDiffAt_id
    apply hraw.congr_of_eventuallyEq
    filter_upwards [hWo.mem_nhds hxW] with x hx
    simp only [g,dif_pos hx,id_eq]
  · filter_upwards [hWo.mem_nhds hxW] with x hx
    change (g x).val.2 = x
    simp only [g,dif_pos hx]

theorem surjective_mfderiv_nativeXMap (q₀ : affineIncidence p i) :
    letI := affineChartedSpace p i
    letI := affineComplex p i
    Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel (N + n - 1)) 𝓘(ℂ, ComplexModel n)
      (nativeXMap p i) q₀) := by
  let := affineChartedSpace p i
  let := affineComplex p i
  obtain ⟨g,hgq,hg,he⟩ := exists_local_holomorphic_X_section p i q₀
  have hd := mfderiv_comp q₀.val.2
    ((nativeXMap p i).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp))
  rw [hgq] at hd
  have hi : mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      ((nativeXMap p i : affineIncidence p i → X) ∘ g) q₀.val.2 =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ, ComplexModel n) q₀.val.2) := by
    rw [he.mfderiv_eq,mfderiv_id]
  have hcomp := hd.symm.trans hi
  intro w
  refine ⟨mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (N + n - 1)) g q₀.val.2 w,?_⟩
  exact congrArg (fun A => A w) hcomp

end SGPT.Trace.BertiniUniversal
