import SGPT.Toric.ProjectiveProductAffinePath
import SGPT.Convex.BoundedLegendreMixedEnergy
import SGPT.Foundations.Analysis.Pending.GlobalSlotPerm

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open scoped Topology ENNReal RealInnerProductSpace

/-- The actual two original native endpoint functions, indexed by genuine binary slots. -/
def projectiveProductBinaryNativeFamily {n : ℕ} (φ u : projectiveProductSpace n → EReal)
    (i : Fin 2) : projectiveProductSpace n → EReal := if i = 0 then φ else u

private theorem binary_native_psh {n : ℕ} {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u) (i : Fin 2) :
    IsThetaPshPotential (projectiveProductFSBackground n).form.val
      (projectiveProductBinaryNativeFamily φ u i) := by
  by_cases hi : i = 0 <;> simp only [projectiveProductBinaryNativeFamily, hi, ↓reduceIte]
  · exact hφ
  · exact hu

/-- The actual global mixed NP measure of an original binary endpoint tuple. -/
def projectiveProductBinaryNativeMeasure {n : ℕ} {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (a : Fin n → Fin 2) : Measure (projectiveProductSpace n) :=
  GlobalNonPluripolar.globalMixedMeasure
    (fun _ : Fin n => (projectiveProductFSBackground n).form)
    (fun i => projectiveProductBinaryNativeFamily φ u (a i))
    (fun i => (binary_native_psh hφ hu (a i)).1)

/-- Literal actual signed native mixed moments, with the original source gap. -/
def projectiveProductNativeTangentPolynomial {n : ℕ} {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u) (t : ℝ) : ℝ :=
  ∑ a : Fin n → Fin 2, (∏ i, if a i = 0 then 1 - t else t) *
    ∫ p, (u p - φ p).toReal ∂projectiveProductBinaryNativeMeasure hφ hu a

/-- Actual compact bounded native mixed products manufacture every signed moment's integrability. -/
theorem integrable_gap_projectiveProductBinaryNativeMeasure {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u) (a : Fin n → Fin 2) :
    Integrable (fun p => (u p - φ p).toReal) (projectiveProductBinaryNativeMeasure hφ hu a) := by
  let μ := projectiveProductBinaryNativeMeasure hφ hu a
  have hb (i : Fin n) : IsBoundedPotential (projectiveProductBinaryNativeFamily φ u (a i)) := by
    by_cases hi : a i = 0 <;> simp only [projectiveProductBinaryNativeFamily, hi, ↓reduceIte]
    · exact hφb
    · exact hub
  let : IsFiniteMeasure μ := globalMixedMeasure_isFiniteMeasure_of_bounded
    (fun i => (binary_native_psh hφ hu (a i)).1) hb
  obtain ⟨Cu, hCu⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hub
  obtain ⟨Cφ, hCφ⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hφb
  have iu : Integrable (fun p => (u p).toReal) μ :=
    GlobalSlotStokes.integrable_of_measurable_bounded
      (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hu.1) hCu μ
  have iφ : Integrable (fun p => (φ p).toReal) μ :=
    GlobalSlotStokes.integrable_of_measurable_bounded
      (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hφ.1) hCφ μ
  have hgap : (fun p => (u p - φ p).toReal) = fun p => (u p).toReal - (φ p).toReal :=
    funext fun p => EReal.toReal_sub (hub.ne_top p) (hub.ne_bot p)
      (hφb.ne_top p) (hφb.ne_bot p)
  rw [hgap]
  exact iu.sub iφ

/-- Genuine positive native multilinearity expands the actual affine diagonal measure
on the open interval. No measure equality or multilinearity certificate is supplied. -/
theorem projectiveProductAffineMixedMeasure_eq_binaryExpansion {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => (projectiveProductFSBackground n).form)
      (fun _ => projectiveProductAffinePotential φ u t)
      (fun _ => (isThetaPshPotential_projectiveProductAffinePotential hφ hu hφb hub
        ⟨ht.1.le, ht.2.le⟩).1) =
      ∑ a : Fin n → Fin 2, ENNReal.ofReal (∏ i, if a i = 0 then 1 - t else t) •
        projectiveProductBinaryNativeMeasure hφ hu a := by
  classical
  let w : Fin 2 → ℝ := fun i => if i = 0 then 1 - t else t
  have hw (i : Fin 2) : 0 < w i := by
    dsimp only [w]
    split_ifs
    · exact sub_pos.mpr ht.2
    · exact ht.1
  have eθ : GlobalMultilinearExpansion.sumForm Finset.univ w
      (fun _ : Fin 2 => (projectiveProductFSBackground n).form) =
        (projectiveProductFSBackground n).form := by
    simp [GlobalMultilinearExpansion.sumForm, Fin.sum_univ_two, w, ← add_smul]
  have eu : GlobalMultilinearExpansion.sumPot Finset.univ w
      (projectiveProductBinaryNativeFamily φ u) = projectiveProductAffinePotential φ u t := by
    funext p
    simp [GlobalMultilinearExpansion.sumPot, Fin.sum_univ_two, w,
      projectiveProductBinaryNativeFamily, projectiveProductAffinePotential]
  have he := GlobalMultilinearExpansion.globalMixedMeasure_diagonal_sumPot
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 2)).Nonempty) hw
    (fun i => (binary_native_psh hφ hu i).1)
    (fun i => (binary_native_psh hφ hu i).quasiPshPotential)
  rw [GlobalDiagonalScaling.globalMixedMeasure_congr (congrArg (fun θ => fun _ : Fin n => θ) eθ)
    (congrArg (fun v => fun _ : Fin n => v) eu) _
    (fun _ => (isThetaPshPotential_projectiveProductAffinePotential hφ hu hφb hub
      ⟨ht.1.le, ht.2.le⟩).1)] at he
  simpa only [Fintype.piFinset_univ, w, projectiveProductBinaryNativeMeasure] using he

/-- True finite sums of original mixed measures identify the actual diagonal tangent integral. -/
theorem projectiveProductAffine_integral_gap_eq_nativeTangent {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ p, (u p - φ p).toReal ∂GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => (projectiveProductFSBackground n).form)
      (fun _ => projectiveProductAffinePotential φ u t)
      (fun _ => (isThetaPshPotential_projectiveProductAffinePotential hφ hu hφb hub
        ⟨ht.1.le, ht.2.le⟩).1)) = projectiveProductNativeTangentPolynomial hφ hu t := by
  rw [projectiveProductAffineMixedMeasure_eq_binaryExpansion hφ hu hφb hub ht]
  rw [integral_finsetSum_measure (fun a _ =>
    (integrable_gap_projectiveProductBinaryNativeMeasure hφ hu hφb hub a).smul_measure
      (by simp))]
  simp only [integral_smul_measure, smul_eq_mul, projectiveProductNativeTangentPolynomial]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => by
    split_ifs
    · exact (sub_pos.mpr ht.2).le
    · exact ht.1.le))]

/-- The genuine original native polynomial is continuous at endpoints as well. -/
theorem continuous_projectiveProductNativeTangentPolynomial {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u) :
    Continuous (projectiveProductNativeTangentPolynomial hφ hu) := by
  classical
  unfold projectiveProductNativeTangentPolynomial
  apply continuous_finsetSum
  intro a _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro i _
  split_ifs <;> fun_prop

/-- Independent true source signed transport and the actual convex diagonal expansion
identify the two original tangent polynomials on the open interval. -/
theorem projectiveProductNativeTangent_eq_tropical {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hiφ : ProjectiveProductCircleInvariant φ) (hiu : ProjectiveProductCircleInvariant u)
    (hφb : IsBoundedPotential φ) (hub : IsBoundedPotential u)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    projectiveProductNativeTangentPolynomial hφ hu t =
      affineTangentPolynomial volume (EuclideanSpace.basisFun (Fin n) ℝ)
        ⟨projectiveProductToricEuclideanProfile φ, projectiveProductToricEuclideanProfile_convex hφ hiφ⟩
        ⟨projectiveProductToricEuclideanProfile u, projectiveProductToricEuclideanProfile_convex hu hiu⟩ t := by
  rw [← projectiveProductAffine_integral_gap_eq_nativeTangent hφ hu hφb hub ht]
  rw [projectiveProductMixedMeasure_integral_gap_eq_tropical hu hiu hub hφ hiφ hφb
    (isThetaPshPotential_projectiveProductAffinePotential hφ hu hφb hub ⟨ht.1.le, ht.2.le⟩)
    (projectiveProductCircleInvariant_affinePotential hiφ hiu t)]
  rw [projectiveProductToricEuclideanProfile_affinePotential hφb hub ⟨ht.1.le, ht.2.le⟩]
  exact integral_gap_affineProfile_eq_tangentPolynomial volume (EuclideanSpace.basisFun (Fin n) ℝ)
    (isCompact_euclideanUnitCube n) (nonempty_euclideanUnitCube n) (convex_euclideanUnitCube n)
    (f := ⟨projectiveProductToricEuclideanProfile φ, projectiveProductToricEuclideanProfile_convex hφ hiφ⟩)
    (g := ⟨projectiveProductToricEuclideanProfile u, projectiveProductToricEuclideanProfile_convex hu hiu⟩)
    (projectiveProductToricProfile_mem_boundedGrowthClass hφ hiφ hφb)
    (projectiveProductToricProfile_mem_boundedGrowthClass hu hiu hub) ⟨ht.1.le, ht.2.le⟩

end SGPT.Toric
