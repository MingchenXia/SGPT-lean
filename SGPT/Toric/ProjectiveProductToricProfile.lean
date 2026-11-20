import SGPT.Toric.ProjectiveProductBoundaryPole
import SGPT.Toric.GlobalTropicalSignedIntegral
import SGPT.Foundations.Analysis.Pending.BoundedGlobalTruncation

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped Topology ContDiff Manifold ProductComplexManifold RealInnerProductSpace
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
/-- Coordinatewise genuine homogeneous character action on the fixed original product. -/
def projectiveProductTorusAction : (n : ℕ) → (Fin n → ℂˣ) →
    projectiveProductSpace n → projectiveProductSpace n
  | 0, _, p => p
  | n + 1, a, p => (projectiveProductTorusAction n (Fin.init a) p.1,
      projectiveTorusAction (a (Fin.last n)) p.2)

/-- The original quotient coordinates read the genuine coordinatewise action. -/
theorem projectiveProductTorusAction_coordinates : (n : ℕ) → (a : Fin n → ℂˣ) →
    (p : projectiveProductSpace n) → (i : Fin n) →
    projectiveProductCoordinates n (projectiveProductTorusAction n a p) i =
      projectiveTorusAction (a i) (projectiveProductCoordinates n p i)
  | 0, _, _, i => Fin.elim0 i
  | n + 1, a, p, i => by
    change (Fin.snoc (projectiveProductCoordinates n
        (projectiveProductTorusAction n (Fin.init a) p.1))
        (projectiveTorusAction (a (Fin.last n)) p.2) : Fin (n + 1) → P1) i =
      projectiveTorusAction (a i)
        ((Fin.snoc (projectiveProductCoordinates n p.1) p.2 : Fin (n + 1) → P1) i)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
    · simpa only [Fin.snoc_castSucc, Fin.init] using
        projectiveProductTorusAction_coordinates n (Fin.init a) p.1 j

/-- The literal identity character fixes every original quotient point. -/
theorem projectiveProductTorusAction_one : (n : ℕ) → (p : projectiveProductSpace n) →
    projectiveProductTorusAction n (fun _ => 1) p = p
  | 0, _ => rfl
  | n + 1, p => by
    change (projectiveProductTorusAction n (fun _ => 1) p.1, projectiveTorusAction 1 p.2) = p
    rw [projectiveProductTorusAction_one, projectiveTorusAction_one]

/-- Original factor quotient group laws produce the actual product group law. -/
theorem projectiveProductTorusAction_mul : (n : ℕ) → (a b : Fin n → ℂˣ) →
    (p : projectiveProductSpace n) →
    projectiveProductTorusAction n (fun i => a i * b i) p =
      projectiveProductTorusAction n a (projectiveProductTorusAction n b p)
  | 0, _, _, _ => rfl
  | n + 1, a, b, p => by
    apply Prod.ext
    · exact projectiveProductTorusAction_mul n (Fin.init a) (Fin.init b) p.1
    · exact projectiveTorusAction_mul (a (Fin.last n)) (b (Fin.last n)) p.2

/-- Genuine original quotient/product topology supplies actual continuity. -/
theorem continuous_projectiveProductTorusAction : (n : ℕ) → (a : Fin n → ℂˣ) →
    Continuous (projectiveProductTorusAction n a)
  | 0, _ => continuous_id
  | n + 1, a =>
    ((continuous_projectiveProductTorusAction n (Fin.init a)).comp continuous_fst).prodMk
      ((continuous_projectiveTorusAction (a (Fin.last n))).comp continuous_snd)

private def characterCoordinates {n : ℕ} (a : Fin n → ℂˣ) (z : ComplexModel n) : ComplexModel n :=
  WithLp.toLp 2 (fun i => (a i : ℂ) * z i)

private theorem characterCoordinates_split_fst (n : ℕ) (a : Fin (n + 1) → ℂˣ)
    (z : ComplexModel (n + 1)) :
    ((prodModelEquiv n 1).symm (characterCoordinates a z)).1 =
      characterCoordinates (Fin.init a) ((prodModelEquiv n 1).symm z).1 := by
  ext i
  rfl

private theorem characterCoordinates_split_snd (n : ℕ) (a : Fin (n + 1) → ℂˣ)
    (z : ComplexModel (n + 1)) :
    ((prodModelEquiv n 1).symm (characterCoordinates a z)).2 =
      (a (Fin.last n) : ℂ) • ((prodModelEquiv n 1).symm z).2 := by
  ext i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  rfl

/-- Literal original inverse affine charts intertwine the genuine quotient action. -/
theorem projectiveProductTorusAction_chart_symm : (n : ℕ) → (a : Fin n → ℂˣ) →
    (z : ComplexModel n) →
    projectiveProductTorusAction n a
      ((projectiveProductNativeChart n (fun _ => false)).val.symm z) =
      (projectiveProductNativeChart n (fun _ => false)).val.symm
        (WithLp.toLp 2 (fun i => (a i : ℂ) * z i))
  | 0, _, z => by
    change z = characterCoordinates _ z
    ext i
    exact Fin.elim0 i
  | n + 1, a, z => by
    change (projectiveProductTorusAction n (Fin.init a)
        ((projectiveProductNativeChart n (fun _ => false)).val.symm
          ((prodModelEquiv n 1).symm z).1),
      projectiveTorusAction (a (Fin.last n)) ((projectiveNativeChart false).val.symm
        ((prodModelEquiv n 1).symm z).2)) =
      ((projectiveProductNativeChart n (fun _ => false)).val.symm
          ((prodModelEquiv n 1).symm (characterCoordinates a z)).1,
        (projectiveNativeChart false).val.symm
          ((prodModelEquiv n 1).symm (characterCoordinates a z)).2)
    rw [characterCoordinates_split_fst, characterCoordinates_split_snd]
    apply Prod.ext
    · exact projectiveProductTorusAction_chart_symm n (Fin.init a) _
    · exact projectiveTorusAction_chart_symm (a (Fin.last n)) false _

/-- Literal source invariance under every genuine coordinate quotient circle action. -/
def ProjectiveProductCircleInvariant {n : ℕ} (u : projectiveProductSpace n → EReal) : Prop :=
  ∀ a : Fin n → ℂˣ, (∀ i, ‖(a i : ℂ)‖ = 1) →
    ∀ p, u (projectiveProductTorusAction n a p) = u p

/-- The literal source reference partition on the original logarithmic coordinates. -/
def projectiveProductReferenceProfile (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, projectiveLineLogPartition (x i)

/-- The literal real reference correction agrees on the actual coordinate torus. -/
theorem projectiveProductReferenceProfile_tropicalization {n : ℕ} {z : ComplexModel n}
    (hz : z ∈ complexTorus n) :
    projectiveProductReferenceProfile n (tropicalization z) = projectiveProductFSPotential n z := by
  apply Finset.sum_congr rfl
  intro i _
  rw [tropicalization_apply_eq_log_norm_sq, ← Complex.normSq_eq_norm_sq]
  exact projectiveLineLogPartition_log_normSq (hz i)

/-- The produced full native local potential restricts to the actual open torus. -/
theorem projectiveProductTropicalLocalPotential (n : ℕ) :
    IsSmoothLocalPotential (projectiveProductFSBackground n).form.val
      (projectiveProductNativeChart n (fun _ => false)) (tropicalSmoothDomain n)
      (projectiveProductFSPotential n) :=
  (projectiveProductFSPotential_localPotential n (fun _ => false)).mono
    (tropicalSmoothDomain n).isOpen (subset_univ _)

/-- Literal original extended values on the actual positive radial section. -/
def projectiveProductToricDescent {n : ℕ} (u : projectiveProductSpace n → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  u ((projectiveProductNativeChart n (fun _ => false)).val.symm (expCoordinates x))

/-- Literal original radial descent with the produced source reference correction. -/
def projectiveProductToricCorrectedDescent {n : ℕ} (u : projectiveProductSpace n → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  projectiveProductToricDescent u x + (projectiveProductReferenceProfile n x : EReal)

/-- Original homogeneous circle invariance proves actual corrected chart values,
retaining original poles without any real conversion. -/
theorem projectiveProductToricCorrectedDescent_tropicalPullback {n : ℕ}
    {u : projectiveProductSpace n → EReal} (hi : ProjectiveProductCircleInvariant u)
    {z : ComplexModel n} (hz : z ∈ complexTorus n) :
    tropicalPullback (projectiveProductToricCorrectedDescent u) z =
      u ((projectiveProductNativeChart n (fun _ => false)).val.symm z) +
        (projectiveProductFSPotential n z : EReal) := by
  let w := expCoordinates (tropicalization z)
  have hw : w ∈ complexTorus n := expCoordinates_mem_complexTorus _
  have hn (i : Fin n) : ‖w i‖ = ‖z i‖ := by
    have hlog := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i)
      (tropicalization_expCoordinates (tropicalization z))
    rw [tropicalization_apply_eq_log_norm_sq, tropicalization_apply_eq_log_norm_sq] at hlog
    have hs := congrArg Real.exp hlog
    rw [Real.exp_log (pow_pos (norm_pos_iff.mpr (hw i)) 2),
      Real.exp_log (pow_pos (norm_pos_iff.mpr (hz i)) 2)] at hs
    nlinarith [norm_nonneg (w i), norm_nonneg (z i)]
  let a : Fin n → ℂˣ := fun i => Units.mk0 (z i / w i) (div_ne_zero (hz i) (hw i))
  have ha (i : Fin n) : ‖(a i : ℂ)‖ = 1 := by
    change ‖z i / w i‖ = 1
    rw [norm_div, hn i, div_self (norm_ne_zero_iff.mpr (hz i))]
  have hrot : characterCoordinates a w = z := by
    ext i
    exact div_mul_cancel₀ (z i) (hw i)
  have hu := hi a ha ((projectiveProductNativeChart n (fun _ => false)).val.symm w)
  rw [projectiveProductTorusAction_chart_symm] at hu
  change u ((projectiveProductNativeChart n (fun _ => false)).val.symm
      (characterCoordinates a w)) = _ at hu
  rw [hrot] at hu
  change u ((projectiveProductNativeChart n (fun _ => false)).val.symm w) +
      (projectiveProductReferenceProfile n (tropicalization z) : EReal) = _
  rw [projectiveProductReferenceProfile_tropicalization hz, hu]

/-- Actual native source PSH, literal circle invariance and a produced original
non-pole torus witness manufacture the genuine tropical PSH input. -/
theorem pshOn_projectiveProductToricCorrectedDescent {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    PSHOn (tropicalPullback (projectiveProductToricCorrectedDescent u)) (complexTorus n) := by
  let e := projectiveProductNativeChart n (fun _ => false)
  have hp := BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn
    hu.1 e (projectiveProductFSPotential_localPotential n (fun _ => false))
  have hraw : PlurisubharmonicOn
      (tropicalPullback (projectiveProductToricCorrectedDescent u)) (complexTorus n) := by
    intro z hz
    apply (hp z (mem_univ _)).congr
    filter_upwards [(isOpen_complexTorus n).mem_nhds hz] with w hw
    exact (projectiveProductToricCorrectedDescent_tropicalPullback hi hw).symm
  refine ⟨hraw.discPshOn, ?_⟩
  let O := e.val.source ∩ e.val ⁻¹' complexTorus n
  have hO : IsOpen O := e.val.isOpen_inter_preimage (isOpen_complexTorus n)
  let z₀ := expCoordinates (0 : EuclideanSpace ℝ (Fin n))
  have hz₀ : z₀ ∈ complexTorus n := expCoordinates_mem_complexTorus _
  have ht : z₀ ∈ e.val.target := by rw [projectiveProductNativeChart_target]; exact mem_univ _
  have hxO : e.val.symm z₀ ∈ O := by
    refine ⟨e.val.map_target ht, ?_⟩
    change e.val (e.val.symm z₀) ∈ complexTorus n
    rwa [e.val.right_inv ht]
  obtain ⟨p, hpO, hfin⟩ := hu.2 (e.val.symm z₀) O hO hxO
  refine ⟨e.val p, hpO.2, ?_⟩
  rw [projectiveProductToricCorrectedDescent_tropicalPullback hi hpO.2]
  change u (e.val.symm (e.val p)) + (projectiveProductFSPotential n (e.val p) : EReal) ≠ ⊥
  rw [e.val.left_inv hpO.1]
  exact EReal.add_ne_bot_iff.mpr ⟨hfin, EReal.coe_ne_bot _⟩

/-- Actual real values of the original descent; the source PSH producer proves
finiteness everywhere before this representation is used. -/
def projectiveProductToricEuclideanProfile {n : ℕ} (u : projectiveProductSpace n → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (projectiveProductToricCorrectedDescent u x).toReal

/-- Genuine original native invariant PSH manufactures finite real convexity. -/
theorem projectiveProductToricEuclideanProfile_convex {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    ConvexOn ℝ univ (projectiveProductToricEuclideanProfile u) :=
  convexOn_toReal_of_pshOn_tropicalPullback (pshOn_projectiveProductToricCorrectedDescent hu hi)

private theorem projectiveProductEuclideanProfile_coe {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) (x : EuclideanSpace ℝ (Fin n)) :
    (projectiveProductToricEuclideanProfile u x : EReal) = projectiveProductToricCorrectedDescent u x := by
  have hf := finite_of_pshOn_tropicalPullback (pshOn_projectiveProductToricCorrectedDescent hu hi) x
  exact EReal.coe_toReal hf.1 hf.2

/-- The same actual inverse chart reads the produced finite original profile. -/
theorem projectiveProductToricEuclideanProfile_corrected {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    EqOn (fun z => chartFunction u (projectiveProductNativeChart n (fun _ => false)) z +
      (projectiveProductFSPotential n z : EReal))
      (fun z => (projectiveProductToricEuclideanProfile u (tropicalization z) : EReal))
      (tropicalSmoothDomain n) := by
  intro z hz
  calc
    _ = projectiveProductToricCorrectedDescent u (tropicalization z) :=
      (projectiveProductToricCorrectedDescent_tropicalPullback hi hz).symm
    _ = _ := (projectiveProductEuclideanProfile_coe hu hi _).symm

/-- This actual native tropical patch is built from original source inputs alone. -/
def projectiveProductToricPatch {n : ℕ} {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    Patch (fun _ : Fin n => (projectiveProductFSBackground n).form) (fun _ => u) :=
  tropicalPotentialPatch (projectiveProductNativeChart n (fun _ => false))
    (projectiveProductTropicalLocalPotential n)
    (projectiveProductToricEuclideanProfile_convex hu hi)
    (projectiveProductToricEuclideanProfile_corrected hu hi)

private theorem productToricPatch_source {n : ℕ} {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    ((projectiveProductToricPatch hu hi).source : Set (projectiveProductSpace n)) =
      projectiveProductTorus n := projectiveProductTorus_chart_source n

private theorem productToricPatch_poleCover {n : ℕ} {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    ((projectiveProductToricPatch hu hi).source : Set (projectiveProductSpace n))ᶜ ⊆
      {p | projectiveProductBoundaryPole n p = ⊥} := by
  rw [productToricPatch_source, projectiveProductBoundaryPole_poleLocus]

/-- Every chart/reference/profile/pole field is manufactured from original
native invariant source inputs before true whole NP transport is consumed. -/
theorem projectiveProductMixedMeasure_eq_tropicalCanonical {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => (projectiveProductFSBackground n).form) (fun _ => u)
      (fun _ => hu.1) =
        (projectiveProductToricPatch hu hi).pushMeasure
          (tropicalCanonicalBTMeasure (projectiveProductToricEuclideanProfile_convex hu hi)) :=
  globalMixedMeasure_eq_tropical_chart_pushMeasure hu
    (projectiveProductNativeChart n (fun _ => false)) (projectiveProductTropicalLocalPotential n)
    (projectiveProductToricEuclideanProfile_convex hu hi)
    (projectiveProductToricEuclideanProfile_corrected hu hi)
    (isGlobalQuasiPshPotential_projectiveProductBoundaryPole n) (productToricPatch_poleCover hu hi)

/-- The actual original native NP total retains literal Euclidean n! Newton volume. -/
theorem projectiveProductMixedMeasure_univ_eq_NewtonBody {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hi : ProjectiveProductCircleInvariant u) :
    GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => (projectiveProductFSBackground n).form) (fun _ => u)
      (fun _ => hu.1) univ = (n.factorial : ENNReal) * volume
      (convexNewtonBody (conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
        (fun x => (projectiveProductToricEuclideanProfile u x : EReal)))) :=
  globalMixedMeasure_univ_eq_tropicalNewtonBody hu
    (projectiveProductNativeChart n (fun _ => false)) (projectiveProductTropicalLocalPotential n)
    (projectiveProductToricEuclideanProfile_convex hu hi)
    (projectiveProductToricEuclideanProfile_corrected hu hi)
    (isGlobalQuasiPshPotential_projectiveProductBoundaryPole n) (productToricPatch_poleCover hu hi)

/-- Actual bounded original weights and the produced native compact Kähler
geometry supply both integrabilities; the independent measure input may be singular. -/
theorem projectiveProductMixedMeasure_integral_gap_eq_tropical {n : ℕ}
    {u φ v : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hiu : ProjectiveProductCircleInvariant u) (hub : IsBoundedPotential u)
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hiφ : ProjectiveProductCircleInvariant φ) (hφb : IsBoundedPotential φ)
    (hv : IsThetaPshPotential (projectiveProductFSBackground n).form.val v)
    (hiv : ProjectiveProductCircleInvariant v) :
    (∫ p, (u p - φ p).toReal ∂GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => (projectiveProductFSBackground n).form) (fun _ => v)
      (fun _ => hv.1)) =
      ∫ x, (projectiveProductToricEuclideanProfile u x - projectiveProductToricEuclideanProfile φ x)
        ∂alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume
          (fun x => (projectiveProductToricEuclideanProfile v x : EReal)) := by
  let μ := GlobalNonPluripolar.globalMixedMeasure
    (fun _ : Fin n => (projectiveProductFSBackground n).form) (fun _ => v) (fun _ => hv.1)
  let : IsFiniteMeasure μ := DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure
    (projectiveProductFSBackground n) (projectiveProductFSBackground n).form hv
  obtain ⟨Cu, hCu⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hub
  obtain ⟨Cφ, hCφ⟩ := GlobalSlotStokes.IsBoundedPotential.exists_abs_toReal_le hφb
  have iu : Integrable (fun p => (u p).toReal) μ :=
    GlobalSlotStokes.integrable_of_measurable_bounded
      (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hu.1) hCu μ
  have iφ : Integrable (fun p => (φ p).toReal) μ :=
    GlobalSlotStokes.integrable_of_measurable_bounded
      (GlobalSlotStokes.ThetaPlurisubharmonic.measurable_toReal hφ.1) hCφ μ
  have hgap : (fun p => (u p - φ p).toReal) = fun p => (u p).toReal - (φ p).toReal := by
    funext p
    exact EReal.toReal_sub (hub.ne_top p) (hub.ne_bot p) (hφb.ne_top p) (hφb.ne_bot p)
  have hint : Integrable (fun p => (u p - φ p).toReal) μ := by
    rw [hgap]
    exact iu.sub iφ
  exact globalMixedMeasure_integral_gap_eq_tropical hu hφ hv
    (projectiveProductNativeChart n (fun _ => false)) (projectiveProductTropicalLocalPotential n)
    (projectiveProductToricEuclideanProfile_convex hu hiu)
    (projectiveProductToricEuclideanProfile_convex hφ hiφ)
    (projectiveProductToricEuclideanProfile_convex hv hiv)
    (projectiveProductToricEuclideanProfile_corrected hu hiu)
    (projectiveProductToricEuclideanProfile_corrected hφ hiφ)
    (projectiveProductToricEuclideanProfile_corrected hv hiv)
    (isGlobalQuasiPshPotential_projectiveProductBoundaryPole n)
    (productToricPatch_poleCover hv hiv) hint

end SGPT.Toric
