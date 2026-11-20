import SGPT.Trace.BertiniSmooth
import SGPT.Trace.BertiniRestrictionChart
import SGPT.Trace.IncidenceTubeExhaustion
import SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction
import SGPT.Foundations.Analysis.Pending.OpensRestriction

/-!
# The actual smooth pencil incidence over a regular central member

Geometric producers for E2 of `thm:Bert`, using the original projective
hyperplane members and the actual incidence subtype topology.
Blueprint: `work/sgpt-resume-20261114/bert-e2-family/blueprint/bert-e2-pencil-family.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.BertiniPencilFamily

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini

variable {n N : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : X → ComplexProjectiveSpace N)

/-- Compactness makes regularity open in the entire original linear system. -/
theorem isOpen_smoothMemberSet [CompactSpace X]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) :
    IsOpen {l : HyperplaneSpace N | IsSmoothHypersurfaceMember n p l} := by
  simpa only [singularMemberSet, compl_ofPred, not_not] using
    (isComplexAnalyticSubset_singularMemberSet p hp).isClosed.isOpen_compl

/-- A single radius keeps every original member of a continuous pencil
smooth at every point, starting from its actual regular central member. -/
theorem exists_closedDisc_smooth_members [CompactSpace X]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    {l : ComplexModel 1 → HyperplaneSpace N} (hl : Continuous l)
    (h₀ : IsSmoothHypersurfaceMember n p (l 0)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t ∈ closedBall (0 : ComplexModel 1) ρ,
      IsSmoothHypersurfaceMember n p (l t) := by
  have hU := (isOpen_smoothMemberSet p hp).preimage hl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 h₀
  refine ⟨r / 2, half_pos hr, fun t ht => hball ?_⟩
  exact (closedBall_subset_ball (by linarith : r / 2 < r)) ht

/-- The actual affine pencil in the dual projective space. Its centre
coefficient is one, so no zero projective lift is introduced. -/
def pencilParameter (i : Fin (N + 1)) (a v : ComplexModel N) (t : ComplexModel 1) :
    HyperplaneSpace N := affinePoint i (a - t 0 • v)

/-- The original affine pencil parameterization is holomorphic. -/
theorem contMDiff_pencilParameter (i : Fin (N + 1)) (a v : ComplexModel N) :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel N) ∞ (pencilParameter i a v) := by
  have hpoint : ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) ∞
      (affinePoint (N := N) i) := by
    intro z
    exact contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (affineChart_mem_atlas i)) (by simp)
  exact hpoint.comp (contDiff_const.sub
    ((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contDiff.smul
      contDiff_const)).contMDiff

/-- Uniform smoothness for the actual native affine pencil, with its
original central hyperplane member as the only regularity input. -/
theorem exists_closedDisc_smooth_pencil [CompactSpace X]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (i : Fin (N + 1)) (a v : ComplexModel N)
    (h₀ : IsSmoothHypersurfaceMember n p (affinePoint i a)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t ∈ closedBall (0 : ComplexModel 1) ρ,
      IsSmoothHypersurfaceMember n p (pencilParameter i a v t) := by
  apply exists_closedDisc_smooth_members p hp (contMDiff_pencilParameter i a v).continuous
  simpa only [pencilParameter, PiLp.zero_apply, zero_smul, sub_zero] using h₀

open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.DerivativeIdeal
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped ProductComplexManifold

/-- The actual product of two native atlas charts. -/
def productComplexChart {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y]
    (a : ComplexChart m Y) (b : ComplexChart n X) : ComplexChart (m + n) (Y × X) :=
  ⟨prodChart a.val b.val, mem_image2_of_mem a.property b.property⟩

/-- A vertical coordinate derivative of an actual product holomorphic germ
is exactly the derivative of its original fibre restriction. -/
theorem chartDeriv_product_vertical {m : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    (a : ComplexChart m Y) (b : ComplexChart n X) {y : Y} {x : X}
    (hy : y ∈ a.val.source) (hx : x ∈ b.val.source) {F : Y × X → ℂ}
    (hF : HolomorphicAt (m + n) F (y, x)) (v : ComplexModel n) :
    chartDeriv (productComplexChart a b) (prodModelEquiv m n (0, v)) F (y, x) =
      chartDeriv b v (fun z => F (y, z)) x := by
  let e := productComplexChart a b
  let H : ComplexModel (m + n) → ℂ := F ∘ e.val.symm
  let I : ComplexModel n → ComplexModel (m + n) := fun z => prodModelEquiv m n (a.val y, z)
  have hsource : (y, x) ∈ e.val.source := by
    simpa only [e, productComplexChart, prodChart_source] using (show (y, x) ∈ a.val.source ×ˢ b.val.source from ⟨hy, hx⟩)
  have hH : DifferentiableAt ℂ H (e.val (y, x)) :=
    (eventually_differentiableAt_comp_symm e hsource hF).self_of_nhds
  have hI : HasFDerivAt I
      ((prodModelEquiv m n : ComplexModel m × ComplexModel n →L[ℂ] ComplexModel (m + n)).comp
        ((0 : ComplexModel n →L[ℂ] ComplexModel m).prod (ContinuousLinearMap.id ℂ (ComplexModel n))))
      (b.val x) :=
    (prodModelEquiv m n).hasFDerivAt.comp (b.val x)
      ((hasFDerivAt_const (a.val y) (b.val x)).prodMk (hasFDerivAt_id (b.val x)))
  have hpoint : I (b.val x) = e.val (y, x) := rfl
  have hcomp : H ∘ I = fun z => F (y, b.val.symm z) := by
    funext z
    simp only [H, I, e, productComplexChart, Function.comp_apply,
      prodChart_symm_apply, ContinuousLinearEquiv.symm_apply_apply, a.val.left_inv hy]
  have hd := hH.hasFDerivAt.comp (b.val x) hI
  rw [hcomp] at hd
  have hv := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v) hd.fderiv
  simpa only [chartDeriv, H, hpoint, Function.comp_def, ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply,
    ContinuousLinearMap.id_apply, e] using hv.symm

section Incidence

variable (i : Fin (N + 1)) (a v : ComplexModel N)
  (U : TopologicalSpace.Opens (ComplexModel 1))

/-- The actual original projective incidence over an open pencil region. -/
def familyIncidence : Set (U × X) :=
  {q | q.2 ∈ member p (pencilParameter i a v q.1.val)}

/-- A normalized local equation, using the same original projective lift
in the chosen chart of X's projective image. -/
def pencilLocalEquation (j : Fin (N + 1)) (q : U × X) : ℂ :=
  pairing (affineLift i (a - q.1.val 0 • v)) (affineLift j (affineChart j (p q.2)))

/-- The equation is jointly holomorphic in the actual parameter and X. -/
theorem holomorphicAt_pencilLocalEquation
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (j : Fin (N + 1)) {q : U × X} (hq : p q.2 ∈ (affineChart j).source) :
    HolomorphicAt (1 + n) (pencilLocalEquation p i a v U j) q := by
  have ht : ContMDiff 𝓘(ℂ, ComplexModel (1 + n)) 𝓘(ℂ, ComplexModel 1) ∞
      (fun q : U × X => q.1.val) :=
    contMDiff_subtype_val.comp (contMDiff_fst (n := 1) (m := n) (X := U) (Y := X))
  have hζ : ContMDiff 𝓘(ℂ, ComplexModel (1 + n)) 𝓘(ℂ, ComplexModel N) ∞
      (fun q : U × X => a - q.1.val 0 • v) :=
    (contDiff_const.sub
      ((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contDiff.smul
        contDiff_const)).contMDiff.comp ht
  change HolomorphicAt (1 + n)
    (fun q : U × X => ∑ k, affineLift i (a - q.1.val 0 • v) k *
      affineLift j (affineChart j (p q.2)) k) q
  apply HolomorphicAt.sum Finset.univ
  intro k _
  have hleft : HolomorphicAt (1 + n) (fun q : U × X => affineLift i (a - q.1.val 0 • v) k) q := by
    filter_upwards [] with q'
    exact (differentiable_affineLift_apply i k _).mdifferentiableAt.comp q'
      (hζ.contMDiffAt.mdifferentiableAt (by simp))
  have hright : HolomorphicAt (1 + n) (fun q : U × X => affineLift j (affineChart j (p q.2)) k) q :=
    (holomorphicAt_affineLift_affineChart_comp p hp j k hq).comp_contMDiff (f := Prod.snd)
      (Eventually.of_forall fun _ =>
        (contMDiff_snd (n := 1) (m := n) (X := U) (Y := X)).contMDiffAt)
  exact hleft.mul hright

omit [TopologicalSpace X] in
/-- The local zero set equals the entire original projective incidence,
with no representative or base-locus exception. -/
theorem mem_familyIncidence_iff_localEquation (j : Fin (N + 1)) {q : U × X}
    (hq : p q.2 ∈ (affineChart j).source) :
    q ∈ familyIncidence p i a v U ↔ pencilLocalEquation p i a v U j q = 0 := by
  change IsIncident (mk (affineLift i (a - q.1.val 0 • v)) (affineLift_ne_zero i _)) (p q.2) ↔ _
  conv_lhs => rw [eq_mk_affineLift_affineChart j hq]
  exact isIncident_mk_mk_iff (affineLift_ne_zero i _) (affineLift_ne_zero j _)
/-- Smoothness of the original member supplies an actual nonzero vertical
derivative of its normalized joint incidence equation. -/
theorem exists_vertical_deriv_localEquation
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (j : Fin (N + 1)) {q : U × X} (hq : q ∈ familyIncidence p i a v U)
    (hqj : p q.2 ∈ (affineChart j).source) :
    ∃ (e : ComplexChart n X) (w : ComplexModel n), q.2 ∈ e.val.source ∧
      chartDeriv e w (fun x => pencilLocalEquation p i a v U j (q.1, x)) q.2 ≠ 0 := by
  obtain ⟨e, w, he, hd⟩ := hsm q.1 q.2 hq j hqj
  let l := pencilParameter i a v q.1.val
  obtain ⟨c, -, hrep⟩ := rep_smul l (affineLift_ne_zero i (a - q.1.val 0 • v)) rfl
  have hfun : memberEquation p l j = fun x => c • pencilLocalEquation p i a v U j (q.1, x) := by
    funext x
    rw [memberEquation, hyperplaneEquation, hrep, pairing_smul_left]
    rfl
  have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (1 + n)) ∞
      (fun x : X => (q.1, x)) := contMDiff_prodMk contMDiff_const contMDiff_id
  have hF := (holomorphicAt_pencilLocalEquation p i a v U hp j hqj).comp_contMDiff
    (f := fun x : X => (q.1, x)) (Eventually.of_forall fun _ => hi.contMDiffAt)
  have hdiff := (eventually_differentiableAt_comp_symm e he hF).self_of_nhds
  have hscaled := hdiff.hasFDerivAt.const_smul c
  have hcoord : memberEquation p l j ∘ e.val.symm =
      fun z => c • pencilLocalEquation p i a v U j (q.1, e.val.symm z) := by
    funext z
    exact congrFun hfun (e.val.symm z)
  have hdscale : chartDeriv e w (memberEquation p l j) q.2 =
      c • chartDeriv e w (fun x => pencilLocalEquation p i a v U j (q.1, x)) q.2 := by
    simp only [chartDeriv]
    rw [hcoord]
    simpa only [Function.comp_def, Pi.smul_def, Pi.smul_apply, smul_apply] using
      congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L w) hscaled.fderiv
  refine ⟨e, w, he, fun hz => hd ?_⟩
  change chartDeriv e w (memberEquation p l j) q.2 = 0
  rw [hdscale, hz, smul_zero]

/-- The actual projective pencil incidence is a regular hypersurface of
the native parameter-product manifold, with the full base locus retained. -/
theorem regularAtDim_familyIncidence
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    {q : U × X} (hq : q ∈ familyIncidence p i a v U) :
    RegularAtDim (n := 1 + n) (familyIncidence p i a v U) q n := by
  let j := chartIndex (p q.2)
  let W : Set (U × X) := {y | p y.2 ∈ (affineChart j).source}
  have hWo : IsOpen W := (affineChart j).open_source.preimage (hp.continuous.comp continuous_snd)
  have hqW : q ∈ W := mem_affineChart_chartIndex (p q.2)
  have hreg := LocalGiraudTransform.regularAtDim_zeroSet hWo
    (fun y hy => holomorphicAt_pencilLocalEquation p i a v U hp j hy)
    (fun y hy hy0 => by
      have hym := (mem_familyIncidence_iff_localEquation p i a v U j hy).mpr hy0
      obtain ⟨e, w, he, hd⟩ := exists_vertical_deriv_localEquation p i a v U hp hsm j hym hy
      let aT := complexChartAt (n := 1) y.1
      have hyT : y.1 ∈ aT.val.source := mem_complexChartAt_source y.1
      refine ⟨productComplexChart aT e, prodModelEquiv 1 n (0, w), ?_, ?_⟩
      · simpa only [productComplexChart, prodChart_source] using
          (show y ∈ aT.val.source ×ˢ e.val.source from ⟨hyT, he⟩)
      · rw [chartDeriv_product_vertical aT e hyT he
          (holomorphicAt_pencilLocalEquation p i a v U hp j hy)]
        exact hd)
    hqW ((mem_familyIncidence_iff_localEquation p i a v U j hqW).mp hq)
  have hdim : 1 + n - 1 = n := by omega
  rw [hdim] at hreg
  apply RegularPointDimension.regularAtDim_of_inter_eq hWo hqW ?_ hreg
  ext y
  simp only [mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hy0, hy⟩, _⟩
    exact ⟨(mem_familyIncidence_iff_localEquation p i a v U j hy).mpr hy0, hy⟩
  · rintro ⟨hym, hy⟩
    exact ⟨⟨(mem_familyIncidence_iff_localEquation p i a v U j hy).mp hym, hy⟩, hy⟩
/-- The entire original pencil incidence is closed on any parameter region. -/
theorem isClosed_familyIncidence
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) :
    IsClosed (familyIncidence p i a v U) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro q hq
  let j := chartIndex (p q.2)
  have hqj : p q.2 ∈ (affineChart j).source := mem_affineChart_chartIndex (p q.2)
  have hW := ((affineChart j).open_source.preimage (hp.continuous.comp continuous_snd)).mem_nhds hqj
  have hF := holomorphicAt_pencilLocalEquation p i a v U hp j hqj
  have hFne : pencilLocalEquation p i a v U j q ≠ 0 := by
    intro hz
    exact hq ((mem_familyIncidence_iff_localEquation p i a v U j hqj).mpr hz)
  filter_upwards [hW, hF.self_of_nhds.continuousAt.eventually_ne hFne] with y hy hFy
  intro hym
  exact hFy ((mem_familyIncidence_iff_localEquation p i a v U j hy).mp hym)

/-- The actual original parameter map on the full incidence subtype. -/
def familyProjection : familyIncidence p i a v U → U := fun q => q.val.1

/-- Properness uses compactness of the original X and retains its base locus. -/
theorem isProperMap_familyProjection [CompactSpace X]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) :
    IsProperMap (familyProjection p i a v U) :=
  isProperMap_fst_of_compactSpace.comp
    ((isClosed_familyIncidence p i a v U hp).isClosedEmbedding_subtypeVal.isProperMap)

/-- The actual native complex atlas is produced from the proved regularity
of the original incidence equation, on its original subspace topology. -/
@[instance_reducible]
def familyChartedSpace
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    ChartedSpace (ComplexModel n) (familyIncidence p i a v U) :=
  SubmanifoldChartedSpace.chartedSpace (by omega : n ≤ 1 + n)
    (fun _ hq => regularAtDim_familyIncidence p i a v U hp hsm hq)

/-- The produced native incidence atlas is a genuine complex manifold. -/
theorem isComplexManifold_family
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    letI := familyChartedSpace p i a v U hp hsm
    IsComplexManifold n (familyIncidence p i a v U) :=
  SubmanifoldChartedSpace.isComplexManifold_chartedSpace (by omega : n ≤ 1 + n)
    (fun _ hq => regularAtDim_familyIncidence p i a v U hp hsm hq)

/-- The inclusion of the produced incidence manifold is actually holomorphic. -/
theorem contMDiff_familyInclusion
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    letI := familyChartedSpace p i a v U hp hsm
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel (1 + n)) ∞
      (Subtype.val : familyIncidence p i a v U → U × X) := by
  exact SubmanifoldChartedSpace.contMDiff_val (by omega : n ≤ 1 + n)
    (fun _ hq => regularAtDim_familyIncidence p i a v U hp hsm hq)

/-- Holomorphy of the original projection is produced from the actual
incidence atlas and inclusion; no manifold or projection certificate is assumed. -/
theorem contMDiff_familyProjection
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    letI := familyChartedSpace p i a v U hp hsm
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ (familyProjection p i a v U) := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  exact (contMDiff_fst (n := 1) (m := n) (X := U) (Y := X)).comp
    (contMDiff_familyInclusion p i a v U hp hsm)

/-- The full original incidence over a smaller disc has a proved smooth psh
exhaustion, with its native complex structure and projection already produced. -/
theorem isWeaklyPseudoconvexOpen_nativeFamilyTube [CompactSpace X]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    {ρ : ℝ} (hρ : 0 < ρ) (hdisc : closedBall (0 : ComplexModel 1) ρ ⊆ (U : Set (ComplexModel 1))) :
    letI := familyChartedSpace p i a v U hp hsm
    SGPT.Okounkov.TranscendentalRelGen.IsWeaklyPseudoconvexOpen (n := n)
      {q : familyIncidence p i a v U | q.val.1.val ∈ ball (0 : ComplexModel 1) ρ} := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  let u₀ : U := ⟨0, hdisc (mem_closedBall_self hρ.le)⟩
  let d := complexChartAt (n := 1) u₀
  have hdsource : d.val.source = univ := by
    simp [d, complexChartAt, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source]
  have hdapply : ∀ u : U, d.val u = u.val := fun _ => rfl
  have hdtgt : d.val.target = (U : Set (ComplexModel 1)) := by
    simp [d, complexChartAt, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_def]
  have h := SGPT.Trace.IncidenceTubeExhaustion.isWeaklyPseudoconvexOpen_preimage_ball_of_proper_holomorphic
    (contMDiff_familyProjection p i a v U hp hsm) (isProperMap_familyProjection p i a v U hp)
    d (by rwa [hdtgt])
  simpa only [hdsource, univ_inter, Set.preimage, Set.mem_ofPred_eq, hdapply, familyProjection] using h
/-- A map into the actual native incidence manifold is holomorphic once
its original ambient map is holomorphic. This is proved in the produced
flattening chart, without a lift-regularity certificate. -/
theorem contMDiffAt_familyLift
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
    [IsComplexManifold m Y] {g : Y → familyIncidence p i a v U} {y : Y}
    (hg : ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (1 + n)) ∞
      (fun z => (g z).val) y) :
    letI := familyChartedSpace p i a v U hp hsm
    ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g y := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  let F := SubmanifoldChartedSpace.FlatData.ofRegularAtDim
    (regularAtDim_familyIncidence p i a v U hp hsm (g y).property)
  have hgy : (g y).val ∈ F.ambSource :=
    SubmanifoldChartedSpace.FlatData.mem_ambSource_ofRegularAtDim _
  have hchart : g y ∈ (chartAt (ComplexModel n) (g y)).source := mem_chart_source _ _
  rw [contMDiffAt_iff_target_of_mem_source hchart]
  refine ⟨tendsto_subtype_rng.mpr hg.continuousAt, ?_⟩
  change ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
    (fun z => FirstPass.RegularLocusDense.coordinateProjection (1 + n) n
      (F.flat (F.amb.val (g z).val))) y
  have ha := (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas F.amb.property) hgy.1).comp y hg
  have hb := (contDiffAt_of_differentiableOn_complex F.differentiableOn_flat
    F.flat.open_source hgy.2).contMDiffAt
  exact (FirstPass.RegularLocusDense.coordinateProjection (1 + n) n).contDiff.contMDiff.contMDiffAt.comp y
    (hb.comp y ha)

end Incidence

/-- An arbitrary original incident point in a SliceChart domain is
recovered exactly by its own parameter and X coordinates. -/
theorem point_of_incident_coordinates {φ : X → EReal} (c : SliceChart n p φ)
    {q : HyperplaneSpace N × X} (hq : q ∈ c.domain) (hmem : q.2 ∈ member p q.1) :
    c.point (affineChart c.i q.1) (c.e.val q.2) = q.2 := by
  let w := prodChart (affineChart c.i) c.e.val q
  have hws : w ∈ c.Φ.source := hq.2.2.1
  have hqj : p q.2 ∈ (affineChart c.j).source :=
    (prodChart_mem_conormalDomain_iff p hq.2.1).mp (c.source_subset hws)
  have hzero := (conormalGenerator_zero_prodChart_eq_zero_iff p hq.1 hq.2.1 hqj).mpr hmem
  have hflat : c.Φ.toFun w = flatProj c.m w := by
    rw [c.toFun_eq, flatMap_eq_flatProj p hzero]
  change c.e.val.symm (((prodModelEquiv N n).symm
    (c.Φ.invFun (flatProj c.m (prodModelEquiv N n
      (affineChart c.i q.1, c.e.val q.2)))))).2 = q.2
  change c.e.val.symm (((prodModelEquiv N n).symm (c.Φ.invFun (flatProj c.m w)))).2 = q.2
  rw [← hflat, c.Φ.left_inv w hws]
  simp only [w, prodChart_apply, ContinuousLinearEquiv.symm_apply_apply, c.e.val.left_inv hq.2.1]

/-- Moving the actual hyperplane coordinate in an original slice chart
is holomorphic in the original manifold X. -/
theorem contMDiffAt_slicePoint {φ : X → EReal} (c : SliceChart n p φ)
    {ζ : ComplexModel N} {b : ComplexModel n}
    (hζ : ζ ∈ ball c.ζ₀ c.r) (hb : b ∈ ball c.z₀ c.r) :
    ContMDiffAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel n) ∞
      (fun z => c.point z b) ζ := by
  have hs := contDiffAt_of_differentiableOn_complex (c.differentiableOn_slice hb)
    isOpen_ball hζ
  exact (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas c.e.property)
    (c.V_subset (c.mapsTo_V ζ hζ b hb))).comp ζ hs.contMDiffAt

omit [IsComplexManifold n X] in
/-- A pair of native manifold germs is holomorphic into the actual native
product atlas, including its standard Euclidean model identification. -/
theorem contMDiffAt_nativePair {k m : ℕ} {Y Z : Type*}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z] [IsComplexManifold k Z]
    {f : Z → Y} {g : Z → X} {z : Z}
    (hf : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel m) ∞ f z)
    (hg : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g z) :
    ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (m + n)) ∞
      (fun w => (f w, g w)) z := by
  rw [contMDiffAt_iff_target] at hf hg ⊢
  refine ⟨hf.1.prodMk hg.1, ?_⟩
  have hpair := hf.2.prodMk_space hg.2
  have h := (prodModelEquiv m n : ComplexModel m × ComplexModel n →L[ℂ]
      ComplexModel (m + n)).contMDiff.contMDiffAt.comp z hpair
  simpa [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def, prodChart_apply] using h

set_option maxHeartbeats 800000 in
/-- At every actual incident point, the original parameter projection
admits an actual local holomorphic right inverse through that point. -/
theorem exists_local_holomorphic_section
    (i : Fin (N + 1)) (a v : ComplexModel N)
    (U : TopologicalSpace.Opens (ComplexModel 1))
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U hp hsm
    ∃ g : U → familyIncidence p i a v U,
      g q.val.1 = q ∧
      ContMDiffAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ g q.val.1 ∧
      (familyProjection p i a v U ∘ g) =ᶠ[𝓝 q.val.1] id := by
  classical
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  let l : U → HyperplaneSpace N := fun t => pencilParameter i a v t.val
  have hl : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel N) ∞ l :=
    (contMDiff_pencilParameter i a v).comp contMDiff_subtype_val
  have hmem : q.val.2 ∈ member p (l q.val.1) := q.property
  obtain ⟨c, hqc⟩ := exists_sliceChart p (fun _ : X => (0 : EReal)) hp
    (manifoldQuasiPlurisubharmonic_const (n := n) (M := X) 0)
    (q₀ := (l q.val.1, q.val.2)) hmem
    ((isSmoothHypersurfaceMember_iff p hp _).mp (hsm q.val.1) q.val.2)
  have hcp : c.point (affineChart c.i (l q.val.1)) (c.e.val q.val.2) = q.val.2 :=
    point_of_incident_coordinates p c (q := (l q.val.1, q.val.2)) hqc hmem
  let ζ : U → ComplexModel N := fun t => affineChart c.i (l t)
  let b := c.e.val q.val.2
  have hb : b ∈ ball c.z₀ c.r := hqc.2.2.2.2
  have hζ : ζ q.val.1 ∈ ball c.ζ₀ c.r :=
    ball_subset_ball (by linarith [c.r_pos]) hqc.2.2.2.1
  have hζhol : ContMDiffAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel N) ∞ ζ q.val.1 :=
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas
      (affineChart_mem_atlas c.i)) hqc.1).comp q.val.1 hl.contMDiffAt
  let W : Set U := {t | l t ∈ (affineChart c.i).source ∧ ζ t ∈ ball c.ζ₀ c.r}
  have hW : W ∈ 𝓝 q.val.1 :=
    Filter.inter_mem (hl.continuous.continuousAt.eventually ((affineChart c.i).open_source.mem_nhds hqc.1))
      (hζhol.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hζ))
  have hm : ∀ t ∈ W, c.point (ζ t) b ∈ member p (pencilParameter i a v t.val) := by
    intro t ht
    have hc := c.point_mem_member ht.2 hb
    have he : affinePoint c.i (ζ t) = l t :=
      (affineChart c.i).left_inv ht.1
    rwa [he] at hc
  let g : U → familyIncidence p i a v U := fun t =>
    if ht : t ∈ W then ⟨(t, c.point (ζ t) b), hm t ht⟩ else q
  have hge : (fun t => (g t).val) =ᶠ[𝓝 q.val.1] (fun t => (t, c.point (ζ t) b)) := by
    filter_upwards [hW] with t ht
    simp only [g, dif_pos ht]
  have hqW : q.val.1 ∈ W := ⟨hqc.1, hζ⟩
  have hgq : g q.val.1 = q := by
    apply Subtype.ext
    simp only [g, dif_pos hqW]
    exact Prod.ext rfl hcp
  refine ⟨g, hgq, ?_, ?_⟩
  · apply contMDiffAt_familyLift p i a v U hp hsm
    exact (contMDiffAt_nativePair (X := X) contMDiffAt_id
      ((contMDiffAt_slicePoint p c hζ hb).comp q.val.1 hζhol)).congr_of_eventuallyEq hge
  · filter_upwards [hW] with t ht
    simp only [Function.comp_apply, familyProjection, g, dif_pos ht, id_eq]

/-- The actual original parameter projection is a holomorphic submersion:
its differential is proved surjective from actual local holomorphic sections. -/
theorem surjective_mfderiv_familyProjection
    (i : Fin (N + 1)) (a v : ComplexModel N)
    (U : TopologicalSpace.Opens (ComplexModel 1))
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U hp hsm
    Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1)
      (familyProjection p i a v U) q) := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  obtain ⟨g, hgq, hg, he⟩ := exists_local_holomorphic_section p i a v U hp hsm q
  have hd := mfderiv_comp q.val.1
    ((contMDiff_familyProjection p i a v U hp hsm).contMDiffAt.mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp))
  rw [hgq] at hd
  have hi : mfderiv 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1)
      (familyProjection p i a v U ∘ g) q.val.1 =
      ContinuousLinearMap.id ℂ (ComplexModel 1) := by
    rw [he.mfderiv_eq, mfderiv_id]
    rfl
  have hcomp := hd.symm.trans hi
  intro w
  refine ⟨mfderiv 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) g q.val.1 w, ?_⟩
  exact congrArg (fun A : ComplexModel 1 →L[ℂ] ComplexModel 1 => A w) hcomp

omit [TopologicalSpace X] in
/-- The actual fibre has the original member's points, with no extra
point and no removed base-locus point. -/
def familyFibreEquivMember (i : Fin (N + 1)) (a v : ComplexModel N)
    (U : TopologicalSpace.Opens (ComplexModel 1)) (t : U) :
    {q : familyIncidence p i a v U | familyProjection p i a v U q = t} ≃
      member p (pencilParameter i a v t.val) where
  toFun q := ⟨q.val.val.2, by
    have h := q.val.property
    change q.val.val.2 ∈ member p (pencilParameter i a v q.val.val.1.val) at h
    have hqt : q.val.val.1 = t := q.property
    simpa only [hqt] using h⟩
  invFun x := ⟨⟨(t, x.val), x.property⟩, rfl⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext q.property.symm rfl
  right_inv _ := rfl

/-- The exact fibre-member identification respects the original subspace
topologies; it is not a chosen replacement of the original fibre. -/
def familyFibreHomeomorphMember (i : Fin (N + 1)) (a v : ComplexModel N)
    (U : TopologicalSpace.Opens (ComplexModel 1)) (t : U) :
    {q : familyIncidence p i a v U | familyProjection p i a v U q = t} ≃ₜ
      member p (pencilParameter i a v t.val) where
  toEquiv := familyFibreEquivMember p i a v U t
  continuous_toFun := (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _

open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-- The original parameter open carries the actual restricted flat Kähler
form; no Kähler background on the parameter domain is assumed. -/
def parameterKahlerBackground (U : TopologicalSpace.Opens (ComplexModel 1)) :
    KahlerBackground 1 U :=
  OpensRestriction.restrictKahler U {
    form := ⟨flatKahlerForm 1, (flatKahlerForm_isKahler 1).2,
      fun e z hz => ((flatKahlerForm_isKahler 1).1 e z hz).1⟩
    isKahler := flatKahlerForm_isKahler 1 }

/-- The actual full native incidence is Kähler, with the literal
restriction of the original product form. -/
def familyKahlerBackground
    (i : Fin (N + 1)) (a v : ComplexModel N)
    (U : TopologicalSpace.Opens (ComplexModel 1))
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    KahlerBackground n (familyIncidence p i a v U) :=
  SubmanifoldKahlerRestriction.kahlerBackground (by omega : n ≤ 1 + n)
    (fun _ hq => regularAtDim_familyIncidence p i a v U hp hsm hq)
    (prodKahlerBackground (parameterKahlerBackground U) omega)

/-- The Kähler form on the original incidence is exactly the pullback
of the sum of the original two factor forms. -/
theorem familyKahlerBackground_form
    (i : Fin (N + 1)) (a v : ComplexModel N)
    (U : TopologicalSpace.Opens (ComplexModel 1))
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    (familyKahlerBackground p i a v U hp hsm omega).form =
      ClosedRealOneOneForm.pullback (contMDiff_familyInclusion p i a v U hp hsm)
        (prodForm (parameterKahlerBackground U).form omega.form) := rfl

end SGPT.Trace.BertiniPencilFamily
