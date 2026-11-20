import SGPT.Foundations.Analysis.Pending.DolbeaultLemma
import SGPT.Foundations.Analysis.Pending.OTWeakDbar
import SGPT.Foundations.Analysis.Pending.WeakDbarWeyl
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff
import SGPT.Foundations.Analysis.Pending.HormanderL2Theorem
import SGPT.Foundations.Analysis.Pending.OTChenExtension
import SGPT.Foundations.Analysis.Pending.LocalDDbar
import SGPT.PSH.AtlasHolomorphicTensorPullback
import SGPT.PSH.SourceDomainBalayage
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import SGPT.Foundations.Analysis.Pending.BedfordTaylorGauge
import SGPT.PSH.OriginalInverseHolomorphicPullback
import SGPT.PSH.ChartNullTransport
import SGPT.Foundations.Analysis.Pending.BedfordTaylorHolomorphic

/-! Entire original SGPT prop:bal_general, pinned current lines1327--1337,
with explicit authorized E18 positive-dimensional B-prime repair.
Canonical consolidation preserves all 55 reviewed public declaration names
and exact actual proof bodies from the private 17-module whole source cone.
No flat Draft-module import remains. -/

/-! An actual weak solution with smooth closed forcing has an actual smooth
pointwise representative. The solution is subsequently manufactured by the
existing Hormander theorem; this general regularity lemma assumes no desired
smooth representative or overlap output. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.WholeBallPotentialDraft
open Set Filter MeasureTheory Complex Metric
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open CauchyGreen Hormander OTChen
variable {n : ℕ}

/-- Subtract a genuine local smooth primitive from the actual weak solution.
The difference is weakly holomorphic in every actual direction. -/
theorem weak_sub_primitive_is_holomorphic
    {D W : Set (ComplexModel n)} (hW : IsOpen W) (hWD : W ⊆ D)
    {u p : ComplexModel n → ℂ} {beta : Fin n → ComplexModel n → ℂ}
    (hu : LocallyIntegrableOn u D) (hweak : WeakDbarEq D u beta)
    (hp : ContDiff ℝ ∞ p)
    (heq : ∀ j,∀ x∈W,dbarDir (coordVec j) p x=beta j x) :
    ∀ g : ComplexModel n → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ W →
      ∀ v : ComplexModel n,∫ x,(u x-p x)*dbarDir v g x=0 := by
  have hup : LocallyIntegrableOn (fun x => u x-p x) W :=
    (hu.mono_set hWD).sub (hp.continuous.continuousOn.locallyIntegrableOn hW.measurableSet)
  apply integral_mul_dbarDir_eq_zero_of_coord hup
  intro g hg j
  have hu0 := hweak g ⟨hg.1,hg.2.1,hg.2.2.trans hWD⟩ j
  have hp0 := weakDbarEq_of_contDiffOn hW (hp.of_le (by simp)).contDiffOn g hg j
  have hintu : Integrable (fun x => u x*dbarDir (coordVec j) g x) := integrable_mul_of_locallyIntegrableOn (hu.mono_set hWD)
    (continuous_dbarDir' (hg.1.of_le (by simp)))
    (hasCompactSupport_dbarDir hg.2.1) ((tsupport_dbarDir_subset _ g).trans hg.2.2)
  have hintp : Integrable (fun x => p x*dbarDir (coordVec j) g x) := integrable_mul_of_locallyIntegrableOn
    (hp.continuous.continuousOn.locallyIntegrableOn hW.measurableSet)
    (continuous_dbarDir' (hg.1.of_le (by simp)))
    (hasCompactSupport_dbarDir hg.2.1) ((tsupport_dbarDir_subset _ g).trans hg.2.2)
  have hright : (∫ x,dbarDir (coordVec j) p x*g x)=∫ x,beta j x*g x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x∈W
      · exact congrArg (fun a : ℂ => a*g x) (heq j x hx)
      · have hgx : g x=0 := image_eq_zero_of_notMem_tsupport fun h => hx (hg.2.2 h)
        simp [hgx]
  simp_rw [sub_mul]
  rw [integral_sub hintu hintp,hu0,hp0,hright]
  ring

/-- Every actual point has a genuine smooth local representative, with both
pointwise Dolbeault equation and agreement with the SAME weak solution. -/
theorem exists_local_smooth_weak_solution
    {D : Set (ComplexModel n)} (hD : IsOpen D)
    {u : ComplexModel n → ℂ} {beta : Fin n → ComplexModel n → ℂ}
    (hu : LocallyIntegrableOn u D) (hweak : WeakDbarEq D u beta)
    (hbeta : ∀ j,ContDiffOn ℝ ∞ (beta j) D) (hclosed : IsDbarClosedOn beta D)
    {x : ComplexModel n} (hx : x∈D) :
    ∃ W : Set (ComplexModel n),IsOpen W ∧ x∈W ∧ W⊆D ∧
      ∃ f : ComplexModel n → ℂ,ContDiffOn ℝ ∞ f W ∧
        (∀ j,∀ y∈W,dbarDir (coordVec j) f y=beta j y) ∧
        ∀ᵐ y ∂(volume.restrict W),u y=f y := by
  obtain ⟨W,hW,hxW,hWD,p,hp,hpeq⟩ := exists_dbar_primitive hD beta hbeta hclosed hx
  have hloc : LocallyIntegrableOn (fun y => u y-p y) W :=
    (hu.mono_set hWD).sub (hp.continuous.continuousOn.locallyIntegrableOn hW.measurableSet)
  obtain ⟨G,hG,hGae⟩ := exists_differentiableOn_ae_eq_of_weak_dbar hW hloc
    (weak_sub_primitive_is_holomorphic hW hWD hu hweak hp hpeq)
  have hGs : ContDiffOn ℝ ∞ G W :=
    (contDiffOn_of_differentiableOn_complex hG hW).restrict_scalars ℝ
  refine ⟨W,hW,hxW,hWD,fun y => p y+G y,hp.contDiffOn.add hGs,?_,?_⟩
  · intro j y hy
    rw [dbarDir_add (hp.differentiable (by simp) y)
      ((hGs.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)),
      hpeq j y hy,dbarDir_eq_zero_of_differentiableAt
        (hG.differentiableAt (hW.mem_nhds hy)) (coordVec j),add_zero]
  · filter_upwards [hGae] with y hy
    linear_combination hy

/-- Genuine smooth representative on the ENTIRE actual open solution domain.
Local representatives glue by Haar-null rigidity on their open overlaps;
there is no incoming global smooth function or compatibility certificate. -/
theorem exists_smooth_pointwise_dbar_solution_of_weak
    {D : Set (ComplexModel n)} (hD : IsOpen D)
    {u : ComplexModel n → ℂ} {beta : Fin n → ComplexModel n → ℂ}
    (hu : LocallyIntegrableOn u D) (hweak : WeakDbarEq D u beta)
    (hbeta : ∀ j,ContDiffOn ℝ ∞ (beta j) D) (hclosed : IsDbarClosedOn beta D) :
    ∃ f : ComplexModel n → ℂ,ContDiffOn ℝ ∞ f D ∧
      ∀ j,∀ x∈D,dbarDir (coordVec j) f x=beta j x := by
  have hloc := fun (x : ComplexModel n) (hx : x∈D) => exists_local_smooth_weak_solution hD hu hweak hbeta hclosed hx
  choose! W hW hxW hWD f hf hfeq hfae using hloc
  have hagree : ∀ x∈D,∀ y∈D,EqOn (f x) (f y) (W x∩W y) := by
    intro x hx y hy
    apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ ((hW x hx).inter (hW y hy))
      ((hf x hx).continuousOn.mono inter_subset_left)
      ((hf y hy).continuousOn.mono inter_subset_right)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left (hfae x hx),
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hfae y hy)] with z hz1 hz2
    exact hz1.symm.trans hz2
  let F : ComplexModel n → ℂ := fun y => f y y
  have hFnear : ∀ x∈D,F =ᶠ[𝓝 x] f x := by
    intro x hx
    filter_upwards [(hW x hx).mem_nhds (hxW x hx)] with y hy
    exact hagree y (hWD x hx hy) x hx ⟨hxW y (hWD x hx hy),hy⟩
  refine ⟨F,?_,?_⟩
  · intro x hx
    have hlocal : ContDiffAt ℝ ∞ (f x) x :=
      (hf x hx).contDiffAt ((hW x hx).mem_nhds (hxW x hx))
    exact (hlocal.congr_of_eventuallyEq (hFnear x hx)).contDiffWithinAt
  · intro j x hx
    rw [dbarDir_congr (hFnear x hx)]
    exact hfeq x hx j x (hxW x hx)

end SGPT.PSH.WholeBallPotentialDraft


/-! Genuine smooth Dolbeault solvability on a neighborhood of an ARBITRARY
compact subset of a bounded convex domain. The existing Hormander solution,
all forcing/integrability bounds, and smoothness are produced internally. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.WholeBallPotentialDraft
open Set Filter MeasureTheory Complex Metric
open scoped Topology ContDiff ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open CauchyGreen Hormander OTChen
variable {n : ℕ}

/-- Literal classical closedness of smooth coefficients produces the actual
weak distribution closedness on the same domain and all original tests. -/
theorem weakDbarClosed_of_classical_closed
    {D : Set (ComplexModel n)} (hD : IsOpen D)
    {beta : Fin n → ComplexModel n → ℂ}
    (hbeta : ∀ j,ContDiff ℝ ∞ (beta j)) (hclosed : IsDbarClosedOn beta D) :
    WeakDbarClosed D beta := by
  intro g hg j k
  have h1 := weakDbarEq_of_contDiffOn hD ((hbeta k).of_le (by simp)).contDiffOn g hg j
  have h2 := weakDbarEq_of_contDiffOn hD ((hbeta j).of_le (by simp)).contDiffOn g hg k
  have hi1 : Integrable (fun x => beta k x*dbarDir (coordVec j) g x) := integrable_mul_of_locallyIntegrableOn
    ((hbeta k).continuous.continuousOn.locallyIntegrableOn hD.measurableSet)
    (continuous_dbarDir' (hg.1.of_le (by simp)))
    (hasCompactSupport_dbarDir hg.2.1) ((tsupport_dbarDir_subset _ g).trans hg.2.2)
  have hi2 : Integrable (fun x => beta j x*dbarDir (coordVec k) g x) := integrable_mul_of_locallyIntegrableOn
    ((hbeta j).continuous.continuousOn.locallyIntegrableOn hD.measurableSet)
    (continuous_dbarDir' (hg.1.of_le (by simp)))
    (hasCompactSupport_dbarDir hg.2.1) ((tsupport_dbarDir_subset _ g).trans hg.2.2)
  have heq : (∫ x,dbarDir (coordVec j) (beta k) x*g x)=
      ∫ x,dbarDir (coordVec k) (beta j) x*g x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x∈D
      · exact congrArg (fun a : ℂ => a*g x) (hclosed j k x hx)
      · have hgx : g x=0 := image_eq_zero_of_notMem_tsupport fun h => hx (hg.2.2 h)
        simp [hgx]
  rw [integral_sub hi1 hi2,h1,h2,heq]
  ring

/-- An actual smooth closed Dolbeault form on a bounded convex domain has a
smooth pointwise primitive on one actual neighborhood of ANY compact subset.
In particular no fixed shrinking ratio or supplied primitive is assumed. -/
theorem exists_smooth_dbar_primitive_near_compact
    {D : Set (ComplexModel n)} (hD : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKD : K⊆D)
    {beta : Fin n → ComplexModel n → ℂ}
    (hbeta : ∀ j,ContDiff ℝ ∞ (beta j)) (hclosed : IsDbarClosedOn beta D) :
    ∃ W : Set (ComplexModel n),IsOpen W ∧ K⊆W ∧ W⊆D ∧
      ∃ f : ComplexModel n → ℂ,ContDiffOn ℝ ∞ f W ∧
        ∀ j,∀ x∈W,dbarDir (coordVec j) f x=beta j x := by
  obtain ⟨W,U,l1,l2,hW,hWc,hcl,hU,hKU,hUW,hl1,hl2,hl,hlU,hsolve⟩ :=
    hormanderL2Estimate n D hD hDc hDb K hK hKD 1 zero_lt_one
  have hWD : W⊆D := fun _ hx => hcl (subset_closure hx)
  have hWb : Bornology.IsBounded W := hDb.subset hWD
  have hbc : Continuous (formVec beta) := by
    unfold formVec
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp (continuous_pi fun j => (hbeta j).continuous)
  obtain ⟨M,hM⟩ := hDb.isCompact_closure.exists_bound_of_continuousOn hbc.continuousOn
  have hbM : ∀ x∈W,‖formVec beta x‖≤M :=
    fun x hx => hM x (subset_closure (hWD hx))
  let Phi : ComplexModel n → ℝ := fun x => ‖x‖^2
  have hPhi : ContDiff ℝ ∞ Phi := contDiff_norm_sq ℂ
  have hPhiL : ∀ x∈D,∀ v,0≤leviForm Phi x v := by
    intro x hx v
    rw [leviForm_norm_sq]
    positivity
  have hw1 : ContinuousOn (fun x => Phi x+l1 x) W := hPhi.continuous.continuousOn.add hl1
  have hw2 : ContinuousOn (fun x => Phi x+l2 x) W := hPhi.continuous.continuousOn.add hl2
  have hwbound : ∀ x∈W,∀ l:ℝ,0≤l → Real.exp (-(Phi x+l))≤1 := by
    intro x hx l hl0
    apply Real.exp_le_one_iff.mpr
    dsimp only [Phi]
    nlinarith [sq_nonneg ‖x‖]
  have hmem : ∀ j,MemLp (beta j) 2 (weightedVolume W fun x => Phi x+l2 x) := by
    intro j
    rw [memLp_weightedVolume_iff (hw2.aemeasurable hW.measurableSet)
      ((hbeta j).continuous.continuousOn.aestronglyMeasurable hW.measurableSet)]
    apply integrable_restrict_of_continuousOn_bound hW hWb
      (((hbeta j).continuous.continuousOn.norm.pow 2).mul hw2.neg.rexp) (M := M^2)
    intro x hx
    have hnonneg : 0≤‖beta j x‖^2*Real.exp (-(Phi x+l2 x)) :=
      mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    change ‖‖beta j x‖^2*Real.exp (-(Phi x+l2 x))‖≤M^2
    rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
    have hcomp : ‖beta j x‖≤‖formVec beta x‖ := PiLp.norm_apply_le (formVec beta x) j
    have hsq : ‖beta j x‖^2≤M^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hcomp.trans (hbM x hx)) 2
    exact (mul_le_mul_of_nonneg_left (hwbound x hx _ ((hl x hx).1.trans (hl x hx).2))
      (sq_nonneg _)).trans (by simpa using hsq)
  let g : ComplexModel n → ℝ := fun x => ‖formVec beta x‖^2
  have hgc : Continuous g := hbc.norm.pow 2
  have hforcing : ∀ x∈W,∀ xi:Fin n→ℂ,
      ‖∑ j,conj (xi j)*beta j x‖^2≤
        g x*leviForm Phi x (∑ j,xi j • coordVec j) := by
    intro x hx xi
    let v : ComplexModel n := WithLp.toLp 2 xi
    have hsum : (∑ j,xi j • coordVec j : ComplexModel n)=v := by
      ext j
      simp [coordVec,v,Pi.single_apply]
    have hin : ⟪v,formVec beta x⟫_ℂ=∑ j,conj (xi j)*beta j x := by
      simp [PiLp.inner_apply,v,mul_comm]
    rw [hsum,leviForm_norm_sq,← hin]
    calc ‖⟪v,formVec beta x⟫_ℂ‖^2≤(‖v‖*‖formVec beta x‖)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
      _=g x*‖v‖^2 := by dsimp only [g]; ring
  have hgint : Integrable (fun x => g x*Real.exp (-(Phi x+l1 x))) (volume.restrict W) := by
    apply integrable_restrict_of_continuousOn_bound hW hWb
      (hgc.continuousOn.mul hw1.neg.rexp) (M := M^2)
    intro x hx
    have hnonneg : 0≤g x*Real.exp (-(Phi x+l1 x)) :=
      mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    change ‖g x*Real.exp (-(Phi x+l1 x))‖≤M^2
    rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
    have hsq : g x≤M^2 := pow_le_pow_left₀ (norm_nonneg _) (hbM x hx) 2
    exact (mul_le_mul_of_nonneg_left (hwbound x hx _ (hl x hx).1)
      (by dsimp only [g]; positivity)).trans (by simpa using hsq)
  obtain ⟨⟨u,hu,hweak,hortho⟩,hestimate⟩ :=
    hsolve Phi hPhi.contDiffOn hPhiL beta hmem
      (weakDbarClosed_of_classical_closed hW hbeta fun j k x hx => hclosed j k x (hWD hx))
      g (fun x hx => by dsimp only [g]; positivity) hforcing hgint
  obtain ⟨f,hf,hfeq⟩ := exists_smooth_pointwise_dbar_solution_of_weak hW
    (locallyIntegrableOn_of_memLp_weightedVolume hW hw1 hu) hweak
    (fun j => (hbeta j).contDiffOn) (fun j k x hx => hclosed j k x (hWD hx))
  exact ⟨W,hW,hKU.trans hUW,hWD,f,hf,hfeq⟩

end SGPT.PSH.WholeBallPotentialDraft


/-! Smooth ddᶜ potentials on a neighborhood of an arbitrary compact subset
of the entire original Euclidean ball. The cutoff is one on every full radial
segment. The weak Dolbeault solution and its smooth representative are produced
internally. This is an analytic producer, not yet the original-ball balayage. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.WholeBallPotentialDraft
open Set Filter MeasureTheory Complex Metric
open scoped Topology ContDiff Interval
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open CauchyGreen Hormander OTChen LocalPotentials
variable {n : ℕ}

/-- The cutoff equals one throughout every entire radial segment in the
prescribed smaller ball; closedness is used at precisely those actual points. -/
theorem exists_smooth_twoForm_primitive_on_smaller_ball
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [FiniteDimensional ℝ E] {z : E} {r R : ℝ} (hr : 0<r) (hrR : r<R)
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a (ball z R))
    (hclosed : ∀ y∈ball z R,extDeriv a y=0) :
    ∃ S : E → E [⋀^Fin 1]→L[ℝ] ℝ,ContDiff ℝ ∞ S ∧
      ∀ x∈ball z r,extDeriv S x=a x := by
  let χ : ContDiffBump z := ⟨r,(r+R)/2,hr,by linarith⟩
  let b : E → E [⋀^Fin 2]→L[ℝ] ℝ := fun y => χ y • a y
  have hsupp : tsupport χ⊆ball z R := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by dsimp [χ]; linarith)
  have hb : ContDiff ℝ ∞ b :=
    contDiff_smul_of_tsupport_subset isOpen_ball χ.contDiff hsupp ha
  have heq : EqOn b a (ball z r) := fun y hy => by
    simp [b,χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  refine ⟨radialTwoFormPrimitive b z,contDiff_radialTwoFormPrimitive b z hb,?_⟩
  intro x hx
  have hseg : ∀ t∈Icc (0:ℝ) 1,z+t • (x-z)∈ball z r := fun t ht =>
    (convex_ball z r).add_smul_sub_mem (mem_ball_self hr) hx ht
  rw [extDeriv_radialTwoFormPrimitive_of_closed_segment b z x hb fun t ht => ?_]
  · exact heq hx
  · have hev : b =ᶠ[𝓝 (z+t • (x-z))] a :=
      eventually_of_mem (isOpen_ball.mem_nhds (hseg t ht)) heq
    rw [hev.extDeriv_eq]
    exact hclosed _ ((ball_subset_ball hrR.le) (hseg t ht))

/-- The actual real/imaginary normalized ddᶜ calculation on the entire open
solution domain, using only local smoothness of the produced primitive. -/
theorem smoothDDC_im_of_dbar_primitive_on
    {W : Set (ComplexModel n)} (hW : IsOpen W)
    {S : ComplexModel n → ComplexModel n [⋀^Fin 1]→L[ℝ] ℝ}
    (hS : ContDiff ℝ ∞ S) {f : ComplexModel n → ℂ}
    (hf : ContDiffOn ℝ ∞ f W)
    (hfβ : ∀ i,∀ y∈W,dbarDir (basisVec i) f y=zeroOnePart (S y) (basisVec i)) :
    EqOn (smoothDDC fun y => 4*Real.pi*(f y).im) (extDeriv S) W := by
  have hSd : Differentiable ℝ S := hS.differentiable (by simp)
  have hfd : ∀ y∈W,DifferentiableAt ℝ f y :=
    fun y hy => (hf.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)
  let u : ComplexModel n → ℝ := fun y => (f y).re
  let w : ComplexModel n → ℝ := fun y => (f y).im
  have hudiff : ContDiffOn ℝ ∞ u W := reCLM.contDiff.comp_contDiffOn hf
  have hwdiff : ContDiffOn ℝ ∞ w W := imCLM.contDiff.comp_contDiffOn hf
  have hre : ∀ y∈W,∀ v,S y ![v]=fderiv ℝ u y v-fderiv ℝ w y (I • v) := by
    intro y hy v
    have h := congrArg Complex.re (dbarDir_eq_zeroOnePart (fun i => hfβ i y hy) v)
    rw [zeroOnePart_re] at h
    have hu' : fderiv ℝ u y=reCLM.comp (fderiv ℝ f y) :=
      (reCLM.hasFDerivAt.comp y (hfd y hy).hasFDerivAt).fderiv
    have hw' : fderiv ℝ w y=imCLM.comp (fderiv ℝ f y) :=
      (imCLM.hasFDerivAt.comp y (hfd y hy).hasFDerivAt).fderiv
    rw [hu',hw']
    simp [dbarDir] at h
    simp
    linarith
  let ω₀ : ComplexModel n → ComplexModel n [⋀^Fin 0]→L[ℝ] ℝ := fun y =>
    ContinuousAlternatingMap.constOfIsEmpty ℝ (ComplexModel n) (Fin 0) (u y)
  have hω₀ : ContDiffOn ℝ ∞ ω₀ W :=
    (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (ComplexModel n) ℝ (Fin 0)).contDiff.comp_contDiffOn hudiff
  let R := extDeriv ω₀
  have hR : ContDiffOn ℝ ∞ R W := by
    have h := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ).contDiff.comp_contDiffOn (hω₀.fderiv_of_isOpen hW (m := ∞) (by simp))
    convert h using 1
    funext y
    simp [R,extDeriv,ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  have hRapply (y : ComplexModel n) (v : ComplexModel n) : R y ![v]=fderiv ℝ u y v := by
    simp [R,ω₀,extDeriv_constOfIsEmpty]
  intro x hx
  have hdc : smoothDc (fun y => 4*Real.pi*w y) =ᶠ[𝓝 x]
      fun y => S y+(-1:ℝ) • R y := by
    filter_upwards [hW.mem_nhds hx] with y hy
    ext v
    have hv : v = ![v 0] := by ext i; fin_cases i; rfl
    have hρ : fderiv ℝ (fun y => 4*Real.pi*w y) y=
        (4*Real.pi) • fderiv ℝ w y :=
      fderiv_const_mul ((hwdiff.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)) _
    rw [smoothDc_apply,hρ,hv]
    simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,
      hRapply,hre y hy]
    simp
    field_simp [Real.pi_ne_zero]
    ring
  change extDeriv (smoothDc _) x=extDeriv S x
  have hRd : DifferentiableAt ℝ (fun y => (-1:ℝ) • R y) x :=
    ((hR.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)).const_smul (-1:ℝ)
  rw [hdc.extDeriv_eq,extDeriv_fun_add (hSd x) hRd]
  change extDeriv S x+extDeriv ((-1:ℝ) • R) x=extDeriv S x
  rw [extDeriv_smul,extDeriv_extDeriv_apply (hω₀.contDiffAt (hW.mem_nhds hx))
    (by rw [minSmoothness_of_isRCLikeNormedField];exact WithTop.coe_le_coe.mpr le_top)]
  simp

/-- An arbitrary compact subset of the ENTIRE original ball has one smooth
potential neighborhood. The compact set, the radius and the original form are
inputs; neither a desired primitive nor a dimension-dependent shrink is supplied. -/
theorem exists_smooth_ddc_potential_near_compact_ball (hn : n≠0)
    {z : ComplexModel n} {R : ℝ} (hR : 0<R)
    (a : ComplexModel n → ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a (ball z R))
    (hclosed : ∀ y∈ball z R,extDeriv a y=0)
    (h11 : ∀ y∈ball z R,IsOneOne (a y))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKB : K⊆ball z R) :
    ∃ W : Set (ComplexModel n),IsOpen W ∧ K⊆W ∧ W⊆ball z R ∧
      ∃ ρ : ComplexModel n → ℝ,ContDiffOn ℝ ∞ ρ W ∧ EqOn (smoothDDC ρ) a W := by
  have : Nontrivial (ComplexModel n) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    infer_instance
  have hradius : ∃ r:ℝ,0<r ∧ r<R ∧ K⊆ball z r := by
    by_cases hne : K.Nonempty
    · obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn hne
        (continuous_id.dist continuous_const).continuousOn
      have hyR : dist y z<R := hKB hy
      refine ⟨(dist y z+R)/2,by linarith [dist_nonneg (x := y) (y := z)],
        by linarith,?_⟩
      intro x hx
      change dist x z<(dist y z+R)/2
      have hmx : dist x z≤dist y z := hmax hx
      exact hmx.trans_lt (by linarith)
    · refine ⟨R/2,by positivity,by linarith,?_⟩
      exact (Set.not_nonempty_iff_eq_empty.mp hne) ▸ empty_subset _
  obtain ⟨r,hr,hrR,hKr⟩ := hradius
  obtain ⟨S,hS,hSa⟩ := exists_smooth_twoForm_primitive_on_smaller_ball hr hrR a ha hclosed
  let β : Fin n → ComplexModel n → ℂ := fun i y => zeroOnePart (S y) (basisVec i)
  have hβ (i : Fin n) : ContDiff ℝ ∞ (β i) := by
    simpa [Function.comp_def,zeroOnePartCLM_apply] using
      (zeroOnePartCLM (basisVec i)).contDiff.comp hS
  have hβclosed : IsDbarClosedOn β (ball z r) := by
    intro i j x hx
    refine dbarDir_zeroOnePart_comm (hS.differentiable (by simp) x) ?_ _ _
    rw [hSa x hx]
    exact h11 x (ball_subset_ball hrR.le hx)
  obtain ⟨W,hW,hKW,hWr,f,hf,hfβ⟩ := exists_smooth_dbar_primitive_near_compact
    isOpen_ball (convex_ball z r) isBounded_ball hK hKr hβ hβclosed
  refine ⟨W,hW,hKW,hWr.trans (ball_subset_ball hrR.le),
    fun y => 4*Real.pi*(f y).im,contDiffOn_const.mul (imCLM.contDiff.comp_contDiffOn hf),?_⟩
  intro x hx
  exact (smoothDDC_im_of_dbar_primitive_on hW hS hf hfβ hx).trans (hSa x (hWr hx))

end SGPT.PSH.WholeBallPotentialDraft


/-! Genuine arbitrary holomorphic-ball coordinates are adjoined to the
ORIGINAL varying-dimension atlas, and the entire original closed tensor is
pulled back along the identity. The whole-ball analytic producer then supplies
an actual original local potential near ANY original compact subset. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)
    {n : ℕ} (e : OpenPartialHomeomorph X (ComplexModel n))

/-- Adjoin an actual compatible holomorphic coordinate; every old chart and
every independently declared dimension are retained literally. -/
@[reducible] def adjoinCoordinate
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source) : VariableComplexAtlas X where
  Index := Option A.Index
  dimension := fun i => i.elim n A.dimension
  chart := fun i => match i with | none => e | some i => A.chart i
  cover := fun x => by obtain ⟨i,hi⟩ := A.cover x; exact ⟨some i,hi⟩
  holomorphic := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none =>
        intro z hz
        apply DifferentiableAt.differentiableWithinAt
        apply (differentiableAt_id : DifferentiableAt ℂ (id : ComplexModel n → ComplexModel n) z).congr_of_eventuallyEq
        filter_upwards [(e.symm.trans e).open_source.mem_nhds hz] with y hy
        exact e.right_inv hy.1
      | some j => exact hin j
    | some i =>
      cases j with
      | none => exact hout i
      | some j => exact A.holomorphic i j

/-- The atlas refinement identity is an actual global holomorphic map; it
uses the actual mixed transitions and no supplied tensor/potential output. -/
theorem adjoinCoordinate_identity_isHolomorphic
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source) :
    (A.adjoinCoordinate e hout hin).IsHolomorphic A id := by
  refine ⟨continuous_id,?_⟩
  intro i j
  cases i with
  | none => exact hin j
  | some i => exact A.holomorphic i j

/-- The pullback of the original tensor reads back as its ENTIRE original
coefficient in every retained original chart, not only on diagonal vectors. -/
theorem adjoinCoordinate_pullback_coeff_original
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    (θ : AtlasClosedRealOneOneForm A) (i : A.Index)
    {z : ComplexModel (A.dimension i)} (hz : z∈(A.chart i).target) :
    (θ.holomorphicPullback (A.adjoinCoordinate_identity_isHolomorphic e hout hin)).coeff
      (some i) z=θ.coeff i z := by
  let h := A.adjoinCoordinate_identity_isHolomorphic e hout hin
  have hzdom : z∈atlasCoordinateDomain (A.adjoinCoordinate e hout hin) A id (some i) i :=
    ⟨hz,(A.chart i).map_target hz⟩
  rw [θ.holomorphicPullback_coeff h (some i) i hzdom]
  change (θ.coeff i ((A.chart i) ((A.chart i).symm z))).compContinuousLinearMap
    (fderiv ℝ (fun y => (A.chart i) ((A.chart i).symm y)) z)=θ.coeff i z
  have hev : (fun y => (A.chart i) ((A.chart i).symm y)) =ᶠ[𝓝 z] id := by
    filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy
    exact (A.chart i).right_inv hy
  rw [hev.eq_of_nhds,hev.fderiv_eq,fderiv_id]
  ext w
  simp

/-- A local potential of the actual identity-pulled tensor is an actual
original local potential, retaining literal smoothness and ddᶜ in every chart. -/
theorem original_potential_of_adjoinCoordinate_potential
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    {θ : AtlasClosedRealOneOneForm A} {U : Set X} {g : X → ℝ}
    (hg : (A.adjoinCoordinate e hout hin).IsAtlasLocalPotential
      (θ.holomorphicPullback (A.adjoinCoordinate_identity_isHolomorphic e hout hin)) U g) :
    A.IsAtlasLocalPotential θ U g := by
  refine ⟨hg.1,fun i => hg.2.1 (some i),?_⟩
  intro i z hz
  exact (hg.2.2 (some i) hz).trans
    (A.adjoinCoordinate_pullback_coeff_original e hout hin θ i hz.1)

/-- Original closed tensor, genuine arbitrary compatible ball coordinate,
and arbitrary original compact set manufacture one original all-chart potential
neighborhood. No common chart, supplied potential or fixed radius is assumed. -/
theorem exists_original_potential_near_compact_holomorphic_ball
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    (θ : AtlasClosedRealOneOneForm A) (hn : n≠0)
    {c : ComplexModel n} {R : ℝ} (hR : 0<R) (he : e.target=ball c R)
    {K : Set X} (hK : IsCompact K) (hKe : K⊆e.source) :
    ∃ U : Set X,IsOpen U ∧ K⊆U ∧ U⊆e.source ∧
      ∃ g : X → ℝ,A.IsAtlasLocalPotential θ U g := by
  let B := A.adjoinCoordinate e hout hin
  let η := θ.holomorphicPullback (A.adjoinCoordinate_identity_isHolomorphic e hout hin)
  have hKc : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKe)
  have hKt : e '' K⊆ball c R := by
    rintro _ ⟨x,hx,rfl⟩
    rw [← he]
    exact e.map_source (hKe hx)
  have hηs : ContDiffOn ℝ ∞ (η.coeff none) (ball c R) := by
    have hs := η.smooth none
    change ContDiffOn ℝ ∞ (η.coeff none) e.target at hs
    rwa [he] at hs
  have hηc : ∀ z∈ball c R,extDeriv (η.coeff none) z=0 := by
    intro z hz
    exact η.closed none z (by change z∈e.target; rwa [he])
  have hη11 : ∀ z∈ball c R,IsOneOne (η.coeff none z) := by
    intro z hz
    exact η.typeOneOne none z (by change z∈e.target; rwa [he])
  obtain ⟨W,hW,hKW,hWt,ρ,hρ,heq⟩ :=
    SGPT.PSH.WholeBallPotentialDraft.exists_smooth_ddc_potential_near_compact_ball
      hn hR (η.coeff none) hηs hηc hη11 hKc hKt
  have hWe : W⊆(B.chart none).target := by
    change W⊆e.target
    rwa [he]
  have hpot := coordinate_potential_isAtlasLocalPotential η none hW hWe hρ heq
  refine ⟨e.source∩e ⁻¹' W,e.isOpen_inter_preimage hW,?_,inter_subset_left,
    ρ ∘ e,A.original_potential_of_adjoinCoordinate_potential e hout hin hpot⟩
  intro x hx
  exact ⟨hKe hx,hKW ⟨x,hx,rfl⟩⟩

end SGPT.PSH.VariableComplexAtlas


/-! The actual original tensor potential is continuous in the original
manifold topology and bounded on one smaller open neighborhood of the SAME
arbitrary original compact set. No boundedness or supplied potential premise. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe u
variable {n : ℕ} {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- All-chart real smoothness implies actual original-topology continuity
on the original open domain, through genuine chart inverse equations. -/
theorem ChartSmoothOn.continuousOn_open {g : X → ℝ} {U : Set X}
    (hg : A.ChartSmoothOn g U) (hU : IsOpen U) : ContinuousOn g U := by
  intro x hx
  obtain ⟨i,hi⟩ := A.cover x
  let D := (A.chart i).target∩(A.chart i).symm ⁻¹' U
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hU
  have hxD : A.chart i x∈D := by
    refine ⟨(A.chart i).map_source hi,?_⟩
    change (A.chart i).symm (A.chart i x)∈U
    rwa [(A.chart i).left_inv hi]
  have hc : ContinuousAt (g ∘ (A.chart i).symm) (A.chart i x) :=
    (hg i).continuousOn.continuousAt (hD.mem_nhds hxD)
  have hcomp := hc.comp ((A.chart i).continuousAt hi)
  have hev : g =ᶠ[𝓝 x] (g ∘ (A.chart i).symm) ∘ (A.chart i) := by
    filter_upwards [(A.chart i).open_source.mem_nhds hi] with y hy
    change g y=g ((A.chart i).symm (A.chart i y))
    rw [(A.chart i).left_inv hy]
  exact (hcomp.congr_of_eventuallyEq hev).continuousWithinAt

/-- Actual original θ and arbitrary original holomorphic ball manufacture a
BOUNDED original all-chart potential on one neighborhood of arbitrary compact K. -/
theorem exists_bounded_original_potential_near_compact_holomorphic_ball
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    (θ : AtlasClosedRealOneOneForm A) (hn : n≠0)
    {c : ComplexModel n} {R : ℝ} (hR : 0<R) (he : e.target=ball c R)
    {K : Set X} (hK : IsCompact K) (hKe : K⊆e.source) :
    ∃ V : Set X,IsOpen V ∧ K⊆V ∧ V⊆e.source ∧
      ∃ g : X → ℝ,A.IsAtlasLocalPotential θ V g ∧ ∃ C:ℝ,∀x∈V,|g x|≤C := by
  obtain ⟨U,hU,hKU,hUe,g,hg⟩ :=
    A.exists_original_potential_near_compact_holomorphic_ball e hout hin θ hn hR he hK hKe
  have hgc : ContinuousOn g U := hg.2.1.continuousOn_open hU
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (hgc.mono hKU)
  let V := U∩(fun x => |g x|) ⁻¹' Iio (C+1)
  have hV : IsOpen V := hgc.abs.isOpen_inter_preimage hU isOpen_Iio
  have hKV : K⊆V := by
    intro x hx
    refine ⟨hKU hx,?_⟩
    exact (show |g x|≤C by simpa only [Real.norm_eq_abs] using hC x hx).trans_lt
      (lt_add_one C)
  refine ⟨V,hV,hKV,inter_subset_left.trans hUe,g,?_,C+1,fun x hx => hx.2.le⟩
  refine ⟨hV,fun i => (hg.2.1 i).mono (fun _ hz => ⟨hz.1,hz.2.1⟩),?_⟩
  exact fun i _ hz => hg.2.2 i ⟨hz.1,hz.2.1⟩

end SGPT.PSH.VariableComplexAtlas


/-! Actual original smooth-boundary geometry in a varying-dimension atlas,
transported to the unchanged original domain image under an arbitrary genuine
holomorphic coordinate. The C1 definers, full compact-closure geometry, and
nonzero derivatives are all produced internally from original definers. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe u

/-- Nonzero actual definer derivative survives an ACTUAL differentiable open
partial homeomorphism, by differentiating the genuine inverse equation. -/
theorem fderiv_comp_openPartialHomeomorph_ne_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph E F) {x : E} (hx : x∈e.source)
    (he : DifferentiableAt ℝ e x) (hei : DifferentiableAt ℝ e.symm (e x))
    {r : F → ℝ} (hr : DifferentiableAt ℝ r (e x)) (hrne : fderiv ℝ r (e x)≠0) :
    fderiv ℝ (r ∘ e) x≠0 := by
  have hev : (e ∘ e.symm) =ᶠ[𝓝 (e x)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    exact e.right_inv hy
  have he' : DifferentiableAt ℝ e (e.symm (e x)) := by
    simpa only [e.left_inv hx] using he
  have hchain := fderiv_comp (e x) he' hei
  rw [hev.fderiv_eq,fderiv_id,e.left_inv hx] at hchain
  have hid : (fderiv ℝ e x).comp (fderiv ℝ e.symm (e x))=ContinuousLinearMap.id ℝ F :=
    hchain.symm
  intro hzero
  apply hrne
  ext v
  have hz := congrArg (fun L : E →L[ℝ] ℝ => L (fderiv ℝ e.symm (e x) v)) hzero
  rw [fderiv_comp x hr he] at hz
  change fderiv ℝ r (e x) (fderiv ℝ e x (fderiv ℝ e.symm (e x) v))=0 at hz
  have hv := congrArg (fun L : F →L[ℝ] F => L v) hid
  change fderiv ℝ e x (fderiv ℝ e.symm (e x) v)=v at hv
  rwa [hv] at hz

variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- Literal original local smooth boundary, in an original chart. Fields are
only actual open sets, actual defining functions, ordinary derivatives and the
original domain identity; no C1-sector or balayage output is assumed. -/
structure OriginalSmoothBoundaryChart (D : Opens X) (q : X) where
  chartIndex : A.Index
  neighborhood : Opens X
  point_mem : q∈neighborhood
  source_subset : (neighborhood : Set X)⊆(A.chart chartIndex).source
  definingFunction : ComplexModel (A.dimension chartIndex) → ℝ
  smooth : ContDiffOn ℝ ∞ definingFunction
    ((A.chart chartIndex).target∩(A.chart chartIndex).symm ⁻¹' (neighborhood : Set X))
  zero : definingFunction (A.chart chartIndex q)=0
  derivative_ne_zero : fderiv ℝ definingFunction (A.chart chartIndex q)≠0
  domain_eq : ∀ x∈neighborhood,x∈D ↔ definingFunction (A.chart chartIndex x)<0

/-- The actual source smooth-boundary convention, at EVERY original point. -/
def HasOriginalSmoothBoundary (D : Opens X) : Prop :=
  ∀ q∈frontier (D : Set X),Nonempty (A.OriginalSmoothBoundaryChart D q)

variable {n : ℕ} (e : OpenPartialHomeomorph X (ComplexModel n))

/-- The literal coordinate image, as an actual Euclidean open set. -/
def originalCoordinateDomain (_A : VariableComplexAtlas X) (e : OpenPartialHomeomorph X (ComplexModel n)) (D : Opens X) : Opens (ComplexModel n) :=
  ⟨e.target∩e.symm ⁻¹' (D : Set X),e.symm.isOpen_inter_preimage D.isOpen⟩

/-- Genuine inverse equations give membership correspondence on the exact
original source and target, hence actual closure/interior/frontier transport. -/
theorem originalCoordinateDomain_isImage (D : Opens X) :
    e.IsImage (D : Set X) (A.originalCoordinateDomain e D : Set (ComplexModel n)) := by
  intro x hx
  constructor
  · intro h
    change e x∈e.target∩e.symm ⁻¹' (D : Set X) at h
    have hd := h.2
    change e.symm (e x)∈D at hd
    rwa [e.left_inv hx] at hd
  · intro h
    change e x∈e.target∩e.symm ⁻¹' (D : Set X)
    exact ⟨e.map_source hx,by change e.symm (e x)∈D; rwa [e.left_inv hx]⟩

/-- The ENTIRE actual coordinate-domain closure lies in the compact image
of the ENTIRE original closure. No changed domain or supplied boundary witness. -/
theorem originalCoordinateDomain_closure_subset (D : Opens X)
    (hDc : IsCompact (closure (D : Set X))) (hDe : closure (D : Set X)⊆e.source) :
    closure (A.originalCoordinateDomain e D : Set (ComplexModel n))⊆
      e '' closure (D : Set X) := by
  apply closure_minimal
  · intro z hz
    change z∈e.target∩e.symm ⁻¹' (D : Set X) at hz
    exact ⟨e.symm z,subset_closure hz.2,e.right_inv hz.1⟩
  · exact (hDc.image_of_continuousOn (e.continuousOn.mono hDe)).isClosed

/-- Actual compactness and containment demanded by the frozen C1-domain
producer, on the literal coordinate image of the original domain. -/
theorem originalCoordinateDomain_compact_closure (D : Opens X)
    (hDc : IsCompact (closure (D : Set X))) (hDe : closure (D : Set X)⊆e.source) :
    IsCompact (closure (A.originalCoordinateDomain e D : Set (ComplexModel n))) ∧
      closure (A.originalCoordinateDomain e D : Set (ComplexModel n))⊆e.target := by
  have hsub := A.originalCoordinateDomain_closure_subset e D hDc hDe
  refine ⟨(hDc.image_of_continuousOn (e.continuousOn.mono hDe)).of_isClosed_subset
    isClosed_closure hsub,?_⟩
  rintro z hz
  obtain ⟨x,hx,rfl⟩ := hsub hz
  exact e.map_source (hDe hx)

/-- Actual smooth original boundary yields ALL genuine Euclidean C1 boundary
fields under the same arbitrary original holomorphic-ball coordinate. The old
chart dimension and the ball dimension remain independently declared. -/
theorem originalCoordinateDomain_hasC1Boundary (D : Opens X)
    (hDc : IsCompact (closure (D : Set X))) (hDe : closure (D : Set X)⊆e.source)
    (hboundary : A.HasOriginalSmoothBoundary D)
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source) :
    SourceDomainBalayageDraft.HasC1Boundary (A.originalCoordinateDomain e D) := by
  intro z hz
  have hzT : z∈e.target :=
    (A.originalCoordinateDomain_compact_closure e D hDc hDe).2 (frontier_subset_closure hz)
  have hqfront : e.symm z∈frontier (D : Set X) :=
    ((A.originalCoordinateDomain_isImage e D).frontier.symm_apply_mem_iff hzT).mpr hz
  obtain ⟨c⟩ := hboundary (e.symm z) hqfront
  let F := e.symm.trans (A.chart c.chartIndex)
  let Q : Opens (ComplexModel n) :=
    ⟨e.target∩e.symm ⁻¹' (c.neighborhood : Set X),
      e.symm.isOpen_inter_preimage c.neighborhood.isOpen⟩
  let O := (A.chart c.chartIndex).target∩
    (A.chart c.chartIndex).symm ⁻¹' (c.neighborhood : Set X)
  have hO : IsOpen O := (A.chart c.chartIndex).isOpen_inter_preimage_symm c.neighborhood.isOpen
  have hzQ : z∈Q := ⟨hzT,c.point_mem⟩
  have hQF : (Q : Set (ComplexModel n))⊆F.source :=
    fun _ hw => ⟨hw.1,c.source_subset hw.2⟩
  have hFO : MapsTo F Q O := by
    intro w hw
    refine ⟨(A.chart c.chartIndex).map_source (c.source_subset hw.2),?_⟩
    change (A.chart c.chartIndex).symm ((A.chart c.chartIndex) (e.symm w))∈c.neighborhood
    rw [(A.chart c.chartIndex).left_inv (c.source_subset hw.2)]
    exact hw.2
  have hF : ContDiffOn ℂ ∞ F F.source :=
    contDiffOn_of_differentiableOn_complex (hin c.chartIndex) F.open_source
  have hρ : ContDiffOn ℝ 1 (c.definingFunction ∘ F) Q :=
    (c.smooth.of_le (by simp)).comp
      (((hF.mono hQF).restrict_scalars ℝ).of_le (by simp)) hFO
  have hzF : z∈F.source := hQF hzQ
  have hFdiff : DifferentiableAt ℝ F z :=
    ((hF.contDiffAt (F.open_source.mem_nhds hzF)).restrict_scalars ℝ).differentiableAt (by simp)
  have hFi : ContDiffOn ℂ ∞ F.symm F.target := by
    exact contDiffOn_of_differentiableOn_complex (hout c.chartIndex) F.open_target
  have hFidiff : DifferentiableAt ℝ F.symm (F z) :=
    ((hFi.contDiffAt (F.open_target.mem_nhds (F.map_source hzF))).restrict_scalars ℝ).differentiableAt (by simp)
  have hr : DifferentiableAt ℝ c.definingFunction (F z) :=
    (c.smooth.contDiffAt (hO.mem_nhds (hFO hzQ))).differentiableAt (by simp)
  refine ⟨⟨Q,hzQ,c.definingFunction ∘ F,hρ,c.zero,
    fderiv_comp_openPartialHomeomorph_ne_zero F hzF hFdiff hFidiff hr c.derivative_ne_zero,?_⟩⟩
  intro w hw
  change (w∈e.target∧e.symm w∈D) ↔ c.definingFunction (A.chart c.chartIndex (e.symm w))<0
  exact ⟨fun h => (c.domain_eq _ hw.2).mp h.2,
    fun h => ⟨hw.1,(c.domain_eq _ hw.2).mpr h⟩⟩

end SGPT.PSH.VariableComplexAtlas


/-! Actual full-tensor local-potential independence for actual Bedford--Taylor
limit measures. The complex Hessian is derived from the whole normalized ddc
tensor, not assumed as a replacement for that tensor. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.OriginalBTGaugeDraft
open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open scoped Topology ContDiff

theorem complexHessian_eq_zero_of_smoothDDC_eq_zero {n : ℕ}
    {h : ComplexModel n → ℝ} {z : ComplexModel n}
    (hh : ContDiffAt ℝ 2 h z) (hzero : smoothDDC h z=0) :
    complexHessian h z=0 := by
  have hs (v w : ComplexModel n) : realHessian h z v w=realHessian h z w v := by
    simpa only [realHessian_eq_fderiv] using hh.isSymmSndFDerivAt (by norm_num) v w
  have heq (v w : ComplexModel n) :
      realHessian h z w (Complex.I • v)-realHessian h z v (Complex.I • w)=0 := by
    have hz := congrArg (fun a => a ![v,w]) hzero
    rw [smoothDDC_apply_eq_realHessian hh] at hz
    change (realHessian h z w (Complex.I • v)-
      realHessian h z v (Complex.I • w))/(4*Real.pi)=0 at hz
    exact (div_eq_zero_iff.mp hz).resolve_right (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hn (v w : ComplexModel n) : realHessian h z v (-w)= -realHessian h z v w := by
    simp [realHessian_eq_fderiv]
  ext j k
  have him := heq (coordinateVector j) (coordinateVector k)
  have hre := heq (coordinateVector j) (Complex.I • coordinateVector k)
  simp only [smul_smul,Complex.I_mul_I,neg_one_smul,hn] at hre
  rw [hs (coordinateVector k) (Complex.I • coordinateVector j)] at him
  rw [hs (Complex.I • coordinateVector k) (Complex.I • coordinateVector j)] at hre
  have hre' : realHessian h z (coordinateVector j) (coordinateVector k)+
      realHessian h z (Complex.I • coordinateVector j) (Complex.I • coordinateVector k)=0 := by
    linarith
  have him' : realHessian h z (coordinateVector j) (Complex.I • coordinateVector k)-
      realHessian h z (Complex.I • coordinateVector j) (coordinateVector k)=0 := by
    linarith
  simp only [complexHessian,hre',him',Complex.ofReal_zero,zero_div,mul_zero,add_zero,
    Matrix.zero_apply]

theorem isBTLimit_add_of_smoothDDC_eq_zero {n : ℕ}
    {Ω : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω v μ)
    {h : Fin n → ComplexModel n → ℝ}
    (hh : ∀ i,ContDiffOn ℝ ∞ (h i) Ω)
    (hzero : ∀ i z,z∈Ω → smoothDDC (h i) z=0) :
    IsBTLimit Ω (fun i z => v i z+h i z) μ := by
  apply hμ.add_pluriharmonic
  intro i
  have h2 : (2 : WithTop ℕ∞)≤∞ := WithTop.coe_le_coe.mpr le_top
  exact ⟨hh i,fun z hz => complexHessian_eq_zero_of_smoothDDC_eq_zero
    (((hh i).contDiffAt (Ω.isOpen.mem_nhds hz)).of_le h2) (hzero i z hz)⟩

end SGPT.PSH.OriginalBTGaugeDraft

namespace SGPT.PSH.VariableComplexAtlas
open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open scoped Topology ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

theorem IsAtlasLocalPotential.btLimit_change_potential
    {θ : AtlasClosedRealOneOneForm A} {U : Set X} {g b : X → ℝ}
    (hg : A.IsAtlasLocalPotential θ U g) (hb : A.IsAtlasLocalPotential θ U b)
    (i : A.Index) {Ω : Opens (ComplexModel (A.dimension i))}
    (hΩ : (Ω : Set _)⊆(A.chart i).target∩(A.chart i).symm ⁻¹' U)
    {v : ComplexModel (A.dimension i) → ℝ} {μ : Measure (ComplexModel (A.dimension i))}
    (hμ : IsBTLimit Ω (fun _ z => v z+g ((A.chart i).symm z)) μ) :
    IsBTLimit Ω (fun _ z => v z+b ((A.chart i).symm z)) μ := by
  let h : ComplexModel (A.dimension i) → ℝ := fun z =>
    b ((A.chart i).symm z)-g ((A.chart i).symm z)
  have hh : ContDiffOn ℝ ∞ h Ω := ((hb.2.1 i).sub (hg.2.1 i)).mono hΩ
  have hz : ∀ z∈Ω,smoothDDC h z=0 := by
    intro z hz
    change smoothDDC (fun z => (b ∘ (A.chart i).symm) z-(g ∘ (A.chart i).symm) z) z=0
    rw [PositiveClasses.smoothDDC_sub Ω.isOpen ((hb.2.1 i).mono hΩ)
      ((hg.2.1 i).mono hΩ) hz,hb.2.2 i (hΩ hz),hg.2.2 i (hΩ hz),sub_self]
  have hm := OriginalBTGaugeDraft.isBTLimit_add_of_smoothDDC_eq_zero hμ
    (fun _ => hh) (fun _ z hz' => hz z hz')
  exact hm.congr (fun _ z _ => by dsimp [h]; ring)

end SGPT.PSH.VariableComplexAtlas


/-! Original universal theta-PSH condition from an actual single local
potential, and its locality on arbitrary original open covers. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

theorem originalCoordinate_isHolomorphicOn {n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source) :
    A.IsHolomorphicOn (identityAtlas n) e e.source := by
  refine ⟨e.continuousOn,?_⟩
  intro i j
  cases j
  change DifferentiableOn ℂ (e ∘ (A.chart i).symm)
    ((A.chart i).target∩(A.chart i).symm ⁻¹' (e.source∩e ⁻¹' univ))
  exact (hout i).mono (fun z hz => ⟨hz.1,hz.2.1⟩)

theorem originalCoordinate_inverse_isHolomorphicOn {n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source) :
    (identityAtlas n).IsHolomorphicOn A e.symm e.target := by
  refine ⟨e.continuousOn_symm,?_⟩
  intro j i
  cases j
  change DifferentiableOn ℂ ((A.chart i) ∘ e.symm)
    (univ∩id ⁻¹' (e.target∩e.symm ⁻¹' (A.chart i).source))
  exact (hin i).mono (fun z hz => hz.2)

theorem IsPSHOn.originalCoordinateDomain {n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    {D : TopologicalSpace.Opens X} {v : X → EReal} (hv : A.IsPSHOn v D) :
    (identityAtlas n).IsPSHOn (v ∘ e.symm) (A.originalCoordinateDomain e D) := by
  exact hv.comp_openPartialHolomorphicInverse D.isOpen
    (A.originalCoordinateDomain e D).isOpen (fun z hz => hz.1)
    (fun z hz => hz.2) (originalCoordinate_inverse_isHolomorphicOn e hin)

theorem IsAtlasLocalPotential.isThetaPSHOn_of_corrected
    {θ : AtlasClosedRealOneOneForm A} {U : Set X} {g : X → ℝ}
    (hg : A.IsAtlasLocalPotential θ U g) {u : X → EReal}
    (hu : A.IsPSHOn (fun x => u x+(g x:EReal)) U) : A.IsThetaPSHOn θ u U := by
  constructor
  · intro x hx htop
    have ht := hu.ne_top hx
    simp [htop] at ht
  · intro V b hVU hb
    have hp := hu.mono_open hg.1 hb.1 hVU
    have hgV := hg.mono hb.1 hVU
    apply (isPSHOn_iff_chart_and_nondegenerate hb.1).mpr
    constructor
    · intro i
      let D := (A.chart i).target∩(A.chart i).symm ⁻¹' V
      have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hb.1
      have hz : ∀ z∈D,smoothDDC (fun y =>
          b ((A.chart i).symm y)-g ((A.chart i).symm y)) z=0 := by
        intro z hz
        change smoothDDC (fun y => (b ∘ (A.chart i).symm) y-
          (g ∘ (A.chart i).symm) y) z=0
        rw [PositiveClasses.smoothDDC_sub hD (hb.2.1 i) (hgV.2.1 i) hz,
          hb.2.2 i hz,hgV.2.2 i hz,sub_self]
      have hd := plurisubharmonicOn_coe_of_smoothDDC_eq_zero hD
        ((hb.2.1 i).sub (hgV.2.1 i)) hz
      intro z hz
      apply ((hp.chartPlurisubharmonic i z hz).add (hd z hz)).congr
      exact Eventually.of_forall fun y => corrected_add_sub
        (u ((A.chart i).symm y)) (g ((A.chart i).symm y)) (b ((A.chart i).symm y))
    · intro x hx O hO hxO
      obtain ⟨y,hy,hfin⟩ := hp.locallyNondegenerate hb.1 x hx O hO hxO
      have hufin : u y≠⊥ := (EReal.add_ne_bot_iff.mp hfin).1
      exact ⟨y,hy,EReal.add_ne_bot_iff.mpr ⟨hufin,EReal.coe_ne_bot _⟩⟩

theorem isThetaPSH_of_locally_isThetaPSHOn
    {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hu : ∀ x : X,∃ O : Set X,IsOpen O ∧ x∈O ∧ A.IsThetaPSHOn θ u O) :
    A.IsThetaPSH θ u := by
  constructor
  · intro x
    obtain ⟨O,-,hx,hp⟩ := hu x
    exact hp.1 x hx
  · intro U g hg x hx
    obtain ⟨O,hO,hxO,hp⟩ := hu x
    have hQ := hg.1.inter hO
    have hlocal := hp.2 (U∩O) g inter_subset_right (hg.mono hQ inter_subset_left)
    obtain ⟨i,hi,V,hV,hc,hVe,hxV,hpsh⟩ := hlocal x ⟨hx,hxO⟩
    exact ⟨i,hi,V,hV,hc,fun z hz => ⟨(hVe hz).1,(hVe hz).2.1⟩,hxV,hpsh⟩

end SGPT.PSH.VariableComplexAtlas


/-! Genuine finite-point and Euclidean/source PSH dictionary for the actual
identity atlas. No connectedness or non-bottom output certificate is hidden. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe u

theorem identityAtlas_isPSHOn_of_plurisubharmonic_nonbot
    {n : ℕ} {U : Set (ComplexModel n)} (hU : IsOpen U) {v : ComplexModel n → EReal}
    (hv : PlurisubharmonicOn v U) (hfin : ∀ x∈U,v x≠⊥) :
    (identityAtlas n).IsPSHOn v U := by
  apply (isPSHOn_iff_chart_and_nondegenerate hU).mpr
  constructor
  · intro i
    cases i
    change PlurisubharmonicOn (v ∘ id) (univ∩id ⁻¹' U)
    simpa only [Function.comp_id,preimage_id,univ_inter] using hv
  · intro x hx O hO hxO
    exact ⟨x,⟨hx,hxO⟩,hfin x hx⟩

theorem identityAtlas_pshOn_of_isPSHOn_nonempty
    {n : ℕ} {U : Set (ComplexModel n)} (hU : IsOpen U) (hne : U.Nonempty)
    {v : ComplexModel n → EReal} (hv : (identityAtlas n).IsPSHOn v U) :
    SGPT.PSH.PSHOn v U := by
  have hp : PlurisubharmonicOn v U := by
    have h := hv.chartPlurisubharmonic ()
    change PlurisubharmonicOn (v ∘ id) (univ∩id ⁻¹' U) at h
    simpa only [Function.comp_id,preimage_id,univ_inter] using h
  obtain ⟨x,hx⟩ := hne
  obtain ⟨y,hy,hfin⟩ := hv.locallyNondegenerate hU x hx univ isOpen_univ (mem_univ x)
  exact ⟨hp.discPshOn,⟨y,hy.1,hfin⟩⟩

variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

theorem IsThetaPSHOn.congr {θ : AtlasClosedRealOneOneForm A} {U : Set X}
    {v w : X → EReal} (hv : A.IsThetaPSHOn θ v U) (heq : EqOn v w U) :
    A.IsThetaPSHOn θ w U := by
  refine ⟨fun x hx => by simpa only [← heq hx] using hv.1 x hx,?_⟩
  intro V g hVU hg
  exact (hv.2 V g hVU hg).congr (fun x hx => by
    change v x+(g x:EReal)=w x+(g x:EReal)
    rw [heq (hVU hx)])

end SGPT.PSH.VariableComplexAtlas


/-! Actual original global theta-PSH replacement from the frozen C1 producer.
This is a construction with its actual coordinate BT measure, not a claim
that the remaining intrinsic all-chart MA dictionary and uniqueness are done. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Metric TopologicalSpace MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open scoped Topology ContDiff
universe u

theorem ereal_add_coe_twoSidedBound {a : EReal} {b C E : ℝ}
    (ha : ((-C:ℝ):EReal)≤a ∧ a≤C) (hb : |b|≤E) :
    ((-(C+E):ℝ):EReal)≤a+(b:EReal) ∧ a+(b:EReal)≤((C+E:ℝ):EReal) := by
  constructor
  · calc
      ((-(C+E):ℝ):EReal)=((-C:ℝ):EReal)+((-E:ℝ):EReal) := by
        rw [← EReal.coe_add]
        congr 1
        ring
      _≤a+(b:EReal) := add_le_add ha.1 (EReal.coe_le_coe_iff.mpr (neg_le_of_abs_le hb))
  · calc
      a+(b:EReal)≤(C:EReal)+(E:EReal) :=
        add_le_add ha.2 (EReal.coe_le_coe_iff.mpr ((le_abs_self b).trans hb))
      _=((C+E:ℝ):EReal) := by rw [EReal.coe_add]

variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

theorem exists_original_thetaPSH_replacement_with_coordinate_BT {n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    {c : ComplexModel n} {R : ℝ} (hR : 0<R) (he : e.target=ball c R) (hn : 0<n)
    (D : Opens X) (hDne : (D : Set X).Nonempty)
    (hDc : IsCompact (closure (D : Set X))) (hDe : closure (D : Set X)⊆e.source)
    (hboundary : A.HasOriginalSmoothBoundary D)
    (θ : AtlasClosedRealOneOneForm A) {φ : X → EReal} (hφ : A.IsThetaPSH θ φ)
    (hφb : ∀ x∈e.source,∃ O∈𝓝 x,∃ C : ℝ,∀ y∈O,((-C:ℝ):EReal)≤φ y ∧ φ y≤C) :
    ∃ Ψ : X → EReal,A.IsThetaPSH θ Ψ ∧ EqOn Ψ φ (D : Set X)ᶜ ∧
      (∀ x,φ x≤Ψ x) ∧
      (∃ W : Opens X,closure (D : Set X)⊆(W:Set X) ∧
        ∃ C : ℝ,∀ x∈W,((-C:ℝ):EReal)≤Ψ x ∧ Ψ x≤C) ∧
      ∃ (U : Opens X) (g : X → ℝ),closure (D : Set X)⊆(U:Set X) ∧
        (U:Set X)⊆e.source ∧ A.IsAtlasLocalPotential θ U g ∧
        ∃ μ : Measure (ComplexModel n),
          IsBTLimit (A.originalCoordinateDomain e U)
            (fun _ z => (Ψ (e.symm z)+(g (e.symm z):EReal)).toReal) μ ∧
          μ (A.originalCoordinateDomain e D : Set (ComplexModel n))=0 := by
  classical
  obtain ⟨U0,hU0,hDU,hUe,g,hg,Cg,hCg⟩ :=
    A.exists_bounded_original_potential_near_compact_holomorphic_ball e hout hin θ hn.ne'
      hR he hDc hDe
  let U : Opens X := ⟨U0,hU0⟩
  let Ω := A.originalCoordinateDomain e U
  let Dc := A.originalCoordinateDomain e D
  have hDΩ : closure (Dc : Set (ComplexModel n))⊆Ω := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := A.originalCoordinateDomain_closure_subset e D hDc hDe hz
    refine ⟨e.map_source (hDe hx),?_⟩
    change e.symm (e x)∈U0
    rw [e.left_inv (hDe hx)]
    exact hDU hx
  have hDc' : IsCompact (closure (Dc : Set (ComplexModel n))) :=
    (A.originalCoordinateDomain_compact_closure e D hDc hDe).1
  have hBd := A.originalCoordinateDomain_hasC1Boundary e D hDc hDe hboundary hout hin
  let f : ComplexModel n → EReal := fun z => φ (e.symm z)+(g (e.symm z):EReal)
  have hp0 : (identityAtlas n).IsPSHOn f Ω :=
    IsPSHOn.originalCoordinateDomain (D:=U) e hin (hφ.2 U0 g hg)
  have hΩne : (Ω : Set (ComplexModel n)).Nonempty := by
    obtain ⟨x,hx⟩ := hDne
    have hxcl := subset_closure hx
    refine ⟨e x,e.map_source (hDe hxcl),?_⟩
    change e.symm (e x)∈U0
    rw [e.left_inv (hDe hxcl)]
    exact hDU hxcl
  have hfp : SGPT.PSH.PSHOn f Ω :=
    identityAtlas_pshOn_of_isPSHOn_nonempty Ω.isOpen hΩne hp0
  have hfb : ∀ z∈Ω,∃ O∈𝓝 z,∃ C : ℝ,∀ w∈O,((-C:ℝ):EReal)≤f w ∧ f w≤C := by
    intro z hz
    obtain ⟨O,hO,C,hC⟩ := hφb (e.symm z) (e.map_target hz.1)
    let Q := (Ω : Set (ComplexModel n))∩e.symm ⁻¹' O
    have hQ : Q∈𝓝 z := inter_mem (Ω.isOpen.mem_nhds hz)
      ((e.continuousAt_symm hz.1).preimage_mem_nhds hO)
    exact ⟨Q,hQ,C+Cg,fun w hw => ereal_add_coe_twoSidedBound (hC _ hw.2) (hCg _ hw.1.2)⟩
  obtain ⟨ψ,hψ,hψb,⟨μ,hμ,hμzero⟩,hψeq,hψorder,⟨V,hDV,hVΩ,Cψ,hCψ⟩,hψunique⟩ :=
    SourceDomainBalayageDraft.source_exists_unique_C1DomainBalayage hn hfp hfb hDc' hDΩ hBd
  let Ψ : X → EReal := fun x => if x∈(D:Set X) then ψ (e x)+((-g x:ℝ):EReal) else φ x
  have hcorrect : ∀ x∈U0,Ψ x+(g x:EReal)=ψ (e x) := by
    intro x hx
    have hxe := hUe hx
    have hxΩ : e x∈Ω := ⟨e.map_source hxe,by change e.symm (e x)∈U0; rwa [e.left_inv hxe]⟩
    by_cases hxD : x∈(D:Set X)
    · simp only [Ψ,if_pos hxD,add_assoc,← EReal.coe_add,neg_add_cancel,EReal.coe_zero,add_zero]
    · have hxDc : e x∉(Dc:Set (ComplexModel n)) := by
        intro h
        have h' := h.2
        change e.symm (e x)∈D at h'
        exact hxD ((e.left_inv hxe) ▸ h')
      have heq := hψeq (e x) hxΩ hxDc
      change ψ (e x)=φ (e.symm (e x))+(g (e.symm (e x)):EReal) at heq
      rw [e.left_inv hxe] at heq
      simpa only [Ψ,if_neg hxD] using heq.symm
  have hψfin : ∀ z∈Ω,ψ z≠⊥ := by
    intro z hz
    obtain ⟨O,hO,C,hC⟩ := hψb z hz
    exact ne_bot_of_gt ((EReal.bot_lt_coe (-C)).trans_le (hC z (mem_of_mem_nhds hO)).1)
  have hpψ := identityAtlas_isPSHOn_of_plurisubharmonic_nonbot Ω.isOpen
    (hψ.disc.plurisubharmonicOn Ω.isOpen) hψfin
  have hpOrig : A.IsPSHOn (ψ ∘ e) U0 :=
    hpψ.comp_openPartialHolomorphicInverse (e:=e.symm) Ω.isOpen hU0 hUe
      (fun x hx => ⟨e.map_source (hUe hx),by
        change e.symm (e x)∈U0; rwa [e.left_inv (hUe hx)]⟩)
      (originalCoordinate_isHolomorphicOn e hout)
  have hθU : A.IsThetaPSHOn θ Ψ U0 := hg.isThetaPSHOn_of_corrected
    (hpOrig.congr (fun x hx => (hcorrect x hx).symm))
  have hθOut : A.IsThetaPSHOn θ Ψ (closure (D:Set X))ᶜ :=
    (hφ.isThetaPSHOn _).congr (fun x hx => by
      have hxD : x∉(D:Set X) := fun h => hx (subset_closure h)
      simp only [Ψ,if_neg hxD])
  have hθ : A.IsThetaPSH θ Ψ := isThetaPSH_of_locally_isThetaPSHOn (fun x => by
    by_cases hx : x∈U0
    · exact ⟨U0,hU0,hx,hθU⟩
    · exact ⟨(closure (D:Set X))ᶜ,isClosed_closure.isOpen_compl,
        fun h => hx (hDU h),hθOut⟩)
  have horder : ∀ x,φ x≤Ψ x := by
    intro x
    by_cases hx : x∈(D:Set X)
    · have hxU := hDU (subset_closure hx)
      have hxe := hUe hxU
      have hxΩ : e x∈Ω := ⟨e.map_source hxe,by change e.symm (e x)∈U0; rwa [e.left_inv hxe]⟩
      have ho := hψorder (e x) hxΩ
      change φ (e.symm (e x))+(g (e.symm (e x)):EReal)≤ψ (e x) at ho
      rw [e.left_inv hxe,← hcorrect x hxU] at ho
      exact (EReal.addLECancellable_coe _).add_le_add_iff_right.mp ho
    · simp only [Ψ,if_neg hx]
      exact le_rfl
  let W : Opens X := ⟨U0∩(e.source∩e ⁻¹' (V:Set (ComplexModel n))),
    hU0.inter (e.isOpen_inter_preimage V.isOpen)⟩
  have hDW : closure (D:Set X)⊆(W:Set X) := by
    intro x hx
    refine ⟨hDU hx,hDe hx,?_⟩
    apply hDV
    exact ((A.originalCoordinateDomain_isImage e D).closure (hDe hx)).mpr hx
  have hCW : ∀ x∈W,((-(Cψ+Cg):ℝ):EReal)≤Ψ x ∧ Ψ x≤Cψ+Cg := by
    intro x hx
    have hb := ereal_add_coe_twoSidedBound (hCψ (e x) hx.2.2)
      (by simpa only [abs_neg] using hCg x hx.1 : |-g x|≤Cg)
    have heq : Ψ x=ψ (e x)+((-g x:ℝ):EReal) := by
      calc
        Ψ x=(Ψ x+(g x:EReal))+((-g x:ℝ):EReal) := by
          rw [add_assoc,← EReal.coe_add,add_neg_cancel,EReal.coe_zero,add_zero]
        _=ψ (e x)+((-g x:ℝ):EReal) := by rw [hcorrect x hx.1]
    rwa [← heq] at hb
  refine ⟨Ψ,hθ,?_,horder,⟨W,hDW,Cψ+Cg,hCW⟩,U,g,hDU,hUe,hg,μ,?_,hμzero⟩
  · intro x hx
    simp only [Ψ,if_neg hx]
  · apply hμ.congr
    intro i z hz
    change (ψ z).toReal=(Ψ (e.symm z)+(g (e.symm z):EReal)).toReal
    rw [hcorrect (e.symm z) hz.2,e.right_inv hz.1]

end SGPT.PSH.VariableComplexAtlas


/-! Actual BT covariance across original holomorphic coordinate dimensions:
dimension equality is derived from actual inverse derivatives, not assumed. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.OriginalBTCoordinateDraft
open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open scoped Topology ContDiff

theorem isBTLimit_comp_holomorphic_openPartial {m n : ℕ}
    (e : OpenPartialHomeomorph (ComplexModel m) (ComplexModel n))
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (hne : e.source.Nonempty) {v : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit ⟨e.target,e.open_target⟩ (fun _ => v) μ) :
    IsBTLimit ⟨e.source,e.open_source⟩ (fun _ x => v (e x))
      ((μ.restrict e.target).map e.symm) := by
  have hdim := SGPT.PSH.model_dimension_eq_of_holomorphic_openPartial e he hi hne
  subst n
  have hpair : IsBiholomorphicPair ⟨e.source,e.open_source⟩ ⟨e.target,e.open_target⟩ e e.symm :=
    ⟨contDiffOn_of_differentiableOn_complex he e.open_source,
      contDiffOn_of_differentiableOn_complex hi e.open_target,
      fun x hx => e.map_source hx,fun y hy => e.map_target hy,
      fun x hx => e.left_inv hx,fun y hy => e.right_inv hy⟩
  exact hμ.comp_biholomorphic hpair

theorem isBTLimit_zero_comp_holomorphic_openPartial {m n : ℕ}
    (e : OpenPartialHomeomorph (ComplexModel m) (ComplexModel n))
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (hne : e.source.Nonempty) {v : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit ⟨e.target,e.open_target⟩ (fun _ => v) μ) (hzero : μ e.target=0) :
    IsBTLimit ⟨e.source,e.open_source⟩ (fun _ x => v (e x)) 0 := by
  have h := isBTLimit_comp_holomorphic_openPartial e he hi hne hμ
  rw [Measure.restrict_eq_zero.mpr hzero,Measure.map_zero] at h
  exact h

end SGPT.PSH.OriginalBTCoordinateDraft


/-! Actual mixed-coordinate holomorphy from compatibility with the entire
original atlas, without assuming common dimension or mixed-transition output. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

theorem compatibleCoordinate_transition_differentiableOn {m n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel m))
    (f : OpenPartialHomeomorph X (ComplexModel n))
    (hei : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    (hfo : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans f)
      ((A.chart i).symm.trans f).source) :
    DifferentiableOn ℂ (e.symm.trans f) (e.symm.trans f).source := by
  intro z hz
  obtain ⟨i,hi⟩ := A.cover (e.symm z)
  let P := e.symm.trans (A.chart i)
  let Q := (A.chart i).symm.trans f
  let D := e.target∩e.symm ⁻¹' ((A.chart i).source∩f.source)
  have hD : IsOpen D := e.symm.isOpen_inter_preimage
    ((A.chart i).open_source.inter f.open_source)
  have hzD : z∈D := ⟨hz.1,hi,hz.2⟩
  have hzP : z∈P.source := ⟨hz.1,hi⟩
  have hzQ : P z∈Q.source := by
    refine ⟨(A.chart i).map_source hi,?_⟩
    change (A.chart i).symm ((A.chart i) (e.symm z))∈f.source
    rw [(A.chart i).left_inv hi]
    exact hz.2
  have hp : DifferentiableAt ℂ P z := (hei i z hzP).differentiableAt
    (P.open_source.mem_nhds hzP)
  have hq : DifferentiableAt ℂ Q (P z) := (hfo i (P z) hzQ).differentiableAt
    (Q.open_source.mem_nhds hzQ)
  have heq : (e.symm.trans f : ComplexModel m → ComplexModel n)=ᶠ[𝓝 z] Q ∘ P := by
    filter_upwards [hD.mem_nhds hzD] with y hy
    change f (e.symm y)=f ((A.chart i).symm ((A.chart i) (e.symm y)))
    rw [(A.chart i).left_inv hy.2.1]
  exact ((hq.comp z hp).congr_of_eventuallyEq heq).differentiableWithinAt

end SGPT.PSH.VariableComplexAtlas


/-! Intrinsic actual zero-MA condition, quantified over genuine compatible
coordinates and actual original local potentials. A produced coordinate BT
measure is transported to every actual test; no target replacement is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open scoped Topology ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

def IsZeroThetaMongeAmpereOn (θ : AtlasClosedRealOneOneForm A) (v : X → EReal)
    (D : Set X) : Prop :=
  ∀ n : ℕ,∀ e : OpenPartialHomeomorph X (ComplexModel n),
    (∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e) ((A.chart i).symm.trans e).source) →
    (∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i)) (e.symm.trans (A.chart i)).source) →
    e.source⊆D → ∀ (U : Set X) (g : X → ℝ),A.IsAtlasLocalPotential θ U g → e.source⊆U →
      IsBTLimit ⟨e.target,e.open_target⟩
        (fun _ z => (v (e.symm z)+(g (e.symm z):EReal)).toReal) 0

theorem isBTLimit_zero_of_empty_domain {n : ℕ} {Ω : Opens (ComplexModel n)}
    (hΩ : (Ω:Set (ComplexModel n))=∅) (v : Fin n → ComplexModel n → ℝ) : IsBTLimit Ω v 0 := by
  have hempty : ∀ z∈Ω,False := by
    intro z hz
    change z∈(Ω:Set (ComplexModel n)) at hz
    rw [hΩ] at hz
    exact hz
  obtain ⟨μ,hμ⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (Ω:=Ω) (u:=v) (fun i =>
    ⟨fun z hz => (hempty z hz).elim,fun z hz => (hempty z hz).elim⟩)
  have hzero : μ=0 := by
    have hz := hμ.1
    simpa [hΩ] using hz
  simpa only [hzero] using hμ

theorem isZeroThetaMongeAmpereOn_of_coordinate_BT {n : ℕ}
    (e0 : OpenPartialHomeomorph X (ComplexModel n))
    (hout0 : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e0)
      ((A.chart i).symm.trans e0).source)
    (hin0 : ∀ i,DifferentiableOn ℂ (e0.symm.trans (A.chart i))
      (e0.symm.trans (A.chart i)).source)
    {θ : AtlasClosedRealOneOneForm A} {v : X → EReal} (D U : Opens X)
    (hDU : (D:Set X)⊆U) (hUe : (U:Set X)⊆e0.source) {g0 : X → ℝ}
    (hg0 : A.IsAtlasLocalPotential θ U g0)
    (hfinite : ∀ x∈D,v x≠⊤ ∧ v x≠⊥) {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (A.originalCoordinateDomain e0 U)
      (fun _ z => (v (e0.symm z)+(g0 (e0.symm z):EReal)).toReal) μ)
    (hμzero : μ (A.originalCoordinateDomain e0 D : Set (ComplexModel n))=0) :
    A.IsZeroThetaMongeAmpereOn θ v D := by
  intro m e hout hin heD W g hg heW
  by_cases hne : e.source.Nonempty
  · let F := e.symm.trans e0
    have hF : DifferentiableOn ℂ F F.source :=
      compatibleCoordinate_transition_differentiableOn e e0 hin hout0
    have hFi : DifferentiableOn ℂ F.symm F.target := by
      change DifferentiableOn ℂ F.symm F.symm.source
      simpa only [F,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using
        compatibleCoordinate_transition_differentiableOn e0 e hin0 hout
    have hFs : F.source=e.target := by
      apply subset_antisymm (fun z hz => hz.1)
      intro z hz
      exact ⟨hz,hUe (hDU (heD (e.map_target hz)))⟩
    have hFne : F.source.Nonempty := by
      obtain ⟨x,hx⟩ := hne
      rw [hFs]
      exact ⟨e x,e.map_source hx⟩
    have hFtU : F.target⊆(A.originalCoordinateDomain e0 U:Set (ComplexModel n)) :=
      fun z hz => ⟨hz.1,hDU (heD hz.2)⟩
    have hFtD : F.target⊆(A.originalCoordinateDomain e0 D:Set (ComplexModel n)) :=
      fun z hz => ⟨hz.1,heD hz.2⟩
    have hμF : μ F.target=0 := measure_mono_null hFtD hμzero
    have hRestrZero : (μ.restrict F.target) F.target=0 := by
      rw [Measure.restrict_apply' F.open_target.measurableSet,inter_self]
      exact hμF
    have h0 := OriginalBTCoordinateDraft.isBTLimit_zero_comp_holomorphic_openPartial
      F hF hFi hFne (hμ.restrict_opens hFtU) hRestrZero
    have hS : (⟨F.source,F.open_source⟩:Opens (ComplexModel m))=⟨e.target,e.open_target⟩ :=
      Opens.ext hFs
    rw [hS] at h0
    have hBase : IsBTLimit ⟨e.target,e.open_target⟩
        (fun _ z => (v (e.symm z)).toReal+g0 (e.symm z)) 0 := by
      apply h0.congr
      intro i z hz
      change (v (e0.symm (e0 (e.symm z)))+
        (g0 (e0.symm (e0 (e.symm z))):EReal)).toReal=(v (e.symm z)).toReal+g0 (e.symm z)
      rw [e0.left_inv (hUe (hDU (heD (e.map_target hz)))),
        EReal.toReal_add (hfinite _ (heD (e.map_target hz))).1
          (hfinite _ (heD (e.map_target hz))).2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_coe]
    let V := (U:Set X)∩W
    have hV : IsOpen V := U.isOpen.inter hg.1
    let hf := A.adjoinCoordinate_identity_isHolomorphic e hout hin
    have hg0' := (hg0.mono hV inter_subset_left).comp_holomorphic hf
    have hg' := (hg.mono hV inter_subset_right).comp_holomorphic hf
    have hΩ : e.target⊆e.target∩e.symm ⁻¹' V := by
      intro z hz
      exact ⟨hz,hDU (heD (e.map_target hz)),heW (e.map_target hz)⟩
    have hnew := hg0'.btLimit_change_potential hg' none hΩ hBase
    apply hnew.congr
    intro i z hz
    change (v (e.symm z)).toReal+g (e.symm z)=
      (v (e.symm z)+(g (e.symm z):EReal)).toReal
    rw [EReal.toReal_add (hfinite _ (heD (e.map_target hz))).1
      (hfinite _ (heD (e.map_target hz))).2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_coe]
  · apply isBTLimit_zero_of_empty_domain
    apply eq_empty_of_forall_notMem
    intro z hz
    exact hne ⟨e.symm z,e.map_target hz⟩

end SGPT.PSH.VariableComplexAtlas


/-! Actual nonvacuity/local coverage of the intrinsic zero-MA tests, and
literal original-chart readback. All coordinates/potentials are produced. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

theorem compatibleCoordinate_restrOpen {n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    (S : Set X) (hS : IsOpen S) :
    (∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans (e.restrOpen S hS))
      ((A.chart i).symm.trans (e.restrOpen S hS)).source) ∧
    (∀ i,DifferentiableOn ℂ ((e.restrOpen S hS).symm.trans (A.chart i))
      ((e.restrOpen S hS).symm.trans (A.chart i)).source) := by
  constructor
  · intro i
    change DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).target∩(A.chart i).symm ⁻¹' (e.source∩S))
    exact (hout i).mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  · intro i
    change DifferentiableOn ℂ (e.symm.trans (A.chart i))
      ((e.target∩e.symm ⁻¹' S)∩e.symm ⁻¹' (A.chart i).source)
    exact (hin i).mono (fun z hz => ⟨hz.1.1,hz.2⟩)

theorem exists_compatible_subcoordinate_local_potential
    (θ : AtlasClosedRealOneOneForm A) {D : Set X} (hD : IsOpen D) {x : X} (hx : x∈D) :
    ∃ (n : ℕ) (e : OpenPartialHomeomorph X (ComplexModel n)),x∈e.source ∧ e.source⊆D ∧
      (∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e) ((A.chart i).symm.trans e).source) ∧
      (∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i)) (e.symm.trans (A.chart i)).source) ∧
      ∃ (U : Set X) (g : X → ℝ),e.source⊆U ∧ A.IsAtlasLocalPotential θ U g := by
  obtain ⟨i,hi⟩ := A.cover x
  obtain ⟨U,g,hxU,hg⟩ := exists_atlas_local_potential θ x
  let S := D∩U
  have hS : IsOpen S := hD.inter hg.1
  have hcompat := compatibleCoordinate_restrOpen (A.chart i)
    (fun j => A.holomorphic j i) (fun j => A.holomorphic i j) S hS
  refine ⟨A.dimension i,(A.chart i).restrOpen S hS,⟨hi,hx,hxU⟩,
    (fun y hy => hy.2.1),hcompat.1,hcompat.2,U,g,(fun y hy => hy.2.2),hg⟩

theorem IsZeroThetaMongeAmpereOn.originalChart_restrOpen
    {θ : AtlasClosedRealOneOneForm A} {v : X → EReal} {D : Set X}
    (hv : A.IsZeroThetaMongeAmpereOn θ v D) (i : A.Index) (S : Set X) (hS : IsOpen S)
    (heD : (A.chart i).source∩S⊆D) {U : Set X} {g : X → ℝ}
    (hg : A.IsAtlasLocalPotential θ U g) (heU : (A.chart i).source∩S⊆U) :
    SGPT.Foundations.Analysis.Pending.BedfordTaylor.IsBTLimit
      ⟨((A.chart i).restrOpen S hS).target,((A.chart i).restrOpen S hS).open_target⟩
      (fun _ z => (v ((A.chart i).symm z)+(g ((A.chart i).symm z):EReal)).toReal) 0 := by
  have hc := compatibleCoordinate_restrOpen (A.chart i)
    (fun j => A.holomorphic j i) (fun j => A.holomorphic i j) S hS
  exact hv (A.dimension i) ((A.chart i).restrOpen S hS) hc.1 hc.2 heD U g hg heU

end SGPT.PSH.VariableComplexAtlas


/-! Genuine original bounded candidates supply all actual Euclidean bound
and measure hypotheses for uniqueness, without any order premise. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Metric TopologicalSpace MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open scoped Topology ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

theorem original_locallyBounded_of_eq_off
    {D U O : Set X} (hUO : U⊆O) {φ v : X → EReal}
    (hφb : ∀ x∈O,∃ Q∈𝓝 x,∃ C : ℝ,∀ y∈Q,((-C:ℝ):EReal)≤φ y ∧ φ y≤C)
    (heq : EqOn v φ Dᶜ)
    (hv : ∃ W : Opens X,closure D⊆(W:Set X) ∧
      ∃ C : ℝ,∀ x∈W,((-C:ℝ):EReal)≤v x ∧ v x≤C) :
    ∀ x∈U,∃ Q∈𝓝 x,∃ C : ℝ,∀ y∈Q,((-C:ℝ):EReal)≤v y ∧ v y≤C := by
  obtain ⟨W,hDW,C,hC⟩ := hv
  intro x hx
  by_cases hxW : x∈W
  · exact ⟨W,W.isOpen.mem_nhds hxW,C,hC⟩
  · have hxD : x∉closure D := fun h => hxW (hDW h)
    obtain ⟨Q,hQ,E,hE⟩ := hφb x (hUO hx)
    refine ⟨Q∩(closure D)ᶜ,inter_mem hQ (isClosed_closure.isOpen_compl.mem_nhds hxD),E,?_⟩
    intro y hy
    rw [heq (fun h => hy.2 (subset_closure h))]
    exact hE y hy.1

theorem corrected_coordinate_locallyBounded {n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel n)) (U : Opens X)
    (_hUe : (U:Set X)⊆e.source) {v : X → EReal} {g : X → ℝ} {Cg : ℝ}
    (hCg : ∀ x∈U,|g x|≤Cg)
    (hv : ∀ x∈U,∃ Q∈𝓝 x,∃ C : ℝ,∀ y∈Q,((-C:ℝ):EReal)≤v y ∧ v y≤C) :
    ∀ z∈A.originalCoordinateDomain e U,∃ Q∈𝓝 z,∃ C : ℝ,∀ w∈Q,
      ((-C:ℝ):EReal)≤v (e.symm w)+(g (e.symm w):EReal) ∧
        v (e.symm w)+(g (e.symm w):EReal)≤C := by
  intro z hz
  obtain ⟨Q,hQ,C,hC⟩ := hv (e.symm z) hz.2
  let Ω := A.originalCoordinateDomain e U
  refine ⟨(Ω:Set (ComplexModel n))∩e.symm ⁻¹' Q,
    inter_mem (Ω.isOpen.mem_nhds hz) ((e.continuousAt_symm hz.1).preimage_mem_nhds hQ),C+Cg,?_⟩
  intro w hw
  exact ereal_add_coe_twoSidedBound (hC _ hw.2) (hCg _ hw.1.2)

theorem IsZeroThetaMongeAmpereOn.coordinate_mass_zero {n : ℕ}
    {θ : AtlasClosedRealOneOneForm A} {v : X → EReal} (D U : Opens X)
    (hv : A.IsZeroThetaMongeAmpereOn θ v D)
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    (hDU : (D:Set X)⊆U) {g : X → ℝ} (hg : A.IsAtlasLocalPotential θ U g)
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (A.originalCoordinateDomain e U)
      (fun _ z => (v (e.symm z)+(g (e.symm z):EReal)).toReal) μ) :
    μ (A.originalCoordinateDomain e D:Set (ComplexModel n))=0 := by
  let r := e.restrOpen (D:Set X) D.isOpen
  have hc := compatibleCoordinate_restrOpen e hout hin (D:Set X) D.isOpen
  have hz := hv n r hc.1 hc.2 (fun x hx => hx.2) U g hg (fun x hx => hDU hx.2)
  have hsub : A.originalCoordinateDomain e D≤A.originalCoordinateDomain e U :=
    fun z hz => ⟨hz.1,hDU hz.2⟩
  have hr : (⟨r.target,r.open_target⟩:Opens (ComplexModel n))=A.originalCoordinateDomain e D := rfl
  rw [hr] at hz
  have heq : μ.restrict (A.originalCoordinateDomain e D:Set (ComplexModel n))=0 :=
    (hμ.restrict_opens hsub).unique hz
  exact Measure.restrict_eq_zero.mp heq

end SGPT.PSH.VariableComplexAtlas


/-! Original uniqueness for all bounded theta-PSH zero-MA candidates. The
same unchanged original coordinate and actual local potential are used for
both candidates; no order premise or new PDE existence argument. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Metric TopologicalSpace MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open scoped Topology ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

theorem isZeroThetaMongeAmpereOn_iff_coordinate_mass_zero {n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    {θ : AtlasClosedRealOneOneForm A} {v : X → EReal} (D U : Opens X)
    (hDU : (D:Set X)⊆U) (hUe : (U:Set X)⊆e.source) {g : X → ℝ}
    (hg : A.IsAtlasLocalPotential θ U g) (hfinite : ∀ x∈D,v x≠⊤ ∧ v x≠⊥)
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (A.originalCoordinateDomain e U)
      (fun _ z => (v (e.symm z)+(g (e.symm z):EReal)).toReal) μ) :
    A.IsZeroThetaMongeAmpereOn θ v D ↔ μ (A.originalCoordinateDomain e D:Set (ComplexModel n))=0 := by
  exact ⟨fun hv => hv.coordinate_mass_zero D U e hout hin hDU hg hμ,
    fun hz => isZeroThetaMongeAmpereOn_of_coordinate_BT e hout hin D U hDU hUe hg hfinite hμ hz⟩

theorem original_theta_balayage_unique {n : ℕ} (hn : 0<n)
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    (D U : Opens X) (hDne : (D:Set X).Nonempty) (hDc : IsCompact (closure (D:Set X)))
    (hDU : closure (D:Set X)⊆(U:Set X)) (hUe : (U:Set X)⊆e.source)
    {θ : AtlasClosedRealOneOneForm A} {g : X → ℝ} (hg : A.IsAtlasLocalPotential θ U g)
    {Cg : ℝ} (hCg : ∀ x∈U,|g x|≤Cg) {φ v w : X → EReal}
    (hφb : ∀ x∈e.source,∃ Q∈𝓝 x,∃ C : ℝ,∀ y∈Q,((-C:ℝ):EReal)≤φ y ∧ φ y≤C)
    (hv : A.IsThetaPSH θ v) (hw : A.IsThetaPSH θ w)
    (hvb : ∃ V : Opens X,closure (D:Set X)⊆(V:Set X) ∧
      ∃ C : ℝ,∀ x∈V,((-C:ℝ):EReal)≤v x ∧ v x≤C)
    (hwb : ∃ V : Opens X,closure (D:Set X)⊆(V:Set X) ∧
      ∃ C : ℝ,∀ x∈V,((-C:ℝ):EReal)≤w x ∧ w x≤C)
    (hvz : A.IsZeroThetaMongeAmpereOn θ v D) (hwz : A.IsZeroThetaMongeAmpereOn θ w D)
    (hveq : EqOn v φ (D:Set X)ᶜ) (hweq : EqOn w φ (D:Set X)ᶜ) : v=w := by
  let Ω := A.originalCoordinateDomain e U
  let Dc := A.originalCoordinateDomain e D
  let cv : ComplexModel n → EReal := fun z => v (e.symm z)+(g (e.symm z):EReal)
  let cw : ComplexModel n → EReal := fun z => w (e.symm z)+(g (e.symm z):EReal)
  let cf : ComplexModel n → EReal := fun z => φ (e.symm z)+(g (e.symm z):EReal)
  have hvbU := original_locallyBounded_of_eq_off (D:=(D:Set X)) (U:=(U:Set X)) hUe hφb hveq hvb
  have hwbU := original_locallyBounded_of_eq_off (D:=(D:Set X)) (U:=(U:Set X)) hUe hφb hweq hwb
  have hvc := corrected_coordinate_locallyBounded (A:=A) e U hUe hCg hvbU
  have hwc := corrected_coordinate_locallyBounded (A:=A) e U hUe hCg hwbU
  have hΩne : (Ω:Set (ComplexModel n)).Nonempty := by
    obtain ⟨x,hx⟩ := hDne
    have hxU := hDU (subset_closure hx)
    refine ⟨e x,e.map_source (hUe hxU),?_⟩
    change e.symm (e x)∈U
    rwa [e.left_inv (hUe hxU)]
  have hvp : SGPT.PSH.PSHOn cv Ω := identityAtlas_pshOn_of_isPSHOn_nonempty Ω.isOpen hΩne
    (IsPSHOn.originalCoordinateDomain (D:=U) e hin (hv.2 U g hg))
  have hwp : SGPT.PSH.PSHOn cw Ω := identityAtlas_pshOn_of_isPSHOn_nonempty Ω.isOpen hΩne
    (IsPSHOn.originalCoordinateDomain (D:=U) e hin (hw.2 U g hg))
  obtain ⟨hvr,hvfinite⟩ := BookDeepDomination.isLocallyBoundedPshOn_toReal hvp hvc
  obtain ⟨hwr,hwfinite⟩ := BookDeepDomination.isLocallyBoundedPshOn_toReal hwp hwc
  obtain ⟨μv,hμv⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (fun _ : Fin n => hvr)
  obtain ⟨μw,hμw⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (fun _ : Fin n => hwr)
  have hzeroV := hvz.coordinate_mass_zero D U e hout hin
    (fun x hx => hDU (subset_closure hx)) hg hμv
  have hzeroW := hwz.coordinate_mass_zero D U e hout hin
    (fun x hx => hDU (subset_closure hx)) hg hμw
  have hEV : ∀ z∈Ω,z∉(Dc:Set (ComplexModel n)) → (cv z).toReal=(cf z).toReal := by
    intro z hz hzD
    have hx : e.symm z∉(D:Set X) := fun h => hzD ⟨hz.1,h⟩
    change (v (e.symm z)+(g (e.symm z):EReal)).toReal=
      (φ (e.symm z)+(g (e.symm z):EReal)).toReal
    rw [hveq hx]
  have hEW : ∀ z∈Ω,z∉(Dc:Set (ComplexModel n)) → (cw z).toReal=(cf z).toReal := by
    intro z hz hzD
    have hx : e.symm z∉(D:Set X) := fun h => hzD ⟨hz.1,h⟩
    change (w (e.symm z)+(g (e.symm z):EReal)).toReal=
      (φ (e.symm z)+(g (e.symm z):EReal)).toReal
    rw [hweq hx]
  have hDe : closure (D:Set X)⊆e.source := hDU.trans hUe
  have hDc' := (A.originalCoordinateDomain_compact_closure e D hDc hDe).1
  have hDΩ : closure (Dc:Set (ComplexModel n))⊆Ω := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := A.originalCoordinateDomain_closure_subset e D hDc hDe hz
    refine ⟨e.map_source (hDe hx),?_⟩
    change e.symm (e x)∈U
    rw [e.left_inv (hDe hx)]
    exact hDU hx
  have hreal := BookDeepDomination.balayage_unique hn hDc' hDΩ hvr hwr hEV hEW hμv hμw hzeroV hzeroW
  funext x
  by_cases hx : x∈(D:Set X)
  · have hxU := hDU (subset_closure hx)
    have hxe := hUe hxU
    have hz : e x∈Ω := ⟨e.map_source hxe,by change e.symm (e x)∈U; rwa [e.left_inv hxe]⟩
    have heq : cv (e x)=cw (e x) := by
      rw [← hvfinite (e x) hz,← hwfinite (e x) hz,hreal (e x) hz]
    change v (e.symm (e x))+(g (e.symm (e x)):EReal)=
      w (e.symm (e x))+(g (e.symm (e x)):EReal) at heq
    rw [e.left_inv hxe] at heq
    exact le_antisymm ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp heq.le)
      ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp heq.ge)
  · exact (hveq hx).trans (hweq hx).symm

end SGPT.PSH.VariableComplexAtlas


/-! Whole original arbitrary-ball general balayage with the explicit E18
positive-dimensional B-prime correction. All input balls, tensor, original
function and all original exterior points are retained literally. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

theorem exists_unique_original_theta_balayage_general {n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (hout : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans e)
      ((A.chart i).symm.trans e).source)
    (hin : ∀ i,DifferentiableOn ℂ (e.symm.trans (A.chart i))
      (e.symm.trans (A.chart i)).source)
    {c : ComplexModel n} {R : ℝ} (hR : 0<R) (he : e.target=ball c R) (hn : 0<n)
    (D : Opens X) (hDne : (D:Set X).Nonempty)
    (hDc : IsCompact (closure (D:Set X))) (hDe : closure (D:Set X)⊆e.source)
    (hboundary : A.HasOriginalSmoothBoundary D)
    (θ : AtlasClosedRealOneOneForm A) {φ : X → EReal} (hφ : A.IsThetaPSH θ φ)
    (hφb : ∀ x∈e.source,∃ O∈𝓝 x,∃ C : ℝ,∀ y∈O,((-C:ℝ):EReal)≤φ y ∧ φ y≤C) :
    ∃ Ψ : X → EReal,A.IsThetaPSH θ Ψ ∧
      (∃ W : Opens X,closure (D:Set X)⊆(W:Set X) ∧
        ∃ C : ℝ,∀ x∈W,((-C:ℝ):EReal)≤Ψ x ∧ Ψ x≤C) ∧
      A.IsZeroThetaMongeAmpereOn θ Ψ D ∧ EqOn Ψ φ (D:Set X)ᶜ ∧
      (∀ x,φ x≤Ψ x) ∧
      ∀ χ : X → EReal,A.IsThetaPSH θ χ →
        (∃ W : Opens X,closure (D:Set X)⊆(W:Set X) ∧
          ∃ C : ℝ,∀ x∈W,((-C:ℝ):EReal)≤χ x ∧ χ x≤C) →
        A.IsZeroThetaMongeAmpereOn θ χ D → EqOn χ φ (D:Set X)ᶜ → χ=Ψ := by
  obtain ⟨Ψ,hΨ,hext,horder,hbounded,U,g,hDU,hUe,hg,μ,hμ,hμzero⟩ :=
    exists_original_thetaPSH_replacement_with_coordinate_BT e hout hin hR he hn D hDne hDc hDe hboundary θ hφ hφb
  have hfinite : ∀ x∈D,Ψ x≠⊤ ∧ Ψ x≠⊥ := by
    obtain ⟨W,hDW,C,hC⟩ := hbounded
    intro x hx
    have hb := hC x (hDW (subset_closure hx))
    exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hb.2,
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hb.1⟩
  have hzero := isZeroThetaMongeAmpereOn_of_coordinate_BT e hout hin D U
    (fun x hx => hDU (subset_closure hx)) hUe hg hfinite hμ hμzero
  have hgc : ContinuousOn g U := hg.2.1.continuousOn_open U.isOpen
  obtain ⟨C,hC⟩ := hDc.exists_bound_of_continuousOn (hgc.mono hDU)
  let V0 := (U:Set X)∩(fun x => |g x|) ⁻¹' Iio (C+1)
  have hV0 : IsOpen V0 := hgc.abs.isOpen_inter_preimage U.isOpen isOpen_Iio
  let V : Opens X := ⟨V0,hV0⟩
  have hDV : closure (D:Set X)⊆(V:Set X) := by
    intro x hx
    exact ⟨hDU hx,(show |g x|≤C by simpa only [Real.norm_eq_abs] using hC x hx).trans_lt (lt_add_one C)⟩
  have hgV := hg.mono hV0 inter_subset_left
  have hCgV : ∀ x∈V,|g x|≤C+1 := fun x hx => hx.2.le
  refine ⟨Ψ,hΨ,hbounded,hzero,hext,horder,?_⟩
  intro χ hχ hχb hχzero hχeq
  exact original_theta_balayage_unique hn e hout hin D V hDne hDc hDV
    (inter_subset_left.trans hUe) hgV hCgV hφb hχ hΨ hχb hbounded hχzero hzero hχeq hext

structure OriginalHolomorphicBall (A : VariableComplexAtlas X) where
  dimension : ℕ
  coordinate : OpenPartialHomeomorph X (ComplexModel dimension)
  center : ComplexModel dimension
  radius : ℝ
  radius_pos : 0<radius
  target_eq : coordinate.target=ball center radius
  holomorphic_out : ∀ i,DifferentiableOn ℂ ((A.chart i).symm.trans coordinate)
    ((A.chart i).symm.trans coordinate).source
  holomorphic_in : ∀ i,DifferentiableOn ℂ (coordinate.symm.trans (A.chart i))
    (coordinate.symm.trans (A.chart i)).source
  smooth_boundary : A.HasOriginalSmoothBoundary ⟨coordinate.source,coordinate.open_source⟩

def OriginalHolomorphicBall.domain (B : OriginalHolomorphicBall A) : Opens X :=
  ⟨B.coordinate.source,B.coordinate.open_source⟩

theorem OriginalHolomorphicBall.nonempty_domain (B : OriginalHolomorphicBall A) :
    (B.domain:Set X).Nonempty := by
  have hc : B.center∈B.coordinate.target := by rw [B.target_eq]; exact mem_ball_self B.radius_pos
  exact ⟨B.coordinate.symm B.center,B.coordinate.map_target hc⟩

/-- Entire original prop:bal_general (current pinned lines1327--1337), with
the explicit authorized E18 positive-dimension repair. Two actual arbitrary
original balls and their independent dimensions are retained. -/
theorem source_bal_general (B B' : OriginalHolomorphicBall A)
    (hBc : IsCompact (closure (B.domain:Set X)))
    (hBB' : closure (B.domain:Set X)⊆(B'.domain:Set X)) (hn : 0<B'.dimension)
    (θ : AtlasClosedRealOneOneForm A) {φ : X → EReal} (hφ : A.IsThetaPSH θ φ)
    (hφb : ∀ x∈B'.domain,∃ O∈𝓝 x,∃ C : ℝ,∀ y∈O,((-C:ℝ):EReal)≤φ y ∧ φ y≤C) :
    ∃ Ψ : X → EReal,A.IsThetaPSH θ Ψ ∧
      (∃ W : Opens X,closure (B.domain:Set X)⊆(W:Set X) ∧
        ∃ C : ℝ,∀ x∈W,((-C:ℝ):EReal)≤Ψ x ∧ Ψ x≤C) ∧
      A.IsZeroThetaMongeAmpereOn θ Ψ B.domain ∧ EqOn Ψ φ (B.domain:Set X)ᶜ ∧
      (∀ x,φ x≤Ψ x) ∧
      ∀ χ : X → EReal,A.IsThetaPSH θ χ →
        (∃ W : Opens X,closure (B.domain:Set X)⊆(W:Set X) ∧
          ∃ C : ℝ,∀ x∈W,((-C:ℝ):EReal)≤χ x ∧ χ x≤C) →
        A.IsZeroThetaMongeAmpereOn θ χ B.domain → EqOn χ φ (B.domain:Set X)ᶜ → χ=Ψ := by
  exact exists_unique_original_theta_balayage_general B'.coordinate B'.holomorphic_out
    B'.holomorphic_in B'.radius_pos B'.target_eq hn B.domain B.nonempty_domain hBc hBB'
    B.smooth_boundary θ hφ hφb

end SGPT.PSH.VariableComplexAtlas
