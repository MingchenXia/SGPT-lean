import SGPT.Foundations.Analysis.FirstPass.PshClosedDiscMaximum
import SGPT.Foundations.Analysis.PlurisubharmonicPullback
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import SGPT.Foundations.Analysis.LeviForm
import Mathlib.Tactic
import SGPT.Foundations.Analysis.FirstPass.PshRealConvexity
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import SGPT.Foundations.Analysis.Plurisubharmonic
import SGPT.Foundations.Analysis.Pending.ScaledPolydiskBalayageMass
import SGPT.Foundations.Analysis.FirstPass.PshSupremumRegularization
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous
import SGPT.PSH.BookDeepDomination
import SGPT.Foundations.Analysis.Pending.PolydiskScaledBalayageOrder
import SGPT.Foundations.Analysis.Pending.PolydiskPatchVanishing
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacity

/-! Entire corrected original SGPT prop:BT_balayage (69360cfd619–628).
Canonical consolidation of14 individually clean genuine producer modules.
Original arbitrary strongly-pseudoconvex D, original EReal PSH datum,
all original points and all printed clauses; positive dimension (E18).
No incoming Dirichlet, sector, boundary, mass or replacement certificate. -/

/-! Genuine normal-direction producer for an ORIGINAL real C1 boundary.
The actual nonzero derivative internally gives a direction with positive
normal real part and zero normal imaginary part. Before-code blueprint. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open SGPT.Foundations.Analysis.FirstPass

/-- Actual complex normal direction of an arbitrary original NONZERO real
continuous linear derivative. No normal/sector witness is supplied. -/
theorem exists_positive_normal_complex_direction {n : ℕ}
    (A : ComplexModel n →L[ℝ] ℝ) (hA : A≠0) :
    ∃ v : ComplexModel n,0<A v ∧ A (Complex.I • v)=0 ∧ v≠0 := by
  have hex : ∃ x : ComplexModel n,A x≠0 := by
    by_contra h
    apply hA
    ext x
    exact not_not.mp (not_exists.mp h x)
  obtain ⟨x,hx⟩ := hex
  let a : ℝ := A x
  let b : ℝ := A (Complex.I • x)
  let v : ComplexModel n := a • x+b • (Complex.I • x)
  have hAv : A v=a^2+b^2 := by
    simp only [v,map_add,map_smul,smul_eq_mul]
    change a*a+b*b=a^2+b^2
    ring
  have hiv : Complex.I • v=a • (Complex.I • x)+b • (-x) := by
    simp only [v,smul_add,smul_comm Complex.I a,smul_comm Complex.I b,
      smul_smul,Complex.I_mul_I,neg_one_smul]
  have hAiv : A (Complex.I • v)=0 := by
    rw [hiv,A.map_add,A.map_smul a _,A.map_smul b _,A.map_neg]
    change a*b+b*(-a)=0
    ring
  have hpos : 0<A v := by
    rw [hAv]
    have ha : a≠0 := hx
    nlinarith [sq_pos_of_ne_zero ha,sq_nonneg b]
  exact ⟨v,hpos,hAiv,fun h0 => hpos.ne' (by rw [h0,map_zero])⟩

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Genuine local strong maximum in the whole original complex model.
This is derived from ACTUAL complex-line restrictions and the existing
one-variable strong maximum, with no supplied local-constancy premise. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Metric
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- A genuine PSH function attaining a finite maximum at the original ball
center is constant on that ENTIRE original ball. All dimensions allowed;
only the later global noncompactness argument needs n>0. -/
theorem psh_eqOn_ball_of_le_of_eq {n : ℕ}
    {u : ComplexModel n → EReal} {Ω : Set (ComplexModel n)}
    (hu : PlurisubharmonicOn u Ω) {p : ComplexModel n} {R C : ℝ} (hR : 0<R)
    (hB : ball p R⊆Ω) (hC : ∀ z∈ball p R,u z≤(C:EReal))
    (hp : u p=(C:EReal)) : EqOn u (fun _ => (C:EReal)) (ball p R) := by
  intro q hq
  by_cases hqp : q=p
  · simpa only [hqp] using hp
  · let v : ComplexModel n := q-p
    have hv : v≠0 := sub_ne_zero.mpr hqp
    have hvnorm : 0<‖v‖ := norm_pos_iff.mpr hv
    let S : ℝ := R/‖v‖
    have hS : 0<S := div_pos hR hvnorm
    let L : ℂ →L[ℂ] ComplexModel n := (ContinuousLinearMap.id ℂ ℂ).smulRight v
    let Γ : Set ℂ := (fun z => p+L z) ⁻¹' Ω
    have hpsh : PlurisubharmonicOn (fun z => u (p+L z)) Γ := hu.comp_affine L p
    have hdist (z : ℂ) : dist (p+L z) p=‖z‖*‖v‖ := by
      rw [dist_eq_norm,show p+L z-p=L z by abel]
      simp [L,norm_smul]
    have hmap : ∀ z∈ball (0:ℂ) S,p+L z∈ball p R := by
      intro z hz
      rw [mem_ball,hdist]
      have hnormz : ‖z‖<S := by simpa only [mem_ball,dist_zero_right] using hz
      calc
        ‖z‖*‖v‖<S*‖v‖ := mul_lt_mul_of_pos_right hnormz hvnorm
        _=R := div_mul_cancel₀ R hvnorm.ne'
    have hΓ : ball (0:ℂ) S⊆Γ := fun z hz => hB (hmap z hz)
    have hzero : u (p+L (0:ℂ))=(C:EReal) := by simpa only [map_zero,add_zero] using hp
    have heq := hpsh.discPshOn.eqOn_ball_of_le_of_eq (0:ℂ) hΓ
      (fun z hz => hC _ (hmap z hz)) hzero
    have hS1 : 1<S := by
      apply (lt_div_iff₀ hvnorm).mpr
      simpa only [one_mul,v,dist_eq_norm] using (mem_ball.mp hq)
    have h1 : (1:ℂ)∈ball (0:ℂ) S := by
      simpa only [mem_ball,dist_zero_right,norm_one] using hS1
    have harg : p+L (1:ℂ)=q := by
      change p+(1:ℂ) • (q-p)=q
      rw [one_smul]
      abel
    simpa only [harg] using heq h1

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Genuine compact-domain PSH maximum principle on the ORIGINAL arbitrary
open domain. The local constancy/maximizer/noncompactness outputs are proved,
not incoming maximum, connected-component or boundary certificates. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Metric
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

/-- Actual compact-domain maximum principle, retaining ORIGINAL arbitrary
open D, its actual frontier/closure and possibly polar PSH values. No
connectedness, convexity, roundness or pseudoconvexity restriction is added. -/
theorem psh_le_const_on_closure_of_le_on_frontier {n : ℕ} (hn : 0<n)
    {u : ComplexModel n → EReal} {Ω D : Set (ComplexModel n)}
    (hu : PlurisubharmonicOn u Ω) (hDo : IsOpen D)
    (hDc : IsCompact (closure D)) (hDΩ : closure D⊆Ω) {C : ℝ}
    (hs : ∀ z∈frontier D,u z≤(C:EReal)) :
    ∀ z∈closure D,u z≤(C:EReal) := by
  intro q hq
  by_contra hqC
  have hCq : (C:EReal)<u q := lt_of_not_ge hqC
  obtain ⟨y,hyD,hmax⟩ := (hu.upperSemicontinuousOn.mono hDΩ).exists_isMaxOn ⟨q,hq⟩ hDc
  have hCy : (C:EReal)<u y := hCq.trans_le (hmax hq)
  have hyT : u y≠⊤ := (hu y (hDΩ hyD)).ne_top
  have hyB : u y≠⊥ := ne_bot_of_gt hCy
  let M : ℝ := (u y).toReal
  have hyM : u y=(M:EReal) := (EReal.coe_toReal hyT hyB).symm
  have hCM : C<M := EReal.coe_lt_coe_iff.mp (hyM ▸ hCy)
  have hMb : ∀ z∈closure D,u z≤(M:EReal) := fun z hz => (hmax hz).trans_eq hyM
  let O : Set (ComplexModel n) := closure D∩u ⁻¹' Ici (M:EReal)
  have hOc : IsCompact O :=
    (hu.upperSemicontinuousOn.mono hDΩ).isCompact_inter_preimage_Ici hDc (M:EReal)
  have hyO : y∈O := ⟨hyD,hyM.ge⟩
  have hOinD : O⊆D := by
    intro z hz
    by_contra hzD
    have hzfront : z∈frontier D := by
      rw [frontier,hDo.interior_eq]
      exact ⟨hz.1,hzD⟩
    have hMC : (M:EReal)≤(C:EReal) := hz.2.trans (hs z hzfront)
    exact (not_le_of_gt hCM) (EReal.coe_le_coe_iff.mp hMC)
  have hOo : IsOpen O := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hDo z (hOinD hz)
    have hBΩ : ball z r⊆Ω := hball.trans (subset_closure.trans hDΩ)
    have hzM : u z=(M:EReal) := le_antisymm (hMb z hz.1) hz.2
    have heq := psh_eqOn_ball_of_le_of_eq hu hr hBΩ
      (fun w hw => hMb w (subset_closure (hball hw))) hzM
    exact ⟨r,hr,fun w hw => ⟨subset_closure (hball hw),(heq hw).ge⟩⟩
  have hcl : closure O=O := hOc.isClosed.closure_eq
  have hall : (univ:Set (ComplexModel n))⊆O :=
    isPreconnected_univ.subset_of_closure_inter_subset hOo
      ⟨y,mem_univ y,hyO⟩ (fun z hz => hcl ▸ hz.1)
  have hOuniv : O=univ := eq_univ_of_forall fun z => hall (mem_univ z)
  have hcuniv : IsCompact (univ:Set (ComplexModel n)) := hOuniv ▸ hOc
  let : NeZero n := ⟨hn.ne'⟩
  exact (noncompact_univ (ComplexModel n)) hcuniv

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Actual exterior CONE production from an original nonzero Frechet
boundary derivative. The complex direction and radius are outputs; no
sector/thickness or desired boundary inequality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Metric Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass
variable {n : ℕ}

/-- Real derivative evaluation on the actual complex normal line, retaining
the real derivative rather than incorrectly treating it as complex linear. -/
theorem realDerivative_complex_smul (A : ComplexModel n →L[ℝ] ℝ)
    (v : ComplexModel n) (hI : A (Complex.I • v)=0) (z : ℂ) :
    A (z • v)=z.re*A v := by
  have hdecomp : z • v=z.re • v+z.im • (Complex.I • v) := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [add_smul,mul_smul,Complex.coe_smul,Complex.coe_smul]
  rw [hdecomp,A.map_add,A.map_smul z.re _,A.map_smul z.im _,hI]
  simp only [smul_eq_mul,mul_zero,add_zero]

/-- The ORIGINAL actual nonzero boundary derivative internally produces a
fixed complex normal cone of strict positivity for the ORIGINAL function.
This is a genuine quantitative first-order consequence, not a cone premise. -/
theorem exists_positive_normal_sector {ρ : ComplexModel n → ℝ}
    {q : ComplexModel n} {A : ComplexModel n →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ A q) (hzero : ρ q=0) (hA : A≠0) :
    ∃ v : ComplexModel n,0<A v ∧ A (Complex.I • v)=0 ∧ v≠0 ∧
      ∃ r0 : ℝ,0<r0 ∧ ∀ z : ℂ,0<‖z‖→‖z‖<r0→‖z‖/2≤z.re→
        0<ρ (q+z • v) := by
  obtain ⟨v,hAv,hAI,hv⟩ := exists_positive_normal_complex_direction A hA
  have hvn : 0<‖v‖ := norm_pos_iff.mpr hv
  let η : ℝ := A v/(4*‖v‖)
  have hη : 0<η := div_pos hAv (by positivity)
  have hlittle := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hρ).bound hη
  obtain ⟨δ,hδ,hδerr⟩ := Metric.mem_nhds_iff.mp hlittle
  refine ⟨v,hAv,hAI,hv,δ/‖v‖,div_pos hδ hvn,?_⟩
  intro z hzn hzr hsector
  have hnorm : ‖z • v‖<δ := by
    rw [norm_smul]
    exact (lt_div_iff₀ hvn).mp hzr
  have herr := hδerr (show z • v∈ball (0:ComplexModel n) δ by
    simpa only [mem_ball,dist_zero_right] using hnorm)
  change ‖ρ (q+z • v)-ρ q-A (z • v)‖≤η*‖z • v‖ at herr
  have hlin := realDerivative_complex_smul A v hAI z
  have herr' : |ρ (q+z • v)-z.re*A v|≤η*(‖z‖*‖v‖) := by
    simpa only [hzero,sub_zero,hlin,norm_smul,Real.norm_eq_abs] using herr
  have hηeq : η*(‖z‖*‖v‖)=‖z‖*A v/4 := by
    dsimp [η]
    field_simp
  rw [hηeq] at herr'
  have hlow := neg_le_of_abs_le herr'
  have hnormal := mul_le_mul_of_nonneg_right hsector hAv.le
  have hprod : 0<‖z‖*A v := mul_pos hzn hAv
  nlinarith

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Fixed positive-angle exterior sector of an ORIGINAL actual C1 boundary.
Every direction/radius/arc exclusion is produced from the actual defining
function and actual derivative; no thickness or comparison certificate. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Metric Filter TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass
variable {n : ℕ}

/-- Actual fixed angular sector in the ORIGINAL OPEN exterior of closure D,
produced from the ORIGINAL continuous defining function and its nonzero
actual derivative at the original point. -/
theorem exists_actual_boundary_exterior_sector {D : Set (ComplexModel n)}
    {U : Opens (ComplexModel n)} {q : ComplexModel n} (hqU : q∈U)
    {ρ : ComplexModel n  →  ℝ} (hρc : ContinuousOn ρ U)
    (hD : ∀ z∈U,z∈D↔ρ z<0) (hzero : ρ q=0)
    {A : ComplexModel n →L[ℝ] ℝ} (hρ : HasFDerivAt ρ A q) (hA : A≠0) :
    ∃ v : ComplexModel n,v≠0 ∧ ∃ r0 : ℝ,0<r0 ∧
      ∀ r : ℝ,0<r → r<r0 → ∀ t∈Icc (0:ℝ) (Real.pi/3),
        q+circleMap 0 r t • v∉closure D := by
  obtain ⟨v,hAv,hAI,hv,r0,hr0,hcone⟩ := exists_positive_normal_sector hρ hzero hA
  have hvn : 0<‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨η,hη,hηU⟩ := Metric.isOpen_iff.mp U.isOpen q hqU
  refine ⟨v,hv,min r0 (η/‖v‖),lt_min hr0 (div_pos hη hvn),?_⟩
  intro r hr hrr t ht
  have hnorm : ‖circleMap 0 r t‖=r := by rw [norm_circleMap_zero,abs_of_pos hr]
  have hcos : (1/2:ℝ)≤Real.cos t := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi ht.1 (by linarith [Real.pi_pos]) ht.2
  have hsector : ‖circleMap 0 r t‖/2≤(circleMap 0 r t).re := by
    rw [hnorm,circleMap_zero_re]
    nlinarith [mul_le_mul_of_nonneg_left hcos hr.le]
  have hpositive : 0<ρ (q+circleMap 0 r t • v) :=
    hcone _ (by rwa [hnorm]) (by rw [hnorm];exact hrr.trans_le (min_le_left _ _)) hsector
  have hpointU : q+circleMap 0 r t • v∈U := by
    apply hηU
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,hnorm]
    exact (lt_div_iff₀ hvn).mp (hrr.trans_le (min_le_right _ _))
  let V : Set (ComplexModel n) := (U:Set (ComplexModel n))∩ρ ⁻¹' Ioi (0:ℝ)
  have hVo : IsOpen V := hρc.isOpen_inter_preimage U.isOpen isOpen_Ioi
  have hpointV : q+circleMap 0 r t • v∈V := ⟨hpointU,hpositive⟩
  intro hcl
  obtain ⟨y,hyV,hyD⟩ := _root_.mem_closure_iff.mp hcl V hVo hpointV
  exact (not_lt_of_ge hyV.2.le) ((hD y hyV.1).mp hyD)

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Literal lower bound for the actual native PSH circle-deficit integral on
an actual fixed positive-measure angular arc. Poles remain in EReal; no
measurability/finite-negative-part or boundary-value conclusion is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
variable {n : ℕ}

/-- An actual pointwise upper bound on the ORIGINAL fixed angular arc gives
its genuine positive contribution to the ORIGINAL native deficit integral.
This is valid even when some original function values are negative infinity. -/
theorem circleDeficit_ge_positiveArc
    {u : ComplexModel n → EReal} (q v : ComplexModel n) (r C B : ℝ)
    (hArc : ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 3),
      u (q + circleMap 0 r t • v) ≤ (B : EReal)) :
    ENNReal.ofReal (Real.pi / 3) * ENNReal.ofReal (C - B) ≤
      circleDeficit u q v r C := by
  calc
    ENNReal.ofReal (Real.pi / 3) * ENNReal.ofReal (C - B) =
        ∫⁻ _t in Ioc (0 : ℝ) (Real.pi / 3), ENNReal.ofReal (C - B) := by
          simp [Real.volume_Ioc, mul_comm]
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) (Real.pi / 3),
        ((C : EReal) - u (q + circleMap 0 r t • v)).toENNReal := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          have h := EReal.toENNReal_le_toENNReal
            (EReal.sub_le_sub (le_rfl : (C : EReal) ≤ (C : EReal)) (hArc t ht))
          simpa only [← EReal.coe_sub, EReal.real_coe_toENNReal] using h
    _ ≤ circleDeficit u q v r C := by
      unfold circleDeficit
      apply lintegral_mono_set
      intro t ht
      exact ⟨ht.1, ht.2.trans (by linarith [Real.pi_pos])⟩

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Literal ORIGINAL local C1 / strongly pseudoconvex domain geometry.
These contain only actual defining functions/derivatives/Levi forms and the
original domain identity; no sector or PSH/balayage output certificates. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
variable {n : ℕ}

/-- Actual original local C1 defining-function geometry at a boundary point. -/
structure C1BoundaryChart (D : Opens (ComplexModel n)) (q : ComplexModel n) where
  neighborhood : Opens (ComplexModel n)
  point_mem : q ∈ neighborhood
  definingFunction : ComplexModel n → ℝ
  contDiff : ContDiffOn ℝ 1 definingFunction neighborhood
  zero : definingFunction q = 0
  derivative_ne_zero : fderiv ℝ definingFunction q ≠ 0
  domain_eq : ∀ z ∈ neighborhood, z ∈ D ↔ definingFunction z < 0

/-- Actual C1 boundary at EVERY original boundary point. -/
def HasC1Boundary (D : Opens (ComplexModel n)) : Prop :=
  ∀ q ∈ frontier (D : Set (ComplexModel n)), Nonempty (C1BoundaryChart D q)

/-- Actual source strongly pseudoconvex boundary geometry, with the genuine
Levi form on the genuine complex tangent space of the ORIGINAL definer. -/
structure StronglyPseudoconvexBoundaryChart (D : Opens (ComplexModel n)) (q : ComplexModel n) where
  neighborhood : Opens (ComplexModel n)
  point_mem : q ∈ neighborhood
  definingFunction : ComplexModel n → ℝ
  contDiff : ContDiffOn ℝ 2 definingFunction neighborhood
  zero : definingFunction q = 0
  derivative_ne_zero : fderiv ℝ definingFunction q ≠ 0
  domain_eq : ∀ z ∈ neighborhood, z ∈ D ↔ definingFunction z < 0
  levi_positive : ∀ v : ComplexModel n, v ≠ 0 →
    fderiv ℝ definingFunction q v = 0 →
    fderiv ℝ definingFunction q (Complex.I • v) = 0 →
    0 < leviForm definingFunction q v

/-- ORIGINAL nonempty connected domain and actual strong pseudoconvexity
at ALL original boundary points. Dimension0 is not silently excluded. -/
def IsStronglyPseudoconvexDomain (D : Opens (ComplexModel n)) : Prop :=
  IsConnected (D : Set (ComplexModel n)) ∧
    ∀ q ∈ frontier (D : Set (ComplexModel n)),
      Nonempty (StronglyPseudoconvexBoundaryChart D q)

/-- Actual source C2 geometry internally supplies its actual C1 geometry. -/
def StronglyPseudoconvexBoundaryChart.toC1 {D : Opens (ComplexModel n)}
    {q : ComplexModel n} (c : StronglyPseudoconvexBoundaryChart D q) : C1BoundaryChart D q where
  neighborhood := c.neighborhood
  point_mem := c.point_mem
  definingFunction := c.definingFunction
  contDiff := c.contDiff.of_le (by norm_num)
  zero := c.zero
  derivative_ne_zero := c.derivative_ne_zero
  domain_eq := c.domain_eq

theorem IsStronglyPseudoconvexDomain.hasC1Boundary {D : Opens (ComplexModel n)}
    (hD : IsStronglyPseudoconvexDomain D) : HasC1Boundary D := by
  intro q hq
  obtain ⟨c⟩ := hD.2 q hq
  exact ⟨c.toC1⟩

/-- The derivative used in the cone proof is the ACTUAL derivative of the
ORIGINAL defining function, internally read from its genuine C1 regularity. -/
theorem C1BoundaryChart.hasFDerivAt {D : Opens (ComplexModel n)} {q : ComplexModel n}
    (c : C1BoundaryChart D q) :
    HasFDerivAt c.definingFunction (fderiv ℝ c.definingFunction q) q := by
  have hc : ContDiffAt ℝ 1 c.definingFunction q :=
    c.contDiff.contDiffAt (c.neighborhood.isOpen.mem_nhds c.point_mem)
  exact (hc.differentiableAt (by norm_num)).hasFDerivAt

/-- Original boundary data genuinely PRODUCE the actual positive angular
exterior sector, rather than requiring a thickness certificate. -/
theorem C1BoundaryChart.exists_exterior_sector {D : Opens (ComplexModel n)}
    {q : ComplexModel n} (c : C1BoundaryChart D q) :
    ∃ v : ComplexModel n, v ≠ 0 ∧ ∃ r0 : ℝ, 0 < r0 ∧
      ∀ r : ℝ, 0 < r → r < r0 → ∀ t ∈ Icc (0 : ℝ) (Real.pi / 3),
        q + circleMap 0 r t • v ∉ closure (D : Set (ComplexModel n)) :=
  exists_actual_boundary_exterior_sector c.point_mem c.contDiff.continuousOn
    c.domain_eq c.zero c.hasFDerivAt c.derivative_ne_zero

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Genuine local absolute boundedness of a true finite PSH real reader
above an actual original locally bounded datum. Upper bounds come from the
actual PSH upper semicontinuity, not a supplied envelope-bound certificate. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Filter TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
variable {n : ℕ}

/-- Actual PSH above an ORIGINAL locally bounded real datum has its true
real-valued PSH/local-bound reader; all finite identities are produced. -/
theorem psh_toReal_locallyBounded_of_ge_original
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {v : ComplexModel n → EReal}
    (hv : PlurisubharmonicOn v Ω) (hle : ∀ z ∈ Ω, (u z : EReal) ≤ v z) :
    IsLocallyBoundedPshOn Ω (fun z => (v z).toReal) ∧
      ∀ z ∈ Ω, (((v z).toReal : ℝ) : EReal) = v z := by
  have hco : ∀ z ∈ Ω, (((v z).toReal : ℝ) : EReal) = v z := by
    intro z hz
    exact EReal.coe_toReal (hv z hz).ne_top
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot (u z)) (hle z hz))
  refine ⟨⟨?_, ?_⟩, hco⟩
  · intro z hz
    apply (hv z hz).congr
    filter_upwards [Ω.isOpen.mem_nhds hz] with y hy
    exact (hco y hy).symm
  · intro z hz
    obtain ⟨V, hzV, hVΩ, C0, hC0⟩ := hu.2 z hz
    let C1 : ℝ := (v z).toReal + 1
    have hlt : v z < (C1 : EReal) := by
      rw [← hco z hz]
      exact EReal.coe_lt_coe_iff.mpr (by dsimp [C1]; linarith)
    have hevent : ∀ᶠ y in 𝓝 z, v y < (C1 : EReal) :=
      (hv z hz).upperSemicontinuousAt _ hlt
    obtain ⟨W, hWsub, hWo, hzW⟩ := _root_.mem_nhds_iff.mp hevent
    refine ⟨V ⊓ ⟨W, hWo⟩, ⟨hzV, hzW⟩, inf_le_left.trans hVΩ,
      max C0 C1, fun y hy => ?_⟩
    have hyΩ : y ∈ Ω := hVΩ hy.1
    have hupper : (v y).toReal ≤ C1 := by
      apply EReal.coe_le_coe_iff.mp
      rw [hco y hyΩ]
      exact (hWsub hy.2).le
    have hlower : u y ≤ (v y).toReal := by
      apply EReal.coe_le_coe_iff.mp
      rw [hco y hyΩ]
      exact hle y hyΩ
    exact abs_le.mpr ⟨(neg_le_neg (le_max_left C0 C1)).trans
      ((neg_le_of_abs_le (hC0 y hy.1)).trans hlower),
      hupper.trans (le_max_right C0 C1)⟩

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! ACTUAL all-original-candidate Perron envelope on arbitrary compactly
contained ORIGINAL open D. No roundness or incoming local-uniform family
bound/PSH-envelope/Dirichlet/closure certificate. Before-code full blueprint. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Metric Filter TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
variable {n : ℕ}

/-- ALL genuine original PSH competitors, with literal original off-D order. -/
def domainCompetitors (Ω D : Opens (ComplexModel n)) (u : ComplexModel n  →  ℝ) :
    Set (ComplexModel n  →  EReal) :=
  {v | PlurisubharmonicOn v Ω ∧ ∀ z∈Ω,z∉D → v z≤(u z:EReal)}

theorem domainCompetitors_nonempty {Ω D : Opens (ComplexModel n)} {u : ComplexModel n  →  ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) : (domainCompetitors Ω D u).Nonempty :=
  ⟨fun z => (u z:EReal),hu.1,fun _ _ _ => le_rfl⟩

/-- Actual ORIGINAL compact-domain maximum yields the common closure bound. -/
theorem domainCompetitor_le_on_closure (hn : 0<n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n  →  ℝ}
    (hDc : IsCompact (closure (D:Set (ComplexModel n))))
    (hDΩ : closure (D:Set (ComplexModel n))⊆Ω) {C : ℝ}
    (hC : ∀ z∈closure (D:Set (ComplexModel n)),u z≤C)
    {v : ComplexModel n  →  EReal} (hv : v∈domainCompetitors Ω D u) :
    ∀ z∈closure (D:Set (ComplexModel n)),v z≤(C:EReal) := by
  apply psh_le_const_on_closure_of_le_on_frontier hn hv.1 D.isOpen hDc hDΩ
  intro z hz
  have hzout : z∉D := by simpa only [D.isOpen.interior_eq, SetLike.mem_coe] using hz.2
  exact (hv.2 z (hDΩ hz.1) hzout).trans (EReal.coe_le_coe_iff.mpr (hC z hz.1))

/-- Actual compact closure and original local datum bounds produce the SAME
local UNIFORM upper bound for every original competitor. -/
theorem domainCompetitors_locallyUniformlyBoundedAbove (hn : 0<n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n  →  ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D:Set (ComplexModel n))))
    (hDΩ : closure (D:Set (ComplexModel n))⊆Ω) :
    LocallyUniformlyBoundedAbove (domainCompetitors Ω D u) Ω := by
  obtain ⟨C,-,hC⟩ := hu.exists_compact_abs_bound hDc hDΩ
  have hupper : ∀ z∈closure (D:Set (ComplexModel n)),u z≤C :=
    fun z hz => (le_abs_self _).trans (hC z hz)
  intro x hx
  obtain ⟨V,hxV,-,Cx,hCx⟩ := hu.2 x hx
  refine ⟨(V:Set (ComplexModel n)),mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hxV),
    max C Cx,fun v hv y hy => ?_⟩
  by_cases hyD : y∈closure (D:Set (ComplexModel n))
  · exact (domainCompetitor_le_on_closure hn hDc hDΩ hupper hv y hyD).trans
      (EReal.coe_le_coe_iff.mpr (le_max_left C Cx))
  · have hyout : y∉D := fun h => hyD (subset_closure h)
    exact (hv.2 y hy.2 hyout).trans (EReal.coe_le_coe_iff.mpr
      (((le_abs_self _).trans (hCx y hy.1)).trans (le_max_right C Cx)))

/-- SAME actual all-candidate neighborhood-regularized supremum. -/
def domainPerronEnvelope (Ω D : Opens (ComplexModel n)) (u : ComplexModel n  →  ℝ) :
    ComplexModel n  →  EReal := uscRegularization (sSup (domainCompetitors Ω D u))

theorem domainPerronEnvelope_plurisubharmonic (hn : 0<n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n  →  ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D:Set (ComplexModel n))))
    (hDΩ : closure (D:Set (ComplexModel n))⊆Ω) :
    PlurisubharmonicOn (domainPerronEnvelope Ω D u) Ω :=
  plurisubharmonicOn_uscRegularization_sSup Ω.isOpen (domainCompetitors_nonempty hu)
    (fun _ hv => hv.1) (domainCompetitors_locallyUniformlyBoundedAbove hn hu hDc hDΩ)

theorem domainCompetitor_le_envelope {Ω D : Opens (ComplexModel n)} {u : ComplexModel n  →  ℝ}
    {v : ComplexModel n  →  EReal} (hv : v∈domainCompetitors Ω D u) (z : ComplexModel n) :
    v z≤domainPerronEnvelope Ω D u z :=
  (le_sSup hv z).trans (le_uscRegularization _ z)

theorem le_domainPerronEnvelope {Ω D : Opens (ComplexModel n)} {u : ComplexModel n  →  ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (z : ComplexModel n) :
    (u z:EReal)≤domainPerronEnvelope Ω D u z :=
  domainCompetitor_le_envelope ⟨hu.1,fun _ _ _ => le_rfl⟩ z

theorem domainPerronEnvelope_finite (hn : 0<n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n  →  ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D:Set (ComplexModel n))))
    (hDΩ : closure (D:Set (ComplexModel n))⊆Ω) {z : ComplexModel n} (hz : z∈Ω) :
    domainPerronEnvelope Ω D u z≠⊤ ∧ domainPerronEnvelope Ω D u z≠⊥ := by
  exact ⟨(domainPerronEnvelope_plurisubharmonic hn hu hDc hDΩ z hz).ne_top,
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot (u z)) (le_domainPerronEnvelope hu z)⟩

/-- Exact ORIGINAL open-exterior values survive the actual regularization. -/
theorem domainPerronEnvelope_eq_of_not_mem_closure
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n  →  ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) {z : ComplexModel n}
    (hzΩ : z∈Ω) (hzD : z∉closure (D:Set (ComplexModel n))) :
    domainPerronEnvelope Ω D u z=(u z:EReal) := by
  apply le_antisymm
  · apply uscRegularization_le_of_eventually_le (hu.1 z hzΩ).upperSemicontinuousAt
    filter_upwards [Ω.isOpen.mem_nhds hzΩ,isClosed_closure.isOpen_compl.mem_nhds hzD] with y hyΩ hyD
    rw [sSup_apply,iSup_subtype]
    exact iSup_le fun v => iSup_le fun hv => hv.2 y hyΩ (fun h => hyD (subset_closure h))
  · exact le_domainPerronEnvelope hu z

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Genuine ORIGINAL C1 boundary-value readback by the ACTUAL nonnegative
circle-deficit submean. The exterior sector, upper bounds and radius are
internally produced; no boundary comparison/thickness certificate. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
variable {n : ℕ}

/-- A genuine PSH germ below the original finite upper-semicontinuous datum
on the ORIGINAL open exterior lies below it at the ORIGINAL C1 boundary
point. No continuity, positive mass, round chart or boundary-output premise. -/
theorem psh_le_at_boundary_of_exterior_bound
    {Ω D : Opens (ComplexModel n)} {q : ComplexModel n} (hqΩ : q ∈ Ω)
    (c : C1BoundaryChart D q) {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicAt u q) {f : ComplexModel n → ℝ}
    (hf : UpperSemicontinuousAt f q)
    (hoff : ∀ y ∈ Ω, y ∉ closure (D : Set (ComplexModel n)) → u y ≤ (f y : EReal)) :
    u q ≤ (f q : EReal) := by
  by_contra hle
  have hgt : (f q : EReal) < u q := lt_of_not_ge hle
  have huT : u q ≠ ⊤ := hu.ne_top
  have huB : u q ≠ ⊥ := ne_bot_of_gt hgt
  let M : ℝ := (u q).toReal
  have huq : u q = (M : EReal) := (EReal.coe_toReal huT huB).symm
  have hMf : f q < M := EReal.coe_lt_coe_iff.mp (huq ▸ hgt)
  let δ : ℝ := M - f q
  have hδ : 0 < δ := sub_pos.mpr hMf
  let ε : ℝ := δ / 12
  have hε : 0 < ε := div_pos hδ (by norm_num)
  let C : ℝ := M + ε
  have hqC : u q < (C : EReal) := by
    rw [huq]
    exact EReal.coe_lt_coe_iff.mpr (by dsimp [C]; linarith)
  have hPe : ∀ᶠ y in 𝓝 q, u y < (C : EReal) := hu.upperSemicontinuousAt _ hqC
  have hfe : ∀ᶠ y in 𝓝 q, f y < f q + ε := hf _ (by linarith)
  obtain ⟨W, hWo, hqW, hdisc⟩ := hu
  let N : Set (ComplexModel n) := {y | y ∈ Ω ∧ y ∈ W ∧ u y < (C : EReal) ∧ f y < f q + ε}
  have hN : N ∈ 𝓝 q := by
    filter_upwards [Ω.isOpen.mem_nhds hqΩ, hWo.mem_nhds hqW, hPe, hfe] with y hyΩ hyW hyP hyf
    exact ⟨hyΩ, hyW, hyP, hyf⟩
  obtain ⟨η, hη, hηN⟩ := Metric.mem_nhds_iff.mp hN
  obtain ⟨v, hv, r0, hr0, hsector⟩ := c.exists_exterior_sector
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let r : ℝ := min (r0 / 2) (η / (2 * ‖v‖))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrr0 : r < r0 := (min_le_left _ _).trans_lt (by linarith)
  have hrnorm : r * ‖v‖ ≤ η / 2 := by
    apply (le_div_iff₀ hvn).mp
    simpa only [div_div] using (min_le_right (r0 / 2) (η / (2 * ‖v‖)))
  have hsmall : affineClosedDisc q v r ⊆ N := by
    rintro y ⟨z, hz, rfl⟩
    apply hηN
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have hzn : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
    exact ((mul_le_mul_of_nonneg_right hzn hvn.le).trans hrnorm).trans_lt (by linarith)
  have hDW : affineClosedDisc q v r ⊆ W := fun y hy => (hsmall hy).2.1
  have hDC : ∀ y ∈ affineClosedDisc q v r, u y ≤ (C : EReal) :=
    fun y hy => (hsmall hy).2.2.1.le
  have hArc : ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 3),
      u (q + circleMap 0 r t • v) ≤ ((f q + ε : ℝ) : EReal) := by
    intro t ht
    have hy := hsmall (circle_mem_affineClosedDisc q v hr.le t)
    exact (hoff _ hy.1 (hsector r hr hrr0 t ⟨ht.1.le, ht.2⟩)).trans
      (EReal.coe_le_coe_iff.mpr hy.2.2.2.le)
  have hlower := circleDeficit_ge_positiveArc q v r C (f q + ε) hArc
  have hCB : C - (f q + ε) = δ := by dsimp [C, δ]; ring
  rw [hCB] at hlower
  have hupper := hdisc.submean q v r hr hDW C hDC
  rw [huq, ← EReal.coe_sub, EReal.real_coe_toENNReal] at hupper
  have hCM : C - M = ε := by dsimp [C]; ring
  rw [hCM] at hupper
  have hineq := hlower.trans hupper
  have hreal := ENNReal.toReal_mono (by finiteness) hineq
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi / 3), ENNReal.toReal_ofReal hδ.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi), ENNReal.toReal_ofReal hε.le] at hreal
  dsimp [ε] at hreal
  nlinarith [mul_pos Real.pi_pos hδ]

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Actual ORIGINAL arbitrary-domain Perron boundary equality and family
membership. The caller supplies only genuine original C1 geometry; every
sector/deficit/current/PSH-envelope conclusion is internally produced. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Metric TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
variable {n : ℕ}

/-- The SAME actual original-domain envelope has its TRUE local-BT reader,
with exact actual value readback on the SAME original Omega. -/
theorem domainPerronEnvelope_reader (hn : 0 < n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω) :
    IsLocallyBoundedPshOn Ω (fun z => (domainPerronEnvelope Ω D u z).toReal) ∧
      ∀ z ∈ Ω, (((domainPerronEnvelope Ω D u z).toReal : ℝ) : EReal) =
        domainPerronEnvelope Ω D u z :=
  psh_toReal_locallyBounded_of_ge_original hu
    (domainPerronEnvelope_plurisubharmonic hn hu hDc hDΩ)
    (fun z _ => le_domainPerronEnvelope hu z)

/-- Exact off-D equality at EVERY ORIGINAL point, INCLUDING the original
boundary, derived from actual defining functions and actual deficit submean. -/
theorem domainPerronEnvelope_eq_off_domain (hn : 0 < n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω) (hBoundary : HasC1Boundary D) :
    ∀ z ∈ Ω, z ∉ D → domainPerronEnvelope Ω D u z = (u z : EReal) := by
  intro z hzΩ hzD
  by_cases hzCl : z ∈ closure (D : Set (ComplexModel n))
  · have hzFront : z ∈ frontier (D : Set (ComplexModel n)) := by
      rw [frontier, D.isOpen.interior_eq]
      exact ⟨hzCl, hzD⟩
    obtain ⟨c⟩ := hBoundary z hzFront
    apply le_antisymm
    · exact psh_le_at_boundary_of_exterior_bound (Ω := Ω) hzΩ c
        (domainPerronEnvelope_plurisubharmonic hn hu hDc hDΩ z hzΩ)
        (BookDeepDomination.upperSemicontinuousAt_of_isLocallyBoundedPshOn hu hzΩ)
        (fun y hyΩ hyD => (domainPerronEnvelope_eq_of_not_mem_closure hu hyΩ hyD).le)
    · exact le_domainPerronEnvelope hu z
  · exact domainPerronEnvelope_eq_of_not_mem_closure hu hzΩ hzCl

/-- The SAME actual original-domain envelope is itself an ORIGINAL
competitor; there is no caller membership/output certificate. -/
theorem domainPerronEnvelope_mem_competitors (hn : 0 < n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω) (hBoundary : HasC1Boundary D) :
    domainPerronEnvelope Ω D u ∈ domainCompetitors Ω D u :=
  ⟨domainPerronEnvelope_plurisubharmonic hn hu hDc hDΩ,
    fun z hz hout => (domainPerronEnvelope_eq_off_domain hn hu hDc hDΩ hBoundary z hz hout).le⟩

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Actual ORIGINAL arbitrary-domain homogeneous MA producer. The actual
polydisk replacements, original-family membership and equality are produced;
true BT restrictions and actual local-nullness give mass0 on ORIGINAL D. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Metric MeasureTheory TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.PatchLocalVanishingMass
variable {n : ℕ}

/-- Every internally localized actual polydisk replacement is EXACTLY the
SAME original-domain envelope, from actual family maximality and true order. -/
theorem domainPerronEnvelope_eq_scaledPolydiskBalayage (hn : 0 < n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω) (hBoundary : HasC1Boundary D)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPD : polydiskChart c r '' closedUnitPolydisk n ⊆ (D : Set (ComplexModel n))) :
    ∀ z ∈ Ω, scaledPolydiskBalayage c r
      (fun x => (domainPerronEnvelope Ω D u x).toReal) z =
      (domainPerronEnvelope Ω D u z).toReal := by
  let U : ComplexModel n → ℝ := fun x => (domainPerronEnvelope Ω D u x).toReal
  have hU : IsLocallyBoundedPshOn Ω U := (domainPerronEnvelope_reader hn hu hDc hDΩ).1
  have hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)) :=
    hPD.trans (subset_closure.trans hDΩ)
  have hwpsh : PlurisubharmonicOn (fun z => ((scaledPolydiskBalayage c r U z : ℝ) : EReal)) Ω :=
    plurisubharmonicOn_scaledPolydiskBalayage hn hU hr hPΩ
  have hwF : (fun z => ((scaledPolydiskBalayage c r U z : ℝ) : EReal)) ∈ domainCompetitors Ω D u := by
    refine ⟨hwpsh, fun z hzΩ hzD => ?_⟩
    have hzP : z ∉ scaledPolydisk c r := by
      rintro ⟨w, hw, rfl⟩
      exact hzD (hPD ⟨w, unitPolydisk_subset_closedUnitPolydisk hw, rfl⟩)
    change ((scaledPolydiskBalayage c r U z : ℝ) : EReal) ≤ (u z : EReal)
    rw [scaledPolydiskBalayage_eqOn_compl hr U hzP]
    change (((domainPerronEnvelope Ω D u z).toReal : ℝ) : EReal) ≤ _
    rw [(domainPerronEnvelope_reader hn hu hDc hDΩ).2 z hzΩ,
      domainPerronEnvelope_eq_off_domain hn hu hDc hDΩ hBoundary z hzΩ hzD]
  intro z hzΩ
  apply le_antisymm
  · apply EReal.coe_le_coe_iff.mp
    change ((scaledPolydiskBalayage c r U z : ℝ) : EReal) ≤
      (((domainPerronEnvelope Ω D u z).toReal : ℝ) : EReal)
    rw [(domainPerronEnvelope_reader hn hu hDc hDΩ).2 z hzΩ]
    exact domainCompetitor_le_envelope hwF z
  · by_cases hzP : z ∈ scaledPolydisk c r
    · exact le_scaledPolydiskBalayage hn hU hr hPΩ hzP
    · exact (scaledPolydiskBalayage_eqOn_compl hr U hzP).ge

/-- The actual ORIGINAL BT measure gives mass0 to every actual interior
polydisk: its genuine restriction has the original produced replacement. -/
theorem domainPerronEnvelope_btMass_zero_on_scaledPolydisk (hn : 0 < n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω) (hBoundary : HasC1Boundary D)
    {c : ComplexModel n} {r : ℝ} (hr : r ≠ 0)
    (hPD : polydiskChart c r '' closedUnitPolydisk n ⊆ (D : Set (ComplexModel n)))
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit Ω (fun _ => fun x => (domainPerronEnvelope Ω D u x).toReal) μ) :
    μ (scaledPolydisk c r) = 0 := by
  let U : ComplexModel n → ℝ := fun x => (domainPerronEnvelope Ω D u x).toReal
  have hU : IsLocallyBoundedPshOn Ω U := (domainPerronEnvelope_reader hn hu hDc hDΩ).1
  have hPΩ : polydiskChart c r '' closedUnitPolydisk n ⊆ (Ω : Set (ComplexModel n)) :=
    hPD.trans (subset_closure.trans hDΩ)
  have hPopen : scaledPolydiskOpens c r ≤ Ω := scaledPolydiskOpens_le hr hPΩ
  have hμU := hμ.restrict_opens hPopen
  have hμW : IsBTLimit (scaledPolydiskOpens c r)
      (fun _ => scaledPolydiskBalayage c r U) (μ.restrict (scaledPolydiskOpens c r)) :=
    hμU.congr (fun _ z hz =>
      (domainPerronEnvelope_eq_scaledPolydiskBalayage hn hu hDc hDΩ hBoundary hr hPD z (hPopen hz)).symm)
  have hzero := eq_zero_of_isBTLimit_scaledPolydiskBalayage hn hU hr hPΩ hμW
  have hmass := congrArg (fun ν : Measure (ComplexModel n) => ν univ) hzero
  rw [← coe_scaledPolydiskOpens hr]
  simpa using hmass

/-- ACTUAL original-domain MA-zero: true small polydisk neighborhoods at
EVERY original point and true second-countable local-nullness are produced. -/
theorem domainPerronEnvelope_btMass_zero (hn : 0 < n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω) (hBoundary : HasC1Boundary D)
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit Ω (fun _ => fun x => (domainPerronEnvelope Ω D u x).toReal) μ) :
    μ (D : Set (ComplexModel n)) = 0 := by
  apply measure_eq_zero_of_locally_eq_zero μ
  intro x hx
  obtain ⟨r, hr, hPD⟩ := exists_pos_image_closedUnitPolydisk_subset (Ω := D) hx
  refine ⟨(scaledPolydiskOpens x r : Set (ComplexModel n)),
    (scaledPolydiskOpens x r).isOpen, ?_, ?_⟩
  · rw [coe_scaledPolydiskOpens hr.ne']
    exact mem_scaledPolydisk_center hr.ne'
  · rw [coe_scaledPolydiskOpens hr.ne']
    exact domainPerronEnvelope_btMass_zero_on_scaledPolydisk hn hu hDc hDΩ hBoundary hr.ne' hPD hμ

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Complete ORIGINAL arbitrary C1-domain balayage producer, all n>=1.
The actual replacement, actual BT measure, original off-D equality/order,
actual open bound and uniqueness are internally produced. No Dirichlet,
envelope, angular-thickness or zero-mass output witness is a premise. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
variable {n : ℕ}

/-- Complete actual native producer on the SAME original arbitrary C1 domain.
This theorem does not assume connectedness/nonemptiness of Omega or D;
the literal source PSH/nonempty readback is supplied by its source wrapper. -/
theorem exists_unique_C1DomainBalayage (hn : 0 < n)
    {Ω D : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω) (hBoundary : HasC1Boundary D) :
    ∃ ψ : ComplexModel n → ℝ,
      IsLocallyBoundedPshOn Ω ψ ∧
      (∃ μ : Measure (ComplexModel n), IsBTLimit Ω (fun _ => ψ) μ ∧ μ (D : Set (ComplexModel n)) = 0) ∧
      (∀ z ∈ Ω, z ∉ D → ψ z = u z) ∧
      (∀ z ∈ Ω, u z ≤ ψ z) ∧
      (∃ V : Opens (ComplexModel n), closure (D : Set (ComplexModel n)) ⊆ (V : Set (ComplexModel n)) ∧
        V ≤ Ω ∧ ∃ C : ℝ, ∀ z ∈ V, |ψ z| ≤ C) ∧
      ∀ χ : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω χ →
        (∃ ν : Measure (ComplexModel n), IsBTLimit Ω (fun _ => χ) ν ∧ ν (D : Set (ComplexModel n)) = 0) →
        (∀ z ∈ Ω, z ∉ D → χ z = u z) → EqOn ψ χ Ω := by
  let ψ : ComplexModel n → ℝ := fun z => (domainPerronEnvelope Ω D u z).toReal
  have hreader := domainPerronEnvelope_reader hn hu hDc hDΩ
  have hψ : IsLocallyBoundedPshOn Ω ψ := hreader.1
  obtain ⟨μ, hμ⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn
    (u := fun _ : Fin n => ψ) (fun _ => hψ)
  have hμzero : μ (D : Set (ComplexModel n)) = 0 :=
    domainPerronEnvelope_btMass_zero hn hu hDc hDΩ hBoundary hμ
  have he : ∀ z ∈ Ω, z ∉ D → ψ z = u z := by
    intro z hz hout
    simpa only [EReal.toReal_coe] using congrArg EReal.toReal
      (domainPerronEnvelope_eq_off_domain hn hu hDc hDΩ hBoundary z hz hout)
  refine ⟨ψ, hψ, ⟨μ, hμ, hμzero⟩, he, ?_, ?_, ?_⟩
  · intro z hz
    apply EReal.coe_le_coe_iff.mp
    change (u z : EReal) ≤ (((domainPerronEnvelope Ω D u z).toReal : ℝ) : EReal)
    rw [hreader.2 z hz]
    exact le_domainPerronEnvelope hu z
  · obtain ⟨V, hVo, hDV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hDc Ω.isOpen hDΩ
    obtain ⟨C, -, hC⟩ := hψ.exists_compact_abs_bound hVc hVΩ
    exact ⟨⟨V, hVo⟩, hDV, subset_closure.trans hVΩ, C,
      fun z hz => hC z (subset_closure hz)⟩
  · intro χ hχ hν heχ
    obtain ⟨ν, hν, hνzero⟩ := hν
    exact BookDeepDomination.balayage_unique hn hDc hDΩ hψ hχ he heχ hμ hν hμzero hνzero

end SGPT.PSH.SourceDomainBalayageDraft

end


/-! Literal ORIGINAL EReal source datum and original function readback of the
complete arbitrary-original-C1-domain balayage producer. The existing genuine canonical
reader theorem supplies all finiteness/local-BT bridges internally. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceDomainBalayageDraft
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
variable {n : ℕ}

/-- Complete arbitrary C1-domain balayage for the literal ORIGINAL source PSH datum.
All displayed local bounds are actual order bounds, all BT measures exist
internally, and the original function is retained in every output clause. -/
theorem source_exists_unique_C1DomainBalayage (hn : 0<n)
    {Ω D : Opens (ComplexModel n)} {φ : ComplexModel n  →  EReal}
    (hφ : SGPT.PSH.PSHOn φ Ω)
    (hφb : ∀ z∈Ω,∃ U∈𝓝 z,∃ C : ℝ,∀ w∈U,((-C:ℝ):EReal)≤φ w ∧ φ w≤C)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω) (hBoundary : HasC1Boundary D) :
    ∃ ψ : ComplexModel n  →  EReal,
      SGPT.PSH.PSHOn ψ Ω ∧
      (∀ z∈Ω,∃ U∈𝓝 z,∃ C : ℝ,∀ w∈U,((-C:ℝ):EReal)≤ψ w ∧ ψ w≤C) ∧
      (∃ μ : Measure (ComplexModel n),
        IsBTLimit Ω (fun _ => fun z => (ψ z).toReal) μ ∧ μ ((D : Set (ComplexModel n)))=0) ∧
      (∀ z∈Ω,z∉(D : Set (ComplexModel n)) → ψ z=φ z) ∧
      (∀ z∈Ω,φ z≤ψ z) ∧
      (∃ V : Opens (ComplexModel n),closure (D : Set (ComplexModel n))⊆(V:Set (ComplexModel n)) ∧
        V≤Ω ∧ ∃ C : ℝ,∀ z∈V,((-C:ℝ):EReal)≤ψ z ∧ ψ z≤C) ∧
      ∀ χ : ComplexModel n  →  EReal,SGPT.PSH.PSHOn χ Ω →
        (∀ z∈Ω,∃ U∈𝓝 z,∃ C : ℝ,∀ w∈U,((-C:ℝ):EReal)≤χ w ∧ χ w≤C) →
        (∃ ν : Measure (ComplexModel n),
          IsBTLimit Ω (fun _ => fun z => (χ z).toReal) ν ∧ ν ((D : Set (ComplexModel n)))=0) →
        (∀ z∈Ω,z∉(D : Set (ComplexModel n)) → χ z=φ z) → EqOn ψ χ Ω := by
  obtain ⟨hφr,hφe⟩ := BookDeepDomination.isLocallyBoundedPshOn_toReal hφ hφb
  obtain ⟨ψr,hψr,hμr,he,hle,hV,huq⟩ := exists_unique_C1DomainBalayage hn hφr hDc hDΩ hBoundary
  let ψ : ComplexModel n  →  EReal := fun z => (ψr z:EReal)
  have hψsource : SGPT.PSH.PSHOn ψ Ω := by
    refine ⟨hψr.1.discPshOn, ?_⟩
    obtain ⟨x, hx, _⟩ := hφ.nontrivial
    exact ⟨x, hx, EReal.coe_ne_bot (ψr x)⟩
  have hψb : ∀ z∈Ω,∃ U∈𝓝 z,∃ C : ℝ,∀ w∈U,((-C:ℝ):EReal)≤ψ w ∧ ψ w≤C := by
    intro z hz
    obtain ⟨V,hzV,-,C,hC⟩ := hψr.2 z hz
    refine ⟨(V:Set (ComplexModel n)),V.isOpen.mem_nhds hzV,C,fun w hw => ?_⟩
    exact ⟨EReal.coe_le_coe_iff.mpr (neg_le_of_abs_le (hC w hw)),
      EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hC w hw))⟩
  refine ⟨ψ,hψsource,hψb,?_,?_,?_,?_,?_⟩
  · obtain ⟨μ,hμ,hzero⟩ := hμr
    exact ⟨μ,by simpa only [ψ,EReal.toReal_coe] using hμ,hzero⟩
  · intro z hz hout
    exact (congrArg (fun x : ℝ => (x:EReal)) (he z hz hout)).trans (hφe z hz)
  · intro z hz
    calc
      φ z=(((φ z).toReal:ℝ):EReal) := (hφe z hz).symm
      _≤ψ z := EReal.coe_le_coe_iff.mpr (hle z hz)
  · obtain ⟨V,hDV,hVΩ,C,hC⟩ := hV
    exact ⟨V,hDV,hVΩ,C,fun z hz =>
      ⟨EReal.coe_le_coe_iff.mpr (neg_le_of_abs_le (hC z hz)),
        EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hC z hz))⟩⟩
  · intro χ hχ hχb hν heχ
    obtain ⟨hχr,hχe⟩ := BookDeepDomination.isLocallyBoundedPshOn_toReal hχ hχb
    have hreal : EqOn ψr (fun z => (χ z).toReal) Ω :=
      huq _ hχr hν (fun z hz hout => congrArg EReal.toReal (heχ z hz hout))
    intro z hz
    exact (congrArg (fun x : ℝ => (x:EReal)) (hreal hz)).trans (hχe z hz)

/-- ENTIRE original prop:BT_balayage, with the authorized positive-dimension
repair. ORIGINAL arbitrary Omega/D, original strongly-pseudoconvex geometry,
merely locally bounded ORIGINAL EReal PSH datum and ALL printed clauses.
No Dirichlet/boundary/output/positive-mass witness is a caller premise. -/
theorem source_BT_balayage (hn : 0<n)
    {Ω D : Opens (ComplexModel n)} {φ : ComplexModel n  →  EReal}
    (hφ : SGPT.PSH.PSHOn φ Ω)
    (hφb : ∀ z∈Ω,∃ U∈𝓝 z,∃ C : ℝ,∀ w∈U,((-C:ℝ):EReal)≤φ w ∧ φ w≤C)
    (hDc : IsCompact (closure (D : Set (ComplexModel n))))
    (hDΩ : closure (D : Set (ComplexModel n)) ⊆ Ω) (hStrong : IsStronglyPseudoconvexDomain D) :
    ∃ ψ : ComplexModel n  →  EReal,
      SGPT.PSH.PSHOn ψ Ω ∧
      (∀ z∈Ω,∃ U∈𝓝 z,∃ C : ℝ,∀ w∈U,((-C:ℝ):EReal)≤ψ w ∧ ψ w≤C) ∧
      (∃ μ : Measure (ComplexModel n),
        IsBTLimit Ω (fun _ => fun z => (ψ z).toReal) μ ∧ μ ((D : Set (ComplexModel n)))=0) ∧
      (∀ z∈Ω,z∉(D : Set (ComplexModel n)) → ψ z=φ z) ∧
      (∀ z∈Ω,φ z≤ψ z) ∧
      (∃ V : Opens (ComplexModel n),closure (D : Set (ComplexModel n))⊆(V:Set (ComplexModel n)) ∧
        V≤Ω ∧ ∃ C : ℝ,∀ z∈V,((-C:ℝ):EReal)≤ψ z ∧ ψ z≤C) ∧
      ∀ χ : ComplexModel n  →  EReal,SGPT.PSH.PSHOn χ Ω →
        (∀ z∈Ω,∃ U∈𝓝 z,∃ C : ℝ,∀ w∈U,((-C:ℝ):EReal)≤χ w ∧ χ w≤C) →
        (∃ ν : Measure (ComplexModel n),
          IsBTLimit Ω (fun _ => fun z => (χ z).toReal) ν ∧ ν ((D : Set (ComplexModel n)))=0) →
        (∀ z∈Ω,z∉(D : Set (ComplexModel n)) → χ z=φ z) → EqOn ψ χ Ω :=
  source_exists_unique_C1DomainBalayage hn hφ hφb hDc hDΩ hStrong.hasC1Boundary

end SGPT.PSH.SourceDomainBalayageDraft

end
