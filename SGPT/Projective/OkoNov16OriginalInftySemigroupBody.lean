import SGPT.Projective.OkoNov16OriginalInftyVeroneseCarrier
import SGPT.Foundations.Schemes.NativeLinePowerSectionNaturality

/-! Blueprint first: oko-nov16-original-infty-semigroup-body.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OkoNov16
open SGPT.Okounkov.AlgebraicValuation
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NAPotential.GAGAMult SGPT.GAGA.H0L SGPT.PSH
open scoped Pointwise
open scoped Topology
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  (J : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]
local instance inftySemigroupBodyTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance inftySemigroupBodyCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance inftySemigroupBodyManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

private theorem inftySemigroup_natCast_add (k l : ℕ) (x : EReal) :
    (k:EReal)*x+(l:EReal)*x=((k+l:ℕ):EReal)*x := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hlR : (0:ℝ)<l := by exact_mod_cast hl
  have hklR : (0:ℝ)<((k+l:ℕ):ℝ) := by exact_mod_cast Nat.add_pos_left hk l
  change ((k:ℝ):EReal)*x+((l:ℝ):EReal)*x=(((k+l:ℕ):ℝ):EReal)*x
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hkR,EReal.coe_mul_bot_of_pos hlR,
      EReal.coe_mul_bot_of_pos hklR,EReal.bot_add]
  | top => rw [EReal.coe_mul_top_of_pos hkR,EReal.coe_mul_top_of_pos hlR,
      EReal.coe_mul_top_of_pos hklR,EReal.top_add_top]
  | coe z =>
    rw [←EReal.coe_mul,←EReal.coe_mul,←EReal.coe_mul,←EReal.coe_add]
    congr 1
    push_cast
    ring

private theorem inftySemigroup_growthProduct {u w : SchemeComplexPoint f → EReal}
    {p : SchemeComplexPoint f} {g h : SchemeComplexPoint f → ℂ}
    (hg : (inftyIdeal (n:=n) u).mem p g) (hh : (inftyIdeal (n:=n) w).mem p h) :
    (inftyIdeal (n:=n) (fun y => u y+w y)).mem p (fun y => g y*h y) := by
  obtain ⟨hgh,C,hC⟩ := mem_inftyIdeal_iff_log_bound.mp hg
  obtain ⟨hhh,D,hD⟩ := mem_inftyIdeal_iff_log_bound.mp hh
  refine mem_inftyIdeal_iff_log_bound.mpr ⟨hgh.mul hhh,C+D,?_⟩
  filter_upwards [hC,hD] with y hy hy'
  have hlog : logNormSq (g y*h y)=logNormSq (g y)+logNormSq (h y) := by
    rw [logNormSq,norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg ‖g y‖),ENNReal.log_mul_add]
    rfl
  show logNormSq (g y*h y)≤u y+w y+((C+D:ℝ):EReal)
  rw [hlog,EReal.coe_add]
  exact (add_le_add hy hy').trans_eq (add_add_add_comm _ _ _ _)

private theorem inftySemigroup_product {L : X.Modules} (a : LineBundleAtlas L)
    {u : SchemeComplexPoint f → EReal} {k l : ℕ}
    {s : bundlePowerGlobalSections L k} {t : bundlePowerGlobalSections L l}
    (hs : IsInftySection f n J u k s) (ht : IsInftySection f n J u l t) :
    IsInftySection f n J u (k+l) (atlasPowerGlobalMul a k l s t) := by
  intro U α p hp
  have h := inftySemigroup_growthProduct f n (hs U α p hp) (ht U α p hp)
  have hw : (fun y => (k:EReal)*u y+(l:EReal)*u y)=
      (fun y => ((k+l:ℕ):EReal)*u y) := funext (fun y => inftySemigroup_natCast_add k l (u y))
  rw [hw] at h
  refine (inftyIdeal_mem_congr ?_).mp h
  have hU : IsOpen (schemeComplexPointImage f ⁻¹' (U:Set X)) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  filter_upwards [hU.mem_nhds hp] with y hy
  have hc := atlasPowerGlobalMul_anyFrame a k l α (𝟙 U) s t
  unfold sectionFrameCoefficient
  rw [show (homOfLE le_top : U ⟶ ⊤)=U.leTop from rfl,hc]
  exact (schemeOpenRegularFunction_mul f n J U _ _ hy).symm

def originalInftySectionSemigroup [IsIntegral X]
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X)
    {L : X.Modules} (a : LineBundleAtlas L) (u : SchemeComplexPoint f → EReal) :
    AddSubsemigroup ((Fin n → ℤ)×ℤ) where
  carrier := AlgebraicValuation.inftySectionSet f n J v c a u
  add_mem' := by
    rintro z w ⟨k,s,hs,hks,rfl⟩ ⟨l,t,ht,hlt,rfl⟩
    have hu := atlasPowerGlobalMul_ne_zero (v:=v) c a k l hs ht
    refine ⟨k+l,atlasPowerGlobalMul a k l s t,hu,inftySemigroup_product f n J a hks hlt,?_⟩
    have hv := sectionValue_mul (v:=v) c a k l s t
    rw [sectionValue_eq_vector c a (k+l) _ hu,sectionValue_eq_vector c a k s hs,
      sectionValue_eq_vector c a l t ht,←WithTop.coe_add,←toLex_add] at hv
    have hv' := toLex.injective (WithTop.coe_injective hv)
    rw [hv']
    ext <;> simp

theorem original_inftySectionBody_veronese [IsIntegral X]
    (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (c : X)
    (hc : IsNonnegAt v c) {L : X.Modules} (a : LineBundleAtlas L)
    (u : SchemeComplexPoint f → EReal) {r : ℕ} (hr : 0<r) :
    SGPT.AlmostSemigroup.Okounkov.body
      (originalInftySectionSemigroup f n J v c (a.tensorPower r) (fun y => (r:EReal)*u y)) =
    (r:ℝ) • SGPT.AlmostSemigroup.Okounkov.body (originalInftySectionSemigroup f n J v c a u) := by
  exact AlgebraicBody.body_eq_smul_of_veronese _ _ hr
    (fun x j => original_inftySectionSet_veronese_iff f n J v c hc a u hr x j)
end SGPT.Okounkov.OkoNov16
