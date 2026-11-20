import SGPT.Okounkov.ValGen2Conc
import SGPT.Foundations.Analysis.Pending.EndpointMixedMassGeneralConvexCombination

/-! Literal extended-real reparametrization and actual native fixed-class dS convergence from left coefficients.
Blueprint: okounkov-convex-left-native-limit.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace SGPT.Okounkov.ConvexLeftNativeLimit
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination
open SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
open scoped Topology

/-- Exact SAME original weights at every pole, no finite-value or coefficient comparison premise. -/
theorem convexComb_from_left_reparam {M : Type*} (u v : M → EReal)
    {s t : ℝ} (hs : 0<s) (hst : s<t) (ht : t<1) :
    convexComb s u v = convexComb ((t-s)/t) v (convexComb t u v) := by
  have ht0 : 0<t := hs.trans hst
  let r := (t-s)/t
  have hr0 : 0<r := div_pos (sub_pos.mpr hst) ht0
  have hr1 : r<1 := (div_lt_one ht0).mpr (by linarith)
  have hrt : (1-r)*t=s := by dsimp only [r];field_simp [ht0.ne'];ring
  have hrs : r+(1-r)*(1-t)=1-s := by dsimp only [r];field_simp [ht0.ne'];ring
  funext x
  symm
  dsimp only [convexComb]
  change (r:EReal)*v x+(((1-r:ℝ):EReal))*(((t:EReal)*u x)+(((1-t:ℝ):EReal))*v x)=_
  rw [ValGen2.ereal_coe_mul_add (sub_pos.mpr hr1),←mul_assoc,←mul_assoc,←EReal.coe_mul,←EReal.coe_mul]
  rw [add_left_comm]
  rw [←EReal.right_distrib_of_nonneg (EReal.coe_nonneg.mpr hr0.le)
    (EReal.coe_nonneg.mpr (mul_nonneg (sub_nonneg.mpr hr1.le) (sub_nonneg.mpr ht.le))),←EReal.coe_add]
  rw [hrt,hrs]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]

/-- Actual native singularity convergence of the SAME convex weights, from ANY strict left coefficient family. -/
theorem tendsto_native_convexComb_from_left (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) {I : Type*} (F : Filter I) (s : I → ℝ)
    (hs : ∀ i, 0<s i ∧ s i<t) (hlim : Tendsto s F (𝓝 t)) :
    let W : I → ThetaPshL1 θ.val := fun i =>
      ⟨convexComb (s i) u v,isThetaPshPotential_convexComb_closed hu hv
        (hs i).1.le ((hs i).2.trans ht1).le⟩
    Tendsto W F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
      ⟨convexComb t u v,isThetaPshPotential_convexComb_closed hu hv ht0.le ht1.le⟩) := by
  let r : I → Ioo (0:ℝ) 1 := fun i => ⟨(t-s i)/t,
    div_pos (sub_pos.mpr (hs i).2) ht0,(div_lt_one ht0).mpr (by linarith [(hs i).1])⟩
  have hr : Tendsto (fun i => (r i).val) F (𝓝 0) := by
    simpa only [r,sub_self,zero_div] using
      (((tendsto_const_nhds : Tendsto (fun _ : I => t) F (𝓝 t)).sub hlim).div_const t)
  have hχ := isThetaPshPotential_convexComb_closed hu hv ht0.le ht1.le
  have hnative := EndpointMixedMassGeneralConvexCombination.tendsto_native_general_convex_zero
    omega θ hbig hv hχ F r hr
  apply hnative.congr
  intro i
  apply Subtype.ext
  exact (convexComb_from_left_reparam u v (hs i).1 (hs i).2 ht1).symm
end SGPT.Okounkov.ConvexLeftNativeLimit
