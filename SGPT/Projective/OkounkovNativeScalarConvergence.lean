import SGPT.Projective.OkounkovNativeScalarKahler
import SGPT.Okounkov.PartialBodyGeneral
import SGPT.Foundations.Analysis.Pending.EndpointMixedMassGeneralConvexCombination

/-! Genuine native dS convergence for actual scalar Kähler weights, no supplied mixed-mass limits.
Blueprint: okounkov-native-scalar-convergence.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.NativeScalarConvergence
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData ThetaPshConvexCombination
open ThetaPshL1Topology SingularCanonicalSingularityDistance
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]

/-- Actual native Kähler scalar family returns to its true original weight in the EXISTING dS topology. -/
theorem exists_left_scalar_native_convergence (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {φ : M → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    ∃ r₀ : ℝ, 0<r₀ ∧ r₀<1 ∧
      ∃ hscalar : ∀ q : Ioo r₀ 1, IsKahlerCurrentPotential θ (fun x => (q.val:EReal)*φ x),
      ∀ (I : Type*) (F : Filter I) (q : I → Ioo r₀ 1),
      Tendsto (fun i => (q i).val) F (𝓝 1) →
        Tendsto (fun i => (⟨fun x => ((q i).val:EReal)*φ x,
          PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hscalar (q i))⟩ : ThetaPshL1 θ.val)) F
          (@nhds (ThetaPshL1 θ.val)
            (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
            ⟨φ,PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ⟩) := by
  obtain ⟨r₀,hr0,hr1,hbase,hK⟩ := NativeScalarKahler.exists_left_scalar_kahler_neighborhood hφ
  have hscalar (q : Ioo r₀ 1) : IsKahlerCurrentPotential θ (fun x => (q.val:EReal)*φ x) :=
    hK q.val q.property.1 q.property.2.le
  refine ⟨r₀,hr0,hr1,hscalar,?_⟩
  intro I F q hq
  have hden : 0<1-r₀ := sub_pos.mpr hr1
  let t : I → Ioo (0:ℝ) 1 := fun i =>
    ⟨(1-(q i).val)/(1-r₀),div_pos (sub_pos.mpr (q i).property.2) hden,
      (div_lt_one hden).mpr (by linarith [(q i).property.1])⟩
  have ht : Tendsto (fun i => (t i).val) F (𝓝 0) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : I => (1:ℝ)) F (𝓝 1)).sub hq).div_const (1-r₀)
    simpa only [sub_self,zero_div,t] using h
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hnative := EndpointMixedMassGeneralConvexCombination.tendsto_native_general_convex_zero
    omega θ hbig hbase hφθ F t ht
  apply hnative.congr
  intro i
  apply Subtype.ext
  funext x
  have ht0 : 0≤(t i).val := (t i).property.1.le
  have ht1 : (t i).val≤1 := (t i).property.2.le
  have hcoef : (t i).val*r₀+(1-(t i).val)=(q i).val := by
    dsimp only [t]
    field_simp [hden.ne']
    ring
  change ((t i).val:EReal)*((r₀:EReal)*φ x)+(((1-(t i).val:ℝ):EReal))*φ x = ((q i).val:EReal)*φ x
  rw [←mul_assoc,←EReal.coe_mul,
    ←EReal.right_distrib_of_nonneg (EReal.coe_nonneg.mpr (mul_nonneg ht0 hr0.le))
      (EReal.coe_nonneg.mpr (sub_nonneg.mpr ht1)),←EReal.coe_add,hcoef]

end SGPT.Okounkov.NativeScalarConvergence
