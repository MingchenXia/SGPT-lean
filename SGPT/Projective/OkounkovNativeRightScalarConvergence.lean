import SGPT.Projective.OkounkovNativeScalarConvergence

/-! Genuine right scalar Kähler neighborhoods and true native dS convergence at ONE.
Blueprint: okounkov-native-right-scalar-convergence.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.NativeRightScalarConvergence
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData ThetaPshConvexCombination
open ThetaPshL1Topology SingularCanonicalSingularityDistance
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M]

omit [CompactSpace M] in
private theorem thetaPsh_of_semipositive_difference {θ η : ClosedRealOneOneForm n M} {φ : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hsemi : (η-θ).val.IsSemipositive) :
    IsThetaPshPotential η.val φ := by
  have hh := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ hsemi
  rwa [add_sub_cancel] at hh

/-- True compact form domination produces a RIGHT interval of actual Kähler scalar weights. -/
theorem exists_right_scalar_kahler_neighborhood {θ : ClosedRealOneOneForm n M} {φ : M → EReal}
    (hφ : IsKahlerCurrentPotential θ φ) :
    ∃ r₁ : ℝ, 1<r₁ ∧ ∀ r : ℝ, 1≤r → r≤r₁ →
      IsKahlerCurrentPotential θ (fun x => (r:EReal)*φ x) := by
  obtain ⟨κ,hκ⟩ := hφ
  obtain ⟨A,hA,hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-θ)
  let r₁ : ℝ := 1+1/(A+1)
  have hA1 : 0<A+1 := by linarith
  have hr₁ : 1<r₁ := by dsimp only [r₁]; linarith [div_pos zero_lt_one hA1]
  refine ⟨r₁,hr₁,?_⟩
  intro r hr hr1
  have hAr : A*(r-1)≤A/(A+1) := by
    have hh : r-1≤1/(A+1) := by dsimp only [r₁] at hr1; linarith
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hh hA.le
  have hAfrac : A/(A+1)<1 := (div_lt_one hA1).mpr (by linarith)
  let b : ℝ := r-A*(r-1)
  have hb : 0<b := by dsimp only [b]; linarith
  let κr := kahlerSmul κ hb
  refine ⟨κr,?_⟩
  apply thetaPsh_of_semipositive_difference (isThetaPshPotential_nonneg_smul hκ (by linarith))
  have he : θ-κr.form-r•(θ-κ.form)=(r-1)•(-θ+A•κ.form) := by
    dsimp only [κr,kahlerSmul,b]
    module
  rw [he]
  exact KahlerDomination.isSemipositive_smul hdom (by linarith)

variable [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

/-- The SAME true native right scalar weights tend to the original in the EXISTING dS topology. -/
theorem exists_right_scalar_native_convergence (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {φ : M → EReal} (hφ : IsKahlerCurrentPotential θ φ) :
    ∃ r₁ : ℝ, 1<r₁ ∧
      ∃ hscalar : ∀ r : Ioo (1:ℝ) r₁, IsKahlerCurrentPotential θ (fun x => (r.val:EReal)*φ x),
      ∀ (I : Type*) (F : Filter I) (r : I → Ioo (1:ℝ) r₁),
      Tendsto (fun i => (r i).val) F (𝓝 1) →
        Tendsto (fun i => (⟨fun x => ((r i).val:EReal)*φ x,
          PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hscalar (r i))⟩ : ThetaPshL1 θ.val)) F
          (@nhds (ThetaPshL1 θ.val)
            (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
            ⟨φ,PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ⟩) := by
  obtain ⟨r₁,hr1,hK⟩ := exists_right_scalar_kahler_neighborhood hφ
  have hscalar (r : Ioo (1:ℝ) r₁) : IsKahlerCurrentPotential θ (fun x => (r.val:EReal)*φ x) :=
    hK r.val r.property.1.le r.property.2.le
  refine ⟨r₁,hr1,hscalar,?_⟩
  intro I F r hr
  have hden : 0<r₁-1 := sub_pos.mpr hr1
  let t : I → Ioo (0:ℝ) 1 := fun i =>
    ⟨((r i).val-1)/(r₁-1),div_pos (sub_pos.mpr (r i).property.1) hden,
      (div_lt_one hden).mpr (by linarith [(r i).property.2])⟩
  have ht : Tendsto (fun i => (t i).val) F (𝓝 0) := by
    have hh := (hr.sub_const 1).div_const (r₁-1)
    simpa only [sub_self,zero_div,t] using hh
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hbase := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential (hK r₁ hr1.le le_rfl)
  have hnative := EndpointMixedMassGeneralConvexCombination.tendsto_native_general_convex_zero
    omega θ hbig hbase hφθ F t ht
  apply hnative.congr
  intro i
  apply Subtype.ext
  funext x
  have ht0 : 0≤(t i).val := (t i).property.1.le
  have ht1 : (t i).val≤1 := (t i).property.2.le
  have hcoef : (t i).val*r₁+(1-(t i).val)=(r i).val := by
    dsimp only [t]
    field_simp [hden.ne']
    ring
  change ((t i).val:EReal)*((r₁:EReal)*φ x)+(((1-(t i).val:ℝ):EReal))*φ x = ((r i).val:EReal)*φ x
  rw [←mul_assoc,←EReal.coe_mul,
    ←EReal.right_distrib_of_nonneg (EReal.coe_nonneg.mpr (mul_nonneg ht0 (by linarith)))
      (EReal.coe_nonneg.mpr (sub_nonneg.mpr ht1)),←EReal.coe_add,hcoef]
end SGPT.Okounkov.NativeRightScalarConvergence
