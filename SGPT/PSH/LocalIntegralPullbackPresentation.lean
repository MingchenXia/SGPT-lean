import SGPT.PSH.FiniteCartierPullback

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending HironakaEffectiveDivisorSum InvertibleIdealQuotient
open scoped Topology Manifold ContDiff

universe u
variable {m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X}

/-- ORIGINAL D,x and genuine modification manufacture ONE SAME local integral
family with literal full ideal-image, EVERY composed-product stalk, actual grouped
coefficients and pole-inclusive original logarithms; no presentation is an input. -/
theorem exists_geometric_q_local_integral_pullback_presentation
    (D : EffectiveGeometricQDivisor (m + 1) X) (x : X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    ∃ U : Opens X, x ∈ U ∧
      ∃ (s : Finset {P // 0 < D.coefficient P}) (d : ℕ)
        (a : {P // 0 < D.coefficient P} → ℕ)
        (g : {P // 0 < D.coefficient P} → X → ℂ),
        (∀ P, P ∈ s ↔ (P.val.val ∩ (U : Set X)).Nonempty) ∧ 0 < d ∧
        (∀ P ∈ s, 0 < a P ∧ D.coefficient P.val = (a P : ℚ) / (d : ℚ)) ∧
        (∀ P ∈ s, MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) (g P) U ∧
          ∀ y ∈ U, ∀ h, (vanishingIdeal (n := m + 1) P.val.val).mem y h ↔
            IsInSpanAt (n := m + 1) (· = g P) y h) ∧
        let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
        let G := fun y => ∏ P ∈ s, g P y ^ a P
        let H := ∑ P ∈ s, a P • geometricPrimeCarrierTotalTransform P.val hπ
        cartierModificationPullback hπ F = H ∧
        H.ideal = GermIdeal.pullback (m := m + 1) π F.ideal ∧
        (∀ y, π y ∈ U → HolomorphicAt (m + 1) (G ∘ π) y ∧
          ∀ h, H.ideal.mem y h ↔ IsInSpanAt (n := m + 1) (· = G ∘ π) y h) ∧
        (∀ A : GeometricPrimeCarrier (m + 1) Y,
          (A.val ∩ π ⁻¹' (U : Set X)).Nonempty →
          (geometricQDivisorModificationPullback D hπ).coefficient A =
            (cartierGeometricPrimeCoefficient H A : ℚ) / (d : ℚ)) ∧
        H.support ∩ π ⁻¹' (U : Set X) =
          (geometricQDivisorModificationPullback D hπ).support ∩ π ⁻¹' (U : Set X) ∧
        ∀ y, (∑ P : {P // P ∈ s}, ((D.coefficient P.val.val : ℝ) : EReal) *
          logNormSq (g P.val (π y))) =
            (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * logNormSq ((G ∘ π) y) := by
  obtain ⟨U, hxU, s, d, a, g, hs, hd, ha, hgens, hrest⟩ :=
    exists_geometric_q_local_integral_cartier_presentation D x
  obtain ⟨hGhol, hFgen, hFsupp, hlog⟩ := hrest
  let F := ∑ P ∈ s, a P • geometricPrimeCarrierEffectiveDivisor P.val
  let G := fun y => ∏ P ∈ s, g P y ^ a P
  let H := ∑ P ∈ s, a P • geometricPrimeCarrierTotalTransform P.val hπ
  have hHF : cartierModificationPullback hπ F = H :=
    cartierModificationPullback_finite_prime_sum hπ s (fun P => P.val) a
  have hsupH : H.support = π ⁻¹' F.support := by
    rw [← hHF]
    exact BlowupExceptionalDivisor.zeroLocus_pullback hπ.1
      (DivisorMetric.isCoherent_of_isInvertible F.isInvertible)
  refine ⟨U, hxU, s, d, a, g, hs, hd, ha, hgens, ?_⟩
  change cartierModificationPullback hπ F = H ∧ _
  refine ⟨hHF, ?_, ?_, ?_, ?_, ?_⟩
  · change H.ideal = GermIdeal.pullback (m := m + 1) π F.ideal
    rw [← hHF, cartierModificationPullback_ideal]
  · intro y hyU
    have hhol : HolomorphicAt (m + 1) G (π y) :=
      holomorphicAt_of_mdifferentiableOn U.isOpen hGhol hyU
    refine ⟨hhol.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt), ?_⟩
    intro h
    change H.ideal.mem y h ↔ IsInSpanAt (n := m + 1) (· = G ∘ π) y h
    rw [← hHF, cartierModificationPullback_ideal]
    exact MemberPullback.pullback_mem_iff_of_generator hπ.1 hhol (hFgen (π y) hyU) h
  · intro A hA
    rw [geometricQDivisorModificationPullback_local_coefficient D hπ U s hs A hA]
    rw [cartierGeometricPrimeCoefficient_finset_sum, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    rw [(ha P hP).2, Nat.cast_mul]
    ring
  · rw [hsupH, geometricQDivisorModificationPullback_support,
      ← preimage_inter, ← preimage_inter, hFsupp]
  · intro y
    exact hlog (π y)

end SGPT.PSH
