import SGPT.Foundations.Analysis.Pending.ActualFiniteFamilyPrimeMultiplicity
import SGPT.Foundations.Analysis.Pending.ActualFlatNormalOrder

/-! The actual common coordinate factor computes the entire original family order.
Blueprint: `trace-native-prime-reader.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open DemaillyApproximantDivisorialLelong HolomorphicGermReducednessBridge
open scoped Topology ENNReal

/-- Actual factorization and genuine frequent residual nonvanishing compute
the ORIGINAL whole family order. No multiplicity equality is a premise. -/
theorem commonFactorization_coordinateOrder {m N a : ℕ}
    (F H : Fin N → ComplexModel (m+1) → ℂ)
    (hF : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)), DifferentiableAt ℂ (F j) z)
    (hH : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)), DifferentiableAt ℂ (H j) z)
    (hfactor : ∀ j, F j =ᶠ[𝓝 0] fun z => z (Fin.last m)^a * H j z)
    (hfreq : ∃ j, ∃ᶠ z in 𝓝 (0 : ComplexModel (m+1)), z (Fin.last m) = 0 ∧ H j z ≠ 0) :
    (⨅ j, emultiplicity
      (HolGerm.mk (fun z : ComplexModel (m+1) => z (Fin.last m))
        (eventually_differentiableAt_coordinate (Fin.last m)))
      (HolGerm.mk (F j) (hF j))) = (a : ℕ∞) := by
  let q := HolGerm.mk (fun z : ComplexModel (m+1) => z (Fin.last m))
    (eventually_differentiableAt_coordinate (Fin.last m))
  have hq : Prime q := HolomorphicCoordinatePrime.prime_coordinate_germ (Fin.last m)
  have hfac (j : Fin N) : HolGerm.mk (F j) (hF j) = q^a * HolGerm.mk (H j) (hH j) := by
    change HolGerm.mk (F j) (hF j) =
      HolGerm.mk (fun z : ComplexModel (m+1) => z (Fin.last m))
        (eventually_differentiableAt_coordinate (Fin.last m)) ^ a * HolGerm.mk (H j) (hH j)
    rw [← HolGerm.mk_pow, ← HolGerm.mk_mul, HolGerm.mk_eq_mk_iff]
    exact hfactor j
  change (⨅ j, emultiplicity q (HolGerm.mk (F j) (hF j))) = (a : ℕ∞)
  apply le_antisymm
  · obtain ⟨j, hj⟩ := hfreq
    have hnot : ¬ q ∣ HolGerm.mk (H j) (hH j) := by
      rintro ⟨b, hb⟩
      obtain ⟨B, hB, rfl⟩ := HolGerm.exists_eq_mk b
      have heq : H j =ᶠ[𝓝 0] fun z => z (Fin.last m) * B z := by
        change HolGerm.mk (H j) (hH j) =
          HolGerm.mk (fun z : ComplexModel (m+1) => z (Fin.last m))
            (eventually_differentiableAt_coordinate (Fin.last m)) * HolGerm.mk B hB at hb
        rw [← HolGerm.mk_mul, HolGerm.mk_eq_mk_iff] at hb
        exact hb
      obtain ⟨z, ⟨hz, hn⟩, he⟩ := (hj.and_eventually heq).exists
      exact hn (by simpa only [hz, zero_mul] using he)
    calc
      _ ≤ emultiplicity q (HolGerm.mk (F j) (hF j)) := iInf_le _ j
      _ = (a : ℕ∞) := by
        rw [hfac j, emultiplicity_mul hq, emultiplicity_pow_self_of_prime hq,
          emultiplicity_eq_zero.mpr hnot, add_zero]
  · exact le_iInf fun j => pow_dvd_iff_le_emultiplicity.mp ⟨HolGerm.mk (H j) (hH j), hfac j⟩

/-- The SAME actual flat factorization computes the ENTIRE original ideal's
normal order, using actual original generators and the genuine flat germ equivalence. -/
theorem originalNormalOrder_eq_commonFactorization
    {m N a : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel (m+1)) M]
    [IsComplexManifold (m+1) M] {E : Set M} {x : M}
    (Φ : DivisorFlattening (m := m) E x)
    (A : SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.GermIdeal (m+1) M)
    (g : Fin N → M → ℂ)
    (hg : ∀ j, SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.HolomorphicAt (m+1) (g j) x)
    (hgen : ∀ v, A.mem x v ↔ SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.IsInSpanAt
      (n := m+1) (· ∈ range g) x v)
    (hF : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)), DifferentiableAt ℂ (fun w => g j (Φ.point w)) z)
    (H : Fin N → ComplexModel (m+1) → ℂ)
    (hH : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel (m+1)), DifferentiableAt ℂ (H j) z)
    (hfactor : ∀ j, (fun z => g j (Φ.point z)) =ᶠ[𝓝 0] fun z => z (Fin.last m)^a * H j z)
    (hfreq : ∃ j, ∃ᶠ z in 𝓝 (0 : ComplexModel (m+1)), z (Fin.last m) = 0 ∧ H j z ≠ 0) :
    FixedGermNormalOrder.originalStalkNormalOrder Φ A = (a : ℕ∞) := by
  rw [FixedGermNormalOrder.originalStalkNormalOrder_eq_generators Φ A g hg hgen]
  simp_rw [ActualFlatNormalOrder.functionNormalOrder_eq_flat]
  simpa only [ActualFlatNormalOrder.flatFunctionGerm] using
    commonFactorization_coordinateOrder (fun j z => g j (Φ.point z)) H hF hH hfactor hfreq

end SGPT.NAPotential.TraceComparison.NativeImage
