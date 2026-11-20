import SGPT.PSH.CanonicalAnalyticGrowthGerm
import SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetChartInvariance

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.PSH

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open HironakaHolomorphicJetChartInvariance

/-- Actual pointed holomorphic composition carries the entire canonical growth
ideal, rather than only a selected finite generator family. -/
theorem map_canonicalGrowthGermIdeal_le_of_holomorphic_pullback
    {m n N : ℕ} (η : ComplexModel m → ComplexModel n)
    (hη : ∀ᶠ z in 𝓝 (0 : ComplexModel m), DifferentiableAt ℂ η z)
    (hη0 : η 0 = 0) (G : Fin N → ComplexModel n → ℂ) :
    Ideal.map (compAlgHom η hη hη0).toRingHom (canonicalGrowthGermIdeal G) ≤
      canonicalGrowthGermIdeal (fun j => G j ∘ η) := by
  have ht : Tendsto η (𝓝 0) (𝓝 0) := by
    simpa only [hη0] using hη.self_of_nhds.continuousAt.tendsto
  unfold canonicalGrowthGermIdeal
  rw [Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro a ⟨g, ⟨F, hF, C, hC, heq, hbound⟩, rfl⟩
  apply Ideal.subset_span
  refine ⟨F ∘ η, holomorphic_comp η hη hη0 hF, C, hC, ?_, ?_⟩
  · rw [← heq]
    exact (compAlgHom_mk η hη hη0 F hF).symm
  · simpa only [Function.comp_apply] using ht.eventually hbound

/-- Actual nonlinear coordinate geometry transports the entire bounded-germ
ideal. Neighbourhood coherence and global ideal-sheaf descent are separate. -/
theorem map_canonicalGrowthGermIdeal_eq_of_local_holomorphic_equiv
    {n N : ℕ} (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (h0 : Φ.toFun 0 = 0) (G : Fin N → ComplexModel n → ℂ) :
    Ideal.map (localGermAlgEquiv Φ h0).toRingEquiv.toRingHom
      (canonicalGrowthGermIdeal G) =
      canonicalGrowthGermIdeal (fun j => G j ∘ Φ.toFun) := by
  let e := localGermAlgEquiv Φ h0
  let H : Fin N → ComplexModel n → ℂ := fun j => G j ∘ Φ.toFun
  have hforward : Ideal.map e.toRingEquiv.toRingHom (canonicalGrowthGermIdeal G) ≤
      canonicalGrowthGermIdeal H :=
    map_canonicalGrowthGermIdeal_le_of_holomorphic_pullback
      Φ.toFun (local_toFun_holomorphic Φ) h0 G
  have htarget : (0 : ComplexModel n) ∈ Φ.target := by
    simpa only [h0] using Φ.mapsTo_toFun Φ.center_mem_source
  have hcomparison : canonicalGrowthGermIdeal (fun j => H j ∘ Φ.invFun) =
      canonicalGrowthGermIdeal G := by
    apply canonicalGrowthGermIdeal_eq_of_norm_comparison
      (a := 1) (b := 1) _ _ zero_lt_one zero_lt_one
    filter_upwards [Φ.isOpen_target.mem_nhds htarget] with z hz
    have heq : (∑ j, ‖(H j ∘ Φ.invFun) z‖) = ∑ j, ‖G j z‖ := by
      apply Finset.sum_congr rfl
      intro j _
      change ‖G j (Φ.toFun (Φ.invFun z))‖ = ‖G j z‖
      rw [Φ.right_inv z hz]
    rw [heq, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have hback : Ideal.map e.symm.toRingEquiv.toRingHom (canonicalGrowthGermIdeal H) ≤
      canonicalGrowthGermIdeal G := by
    change Ideal.map
      (compAlgHom Φ.invFun (local_invFun_holomorphic Φ h0)
        (local_invFun_zero Φ h0)).toRingHom (canonicalGrowthGermIdeal H) ≤
      canonicalGrowthGermIdeal G
    rw [← hcomparison]
    exact map_canonicalGrowthGermIdeal_le_of_holomorphic_pullback Φ.invFun
      (local_invFun_holomorphic Φ h0) (local_invFun_zero Φ h0) H
  apply le_antisymm hforward
  have hmap := Ideal.map_mono hback (f := e.toRingEquiv.toRingHom)
  have hcancel : Ideal.map e.toRingEquiv.toRingHom
      (Ideal.map e.symm.toRingEquiv.toRingHom (canonicalGrowthGermIdeal H)) =
      canonicalGrowthGermIdeal H := by
    exact Ideal.map_of_equiv e.toRingEquiv.symm
  rw [hcancel] at hmap
  exact hmap

end SGPT.PSH
