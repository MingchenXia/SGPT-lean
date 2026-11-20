import SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreNearbyStalks
import SGPT.Foundations.Analysis.Pending.HironakaSmoothSubmersionGermIdealColon
import SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk

/-! Full actual structure-sheaf stalk to a fixed adapted chart. No coherence,
reducedness, or finite-generation hypothesis is imposed. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.HironakaG10AdaptedStalkIdeal
noncomputable section
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.HolomorphicIdealSheaves HolGerm BlowupFlatCoordinates
  HironakaSmoothSubmersionGermIdealColon HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreCoherentDomain
  HironakaHolomorphicJetRankLoci HironakaSmoothCentreRealDomainActualSheafStalk
  OkaRelationSheaf HironakaRelativeNormalCoherentTranslatedJets

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A holomorphic germ in the adapted chart becomes its original preferred
chart germ under the actual coordinate equivalence. -/
theorem nearby_equiv_adaptedGerm (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (f : M → ℂ) (hf : HolomorphicAt n f x) :
    actualNearbyGermEquiv Φ 0 (actualFlattening_target_zero_mem x Φ h0)
        (adaptedGerm x Φ h0 f hf) =
      chartTranslatedGerm x x (mem_chart_source _ x) f hf := by
  have h0T := actualFlattening_target_zero_mem x Φ h0
  have hInv := actualFlatteningInverseMap_zero x Φ h0
  have hfat : HolAt ((f ∘ actualFlatteningInverseMap x Φ) ∘ actualAffineTranslation n 0) 0 := by
    simpa only [actualAffineTranslation, zero_add, Function.comp_def, actualFlatteningInverseMap] using
      (holomorphic_adapted_iff x Φ h0 f).mpr hf
  have hfInv : HolomorphicAt n f (actualFlatteningInverseMap x Φ 0) := by rwa [hInv]
  have h := actualNearbyGermEquiv_original_function x Φ hsrc 0 h0T f hfInv hfat
  have hL : HolGerm.mk ((f ∘ actualFlatteningInverseMap x Φ) ∘ actualAffineTranslation n 0) hfat =
      adaptedGerm x Φ h0 f hf := by
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      simp only [Function.comp_def, actualAffineTranslation, zero_add, actualFlatteningInverseMap]
  have hInvFun : Φ.invFun 0 = chartAt (ComplexModel n) x x := by
    rw [← h0, Φ.left_inv _ Φ.center_mem_source]
  have hR : chartTranslatedGerm x (actualFlatteningInverseMap x Φ 0)
      (actualNearbyPoint_mem_chart_source x Φ hsrc 0 h0T) f hfInv =
      chartTranslatedGerm x x (mem_chart_source _ x) f hf := by
    unfold chartTranslatedGerm translatedGerm
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      rw [actualNearbyPoint_chart_value x Φ hsrc 0 h0T, hInvFun]
  exact (congrArg (actualNearbyGermEquiv Φ 0 h0T) hL.symm).trans (h.trans hR)

/-- The actual structure-sheaf stalk itself, expressed in the chosen adapted
coordinates, as a ring equivalence. -/
def adaptedStalkEquiv (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    actualComplexStructureStalk (n := n) x ≃+* HolGerm (ComplexModel n) :=
  (actualStalkChartEquiv (n := n) x).trans
    (actualNearbyGermEquiv Φ 0 (actualFlattening_target_zero_mem x Φ h0)).toRingEquiv.symm

/-- This equivalence takes the literal stalk germ of each original function to
its own literal adapted germ. -/
theorem adaptedStalkEquiv_originalFunctionGerm (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (f : M → ℂ) (hf : HolomorphicAt n f x) :
    adaptedStalkEquiv x Φ h0 (actualOriginalFunctionGerm x f hf) =
      adaptedGerm x Φ h0 f hf := by
  change (actualNearbyGermEquiv Φ 0 (actualFlattening_target_zero_mem x Φ h0)).symm
    (actualStalkChartEquiv (n := n) x (actualOriginalFunctionGerm x f hf)) = _
  rw [actualOriginalFunctionGerm_chart]
  apply (actualNearbyGermEquiv Φ 0 (actualFlattening_target_zero_mem x Φ h0)).injective
  rw [AlgEquiv.apply_symm_apply, nearby_equiv_adaptedGerm x Φ hsrc h0 f hf]

/-- The image of the ENTIRE actual stalk ideal is exactly the ENTIRE adapted
ideal of the same original germ ideal. -/
theorem map_actualWholeSheafStalkIdeal_adapted (I : GermIdeal n M) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) :
    Ideal.map (adaptedStalkEquiv x Φ h0).toRingHom (actualWholeSheafStalkIdeal I x) =
      adaptedIdeal I x Φ h0 := by
  simp only [actualWholeSheafStalkIdeal, adaptedIdeal, Ideal.map_span]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨f, hf, hmem, rfl⟩, rfl⟩
    exact ⟨f, hf, hmem, adaptedStalkEquiv_originalFunctionGerm x Φ hsrc h0 f hf⟩
  · rintro ⟨f, hf, hmem, rfl⟩
    exact ⟨actualOriginalFunctionGerm x f hf, ⟨f, hf, hmem, rfl⟩,
      adaptedStalkEquiv_originalFunctionGerm x Φ hsrc h0 f hf⟩


/-- Any pivot-saturated ideal in the adapted chart gives a regular pivot in
its literal structure-sheaf-stalk quotient. The ideal is transported whole,
with no reduction or coherence assumption. -/
theorem adaptedStalk_quotient_pivot_regular (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (N : Ideal (HolGerm (ComplexModel n))) (p : HolGerm (ComplexModel n))
    (hsat : ∀ g, p * g ∈ N → g ∈ N) :
    let E := adaptedStalkEquiv x Φ h0
    let N' := N.comap E.toRingHom
    IsRegular (Ideal.Quotient.mk N' (E.symm p)) := by
  dsimp only
  let E := adaptedStalkEquiv x Φ h0
  let N' := N.comap E.toRingHom
  have hsat' : ∀ g, E.symm p * g ∈ N' → g ∈ N' := by
    intro g hg
    change E (E.symm p * g) ∈ N at hg
    change E g ∈ N
    exact hsat (E g) (by simpa only [map_mul, RingEquiv.apply_symm_apply] using hg)
  change IsRegular (Ideal.Quotient.mk N' (E.symm p))
  rw [isRegular_iff_eq_zero_of_mul]
  have h : ∀ v : actualComplexStructureStalk (n := n) x ⧸ N',
      Ideal.Quotient.mk N' (E.symm p) * v = 0 → v = 0 := by
    intro v hv
    obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hv
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hsat' v hv
  exact ⟨h, fun v hv => h v (by rw [mul_comm]; exact hv)⟩

end
end SGPT.Unibranch.HironakaG10AdaptedStalkIdeal
