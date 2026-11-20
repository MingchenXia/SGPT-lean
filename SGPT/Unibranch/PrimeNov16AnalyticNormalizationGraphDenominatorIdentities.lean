import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkFunctions

/-! Actual full-stalk denominator identities from the literal whole carrier.
Blueprint: prime-nov16-analytic-normalization-graph-denominator-identities.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm GermAlgebraicParametrization RegularLocusDense
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphDenominatorIdentities
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphStalkFinite
open PrimeNov16AnalyticNormalizationStalkCalculus
open PrimeNov16AnalyticNormalizationGraphOriginalStalk
open PrimeNov16AnalyticNormalizationGraphStalkCoordinates

theorem graphGermMap_eq_zero_iff {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G) (f : HolGerm (ComplexModel (n+k))) :
    graphGermMap U C H G p f = 0 ↔ f ∈ AnalyticGermDecomposition.vanishingIdeal
      {v : ComplexModel (n+k) | v+p.val.val ∈ nativeCarrier U C H G} := by
  change nativeOriginalStalkEquiv U C H G p
    ((translatedStalkEquiv (nativeCarrier U C H G) (nativePoint U C H G p)).symm
      (Ideal.Quotient.mk _ f)) = 0 ↔ _
  rw [map_eq_zero_iff _ (nativeOriginalStalkEquiv U C H G p).injective,
    map_eq_zero_iff _ (translatedStalkEquiv (nativeCarrier U C H G) (nativePoint U C H G p)).symm.injective,
    Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem graphGermMap_constant {n k : ℕ} (U : Opens (ComplexModel n)) (C : Set U)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G) (c : ℂ) :
    graphGermMap U C H G p (HolGerm.constHom c) =
      graphStalkStructureMap U C H G p (HolGerm.constHom c) := rfl

theorem graph_fibre_denominator_identity {n k : ℕ} (U : Opens (ComplexModel n)) {C : Set U}
    (hC : IsComplexAnalyticSubset (n := n) C)
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (hH0 : ∀ᶠ x in 𝓝 0,DifferentiableAt ℂ H x)
    (hG0 : ∀ i,∀ᶠ x in 𝓝 0,DifferentiableAt ℂ (G i) x)
    (p : graphClosure U C H G) (hp : baseProjection n k p.val.val = 0) (i : Fin k) :
    graphStalkStructureMap U C H G p (HolGerm.mk H hH0) *
      (graphCoordinate U C H G p (Fin.natAdd n i) +
        graphStalkStructureMap U C H G p (HolGerm.constHom (p.val.val (Fin.natAdd n i)))) =
      graphStalkStructureMap U C H G p (HolGerm.mk (G i) (hG0 i)) := by
  let idx := Fin.natAdd n i
  let c := p.val.val idx
  let Y : ComplexModel (n+k) → ℂ := fun v => v idx+c
  have hY : ∀ᶠ v in 𝓝 (0 : ComplexModel (n+k)),DifferentiableAt ℂ Y v :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj (𝕜 := ℂ) idx).differentiableAt.add_const c
  have hHY := eventually_differentiableAt_comp_clm (coordinateProjection (n+k) n) hH0
  have hGY := eventually_differentiableAt_comp_clm (coordinateProjection (n+k) n) (hG0 i)
  have hraw := eventually_differentiableAt_sub (eventually_differentiableAt_mul hHY hY) hGY
  have hYg : coord idx+HolGerm.constHom c = HolGerm.mk Y hY := by
    rw [← HolGerm.mk_const]
    exact (HolGerm.mk_add _ _ _ _).symm
  have hrawg : projGerm (n+k) n (HolGerm.mk H hH0) * (coord idx+HolGerm.constHom c) -
      projGerm (n+k) n (HolGerm.mk (G i) (hG0 i)) =
      HolGerm.mk (fun v => H (coordinateProjection (n+k) n v)*Y v-G i (coordinateProjection (n+k) n v)) hraw := by
    rw [hYg,projGerm_mk,projGerm_mk]
    exact (HolGerm.mk_sub _ _ (eventually_differentiableAt_mul hHY hY) hGY).symm
  have hzero : graphGermMap U C H G p
      (projGerm (n+k) n (HolGerm.mk H hH0) * (coord idx+HolGerm.constHom c) -
        projGerm (n+k) n (HolGerm.mk (G i) (hG0 i))) = 0 := by
    apply (graphGermMap_eq_zero_iff U C H G p _).mpr
    rw [hrawg,AnalyticGermDecomposition.mem_vanishingIdeal_mk]
    apply Eventually.of_forall
    intro v hv
    obtain ⟨z,hz,hzv⟩ := hv
    have he := ((mem_denominatorSet U C H G z).mp
      (graphClosure_subset_denominatorSet U hC H G hH hG hz)).2 i
    have hb : baseProjection n k z.val = coordinateProjection (n+k) n v := by
      rw [hzv,map_add,hp,add_zero,baseProjection_coordinateProjection]
    have hw : fibreProjection n k z.val i = Y v := by
      rw [fibreProjection_coordinate,hzv]
      rfl
    rw [hb,hw] at he
    exact sub_eq_zero.mpr he
  rw [map_sub,map_mul,map_add,graphGermMap_base_square,graphGermMap_base_square,
    graphGermMap_constant] at hzero
  exact sub_eq_zero.mp hzero

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphDenominatorIdentities
