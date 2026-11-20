import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralGermFaithful
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphOriginalStalk

/-! Exact ORIGINAL germ coefficient kernel at every actual central graph point.
Blueprint: prime-nov16-analytic-normalization-central-stalk-injective.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HolGerm GermAlgebraicParametrization RegularLocusDense
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralStalkInjective
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphStalkFinite
open PrimeNov16AnalyticNormalizationStalkCalculus
open PrimeNov16AnalyticNormalizationGraphOriginalStalk

theorem stalkStructureMap_eq_zero_iff {d m : ℕ} (C : Set (ComplexModel m))
    (p : C) (f : HolGerm (ComplexModel d)) :
    stalkStructureMap C p d f = 0 ↔ projGerm m d f ∈
      AnalyticGermDecomposition.vanishingIdeal {v : ComplexModel m | v+p.val ∈ C} := by
  constructor
  · intro hf
    have he := congrArg (translatedStalkEquiv C p) hf
    change (translatedStalkEquiv C p) ((translatedStalkEquiv C p).symm
      (Ideal.Quotient.mk _ (projGerm m d f))) = _ at he
    rw [RingEquiv.apply_symm_apply,map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  · intro hf
    change (translatedStalkEquiv C p).symm (Ideal.Quotient.mk _ (projGerm m d f)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf,map_zero]

theorem native_central_kernel_iff {n k : ℕ}
    {Z : Set (ComplexModel n)} (hZ : AnalyticGermDecomposition.IsIrreducibleGerm Z)
    (U : Opens (ComplexModel n))
    (hC : IsComplexAnalyticSubset (n := n) {x : U | x.val ∈ Z})
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (p : graphClosure U {x : U | x.val ∈ Z} H G)
    (hp : baseProjection n k p.val.val = 0) (f : HolGerm (ComplexModel n)) :
    stalkStructureMap (nativeCarrier U {x : U | x.val ∈ Z} H G)
      (nativePoint U {x : U | x.val ∈ Z} H G p) n f = 0 ↔
      f ∈ AnalyticGermDecomposition.vanishingIdeal Z := by
  rw [stalkStructureMap_eq_zero_iff]
  obtain ⟨F,hF,rfl⟩ := HolGerm.exists_eq_mk f
  rw [projGerm_mk,AnalyticGermDecomposition.mem_vanishingIdeal_mk,
    AnalyticGermDecomposition.mem_vanishingIdeal_mk]
  change (∀ᶠ v in 𝓝 (0 : ComplexModel (n+k)),
    v+p.val.val ∈ nativeCarrier U {x : U | x.val ∈ Z} H G →
      F (coordinateProjection (n+k) n v) = 0) ↔
    ∀ᶠ x in 𝓝 (0 : ComplexModel n),x ∈ Z → F x = 0
  constructor
  · intro hvan
    apply PrimeNov16AnalyticNormalizationCentralGermFaithful.original_germ_zero_of_central_graph_pullback_zero
      hZ U hC H G hH hG p hp F hF
    have ht : Tendsto (fun z : wideDomain k U => z.val-p.val.val)
        (𝓝 p.val) (𝓝 (0 : ComplexModel (n+k))) := by
      simpa only [sub_self] using
        (show Continuous (fun z : wideDomain k U => z.val-p.val.val) from
          continuous_subtype_val.sub continuous_const).tendsto p.val
    filter_upwards [ht.eventually hvan] with z hz hzS
    have hzN : z.val ∈ nativeCarrier U {x : U | x.val ∈ Z} H G := ⟨z,hzS,rfl⟩
    have he := hz (by simpa only [sub_add_cancel] using hzN)
    rw [← baseProjection_coordinateProjection,map_sub,hp,sub_zero] at he
    exact he
  · intro hvan
    have ht : Tendsto (coordinateProjection (n+k) n)
        (𝓝 (0 : ComplexModel (n+k))) (𝓝 (0 : ComplexModel n)) := by
      simpa only [map_zero] using (coordinateProjection (n+k) n).continuous.tendsto 0
    filter_upwards [ht.eventually hvan] with v hv hvN
    obtain ⟨z,hzS,hzv⟩ := hvN
    have hzZ := (graphClosure_subset_denominatorSet U hC H G hH hG hzS).1
    have he : baseProjection n k z.val = coordinateProjection (n+k) n v := by
      rw [hzv,map_add,hp,add_zero,baseProjection_coordinateProjection]
    change baseProjection n k z.val ∈ Z at hzZ
    rw [he] at hzZ
    exact hv hzZ

/-- The SAME original germ quotient embeds into the SAME original graph
stalk, with the actual open-restriction equivalence internally constructed. -/
def centralBaseMap {n k : ℕ}
    {Z : Set (ComplexModel n)} (hZ : AnalyticGermDecomposition.IsIrreducibleGerm Z)
    (U : Opens (ComplexModel n))
    (hC : IsComplexAnalyticSubset (n := n) {x : U | x.val ∈ Z})
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (p : graphClosure U {x : U | x.val ∈ Z} H G)
    (hp : baseProjection n k p.val.val = 0) :
    (HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z) →+*
      ((HironakaActualAnalyticSubspace.actualSubspaceSheaf (n := n+k)
        (graphClosure U {x : U | x.val ∈ Z} H G)).presheaf.stalk p).carrier :=
  (nativeOriginalStalkEquiv U {x : U | x.val ∈ Z} H G p).toRingHom.comp
    (Ideal.Quotient.lift _
      (stalkStructureMap (nativeCarrier U {x : U | x.val ∈ Z} H G)
        (nativePoint U {x : U | x.val ∈ Z} H G p) n)
      (fun f hf => (native_central_kernel_iff hZ U hC H G hH hG p hp f).mpr hf))

theorem centralBaseMap_injective {n k : ℕ}
    {Z : Set (ComplexModel n)} (hZ : AnalyticGermDecomposition.IsIrreducibleGerm Z)
    (U : Opens (ComplexModel n))
    (hC : IsComplexAnalyticSubset (n := n) {x : U | x.val ∈ Z})
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (p : graphClosure U {x : U | x.val ∈ Z} H G)
    (hp : baseProjection n k p.val.val = 0) :
    Function.Injective (centralBaseMap hZ U hC H G hH hG p hp) := by
  apply (nativeOriginalStalkEquiv U {x : U | x.val ∈ Z} H G p).injective.comp
  apply RingHom.lift_injective_of_ker_le_ideal
  intro f hf
  exact (native_central_kernel_iff hZ U hC H G hH hG p hp f).mp hf

theorem centralBaseMap_finite {n k : ℕ}
    {Z : Set (ComplexModel n)} (hZ : AnalyticGermDecomposition.IsIrreducibleGerm Z)
    (U : Opens (ComplexModel n))
    (hC : IsComplexAnalyticSubset (n := n) {x : U | x.val ∈ Z})
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (p : graphClosure U {x : U | x.val ∈ Z} H G)
    (hp : baseProjection n k p.val.val = 0)
    (d : Fin k → ℕ) (a : Fin k → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < d i → DifferentiableOn ℂ (a i j) U)
    (hmonic : ∀ x : {x : U | x.val ∈ Z},H x.val.val ≠ 0 → ∀ i,
      GermParametrizationData.monicEval (d i) (a i) x.val.val (G i x.val.val/H x.val.val) = 0) :
    (centralBaseMap hZ U hC H G hH hG p hp).Finite := by
  apply RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (AnalyticGermDecomposition.vanishingIdeal Z))
  have he : (centralBaseMap hZ U hC H G hH hG p hp).comp
      (Ideal.Quotient.mk (AnalyticGermDecomposition.vanishingIdeal Z)) =
      graphStalkStructureMap U {x : U | x.val ∈ Z} H G p := by
    ext f
    rfl
  rw [he]
  exact graphStalkStructureMap_finite U _ H G d a ha hmonic p

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralStalkInjective
