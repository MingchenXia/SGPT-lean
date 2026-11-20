import SGPT.Unibranch.PrimeNov16AnalyticNormalizationNormalColon
import SGPT.Foundations.Analysis.Pending.HironakaRelativeNormalAnalyticGraphQuotient
import SGPT.Foundations.Analysis.Pending.CoherentIdealColon

/-! Whole ORIGINAL coherent product/colon dictionaries, not supplier fields.
Blueprint: prime-nov16-analytic-normalization-coherent-colon-dictionary.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open HolGerm OkaRelationSheaf
open SGPT.Foundations.Analysis.Pending.HironakaRelativeNormalDeformationInitialRelations
open SGPT.Foundations.Analysis.Pending.HironakaRelativeNormalAnalyticGraphQuotient
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentColonDictionary

theorem originalOriginIdeal_colon {n : ℕ} (I J : GermIdeal n (ComplexModel n))
    (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    originalCoherentOriginIdeal (InvertibleIdealQuotient.colon I J) =
      (originalCoherentOriginIdeal I).colon (originalCoherentOriginIdeal J : Set (HolGerm (ComplexModel n))) := by
  have hcolon := CoherentIdealColon.isCoherent_colon_of_isCoherent hI hJ
  ext a
  obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk a
  rw [mk_mem_originalCoherentOriginIdeal_iff _ hcolon hf]
  constructor
  · intro hfc
    apply Submodule.mem_colon.mpr
    intro b hb
    obtain ⟨g,hg,rfl⟩ := HolGerm.exists_eq_mk b
    have hJg := (mk_mem_originalCoherentOriginIdeal_iff J hJ hg).mp hb
    have hprod := (mk_mem_originalCoherentOriginIdeal_iff I hI (eventually_differentiableAt_mul hg hf)).mpr (hfc.2 g hJg)
    rw [HolGerm.mk_mul g f hg hf] at hprod
    simpa only [smul_eq_mul,mul_comm] using hprod
  · intro hfc
    refine ⟨hf.mono (fun _ h => h.mdifferentiableAt),?_⟩
    intro g hg
    have hgh := (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hg).mono fun _ h => h.differentiableAt
    have hgm := (mk_mem_originalCoherentOriginIdeal_iff J hJ hgh).mpr hg
    have hprod := (Submodule.mem_colon.mp hfc) (HolGerm.mk g hgh) hgm
    apply (mk_mem_originalCoherentOriginIdeal_iff I hI (eventually_differentiableAt_mul hgh hf)).mp
    rw [HolGerm.mk_mul g f hgh hf]
    simpa only [smul_eq_mul,mul_comm] using hprod

theorem originalOriginIdeal_product {n : ℕ} (I J : GermIdeal n (ComplexModel n))
    (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    originalCoherentOriginIdeal (I.mul J) = originalCoherentOriginIdeal I*originalCoherentOriginIdeal J := by
  have hprod := IdealWeightPowers.isCoherent_mul hI hJ
  apply le_antisymm
  · intro a ha
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk a
    have hfm := (mk_mem_originalCoherentOriginIdeal_iff _ hprod hf).mp ha
    let S : (ComplexModel n → ℂ) → Prop := fun t => ∃ p q,I.mem 0 p ∧ J.mem 0 q ∧ t=p*q
    have hS : ∀ t,S t → HolAt t 0 := by
      rintro t ⟨p,q,hp,hq,rfl⟩
      exact ((RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hp).mul
        (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hq)).mono fun _ h => h.differentiableAt
    apply whole_origin_span_mem _ S hS ?_ hf hfm
    rintro t ⟨p,q,hp,hq,rfl⟩
    have hph := (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hp).mono fun _ h => h.differentiableAt
    have hqh := (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hq).mono fun _ h => h.differentiableAt
    have hm := Ideal.mul_mem_mul ((mk_mem_originalCoherentOriginIdeal_iff I hI hph).mpr hp)
      ((mk_mem_originalCoherentOriginIdeal_iff J hJ hqh).mpr hq)
    change HolGerm.mk (fun z => p z*q z) (eventually_differentiableAt_mul hph hqh) ∈ _
    rw [HolGerm.mk_mul p q hph hqh]
    exact hm
  · apply Ideal.mul_le.mpr
    intro a ha b hb
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk a
    obtain ⟨g,hg,rfl⟩ := HolGerm.exists_eq_mk b
    have hfI := (mk_mem_originalCoherentOriginIdeal_iff I hI hf).mp ha
    have hgJ := (mk_mem_originalCoherentOriginIdeal_iff J hJ hg).mp hb
    rw [← HolGerm.mk_mul f g hf hg]
    apply (mk_mem_originalCoherentOriginIdeal_iff _ hprod (eventually_differentiableAt_mul hf hg)).mpr
    refine ⟨(eventually_differentiableAt_mul hf hg).mono (fun _ h => h.mdifferentiableAt),1,fun _ => f*g,
      fun _ _ => 1,fun _ => ⟨f,g,hfI,hgJ,rfl⟩,fun _ => holomorphicAt_const 1,?_⟩
    exact Eventually.of_forall fun z => by simp

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentColonDictionary
