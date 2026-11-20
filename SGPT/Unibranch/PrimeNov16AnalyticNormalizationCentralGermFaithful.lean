import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphDensity
import SGPT.Foundations.Analysis.Pending.IrreducibleGermLocal

/-! Actual central graph pullback is faithful on original base germs.
Blueprint: prime-nov16-analytic-normalization-central-germ-faithful.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralGermFaithful
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGoodIso

/-- Continuity is read from the already INTERNALLY constructed actual
full-LRS good inverse for the full ambient carrier. -/
theorem rationalSection_continuous {n k : ℕ} (U : Opens (ComplexModel n))
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U) :
    Continuous (fun x : goodBase U H hH => (rationalSection U H hH G x).val) := by
  let e := goodIso U (show IsComplexAnalyticSubset (n := n) (univ : Set U) from
    isComplexAnalyticSubset_univ) H G hH hG
  let lift : goodBase U H hH → ((Subtype.val : goodBase U H hH → U) ⁻¹' (univ : Set U)) :=
    fun x => ⟨x,mem_univ _⟩
  have hlift : Continuous lift := continuous_id.subtype_mk _
  exact continuous_subtype_val.comp
    (continuous_subtype_val.comp (e.hom.base.hom.continuous.comp hlift))

theorem rationalSection_base {n k : ℕ} (U : Opens (ComplexModel n))
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (x : goodBase U H hH) :
    baseProjection n k (rationalSection U H hH G x).val.val = x.val.val := by
  exact congrArg Prod.fst ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).apply_symm_apply
    (x.val.val,rationalVector H G x.val.val))

theorem rationalSection_eq_of_graph {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (q : wideDomain k U)
    (hq : q ∈ rationalGraph U C H G) (hqH : H (baseProjection n k q.val) ≠ 0) :
    (rationalSection U H hH G ⟨basePoint U q,hqH⟩).val = q := by
  apply Subtype.ext
  apply PrimeNov16AnalyticNormalizationGraphFinite.coordinates_injective
  · exact rationalSection_base U H G hH _
  · change ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ))
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℂ)).symm
        (baseProjection n k q.val,rationalVector H G (baseProjection n k q.val)))).2 = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    ext i
    change G i (baseProjection n k q.val)/H (baseProjection n k q.val) = fibreProjection n k q.val i
    exact (div_eq_iff hqH).mpr
      (((mem_denominatorSet U C H G q).mp hq.1).2 i |>.symm.trans (mul_comm _ _))

theorem original_germ_zero_of_central_graph_pullback_zero {n k : ℕ}
    {Z : Set (ComplexModel n)} (hZ : AnalyticGermDecomposition.IsIrreducibleGerm Z)
    (U : Opens (ComplexModel n))
    (hC : IsComplexAnalyticSubset (n := n) {x : U | x.val ∈ Z})
    (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (hH : DifferentiableOn ℂ H U) (hG : ∀ i,DifferentiableOn ℂ (G i) U)
    (p : graphClosure U {x : U | x.val ∈ Z} H G)
    (hp : baseProjection n k p.val.val = 0)
    (F : ComplexModel n → ℂ) (hF : ∀ᶠ x in 𝓝 0,DifferentiableAt ℂ F x)
    (hzero : ∀ᶠ z in 𝓝 p.val,z ∈ graphClosure U {x : U | x.val ∈ Z} H G →
      F (baseProjection n k z.val) = 0) :
    ∀ᶠ x in 𝓝 (0 : ComplexModel n),x ∈ Z → F x = 0 := by
  by_contra hnot
  obtain ⟨Ω,hΩ,h0Ω,hthin⟩ := IrreducibleGermLocal.exists_thin_nhds hZ
    (AnalyticGermDecomposition.isAnalyticGerm_zeroSet hF) hnot
  obtain ⟨O,hOsub,hO,hpO⟩ := mem_nhds_iff.mp hzero
  have hbase : Continuous (fun z : wideDomain k U => baseProjection n k z.val) :=
    (baseProjection n k).continuous.comp continuous_subtype_val
  have hpΩ : baseProjection n k p.val.val ∈ Ω := hp.symm ▸ h0Ω
  obtain ⟨q,hq,hqΓ⟩ := mem_closure_iff.mp p.property
    (O ∩ (fun z : wideDomain k U => baseProjection n k z.val) ⁻¹' Ω)
    (hO.inter (hΩ.preimage hbase)) ⟨hpO,hpΩ⟩
  have hqH : H (baseProjection n k q.val) ≠ 0 :=
    fun he => hqΓ.2 ((mem_badSet U H q).mpr he)
  have hqZ := ((mem_denominatorSet U {x : U | x.val ∈ Z} H G q).mp hqΓ.1).1
  let x : goodBase U H hH := ⟨basePoint U q,hqH⟩
  let σ : goodBase U H hH → wideDomain k U := fun u => (rationalSection U H hH G u).val
  have hσ : Continuous σ := rationalSection_continuous U H G hH hG
  have hσx : σ x = q := rationalSection_eq_of_graph U _ H G hH q hqΓ hqH
  let V : Set (goodBase U H hH) := σ ⁻¹' O
  have hV : IsOpen V := hO.preimage hσ
  have hxV : x ∈ V := by change σ x ∈ O; rw [hσx]; exact hq.1
  let native : goodBase U H hH → ComplexModel n := fun u => u.val.val
  have hn : IsOpenMap native := U.isOpen.isOpenMap_subtype_val.comp
    (goodBase U H hH).isOpen.isOpenMap_subtype_val
  obtain ⟨y,hy,hyF⟩ := hthin (native '' V) (hn V hV)
    ⟨baseProjection n k q.val,⟨⟨x,hxV,rfl⟩,hqZ,hq.2⟩⟩
  obtain ⟨u,huV,huY⟩ := hy.1
  change u.val.val = y at huY
  have huC : u.val ∈ {x : U | x.val ∈ Z} := by
    change u.val.val ∈ Z
    rw [huY]
    exact hy.2.1
  have hσC : σ u ∈ graphClosure U {x : U | x.val ∈ Z} H G :=
    ((goodIso U hC H G hH hG).hom.base ⟨u,huC⟩).property
  have hFu : F (baseProjection n k (σ u).val) = 0 := hOsub huV hσC
  have hbaseσ : baseProjection n k (σ u).val = u.val.val := rationalSection_base U H G hH u
  apply hyF
  change F y = 0
  rw [← huY,← hbaseσ]
  exact hFu

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralGermFaithful
