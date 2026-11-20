import SGPT.Trace.BertiniMovingEvaluations
import SGPT.Trace.BertiniNativeQuotientFamilyFrame
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual finite moving evaluation matrices produce genuine holomorphic coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

private theorem exists_holomorphic_evaluation_leftInverse {r : ℕ} {A : Type*} [Fintype A]
    (V : TopologicalSpace.Opens (ComplexModel 1))
    (M : V → ((Fin r → ℂ) →L[ℂ] (A → ℂ)))
    (hM : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, (Fin r → ℂ) →L[ℂ] (A → ℂ)) ∞ M)
    (t₀ : V) (h0 : Function.Injective (M t₀)) :
    ∃ (W : TopologicalSpace.Opens (ComplexModel 1)) (hWV : W ≤ V) (_ht₀ : t₀.val ∈ W)
      (J : W → ((A → ℂ) →L[ℂ] (Fin r → ℂ))),
      ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, (A → ℂ) →L[ℂ] (Fin r → ℂ)) ∞ J ∧
      ∀ (t : W) (c : Fin r → ℂ), J t (M (TopologicalSpace.Opens.inclusion hWV t) c) = c := by
  classical
  let D := (M t₀).toLinearMap.leftInverse.toContinuousLinearMap
  have hDM : D.comp (M t₀) = ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
    apply ContinuousLinearMap.ext
    intro c
    exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr h0) c
  let B : V → ((Fin r → ℂ) →L[ℂ] (Fin r → ℂ)) := fun t => D.comp (M t)
  have hB : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, (Fin r → ℂ) →L[ℂ] (Fin r → ℂ)) ∞ B :=
    contMDiff_const.clm_comp hM
  let O := B ⁻¹' Set.range ((↑) : ((Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ)) → _)
  have hO : IsOpen O := ContinuousLinearEquiv.isOpen.preimage hB.continuous
  have htO : t₀ ∈ O := ⟨ContinuousLinearEquiv.refl ℂ _,hDM.symm⟩
  let W : TopologicalSpace.Opens (ComplexModel 1) :=
    ⟨Subtype.val '' O,V.isOpen.isOpenMap_subtype_val _ hO⟩
  have hWV : W ≤ V := by rintro _ ⟨t,_,rfl⟩; exact t.property
  have htW : t₀.val ∈ W := ⟨t₀,htO,rfl⟩
  let inc : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) W V ∞ :=
    ⟨TopologicalSpace.Opens.inclusion hWV,contMDiff_inclusion hWV⟩
  have hInv (t : W) : (B (inc t)).IsInvertible := by
    obtain ⟨z,hz,heq⟩ := t.property
    have hz' : z = inc t := Subtype.ext heq
    exact hz' ▸ hz
  let J : W → ((A → ℂ) →L[ℂ] (Fin r → ℂ)) := fun t => (B (inc t)).inverse.comp D
  refine ⟨W,hWV,htW,J,?_,?_⟩
  · intro t
    have hi := (hInv t).contDiffAt_map_inverse.contMDiffAt.comp t
      ((hB.comp inc.contMDiff).contMDiffAt)
    exact hi.clm_comp contMDiffAt_const
  · intro t c
    exact (hInv t).inverse_apply_self c

private def evaluationColumnAssembly {r : ℕ} {A : Type*} [Fintype A] :
    (Fin r → (A → ℂ)) →L[ℂ] ((Fin r → ℂ) →L[ℂ] (A → ℂ)) :=
  LinearMap.toContinuousLinearMap {
    toFun b := LinearMap.toContinuousLinearMap {
      toFun c := ∑ j, c j • b j
      map_add' c d := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
      map_smul' a c := by simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply] }
    map_add' b c := by
      apply ContinuousLinearMap.ext
      intro a
      change (∑ j, a j • (b j + c j)) = (∑ j, a j • b j) + (∑ j, a j • c j)
      simp only [smul_add,Finset.sum_add_distrib]
    map_smul' a b := by
      apply ContinuousLinearMap.ext
      intro c
      change (∑ j, c j • (a • b j)) = a • (∑ j, c j • b j)
      simp only [Finset.smul_sum,smul_smul,mul_comm a] }

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem exists_actual_member_holomorphic_coefficient_extractor
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) (t₀ : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t₀.val 0 • v) (hsm t₀)
    letI := nativeBertiniMemberComplex p i (a - t₀.val 0 • v) (hsm t₀)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t₀.val 0 • v))).isCompact
    ∀ (r : ℕ) (T : Fin r → HolomorphicSections (n := d + 1)
      (familyNativePhysicalModel p i a v U hsm L).Fiber),
      (∀ c : Fin r → ℂ, familyNativeMemberAdjunctionSection p i a v U hsm L t₀
        (∑ j, c j • T j) = 0 → c = 0) →
      ∃ (W : TopologicalSpace.Opens (ComplexModel 1)) (_hWU : W ≤ U) (ht₀ : t₀.val ∈ W)
        (A : Finset (member p (affinePoint i (a - t₀.val 0 • v))))
        (e : A → AtlasFrame (familyNativePhysicalModel p i a v U hsm L))
        (g : A → ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (d + 1))
          W (familyIncidence p i a v U) ∞)
        (J : W → ((A → ℂ) →L[ℂ] (Fin r → ℂ)))
        (_he : ∀ (y : A) (t : W), g y t ∈ (e y).val.baseSet),
        (∀ y : A, g y ⟨t₀.val,ht₀⟩ = ⟨(t₀,y.val.val),y.val.property⟩) ∧
        (∀ (y : A) (t : W), (g y t).val.1.val = t.val) ∧
        ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, (A → ℂ) →L[ℂ] (Fin r → ℂ)) ∞ J ∧
        ∃ (C : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber →ₗ[ℂ]
          (W → Fin r → ℂ)),
        (∀ F t, C F t = J t (fun y => ((e y).val ⟨g y t,F (g y t)⟩).2)) ∧
        (∀ F, ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, Fin r → ℂ) ∞ (C F)) ∧
        (∀ (c : Fin r → ℂ) (t : W), C (∑ j, c j • T j) t = c) ∧
        ∀ (F : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber) (t : W),
          (∃ c : Fin r → ℂ, ∀ q : familyIncidence p i a v U,
            q.val.1.val = t.val → F q = ∑ j, c j • T j q) →
          ∀ q : familyIncidence p i a v U, q.val.1.val = t.val →
            F q = ∑ j, (C F t) j • T j q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t₀.val 0 • v) (hsm t₀)
  let := nativeBertiniMemberComplex p i (a - t₀.val 0 • v) (hsm t₀)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t₀.val 0 • v))).isCompact
  classical
  intro r T hInd
  let B := familyNativePhysicalModel p i a v U hsm L
  let H := HolomorphicSections (n := d + 1) B.Fiber
  have hsum_eval (c : Fin r → ℂ) (q : familyIncidence p i a v U) :
      (∑ j, c j • T j) q = ∑ j, c j • T j q := by
    change ((ContMDiffSection.coeAddHom 𝓘(ℂ, ComplexModel (d + 1)) ℂ ∞ B.Fiber)
      (∑ j, c j • T j)) q = _
    rw [map_sum]
    simp only [Finset.sum_apply,ContMDiffSection.coeAddHom_apply]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  obtain ⟨A,e,he,hA,V,hVU,htV,g,hg,_⟩ := exists_finite_member_movingEvaluations p i a v U hsm L t₀
  let O : Set V := ⋂ y : A, (g y) ⁻¹' (e y).val.baseSet
  have hO : IsOpen O := isOpen_iInter_of_finite fun y =>
    (e y).val.open_baseSet.preimage (g y).contMDiff.continuous
  have htO : (⟨t₀.val,htV⟩ : V) ∈ O := by
    apply mem_iInter.mpr
    intro y
    change g y ⟨t₀.val,htV⟩ ∈ (e y).val.baseSet
    rw [(hg y).1]
    exact he y
  let V₁ : TopologicalSpace.Opens (ComplexModel 1) :=
    ⟨Subtype.val '' O,V.isOpen.isOpenMap_subtype_val _ hO⟩
  have hV₁V : V₁ ≤ V := by rintro _ ⟨z,_,rfl⟩; exact z.property
  have htV₁ : t₀.val ∈ V₁ := ⟨⟨t₀.val,htV⟩,htO,rfl⟩
  let inc₁ : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) V₁ V ∞ :=
    ⟨TopologicalSpace.Opens.inclusion hV₁V,contMDiff_inclusion hV₁V⟩
  let g₁ (y : A) := (g y).comp inc₁
  have hframe (t : V₁) (y : A) : g₁ y t ∈ (e y).val.baseSet := by
    obtain ⟨z,hz,heq⟩ := t.property
    have hz' : z = inc₁ t := Subtype.ext heq
    have hmem := mem_iInter.mp hz y
    change g y (inc₁ t) ∈ (e y).val.baseSet
    rw [← hz']
    exact hmem
  have hproj (t : V₁) (y : A) : (g₁ y t).val.1.val = t.val := (hg y).2 (inc₁ t)
  have hbase (y : A) : g₁ y ⟨t₀.val,htV₁⟩ = ⟨(t₀,y.val.val),y.val.property⟩ := (hg y).1
  let E (t : V₁) : H →ₗ[ℂ] (A → ℂ) := {
    toFun F := fun y => ((e y).val.linearEquivAt ℂ (g₁ y t) (hframe t y)) (F (g₁ y t))
    map_add' F G := by
      ext y
      change ((e y).val.linearEquivAt ℂ _ _) (F (g₁ y t) + G (g₁ y t)) = _
      exact map_add _ _ _
    map_smul' c F := by
      ext y
      change ((e y).val.linearEquivAt ℂ _ _) (c • F (g₁ y t)) = _
      exact map_smul _ _ _ }
  have hE (F : H) : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, A → ℂ) ∞ (fun t => E t F) := by
    apply contMDiff_pi_space.mpr
    intro y t
    exact contMDiffAt_nativeSection_movingPointCoefficient B (e y) F V₁ (g₁ y) t (hframe t y)
  let comb : (Fin r → ℂ) →ₗ[ℂ] H :=
    ∑ j, (LinearMap.proj j : (Fin r → ℂ) →ₗ[ℂ] ℂ).smulRight (T j)
  have hcomb (c : Fin r → ℂ) : comb c = ∑ j, c j • T j := by
    simp [comb]
  let M : V₁ → ((Fin r → ℂ) →L[ℂ] (A → ℂ)) := fun t => ((E t).comp comb).toContinuousLinearMap
  have hM : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, (Fin r → ℂ) →L[ℂ] (A → ℂ)) ∞ M := by
    have heq : M = fun t => evaluationColumnAssembly (fun j => E t (T j)) := by
      funext t
      ext c y
      change (E t (comb c)) y = (∑ j, c j • E t (T j)) y
      rw [hcomb]
      rw [map_sum]
      simp only [map_smul]
    rw [heq]
    exact evaluationColumnAssembly.contMDiff.comp (contMDiff_pi_space.mpr fun j => hE (T j))
  have hM0 : Function.Injective (M ⟨t₀.val,htV₁⟩) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    apply hInd c
    apply hA
    intro y
    rw [memberFamilyFrameEvaluation_familyImage]
    have hcy := congrFun hc y
    change E ⟨t₀.val,htV₁⟩ (comb c) y = 0 at hcy
    rw [hcomb] at hcy
    change ((e y).val.linearEquivAt ℂ (g₁ y ⟨t₀.val,htV₁⟩) (hframe ⟨t₀.val,htV₁⟩ y))
      ((∑ j, c j • T j) (g₁ y ⟨t₀.val,htV₁⟩)) = 0 at hcy
    change ((e y).val ⟨g₁ y ⟨t₀.val,htV₁⟩,(∑ j, c j • T j) (g₁ y ⟨t₀.val,htV₁⟩)⟩).2 = 0 at hcy
    rw [hbase y] at hcy
    exact hcy
  obtain ⟨W,hWV₁,htW,J,hJ,hJM⟩ := exists_holomorphic_evaluation_leftInverse V₁ M hM ⟨t₀.val,htV₁⟩ hM0
  let inc : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) W V₁ ∞ :=
    ⟨TopologicalSpace.Opens.inclusion hWV₁,contMDiff_inclusion hWV₁⟩
  let C : H →ₗ[ℂ] (W → Fin r → ℂ) := {
    toFun F := fun t => J t (E (inc t) F)
    map_add' F G := by ext t j; simp only [map_add,Pi.add_apply]
    map_smul' c F := by ext t j; simp only [map_smul,Pi.smul_apply,RingHom.id_apply] }
  let gW (y : A) := (g₁ y).comp inc
  refine ⟨W,(hWV₁.trans hV₁V).trans hVU,htW,A,e,gW,J,
    (fun y t => hframe (inc t) y),(fun y => hbase y),
    (fun y t => hproj (inc t) y),hJ,C,?_,?_,?_,?_⟩
  · intro F t
    rfl
  · intro F
    exact hJ.clm_apply ((hE F).comp inc.contMDiff)
  · intro c t
    change J t (E (inc t) (∑ j, c j • T j)) = c
    rw [← hcomb]
    exact hJM t c
  · intro F t hLanding q hqt
    obtain ⟨c,hc⟩ := hLanding
    have hEval : E (inc t) F = M (inc t) c := by
      ext y
      have hq := hc (g₁ y (inc t)) (hproj (inc t) y)
      change (E (inc t) F) y = (E (inc t) (comb c)) y
      rw [hcomb]
      change ((e y).val.linearEquivAt ℂ (g₁ y (inc t)) (hframe (inc t) y))
        (F (g₁ y (inc t))) = _
      rw [hq]
      change _ = ((e y).val.linearEquivAt ℂ (g₁ y (inc t)) (hframe (inc t) y))
        ((∑ j, c j • T j) (g₁ y (inc t)))
      exact congrArg ((e y).val.linearEquivAt ℂ (g₁ y (inc t)) (hframe (inc t) y))
        (hsum_eval c (g₁ y (inc t))).symm
    have hC : C F t = c := by
      change J t (E (inc t) F) = c
      rw [hEval]
      exact hJM t c
    rw [hC]
    exact hc q hqt

end SGPT.Trace.BertiniFamilyCanonical
