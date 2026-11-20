import SGPT.Trace.BertiniNativeMovingCoefficients
import SGPT.Trace.BertiniNativeBaseFrameCoefficients

/-! Geometry selected BEFORE every actual small domain and EVERY genuine small section. -/
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

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem exists_actual_small_member_holomorphic_coefficient_extractor
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
      ∃ (W : TopologicalSpace.Opens (ComplexModel 1)) (hWU : W ≤ U) (_ht₀ : t₀.val ∈ W),
        ∀ (V : TopologicalSpace.Opens (ComplexModel 1)) (hVW : V ≤ W),
        let hVU := hVW.trans hWU
        letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
        letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
        ∃ C : HolomorphicSections (n := d + 1)
            (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber →ₗ[ℂ]
            (V → Fin r → ℂ),
          (∀ F, ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, Fin r → ℂ) ∞ (C F)) ∧
          (∀ (c : Fin r → ℂ) (t : V),
            C (familyPhysicalBaseRestriction p i a v U V hVU hsm L (∑ j, c j • T j)) t = c) ∧
          ∀ (F : HolomorphicSections (n := d + 1)
            (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber)
            (t : V),
            (∃ c : Fin r → ℂ, ∀ q : familyIncidence p i a v V,
              q.val.1.val = t.val → F q = ∑ j, c j • T j (familyBaseInclusion p i a v U V hVU q)) →
            ∀ q : familyIncidence p i a v V, q.val.1.val = t.val →
              F q = ∑ j, (C F t) j • T j (familyBaseInclusion p i a v U V hVU q) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t₀.val 0 • v) (hsm t₀)
  let := nativeBertiniMemberComplex p i (a - t₀.val 0 • v) (hsm t₀)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t₀.val 0 • v))).isCompact
  classical
  intro r T hInd
  obtain ⟨W,hWU,htW,A,e,g,J,he,hg0,hgp,hJ,C₀,hC₀,hC₀holo,hC₀norm,_⟩ :=
    exists_actual_member_holomorphic_coefficient_extractor p i a v U hsm L t₀ r T hInd
  refine ⟨W,hWU,htW,?_⟩
  intro V hVW
  let hVU := hVW.trans hWU
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  let B := familyNativePhysicalModel p i a v U hsm L
  let H := HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v V hsV L).Fiber
  let inc : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) V W ∞ :=
    ⟨TopologicalSpace.Opens.inclusion hVW,contMDiff_inclusion hVW⟩
  let gTube (y : A) : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (d + 1))
      V (familyBaseTube p i a v U V) ∞ :=
    ⟨fun t => ⟨g y (inc t),by
        change (g y (inc t)).val.1.val ∈ V
        rw [hgp y (inc t)]
        exact t.property⟩,
      (ContMDiff.subtypeVal_comp_iff (familyBaseTube p i a v U V) _).mp
        ((g y).contMDiff.comp inc.contMDiff)⟩
  let gs (y : A) := (nativeFamilyBaseTubeInverse p i a v U V hVU hsm).comp (gTube y)
  have hpoint (y : A) (t : V) : familyBaseInclusion p i a v U V hVU (gs y t) = g y (inc t) := rfl
  have hparam (y : A) (t : V) : (gs y t).val.1.val = t.val := hgp y (inc t)
  have he' (y : A) (t : V) : familyBaseInclusion p i a v U V hVU (gs y t) ∈ (e y).val.baseSet :=
    hpoint y t ▸ he y (inc t)
  let E (t : V) : H →ₗ[ℂ] (A → ℂ) := {
    toFun F := fun y => ((e y).val.linearEquivAt ℂ (familyBaseInclusion p i a v U V hVU (gs y t)) (he' y t)) (F (gs y t))
    map_add' F G := by
      ext y
      change ((e y).val.linearEquivAt ℂ (familyBaseInclusion p i a v U V hVU (gs y t)) (he' y t))
        (F (gs y t) + G (gs y t)) = _
      exact map_add _ _ _
    map_smul' c F := by
      ext y
      change ((e y).val.linearEquivAt ℂ (familyBaseInclusion p i a v U V hVU (gs y t)) (he' y t))
        (c • F (gs y t)) = _
      exact map_smul _ _ _ }
  have hE (F : H) : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, A → ℂ) ∞ (fun t => E t F) := by
    apply contMDiff_pi_space.mpr
    intro y t
    exact (contMDiffAt_familySmallSection_largeFrameCoefficient p i a v U V hVU hsm L F
      (e y) (gs y t) (he' y t)).comp t (gs y).contMDiff.contMDiffAt
  let C : H →ₗ[ℂ] (V → Fin r → ℂ) := {
    toFun F := fun t => J (inc t) (E t F)
    map_add' F G := by ext t j; simp only [map_add,Pi.add_apply]
    map_smul' c F := by ext t j; simp only [map_smul,Pi.smul_apply,RingHom.id_apply] }
  have hnorm (c : Fin r → ℂ) (t : V) :
      C (familyPhysicalBaseRestriction p i a v U V hVU hsm L (∑ j, c j • T j)) t = c := by
    have h := hC₀norm c (inc t)
    rw [hC₀] at h
    exact h
  refine ⟨C,?_,hnorm,?_⟩
  · intro F
    exact (hJ.comp inc.contMDiff).clm_apply (hE F)
  · intro F t hLanding q hqt
    obtain ⟨c,hc⟩ := hLanding
    let R := familyPhysicalBaseRestriction p i a v U V hVU hsm L (∑ j, c j • T j)
    have hEval : E t F = E t R := by
      ext y
      apply congrArg ((e y).val.linearEquivAt ℂ
        (familyBaseInclusion p i a v U V hVU (gs y t)) (he' y t))
      have h := hc (gs y t) (hparam y t)
      change F (gs y t) = (∑ j, c j • T j) (familyBaseInclusion p i a v U V hVU (gs y t))
      refine h.trans ?_
      symm
      change ((ContMDiffSection.coeAddHom 𝓘(ℂ, ComplexModel (d + 1)) ℂ ∞ B.Fiber)
        (∑ j, c j • T j)) (familyBaseInclusion p i a v U V hVU (gs y t)) = _
      rw [map_sum]
      simp only [Finset.sum_apply,ContMDiffSection.coeAddHom_apply]
      apply Finset.sum_congr rfl
      intro j _
      rfl
    have hcoeff : C F t = c := by
      change J (inc t) (E t F) = c
      rw [hEval]
      exact hnorm c t
    rw [hcoeff]
    exact hc q hqt

end SGPT.Trace.BertiniFamilyCanonical
