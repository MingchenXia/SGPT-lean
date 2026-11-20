import SGPT.GAGA.TowerAlgKahler
import SGPT.Okounkov.ChowBlDeltaCont

/-!
# `cor:Deltacontimplyvarphi` for projective manifolds, without a Kähler hypothesis

Source `chapter_Okounkov.tex`, `cor:Deltacontimplyvarphi`: *let `φ, ψ ∈ PSH(X, θ)_{>0}`; if
`Δ_{W•}(π^*θ, π^*φ) ⊆ Δ_{W•}(π^*θ, π^*ψ)` for all modifications `π : Y → X` and all admissible
flags `W•` on `Y`, then `φ ⪯_𝓘 ψ`.*  Lane TOWER-ALG, blueprint `claude-tower-alg.tex`, node
`claude-tower-alg:delta-cont`.

Lane CHOW-BLOWUP proved the transcendental form
`SGPT.Okounkov.ChowBl.sourceIOrder_of_generalPartialBody_subset` for a compact connected complex
manifold `X` with a holomorphic embedding `Ψ : X → ℙᴺ` *and* a Kähler background `hK`.  For a
projective manifold the Kähler background is automatic: `Ψ^* ω_FS` is Kähler
(`SGPT.GAGA.TowerAlg.kahlerBackgroundOfHolomorphicEmbedding`).  The corollary below therefore
needs only the embedding.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TowerAlg

universe u

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH.VariableComplexAtlas
open SGPT.Projective

variable {m N : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- **`cor:Deltacontimplyvarphi`, transcendental form, for projective `X`** (no Kähler
hypothesis): `X` compact connected with a holomorphic embedding `Ψ : X → ℙᴺ`, `θ` a closed real
`(1,1)`-form, `φ, ψ` `θ`-psh.  If `Δ_{W•}(π^*θ, π^*φ) ⊆ Δ_{W•}(π^*θ, π^*ψ)` for every finite
sequence of blow-ups with smooth centres `π : Y → X` and every smooth flag `W•` on `Y`, then
`φ ⪯_𝓘 ψ`.  The Kähler background required by
`SGPT.Okounkov.ChowBl.sourceIOrder_of_generalPartialBody_subset` is `Ψ^* ω_FS`. -/
theorem sourceIOrder_of_generalPartialBody_subset_of_embedding [CompactSpace X] [ConnectedSpace X]
    {Ψ : X → ComplexProjectiveSpace N} (hΨ : SGPT.GAGA.H0S.IsHolomorphicEmbedding (n := m + 1) Ψ)
    (θ : ClosedRealOneOneForm (m + 1) X)
    {φ ψ : X → EReal} (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential θ.val ψ)
    (hsub : ∀ (W : OriginalFlagGeometry.{u} (m + 1)) (π : W.carrier → X)
      (_ : IsBlowupSequence (m + 1) X W.carrier π) (hmod : IsAnalyticModification (n := m + 1) π),
      PartialBody.generalPartialBody W (ClosedRealOneOneForm.pullback hmod.1 θ)
          (fun y => φ (π y)) ⊆
        PartialBody.generalPartialBody W (ClosedRealOneOneForm.pullback hmod.1 θ)
          (fun y => ψ (π y))) :
    sourceIOrder (ofFixedModel (m + 1) X) φ ψ :=
  SGPT.Okounkov.ChowBl.sourceIOrder_of_generalPartialBody_subset hΨ
    (SGPT.GAGA.TowerAlg.nonempty_kahlerBackground_of_isHolomorphicEmbedding hΨ) θ hφ hψ hsub

end SGPT.Okounkov.TowerAlg

end
