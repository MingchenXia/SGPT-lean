import SGPT.Projective.OkounkovOriginalKahlerQEAOwnLimit
import SGPT.Projective.OkounkovOriginalWeightedKahlerQEA
import SGPT.Projective.OkounkovOriginalAnalyticUpperPoints
import SGPT.Okounkov.ValGen2Conc
import SGPT.Convex.MinkowskiHausdorffLimit

/-! Actual same-own-body rational concavity beyond analytic singularities, with all producers internal.
Blueprint: okounkov-original-rational-kahler-concavity.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.TranscendentalCore SGPT.AlmostSemigroup
open scoped Topology Pointwise ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)]
local instance rationalKahlerConcTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance rationalKahlerConcCharts : ChartedSpace (ComplexModel (m+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m+1)
local instance rationalKahlerConcManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (m+1)

/-- Actual original rational concavity, arbitrary original valuation and ANY Kähler-current weights. -/
theorem original_partialBody_rational_concavity_kahler {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m+1) E L)
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
    {φ ψ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact; IsKahlerCurrentPotential (H.curvature a) ψ)
    (p q : ℕ) (hp : 0<p) (hq : 0<q) :
    letI := E.isProper
    letI := E.isSeparated
    letI := E.quasiCompact
    let t : ℚ := (p:ℚ)/(p+q)
    ∃ (hKc : IsCompact (centreOkounkovBody f v a)) (hKv : Convex ℝ (centreOkounkovBody f v a)),
      IsKahlerCurrentPotential (H.curvature a) (convexComb (t:ℝ) φ ψ) ∧
      (t:ℝ) • ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) φ +
        (1-(t:ℝ)) • ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) ψ ⊆
      ValGen.partialBody f (m+1) E v (valuationCenter f v) a (SGPT.GAGA.OkoClose.coneOver _ hKc hKv) (convexComb (t:ℝ) φ ψ) := by
  let := E.isProper
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let c := valuationCenter f v
  let t : ℚ := (p:ℚ)/(p+q)
  have hpQ : (0:ℚ)<p := by exact_mod_cast hp
  have hqQ : (0:ℚ)<q := by exact_mod_cast hq
  have ht0 : 0<t := div_pos hpQ (add_pos hpQ hqQ)
  have ht1 : t<1 := (div_lt_one (add_pos hpQ hqQ)).mpr (by linarith)
  have htR0 : (0:ℝ)<t := by exact_mod_cast ht0
  have htR1 : (t:ℝ)<1 := by exact_mod_cast ht1
  have htread : (t:ℝ)=(p:ℝ)/(p+q) := by simp only [t,Rat.cast_div,Rat.cast_add,Rat.cast_natCast]
  have htother : 1-(t:ℝ)=(q:ℝ)/(p+q) := by
    rw [htread]
    have hd : (p:ℝ)+q≠0 := by
      have hpR : (0:ℝ)<p := by exact_mod_cast hp
      have hqR : (0:ℝ)<q := by exact_mod_cast hq
      exact (add_pos hpR hqR).ne'
    field_simp [hd]
    ring
  let θ := H.curvature a
  have hconv (ρ σ : SchemeComplexPoint f → EReal) (hρ : IsKahlerCurrentPotential θ ρ)
      (hσ : IsThetaPshPotential θ.val σ) : IsKahlerCurrentPotential θ (convexComb (t:ℝ) ρ σ) := by
    have hh := TranscendentalCore.isKahlerCurrentPotential_add_smul hρ hσ htR0 (sub_nonneg.mpr htR1.le)
    have hf : (t:ℝ)•θ+(1-(t:ℝ))•θ=θ := by module
    rwa [hf] at hh
  have hφθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hφ
  have hψθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hψ
  have hχ := hconv φ ψ hφ hψθ
  have hbig := original_isBig_of_positive_iVolume_allDimensions f (m+1) E a H hφθ
    (original_iVolume_pos_of_kahler_allDimensions f (m+1) E a H hφ)
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f (m+1) E
  obtain ⟨hKc,hKv,hinter,hS,hfull⟩ := sectionSemigroup_mem_ownBody_fullSemigroupLocus_allDimensions
    f a (m+1) E hbig v hv c
  let C := SGPT.GAGA.OkoClose.coneOver _ hKc hKv
  let B := fun ρ => ValGen.partialBody f (m+1) E v c a C ρ
  have hgeom (ρ : SchemeComplexPoint f → EReal) (hρ : IsKahlerCurrentPotential θ ρ) :
      IsCompact (B ρ) ∧ Convex ℝ (B ρ) ∧ (B ρ).Nonempty := by
    obtain ⟨hKρc,hKρv,hBc,hBv,hBne,hvol⟩ := OriginalAnalyticUpperPoints.exists_kahler_partialBody_geometry
      f E a H hbig v hv c hρ
    exact ⟨hBc,hBv,hBne⟩
  obtain ⟨U,hU⟩ := PartialBody.exists_isKahlerQEA hφ
  obtain ⟨V,hV⟩ := PartialBody.exists_isKahlerQEA hψ
  let W := fun j => convexComb (t:ℝ) (U j) (V j)
  have hW := original_rational_convexComb_kahlerQEA f E θ hU hV t ht0 ht1
  obtain ⟨hKUc,hKUv,hleU,hlimU⟩ := original_kahlerQEA_partialBody_limit f E a H v hv hφ U hU
  obtain ⟨hKVc,hKVv,hleV,hlimV⟩ := original_kahlerQEA_partialBody_limit f E a H v hv hψ V hV
  obtain ⟨hKWc,hKWv,hleW,hlimW⟩ := original_kahlerQEA_partialBody_limit f E a H v hv hχ W hW
  have hWcur (j : ℕ) : IsKahlerCurrentPotential θ (W j) := hconv _ _ (hU.2 j).2 (hV.2 j).1.1
  have hstage (j : ℕ) : (t:ℝ)•B (U j)+(1-(t:ℝ))•B (V j)⊆B (W j) := by
    let γ := fun z => (((p:ℝ)/(p+q):ℝ):EReal)*U j z+(((q:ℝ)/(p+q):ℝ):EReal)*V j z
    have hγ : γ=W j := by
      funext z
      dsimp only [γ,W,convexComb]
      rw [htother,htread]
    have hγK : IsKahlerCurrentPotential θ γ := hγ.symm ▸ hWcur j
    have hγθ := PartialBody.isThetaPshPotential_of_isKahlerCurrentPotential hγK
    have hmass := PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hγK hγθ
    have hh := ValGen2.partialBody_convexComb_superset_of_analytic f E Y hY c v a H (C:=C) hS hfull.2
      (hU.2 j).2 (hU.1.2.1 j) (hV.2 j).2 (hV.1.2.1 j) hp hq hγθ hmass
    change ((p:ℝ)/(p+q))•B (U j)+((q:ℝ)/(p+q))•B (V j)⊆B γ at hh
    rw [hγ] at hh
    rw [htother,htread]
    exact hh
  refine ⟨hKc,hKv,hχ,?_⟩
  exact SGPT.Convex.MinkowskiHausdorffLimit.weighted_sum_subset_of_hausdorff_limits
    (hgeom φ hφ).1 (hgeom φ hφ).2.2 (hgeom ψ hψ).1 (hgeom ψ hψ).2.2
    (hgeom _ hχ).1 (hgeom _ hχ).2.2
    (fun j => (hgeom _ (hU.2 j).2).1) (fun j => (hgeom _ (hU.2 j).2).2.2)
    (fun j => (hgeom _ (hV.2 j).2).1) (fun j => (hgeom _ (hV.2 j).2).2.2)
    (fun j => (hgeom _ (hWcur j)).1) (fun j => (hgeom _ (hWcur j)).2.2)
    hlimU hlimV hlimW (t:ℝ) (1-(t:ℝ)) (Eventually.of_forall hstage)
end SGPT.Okounkov.OriginalBook
