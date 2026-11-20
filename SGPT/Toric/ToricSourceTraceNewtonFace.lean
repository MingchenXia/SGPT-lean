import SGPT.Toric.ToricFaceSourceBodyComparison
import SGPT.Toric.ToricFaceZeroPrefixDictionary
import SGPT.Toric.ToricFaceTraceVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Okounkov.SourceMultiSlice
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SourceTraceRepresentativeDefinition
open scoped Topology Manifold ContDiff Classical ENNReal
variable {m k : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin (m + k) → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- COMPLETE original thm:tracetor in the ACTUAL original character space:
the Newton body of the literal original normalized trace is exactly
(Δ_X∩Qσ)−mσ. All original mass/generic/defined-trace/I-volume hypotheses,
arbitrary original Cartier representative, original poles, every σ rank and
ambient/target dimension0 are retained. The actual native Y, restricted DY,
metric, invariant positive trace, all flag/body/affine dictionaries are
produced internally; no target presentation or body certificate is input. -/
theorem BigToricMetric.sourceTrace_newtonBody_face
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (hφpos : 0 < h.MA hφ univ)
    (v : latticePolytopeVertices γ) (e : Fin (m + k) ≃ Fin (m + k))
    (mσ : Fin (m + k) → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v ''
      toricFlagSelectedIndices e (originalIndex m k)) mσ)
    (_hν : sourceGenericLelongNumber (n := m + k)
      (toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) φ = 0)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground
        (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k)))
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v
          (toricFlagSelectedIndices e (originalIndex m k))))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) h.form φ)
    (_hTraceIVolume : 0 < toricFaceSourceTraceIVolume h v
      (toricFlagSelectedIndices e (originalIndex m k)) hdefined) :
    let τ := SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground
        (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k)))
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v
          (toricFlagSelectedIndices e (originalIndex m k))))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) h.form φ hdefined
    let η := toricFaceRestrictedMetric h v (toricFlagSelectedIndices e (originalIndex m k)) mσ hσ
    τ ∈ η.PSHTor ∧
      (toricFaceRealCharacterCoordinates (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))).symm ''
          η.newtonBody τ =
        {x : toricStratumRealSpace (polytopeToricRay γ hs v '' toricFlagSelectedIndices e (originalIndex m k)) |
          x.val + latticeVector mσ ∈ h.newtonBody φ ∩
            toricDivisorFace D (polytopeToricRay γ hs v '' toricFlagSelectedIndices e (originalIndex m k))} := by
  intro τ η
  obtain ⟨hτ,hτpos,hslice⟩ := toricFace_sourcePartialBody_zeroSlice h hφ v e mσ hσ hdefined
  refine ⟨hτ,?_⟩
  let J := toricFlagSelectedIndices e (originalIndex m k)
  let C := toricFaceRealCharacterCoordinates (hs := hs) v J
  let qY := toricFaceVertexEquiv (hs := hs) v J (toricFaceBaseVertex (hs := hs) v J)
  let eY := toricFaceTailOrder (hs := hs) v e (originalIndex m k)
  let castCoord : (Fin (toricFaceDimension J) → ℝ) → Fin m → ℝ :=
    fun q j => q (Fin.cast (toricFaceOriginalDimension e).symm j)
  let Φ := toricFlagRealMap hs v e D
  let Ψ := toricFlagRealMap
    (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) qY eY
    (toricFaceRestrictedDivisor D v J mσ)
  have hX := h.sourceToricPartialBody_eq_flagImage hφ hφpos v e
  have hY := η.sourceToricPartialBody_eq_flagImage hτ hτpos qY eY
  have himage : zeroSlice m k (Φ '' h.newtonBody φ) =
      (fun y => castCoord (Ψ y)) '' η.newtonBody τ := by
    calc
      zeroSlice m k (Φ '' h.newtonBody φ) = zeroSlice m k (h.sourceToricPartialBody hφ v e) :=
        congrArg (zeroSlice m k) hX
      _ = castCoord '' η.sourceToricPartialBody hτ qY eY := hslice
      _ = castCoord '' (Ψ '' η.newtonBody τ) := congrArg (Set.image castCoord) hY.symm
      _ = _ := by simp only [Set.image_image]
  have hdiagram (x : toricStratumRealSpace (polytopeToricRay γ hs v '' J)) :
      zeroPrefix m k (castCoord (Ψ (C x))) = Φ (x.val + latticeVector mσ) :=
    toricFace_zeroPrefix_flagRealMap D v e mσ hσ x
  have hXP := (h.newtonBody_properties (h.nonempty_toricDivisorPolytope_of_mem hφ) hφ).2.2.2
  ext x
  constructor
  · rintro ⟨y,hy,hyx⟩
    have hyEq := congrArg C hyx
    rw [ContinuousLinearEquiv.apply_symm_apply] at hyEq
    subst y
    have hq : castCoord (Ψ (C x)) ∈ zeroSlice m k (Φ '' h.newtonBody φ) :=
      himage.symm ▸ ⟨C x,hy,rfl⟩
    change zeroPrefix m k (castCoord (Ψ (C x))) ∈ Φ '' h.newtonBody φ at hq
    rw [hdiagram x] at hq
    obtain ⟨p,hp,hpeq⟩ := hq
    have hpx : p = x.val + latticeVector mσ := toricFlagRealMap_injective v e D hpeq
    have hx : x.val + latticeVector mσ ∈ h.newtonBody φ := hpx ▸ hp
    exact ⟨hx,toricDivisorFace_add_Cartier_of_annihilator hσ x (hXP hx)⟩
  · intro hx
    have hq : castCoord (Ψ (C x)) ∈ zeroSlice m k (Φ '' h.newtonBody φ) := by
      change zeroPrefix m k (castCoord (Ψ (C x))) ∈ Φ '' h.newtonBody φ
      rw [hdiagram x]
      exact ⟨x.val + latticeVector mσ,hx.1,rfl⟩
    have hq' : castCoord (Ψ (C x)) ∈ (fun y => castCoord (Ψ y)) '' η.newtonBody τ := himage ▸ hq
    obtain ⟨y,hy,heq⟩ := hq'
    have hΨ : Ψ y = Ψ (C x) := castToricFlagCoordinates_injective (toricFaceOriginalDimension e) heq
    have hyEq : y = C x := toricFlagRealMap_injective qY eY (toricFaceRestrictedDivisor D v J mσ) hΨ
    refine ⟨y,hy,?_⟩
    rw [hyEq, ContinuousLinearEquiv.symm_apply_apply]


/-- Every original selected ray subset of the specified source rank has an
internally produced full ordering with exactly that prefix; no ordering is input. -/
theorem exists_toricFlagSelectedIndices_of_card
    (J : Set (Fin (m+k))) (hJ : Fintype.card J = k) :
    ∃ e : Fin (m+k) ≃ Fin (m+k), J = toricFlagSelectedIndices e (originalIndex m k) := by
  classical
  obtain ⟨e,i,he⟩ := exists_toricFlagSelectedIndices J
  have hdim : toricFaceDimension J = m := by
    unfold toricFaceDimension
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin,hJ,Nat.add_sub_cancel_right]
  have hdi := toricFaceDimension_flagSelectedIndices e i
  rw [←he,hdim] at hdi
  have hi : i = originalIndex m k := by
    apply Fin.ext
    have := i.isLt
    change i.val = k
    omega
  exact ⟨e,by simpa only [hi] using he⟩

/-- The complete source face formula for EVERY original cone representation,
with only its actual rank and original source hypotheses. The full flag/order
is manufactured internally from the genuine finite source ray subset. -/
theorem BigToricMetric.sourceTrace_newtonBody_face_of_cone
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (hφpos : 0 < h.MA hφ univ)
    (v : latticePolytopeVertices γ) (J : Set (Fin (m+k))) (hJ : Fintype.card J = k)
    (mσ : Fin (m+k) → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (hν : sourceGenericLelongNumber (n := m+k)
      (toricFaceSourceInclusion (hs := hs) v J) φ = 0)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form φ)
    (hTraceIVolume : 0 < toricFaceSourceTraceIVolume h v J hdefined) :
    let τ := SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form φ hdefined
    let η := toricFaceRestrictedMetric h v J mσ hσ
    τ ∈ η.PSHTor ∧
      (toricFaceRealCharacterCoordinates (hs := hs) v J).symm '' η.newtonBody τ =
        {x : toricStratumRealSpace (polytopeToricRay γ hs v '' J) |
          x.val + latticeVector mσ ∈ h.newtonBody φ ∩
            toricDivisorFace D (polytopeToricRay γ hs v '' J)} := by
  obtain ⟨e,he⟩ := exists_toricFlagSelectedIndices_of_card J hJ
  subst J
  exact h.sourceTrace_newtonBody_face hφ hφpos v e mσ hσ hν hdefined hTraceIVolume

end SGPT.Toric
