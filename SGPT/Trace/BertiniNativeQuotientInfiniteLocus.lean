import SGPT.Trace.BertiniNativeQuotientEnergyField

/-! Literal actual quotient infinity locus, independent of the chosen finite quotient basis. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

def nativeBertiniQuotientInfiniteLocus : Set (ComplexModel N) :=
  {ζ | ∃ hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ),
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∃ q : NativeBertiniMultiplierQuotient p i ζ L hφ,
      nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ q = ⊤}

variable (V : TopologicalSpace.Opens (ComplexModel N))
  (hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ.val)) {r : ℕ}
  (S : Fin r → nativeMultiplierSections
    (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)

theorem nativeBertiniQuotientInfiniteLocus_iff_frame
    (hBasis : ∀ ζ : V, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i ζ.val L hφ),
      ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ.val)).range.mkQ (S j))
    (ζ : V) : ζ.val ∈ nativeBertiniQuotientInfiniteLocus p i L hφ ↔
      ∃ v : Fin r → ℂ, nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ.val v = ⊤ := by
  classical
  let := nativeBertiniMemberChartedSpace p i ζ.val (hsV ζ)
  let := nativeBertiniMemberComplex p i ζ.val (hsV ζ)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i ζ.val)).isCompact
  obtain ⟨b,hb⟩ := hBasis ζ
  have hrep (q : NativeBertiniMultiplierQuotient p i ζ.val L hφ) :
      (∑ j, (b.equivFun q) j • (nativeMultiplierSectionMap
        (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)
        hφ (nativeBertiniAffineSection p i ζ.val)).range.mkQ (S j)) = q := by
    calc
      _ = ∑ j, (b.equivFun q) j • b j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hb j]
      _ = b.equivFun.symm (b.equivFun q) := (b.equivFun_symm_apply _).symm
      _ = q := b.equivFun.symm_apply_apply q
  constructor
  · rintro ⟨_,q,hq⟩
    refine ⟨b.equivFun q,?_⟩
    rw [nativeBertiniQuotientFrameEnergy_apply p i V hsV L hφ S ζ, hrep]
    exact hq
  · rintro ⟨v,hv⟩
    refine ⟨hsV ζ,(∑ j, v j • (nativeMultiplierSectionMap
      (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)
      hφ (nativeBertiniAffineSection p i ζ.val)).range.mkQ (S j)),?_⟩
    rw [nativeBertiniQuotientFrameEnergy_apply p i V hsV L hφ S ζ] at hv
    exact hv

theorem nativeBertiniQuotientFrame_infinite_set
    (hBasis : ∀ ζ : V, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i ζ.val L hφ),
      ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ.val)).range.mkQ (S j)) :
    {ζ | ∃ v : Fin r → ℂ, nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ v = ⊤} =
      (V : Set (ComplexModel N)) ∩ nativeBertiniQuotientInfiniteLocus p i L hφ := by
  ext ζ
  by_cases hζ : ζ ∈ V
  · constructor
    · intro h
      exact ⟨hζ,(nativeBertiniQuotientInfiniteLocus_iff_frame p i L hφ V hsV S hBasis ⟨ζ,hζ⟩).mpr h⟩
    · rintro ⟨_,h⟩
      exact (nativeBertiniQuotientInfiniteLocus_iff_frame p i L hφ V hsV S hBasis ⟨ζ,hζ⟩).mp h
  · simp [nativeBertiniQuotientFrameEnergy,hζ]

theorem nativeBertiniQuotientFrame_infinite_iff_other_frame
    (hBasis : ∀ ζ : V, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p i ζ.val L hφ),
      ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ.val)).range.mkQ (S j))
    {s : ℕ} (W : TopologicalSpace.Opens (ComplexModel N))
    (hsW : ∀ ζ : W, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ.val))
    (T : Fin s → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
    (hOther : ∀ ζ : W, ∃ b : Module.Basis (Fin s) ℂ (NativeBertiniMultiplierQuotient p i ζ.val L hφ),
      ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ.val)).range.mkQ (T j))
    (ζ : ComplexModel N) (hζV : ζ ∈ V) (hζW : ζ ∈ W) :
    (∃ v : Fin r → ℂ, nativeBertiniQuotientFrameEnergy p i V hsV L hφ S ζ v = ⊤) ↔
      ∃ w : Fin s → ℂ, nativeBertiniQuotientFrameEnergy p i W hsW L hφ T ζ w = ⊤ :=
  (nativeBertiniQuotientInfiniteLocus_iff_frame p i L hφ V hsV S hBasis ⟨ζ,hζV⟩).symm.trans
    (nativeBertiniQuotientInfiniteLocus_iff_frame p i L hφ W hsW T hOther ⟨ζ,hζW⟩)

end SGPT.Trace.Bertini
