import SGPT.Trace.BertiniNativeDeterminantPluripolar
import Mathlib.Topology.Compactness.Lindelof

/-! Actual canonical-label countable projective exceptional set; no cross-chart metric assertion. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.DirImg2
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

private theorem sourcePluripolar_iUnion_countable {N : ℕ} {ι : Type} [Countable ι]
    (S : ι → Set (HyperplaneSpace N))
    (hEmpty : (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar ∅)
    (hS : ∀ i, (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (S i)) :
    (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (⋃ i, S i) := by
  classical
  let := Encodable.ofCountable ι
  let T : ℕ → Set (HyperplaneSpace N) := fun n => match Encodable.decode (α := ι) n with
    | none => ∅
    | some i => S i
  have hT (n : ℕ) : (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (T n) := by
    cases hn : Encodable.decode (α := ι) n with
    | none => simpa only [T,hn] using hEmpty
    | some i => simpa only [T,hn] using hS i
  have heq : (⋃ n, T n) = ⋃ i, S i := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n,hx⟩
      cases hn : Encodable.decode (α := ι) n with
      | none => simp only [T,hn,mem_empty_iff_false] at hx
      | some i => exact ⟨i,by simpa only [T,hn] using hx⟩
    · rintro ⟨i,hi⟩
      exact ⟨Encodable.encode i,by simpa only [T,Encodable.encodek] using hi⟩
  rw [← heq]
  exact SGPT.PSH.VariableComplexAtlas.LocallyPluripolar.iUnion hT

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d+1)) X] [IsComplexManifold (d+1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (L : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d+1) φ)

private theorem native_canonical_exception_from_actual_local_pieces
    (F : Finset X)
    (hF : (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (finitePointHyperplaneException p F))
    (hLocal : ∀ (ell : HyperplaneSpace N) (_hsm : IsSmoothHypersurfaceMember (d+1) p ell),
      ell ∉ finitePointHyperplaneException p F →
      ∃ U : TopologicalSpace.Opens (ComplexModel N), affineChart (chartIndex ell) ell ∈ U ∧
        LocallyPluripolarOn (nativeBertiniQuotientInfiniteLocus p (chartIndex ell) L hφ) U ∧
        (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar
          (affinePoint (chartIndex ell) '' (nativeBertiniQuotientInfiniteLocus p (chartIndex ell) L hφ ∩ U))) :
    ∃ E : Set (HyperplaneSpace N), (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar E ∧
      finitePointHyperplaneException p F ⊆ E ∧
      ∀ (ell : HyperplaneSpace N) (_hsm : IsSmoothHypersurfaceMember (d+1) p ell), ell ∉ E →
        affineChart (chartIndex ell) ell ∉ nativeBertiniQuotientInfiniteLocus p (chartIndex ell) L hφ := by
  classical
  have hEmpty := hF.mono (empty_subset _)
  have hLabel (i : Fin (N+1)) : ∃ E : Set (HyperplaneSpace N),
      (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar E ∧
      ∀ (ell : HyperplaneSpace N), chartIndex ell = i → IsSmoothHypersurfaceMember (d+1) p ell →
        ell ∉ finitePointHyperplaneException p F →
        affineChart i ell ∈ nativeBertiniQuotientInfiniteLocus p i L hφ → ell ∈ E := by
    let Z : Set (HyperplaneSpace N) := {ell | chartIndex ell = i ∧
      IsSmoothHypersurfaceMember (d+1) p ell ∧ ell ∉ finitePointHyperplaneException p F}
    have hPieces (t : Z) : ∃ U : TopologicalSpace.Opens (ComplexModel N), affineChart i t.val ∈ U ∧
        (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar
          (affinePoint i '' (nativeBertiniQuotientInfiniteLocus p i L hφ ∩ U)) := by
      obtain ⟨U,hU,_hl,hp⟩ := hLocal t.val t.property.2.1 t.property.2.2
      exact ⟨U,by simpa only [t.property.1] using hU,by simpa only [t.property.1] using hp⟩
    choose U hcentre hPiece using hPieces
    let O : Z → Set (HyperplaneSpace N) := fun t => affinePoint i '' U t
    have hO (t : Z) : IsOpen (O t) := (isOpenEmbedding_affinePoint i).isOpenMap _ (U t).isOpen
    have hCover : Z ⊆ ⋃ t : Z, O t := by
      intro ell hell
      let t : Z := ⟨ell,hell⟩
      refine mem_iUnion.mpr ⟨t,affineChart i ell,hcentre t,?_⟩
      have hleft := (affineChart (chartIndex ell)).left_inv (mem_affineChart_chartIndex ell)
      simpa only [hell.1,affineChart_symm_apply] using hleft
    obtain ⟨c,hc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof Z).elim_countable_subcover O hO hCover
    let : Countable c := hc.to_subtype
    let E := ⋃ t : c, affinePoint i '' (nativeBertiniQuotientInfiniteLocus p i L hφ ∩ U t.val)
    have hE : (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar E :=
      sourcePluripolar_iUnion_countable _ hEmpty (fun t : c => hPiece t.val)
    refine ⟨E,hE,?_⟩
    intro ell hindex hs hell hinf
    have hellZ : ell ∈ Z := ⟨hindex,hs,hell⟩
    obtain ⟨t,ht⟩ := mem_iUnion.mp (hcov hellZ)
    obtain ⟨htc,hellO⟩ := mem_iUnion.mp ht
    obtain ⟨z,hzU,hzell⟩ := hellO
    have hz : z = affineChart i ell := by rw [← hzell,affineChart_affinePoint]
    refine mem_iUnion.mpr ⟨⟨t,htc⟩,z,⟨?_,hzU⟩,hzell⟩
    rwa [hz]
  choose E hE hCover using hLabel
  let pieces : Option (Fin (N+1)) → Set (HyperplaneSpace N) := fun i => match i with
    | none => finitePointHyperplaneException p F
    | some i => E i
  have hpieces (i : Option (Fin (N+1))) : (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (pieces i) := by
    cases i with
    | none => exact hF
    | some i => exact hE i
  refine ⟨⋃ i, pieces i,sourcePluripolar_iUnion_countable pieces hEmpty hpieces,?_,?_⟩
  · intro ell hell
    exact mem_iUnion.mpr ⟨none,hell⟩
  · intro ell hs hell hinf
    apply hell
    refine mem_iUnion.mpr ⟨some (chartIndex ell),?_⟩
    apply hCover (chartIndex ell) ell rfl hs
    · intro hbad
      exact hell (mem_iUnion.mpr ⟨none,hbad⟩)
    · exact hinf


theorem exists_uniform_nativeBertini_projective_infinite_exception
    [ConnectedSpace X] {k : ℕ}
    (p : ContMDiffMap 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel (k+1)) X (ComplexProjectiveSpace (k+1)) ∞)
    (G : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
    (hG : SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric G)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d+1) φ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ (A : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
      (hA : SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric A),
      (sourceNativeFirstChernForm A hA).val.IsSemipositive → ∀ power : ℕ, k₀ ≤ power →
      let L := twistedPower G A power
      ∃ E : Set (HyperplaneSpace (k+1)), (ofFixedModel (k+1) (HyperplaneSpace (k+1))).LocallyPluripolar E ∧
        ∀ (ell : HyperplaneSpace (k+1)) (_hsm : IsSmoothHypersurfaceMember (d+1) p ell), ell ∉ E →
          affineChart (chartIndex ell) ell ∉ nativeBertiniQuotientInfiniteLocus p (chartIndex ell) L hφ := by
  obtain ⟨k0,hk0,hLocal⟩ := exists_uniform_nativeBertini_local_infinite_locus_pluripolar p G hG hGpos φ hφ
  refine ⟨k0,hk0,?_⟩
  intro A hA hAsemi power hpower
  dsimp only
  obtain ⟨F,_hFn,_hFa,_hFproper,hFpl,hPieces⟩ := hLocal A hA hAsemi power hpower
  obtain ⟨E,hE,_hFE,hgood⟩ := native_canonical_exception_from_actual_local_pieces p (twistedPower G A power) hφ F hFpl hPieces
  exact ⟨E,hE,hgood⟩

end SGPT.Trace.Bertini
