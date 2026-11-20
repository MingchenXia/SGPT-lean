import SGPT.Trace.BertiniNativeProjectiveException
import SGPT.Trace.BertiniUniversalH0FailureLocus
import SGPT.Trace.BertiniUniversalRawGoodMember

/-! LITERAL raw original book Bertini good set; actual positive native input only. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.DirImg2
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.BertiniUniversal

variable {d k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d+1)) X] [IsComplexManifold (d+1) X] [CompactSpace X] [ConnectedSpace X]
  (p : ContMDiffMap 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel (k+1)) X (ComplexProjectiveSpace (k+1)) ∞)
  (G : HermitianHolomorphicLineBundle.{0,0} (d+1) X)
  (hG : SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric G)
  (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)

include G hG hGpos in
theorem coPluripolar_book_bertiniGoodSet_of_original_global_positive_native
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d+1) φ) :
    (ofFixedModel (k+1) (HyperplaneSpace (k+1))).CoPluripolar (bertiniGoodSet p p.contMDiff φ) := by
  classical
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let omegaG : KahlerBackground (d+1) X := ⟨sourceNativeFirstChernForm G hG,hGpos⟩
  have hGsemi : (sourceNativeFirstChernForm G hG).val.IsSemipositive := omegaG.isSemipositive
  obtain ⟨kE,_hkE,hExceptions⟩ := exists_uniform_nativeBertini_projective_infinite_exception p G hG hGpos φ hφ
  obtain ⟨kH,_hkH,hImages⟩ := exists_uniform_original_intrinsicH0_failure_locus_eq_infinite p G hG hGpos φ hφ
  let K := max kE kH
  have hEach (j : ℕ) := hExceptions G hG hGsemi (K+j) ((le_max_left _ _).trans (Nat.le_add_right K j))
  choose E hE hFinite using hEach
  let bad : ℕ → Set (HyperplaneSpace (k+1)) := fun j => if j=0 then singularMemberSet (d+1) p else E (j-1)
  have hBad (j : ℕ) : (ofFixedModel (k+1) (HyperplaneSpace (k+1))).LocallyPluripolar (bad j) := by
    by_cases hj : j=0
    · simpa only [bad,if_pos hj] using locallyPluripolar_singularMemberSet p p.contMDiff (by omega : 1 ≤ k+1)
    · simpa only [bad,if_neg hj] using hE (j-1)
  have hUnion := SGPT.PSH.VariableComplexAtlas.LocallyPluripolar.iUnion hBad
  apply hUnion.mono
  intro ell hell
  by_contra hnot
  apply hell
  have hsmooth : IsSmoothHypersurfaceMember (d+1) p ell := by
    by_contra hs
    apply hnot
    exact mem_iUnion.mpr ⟨0,by simpa only [bad,if_pos rfl,singularMemberSet,mem_ofPred_eq] using hs⟩
  have hNotE (j : ℕ) : ell ∉ E j := by
    intro hj
    apply hnot
    exact mem_iUnion.mpr ⟨j+1,by simpa only [bad,Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel] using hj⟩
  let i := chartIndex ell
  let zeta := affineChart i ell
  have hpoint : affinePoint i zeta = ell := by
    exact (affineChart i).left_inv (mem_affineChart_chartIndex ell)
  have hsm : IsSmoothHypersurfaceMember (d+1) p (affinePoint i zeta) := hpoint.symm ▸ hsmooth
  have hbook : affinePoint i zeta ∈ bertiniGoodSet p p.contMDiff φ := by
    let := nativeBertiniMemberChartedSpace p i zeta hsm
    let := nativeBertiniMemberComplex p i zeta hsm
    let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i zeta)).isCompact
    apply mem_book_bertiniGoodSet_of_raw_step14 p i zeta hsm G G hG hG hGpos φ hφ.1
    intro hφglobal
    refine ⟨K,?_⟩
    intro power hpower
    have hInf := hFinite (power-K) ell hsmooth (hNotE (power-K))
    have hKpower : K+(power-K)=power := Nat.add_sub_of_le hpower
    have hNoInf : zeta ∉ nativeBertiniQuotientInfiniteLocus p i (twistedPower G G power) hφglobal := by
      simpa only [hKpower] using hInf
    have hSet := hImages G hG hGsemi power ((le_max_right _ _).trans hpower) i
    have hNoFailure : zeta ∉ originalIntrinsicH0ImageFailureLocus p i (twistedPower G G power) hφglobal := by
      rw [hSet]
      exact hNoInf
    by_contra hFailure
    exact hNoFailure ⟨hsm,hFailure⟩
  simpa only [hpoint] using hbook


include G hG hGpos in
theorem coPluripolar_book_bertiniGoodSet_of_raw_positive_native
    (φ : X → EReal) (hφ : ManifoldQuasiPlurisubharmonic (n := d+1) φ) :
    (ofFixedModel (k+1) (HyperplaneSpace (k+1))).CoPluripolar (bertiniGoodSet p p.contMDiff φ) := by
  classical
  obtain hbot | hglobal := raw_qpsh_eq_bot_or_original_global hφ
  · have hBad := locallyPluripolar_singularMemberSet p p.contMDiff (by omega : 1 ≤ k+1)
    apply hBad.mono
    intro ell hell
    by_contra hnot
    apply hell
    have hsmooth : IsSmoothHypersurfaceMember (d+1) p ell := by
      simpa only [singularMemberSet,mem_ofPred_eq,not_not] using hnot
    let i := chartIndex ell
    let zeta := affineChart i ell
    have hpoint : affinePoint i zeta = ell := (affineChart i).left_inv (mem_affineChart_chartIndex ell)
    have hsm : IsSmoothHypersurfaceMember (d+1) p (affinePoint i zeta) := hpoint.symm ▸ hsmooth
    have hbook : affinePoint i zeta ∈ bertiniGoodSet p p.contMDiff φ := by
      let := nativeBertiniMemberChartedSpace p i zeta hsm
      let := nativeBertiniMemberComplex p i zeta hsm
      let := isCompact_iff_compactSpace.mp
        (isClosed_member p p.contMDiff.continuous (affinePoint i zeta)).isCompact
      apply mem_book_bertiniGoodSet_of_raw_step14 p i zeta hsm G G hG hG hGpos φ hφ
      intro hglobal
      obtain ⟨y,_hy,hyfinite⟩ := hglobal.2 (Classical.choice inferInstance) univ isOpen_univ (mem_univ _)
      exact (hyfinite (hbot y)).elim
    simpa only [hpoint] using hbook
  · exact coPluripolar_book_bertiniGoodSet_of_original_global_positive_native p G hG hGpos φ hglobal

end SGPT.Trace.Bertini
