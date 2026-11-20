import SGPT.Trace.BertiniNativeBookBertini
import SGPT.Trace.BertiniUniversalProjectivePositive
import SGPT.Trace.DirImg2ABT
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground

/-! Actual source analytic Bertini trace corollary, without an incoming Bertini certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.BertiniGeneral SGPT.Trace.Trace2Bertini

variable {d k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d+1)) X] [IsComplexManifold (d+1) X] [CompactSpace X] [ConnectedSpace X]
  (hproj : IsProjectiveManifold (d+1) X)
  (p : X → ComplexProjectiveSpace (k+1))
  (hp : ContMDiff 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel (k+1)) ∞ p)
  (omega : KahlerBackground (d+1) X) (hnd : IsNondegenerate p)
  (hconn : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (k+1) (HyperplaneSpace (k+1))).CoPluripolar
    {ell | IsConnected (member p ell)})

include hproj hnd hconn in
theorem coPluripolar_abtTrace_of_original_projective
    {theta : ClosedRealOneOneForm (d+1) X} {φ : X → EReal} (hφ : IsThetaPshPotential theta.val φ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel (k+1) (HyperplaneSpace (k+1))).CoPluripolar
      {ell | ∃ h : IsConnectedSmoothMember (d+1) p ell,
        IsABTTrace omega (isClosedConnectedSubmanifold_member p hp h) φ} := by
  obtain ⟨G,hG,hGpos⟩ := SGPT.Trace.BertiniUniversal.exists_actual_positive_native_bundle_of_book_projective hproj
  let P : ContMDiffMap 𝓘(ℂ,ComplexModel (d+1)) 𝓘(ℂ,ComplexModel (k+1)) X (ComplexProjectiveSpace (k+1)) ∞ := ⟨p,hp⟩
  refine SGPT.Trace.DirImg2.coPluripolar_abtTrace_of_rat_reverse p hp (by omega) omega hnd (by omega) hconn hφ ?_
  intro q hq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqφ := SGPT.NAPotential.BJPrep.manifoldQuasiPlurisubharmonic_const_mul hφ.1.quasiPlurisubharmonic hq'
  exact SGPT.Trace.DirImg2.coPluripolar_reverse_of_bertiniGoodSet_mul p hp hq'
    (coPluripolar_book_bertiniGoodSet_of_raw_positive_native P G hG hGpos _ hqφ)

include hproj hnd hconn in
theorem coPluripolar_abtTrace_of_original_global_qpsh
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d+1) φ) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel (k+1) (HyperplaneSpace (k+1))).CoPluripolar
      {ell | ∃ h : IsConnectedSmoothMember (d+1) p ell,
        IsABTTrace omega (isClosedConnectedSubmanifold_member p hp h) φ} := by
  obtain ⟨C,_hC,hCφ⟩ := GlobalQuasiPshKahlerBackground.exists_pos_isThetaPshPotential_smul omega hφ
  exact coPluripolar_abtTrace_of_original_projective hproj p hp omega hnd hconn hCφ

end SGPT.Trace.Bertini
