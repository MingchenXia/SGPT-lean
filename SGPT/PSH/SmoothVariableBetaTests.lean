import SGPT.PSH.BookCurrentProducts
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmooth

/-! Actual LF wedge testing maps for EVERY smooth source beta family. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.ComplexCurrentDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorSmooth
open ClosedProductCurrents ProductTestForms TopDegreeDensity
open SGPT.PSH.BookCurrent
open scoped Topology Distributions ContDiff

/-- Genuine continuous real-linear covector component operation. -/
def betaRealCovectorCLM (n : ℕ) :
    (ComplexModel n →L[ℂ] ℂ) →L[ℝ] (ComplexModel n →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := reForm
      map_add' := by intro a b; ext v; rfl
      map_smul' := by intro c a; ext v; simp [reForm] }

def betaImagCovectorCLM (n : ℕ) :
    (ComplexModel n →L[ℂ] ℂ) →L[ℝ] (ComplexModel n →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := imForm
      map_add' := by intro a b; ext v; rfl
      map_smul' := by intro c a; ext v; simp [imForm] }

/-- Actual continuous one-covector to one-form map, with full evaluations. -/
def covectorOneFormCLM (n : ℕ) : (ComplexModel n →L[ℝ] ℝ) →L[ℝ] RealForm n 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := ContinuousAlternatingMap.ofSubsingleton ℝ (ComplexModel n) ℝ (0 : Fin 1)
      map_add' := by intro a b; ext v; rfl
      map_smul' := by intro c a; ext v; rfl }

/-- Genuine smoothness of the literal source i beta wedge bar beta map. -/
theorem contDiffOn_oneOneSquare {n : ℕ} {U : Set (ComplexModel n)}
    {b : ComplexModel n → ComplexModel n →L[ℂ] ℂ} (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (fun z => oneOneSquare (b z)) U := by
  have hr := (betaRealCovectorCLM n).contDiff.comp_contDiffOn hb
  have hi := (covectorOneFormCLM n).contDiff.comp_contDiffOn
    ((betaImagCovectorCLM n).contDiff.comp_contDiffOn hb)
  let P : (ComplexModel n →L[ℝ] RealForm n 1) →L[ℝ] RealForm n 2 :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  exact (P.contDiff.comp_contDiffOn (hr.smulRight hi)).const_smul (2 : ℝ)

/-- Every actual variable source product is genuinely smooth on its domain. -/
theorem contDiffOn_betaProduct {n : ℕ} {U : Set (ComplexModel n)} :
    ∀ (p : ℕ) (beta : Fin p → ComplexModel n → ComplexModel n →L[ℂ] ℂ),
      (∀ j,ContDiffOn ℝ ∞ (beta j) U) →
      ContDiffOn ℝ ∞ (fun z => betaProduct (fun j => beta j z)) U
  | 0,_,_ => contDiffOn_const
  | p+1,beta,hbeta =>
    contDiffOn_coordinateWedge
      (contDiffOn_betaProduct p (fun j => beta j.castSucc) (fun j => hbeta j.castSucc))
      (contDiffOn_oneOneSquare (hbeta (Fin.last p)))

variable {n k : ℕ} (U : Opens (ComplexModel n))

/-- Genuine scalar-test times tensor field smooth only on the ACTUAL U. -/
def smoothTensorTest (g : ComplexModel n → RealForm n k)
    (hg : ContDiffOn ℝ ∞ g (U : Set (ComplexModel n))) (phi : 𝓓(U,ℝ)) :
    𝓓(U,RealForm n k) where
  toFun z := phi z • g z
  contDiff' := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z∈U
    · exact phi.contDiff.contDiffAt.smul (hg.contDiffAt (U.isOpen.mem_nhds hz))
    · apply (contDiffAt_const (c := (0 : RealForm n k))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (phi.tsupport_subset h))] with y hy
      simp [hy]
  hasCompactSupport' := phi.hasCompactSupport.smul_right
  tsupport_subset' := (tsupport_smul_subset_left _ _).trans phi.tsupport_subset

/-- Actual supported-stage cutoff gluing proves LF continuity; global
smoothness of the source variable family is NOT an added hypothesis. -/
def smoothTensorTestCLM (g : ComplexModel n → RealForm n k)
    (hg : ContDiffOn ℝ ∞ g (U : Set (ComplexModel n))) :
    𝓓(U,ℝ) →L[ℝ] 𝓓(U,RealForm n k) := by
  refine TestFunction.limitCLM ℝ (smoothTensorTest U g hg) (fun K hK => ?_) ?_
  · let chi := cutoffOf K hK
    have hchi := cutoffOf_spec K hK
    have hchig : ContDiff ℝ ∞ (fun z => chi z • g z) := by
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hz : z∈U
      · exact hchi.1.contDiffAt.smul (hg.contDiffAt (U.isOpen.mem_nhds hz))
      · apply (contDiffAt_const (c := (0 : RealForm n k))).congr_of_eventuallyEq
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hchi.2.2 h))] with y hy
        simp [chi,hy]
    exact (TestFunction.ofSupportedInCLM ℝ hK).comp
      (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hchig)
  · intro K hK f
    apply TestFunction.ext
    intro z
    change f z • g z=f z • (cutoffOf K hK z • g z)
    by_cases hz : z∈(K : Set (ComplexModel n))
    · rw [((cutoffOf_spec K hK).2.1 z hz).eq_of_nhds]
      simp
    · rw [f.zero_on_compl hz]
      simp

theorem smoothTensorTestCLM_apply (g : ComplexModel n → RealForm n k)
    (hg : ContDiffOn ℝ ∞ g (U : Set (ComplexModel n))) (phi : 𝓓(U,ℝ)) (z : ComplexModel n) :
    smoothTensorTestCLM U g hg phi z=phi z • g z := rfl

/-- EVERY source smooth (1,0)-family produces its actual continuous LF
wedge testing map on scalar tests, all p including zero. -/
def variableBetaTestCLM {p : ℕ}
    (beta : Fin p → ComplexModel n → ComplexModel n →L[ℂ] ℂ)
    (hbeta : ∀ j,ContDiffOn ℝ ∞ (beta j) (U : Set (ComplexModel n))) :
    𝓓(U,ℝ) →L[ℝ] 𝓓(U,RealForm n (2*p)) :=
  smoothTensorTestCLM U _ (contDiffOn_betaProduct p beta hbeta)

theorem variableBetaTestCLM_apply {p : ℕ}
    (beta : Fin p → ComplexModel n → ComplexModel n →L[ℂ] ℂ)
    (hbeta : ∀ j,ContDiffOn ℝ ∞ (beta j) (U : Set (ComplexModel n)))
    (phi : 𝓓(U,ℝ)) (z : ComplexModel n) :
    variableBetaTestCLM U beta hbeta phi z=phi z • betaProduct (fun j => beta j z) := rfl

end SGPT.PSH.ComplexCurrentDraft
