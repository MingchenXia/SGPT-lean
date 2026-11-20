import SGPT.Okounkov.SourceSliceResolvedTools
import SGPT.Okounkov.SourceTraceModification
import SGPT.Okounkov.PartialBodyDSRepresentative
import SGPT.Okounkov.TranscendentalVolIdLinear
import SGPT.Okounkov.TranscendentalWNStatement

/-! The literal original correction matrix commutes with the actual zero
slice, with the genuine restricted flag lifting on the tail. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceSlice
open Set Matrix
open scoped Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalMain

/-- The actual correction on a vector with first coordinate zero is precisely
the actual correction of its unchanged original tail. -/
theorem cons_zero_vecMul_correction {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) (y : Fin m → ℝ) :
    Fin.cons 0 y ᵥ* correctionMatrixReal hπ =
      Fin.cons 0 (y ᵥ* correctionMatrixReal hπ.tailMap_isFlagLifting) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact vecMul_correctionMatrixReal_zero hπ (Fin.cons 0 y)
  · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1

/-- Zero-coordinate slices of actual corrected bodies are corrected by the
actual restricted tail lifting; no block-matrix certificate is assumed. -/
theorem firstCoordinateSlice_image_correction {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) (B : Set (Fin (m + 1) → ℝ)) :
    firstCoordinateSlice ((fun x => x ᵥ* correctionMatrixReal hπ) '' B) 0 =
      (fun y => y ᵥ* correctionMatrixReal hπ.tailMap_isFlagLifting) ''
        firstCoordinateSlice B 0 := by
  ext y
  constructor
  · rintro ⟨z, hz, heq⟩
    change z ᵥ* correctionMatrixReal hπ = Fin.cons 0 y at heq
    have hz0 : z 0 = 0 := by
      have h := congrFun heq 0
      rw [vecMul_correctionMatrixReal_zero hπ] at h
      exact h
    have hzcons : z = Fin.cons 0 (fun j : Fin m => z j.succ) := by
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      exact hz0
    refine ⟨(fun j : Fin m => z j.succ), ?_, ?_⟩
    · change Fin.cons 0 (fun j : Fin m => z j.succ) ∈ B
      rw [← hzcons]
      exact hz
    · rw [hzcons, cons_zero_vecMul_correction hπ] at heq
      funext j
      exact congrFun heq j.succ
  · rintro ⟨z, hz, heq⟩
    change z ᵥ* correctionMatrixReal hπ.tailMap_isFlagLifting = y at heq
    refine ⟨Fin.cons 0 z, hz, ?_⟩
    change Fin.cons 0 z ᵥ* correctionMatrixReal hπ = Fin.cons 0 y
    rw [cons_zero_vecMul_correction hπ, heq]

/-- The same actual current has the same general body for geometrically
identical smooth forms; this is the proved representative theorem with g=0. -/
theorem generalPartialBody_eq_of_geometricallyEq {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ η : ClosedRealOneOneForm (m + 1) F.carrier}
    (hgeo : η.val.GeometricallyEq θ.val) {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    PartialBody.generalPartialBody F η φ = PartialBody.generalPartialBody F θ φ := by
  have hg : ChartSmooth (n := m + 1) (fun _ : F.carrier => (0 : ℝ)) :=
    fun _ => contDiffOn_const
  have hcoeff : ∀ (e : ComplexChart (m + 1) F.carrier) (z : ComplexModel (m + 1)),
      z ∈ e.val.target → η.val.coeff e z = θ.val.coeff e z +
        smoothDDC (fun _ => (0 : ℝ)) z := by
    intro e z hz
    rw [GlobalPotentialTransforms.smoothDDC_const, add_zero]
    exact hgeo e hz
  simpa only [EReal.coe_zero, sub_zero] using
    (PartialBody.generalPartialBody_sub_smooth hg hcoeff hφ)

/-- The actual restricted modification diagram supplies geometric equality
of the two original pulled-back forms. -/
theorem firstFlagRestriction_pullback_geometricallyEq {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) (θ : ClosedRealOneOneForm (m + 1) F.carrier) :
    (firstFlagRestriction W (ClosedRealOneOneForm.pullback hπ.1.1 θ)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback hπ.tailMap_isFlagLifting.1.1
        (firstFlagRestriction F θ)).val := by
  have h₁ := TranscendentalVolId.pullback_comp_geometricallyEq' hπ.1.1
    (TranscendentalWN.contMDiff_firstFlagInclusion W) θ.val
  have h₂ := TranscendentalVolId.pullback_comp_geometricallyEq'
    (TranscendentalWN.contMDiff_firstFlagInclusion F) hπ.tailMap_isFlagLifting.1.1 θ.val
  exact h₁.symm.trans h₂
end SGPT.Okounkov.SourceSlice
