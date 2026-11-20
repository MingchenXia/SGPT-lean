import SGPT.Okounkov.SourceCurrentValuationRealDivisor
import SGPT.Okounkov.SourceCurrentValuationResidual

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceCurrentValuation
open Set Filter
open scoped Topology Pointwise NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalPartial

/-- Whole source cor:valuationcurrentinPOB membership for every ORIGINAL
positive current in every dimension, using the genuine source body at zero.
There is no supplied trace, model, valuation, rationality or analyticity
certificate. The proof simultaneously handles all positive target currents. -/
theorem flagValuation_mem_generalBody :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n)
      (θ : ClosedRealOneOneForm n F.carrier) (φ : F.carrier → EReal)
      (hφ : IsThetaPshPotential θ.val φ),
      flagValuation F φ ∈ SourceTestCurveAllDimensions.generalBody F θ ⟨φ, hφ⟩ := by
  intro n
  induction n with
  | zero =>
      intro F θ φ hφ
      change flagValuation F φ ∈ ZeroSource.generalBody F θ φ hφ
      rw [ZeroSource.generalBody_eq_partial, ZeroSource.partialOkounkovBody_eq_univ F hφ]
      exact mem_univ _
  | succ m ih =>
      intro F θ φ hφ
      have hKmem (σ : ClosedRealOneOneForm (m + 1) F.carrier)
          (u : F.carrier → EReal) (hK : IsKahlerCurrentPotential σ u) :
          flagValuation F u ∈ generalPartialBody F σ u := by
        have hu := isThetaPshPotential_of_isKahlerCurrentPotential hK
        let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
          (Subtype.val : F.tail.carrier → F.carrier) u).toNNReal
        obtain ⟨E, hE, hKv, hz, hrec⟩ := exists_kahler_normalized_first_residual F hK
        let β : ClosedRealOneOneForm (m + 1) F.carrier := σ - (c : ℝ) • E.curvature
        let v : F.carrier → EReal := extensionAcross (F.flag (1 : Fin (m + 2)))
          (smoothDivisorOffResidual E c u)
        have hv : IsThetaPshPotential β.val v :=
          isThetaPshPotential_of_isKahlerCurrentPotential hKv
        obtain ⟨τ, ψ, hτ, hψ, hP, hslice⟩ :=
          SourceSlice.exists_source_trace_representative_of_kahler_zero F hKv hz
        have htail := ih F.tail (firstFlagRestriction F β) ψ hψ
        have hres : Fin.cons 0 (flagValuation F.tail ψ) ∈ generalPartialBody F β v := by
          change flagValuation F.tail ψ ∈ firstCoordinateSlice (generalPartialBody F β v) 0
          rw [hslice]
          exact htail
        have hdiv := smul_flagValuation_mem_generalPartialBody_weight F hE c.property
        have hcu := isThetaPshPotential_nonneg_smul
          (TranscendentalSlice.weight_mem_analyticCurrents hE).1 c.property
        have hsum : Fin.cons 0 (flagValuation F.tail ψ) +
            (c : ℝ) • flagValuation F E.weight ∈
            generalPartialBody F (β + (c : ℝ) • E.curvature)
              (fun x => v x + ((c : ℝ) : EReal) * E.weight x) :=
          generalPartialBody_add_subset hv hcu ⟨_, hres, _, hdiv, rfl⟩
        have hvec : Fin.cons 0 (flagValuation F.tail ψ) +
            (c : ℝ) • flagValuation F E.weight = flagValuation F u := by
          rw [TranscendentalSlice.flagValuation_weight hE,
            flagValuation_eq_cons_of_residual_sourceTrace F hu hE hτ hψ hP]
          funext i
          exact Fin.cases (by simp [c]) (fun j => by simp) i
        have hform : β + (c : ℝ) • E.curvature = σ := sub_add_cancel _ _
        have hfun : (fun x => v x + ((c : ℝ) : EReal) * E.weight x) = u := hrec
        simpa only [hform, hfun, hvec] using hsum
      change flagValuation F φ ∈ generalPartialBody F θ φ
      rw [generalPartialBody, mem_iInter]
      intro j
      have he : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
      have hK := isKahlerCurrentPotential_add_smul hφ F.omega he
      have hmem := hKmem _ φ hK
      rwa [generalPartialBody_eq_kahlerPartialBody hK] at hmem

/-- Exact positive-dimensional source carrier, with an arbitrary original
positive current and no auxiliary source-output assumptions. -/
theorem flagValuation_mem_generalPartialBody {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    flagValuation F φ ∈ generalPartialBody F θ φ :=
  flagValuation_mem_generalBody (m + 1) F θ φ hφ

/-- WHOLE printed cor:valuationcurrentinPOB, including the original
traditional-body inclusion on the domain where Δ(α) is defined. -/
theorem valuationcurrentinPOB {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ)
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ)) :
    flagValuation F φ ∈ generalPartialBody F θ φ ∧
      generalPartialBody F θ φ ⊆ tradOkounkovBody F θ :=
  ⟨flagValuation_mem_generalPartialBody F hφ,
    Valuative.generalPartialBody_subset_tradOkounkovBody hφ hbig⟩

end SGPT.Okounkov.SourceCurrentValuation
