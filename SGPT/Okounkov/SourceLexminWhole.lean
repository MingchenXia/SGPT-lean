import SGPT.Okounkov.SourceLexminTranslatedBody
import SGPT.Okounkov.SourceLexminVectorOrdering

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceLexmin
open Set Filter
open scoped Topology Pointwise NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending ThetaPshCodimTwoExtension
open SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.PartialBody
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalPartial

/-- Whole original lexicographic least-element assertion, strengthened to
ALL original positive currents and every actual dimension. The genuine
source body, original vector, real generic coefficients and poles remain
unchanged. All residuals, traces, tail readers and body points are produced. -/
theorem isLeast_generalBody :
    ∀ (n : ℕ) (F : OriginalFlagGeometry.{u} n)
      (θ : ClosedRealOneOneForm n F.carrier) (u : F.carrier → EReal)
      (hu : IsThetaPshPotential θ.val u),
      IsLeast (toLex '' SourceTestCurveAllDimensions.generalBody F θ ⟨u, hu⟩)
        (toLex (flagValuation F u)) := by
  intro n
  induction n with
  | zero =>
      intro F θ u hu
      refine ⟨⟨_, SourceCurrentValuation.flagValuation_mem_generalBody 0 F θ u hu, rfl⟩, ?_⟩
      rintro _ ⟨x, _hx, rfl⟩
      have heq : flagValuation F u = x := funext fun i => Fin.elim0 i
      rw [heq]
  | succ m ih =>
      intro F θ u hu
      have hKleast (σ : ClosedRealOneOneForm (m + 1) F.carrier)
          (φ : F.carrier → EReal) (hK : IsKahlerCurrentPotential σ φ)
          (x : Fin (m + 1) → ℝ) (hx : x ∈ generalPartialBody F σ φ) :
          toLex (flagValuation F φ) ≤ toLex x := by
        have hφ := isThetaPshPotential_of_isKahlerCurrentPotential hK
        let c : ℝ≥0 := (sourceGenericLelongNumber (n := m + 1)
          (Subtype.val : F.tail.carrier → F.carrier) φ).toNNReal
        obtain ⟨E, hE, hKv, hz, hrec⟩ :=
          SourceCurrentValuation.exists_kahler_normalized_first_residual F hK
        let β : ClosedRealOneOneForm (m + 1) F.carrier := σ - (c : ℝ) • E.curvature
        let v : F.carrier → EReal := extensionAcross (F.flag (1 : Fin (m + 2)))
          (smoothDivisorOffResidual E c φ)
        have hv : IsThetaPshPotential β.val v :=
          isThetaPshPotential_of_isKahlerCurrentPotential hKv
        have hform : β + (c : ℝ) • E.curvature = σ := sub_add_cancel _ _
        have hfun : (fun y => v y + ((c : ℝ) : EReal) * E.weight y) = φ := hrec
        have htrans : generalPartialBody F σ φ =
            ((c : ℝ) • flagValuation F E.weight) +ᵥ generalPartialBody F β v := by
          have ht : generalPartialBody F (β + (c : ℝ) • E.curvature)
              (fun y => v y + ((c : ℝ) : EReal) * E.weight y) =
              ((c : ℝ) • flagValuation F E.weight) +ᵥ generalPartialBody F β v :=
            generalPartialBody_eq_divisor_translate_of_kahler F hKv hE c.property
          simpa only [hform, hfun] using ht
        rw [htrans] at hx
        obtain ⟨z, hzb, rfl⟩ := hx
        change toLex (flagValuation F φ) ≤ toLex (((c : ℝ) • flagValuation F E.weight) + z)
        obtain ⟨τ, ψ, hτ, hψ, hP, hslice⟩ :=
          SourceSlice.exists_source_trace_representative_of_kahler_zero F hKv hz
        have hvalue : flagValuation F φ = Fin.cons (c : ℝ) (flagValuation F.tail ψ) :=
          SourceCurrentValuation.flagValuation_eq_cons_of_residual_sourceTrace F hφ hE hτ hψ hP
        have hhead : 0 ≤ z 0 := by
          have h := Valuative.flagValuation_zero_le_of_mem_generalPartialBody hv hzb
          rw [SourceSlice.flagValuation_first_zero_of_source_generic_zero F hv hz] at h
          exact h
        have hvec : ((c : ℝ) • flagValuation F E.weight) + z =
            Fin.cons ((c : ℝ) + z 0) (Fin.tail z) := by
          rw [TranscendentalSlice.flagValuation_weight hE]
          funext i
          exact Fin.cases (by simp) (fun j => by simp [Fin.tail]) i
        rw [hvalue, hvec]
        rcases hhead.eq_or_lt with hz0 | hzpos
        · have hrepr : Fin.cons 0 (Fin.tail z) = z := by
            funext i
            exact Fin.cases (by simpa only [Fin.cons_zero] using hz0)
              (fun j => by simp [Fin.tail]) i
          have htailmem : Fin.tail z ∈ SourceTestCurveAllDimensions.generalBody
              F.tail (firstFlagRestriction F β) ⟨ψ, hψ⟩ := by
            rw [← hslice]
            change Fin.cons 0 (Fin.tail z) ∈ generalPartialBody F β v
            rwa [hrepr]
          have htail := (ih F.tail (firstFlagRestriction F β) ψ hψ).2 ⟨_, htailmem, rfl⟩
          simpa only [← hz0, add_zero] using toLex_cons_le_cons (c : ℝ) htail
        · exact (toLex_cons_lt_cons_of_head_lt (by linarith : (c : ℝ) < c + z 0)
            (flagValuation F.tail ψ) (Fin.tail z)).le
      refine ⟨⟨_, SourceCurrentValuation.flagValuation_mem_generalBody (m + 1) F θ u hu, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : x ∈ kahlerPartialBody F (θ + (1 : ℝ) • F.omega.form) u := by
        change x ∈ generalPartialBody F θ u at hx
        rw [generalPartialBody_eq_iInter_pos hu, mem_iInter₂] at hx
        exact hx 1 zero_lt_one
      have hK := isKahlerCurrentPotential_add_smul hu F.omega zero_lt_one
      have hx1' : x ∈ generalPartialBody F (θ + (1 : ℝ) • F.omega.form) u := by
        rwa [generalPartialBody_eq_kahlerPartialBody hK]
      exact hKleast _ u hK x hx1'

/-- Exact original thm:KahcurrminOkoun on the literal positive-dimensional
body, with only the original Kähler-current premise. -/
theorem kahcurrminOkoun {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hK : IsKahlerCurrentPotential θ u) :
    IsLeast (toLex '' generalPartialBody F θ u) (toLex (flagValuation F u)) :=
  isLeast_generalBody (m + 1) F θ u (isThetaPshPotential_of_isKahlerCurrentPotential hK)

/-- Whole printed cor:KahcurrminOkoun, in fact strengthened to all original
positive currents without needing their additional positive I-volume premise. -/
theorem positive_current_lexmin {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    {θ : ClosedRealOneOneForm (m + 1) F.carrier} {u : F.carrier → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    IsLeast (toLex '' generalPartialBody F θ u) (toLex (flagValuation F u)) :=
  isLeast_generalBody (m + 1) F θ u hu

end SGPT.Okounkov.SourceLexmin
