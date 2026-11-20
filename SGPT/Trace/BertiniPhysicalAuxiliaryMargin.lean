import SGPT.Trace.BertiniFamilyMatchedCurvature
import SGPT.Trace.BertiniAuxiliaryCurvatureChoice
import SGPT.Trace.BertiniRelativeBasePositivity

/-! Original positive powers, chosen after the manufactured C, produce
literal all-frame raw sharp-extension margins on actual full families. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Bergman.NativeHermitianMetric SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.TwistedL2
open SGPT.Trace.BertiniRelativeBasePositivity SGPT.Trace.BertiniAuxiliaryCurvatureChoice

variable {d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem familyPhysical_raw_curvature_of_original
    (omega : KahlerBackground (d + 1) X)
    (L : HermitianHolomorphicLineBundle (d + 1) X) (hL : IsSourceSmoothHermitianMetric L)
    (A : ℝ) (hA : ∀ (c : ComplexChart (d + 1) X) (z : ComplexModel (d + 1)),
      z ∈ c.val.target → ∀ w : ComplexModel (d + 1),
      A * omega.form.val.coeff c z ![w,Complex.I • w] ≤
        (sourceNativeFirstChernForm L hL).val.coeff c z ![w,Complex.I • w])
    {N : ℕ}
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
    (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val)) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (c : ComplexChart (d + 1) (familyIncidence p i a v U))
      (e : AtlasFrame (familyNativePhysicalModel p i a v U hsm L)) (ρ : ComplexModel (d + 1) → ℝ),
      IsChartDensity (familyMatchedVolume p i a v U hsm) c ρ →
      ∀ z ∈ chartFrameDomain (familyNativePhysicalModel p i a v U hsm L) c e,
      ∀ w : ComplexModel (d + 1),
      Real.pi * A * familyXQuad p i a v U p.contMDiff hsm omega c z w ≤
        leviForm (SGPT.Trace.TwistedL2.localWeight (familyNativePhysicalModel p i a v U hsm L)
          c e ρ (fun _ => 0)) z w := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro c e ρ hρ z hz w
  rw [familyPhysical_localWeight_levi_originalChern p i a v U hsm L hL c e ρ hρ z hz w]
  let q := familyNativeXMap p i a v U hsm
  let cX := complexChartAt (n := d + 1) (q (c.val.symm z))
  let F := HolomorphicMaps.coordinateMap q c cX
  let D := fderiv ℝ F z
  have hzc : z ∈ HolomorphicMaps.coordinateDomain q c cX := ⟨hz.1,mem_complexChartAt_source _⟩
  have hFz : F z ∈ cX.val.target := HolomorphicMaps.coordinateMap_mem_target hzc
  have hvec (u v : ComplexModel (d + 1)) : D ∘ ![u,v] = ![D u,D v] := by
    funext k
    fin_cases k <;> rfl
  have hDI : D (Complex.I • w) = Complex.I • D w :=
    HolomorphicMaps.coordinateMap_fderiv_map_smul_complex q.contMDiff c cX hzc Complex.I w
  have hθ : (ClosedRealOneOneForm.pullback q.contMDiff (sourceNativeFirstChernForm L hL)).val.coeff
      c z ![w,Complex.I • w] = (sourceNativeFirstChernForm L hL).val.coeff cX (F z) ![D w,Complex.I • D w] := by
    rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff q.contMDiff _ c cX hzc,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,hvec,hDI]
  have hω : familyXQuad p i a v U p.contMDiff hsm omega c z w =
      omega.form.val.coeff cX (F z) ![D w,Complex.I • D w] := by
    change (SmoothRealForm.pullback q.contMDiff omega.form.val).coeff c z ![w,Complex.I • w] = _
    rw [SmoothRealForm.pullback_coeff q.contMDiff _ c cX hzc,
      ContinuousAlternatingMap.compContinuousLinearMap_apply,hvec,hDI]
  rw [hθ,hω]
  have h := mul_le_mul_of_nonneg_left (hA cX (F z) hFz (D w)) Real.pi_pos.le
  exact (by simpa only [mul_assoc] using h)

theorem exists_actual_auxiliary_family_raw_curvature_all_twists
    (omega : KahlerBackground (d + 1) X)
    (G E : HermitianHolomorphicLineBundle (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler) (C κ : ℝ) :
    ∃ a₀ : ℕ, 0 < a₀ ∧ ∀ k : ℕ, a₀ ≤ k →
      ∀ (S : HermitianHolomorphicLineBundle (d + 1) X) (hS : IsSourceSmoothHermitianMetric S),
      (sourceNativeFirstChernForm S hS).val.IsSemipositive → ∀ b : ℕ,
      ∀ (N : ℕ)
        (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
        (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
        (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val)),
      letI := familyChartedSpace p i a v U p.contMDiff hsm
      letI := isComplexManifold_family p i a v U p.contMDiff hsm
      let L := twistedPower S (twistedPower G E k) b
      ∀ (c : ComplexChart (d + 1) (familyIncidence p i a v U))
        (e : AtlasFrame (familyNativePhysicalModel p i a v U hsm L)) (ρ : ComplexModel (d + 1) → ℝ),
        IsChartDensity (familyMatchedVolume p i a v U hsm) c ρ →
        ∀ z ∈ chartFrameDomain (familyNativePhysicalModel p i a v U hsm L) c e,
        ∀ w : ComplexModel (d + 1),
        Real.pi * (C + κ) * familyXQuad p i a v U p.contMDiff hsm omega c z w ≤
          leviForm (SGPT.Trace.TwistedL2.localWeight (familyNativePhysicalModel p i a v U hsm L)
            c e ρ (fun _ => 0)) z w := by
  obtain ⟨a₀,ha₀,hchoice⟩ := exists_actual_native_auxiliary_for_all_semipositive_twists omega G E hG hE hGpos C κ
  refine ⟨a₀,ha₀,?_⟩
  intro k hk S hS hSsemi b N p i a v U hsm
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact familyPhysical_raw_curvature_of_original omega (twistedPower S (twistedPower G E k) b)
    (sourceNativeTwistedPower_smooth S (twistedPower G E k) hS
      (sourceNativeTwistedPower_smooth G E hG hE k) b)
    (C + κ) (hchoice k hk S hS hSsemi b) p i a v U hsm

end SGPT.Trace.BertiniFamilyCanonical
