import SGPT.Foundations.Schemes.NativePolarizedResidueGlobalSections
import SGPT.Foundations.Schemes.NativeProjectiveTwistedHilbertPolynomial
/-!
# NativePolarizedResidueHilbert

Actual closed-projective chart finiteness/quasicoherence and the genuine residue global-section equivalence derive eventual dimension polynomials on every original line-power residue progression. Native Fano geometry retains the ORIGINAL structure map and gives finitely many actual residue polynomials with one uniform bound. Degree is bounded by ambient embedding dimension; intrinsic dimension and intersection leading coefficient remain open.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {X : Scheme} (L : IntrinsicLineBundle X)
    {K : Type} [Field K] (n : ℕ) (f : X ⟶ polynomialProj K n) [hf : IsClosedImmersion f]
    (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (e : bundleTensorPower L.sheaf q ≅
    (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

include e hf in
/-- Genuine positive projective geometry derives an eventual polynomial for actual line-power section dimensions in every real residue progression. -/
theorem nativePolarizedResidueSectionDimension_eventualPolynomial (r : ℕ) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ n ∧ ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      letI := schemeGlobalSectionModule (actualPolynomialProjectivePullbackStructureMap f)
        (bundleTensorPower L.sheaf (q * m + r))
      (Module.finrank K (bundlePowerGlobalSections L.sheaf (q * m + r)) : ℚ) = Q.eval (m : ℚ) := by
  let M := (Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)
  have : ∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
      Γ(polynomialProjModuleChart M j, ⊤) :=
    fun j ↦ polynomialProjPushforwardChartSections_finite f (L.atlas.tensorPower r) j
  have : ∀ j, (polynomialProjModuleChart M j).IsQuasicoherent :=
    fun j ↦ polynomialProjPushforwardChart_isQuasicoherent f (L.atlas.tensorPower r) j
  obtain ⟨Q, hQdeg, b, hQ⟩ := polynomialProjTwistedSectionDimension_eventualPolynomial K n M
  refine ⟨Q, hQdeg, b, fun m hm ↦ ?_⟩
  let := schemeGlobalSectionModule (actualPolynomialProjectivePullbackStructureMap f)
    (bundleTensorPower L.sheaf (q * m + r))
  have he := (nativePolarizedResidueGlobalSectionsEquiv L n f q e m r).finrank_eq
  exact (congrArg (fun a : ℕ ↦ (a : ℚ)) he).trans (hQ m hm).2

include e hf in
/-- The actual residue Hilbert polynomial retains any original structural map identified by the genuine projective base compatibility. -/
theorem nativePolarizedResidueSectionDimension_eventualPolynomial_over
    (p : X ⟶ Spec (.of K)) (hp : actualPolynomialProjectivePullbackStructureMap f = p) (r : ℕ) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ n ∧ ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      letI := schemeGlobalSectionModule p (bundleTensorPower L.sheaf (q * m + r))
      (Module.finrank K (bundlePowerGlobalSections L.sheaf (q * m + r)) : ℚ) = Q.eval (m : ℚ) := by
  subst p
  exact nativePolarizedResidueSectionDimension_eventualPolynomial L n f q e r

/-- The actual native Fano anticanonical section dimensions have a genuine eventual polynomial along every original positive-polarization residue progression. -/
theorem SmoothProjectiveFano.nativeAnticanonicalResidueSectionDimension_eventualPolynomial {d : ℕ}
    (F : SmoothProjectiveFano d) (r : ℕ) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ F.projective.ambientDimension ∧
      ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
        letI := schemeGlobalSectionModule F.structureMap
          (bundleTensorPower (smoothAnticanonicalLineBundle F.structureMap d).sheaf
            (F.anticanonicalPower * m + r))
        (Module.finrank ℂ
          (bundlePowerGlobalSections (smoothAnticanonicalLineBundle F.structureMap d).sheaf
            (F.anticanonicalPower * m + r)) : ℚ) = Q.eval (m : ℚ) := by
  exact nativePolarizedResidueSectionDimension_eventualPolynomial_over
    (smoothAnticanonicalLineBundle F.structureMap d) F.projective.ambientDimension F.projective.map
      F.anticanonicalPower F.positivityIso F.structureMap F.projective.over_base r

/-- The actual finitely many native Fano residue polynomials admit one genuine comparison threshold, chosen uniformly over all original polarization residues. -/
theorem SmoothProjectiveFano.nativeAnticanonicalResidueSectionDimension_uniformPolynomial {d : ℕ}
    (F : SmoothProjectiveFano d) :
    ∃ Q : Fin F.anticanonicalPower → Polynomial ℚ,
      (∀ r, (Q r).natDegree ≤ F.projective.ambientDimension) ∧
      ∃ b : ℕ, ∀ (r : Fin F.anticanonicalPower) (m : ℕ), b ≤ m →
        letI := schemeGlobalSectionModule F.structureMap
          (bundleTensorPower (smoothAnticanonicalLineBundle F.structureMap d).sheaf
            (F.anticanonicalPower * m + r.val))
        (Module.finrank ℂ
          (bundlePowerGlobalSections (smoothAnticanonicalLineBundle F.structureMap d).sheaf
            (F.anticanonicalPower * m + r.val)) : ℚ) = (Q r).eval (m : ℚ) := by
  classical
  choose Q hQ b hb using fun r : Fin F.anticanonicalPower ↦
    F.nativeAnticanonicalResidueSectionDimension_eventualPolynomial r.val
  refine ⟨Q, hQ, Finset.univ.sup b, fun r m hm ↦ hb r m ?_⟩
  exact (Finset.le_sup (Finset.mem_univ r)).trans hm

end
end SGPT.Foundations.Schemes
