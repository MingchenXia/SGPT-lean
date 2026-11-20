import SGPT.Foundations.Schemes.PolynomialTwistedChartGenerators
import SGPT.Foundations.Schemes.NativeProjectivePowerCoordinateFrames
import SGPT.Foundations.Schemes.NativePositiveProjectiveCoordinateSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual power coordinate applied to the original global one has
coefficient one on its OWN true chart, including the literal zero power. -/
theorem nativePolynomialPowerCoordinateHom_global_coefficients_one
    (k : ℕ) (i : Fin (n + 1)) :
    atlasPowerGlobalCoefficients (polynomialProjTwistingLine K n).atlas k i
      ((nativePolynomialPowerCoordinateHom K n k i).val.app (.op ⊤) (1 : Γ(polynomialProj K n, ⊤))) = 1 := by
  unfold atlasPowerGlobalCoefficients
  rw [nativeGlobalHom_one_restrict]
  have h := nativeGlobalGeneratorFrame_hom_one (nativePolynomialPowerCoordinateHom K n k i)
    (polynomialProjCoordinateOpen K n i) (𝟙 _)
  rw [nativePolynomialPowerCoordinateHom_generatorFrame] at h
  exact h

variable (M : (polynomialProj K n).Modules)
  [∀ j, Module.Finite (polynomialProjCoordinateRing K n j) Γ(polynomialProjModuleChart M j, ⊤)]
  [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]

/-- A genuine finite supremum of the CONCRETE original extension degrees;
the empty-index case has bound zero. -/
def polynomialProjCommonTwistGeneratorBound : ℕ :=
  Finset.univ.sup (polynomialProjFiniteChartGeneratorDegree K n M)

/-- Every actual concrete generator degree is at most the same finite bound. -/
theorem polynomialProjFiniteChartGeneratorDegree_le_commonBound
    (b : polynomialProjFiniteChartGeneratorIndex K n M) :
    polynomialProjFiniteChartGeneratorDegree K n M b ≤ polynomialProjCommonTwistGeneratorBound K n M :=
  Finset.le_sup (Finset.mem_univ b)

/-- Pad each actual generator by its OWN coordinate power to the SAME
actual degree D, preserving its original coefficient on its own chart. -/
def polynomialProjCommonDegreeChartGenerator (D : ℕ)
    (hD : polynomialProjCommonTwistGeneratorBound K n M ≤ D)
    (b : polynomialProjFiniteChartGeneratorIndex K n M) :
    bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M D :=
  let d := polynomialProjFiniteChartGeneratorDegree K n M b
  let hd : d ≤ D := (polynomialProjFiniteChartGeneratorDegree_le_commonBound K n M b).trans hD
  (Nat.sub_add_cancel hd) ▸ atlasTwistedGlobalAction (polynomialProjTwistingLine K n).atlas M
    (D - d) d ((nativePolynomialPowerCoordinateHom K n (D - d) b.1).val.app (.op ⊤)
      (1 : Γ(polynomialProj K n, ⊤)))
    (polynomialProjFiniteChartGeneratorTwist K n M b)

/-- The padded common-degree section has EXACTLY its original own-chart
generator coefficient, not merely a spanning or asymptotic readback. -/
theorem polynomialProjCommonDegreeChartGenerator_coefficient_self (D : ℕ)
    (hD : polynomialProjCommonTwistGeneratorBound K n M ≤ D)
    (b : polynomialProjFiniteChartGeneratorIndex K n M) :
    atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M D b.1
      (polynomialProjCommonDegreeChartGenerator K n M D hD b) =
        polynomialProjFiniteChartGeneratorSection K n M b := by
  have hcast {d e : ℕ} (h : d = e)
      (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M d) :
      atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M e b.1 (h ▸ t) =
        atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M d b.1 t := by
    cases h
    rfl
  unfold polynomialProjCommonDegreeChartGenerator
  rw [hcast, atlasTwistedGlobalAction_coefficients,
    nativePolynomialPowerCoordinateHom_global_coefficients_one, one_smul,
    polynomialProjFiniteChartGeneratorTwist_coefficient]

/-- For EVERY D beyond the actual finite bound, the SAME finite family of
genuine degree-D globals spans every original native chart by its true coefficients. -/
theorem polynomialProjCommonDegreeChartGeneratorCoefficients_span (D : ℕ)
    (hD : polynomialProjCommonTwistGeneratorBound K n M ≤ D) (j : Fin (n + 1)) :
    Submodule.span (polynomialProjCoordinateRing K n j)
      (Set.range (fun b ↦ (polynomialProjChartTopSectionsIso M j).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M D j
          (polynomialProjCommonDegreeChartGenerator K n M D hD b)))) = ⊤ := by
  apply top_unique
  rw [← polynomialProjFiniteChartGenerators_span K n M j]
  apply Submodule.span_mono
  rintro _ ⟨b, rfl⟩
  refine ⟨⟨j, b⟩, ?_⟩
  have hc := congrArg (fun z : Γ(M, polynomialProjCoordinateOpen K n j) ↦
    (polynomialProjChartTopSectionsIso M j).inv z)
    (polynomialProjCommonDegreeChartGenerator_coefficient_self K n M D hD ⟨j, b⟩)
  exact hc.trans (Iso.hom_inv_id_apply _ _)

/-- Actual closed-projective line geometry PRODUCES the common bound,
finite index and all genuine common-degree spanning families, with no
generation, degree or intersection outcome certificate input. -/
theorem closedPolynomialProjPushforward_exists_commonDegree_chart_generators
    {X : Scheme} (f : X ⟶ polynomialProj K n) [IsClosedImmersion f]
    {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ (m : Fin (n + 1) → ℕ) (B : ℕ), ∀ D : ℕ, B ≤ D →
      ∃ t : (Σ j : Fin (n + 1), Fin (m j)) →
        bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
          ((Scheme.Modules.pushforward f).obj L) D,
        ∀ j, Submodule.span (polynomialProjCoordinateRing K n j)
          (Set.range (fun b ↦ (polynomialProjChartTopSectionsIso ((Scheme.Modules.pushforward f).obj L) j).inv
            (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
              ((Scheme.Modules.pushforward f).obj L) D j (t b)))) = ⊤ := by
  let M := (Scheme.Modules.pushforward f).obj L
  let : ∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
      Γ(polynomialProjModuleChart M j, ⊤) := fun j ↦ polynomialProjPushforwardChartSections_finite f a j
  let : ∀ j, (polynomialProjModuleChart M j).IsQuasicoherent :=
    fun j ↦ polynomialProjPushforwardChart_isQuasicoherent f a j
  refine ⟨polynomialProjFiniteChartGeneratorCount K n M,
    polynomialProjCommonTwistGeneratorBound K n M, fun D hD ↦ ?_⟩
  exact ⟨polynomialProjCommonDegreeChartGenerator K n M D hD,
    polynomialProjCommonDegreeChartGeneratorCoefficients_span K n M D hD⟩

end
end SGPT.Foundations.Schemes
