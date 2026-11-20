import SGPT.Foundations.Schemes.PolynomialTwistedGlobalExtension
import SGPT.Foundations.Schemes.PolynomialTwistedFiniteSpan

/-! # Genuine finite homogeneous global generators for actual projective charts

Finite actual affine-chart generators are extended to true global tensor
twists. Their normalized coefficients generate every actual chart module;
their literal polynomial span is finite and carries its native integral grading.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ) (M : (polynomialProj K n).Modules)
attribute [local instance] MvPolynomial.gradedAlgebra

section FiniteCharts

variable [∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
  Γ(polynomialProjModuleChart M j, ⊤)]

/-- The actual finite generator count chosen in the native module of each true affine chart. -/
def polynomialProjFiniteChartGeneratorCount (j : Fin (n + 1)) : ℕ :=
  (Module.Finite.exists_fin (R := polynomialProjCoordinateRing K n j)
    (M := Γ(polynomialProjModuleChart M j, ⊤))).choose

/-- A finite family of genuine native affine-chart sections spanning that actual module. -/
def polynomialProjFiniteChartGenerators (j : Fin (n + 1)) :
    Fin (polynomialProjFiniteChartGeneratorCount K n M j) →
      Γ(polynomialProjModuleChart M j, ⊤) :=
  (Module.Finite.exists_fin (R := polynomialProjCoordinateRing K n j)
    (M := Γ(polynomialProjModuleChart M j, ⊤))).choose_spec.choose

/-- The chosen finite chart sections truly span the entire actual chart module. -/
theorem polynomialProjFiniteChartGenerators_span (j : Fin (n + 1)) :
    Submodule.span (polynomialProjCoordinateRing K n j)
      (Set.range (polynomialProjFiniteChartGenerators K n M j)) = ⊤ :=
  (Module.Finite.exists_fin (R := polynomialProjCoordinateRing K n j)
    (M := Γ(polynomialProjModuleChart M j, ⊤))).choose_spec.choose_spec

/-- A genuine finite index, consisting of a chart and one of its actual generators. -/
abbrev polynomialProjFiniteChartGeneratorIndex :=
  Σ j : Fin (n + 1), Fin (polynomialProjFiniteChartGeneratorCount K n M j)

/-- The actual chart generator transported to the same native projective coordinate open. -/
def polynomialProjFiniteChartGeneratorSection (b : polynomialProjFiniteChartGeneratorIndex K n M) :
    Γ(M, polynomialProjCoordinateOpen K n b.1) :=
  (polynomialProjChartTopSectionsIso M b.1).hom
    (polynomialProjFiniteChartGenerators K n M b.1 b.2)

section ActualExtensions

variable [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]

/-- The actual twist degree produced by the genuine global extension theorem for each chart generator. -/
def polynomialProjFiniteChartGeneratorDegree (b : polynomialProjFiniteChartGeneratorIndex K n M) : ℕ :=
  (polynomialProjCoordinateSection_twistedGlobalExtension K n M b.1
    (polynomialProjFiniteChartGeneratorSection K n M b)).choose

/-- Genuine global tensor sections obtained by extending actual finite affine-chart generators. -/
def polynomialProjFiniteChartGeneratorTwist (b : polynomialProjFiniteChartGeneratorIndex K n M) :
    bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M
      (polynomialProjFiniteChartGeneratorDegree K n M b) :=
  (polynomialProjCoordinateSection_twistedGlobalExtension K n M b.1
    (polynomialProjFiniteChartGeneratorSection K n M b)).choose_spec.choose

/-- Every true global extension recovers its actual original chart generator in the source frame. -/
theorem polynomialProjFiniteChartGeneratorTwist_coefficient
    (b : polynomialProjFiniteChartGeneratorIndex K n M) :
    atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M
      (polynomialProjFiniteChartGeneratorDegree K n M b) b.1
      (polynomialProjFiniteChartGeneratorTwist K n M b) =
        polynomialProjFiniteChartGeneratorSection K n M b :=
  (polynomialProjCoordinateSection_twistedGlobalExtension K n M b.1
    (polynomialProjFiniteChartGeneratorSection K n M b)).choose_spec.choose_spec

/-- Every chosen homogeneous section has a true normalized coefficient in each native affine-chart module. -/
def polynomialProjFiniteChartGeneratorCoefficients (j : Fin (n + 1))
    (b : polynomialProjFiniteChartGeneratorIndex K n M) : Γ(polynomialProjModuleChart M j, ⊤) :=
  (polynomialProjChartTopSectionsIso M j).inv
    (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M
      (polynomialProjFiniteChartGeneratorDegree K n M b) j
      (polynomialProjFiniteChartGeneratorTwist K n M b))

/-- The true normalized source coefficient is literally the original chosen native affine generator. -/
theorem polynomialProjFiniteChartGeneratorCoefficients_self (j : Fin (n + 1))
    (b : Fin (polynomialProjFiniteChartGeneratorCount K n M j)) :
    polynomialProjFiniteChartGeneratorCoefficients K n M j ⟨j, b⟩ =
      polynomialProjFiniteChartGenerators K n M j b := by
  unfold polynomialProjFiniteChartGeneratorCoefficients
  rw [polynomialProjFiniteChartGeneratorTwist_coefficient]
  exact Iso.hom_inv_id_apply _ _

/-- The true coefficients of the genuine finite homogeneous family generate every actual native chart module. -/
theorem polynomialProjFiniteChartGeneratorCoefficients_span (j : Fin (n + 1)) :
    Submodule.span (polynomialProjCoordinateRing K n j)
      (Set.range (polynomialProjFiniteChartGeneratorCoefficients K n M j)) = ⊤ := by
  apply top_unique
  rw [← polynomialProjFiniteChartGenerators_span K n M j]
  apply Submodule.span_mono
  rintro _ ⟨b, rfl⟩
  exact ⟨⟨j, b⟩, polynomialProjFiniteChartGeneratorCoefficients_self K n M j b⟩

/-- The literal finite homogeneous polynomial submodule built from those genuine global extensions. -/
abbrev polynomialProjChartGeneratedTwistedSpan :=
  polynomialProjTwistedFiniteSpan K n M (polynomialProjFiniteChartGeneratorDegree K n M)
    (polynomialProjFiniteChartGeneratorTwist K n M)

/-- Its true integral degree pieces are inherited from the native actual twisted-section grading. -/
abbrev polynomialProjChartGeneratedTwistedSpanPiece :=
  polynomialProjTwistedFiniteSpanPiece K n M (polynomialProjFiniteChartGeneratorDegree K n M)
    (polynomialProjFiniteChartGeneratorTwist K n M)

/-- The actual chart-generated polynomial span is finite by its literal finite homogeneous generators. -/
instance polynomialProjChartGeneratedTwistedSpan_finite :
    Module.Finite (MvPolynomial (Fin (n + 1)) K) (polynomialProjChartGeneratedTwistedSpan K n M) :=
  polynomialProjTwistedFiniteSpan_finite K n M (polynomialProjFiniteChartGeneratorDegree K n M)
    (polynomialProjFiniteChartGeneratorTwist K n M)

/-- The actual chart-generated span has its native internal integral decomposition. -/
instance polynomialProjChartGeneratedTwistedSpanDecomposition :
    DirectSum.Decomposition (polynomialProjChartGeneratedTwistedSpanPiece K n M) :=
  polynomialProjTwistedFiniteSpanDecomposition K n M (polynomialProjFiniteChartGeneratorDegree K n M)
    (polynomialProjFiniteChartGeneratorTwist K n M)

/-- Its native degree pieces obey the actual integral polynomial homogeneous multiplication law. -/
instance polynomialProjChartGeneratedTwistedSpanGradedSMul :
    SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjChartGeneratedTwistedSpanPiece K n M) :=
  polynomialProjTwistedFiniteSpanGradedSMul K n M (polynomialProjFiniteChartGeneratorDegree K n M)
    (polynomialProjFiniteChartGeneratorTwist K n M)

/-- Every genuine chart-generator extension is an actual element of the constructed finite polynomial span. -/
def polynomialProjChartGeneratedTwistedGenerator (b : polynomialProjFiniteChartGeneratorIndex K n M) :
    polynomialProjChartGeneratedTwistedSpan K n M :=
  ⟨polynomialProjTwistedFiniteGenerators K n M (polynomialProjFiniteChartGeneratorDegree K n M)
      (polynomialProjFiniteChartGeneratorTwist K n M) b,
    Submodule.subset_span ⟨b, rfl⟩⟩

/-- Those literal included generators belong to their actual integral homogeneous degree pieces. -/
theorem polynomialProjChartGeneratedTwistedGenerator_mem_piece
    (b : polynomialProjFiniteChartGeneratorIndex K n M) :
    polynomialProjChartGeneratedTwistedGenerator K n M b ∈
      polynomialProjChartGeneratedTwistedSpanPiece K n M
        (polynomialProjFiniteChartGeneratorDegree K n M b : ℤ) :=
  polynomialProjTwistedSectionPiece_ofTwistedSection K n M
    (polynomialProjFiniteChartGeneratorDegree K n M b) (polynomialProjFiniteChartGeneratorTwist K n M b)

end ActualExtensions

end FiniteCharts

/-- Genuine closed-projective line geometry constructs a finite homogeneous global family generating every actual chart. -/
theorem closedPolynomialProjPushforward_exists_finite_twisted_chart_generators
    {X : Scheme} (f : X ⟶ polynomialProj K n) [IsClosedImmersion f]
    {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ (m : Fin (n + 1) → ℕ) (d : (Σ j : Fin (n + 1), Fin (m j)) → ℕ)
      (t : ∀ b, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
        ((Scheme.Modules.pushforward f).obj L) (d b)),
      ∀ j, Submodule.span (polynomialProjCoordinateRing K n j)
        (Set.range (fun b => (polynomialProjChartTopSectionsIso ((Scheme.Modules.pushforward f).obj L) j).inv
          (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
            ((Scheme.Modules.pushforward f).obj L) (d b) j (t b)))) = ⊤ := by
  let M := (Scheme.Modules.pushforward f).obj L
  let : ∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
      Γ(polynomialProjModuleChart M j, ⊤) := fun j => polynomialProjPushforwardChartSections_finite f a j
  let : ∀ j, (polynomialProjModuleChart M j).IsQuasicoherent :=
    fun j => polynomialProjPushforwardChart_isQuasicoherent f a j
  exact ⟨polynomialProjFiniteChartGeneratorCount K n M,
    polynomialProjFiniteChartGeneratorDegree K n M,
    polynomialProjFiniteChartGeneratorTwist K n M,
    polynomialProjFiniteChartGeneratorCoefficients_span K n M⟩

end

end SGPT.Foundations.Schemes
