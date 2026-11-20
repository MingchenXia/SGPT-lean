import SGPT.TestCurve.FGRelMain
import SGPT.GAGA.SmoothFlagsScheme

/-!
# `rmk:NApotential:L862` without a smooth flag


Source `rmk:NApotential:L862` (`chapter_NApotential.tex`): *when `{θ}` is a Hodge class and `Γ` is
induced by a test configuration, our Duistermaat–Heckman measure coincides with the more
traditional definition of [BHJ17, §3.2].*  Lanes NA-NS, TC-ENC and FG-REL proved that the rescaled
weight measures `(n!/kⁿ) ν_k` of the filtration `𝓕` induced by a test configuration converge
weakly to `DH(Γ^𝓕)` (`SGPT.TestCurve.TCEnc.testConfiguration_rescaledJumpMeasure_tendsto`,
`SGPT.TestCurve.FGRel.equivariantCoordinates_rescaledJumpMeasure_tendsto`) on an `X` *carrying a
smooth flag* `Y•` (with which `DH(Γ^𝓕)` is computed, `def:DHm`).

Every integral smooth projective `X` has a complex point (`nonempty_schemeComplexPoint_of_isIntegral`,
Nullstellensatz), carries a smooth flag (`SGPT.GAGA.SmoothFlags.smoothFlagsExist`), and `X(ℂ)` is
connected (`SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral`).  Hence the flag hypothesis is removed below:
the rescaled weight measures converge weakly to a finite measure which is `DH(Γ^𝓕)` computed with
**any** smooth flag (so, as a by-product, the limit does not depend on the flag, as asserted in
`thm:DHindep`).

* `testConfiguration_rescaledJumpMeasure_tendsto_flagFree`,
  `testConfiguration_normalized_tendsto_flagFree`: for test configurations with finitely generated
  induced filtration;
* `equivariantCoordinates_rescaledJumpMeasure_tendsto_flagFree`,
  `equivariantCoordinates_normalized_tendsto_flagFree`: for test configurations with equivariant
  coordinates (finite generation discharged by lane FG-REL).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.QwNA

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Filter Set SGPT.Okounkov MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.TestCurve.TCEnc SGPT.TestCurve.FGRel SGPT.NAPotential.NANS.TestConfig
open scoped Topology

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f}

local instance qwNAFlagFreeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance qwNAFlagFreeCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance qwNAFlagFreeManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance qwNAFlagFreeMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance qwNAFlagFreeBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

omit [SmoothOfRelativeDimension (m + 1) f] in
/-- An integral scheme `X` of finite type over `ℂ` (here: with a closed projective embedding) has a
complex point (Hilbert's Nullstellensatz): `X(ℂ) ≠ ∅`. -/
theorem nonempty_schemeComplexPoint_of_isIntegral (E : ClosedProjectiveEmbedding f) [IsIntegral X] :
    Nonempty (SchemeComplexPoint f) := by
  have := E.locallyOfFiniteType
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty (U : X.Opens) := ⟨⟨x, hxU⟩⟩
  obtain ⟨P, hP⟩ := Ideal.exists_maximal Γ(X, U)
  obtain ⟨p, -⟩ := SGPT.NAPotential.Berkovich.exists_schemeComplexPoint_fromSpec f hU P hP
  exact ⟨p⟩

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L}
  (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **`rmk:NApotential:L862` for a test configuration, without a smooth flag**: for a test
configuration `(𝓧, 𝓛)` of `(X, L)` with finitely generated induced filtration `𝓕` and
`θ = c₁(L, h)` Kähler (a Hodge class), on every integral smooth projective `X`, the rescaled weight measures `(n!/kⁿ) ν_k` of `𝓕` converge weakly to a finite measure
`μ` which is the Duistermaat–Heckman measure `DH(Γ^𝓕)` (`def:DHm`) computed with every smooth flag
of `X`. -/
theorem testConfiguration_rescaledJumpMeasure_tendsto_flagFree (T : TestConfiguration f a)
    (hfg : T.FiltrationFinitelyGenerated E)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun j : ℕ => rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j) atTop
        (𝓝 μ) ∧
      ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
        μ = filtrationDHFinite (T.inducedFiltration E hfg) H Y hY hbig := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint_of_isIntegral E
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  obtain ⟨Y₀, hY₀⟩ := SGPT.GAGA.SmoothFlags.smoothFlagsExist X f E m
  have h₀ := testConfiguration_rescaledJumpMeasure_tendsto H Y₀ hY₀ T hfg hK hbig
  exact ⟨_, h₀, fun Y hY =>
    tendsto_nhds_unique h₀ (testConfiguration_rescaledJumpMeasure_tendsto H Y hY T hfg hK hbig)⟩

/-- **`rmk:NApotential:L862` for a test configuration, normalized form, without a smooth flag**:
the normalized weight measures `N_k⁻¹ ν_k` converge weakly to `μ / μ(ℝ)` and the masses
`n! N_k / kⁿ` converge to `μ(ℝ)`, where `μ = DH(Γ^𝓕)` (computed with every smooth flag). -/
theorem testConfiguration_normalized_tendsto_flagFree (T : TestConfiguration f a)
    (hfg : T.FiltrationFinitelyGenerated E)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j).normalize)
        atTop (𝓝 μ.normalize) ∧
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j).mass)
        atTop (𝓝 μ.mass) ∧
      ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
        μ = filtrationDHFinite (T.inducedFiltration E hfg) H Y hY hbig := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint_of_isIntegral E
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  obtain ⟨Y₀, hY₀⟩ := SGPT.GAGA.SmoothFlags.smoothFlagsExist X f E m
  obtain ⟨μ, -, hμ⟩ := testConfiguration_rescaledJumpMeasure_tendsto_flagFree H T hfg hK hbig
  obtain ⟨h1, h2⟩ := testConfiguration_normalized_tendsto H Y₀ hY₀ T hfg hK hbig
  rw [← hμ Y₀ hY₀] at h1 h2
  exact ⟨μ, h1, h2, hμ⟩

/-- **`rmk:NApotential:L862` for an ample test configuration (equivariant coordinates), without a
smooth flag and without a finite generation hypothesis**: `(n!/kⁿ) ν_k → DH(Γ^𝓕)` weakly, `DH(Γ^𝓕)`
computed with every smooth flag of `X`. -/
theorem equivariantCoordinates_rescaledJumpMeasure_tendsto_flagFree (T : TestConfiguration f a)
    (C : EquivariantCoordinates T)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun j : ℕ => rescaledFiniteMeasure
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        (m + 1) j) atTop (𝓝 μ) ∧
      ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
        μ = filtrationDHFinite
          (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
          H Y hY hbig :=
  testConfiguration_rescaledJumpMeasure_tendsto_flagFree H T _ hK hbig

/-- **`rmk:NApotential:L862` for an ample test configuration (equivariant coordinates), normalized
form, without a smooth flag**: `N_k⁻¹ ν_k → DH(Γ^𝓕) / DH(Γ^𝓕)(ℝ)` weakly and
`n! N_k / kⁿ → DH(Γ^𝓕)(ℝ)`. -/
theorem equivariantCoordinates_normalized_tendsto_flagFree (T : TestConfiguration f a)
    (C : EquivariantCoordinates T)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        (m + 1) j).normalize) atTop (𝓝 μ.normalize) ∧
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        (m + 1) j).mass) atTop (𝓝 μ.mass) ∧
      ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
        μ = filtrationDHFinite
          (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
          H Y hY hbig :=
  testConfiguration_normalized_tendsto_flagFree H T _ hK hbig

end SGPT.TestCurve.QwNA

end
