import SGPT.Okounkov.OF3NuOk
import SGPT.Okounkov.OF3SectionOrderConstancy
import SGPT.Okounkov.FlagValuationPrefixIdeals
import SGPT.Okounkov.SchemePointSectionGerm
import SGPT.Foundations.Analysis.Pending.IdealPowerNormalOrder
import SGPT.Foundations.Analysis.Pending.ManifoldFiniteSpanChartTransport

/-!
# Flag valuations have first coordinate `ord_{Y₁}`

Source: chapter *The theory of Okounkov bodies*, `def:admfl` and the definition of `ν_{Y•}`
(*"`ν₁ = ord_{Y₁}(s^{(0)})` ... The same construction applies to a non-zero section `s ∈ H⁰(X, L)`
after choosing a local trivialization of `L` near `Yₙ`"*), used in `thm:nuOk`.

We check that the hypothesis `SGPT.Okounkov.OF3.IsFirstCoordinateOrder` of the general form of
`thm:nuOk` (`SGPT.Okounkov.OF3.isLeast_firstCoordinate_partialBody`) is satisfied by the flag
valuation `ν_{Y•}` of every smooth flag, with `E = Y₁` (the identity presentation), and by every
valuation with the same first coordinate. Hence the general theorem contains the smooth-flag form
of `thm:nuOk` (lanes OKO-CLOSE and OF).

## Main results

* `originalFirstFlagGermOrder_eq_normalOrder`: on holomorphic germs at the flag point, the first
  flag order (the multiplicity of the prime equation of `Y₁`) is the order along `Y₁` in any
  flattening of `Y₁` (`SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder.normalOrder`): the two
  prime equations generate the same ideal (germs vanishing on `Y₁`).
* `identityPresentation`: a closed connected hypersurface of `X(ℂ)` as a prime divisor over `X`.
* `plainSectionValue_flag`: the value of a section of any line bundle for `ν_{Y•}` is the flag
  germ valuation of its coefficient germ at the flag point.
* **`isFirstCoordinateOrder_flag`**, `isFirstCoordinateOrder_of_prefix_eq`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF3

open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.FixedGermNormalOrder
open SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.Pending.BlowupTowers
open SGPT.PSH.CompactPrimeOver SGPT.Okounkov.AlgebraicValuation

universe u

/-! ### The first flag order is the normal order along `Y₁` -/

section Germs

variable {m : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y] {D : Set Y} {y : Y}

/-- A principal span condition read on chart-translated germs. -/
theorem isInSpanAt_eq_iff_mem_span (u g : Y → ℂ) (hu : HolomorphicAt (m + 1) u y)
    (hg : HolomorphicAt (m + 1) g y) :
    IsInSpanAt (n := m + 1) (· = u) y g ↔
      chartTranslatedGerm y y (mem_chart_source _ y) g hg ∈
        Ideal.span {chartTranslatedGerm y y (mem_chart_source _ y) u hu} := by
  have hchart := ManifoldFiniteSpanChartTransport.isInSpanAt_comp_chartSymm_iff
    (mem_chart_source (ComplexModel (m + 1)) y) (fun _ : Fin 1 => u) g
  have htranslated := isInSpanAt_iff_translatedGerm_mem
    (fun _ : Fin 1 => fun z => u ((chartAt (ComplexModel (m + 1)) y).symm z))
    ((chartAt (ComplexModel (m + 1)) y) y)
    (fun _ => CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ y) hu)
    (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ y) hg)
  simpa only [translatedIdeal, chartTranslatedGerm, range_const, mem_singleton_iff] using
    hchart.trans htranslated

/-- The chart-translated germ of the flattening equation is the divisor equation germ. -/
theorem chartTranslatedGerm_flatCoord_last (Φ : DivisorFlattening (m := m) D y)
    (h : HolomorphicAt (m + 1) (flatCoord Φ.Φ (Fin.last m)) y) :
    chartTranslatedGerm y y (mem_chart_source _ y) (flatCoord Φ.Φ (Fin.last m)) h =
      divisorEquationGerm Φ := by
  unfold chartTranslatedGerm translatedGerm divisorEquationGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  let e := (complexChartAt (n := m + 1) y).val
  have ht : Tendsto (fun z : ComplexModel (m + 1) => z + e y) (𝓝 0) (𝓝 (e y)) := by
    simpa only [zero_add] using (continuous_add_const (e y)).tendsto 0
  filter_upwards [ht.eventually (e.open_target.mem_nhds
    (e.map_source (mem_complexChartAt_source y)))] with z hz
  change Φ.Φ.toFun (e (e.symm (z + e y))) (Fin.last m) = Φ.Φ.toFun (z + e y) (Fin.last m)
  rw [e.right_inv hz]

/-- **Germs vanishing on the hypersurface `D` are the multiples of its equation.** -/
theorem vanishingIdeal_mem_iff_dvd (Φ : DivisorFlattening (m := m) D y) (g : Y → ℂ)
    (hg : HolomorphicAt (m + 1) g y) :
    (vanishingIdeal (n := m + 1) D).mem y g ↔
      divisorEquationGerm Φ ∣ chartTranslatedGerm y y (mem_chart_source _ y) g hg := by
  have hflat : HolomorphicAt (m + 1) (flatCoord Φ.Φ (Fin.last m)) y :=
    holomorphicAt_flatCoord Φ.Φ (Fin.last m) (mem_flatDomain_self Φ.Φ)
  rw [IdealPowerNormalOrder.vanishingIdeal_mem_iff_flat_equation Φ g,
    isInSpanAt_eq_iff_mem_span _ g hflat hg, chartTranslatedGerm_flatCoord_last Φ hflat,
    Ideal.mem_span_singleton]

/-- The chart equivalence of native germs is the chart translation. -/
theorem chartEquiv_mk_eq (g : Y → ℂ) (hg : HolomorphicAt (m + 1) g y) :
    NativeHolGerm.chartEquiv y (NativeHolGerm.mk g hg) =
      chartTranslatedGerm y y (mem_chart_source _ y) g hg := by
  apply Subtype.ext
  rw [NativeHolGerm.chartEquiv_mk]
  rfl

end Germs

/-- **The first flag order is the normal order along `Y₁`.** -/
theorem originalFirstFlagGermOrder_eq_normalOrder {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (x : F.tail.carrier) (Φ : DivisorFlattening (m := m) (F.flag (1 : Fin (m + 2))) x.1)
    (g : NativeHolGerm (m + 1) F.carrier x.1) :
    originalFirstFlagGermOrder F x g = normalOrder Φ (NativeHolGerm.chartEquiv x.1 g) := by
  classical
  set t := originalFirstFlagGermParameter F x with ht
  set ψ := NativeHolGerm.chartEquiv (n := m + 1) (M := F.carrier) x.1 with hψ
  set Dg := divisorEquationGerm Φ with hDg
  have hkey : ∀ h : NativeHolGerm (m + 1) F.carrier x.1, t ∣ h ↔ Dg ∣ ψ h := by
    intro h
    obtain ⟨u, hu, rfl⟩ := NativeHolGerm.exists_eq_mk h
    have h1 : t ∣ NativeHolGerm.mk u hu ↔
        originalFirstFlagGermRestriction F x (NativeHolGerm.mk u hu) = 0 := by
      rw [← Ideal.mem_span_singleton, ← (originalFirstFlagGermParameter_spec F x).2.2,
        RingHom.mem_ker]
    rw [h1, originalFirstFlagRestriction_mk_eq_zero_iff, vanishingIdeal_mem_iff_dvd Φ u hu,
      hψ, chartEquiv_mk_eq]
  have hassoc : Associated (ψ t) Dg := by
    have h1 : Dg ∣ ψ t := (hkey t).mp dvd_rfl
    have h2 : t ∣ ψ.symm Dg := (hkey (ψ.symm Dg)).mpr (by rw [RingEquiv.apply_symm_apply])
    have h3 : ψ t ∣ Dg := by
      have := map_dvd ψ h2
      rwa [RingEquiv.apply_symm_apply] at this
    exact associated_of_dvd_dvd h3 h1
  change emultiplicity t g = emultiplicity Dg (ψ g)
  rw [emultiplicity_eq_of_associated_left hassoc, emultiplicity_map_eq ψ]

/-! ### The scheme setting -/

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] (E : ClosedProjectiveEmbedding f)
  [IsSeparated f] [QuasiCompact f]

local instance of3FlagTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of3FlagCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of3FlagManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

omit [IsIntegral X] in
/-- The identity is an analytic modification. -/
theorem isAnalyticModification_id' :
    IsAnalyticModification (n := m + 1) (id : SchemeComplexPoint f → SchemeComplexPoint f) :=
  ⟨contMDiff_id, isProperMap_id, ∅, ∅, id, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, preimage_empty, contMDiff_id.contMDiffOn,
    (fun _ _ => rfl), (fun _ _ => rfl)⟩

omit [IsIntegral X] in
/-- A closed connected complex hypersurface `D` of `X(ℂ)` (e.g. a smooth prime divisor of `X`)
as a prime divisor over `X`, presented on `X(ℂ)` itself. -/
def identityPresentation (D : Set (SchemeComplexPoint f))
    (hD : IsClosedConnectedSubmanifold (m + 1) D m) :
    PrimePresentation (m + 1) (SchemeComplexPoint f) where
  model := ⟨SchemeComplexPoint f⟩
  projection := id
  modification := isAnalyticModification_id' f
  divisor := D
  divisorDimension := m
  smooth := hD
  codimension_one := rfl

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

omit [IsIntegral X] [IsSeparated f] [QuasiCompact f] in
include hY in
/-- The first member of a smooth flag is a closed connected hypersurface. -/
theorem isClosedConnectedSubmanifold_flag_one :
    IsClosedConnectedSubmanifold (m + 1) (Y (1 : Fin (m + 2))) m := by
  have h := hY.2.2 (1 : Fin (m + 2))
  simpa using h

/-- **The value of a section for `ν_{Y•}`** is the flag germ valuation of its coefficient germ
in any frame at the flag point. -/
theorem plainSectionValue_flag {M : X.Modules} (b : LineBundleAtlas M) (s : bundleSections M ⊤) :
    plainSectionValue (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)
        (flagCentre (f := f) (n := m + 1) (E := E) Y hY) b s =
      originalFlagGermValuation (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (schemeProjectiveOriginalFlagPoint f (m + 1) E (schemeProjectiveTNKahlerBackground f (m + 1) E)
          Y hY)
        (schemePointSectionNativeGerm f (m + 1)
          (schemeProjectiveOriginalFlagPoint f (m + 1) E
            (schemeProjectiveTNKahlerBackground f (m + 1) E) Y hY).val b s) := by
  set x := schemeProjectiveOriginalFlagPoint f (m + 1) E
    (schemeProjectiveTNKahlerBackground f (m + 1) E) Y hY with hx
  have hc := isNonnegAt_flag f (m + 1) E Y hY
  have : Nonempty (schemePointFrameOpen f x.val b) := schemePointFrameOpen_nonempty f x.val b
  rw [plainSectionValue_eq_frame hc b (schemePointFrame f x.val b) (schemePointFrame_mem f x.val b) s,
    schemeFubiniStudyFunctionFieldValuation_apply]
  let := schemeGlobalSectionModule f M
  let := schemeFunctionFieldAlgebra f
  change originalFlagGermFractionValuation (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) x
    (schemePointGlobalSectionsGerm f (m + 1) x.val b s) = _
  rw [schemePointGlobalSectionsGerm_native]
  exact originalFlagGermFractionValuation_algebraMap _ x _

omit [IsIntegral X] in
/-- The flag point lies on `Y₁`. -/
theorem flagPoint_mem_one :
    (schemeProjectiveOriginalFlagPoint f (m + 1) E (schemeProjectiveTNKahlerBackground f (m + 1) E)
      Y hY).val ∈ Y (1 : Fin (m + 2)) :=
  (OriginalFlagGermPoint.first (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
    (schemeProjectiveOriginalFlagPoint f (m + 1) E (schemeProjectiveTNKahlerBackground f (m + 1) E)
      Y hY)).2

/-- **The flag valuation `ν_{Y•}` of a smooth flag has first coordinate `ord_{Y₁}`**: it satisfies
the hypothesis `IsFirstCoordinateOrder` of `isLeast_firstCoordinate_partialBody`, for `E = Y₁`
presented on `X(ℂ)` itself. -/
theorem isFirstCoordinateOrder_flag :
    IsFirstCoordinateOrder f E (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)
      (identityPresentation f (Y (1 : Fin (m + 2))) (isClosedConnectedSubmanifold_flag_one f Y hY)) := by
  intro M b s hs
  let := E.isProper
  have hcen : valuationCenter f (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY) =
      flagCentre (f := f) (n := m + 1) (E := E) Y hY :=
    OF.valuationCenter_flagValuation f E Y hY
  set F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY with hF
  set x := schemeProjectiveOriginalFlagPoint f (m + 1) E
    (schemeProjectiveTNKahlerBackground f (m + 1) E) Y hY with hx
  set g := schemePointSectionNativeGerm f (m + 1) x.val b s with hgdef
  have hg : g ≠ 0 := (schemePointSectionNativeGerm_eq_zero_iff f (m + 1) x.val b s).not.mpr hs
  have hval := plainSectionValue_flag f E Y hY b s
  rw [originalFlagGermValuation_apply_of_ne_zero F x g hg] at hval
  have hvec : plainSectionVector (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)
      (flagCentre (f := f) (n := m + 1) (E := E) Y hY) b s hs =
      fun i => (originalFlagGermVector F x g hg i : ℤ) := by
    rw [plainSectionValue_eq_vector _ b s hs] at hval
    exact toLex.injective (WithTop.coe_injective hval)
  change 0 ≤ plainSectionVector (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)
      (valuationCenter f (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)) b s hs 0 ∧
    (((plainSectionVector (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)
      (valuationCenter f (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)) b s hs 0).toNat :
        ℕ) : ℕ∞) = sectionDivisorOrder f E _ s
  rw [hcen, hvec]
  have h0 : originalFlagGermVector F x g hg 0 =
      originalFirstFlagGermOrderNat F (OriginalFlagGermPoint.first F x) g := rfl
  refine ⟨Int.natCast_nonneg _, ?_⟩
  simp only [h0, Int.toNat_natCast]
  rw [← originalFirstFlagGermOrderNat_spec F (OriginalFlagGermPoint.first F x) g hg]
  -- a flattening of `Y₁` at the flag point
  have hE := isClosedConnectedSubmanifold_flag_one f Y hY
  have hxE := flagPoint_mem_one f E Y hY
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 x.val hxE)
  rw [originalFirstFlagGermOrder_eq_normalOrder F (OriginalFlagGermPoint.first F x) Φ g]
  have hU := schemePointFrame_mem f x.val b
  have hgmk : g = NativeHolGerm.mk (frameCoefficient f m E (schemePointFrame f x.val b) s)
      (frameCoefficient_holomorphicAt (m := m) f E (schemePointFrame f x.val b) s hU) :=
    (schemeOpenRegularFunction_germ f (m + 1) E _ _ x.val hU).symm
  rw [hgmk, chartEquiv_mk_eq]
  obtain ⟨hord, -⟩ := sectionDivisorOrder_eq_pullbackNormalOrder f E b
    (identityPresentation f (Y (1 : Fin (m + 2))) hE) hs (y := x.val) hxE
    (schemePointFrame f x.val b) hU Φ
  rw [hord]
  rfl

/-- Every valuation with the same first coordinate as `ν_{Y•}` (OF's hypothesis, e.g. the
valuation of an admissible flag with smooth first member `Y₁`) has first coordinate `ord_{Y₁}`. -/
theorem isFirstCoordinateOrder_of_prefix_eq
    (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hpre : ValCurr.prefixValuation (Nat.le_add_left 1 m) v =
      ValCurr.prefixValuation (Nat.le_add_left 1 m)
        (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)) :
    IsFirstCoordinateOrder f E v
      (identityPresentation f (Y (1 : Fin (m + 2))) (isClosedConnectedSubmanifold_flag_one f Y hY)) := by
  intro M b s hs
  let := E.isProper
  have hw := isFirstCoordinateOrder_flag f E Y hY M b s hs
  have hcv : IsNonnegAt v (valuationCenter f v) := (isValuationCenter_valuationCenter f v).1
  have hcw : IsNonnegAt (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)
      (valuationCenter f (schemeFubiniStudyFunctionFieldValuation f (m + 1) E Y hY)) :=
    (isValuationCenter_valuationCenter f _).1
  have heq := OF.plainSectionVector_zero_eq_of_prefixValuation_eq f v _ hpre hcv hcw b s hs
  change 0 ≤ plainSectionVector v (valuationCenter f v) b s hs 0 ∧
    (((plainSectionVector v (valuationCenter f v) b s hs 0).toNat : ℕ) : ℕ∞) =
      sectionDivisorOrder f E _ s
  rw [heq]
  exact hw

end Scheme

end SGPT.Okounkov.OF3
