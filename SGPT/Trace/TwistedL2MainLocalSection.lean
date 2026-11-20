import SGPT.Trace.TwistedL2MainLocalRegularity
import SGPT.Trace.TwistedL2MainVolumeSupport

/-!
# Actual local sections from chart representatives

The chart representative defines a bundle section on the corresponding open
piece. Frame-coordinate continuity is used to compare representatives on
intersections before constructing the global section.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- The manifold open set corresponding to a chart-frame piece. -/
def localSectionRegion (c : ComplexChart n X) (e : AtlasFrame T.L) : Set X :=
  T.U ∩ (c.val.source ∩ e.val.baseSet)

theorem isOpen_localSectionRegion (c : ComplexChart n X) (e : AtlasFrame T.L) :
    IsOpen (T.localSectionRegion c e) :=
  T.isOpen_U.inter (c.val.open_source.inter e.val.open_baseSet)

/-- The section represented by a scalar chart function in the actual frame. -/
def localSection (c : ComplexChart n X) (e : AtlasFrame T.L)
    (F : ComplexModel n → ℂ) (x : X) : T.L.Fiber x :=
  e.val.symm x (F (c.val x))

/-- Its coefficient in any other actual frame is the scalar representative
times the actual frame-transition coefficient. -/
theorem frameCoeff_localSection (c : ComplexChart n X) (e e' : AtlasFrame T.L)
    (F : ComplexModel n → ℂ) {x : X} (he : x ∈ e.val.baseSet) (he' : x ∈ e'.val.baseSet) :
    (e'.val ⟨x, T.localSection c e F x⟩).2 =
      F (c.val x) * (e'.val ⟨x, e.val.symm x 1⟩).2 := by
  have := e.property
  have hsymm : e.val.symm x (F (c.val x)) = F (c.val x) • e.val.symm x 1 := by
    rw [← e.val.symmL_apply (R := ℂ) he (F (c.val x)),
      ← e.val.symmL_apply (R := ℂ) he 1, ← map_smul, smul_eq_mul, mul_one]
  rw [localSection, hsymm, frameCoeff_smul_apply e' he']

/-- A holomorphic chart representative gives a section whose coefficient in
any other frame is continuous on the overlap of their base sets. -/
theorem continuousOn_frameCoeff_localSection (c : ComplexChart n X)
    (e e' : AtlasFrame T.L) {F : ComplexModel n → ℂ}
    (hF : DifferentiableOn ℂ F (T.pieceDomain c e)) :
    ContinuousOn (fun x => (e'.val ⟨x, T.localSection c e F x⟩).2)
      (T.localSectionRegion c e ∩ e'.val.baseSet) := by
  let V := T.localSectionRegion c e ∩ e'.val.baseSet
  have hc : ContinuousOn (fun x => F (c.val x)) V := by
    refine hF.continuousOn.comp (c.val.continuousOn.mono ?_) ?_
    · intro x hx
      exact hx.1.2.1
    · intro x hx
      refine ⟨⟨c.val.map_source hx.1.2.1, ?_⟩, ?_⟩
      · simpa only [mem_preimage, c.val.left_inv hx.1.2.1] using hx.1.2.2
      · simpa only [mem_preimage, c.val.left_inv hx.1.2.1] using hx.1.1
  have ht : ContinuousOn (fun x => (e'.val ⟨x, e.val.symm x 1⟩).2) V :=
    (continuousOn_frameCoeff_frame e' e).mono fun x hx => ⟨hx.2, hx.1.2.2⟩
  refine (hc.mul ht).congr ?_
  intro x hx
  exact T.frameCoeff_localSection c e e' F hx.1.2.2 hx.2


/-- The inverse image of the chart piece, restricted to the chart source, is
the actual open manifold region carrying the local section. -/
theorem preimage_piece_eq_localSectionRegion (c : ComplexChart n X) (e : AtlasFrame T.L) :
    c.val ⁻¹' T.pieceDomain c e ∩ c.val.source = T.localSectionRegion c e := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, hx.2, ?_⟩
    · simpa only [mem_preimage, c.val.left_inv hx.2] using hx.1.2
    · simpa only [mem_preimage, c.val.left_inv hx.2] using hx.1.1.2
  · intro hx
    refine ⟨⟨⟨c.val.map_source hx.2.1, ?_⟩, ?_⟩, hx.2.1⟩
    · simpa only [mem_preimage, c.val.left_inv hx.2.1] using hx.2.2
    · simpa only [mem_preimage, c.val.left_inv hx.2.1] using hx.1

/-- The Weyl representative defines a genuine local section equal almost
everywhere to the original bundle-valued difference `G - correction`. -/
theorem exists_localSection_ae_difference
    (u : Lp ℂ 2 (T.μ.restrict T.U))
    (htest : ∀ p : T.LocalTestPiece, ⟪p.adjoint, u⟫_ℂ = p.pairing)
    (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) :
    ∃ F : ComplexModel n → ℂ, DifferentiableOn ℂ F (T.pieceDomain c e) ∧
      ∀ᵐ x ∂(T.μ.restrict (T.localSectionRegion c e)),
        T.localSection c e F x = T.G x - T.correctionSection u x := by
  obtain ⟨F, hF, hFae⟩ := T.exists_chart_representative_ae_manifold u htest c e hρ
  refine ⟨F, hF, ?_⟩
  rw [Measure.restrict_restrict' c.val.open_source.measurableSet,
    T.preimage_piece_eq_localSectionRegion c e] at hFae
  filter_upwards [hFae, ae_restrict_mem (T.isOpen_localSectionRegion c e).measurableSet] with x hx hreg
  have he := e.val.symm_apply_apply_mk hreg.2.2 (T.G x - T.correctionSection u x)
  rw [hx] at he
  exact he

/-- Two local representatives of the same actual almost-everywhere section
agree at every point of their overlap. -/
theorem localSections_eq_on_overlap
    (u : Lp ℂ 2 (T.μ.restrict T.U))
    (c₁ c₂ : ComplexChart n X) (e₁ e₂ : AtlasFrame T.L)
    {F₁ F₂ : ComplexModel n → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (T.pieceDomain c₁ e₁))
    (hF₂ : DifferentiableOn ℂ F₂ (T.pieceDomain c₂ e₂))
    (hae₁ : ∀ᵐ x ∂(T.μ.restrict (T.localSectionRegion c₁ e₁)),
      T.localSection c₁ e₁ F₁ x = T.G x - T.correctionSection u x)
    (hae₂ : ∀ᵐ x ∂(T.μ.restrict (T.localSectionRegion c₂ e₂)),
      T.localSection c₂ e₂ F₂ x = T.G x - T.correctionSection u x) :
    EqOn (fun x => (e₁.val ⟨x, T.localSection c₁ e₁ F₁ x⟩).2)
      (fun x => (e₁.val ⟨x, T.localSection c₂ e₂ F₂ x⟩).2)
      (T.localSectionRegion c₁ e₁ ∩ T.localSectionRegion c₂ e₂) := by
  let V := T.localSectionRegion c₁ e₁ ∩ T.localSectionRegion c₂ e₂
  let : Measure.IsOpenPosMeasure T.μ := smoothPositiveVolume_isOpenPosMeasure T.volume_smooth
  have hV : IsOpen V := (T.isOpen_localSectionRegion c₁ e₁).inter
    (T.isOpen_localSectionRegion c₂ e₂)
  have hcont₁ : ContinuousOn (fun x => (e₁.val ⟨x, T.localSection c₁ e₁ F₁ x⟩).2) V :=
    (T.continuousOn_frameCoeff_localSection c₁ e₁ e₁ hF₁).mono
      (fun x hx => ⟨hx.1, hx.1.2.2⟩)
  have hcont₂ : ContinuousOn (fun x => (e₁.val ⟨x, T.localSection c₂ e₂ F₂ x⟩).2) V :=
    (T.continuousOn_frameCoeff_localSection c₂ e₂ e₁ hF₂).mono
      (fun x hx => ⟨hx.2, hx.1.2.2⟩)
  have hae : (fun x => (e₁.val ⟨x, T.localSection c₁ e₁ F₁ x⟩).2) =ᵐ[T.μ.restrict V]
      (fun x => (e₁.val ⟨x, T.localSection c₂ e₂ F₂ x⟩).2) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hae₁,
      ae_restrict_of_ae_restrict_of_subset inter_subset_right hae₂] with x hx₁ hx₂
    rw [hx₁, hx₂]
  exact Measure.eqOn_open_of_ae_eq hae hV hcont₁ hcont₂

/-- The local sections themselves, not just their scalar coefficients, agree
pointwise on overlaps. -/
theorem localSections_eq_fiber_on_overlap
    (u : Lp ℂ 2 (T.μ.restrict T.U))
    (c₁ c₂ : ComplexChart n X) (e₁ e₂ : AtlasFrame T.L)
    {F₁ F₂ : ComplexModel n → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (T.pieceDomain c₁ e₁))
    (hF₂ : DifferentiableOn ℂ F₂ (T.pieceDomain c₂ e₂))
    (hae₁ : ∀ᵐ x ∂(T.μ.restrict (T.localSectionRegion c₁ e₁)),
      T.localSection c₁ e₁ F₁ x = T.G x - T.correctionSection u x)
    (hae₂ : ∀ᵐ x ∂(T.μ.restrict (T.localSectionRegion c₂ e₂)),
      T.localSection c₂ e₂ F₂ x = T.G x - T.correctionSection u x)
    {x : X} (hx : x ∈ T.localSectionRegion c₁ e₁ ∩ T.localSectionRegion c₂ e₂) :
    T.localSection c₁ e₁ F₁ x = T.localSection c₂ e₂ F₂ x := by
  have hcoord := T.localSections_eq_on_overlap u c₁ c₂ e₁ e₂ hF₁ hF₂ hae₁ hae₂ hx
  have h := congrArg (e₁.val.symm x) hcoord
  simpa only [e₁.val.symm_apply_apply_mk hx.1.2.2] using h

end TwistedDatum
end SGPT.Trace.TwistedL2
