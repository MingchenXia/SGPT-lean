import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.PSH.ThetaRooftop
import SGPT.Foundations.Analysis.FirstPass.IEnvelope

/-! # Original all-chart multiplier order and I-envelope

The positive-real multiplier characterization defines the source relations.
The five-way valuation/modification characterizations remain separate theorems.
The source relation retains its actual QPSH domain. The I-model predicate
retains actual theta-PSH, not only a formal fixed-point equation.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

universe u
variable {X : Type u} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Actual inclusion of multiplier germs in one original chart, tested using
its own canonical Borel Haar measure. No pole is replaced by a real value. -/
def chartMultiplierIncluded (A : VariableComplexAtlas X) (φ : X → EReal) (c : ℝ)
    (ψ : X → EReal) (d : ℝ) (i : A.Index) : Prop := by
  letI : MeasurableSpace (ComplexModel (A.dimension i)) := borel _
  letI : BorelSpace (ComplexModel (A.dimension i)) := ⟨rfl⟩
  exact ∀ z ∈ (A.chart i).target, ∀ f : ComplexModel (A.dimension i) → ℂ,
    AnalyticAt ℂ f z →
      MultiplierIntegrableAt (A.coordinate φ i) c f z volume →
        MultiplierIntegrableAt (A.coordinate ψ i) d f z volume

/-- Source `def:Imoresing`, choosing its literal positive-real-exponent
multiplier characterization on the original QPSH domain. -/
def sourceIOrder (A : VariableComplexAtlas X) (φ ψ : X → EReal) : Prop :=
  A.IsQPSH φ ∧ A.IsQPSH ψ ∧
    ∀ c : ℝ, 0 < c → ∀ i, chartMultiplierIncluded A φ c ψ c i

/-- Source `def:Iequiv`: both actual original multiplier inclusions. -/
def sourceIEquivalent (A : VariableComplexAtlas X) (φ ψ : X → EReal) : Prop :=
  sourceIOrder A φ ψ ∧ sourceIOrder A ψ φ

theorem sourceIOrder_refl {φ : X → EReal} (hφ : A.IsQPSH φ) :
    sourceIOrder A φ φ :=
  ⟨hφ, hφ, fun _ _ _ _ _ _ _ h => h⟩

theorem sourceIOrder_trans {φ ψ η : X → EReal}
    (hφψ : sourceIOrder A φ ψ) (hψη : sourceIOrder A ψ η) :
    sourceIOrder A φ η := by
  refine ⟨hφψ.1, hψη.2.1, ?_⟩
  intro c hc i z hz f hf hmem
  exact hψη.2.2 c hc i z hz f hf (hφψ.2.2 c hc i z hz f hf hmem)

theorem sourceIEquivalent_refl {φ : X → EReal} (hφ : A.IsQPSH φ) :
    sourceIEquivalent A φ φ :=
  ⟨sourceIOrder_refl hφ, sourceIOrder_refl hφ⟩

theorem sourceIEquivalent_symm {φ ψ : X → EReal}
    (h : sourceIEquivalent A φ ψ) : sourceIEquivalent A ψ φ := ⟨h.2, h.1⟩

theorem sourceIEquivalent_trans {φ ψ η : X → EReal}
    (hφψ : sourceIEquivalent A φ ψ) (hψη : sourceIEquivalent A ψ η) :
    sourceIEquivalent A φ η :=
  ⟨sourceIOrder_trans hφψ.1 hψη.1, sourceIOrder_trans hψη.2 hφψ.2⟩

/-- The literal complete original normalized competitor family. -/
def sourceICompetitors (θ : AtlasClosedRealOneOneForm A) (φ : X → EReal) :=
  {v : X → EReal // A.IsThetaPSH θ v ∧ v ≤ 0 ∧ sourceIEquivalent A v φ}

/-- Source `def:Ienv`, with all original competitors and the actual empty
supremum retained before neighborhood upper regularization. -/
def sourceIEnvelope (θ : AtlasClosedRealOneOneForm A) (φ : X → EReal) :
    X → EReal := uscSup (fun v : sourceICompetitors θ φ => v.1)

/-- An original I-model is genuinely theta-PSH and fixed by its I-envelope. -/
def sourceIModel (θ : AtlasClosedRealOneOneForm A) (φ : X → EReal) : Prop :=
  A.IsThetaPSH θ φ ∧ φ = sourceIEnvelope θ φ

theorem sourceIEnvelope_le_zero (θ : AtlasClosedRealOneOneForm A) (φ : X → EReal) :
    sourceIEnvelope θ φ ≤ 0 :=
  uscRegularization_le (continuous_const.upperSemicontinuous)
    (fun x => iSup_le fun v => v.2.2.1 x)

theorem le_sourceIEnvelope {θ : AtlasClosedRealOneOneForm A} {φ v : X → EReal}
    (hv : A.IsThetaPSH θ v) (hv0 : v ≤ 0) (hvφ : sourceIEquivalent A v φ) :
    v ≤ sourceIEnvelope θ φ := by
  intro x
  exact (le_iSup (fun w : sourceICompetitors θ φ => w.1 x) ⟨v, hv, hv0, hvφ⟩).trans
    (le_uscRegularization (fun y => ⨆ w : sourceICompetitors θ φ, w.1 y) x)

theorem upperSemicontinuous_sourceIEnvelope
    (θ : AtlasClosedRealOneOneForm A) (φ : X → EReal) :
    UpperSemicontinuous (sourceIEnvelope θ φ) :=
  upperSemicontinuous_uscRegularization _

/-- This is conditional only on actual nonemptiness; it makes no assertion
that the output is multiplier-equivalent or that nonemptiness is automatic. -/
theorem isThetaPSH_sourceIEnvelope_of_nonempty
    {θ : AtlasClosedRealOneOneForm A} {φ : X → EReal}
    (hn : Nonempty (sourceICompetitors θ φ)) :
    A.IsThetaPSH θ (sourceIEnvelope θ φ) := by
  let := hn
  exact isThetaPSH_uscSup_of_majorant (w := fun _ => (0 : EReal)) (fun v => v.2.1)
    continuous_const.upperSemicontinuous (fun _ => EReal.coe_ne_top (0 : ℝ))
    (fun v => v.2.2.1)

theorem sourceIEnvelope_eq_of_equivalent {θ : AtlasClosedRealOneOneForm A}
    {φ ψ : X → EReal} (h : sourceIEquivalent A φ ψ) :
    sourceIEnvelope θ φ = sourceIEnvelope θ ψ := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro v
    exact le_iSup (fun w : sourceICompetitors θ ψ => w.1 x)
      ⟨v.1, v.2.1, v.2.2.1, sourceIEquivalent_trans v.2.2.2 h⟩
  · apply iSup_le
    intro v
    exact le_iSup (fun w : sourceICompetitors θ φ => w.1 x)
      ⟨v.1, v.2.1, v.2.2.1,
        sourceIEquivalent_trans v.2.2.2 (sourceIEquivalent_symm h)⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual all-chart membership quantifiers, with the same Haar measure and
exponent, are exactly the native all-chart germ inclusion. -/
theorem chartMultiplierIncluded_iff_native (φ ψ : M → EReal) (c d : ℝ) :
    (∀ i, chartMultiplierIncluded (ofFixedModel n M) φ c ψ d i) ↔
      QuasiEquisingularApproximation.MultiplierIdealIncluded (n := n) φ c ψ d :=
  Iff.rfl

theorem sourceIOrder_iff_native {φ ψ : M → EReal}
    (hφ : (ofFixedModel n M).IsQPSH φ) (hψ : (ofFixedModel n M).IsQPSH ψ) :
    sourceIOrder (ofFixedModel n M) φ ψ ↔
      IEnvelope.IOrderOnManifold (n := n) φ ψ := by
  constructor
  · exact fun h => h.2.2
  · exact fun h => ⟨hφ, hψ, h⟩

theorem sourceIEquivalent_iff_native {φ ψ : M → EReal}
    (hφ : (ofFixedModel n M).IsQPSH φ) (hψ : (ofFixedModel n M).IsQPSH ψ) :
    sourceIEquivalent (ofFixedModel n M) φ ψ ↔
      IEnvelope.IEquivalentOnManifold (n := n) φ ψ := by
  exact and_congr (sourceIOrder_iff_native hφ hψ) (sourceIOrder_iff_native hψ hφ)

/-- Entire normalized competitor reindexing with the original genuine
theta-PSH reference. No fixed-point or envelope-PSH certificate is supplied. -/
theorem sourceIEnvelope_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIEnvelope θ φ = IEnvelope.iSingularityEnvelope (atlasClosedFormToNative θ).val φ := by
  apply congrArg uscRegularization
  funext x
  rw [IEnvelope.iSingularitySupremum_apply]
  apply le_antisymm
  · apply iSup_le
    intro v
    exact le_iSup_of_le v.1 (le_iSup_of_le
      ⟨⟨(isThetaPSH_iff_nativeThetaPotential θ v.1).mp v.2.1, v.2.2.1⟩,
        (sourceIEquivalent_iff_native ⟨θ, v.2.1⟩ ⟨θ, hφ⟩).mp v.2.2.2⟩ le_rfl)
  · apply iSup_le
    intro v
    apply iSup_le
    rintro ⟨⟨hv, hv0⟩, hvφ⟩
    have hv' := (isThetaPSH_iff_nativeThetaPotential θ v).mpr hv
    exact le_iSup (fun w : sourceICompetitors θ φ => w.1 x)
      ⟨v, hv', hv0, (sourceIEquivalent_iff_native ⟨θ, hv'⟩ ⟨θ, hφ⟩).mpr hvφ⟩

theorem sourceIModel_iff_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal) :
    sourceIModel θ φ ↔ IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val φ := by
  constructor
  · rintro ⟨hφ, heq⟩
    exact ⟨(isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ,
      heq.trans (sourceIEnvelope_eq_native θ φ hφ)⟩
  · rintro ⟨hφ, heq⟩
    have hφ' := (isThetaPSH_iff_nativeThetaPotential θ φ).mpr hφ
    exact ⟨hφ', heq.trans (sourceIEnvelope_eq_native θ φ hφ').symm⟩

end SGPT.PSH.VariableComplexAtlas
