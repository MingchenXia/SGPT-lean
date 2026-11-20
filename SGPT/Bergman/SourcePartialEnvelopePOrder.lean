import SGPT.Bergman.SourcePartialEnvelopes
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMaximumOrders
import SGPT.Envelopes.SourceGlobalPRelativeEnvelope
import SGPT.PSH.SourceIEnvelopeMonotonicity
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

/-! Exact frozen P6 tail after namespace alpha-renaming only.
No inherited proof bodies copied. Canonical acceptance and actual private discovery pending. -/

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology

namespace SGPT.Bergman.PartialPOrder

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Bergman.PartialEnvelope
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology Classical

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Entire literal first RHS candidate type of cor:partial_P_new_def.
The order is the actual original GLOBAL P-order, with zero-mass members retained. -/
def partialPCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) :=
  {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
    partialObstacle (n := n) K f v ∧ GlobalPComparison.sourcePOrder (n := n) v φ}

/-- The exact genuine positive-mass subtype in the second original RHS. -/
def positivePartialPCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) :=
  {v : partialPCompetitors θ φ K f //
    0 < sourcePotentialNonPluripolarMeasure θ v.val v.property.1 univ}

private theorem globalPOrder_max_with_shift (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {η φ : M → EReal}
    (hη : (ofFixedModel n M).IsThetaPSH θ η) (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (c : ℝ) (hP : GlobalPComparison.sourcePOrder (n := n) η φ) :
    GlobalPComparison.sourcePOrder (n := n) (fun x => max (η x) (φ x + (c : EReal))) φ := by
  let w : M → EReal := fun x => max (η x) (φ x + (c : EReal))
  let m : M → EReal := fun x => max (η x) (φ x)
  have hw := sourceThetaMaximum_genuine hη (sourceThetaPSH_add_const hφ c)
  have hm := sourceThetaMaximum_genuine hη hφ
  have hηn := (isThetaPSH_iff_nativeThetaPotential θ η).mp hη
  have hφn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  have hmaxP := (GlobalQuasiPshMaximumOrders.sourcePOrder_iff_sourcePEquivalent_max_globalQuasiPsh
    ω hηn.quasiPshPotential hφn.quasiPshPotential).mp hP
  have hmore : MoreSingularOn w m univ := by
    refine ⟨max c 0, fun x _ => max_le ?_ ?_⟩
    · calc
        η x = η x + 0 := (add_zero _).symm
        _ ≤ m x + ((max c 0 : ℝ) : EReal) := add_le_add
          (le_max_left (η x) (φ x)) (EReal.coe_nonneg.mpr (le_max_right c 0))
    · exact add_le_add (le_max_right (η x) (φ x))
        (EReal.coe_le_coe_iff.mpr (le_max_left c 0))
  exact GlobalPComparison.sourcePOrder_trans ω
    (GlobalPComparison.sourcePOrder_of_moreSingular ω
      ((isThetaPSH_iff_nativeThetaPotential θ w).mp hw).quasiPshPotential
      ((isThetaPSH_iff_nativeThetaPotential θ m).mp hm).quasiPshPotential hmore) hmaxP.1

/-- Positive original reference/lower obstacle manufacture positive P-order
competitors above EVERY original candidate, even an actual zero-mass one. -/
theorem positivePartialPCompetitors_cofinal (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ f x)
    (v : partialPCompetitors θ φ K f) :
    ∃ w : positivePartialPCompetitors θ φ K f, v.val ≤ w.val.val := by
  obtain ⟨A, hA⟩ := ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).exists_global_upper_bound
  obtain ⟨B, hB⟩ := hf
  let c := B - A
  let χ : M → EReal := fun x => φ x + (c : EReal)
  have hχ : (ofFixedModel n M).IsThetaPSH θ χ := sourceThetaPSH_add_const hφ c
  have hχB (x : M) : χ x ≤ (B : EReal) := by
    calc
      χ x ≤ (A : EReal) + (c : EReal) := add_le_add (hA x) le_rfl
      _ = (B : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        dsimp only [c]
        ring
  have hχpos : 0 < sourcePotentialNonPluripolarMeasure θ χ hχ univ :=
    hφpos.trans_eq (sourceAffine_mass_add_const hφ c).symm
  let w : M → EReal := fun x => max (v.val x) (χ x)
  have hw : (ofFixedModel n M).IsThetaPSH θ w := sourceThetaMaximum_genuine v.property.1 hχ
  have hwK : partialObstacle (n := n) K f w := by
    obtain ⟨S, hS, hbound⟩ := (partialObstacle_iff_exists_pluripolar K f v.val).mp v.property.2.1
    exact (partialObstacle_iff_exists_pluripolar K f w).mpr
      ⟨S, hS, fun x hx => max_le (hbound x hx) ((hχB x.val).trans (hB x))⟩
  have hwP : GlobalPComparison.sourcePOrder (n := n) w φ :=
    globalPOrder_max_with_shift ω v.property.1 hφ c v.property.2.2
  have hχw : SGPT.PSH.SingularityLE χ w :=
    MoreSingularOn.of_le fun x _ => le_max_right (v.val x) (χ x)
  have hwpos : 0 < sourcePotentialNonPluripolarMeasure θ w hw univ :=
    hχpos.trans_le (sourcePotentialNonPluripolarMass_mono ω hχ hw hχw)
  exact ⟨⟨⟨w, hw, hwK, hwP⟩, hwpos⟩, fun x => le_max_left (v.val x) (χ x)⟩

/-- Every genuine positive GLOBAL-P candidate is dominated by the literal
ordinary partial envelope through ALL original positive-real shifted roofs. -/
theorem le_partialEnvelope_of_positive_globalP (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} {f : K → EReal} (v : positivePartialPCompetitors θ φ K f) :
    v.val.val ≤ partialEnvelope θ φ K f := by
  let H := partialEnvelope θ φ K f
  have hH : UpperSemicontinuous H := upperSemicontinuous_partialEnvelope θ φ K f
  have hη := v.val.property.1
  have hroof (C : {C : ℝ // 0 < C}) :
      thetaRooftop θ v.val.val (fun x => φ x + (C.val : EReal)) ≤ H := by
    obtain ⟨hr, _hne, _hmass, _hpos⟩ := sourcePOrder_shiftedRooftop_positive
      ω hφ hη hφpos v.property v.val.property.2.2 C.val C.property.le
    apply le_partialEnvelope hr
      (partialObstacle_of_le v.val.property.2.1 (thetaRooftop_le_left θ _ _))
    exact (singularityLE_iff_exists_real _ _).mpr ⟨C.val, thetaRooftop_le_right θ _ _⟩
  have hexa := sourcePOrder_relativeRooftop_exhaustion
    ω hφ hη hφpos v.property v.val.property.2.2
  have hsup : uscSup (fun C : {C : ℝ // 0 < C} =>
      thetaRooftop θ v.val.val (fun x => φ x + (C.val : EReal))) ≤ H :=
    uscRegularization_le hH (fun x => iSup_le fun C => hroof C x)
  exact hexa.symm.le.trans hsup

/-- Exact first TWO identities of cor:partial_P_new_def, with genuine GLOBAL
P-order and ALL/positive actual candidates. The two EVERYWHERE identities
remain separate unproved obligations; no full-corollary promotion here. -/
theorem partialEnvelope_globalP_qe_descriptions (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ f x) :
    partialEnvelope θ φ K f = uscSup (fun v : partialPCompetitors θ φ K f => v.val) ∧
      partialEnvelope θ φ K f =
        uscSup (fun v : positivePartialPCompetitors θ φ K f => v.val.val) := by
  have hOrdP (v : partialCompetitors θ φ K f) :
      GlobalPComparison.sourcePOrder (n := n) v.val φ :=
    GlobalPComparison.sourcePOrder_of_moreSingular ω
      ((isThetaPSH_iff_nativeThetaPotential θ v.val).mp v.property.1).quasiPshPotential
      ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).quasiPshPotential v.property.2.2
  have hOrdAll : partialEnvelope θ φ K f ≤
      uscSup (fun v : partialPCompetitors θ φ K f => v.val) := by
    apply uscRegularization_mono
    intro x
    apply iSup_le
    intro v
    exact le_iSup (fun w : partialPCompetitors θ φ K f => w.val x)
      ⟨v.val, v.property.1, v.property.2.1, hOrdP v⟩
  have hAllOrd : uscSup (fun v : partialPCompetitors θ φ K f => v.val) ≤
      partialEnvelope θ φ K f := by
    apply uscRegularization_le (upperSemicontinuous_partialEnvelope θ φ K f)
    intro x
    apply iSup_le
    intro v
    obtain ⟨w, hvw⟩ := positivePartialPCompetitors_cofinal ω hφ hφpos hf v
    exact (hvw x).trans (le_partialEnvelope_of_positive_globalP ω hφ hφpos w x)
  have hPosOrd : uscSup (fun v : positivePartialPCompetitors θ φ K f => v.val.val) ≤
      partialEnvelope θ φ K f :=
    uscRegularization_le (upperSemicontinuous_partialEnvelope θ φ K f)
      (fun x => iSup_le fun v => le_partialEnvelope_of_positive_globalP ω hφ hφpos v x)
  have hOrdPos : partialEnvelope θ φ K f ≤
      uscSup (fun v : positivePartialPCompetitors θ φ K f => v.val.val) := by
    rw [partialEnvelope_eq_positive ω hφ hφpos hf]
    apply uscRegularization_mono
    intro x
    apply iSup_le
    intro v
    exact le_iSup (fun w : positivePartialPCompetitors θ φ K f => w.val.val x)
      ⟨⟨v.val.val, v.val.property.1, v.val.property.2.1, hOrdP v.val⟩, v.property⟩
  exact ⟨le_antisymm hOrdAll hAllOrd, le_antisymm hOrdPos hPosOrd⟩

end SGPT.Bergman.PartialPOrder
