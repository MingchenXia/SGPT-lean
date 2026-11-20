import SGPT.PSH.SourceThetaPSHCompactness
import SGPT.Envelopes.SourceGlobalPRelativeEnvelope
import SGPT.PSH.SourceIEnvelopeMonotonicity
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

/-! # Original partial envelopes and retained bounded-above obstacles

Literal subtype obstacles and actual ambient pluripolar exceptional sets are
retained. The positive-mass cofinality and global P-order comparison use actual
original potentials and internally manufactured competitors. Obstacle retention
uses the actual Choquet family, not an assumed output PSH or boundedness fact.
The full compound source proposition's concavity clause is not proved here.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology

namespace SGPT.Bergman.PartialEnvelope

open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual original failure set on K must be locally pluripolar in X. -/
def partialObstacle (K : Set M) (f : K → EReal) (v : M → EReal) : Prop :=
  SourceQuasiEverywhere (n := n) (fun x => ∀ hx : x ∈ K, v x ≤ f ⟨x, hx⟩)

/-- The source's existential ambient exceptional set, with literal subtype f. -/
theorem partialObstacle_iff_exists_pluripolar (K : Set M) (f : K → EReal) (v : M → EReal) :
    partialObstacle (n := n) K f v ↔
      ∃ S : Set M, (ofFixedModel n M).LocallyPluripolar S ∧
        ∀ x : K, x.val ∉ S → v x.val ≤ f x := by
  constructor
  · intro h
    refine ⟨{x | ¬ ∀ hx : x ∈ K, v x ≤ f ⟨x, hx⟩}, h, ?_⟩
    intro x hx
    exact (not_not.mp hx) x.property
  · rintro ⟨S, hS, hbound⟩
    apply hS.mono
    intro x hbad
    by_contra hxS
    exact hbad (fun hx => hbound ⟨x, hx⟩ hxS)

theorem partialObstacle_of_forall {K : Set M} {f : K → EReal} {v : M → EReal}
    (h : ∀ x : K, v x.val ≤ f x) : partialObstacle (n := n) K f v :=
  sourceQuasiEverywhere_of_forall (fun x hx => h ⟨x, hx⟩)

/-- Lowering a candidate retains its actual original exceptional set. -/
theorem partialObstacle_of_le {K : Set M} {f : K → EReal} {v w : M → EReal}
    (hw : partialObstacle (n := n) K f w) (hvw : v ≤ w) :
    partialObstacle (n := n) K f v := by
  obtain ⟨S, hS, hbound⟩ := (partialObstacle_iff_exists_pluripolar K f w).mp hw
  exact (partialObstacle_iff_exists_pluripolar K f v).mpr
    ⟨S, hS, fun x hx => (hvw x.val).trans (hbound x hx)⟩

theorem partialObstacle_mono {K : Set M} {f g : K → EReal} {v : M → EReal}
    (hf : partialObstacle (n := n) K f v) (hfg : f ≤ g) :
    partialObstacle (n := n) K g v := by
  obtain ⟨S, hS, hbound⟩ := (partialObstacle_iff_exists_pluripolar K f v).mp hf
  exact (partialObstacle_iff_exists_pluripolar K g v).mpr
    ⟨S, hS, fun x hx => (hbound x hx).trans (hfg x)⟩

/-- The actual obstacle is unrestricted away from the original set K. -/
def extendedObstacle (K : Set M) (f : K → EReal) : M → EReal := by
  classical
  exact fun x => if hx : x ∈ K then f ⟨x, hx⟩ else ⊤

theorem partialObstacle_iff_extended (K : Set M) (f : K → EReal) (v : M → EReal) :
    partialObstacle (n := n) K f v ↔
      SourceQuasiEverywhere (n := n) (fun x => v x ≤ extendedObstacle K f x) := by
  have heq : (fun x => ∀ hx : x ∈ K, v x ≤ f ⟨x, hx⟩) =
      (fun x => v x ≤ extendedObstacle K f x) := by
    classical
    funext x
    apply propext
    by_cases hx : x ∈ K <;> simp [extendedObstacle, hx]
  change SourceQuasiEverywhere (n := n) _ ↔ _
  rw [heq]

/-- All original ordinary partial-envelope candidates; no positive mass restriction. -/
def partialCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) :=
  {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
    partialObstacle (n := n) K f v ∧ SGPT.PSH.SingularityLE v φ}

/-- All original ideal partial-envelope candidates with original QPSH domains. -/
def partialICompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) :=
  {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
    partialObstacle (n := n) K f v ∧ sourceIOrder (ofFixedModel n M) v φ}

/-- SGPT def:partial_env ordinary operator, including the empty supremum. -/
def partialEnvelope (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) : M → EReal :=
  uscSup (fun v : partialCompetitors θ φ K f => v.val)

/-- SGPT def:partial_env ideal operator; positive-real multipliers are not truncated. -/
def partialIEnvelope (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) : M → EReal :=
  uscSup (fun v : partialICompetitors θ φ K f => v.val)

/-- The same source operation is the EXISTING relative envelope at the actual extension. -/
theorem partialEnvelope_eq_relative (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) :
    partialEnvelope θ φ K f = sourceRelativeEnvelope θ φ (extendedObstacle K f) := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro v
    exact le_iSup (fun w : sourceRelativeEnvelopeCompetitors θ φ (extendedObstacle K f) => w.val x)
      ⟨v.val, v.property.1, (partialObstacle_iff_extended K f v.val).mp v.property.2.1,
        v.property.2.2⟩
  · apply iSup_le
    intro v
    exact le_iSup (fun w : partialCompetitors θ φ K f => w.val x)
      ⟨v.val, v.property.1, (partialObstacle_iff_extended K f v.val).mpr v.property.2.1,
        v.property.2.2⟩

theorem upperSemicontinuous_partialEnvelope
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (K : Set M) (f : K → EReal) : UpperSemicontinuous (partialEnvelope θ φ K f) :=
  upperSemicontinuous_uscRegularization _

theorem upperSemicontinuous_partialIEnvelope
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (K : Set M) (f : K → EReal) : UpperSemicontinuous (partialIEnvelope θ φ K f) :=
  upperSemicontinuous_uscRegularization _

theorem le_partialEnvelope {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {φ v : M → EReal} {K : Set M} {f : K → EReal}
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (hK : partialObstacle (n := n) K f v)
    (hvφ : SGPT.PSH.SingularityLE v φ) : v ≤ partialEnvelope θ φ K f := by
  intro x
  exact (le_iSup (fun w : partialCompetitors θ φ K f => w.val x) ⟨v, hv, hK, hvφ⟩).trans
    (le_uscRegularization (fun y => ⨆ w : partialCompetitors θ φ K f, w.val y) x)

theorem le_partialIEnvelope {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {φ v : M → EReal} {K : Set M} {f : K → EReal}
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (hK : partialObstacle (n := n) K f v)
    (hvφ : sourceIOrder (ofFixedModel n M) v φ) : v ≤ partialIEnvelope θ φ K f := by
  intro x
  exact (le_iSup (fun w : partialICompetitors θ φ K f => w.val x) ⟨v, hv, hK, hvφ⟩).trans
    (le_uscRegularization (fun y => ⨆ w : partialICompetitors θ φ K f, w.val y) x)

/-- Entire original-family inclusion, valid for empty and top-valued envelopes too. -/
theorem partialEnvelope_mono_obstacle (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) {f g : K → EReal} (hfg : f ≤ g) :
    partialEnvelope θ φ K f ≤ partialEnvelope θ φ K g := by
  apply uscRegularization_mono
  intro x
  apply iSup_le
  intro v
  exact le_iSup (fun w : partialCompetitors θ φ K g => w.val x)
    ⟨v.val, v.property.1, partialObstacle_mono v.property.2.1 hfg, v.property.2.2⟩

theorem partialIEnvelope_mono_obstacle (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) {f g : K → EReal} (hfg : f ≤ g) :
    partialIEnvelope θ φ K f ≤ partialIEnvelope θ φ K g := by
  apply uscRegularization_mono
  intro x
  apply iSup_le
  intro v
  exact le_iSup (fun w : partialICompetitors θ φ K g => w.val x)
    ⟨v.val, v.property.1, partialObstacle_mono v.property.2.1 hfg, v.property.2.2⟩

theorem partialIEnvelope_mono_reference (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ ψ : M → EReal} (K : Set M) (f : K → EReal)
    (hφψ : sourceIOrder (ofFixedModel n M) φ ψ) :
    partialIEnvelope θ φ K f ≤ partialIEnvelope θ ψ K f := by
  apply uscRegularization_mono
  intro x
  apply iSup_le
  intro v
  exact le_iSup (fun w : partialICompetitors θ ψ K f => w.val x)
    ⟨v.val, v.property.1, v.property.2.1, sourceIOrder_trans v.property.2.2 hφψ⟩

/-- The original additive source comparison gives all original multiplier levels. -/
theorem sourceIOrder_of_singularityLE
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v φ : M → EReal}
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hvφ : SGPT.PSH.SingularityLE v φ) : sourceIOrder (ofFixedModel n M) v φ := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real v φ).mp hvφ
  apply (sourceIOrder_iff_native ⟨θ, hv⟩ ⟨θ, hφ⟩).mpr
  exact iOrderOnManifold_of_le_add
    ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).1.quasiPlurisubharmonic hC

/-- Original prop:partial_env clause1, with the actual original reference. -/
theorem partialEnvelope_le_partialIEnvelope
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (K : Set M) (f : K → EReal) :
    partialEnvelope θ φ K f ≤ partialIEnvelope θ φ K f := by
  apply uscRegularization_mono
  intro x
  apply iSup_le
  intro v
  exact le_iSup (fun w : partialICompetitors θ φ K f => w.val x)
    ⟨v.val, v.property.1, v.property.2.1,
      sourceIOrder_of_singularityLE v.property.1 hφ v.property.2.2⟩

end SGPT.Bergman.PartialEnvelope

namespace SGPT.Bergman.PartialEnvelope

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Positive mass is a property of a genuine original partial competitor. -/
def positivePartialCompetitors (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (K : Set M) (f : K → EReal) :=
  {v : partialCompetitors θ φ K f //
    0 < sourcePotentialNonPluripolarMeasure θ v.val v.property.1 univ}

/-- Original compactness and the obstacle lower bound manufacture a genuine
positive-mass candidate above every original ordinary candidate. -/
theorem positivePartialCompetitors_cofinal (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ f x)
    (v : partialCompetitors θ φ K f) :
    ∃ w : positivePartialCompetitors θ φ K f, v.val ≤ w.val.val := by
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
  have hwφ : SGPT.PSH.SingularityLE w φ := by
    obtain ⟨D, hD⟩ := (SGPT.PSH.singularityLE_iff_exists_real v.val φ).mp v.property.2.2
    apply (SGPT.PSH.singularityLE_iff_exists_real w φ).mpr
    refine ⟨max D c, fun x => max_le ?_ ?_⟩
    · exact (hD x).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left D c)))
    · exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right D c))
  have hχw : SGPT.PSH.SingularityLE χ w :=
    MoreSingularOn.of_le fun x _ => le_max_right (v.val x) (χ x)
  have hwpos : 0 < sourcePotentialNonPluripolarMeasure θ w hw univ :=
    hχpos.trans_le (sourcePotentialNonPluripolarMass_mono ω hχ hw hχw)
  exact ⟨⟨⟨w, hw, hwK, hwφ⟩, hwpos⟩, fun x => le_max_left (v.val x) (χ x)⟩

/-- The entire original partial envelope is unchanged by the produced
positive-mass cofinality; no nonempty-family certificate is assumed. -/
theorem partialEnvelope_eq_positive (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {K : Set M} {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ f x) :
    partialEnvelope θ φ K f =
      uscSup (fun v : positivePartialCompetitors θ φ K f => v.val.val) := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro v
    obtain ⟨w, hvw⟩ := positivePartialCompetitors_cofinal ω hφ hφpos hf v
    exact (hvw x).trans (le_iSup (fun w : positivePartialCompetitors θ φ K f => w.val.val x) w)
  · apply iSup_le
    intro v
    exact le_iSup (fun w : partialCompetitors θ φ K f => w.val x) v.val

/-- Whole original prop:Penv_partial_monotone: the actual GLOBAL P-order,
positive original references and subtype obstacle supply every needed roof. -/
theorem partialEnvelope_mono_globalPOrder (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ ψ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (hψpos : 0 < sourcePotentialNonPluripolarMeasure θ ψ hψ univ)
    {K : Set M} {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, (B : EReal) ≤ f x)
    (hP : GlobalPComparison.sourcePOrder (n := n) φ ψ) :
    partialEnvelope θ φ K f ≤ partialEnvelope θ ψ K f := by
  let H := partialEnvelope θ ψ K f
  have hH : UpperSemicontinuous H := upperSemicontinuous_partialEnvelope θ ψ K f
  have hpositive (v : positivePartialCompetitors θ φ K f) : v.val.val ≤ H := by
    have hη := v.val.property.1
    have hηn := (isThetaPSH_iff_nativeThetaPotential θ v.val.val).mp hη
    have hφn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
    have hηφP : GlobalPComparison.sourcePOrder (n := n) v.val.val φ :=
      GlobalPComparison.sourcePOrder_of_moreSingular ω hηn.quasiPshPotential hφn.quasiPshPotential
        v.val.property.2.2
    have hηψP : GlobalPComparison.sourcePOrder (n := n) v.val.val ψ :=
      GlobalPComparison.sourcePOrder_trans ω hηφP hP
    have hroof (C : {C : ℝ // 0 < C}) :
        thetaRooftop θ v.val.val (fun x => ψ x + (C.val : EReal)) ≤ H := by
      obtain ⟨hr, _hne, _hmass, _hpos⟩ := sourcePOrder_shiftedRooftop_positive
        ω hψ hη hψpos v.property hηψP C.val C.property.le
      apply le_partialEnvelope hr
        (partialObstacle_of_le v.val.property.2.1 (thetaRooftop_le_left θ _ _))
      exact (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
        ⟨C.val, thetaRooftop_le_right θ _ _⟩
    have hexa := sourcePOrder_relativeRooftop_exhaustion ω hψ hη hψpos v.property hηψP
    have hsup : uscSup (fun C : {C : ℝ // 0 < C} =>
        thetaRooftop θ v.val.val (fun x => ψ x + (C.val : EReal))) ≤ H :=
      uscRegularization_le hH (fun x => iSup_le fun C => hroof C x)
    exact hexa.symm.le.trans hsup
  rw [partialEnvelope_eq_positive ω hφ hφpos hf]
  exact uscRegularization_le hH (fun x => iSup_le fun v => hpositive v x)

end SGPT.Bergman.PartialEnvelope

namespace SGPT.Bergman.PartialEnvelopeRetention

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope
open SGPT.PSH.ConnectedThetaPSHCompactness
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology Classical

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem locallyPluripolar_union {S T : Set M}
    (hS : (ofFixedModel n M).LocallyPluripolar S)
    (hT : (ofFixedModel n M).LocallyPluripolar T) :
    (ofFixedModel n M).LocallyPluripolar (S ∪ T) := by
  let U : ℕ → Set M := fun j => if j = 0 then S else T
  have hU (j : ℕ) : (ofFixedModel n M).LocallyPluripolar (U j) := by
    by_cases hj : j = 0
    · simpa only [U, if_pos hj] using hS
    · simpa only [U, if_neg hj] using hT
  apply (VariableComplexAtlas.LocallyPluripolar.iUnion hU).mono
  intro x hx
  rcases hx with hx | hx
  · exact mem_iUnion.mpr ⟨0, by simpa only [U, if_pos rfl] using hx⟩
  · exact mem_iUnion.mpr ⟨1, by simpa only [U, Nat.one_ne_zero, if_false] using hx⟩

variable [CompactSpace M] [ConnectedSpace M]

/-- Original bounded-above subtype obstacles survive the actual regularized
supremum of every genuine nonempty theta-PSH family. All uniform bounds and
all ambient pluripolar exceptional sets are manufactured internally. -/
theorem partialObstacle_uscSup {I : Type*} [Nonempty I]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K)
    {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, f x ≤ (B : EReal))
    {v : I → M → EReal} (hv : ∀ i, (ofFixedModel n M).IsThetaPSH θ (v i))
    (hvK : ∀ i, partialObstacle (n := n) K f (v i)) :
    partialObstacle (n := n) K f (uscSup v) := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨s, hs, heq⟩ := exists_seq_uscRegularization_iSup_eq (range_nonempty v)
  have hsθ (j : ℕ) : (ofFixedModel n M).IsThetaPSH θ (s j) := by
    obtain ⟨i, hi⟩ := hs j
    exact hi ▸ hv i
  have hsK (j : ℕ) : partialObstacle (n := n) K f (s j) := by
    obtain ⟨i, hi⟩ := hs j
    exact hi ▸ hvK i
  let S : ℕ → Set M := fun j => {x | ¬ ∀ hx : x ∈ K, s j x ≤ f ⟨x, hx⟩}
  have hS (j : ℕ) : (ofFixedModel n M).LocallyPluripolar (S j) := hsK j
  let N : Set M := ⋃ j, S j
  have hN : (ofFixedModel n M).LocallyPluripolar N :=
    VariableComplexAtlas.LocallyPluripolar.iUnion hS
  have hKN : (ofFixedModel n M).NonPluripolar (K \ N) := by
    intro hbad
    apply hK
    apply (locallyPluripolar_union hbad hN).mono
    intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl ⟨hx, hxN⟩
  obtain ⟨C, hC⟩ := source_nonpluripolar_uniform_sup (ofFixedModel n M)
    (Classical.arbitrary M) θ (K \ N) hKN B
  have hsbound (j : ℕ) (x : M) : s j x ≤ (C : EReal) := by
    have hsup := hC ⟨s j, hsθ j⟩ (fun y hy => ?_)
    · obtain ⟨c, hc, _⟩ := native_exists_real_sup
        ((isThetaPSH_iff_nativeThetaPotential θ (s j)).mp (hsθ j))
      rw [hc, EReal.toReal_coe] at hsup
      exact (le_iSup (s j) x).trans (hc.trans_le (EReal.coe_le_coe_iff.mpr hsup))
    · have hyS : y ∉ S j := fun hyS => hy.2 (mem_iUnion.mpr ⟨j, hyS⟩)
      have hyf : ∀ hyK : y ∈ K, s j y ≤ f ⟨y, hyK⟩ := not_not.mp hyS
      exact (hyf hy.1).trans (hB ⟨y, hy.1⟩)
  let E : Set M := {x | (⨆ j, s j x) < uscSup s x}
  have hE : (ofFixedModel n M).LocallyPluripolar E :=
    source_theta_sup_exceptional hsθ hsbound
  have hseq : uscSup s = uscSup v := by
    have hsfn : (⨆ j, s j) = fun x => ⨆ j, s j x := by
      funext x
      exact iSup_apply
    rw [hsfn, sSup_range_eq] at heq
    exact heq
  apply (partialObstacle_iff_exists_pluripolar K f (uscSup v)).mpr
  refine ⟨N ∪ E, locallyPluripolar_union hN hE, ?_⟩
  intro x hx
  have hxN : x.val ∉ N := fun h => hx (Or.inl h)
  have hxE : x.val ∉ E := fun h => hx (Or.inr h)
  have hraw : (⨆ j, s j x.val) ≤ f x := by
    apply iSup_le
    intro j
    have hxS : x.val ∉ S j := fun h => hxN (mem_iUnion.mpr ⟨j, h⟩)
    exact (not_not.mp hxS) x.property
  have hreg : uscSup s x.val ≤ ⨆ j, s j x.val := le_of_not_gt hxE
  rw [← hseq]
  exact hreg.trans hraw

/-- The entire original ordinary partial envelope retains every bounded-above
literal subtype obstacle q.e., including an actually empty competitor family. -/
theorem partialEnvelope_obstacle
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K)
    {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, f x ≤ (B : EReal)) :
    partialObstacle (n := n) K f (partialEnvelope θ φ K f) := by
  by_cases hi : Nonempty (partialCompetitors θ φ K f)
  · let := hi
    exact partialObstacle_uscSup hK hf (fun v => v.property.1) (fun v => v.property.2.1)
  · let : IsEmpty (partialCompetitors θ φ K f) := ⟨fun v => hi ⟨v⟩⟩
    apply partialObstacle_of_forall
    intro x
    simp only [partialEnvelope, uscSup, iSup_of_empty, uscRegularization_const]
    exact bot_le

/-- The same full original obstacle-retention clause for the original ideal
partial envelope, preserving the exact all-positive-level order subtype. -/
theorem partialIEnvelope_obstacle
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    {K : Set M} (hK : (ofFixedModel n M).NonPluripolar K)
    {f : K → EReal} (hf : ∃ B : ℝ, ∀ x : K, f x ≤ (B : EReal)) :
    partialObstacle (n := n) K f (partialIEnvelope θ φ K f) := by
  by_cases hi : Nonempty (partialICompetitors θ φ K f)
  · let := hi
    exact partialObstacle_uscSup hK hf (fun v => v.property.1) (fun v => v.property.2.1)
  · let : IsEmpty (partialICompetitors θ φ K f) := ⟨fun v => hi ⟨v⟩⟩
    apply partialObstacle_of_forall
    intro x
    simp only [partialIEnvelope, uscSup, iSup_of_empty, uscRegularization_const]
    exact bot_le

end SGPT.Bergman.PartialEnvelopeRetention
