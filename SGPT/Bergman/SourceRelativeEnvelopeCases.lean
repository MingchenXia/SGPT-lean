import SGPT.Bergman.SourcePartialEnvelopes
import SGPT.PSH.SourceCapacity
import SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact

/-! # All four original relative-envelope compatibility cases

The original genuine reference is retained, with arbitrary extended-real
obstacles. In particular it internally supplies a nonempty theta-PSH class
for the SAME minimal envelope; no positive-mass or big-class input is used.
The stronger all-K domain includes the original closed non-pluripolar K.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.RelativeEnvelopeCases

open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original whole-X subtype obstacle is exactly global QE comparison. -/
theorem partialObstacle_univ_iff (g v : M → EReal) :
    partialObstacle (n := n) univ (fun x : (univ : Set M) => g x.val) v ↔
      SourceQuasiEverywhere (n := n) (fun x => v x ≤ g x) := by
  have heq : (fun x : M => ∀ hx : x ∈ (univ : Set M), v x ≤ g x) =
      (fun x => v x ≤ g x) := by
    funext x
    exact propext ⟨fun h => h (mem_univ x), fun h _ => h⟩
  change SourceQuasiEverywhere (n := n) _ ↔ _
  rw [heq]

/-- Zero need not be theta-PSH: genuine comparison uses its real continuity. -/
theorem sourceQuasiEverywhere_le_zero_iff
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : M → EReal}
    (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    SourceQuasiEverywhere (n := n) (fun x => v x ≤ 0) ↔ v ≤ 0 := by
  constructor
  · intro h
    have hq := (sourceQuasiEverywhere_iff_native _).mp h
    have hn := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
    change ∀ x, v x ≤ 0
    simpa only [EReal.coe_zero] using
      ContinuousObstacleEnvelopeContact.le_coe_of_ae_in_charts_le hn.1
        (F := fun _ : M => (0 : ℝ)) continuous_const
        (fun e => hq.ae_in_chart e volume)
  · exact sourceQuasiEverywhere_of_forall

/-- ALL whole-X candidates reindex the existing generalized relative envelope. -/
theorem partialEnvelope_univ (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ g : M → EReal) :
    partialEnvelope θ φ univ (fun x : (univ : Set M) => g x.val) =
      sourceRelativeEnvelope θ φ g := by
  rw [partialEnvelope_eq_relative]
  have heq : extendedObstacle univ (fun x : (univ : Set M) => g x.val) = g := by
    funext x
    simp only [extendedObstacle, mem_univ, dif_pos]
  rw [heq]

/-- The normalized ordinary envelope is exactly the zero whole-X partial case. -/
theorem partialEnvelope_univ_zero (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) :
    partialEnvelope θ φ univ (fun _ => 0) = sourceSingularityEnvelope θ φ := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro v
    have hv0 := (sourceQuasiEverywhere_le_zero_iff v.property.1).mp
      ((partialObstacle_univ_iff (fun _ => 0) v.val).mp v.property.2.1)
    exact le_iSup (fun w : sourceSingularityCompetitors θ φ => w.val x)
      ⟨v.val, v.property.1, hv0, v.property.2.2⟩
  · apply iSup_le
    intro v
    exact le_iSup (fun w : partialCompetitors θ φ univ (fun _ => 0) => w.val x)
      ⟨v.val, v.property.1, partialObstacle_of_forall (fun y => v.property.2.1 y.val),
        v.property.2.2⟩

variable [CompactSpace M] [Nonempty M]

/-- The true ALL-I-order characterization handles arbitrary zero input mass. -/
theorem partialIEnvelope_univ_zero
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    partialIEnvelope θ φ univ (fun _ => 0) = sourceIEnvelope θ φ := by
  apply le_antisymm
  · apply uscRegularization_le (upperSemicontinuous_sourceIEnvelope θ φ)
    intro x
    apply iSup_le
    intro v
    have hv0 := (sourceQuasiEverywhere_le_zero_iff v.property.1).mp
      ((partialObstacle_univ_iff (fun _ => 0) v.val).mp v.property.2.1)
    have hle : v.val ≤ sourceIEnvelope θ φ := by
      rw [sourceIEnvelope_eq_sSup_sourceIOrder hφ]
      exact le_sSup ⟨v.property.1, hv0, v.property.2.2⟩
    exact hle x
  · exact le_partialIEnvelope (isThetaPSH_sourceIEnvelope hφ)
      (partialObstacle_of_forall (fun x => sourceIEnvelope_le_zero θ φ x.val))
      (sourceIEquivalent_iEnvelope hφ).2

/-- Original genuine phi supplies the actual Vtheta, without bigness or mass. -/
theorem sourceMinimalEnvelope_genuine_of_reference
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    (ofFixedModel n M).IsThetaPSH θ (sourceMinimalEnvelope θ) := by
  apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
  rw [sourceMinimalEnvelope_eq_native]
  let T := atlasClosedFormToNative θ
  have hn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  exact FirstPass.thetaPshSupremum_isThetaPshPotential T.val T.property.1 T.property.2
    hn.1.hasSmoothLocalPotentials ⟨φ, hn⟩

/-- Every genuine eta has the true finite additive comparison to the same Vtheta. -/
theorem singularityLE_sourceMinimalEnvelope
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ η : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hη : (ofFixedModel n M).IsThetaPSH θ η) :
    SGPT.PSH.SingularityLE η (sourceMinimalEnvelope θ) := by
  rw [sourceMinimalEnvelope_eq_native]
  let T := atlasClosedFormToNative θ
  have hn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ
  exact FirstPass.thetaPshSupremum_minimalSingularities T.val T.property.1 T.property.2
    hn.1.hasSmoothLocalPotentials ⟨φ, hn⟩ η
    ((isThetaPSH_iff_nativeThetaPotential θ η).mp hη)

/-- ALL ordinary minimal-reference candidates equal the literal unrestricted family. -/
theorem partialEnvelope_minimal_eq_unrestricted
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (K : Set M) (f : K → EReal) :
    partialEnvelope θ (sourceMinimalEnvelope θ) K f =
      uscSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
        partialObstacle (n := n) K f v} => v.val) := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro v
    exact le_iSup (fun w : {w : M → EReal // (ofFixedModel n M).IsThetaPSH θ w ∧
      partialObstacle (n := n) K f w} => w.val x) ⟨v.val, v.property.1, v.property.2.1⟩
  · apply iSup_le
    intro v
    exact le_iSup (fun w : partialCompetitors θ (sourceMinimalEnvelope θ) K f => w.val x)
      ⟨v.val, v.property.1, v.property.2, singularityLE_sourceMinimalEnvelope hφ v.property.1⟩

/-- ALL ideal minimal-reference candidates give the SAME unrestricted family. -/
theorem partialIEnvelope_minimal_eq_unrestricted
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (K : Set M) (f : K → EReal) :
    partialIEnvelope θ (sourceMinimalEnvelope θ) K f =
      uscSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
        partialObstacle (n := n) K f v} => v.val) := by
  have hV := sourceMinimalEnvelope_genuine_of_reference hφ
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro v
    exact le_iSup (fun w : {w : M → EReal // (ofFixedModel n M).IsThetaPSH θ w ∧
      partialObstacle (n := n) K f w} => w.val x) ⟨v.val, v.property.1, v.property.2.1⟩
  · apply iSup_le
    intro v
    exact le_iSup (fun w : partialICompetitors θ (sourceMinimalEnvelope θ) K f => w.val x)
      ⟨v.val, v.property.1, v.property.2,
        sourceIOrder_of_singularityLE v.property.1 hV
          (singularityLE_sourceMinimalEnvelope hφ v.property.1)⟩

/-- The literal third compatibility group, preserving every original weight value. -/
theorem partialEnvelopes_minimal_reference
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (K : Set M) (f : K → EReal) :
    partialEnvelope θ (sourceMinimalEnvelope θ) K f =
        partialIEnvelope θ (sourceMinimalEnvelope θ) K f ∧
      partialIEnvelope θ (sourceMinimalEnvelope θ) K f =
        uscSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
          partialObstacle (n := n) K f v} => v.val) :=
  ⟨(partialEnvelope_minimal_eq_unrestricted hφ K f).trans
      (partialIEnvelope_minimal_eq_unrestricted hφ K f).symm,
    partialIEnvelope_minimal_eq_unrestricted hφ K f⟩

/-- The whole-X minimal case is BOTH its literal QE supremum and existing Ptheta(g). -/
theorem partialEnvelope_minimal_univ
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (g : M → EReal) :
    partialEnvelope θ (sourceMinimalEnvelope θ) univ
        (fun x : (univ : Set M) => g x.val) =
        uscSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
          SourceQuasiEverywhere (n := n) (fun x => v x ≤ g x)} => v.val) ∧
      partialEnvelope θ (sourceMinimalEnvelope θ) univ
        (fun x : (univ : Set M) => g x.val) = sourceRelativeEnvelope θ (fun _ => ⊤) g := by
  have hfirst : partialEnvelope θ (sourceMinimalEnvelope θ) univ
      (fun x : (univ : Set M) => g x.val) =
      uscSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
        SourceQuasiEverywhere (n := n) (fun x => v x ≤ g x)} => v.val) := by
    rw [partialEnvelope_minimal_eq_unrestricted hφ]
    apply congrArg uscRegularization
    funext x
    apply le_antisymm
    · apply iSup_le
      intro v
      exact le_iSup (fun w : {w : M → EReal // (ofFixedModel n M).IsThetaPSH θ w ∧
        SourceQuasiEverywhere (n := n) (fun x => w x ≤ g x)} => w.val x)
        ⟨v.val, v.property.1, (partialObstacle_univ_iff g v.val).mp v.property.2⟩
    · apply iSup_le
      intro v
      exact le_iSup (fun w : {w : M → EReal // (ofFixedModel n M).IsThetaPSH θ w ∧
        partialObstacle (n := n) univ (fun y : (univ : Set M) => g y.val) w} => w.val x)
        ⟨v.val, v.property.1, (partialObstacle_univ_iff g v.val).mpr v.property.2⟩
  refine ⟨hfirst, hfirst.trans ?_⟩
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro v
    have htop : SGPT.PSH.SingularityLE v.val (fun _ : M => ⊤) :=
      (singularityLE_iff_exists_real _ _).mpr ⟨0, fun _ => by simp only [EReal.coe_zero,
        add_zero, le_top]⟩
    exact le_iSup (fun w : sourceRelativeEnvelopeCompetitors θ (fun _ => ⊤) g => w.val x)
      ⟨v.val, v.property.1, v.property.2, htop⟩
  · apply iSup_le
    intro v
    exact le_iSup (fun w : {w : M → EReal // (ofFixedModel n M).IsThetaPSH θ w ∧
      SourceQuasiEverywhere (n := n) (fun x => w x ≤ g x)} => w.val x)
      ⟨v.val, v.property.1, v.property.2.1⟩

/-- WHOLE original ex:rel_env_cases: all four groups, arbitrary EReal obstacles,
zero-mass original genuine reference, and Vtheta genuinely produced internally. -/
theorem relative_envelope_cases
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (K : Set M) (f : K → EReal)
    (g : M → EReal) :
    (partialEnvelope θ φ univ (fun _ => 0) = sourceSingularityEnvelope θ φ ∧
      partialIEnvelope θ φ univ (fun _ => 0) = sourceIEnvelope θ φ) ∧
    (partialEnvelope θ φ univ (fun x : (univ : Set M) => g x.val) =
      sourceRelativeEnvelope θ φ g) ∧
    (partialEnvelope θ (sourceMinimalEnvelope θ) K f =
        partialIEnvelope θ (sourceMinimalEnvelope θ) K f ∧
      partialIEnvelope θ (sourceMinimalEnvelope θ) K f =
        uscSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
          partialObstacle (n := n) K f v} => v.val)) ∧
    (partialEnvelope θ (sourceMinimalEnvelope θ) univ
        (fun x : (univ : Set M) => g x.val) =
        uscSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
          SourceQuasiEverywhere (n := n) (fun x => v x ≤ g x)} => v.val) ∧
      partialEnvelope θ (sourceMinimalEnvelope θ) univ
        (fun x : (univ : Set M) => g x.val) = sourceRelativeEnvelope θ (fun _ => ⊤) g) :=
  ⟨⟨partialEnvelope_univ_zero θ φ, partialIEnvelope_univ_zero hφ⟩,
    partialEnvelope_univ θ φ g, partialEnvelopes_minimal_reference hφ K f,
    partialEnvelope_minimal_univ hφ g⟩

end SGPT.Bergman.RelativeEnvelopeCases
