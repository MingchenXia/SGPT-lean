import SGPT.NAPotential.SemipositiveProjectiveLimit

/-! Both entire source arrows, including the nondirected semipositive
positive-volume indexing cone. Every actual positive reader is recovered
internally; original component embeddings define the second map. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.WholeClosureNA.SemipositiveProjective

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {α β θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The exact positive embedding preserves and reflects original intrinsic
order, even across different actual whole backgrounds. -/
theorem positiveEmbedding_order_iff (omega : KahlerBackground n M)
    (G : SourcePositiveIModelTestCurve α) (H : SourcePositiveIModelTestCurve β) :
    SourceTestCurvePOrder G.val H.val ↔
      SourceNAPOrder (sourcePositiveTestCurveToNA G) (sourcePositiveTestCurveToNA H) := by
  rw [sourceNAPOrder_iff_realizedComponents _ _ omega omega]
  have hg := sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent G omega
  have hh := sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent H omega
  exact ⟨fun h => SourceTestCurvePOrder.trans omega hg.1
      (SourceTestCurvePOrder.trans omega h hh.2),
    fun h => SourceTestCurvePOrder.trans omega hg.2
      (SourceTestCurvePOrder.trans omega h hh.1)⟩

/-- Literal transition/embedding commuting square on the original objects. -/
theorem positiveEmbedding_transition (omega : KahlerBackground n M)
    (h : (atlasClosedFormToNative β - atlasClosedFormToNative α).val.IsSemipositive)
    (G : SourcePositiveIModelTestCurve α) :
    sourcePositiveTestCurveToNA (sourceIModelTestCurveTransition omega h G) =
      (sourcePositiveTestCurveToNA G).transition h := by
  have hc := sourceIModelTestCurveTransition_POrder_equivalent omega h G
  have hn₁ := (positiveEmbedding_order_iff omega _ _).mp hc.1
  have hn₂ := (positiveEmbedding_order_iff omega _ _).mp hc.2
  have ht := (sourcePositiveTestCurveToNA G).transition_POrder_equivalent omega h
  exact SourceNAPOrder.antisymm (hn₂.trans ht.1) (ht.2.trans hn₁)

/-- Actual positive projective limit. The arbitrary Kähler argument used to
implement the canonical transition is quantified; fixed-reader compatibility
is equivalent by the proved ambient-independence law below. -/
structure PositiveLimit (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (S : Set (Index n M)) where
  family : ∀ η : Member S, SourcePositiveIModelTestCurve (background θ η.val)
  compatible : ∀ (η ζ : Member S) (h : IndexLE η.val ζ.val) (omega : KahlerBackground n M),
    sourceIModelTestCurveTransition omega (background_difference θ h) (family η) = family ζ

@[ext] theorem PositiveLimit.ext {S : Set (Index n M)} {P Q : PositiveLimit θ S}
    (h : ∀ η, P.family η = Q.family η) : P = Q := by
  cases P with
  | mk p hp =>
    cases Q with
    | mk q hq =>
      have he : p = q := funext h
      subst q
      rfl

/-- This definition stores exactly usual compatibility: requiring one
arbitrary actual Kähler presentation already supplies every other one. -/
def PositiveLimit.ofFixedCompatibility {S : Set (Index n M)} (omega : KahlerBackground n M)
    (f : ∀ η : Member S, SourcePositiveIModelTestCurve (background θ η.val))
    (h : ∀ (η ζ : Member S) (hηζ : IndexLE η.val ζ.val),
      sourceIModelTestCurveTransition omega (background_difference θ hηζ) (f η) = f ζ) :
    PositiveLimit θ S where
  family := f
  compatible η ζ hηζ B := by
    rw [sourceIModelTestCurveTransition_ambient_independent B omega
      (background_difference θ hηζ) (f η)]
    exact h η ζ hηζ

/-- The source second map is the literal componentwise original embedding. -/
def embedPositiveLimit (omega : KahlerBackground n M) {S : Set (Index n M)}
    (P : PositiveLimit θ S) : NALimit θ S where
  family η := sourcePositiveTestCurveToNA (P.family η)
  compatible η ζ h := by
    rw [← positiveEmbedding_transition omega (background_difference θ h) (P.family η),
      P.compatible η ζ h omega]

/-- Genuine positive volume of eta constructs the exact positive reader. -/
def positiveReader (omega : KahlerBackground n M) (Γ : SourceNAPotential θ) (η : Index n M) :
    SourcePositiveIModelTestCurve (background θ η) :=
  semipositivePositiveVolumeReader omega Γ (nativeClosedFormToAtlas (representative η))
    (by simpa only [sourceNativeAtlasForm_roundTrip] using representative_semipositive η)
    (by simpa only [sourceNativeAtlasForm_roundTrip] using representative_volume_pos η)

theorem positiveReader_embedding (omega : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (η : Index n M) :
    sourcePositiveTestCurveToNA (positiveReader omega Γ η) =
      Γ.backgroundChange (nativeClosedFormToAtlas (representative η))
        (by simpa only [sourceNativeAtlasForm_roundTrip] using representative_semipositive η) :=
  semipositivePositiveVolumeReader_embedding omega Γ
    (nativeClosedFormToAtlas (representative η))
    (by simpa only [sourceNativeAtlasForm_roundTrip] using representative_semipositive η)
    (by simpa only [sourceNativeAtlasForm_roundTrip] using representative_volume_pos η)

/-- Manufacture all original positive compatibility identities by the
actual embedding commuting square and original embedding injectivity. -/
def toPositiveLimit (omega : KahlerBackground n M) (S : Set (Index n M))
    (Γ : SourceNAPotential θ) : PositiveLimit θ S where
  family η := positiveReader omega Γ η.val
  compatible η ζ h B := by
    apply sourcePositiveTestCurveToNA_injective omega
    rw [positiveEmbedding_transition B (background_difference θ h),
      positiveReader_embedding, positiveReader_embedding]
    exact (toNALimit omega S Γ).compatible η ζ h

/-- Exact original source commuting triangle, with no supplied comparison law. -/
theorem embed_toPositiveLimit (omega : KahlerBackground n M) (S : Set (Index n M))
    (Γ : SourceNAPotential θ) :
    embedPositiveLimit omega (toPositiveLimit omega S Γ) = toNALimit omega S Γ := by
  apply NALimit.ext
  intro η
  exact positiveReader_embedding omega Γ η.val

/-- Componentwise injectivity applies to whole actual compatible families. -/
theorem embedPositiveLimit_injective (omega : KahlerBackground n M) {S : Set (Index n M)} :
    Function.Injective (embedPositiveLimit (θ := θ) omega (S := S)) := by
  intro P Q h
  apply PositiveLimit.ext
  intro η
  exact sourcePositiveTestCurveToNA_injective omega
    (congrArg (fun R : NALimit θ S => R.family η) h)

/-- Every non-positive compatible family has an ACTUAL positive-family
preimage, by the manufactured original system and positive recovery. -/
theorem embedPositiveLimit_bijective (omega : KahlerBackground n M)
    {S : Set (Index n M)} (hS : ContainsKahler S) :
    Function.Bijective (embedPositiveLimit (θ := θ) omega (S := S)) := by
  refine ⟨embedPositiveLimit_injective omega, ?_⟩
  intro P
  refine ⟨toPositiveLimit omega S (P.recover omega hS), ?_⟩
  rw [embed_toPositiveLimit, P.toNALimit_recover omega hS]

theorem toPositiveLimit_injective (omega : KahlerBackground n M)
    {S : Set (Index n M)} (hS : ContainsKahler S) :
    Function.Injective (toPositiveLimit (θ := θ) omega S) := by
  intro Γ Δ h
  apply toNALimit_injective omega hS
  simpa only [embed_toPositiveLimit] using congrArg (embedPositiveLimit omega) h

/-- Concrete recovered original system for an actual positive family. -/
def recoverPositive (omega : KahlerBackground n M) {S : Set (Index n M)}
    (hS : ContainsKahler S) (P : PositiveLimit θ S) : SourceNAPotential θ :=
  (embedPositiveLimit omega P).recover omega hS

theorem toPositiveLimit_recoverPositive (omega : KahlerBackground n M)
    {S : Set (Index n M)} (hS : ContainsKahler S) (P : PositiveLimit θ S) :
    toPositiveLimit omega S (recoverPositive omega hS P) = P := by
  apply embedPositiveLimit_injective omega
  rw [embed_toPositiveLimit]
  exact (embedPositiveLimit omega P).toNALimit_recover omega hS

/-- Full first source bijection for arbitrary actual S containing Kah(X). -/
theorem toPositiveLimit_bijective (omega : KahlerBackground n M)
    {S : Set (Index n M)} (hS : ContainsKahler S) :
    Function.Bijective (toPositiveLimit (θ := θ) omega S) :=
  ⟨toPositiveLimit_injective omega hS,
    fun P => ⟨recoverPositive omega hS P, toPositiveLimit_recoverPositive omega hS P⟩⟩

def positiveLimitEquiv (omega : KahlerBackground n M) {S : Set (Index n M)}
    (hS : ContainsKahler S) : SourceNAPotential θ ≃ PositiveLimit θ S where
  toFun := toPositiveLimit omega S
  invFun := recoverPositive omega hS
  left_inv Γ := toPositiveLimit_injective omega hS
    (toPositiveLimit_recoverPositive omega hS (toPositiveLimit omega S Γ))
  right_inv := toPositiveLimit_recoverPositive omega hS

/-- Actual inverse for the second arrow: recover the original NA system,
then manufacture its whole positive extension. -/
def positiveToNALimitEquiv (omega : KahlerBackground n M) {S : Set (Index n M)}
    (hS : ContainsKahler S) : PositiveLimit θ S ≃ NALimit θ S where
  toFun := embedPositiveLimit omega
  invFun P := toPositiveLimit omega S (P.recover omega hS)
  left_inv P := toPositiveLimit_recoverPositive omega hS P
  right_inv P := (embed_toPositiveLimit omega S _).trans (P.toNALimit_recover omega hS)

/-- Canonical positive readers do not depend on the auxiliary Kähler
presentation used by the genuine positive-part recovery theorem. -/
theorem positiveReader_independent (omega omega' : KahlerBackground n M)
    (Γ : SourceNAPotential θ) (η : Index n M) :
    positiveReader omega Γ η = positiveReader omega' Γ η := by
  apply sourcePositiveTestCurveToNA_injective omega
  rw [positiveReader_embedding, positiveReader_embedding]

/-- Original curve order reads the exact original NA order on every index. -/
theorem toPositiveLimit_order_iff (omega : KahlerBackground n M) {S : Set (Index n M)}
    (hS : ContainsKahler S) {σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ) :
    SourceNAPOrder Γ Δ ↔ ∀ η : Member S,
      SourceTestCurvePOrder ((toPositiveLimit omega S Γ).family η).val
        ((toPositiveLimit omega S Δ).family η).val := by
  rw [toNALimit_order_iff omega hS Γ Δ]
  apply forall_congr'
  intro η
  rw [positiveEmbedding_order_iff omega]
  change SourceNAPOrder ((toNALimit omega S Γ).family η) ((toNALimit omega S Δ).family η) ↔
    SourceNAPOrder (sourcePositiveTestCurveToNA (positiveReader omega Γ η.val))
      (sourcePositiveTestCurveToNA (positiveReader omega Δ η.val))
  rw [positiveReader_embedding, positiveReader_embedding]
  rfl

/-- Exactly the already imported Kähler positive-component family type. -/
abbrev KahlerPositiveFamily (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :=
  {c : ∀ κ : SourceKahlerForm n M, SourcePositiveIModelTestCurve (sourceNAComponentBackground θ κ) //
    ∀ (κ ζ : SourceKahlerForm n M) (h : sourceKahlerFormLE κ ζ),
      sourceIModelTestCurveTransition (sourceKahlerFormRepresentative ζ)
        (sourceNAComponentBackground_difference θ h) (c κ) = c ζ}

/-- The Kähler second arrow is also the literal componentwise embedding. -/
def embedKahlerPositiveFamily (P : KahlerPositiveFamily θ) : SourceNAProjectiveLimit θ :=
  ((sourceNAPotentialEquivCompatibleComponents θ).symm P).toEmbeddedProjectiveLimit

theorem embedKahlerPositiveFamily_family (P : KahlerPositiveFamily θ) (κ : SourceKahlerForm n M) :
    (embedKahlerPositiveFamily P).family κ = sourcePositiveTestCurveToNA (P.val κ) := rfl

theorem embedKahlerPositiveFamily_bijective (omega : KahlerBackground n M) :
    Function.Bijective (embedKahlerPositiveFamily (θ := θ)) :=
  (SourceNAPotential.toEmbeddedProjectiveLimit_bijective (θ := θ) omega).comp
    (sourceNAPotentialEquivCompatibleComponents θ).symm.bijective

/-- COMPLETE source prop:PSHNAreform1: BOTH printed arrows, for BOTH printed
indexing domains, using their actual original positive and non-positive spaces.
The semipositive cone is not assumed directed. All n, including n=0. -/
theorem source_PSHNAreform1_whole (omega : KahlerBackground n M) :
    (Function.Bijective (toPositiveLimit (θ := θ) omega Set.univ) ∧
      Function.Bijective (embedPositiveLimit (θ := θ) omega (S := Set.univ))) ∧
    (Function.Bijective ((sourceNAPotentialEquivCompatibleComponents θ) :
        SourceNAPotential θ → KahlerPositiveFamily θ) ∧
      Function.Bijective (embedKahlerPositiveFamily (θ := θ))) := by
  have hS : ContainsKahler (Set.univ : Set (Index n M)) := fun _ => Set.mem_univ _
  exact ⟨⟨toPositiveLimit_bijective omega hS, embedPositiveLimit_bijective omega hS⟩,
    ⟨(sourceNAPotentialEquivCompatibleComponents θ).bijective,
      embedKahlerPositiveFamily_bijective omega⟩⟩

end SGPT.PSH.VariableComplexAtlas.WholeClosureNA.SemipositiveProjective
