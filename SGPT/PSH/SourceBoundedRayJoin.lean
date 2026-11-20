import SGPT.PSH.SourceRadialEnergy
import SGPT.PSH.SourceRelativeGeodesics
import SGPT.PSH.SourceDarvasComparison
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinDistance

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- EXACT original R-infinity: same singularity type relative to the
possibly unbounded model at every original nonnegative time. -/
abbrev SourceBoundedGeodesicRay (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) :=
  {ℓ : SourceRayFamily M // ℓ ∈ sourceBoundedRays omega θ φ hφ}

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- Actual relative same-type inclusion manufactures the entire original
positive-time finite-energy contract, preserving the SAME source ray. -/
def sourceBoundedRayToFiniteEnergyRay (omega : KahlerBackground n M)
    (L : SourceBoundedGeodesicRay omega θ φ hφ) : SourceFiniteEnergyRay omega θ φ hφ := by
  refine ⟨L.val, ⟨L.property.1.1, ?_⟩, L.property.2⟩
  intro t _
  exact (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mpr
    (RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ((sourceRelativeEInfinity_iff_native θ φ _).mp (L.property.1.2 t)))

/-- Genuine full-mass original ray inclusion retains EVERY original time. -/
def sourceBoundedRayToGeodesicRay (omega : KahlerBackground n M)
    (L : SourceBoundedGeodesicRay omega θ φ hφ) : SourceGeodesicRay omega θ φ hφ :=
  ⟨L.val, L.property.1.1, L.property.2⟩

/-- Literal original closed Perron stage from the model to the actual
pointwise terminal maximum; its source use has 0≤s≤T and T>0. -/
def sourceBoundedRayJoinStage (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (ℓ k : SourceRayFamily M) (T s : ℝ) : M → EReal :=
  sourcePerronClosedSlice omega θ φ
    (fun x ↦ max (sourceRayExtension ℓ T x) (sourceRayExtension k T x)) (s / T)

omit [ConnectedSpace M] in
/-- Complete literal stage dictionary retains the actual closed Perron
trace and every original endpoint/pole, with no output-class premise. -/
theorem sourceBoundedRayJoinStage_eq_native (omega : KahlerBackground n M)
    (ℓ k : SourceRayFamily M) (T s : ℝ) :
    sourceBoundedRayJoinStage omega θ φ ℓ k T s =
      SingularBoundedRayJoinStages.joinStage (atlasClosedFormToNative θ) φ
        (sourceRayExtension ℓ) (sourceRayExtension k) T s := by
  exact sourcePerronClosedSlice_eq_native omega θ φ _ (s / T)

/-- The EXACT original spatial usc supremum of actual stages over ALL
real terminal times T>s, on the original nonnegative time domain. -/
def sourceBoundedRayJoinFamily (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (ℓ k : SourceRayFamily M) : SourceRayFamily M :=
  fun s ↦ SGPT.PSH.uscSup (fun T : {T : ℝ // s.val < T} ↦
    sourceBoundedRayJoinStage omega θ φ ℓ k T.val s.val)

omit [ConnectedSpace M] in
/-- Actual source spatial regularization and the WHOLE original stage
family identify the same native join slice at EVERY original time. -/
theorem sourceBoundedRayJoinFamily_eq_native (omega : KahlerBackground n M)
    (ℓ k : SourceRayFamily M) (s : Ici (0 : ℝ)) :
    sourceBoundedRayJoinFamily omega θ φ ℓ k s =
      SingularBoundedRayJoinSlices.joinSlice (atlasClosedFormToNative θ) φ
        (sourceRayExtension ℓ) (sourceRayExtension k) s.val := by
  have hs : (0 : ℝ) ≤ s.val := s.property
  unfold sourceBoundedRayJoinFamily
  rw [sourceUscSup_eq_native]
  unfold SingularBoundedRayJoinSlices.joinSlice
  rw [max_eq_left hs]
  apply congrArg uscRegularization
  exact iSup_congr fun T ↦ sourceBoundedRayJoinStage_eq_native omega ℓ k T.val s.val

omit [ConnectedSpace M] in
/-- The WHOLE normalized real-time reader equals the native join; clipping
adds no source times and changes no original nonnegative-time potential. -/
theorem sourceBoundedRayJoinFamily_extension (omega : KahlerBackground n M)
    (ℓ k : SourceRayFamily M) :
    sourceRayExtension (sourceBoundedRayJoinFamily omega θ φ ℓ k) =
      SingularBoundedRayJoinSlices.joinSlice (atlasClosedFormToNative θ) φ
        (sourceRayExtension ℓ) (sourceRayExtension k) := by
  funext t
  change sourceBoundedRayJoinFamily omega θ φ ℓ k ⟨max t 0, le_max_right t 0⟩ = _
  rw [sourceBoundedRayJoinFamily_eq_native]
  let U : ℝ → M → EReal := fun r ↦ uscRegularization
    (⨆ T : {T : ℝ // r < T}, SingularBoundedRayJoinStages.joinStage
      (atlasClosedFormToNative θ) φ (sourceRayExtension ℓ) (sourceRayExtension k) T.val r)
  change U (max (max t 0) 0) = U (max t 0)
  exact congrArg U (by simp only [max_assoc, max_self])

/-- Genuine stage geometry, internally produced uniform bounds and actual
increasing-endpoint stability manufacture the ENTIRE original bounded-ray
contract, including every closed interval and the initial model. -/
theorem sourceBoundedRayJoinFamily_mem (omega : KahlerBackground n M)
    (L K : SourceBoundedGeodesicRay omega θ φ hφ) :
    sourceBoundedRayJoinFamily omega θ φ L.val K.val ∈ sourceBoundedRays omega θ φ hφ := by
  apply (mem_sourceBoundedRays_iff_native omega θ φ hφ _).mpr
  rw [sourceBoundedRayJoinFamily_extension]
  exact SingularBoundedRayJoinRay.isBoundedRayFromModel_joinSlice omega
    ((mem_sourceBoundedRays_iff_native omega θ φ hφ L.val).mp L.property)
    ((mem_sourceBoundedRays_iff_native omega θ φ hφ K.val).mp K.property)

/-- The actual original bounded join is constructed, not chosen from a
supplied class/leastness certificate. -/
def sourceBoundedRayJoin (omega : KahlerBackground n M)
    (L K : SourceBoundedGeodesicRay omega θ φ hφ) : SourceBoundedGeodesicRay omega θ φ hφ :=
  ⟨sourceBoundedRayJoinFamily omega θ φ L.val K.val, sourceBoundedRayJoinFamily_mem omega L K⟩

/-- EXACT printed definition: the bounded ray lies above both inputs and
below EVERY original bounded upper ray. Existence is proved below. -/
def SourceIsBoundedRayJoin (omega : KahlerBackground n M)
    (L K J : SourceBoundedGeodesicRay omega θ φ hφ) : Prop :=
  SourceRayLE L.val J.val ∧ SourceRayLE K.val J.val ∧
    ∀ H : SourceBoundedGeodesicRay omega θ φ hφ,
      SourceRayLE L.val H.val → SourceRayLE K.val H.val → SourceRayLE J.val H.val

/-- WHOLE original join existence/leastness: actual native endpoint
monotonicity and USC comparison prove the exact original definition. -/
theorem sourceBoundedRayJoin_isJoin (omega : KahlerBackground n M)
    (L K : SourceBoundedGeodesicRay omega θ φ hφ) :
    SourceIsBoundedRayJoin omega L K (sourceBoundedRayJoin omega L K) := by
  have hL := (mem_sourceBoundedRays_iff_native omega θ φ hφ L.val).mp L.property
  have hK := (mem_sourceBoundedRays_iff_native omega θ φ hφ K.val).mp K.property
  refine ⟨?_, ?_, ?_⟩
  · intro t x
    have h := SingularBoundedRayJoinSlices.max_le_joinSlice hL hK t.property x
    rw [← sourceBoundedRayJoinFamily_eq_native omega L.val K.val t] at h
    simpa only [sourceBoundedRayJoin, sourceRayExtension_nonneg L.val t.val t.property,
      sourceRayExtension_nonneg K.val t.val t.property] using (le_max_left _ _).trans h
  · intro t x
    have h := SingularBoundedRayJoinSlices.max_le_joinSlice hL hK t.property x
    rw [← sourceBoundedRayJoinFamily_eq_native omega L.val K.val t] at h
    simpa only [sourceBoundedRayJoin, sourceRayExtension_nonneg L.val t.val t.property,
      sourceRayExtension_nonneg K.val t.val t.property] using (le_max_right _ _).trans h
  · intro H hLH hKH t
    have hH := (mem_sourceBoundedRays_iff_native omega θ φ hφ H.val).mp H.property
    have h := SingularBoundedRayJoinSlices.joinSlice_le_upperRay ⟨hH.1.1, hH.2⟩
      ((sourceRayLE_iff_extension L.val H.val).mp hLH)
      ((sourceRayLE_iff_extension K.val H.val).mp hKH) t.property
    rw [← sourceBoundedRayJoinFamily_eq_native omega L.val K.val t,
      sourceRayExtension_nonneg H.val t.val t.property] at h
    exact h

omit [BorelSpace M] [ConnectedSpace M] in
/-- Minimality gives uniqueness of the literal original ray, at EVERY
point and time, without AE quotients or normalization. -/
theorem SourceIsBoundedRayJoin.unique {omega : KahlerBackground n M}
    {L K J H : SourceBoundedGeodesicRay omega θ φ hφ}
    (hJ : SourceIsBoundedRayJoin omega L K J) (hH : SourceIsBoundedRayJoin omega L K H) : J = H := by
  apply Subtype.ext
  exact le_antisymm (hJ.2.2 H hH.1 hH.2.1) (hH.2.2 J hJ.1 hJ.2.1)

/-- The actual original join retains the prescribed original initial
model even when that model is unbounded. -/
theorem sourceBoundedRayJoin_zero (omega : KahlerBackground n M)
    (L K : SourceBoundedGeodesicRay omega θ φ hφ) :
    (sourceBoundedRayJoin omega L K).val ⟨0, by simp⟩ = φ :=
  (sourceBoundedRayJoin omega L K).property.2

/-- The WHOLE original join-energy clause as actual unrestricted real
Tendsto, with literal ORIGINAL extended energy and literal LIMSUP radial
energy. Every finite-type/E1 energy used natively is produced internally. -/
theorem sourceBoundedRayJoin_radialEnergy_tendsto (omega : KahlerBackground n M)
    (L K : SourceBoundedGeodesicRay omega θ φ hφ) :
    Tendsto (fun T : ℝ => ((T⁻¹ : ℝ) : EReal) * sourceRelativeEnergy θ φ
      (fun x ↦ max (sourceRayExtension L.val T x) (sourceRayExtension K.val T x)) hφ) atTop
      (𝓝 (sourceRadialEnergy omega
        (sourceBoundedRayToGeodesicRay omega (sourceBoundedRayJoin omega L K)))) := by
  have hL := (mem_sourceBoundedRays_iff_native omega θ φ hφ L.val).mp L.property
  have hK := (mem_sourceBoundedRays_iff_native omega θ φ hφ K.val).mp K.property
  have hT := SingularBoundedRayJoinEnergy.tendsto_terminal_max_energy_div omega hL hK
  have he : sourceRadialEnergy omega
      (sourceBoundedRayToGeodesicRay omega (sourceBoundedRayJoin omega L K)) =
      RelativeDarvasDistance.energy (atlasClosedFormToNative θ) φ hφ.toNative
        (SingularBoundedRayJoinSlices.joinSlice (atlasClosedFormToNative θ) φ
          (sourceRayExtension L.val) (sourceRayExtension K.val) 1) := by
    rw [sourceRadialEnergy_eq_native]
    change RelativeGeodesicRays.radialEnergy (atlasClosedFormToNative θ) φ hφ.toNative
      (sourceRayExtension (sourceBoundedRayJoinFamily omega θ φ L.val K.val)) = _
    rw [sourceBoundedRayJoinFamily_extension]
    exact (SingularBoundedRayJoinEnergy.radialEnergy_joinSlice_eq_limUnder_terminal_max
      omega hL hK).trans hT.limUnder_eq
  rw [he]
  simpa only [sourceRelativeEnergy_eq_native] using hT

/-- The actual original limit formula follows from the just-produced
convergence, preserving the original full real terminal-time filter. -/
theorem sourceBoundedRayJoin_radialEnergy_eq_limUnder (omega : KahlerBackground n M)
    (L K : SourceBoundedGeodesicRay omega θ φ hφ) :
    sourceRadialEnergy omega (sourceBoundedRayToGeodesicRay omega (sourceBoundedRayJoin omega L K)) =
      Filter.limUnder atTop (fun T : ℝ => ((T⁻¹ : ℝ) : EReal) * sourceRelativeEnergy θ φ
        (fun x ↦ max (sourceRayExtension L.val T x) (sourceRayExtension K.val T x)) hφ) :=
  (sourceBoundedRayJoin_radialEnergy_tendsto omega L K).limUnder_eq.symm

/-- WHOLE original TWO-sided join distance estimate, with the EXACT
original dimensional constant 3(n+1)2^(n+2), on ALL original bounded rays.
Actual same-type inclusion manufactures the needed original R1 objects. -/
theorem sourceBoundedRayJoin_distance_bounds (omega : KahlerBackground n M)
    (L K : SourceBoundedGeodesicRay omega θ φ hφ) :
    sourceRadialDarvasDistance omega (sourceBoundedRayToFiniteEnergyRay omega L)
        (sourceBoundedRayToFiniteEnergyRay omega K) ≤
      sourceRadialDarvasDistance omega (sourceBoundedRayToFiniteEnergyRay omega L)
          (sourceBoundedRayToFiniteEnergyRay omega (sourceBoundedRayJoin omega L K)) +
        sourceRadialDarvasDistance omega (sourceBoundedRayToFiniteEnergyRay omega K)
          (sourceBoundedRayToFiniteEnergyRay omega (sourceBoundedRayJoin omega L K)) ∧
    sourceRadialDarvasDistance omega (sourceBoundedRayToFiniteEnergyRay omega L)
        (sourceBoundedRayToFiniteEnergyRay omega (sourceBoundedRayJoin omega L K)) +
      sourceRadialDarvasDistance omega (sourceBoundedRayToFiniteEnergyRay omega K)
        (sourceBoundedRayToFiniteEnergyRay omega (sourceBoundedRayJoin omega L K)) ≤
      (sourceIThetaComparisonConstant n : EReal) *
        sourceRadialDarvasDistance omega (sourceBoundedRayToFiniteEnergyRay omega L)
          (sourceBoundedRayToFiniteEnergyRay omega K) := by
  have hn := SingularBoundedRayJoinDistance.rayD1_join_two_sided omega
    ((mem_sourceBoundedRays_iff_native omega θ φ hφ L.val).mp L.property)
    ((mem_sourceBoundedRays_iff_native omega θ φ hφ K.val).mp K.property)
  simp only [sourceRadialDarvasDistance_eq_native, sourceBoundedRayToFiniteEnergyRay,
    sourceBoundedRayJoin, sourceBoundedRayJoinFamily_extension, sourceIThetaComparisonConstant]
  exact hn

end SGPT.PSH.VariableComplexAtlas
