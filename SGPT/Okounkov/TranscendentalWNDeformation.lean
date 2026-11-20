import SGPT.Okounkov.TranscendentalWNDeformationCentre
import SGPT.Foundations.Analysis.Pending.BlowupExistence
import SGPT.Foundations.Analysis.Pending.BlowupKahler
import SGPT.Foundations.Analysis.Pending.BlowupConnected
import SGPT.Foundations.Analysis.Pending.BlowupCompact
import SGPT.Foundations.Analysis.Pending.BlowupIsomorphismOff
import SGPT.Foundations.Analysis.Pending.BlowupExistenceCodimOne
import SGPT.Foundations.Analysis.Pending.BlowupSNCTransform
import SGPT.Foundations.Analysis.Pending.SNCGlobalPrimeComponents
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra

/-!
# The deformation of `X` to the normal cone of `Y₁`: existence and geometry

Blueprint `tok-wn:deformation` (chapter `claude-tok-wn`), sub-lemmas `tok-wn-def:*` of
`claude-tok-wn-def`; WN21 §1.1 and the beginning of §4.

For the flag geometry `F` (`X` compact Kähler of dimension `m + 1`, `Z = Y₁`):

* `deformationExists` (`DeformationExistsStatement`): the blow-up `μ : 𝒳 → X × ℙ¹` along
  `Z × {0}` exists (TN's construction `BlowupConstruction.blowupProj`, since `Z × {0}` is a
  nowhere dense closed submanifold, `TranscendentalWNDeformationCentre`).

For every deformation `μ` (`IsNormalConeDeformation F μ`):

* `compactSpace_normalCone`, `connectedSpace_normalCone`, `nonempty_kahler_normalCone`: `𝒳` is a
  compact connected Kähler manifold (Blanchard; `X × ℙ¹` carries the product Kähler form
  `p₁^*ω + p₂^*ω_FS`);
* `isIsomorphismOver_normalCone`: `μ` is an isomorphism over the complement of `Z × {0}`;
* `exists_fibreSection`: for `τ ≠ 0` the fibre `X_τ` is the image of the holomorphic section
  `x ↦ μ⁻¹(x, τ)`;
* `pullback_vanishingIdeal_centre_zeroSection`: the ideal of `Z × {0}` pulls back along
  `x ↦ (x, 0)` to the ideal of the smooth hypersurface `Z`, which is invertible; hence
  `exists_centralSection`: `x ↦ (x, 0)` lifts (uniquely) to a holomorphic `ι' : X → 𝒳` whose
  image is the strict transform `X'` and with `ι'⁻¹(ℰ) = Z`;
* `centralFibre_eq_union`: `X₀ = X' ∪ ℰ`;
* `regularAtDim_strictCentralFibre`, `regularAtDim_exceptionalSet`: `X'` and `ℰ` are closed
  submanifolds of dimension `m + 1`;
* `deformationGeometry` (`DeformationGeometryStatement`): all of the above.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-! ### Existence -/

/-- **`tok-wn:deformation`, existence**: the blow-up of `X × ℙ¹` along `Z × {0}` exists. -/
theorem deformationExists : DeformationExistsStatement F :=
  BlowupExistence.exists_isBlowupAlong (deformationCentre F)
    (isClosedSubmanifold_deformationCentre F) (interior_deformationCentre F)

/-- The product Kähler form `p₁^*ω + p₂^*ω_FS` on `X × ℙ¹`. -/
def deformationBaseKahler : KahlerBackground (m + 1 + 1) (F.carrier × ProjectiveLine) :=
  prodKahlerBackground F.omega SGPT.Toric.projectiveNativeFSBackground

/-! ### The section `x ↦ (x, 0)` and the ideal of the centre -/

/-- The holomorphic map `x ↦ (x, τ)`, `X → X × ℙ¹`. -/
theorem contMDiff_slice (p : ProjectiveLine) :
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
      (fun x : F.carrier => (x, p)) :=
  contMDiff_prodMk contMDiff_id contMDiff_const

/-- **The ideal of `Z × {0}` restricts to the ideal of `Z`**: along `x ↦ (x, 0)`, the ideal
`𝓘_{Z × {0}}` pulls back to `𝓘_Z` (germwise).  Indeed `(x, 0) ∈ Z × {0} ⟺ x ∈ Z`, and every germ
`f ∈ 𝓘_Z` is the pullback of `f ∘ π_X ∈ 𝓘_{Z × {0}}`. -/
theorem pullback_vanishingIdeal_centre_zeroSection :
    GermIdeal.pullback (m := m + 1) (fun x : F.carrier => (x, projectiveZero))
        (vanishingIdeal (n := m + 1 + 1) (deformationCentre F)) =
      vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))) := by
  set g : F.carrier → F.carrier × ProjectiveLine := fun x => (x, projectiveZero) with hg
  have hgC : ∀ x, g x ∈ deformationCentre F ↔ x ∈ F.flag (1 : Fin (m + 2)) := by
    intro x
    simp [hg, mem_deformationCentre_iff]
  have hgc : Continuous g := continuous_id.prodMk continuous_const
  ext x f
  constructor
  · rintro ⟨hf, N, s, a, hs, -, hsum⟩
    refine ⟨hf, ?_⟩
    have hvan : ∀ i, ∀ᶠ y in 𝓝 x, y ∈ F.flag (1 : Fin (m + 2)) → s i y = 0 := by
      intro i
      obtain ⟨b, ⟨-, hb⟩, hsb⟩ := hs i
      have := hgc.continuousAt.eventually hb
      filter_upwards [this] with y hy hyZ
      rw [hsb]
      exact hy ((hgC y).mpr hyZ)
    have hall : ∀ᶠ y in 𝓝 x, ∀ i, y ∈ F.flag (1 : Fin (m + 2)) → s i y = 0 :=
      Filter.eventually_all.mpr hvan
    filter_upwards [hall, hsum] with y hy hyf hyZ
    rw [hyf]
    exact Finset.sum_eq_zero fun i _ => by rw [hy i hyZ, mul_zero]
  · rintro ⟨hf, hfZ⟩
    refine ⟨hf, 1, fun _ => f, fun _ => fun _ => 1, fun _ => ⟨fun q => f q.1, ⟨?_, ?_⟩, rfl⟩,
      fun _ => holomorphicAt_const 1, ?_⟩
    · have hf' : HolomorphicAt (m + 1) f (Prod.fst (g x)) := hf
      exact HolomorphicAt.comp_contMDiff (f := Prod.fst) hf'
        (Eventually.of_forall fun _ => contMDiff_fst.contMDiffAt)
    · have h1 : Tendsto Prod.fst (𝓝 (g x)) (𝓝 x) := continuous_fst.continuousAt.tendsto
      filter_upwards [h1.eventually hfZ] with q hq hqC
      exact hq ((mem_deformationCentre_iff F).mp hqC).1
    · exact Eventually.of_forall fun y => by simp

/-- The ideal of `Z` is invertible (`Z` is a smooth hypersurface with empty interior). -/
theorem isInvertible_vanishingIdeal_firstFlag :
    (vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))).IsInvertible :=
  BlowupExistenceCodimOne.isInvertible_vanishingIdeal_of_codimOne F.firstDivisor.1
    (interior_firstFlag F) fun x hx => ⟨m, F.firstDivisor.2.2 x hx, rfl⟩

/-! ### Properties of an arbitrary deformation to the normal cone -/

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
variable {F} in
theorem IsNormalConeDeformation.contMDiff (hμ : IsNormalConeDeformation F μ) :
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ μ :=
  BlowupSequences.IsBlowupAlong.contMDiff hμ

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
variable {F} in
theorem IsNormalConeDeformation.continuous (hμ : IsNormalConeDeformation F μ) : Continuous μ :=
  hμ.contMDiff.continuous

/-- `𝒳` is compact. -/
theorem compactSpace_normalCone (hμ : IsNormalConeDeformation F μ) : CompactSpace 𝒳 :=
  BlowupCompact.compactSpace_of_isBlowupAlong hμ

/-- `𝒳` is connected. -/
theorem connectedSpace_normalCone (hμ : IsNormalConeDeformation F μ) : ConnectedSpace 𝒳 :=
  BlowupConnected.connectedSpace_of_isBlowupAlong hμ

/-- `𝒳` is Kähler (Blanchard). -/
theorem nonempty_kahler_normalCone (hμ : IsNormalConeDeformation F μ) :
    Nonempty (KahlerBackground (m + 1 + 1) 𝒳) :=
  (BlowupKahler.compactSpace_and_kahler_of_isBlowupAlong ⟨deformationBaseKahler F⟩ hμ).2

/-- `μ` is an isomorphism over the complement of `Z × {0}`. -/
theorem isIsomorphismOver_normalCone (hμ : IsNormalConeDeformation F μ) :
    IsIsomorphismOver (m + 1 + 1) μ (deformationCentre F)ᶜ :=
  BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hμ

/-- Two points of `𝒳` off `ℰ` with the same image are equal. -/
theorem eq_of_map_eq_of_notMem (hμ : IsNormalConeDeformation F μ) {z z' : 𝒳}
    (hz : μ z ∉ deformationCentre F) (h : μ z = μ z') : z = z' :=
  (isIsomorphismOver_normalCone F hμ).1.injOn hz (show μ z' ∈ (deformationCentre F)ᶜ from h ▸ hz) h

/-- **The fibres `X_τ`, `τ ≠ 0`, are copies of `X`**: the inclusion `x ↦ (x, τ)` lifts to a
holomorphic section `s` of `μ` with image `X_τ`. -/
theorem exists_fibreSection (hμ : IsNormalConeDeformation F μ) {p : ProjectiveLine}
    (hp : p ≠ projectiveZero) : ∃ s : F.carrier → 𝒳,
      ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ s ∧
        (∀ x, μ (s x) = (x, p)) ∧ range s = fibreAt F μ p := by
  have hnot : ∀ x : F.carrier, (x, p) ∉ deformationCentre F := fun x h =>
    hp ((mem_deformationCentre_iff F).mp h).2
  obtain ⟨s, ⟨hs, hμs⟩, -⟩ := hμ.2.2.2.2 (m + 1) F.carrier (fun x => (x, p))
    (contMDiff_slice F p)
    (isInvertible_pullback_vanishingIdeal_of_disjoint
      (isClosed_deformationCentre F) hnot)
  have hμs' : ∀ x, μ (s x) = (x, p) := fun x => congrFun hμs x
  refine ⟨s, hs, hμs', ?_⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    simp [fibreAt, hμs']
  · intro hz
    have hz' : (μ z).2 = p := by simpa [fibreAt] using hz
    refine ⟨(μ z).1, ?_⟩
    have hzC : μ (s (μ z).1) ∉ deformationCentre F := by rw [hμs']; exact hnot _
    refine eq_of_map_eq_of_notMem F hμ hzC ?_
    rw [hμs', ← hz']

/-- **The strict transform `X'` is a copy of `X`**: the map `x ↦ (x, 0)` lifts to a holomorphic
`ι' : X → 𝒳` (its pullback of `𝓘_{Z × {0}}` is the invertible ideal of `Z`), whose image is
`X'` and with `ι'⁻¹(ℰ) = Z`. -/
theorem exists_centralSection (hμ : IsNormalConeDeformation F μ) : ∃ ι : F.carrier → 𝒳,
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ι ∧
      (∀ x, μ (ι x) = (x, projectiveZero)) ∧ range ι = strictCentralFibre F μ ∧
      ι ⁻¹' exceptionalSet F μ = F.flag (1 : Fin (m + 2)) := by
  have hinv : (GermIdeal.pullback (m := m + 1) (fun x : F.carrier => (x, projectiveZero))
      (vanishingIdeal (n := m + 1 + 1) (deformationCentre F))).IsInvertible := by
    rw [pullback_vanishingIdeal_centre_zeroSection F]
    exact isInvertible_vanishingIdeal_firstFlag F
  obtain ⟨ι, ⟨hι, hμι⟩, -⟩ := hμ.2.2.2.2 (m + 1) F.carrier (fun x => (x, projectiveZero))
    (contMDiff_slice F projectiveZero) hinv
  have hμι' : ∀ x, μ (ι x) = (x, projectiveZero) := fun x => congrFun hμι x
  have hιC : ∀ x, ι x ∈ exceptionalSet F μ ↔ x ∈ F.flag (1 : Fin (m + 2)) := by
    intro x
    simp [exceptionalSet, hμι', mem_deformationCentre_iff]
  refine ⟨ι, hι, hμι', ?_, Set.ext hιC⟩
  have hoff : ∀ x, x ∉ F.flag (1 : Fin (m + 2)) →
      ι x ∈ μ ⁻¹' (centralBase F \ deformationCentre F) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · simp [hμι', mem_centralBase_iff]
    · simpa [hμι', mem_deformationCentre_iff] using hx
  apply le_antisymm
  · -- `ι(X) ⊆ X'`: `X \ Z` is dense in `X`
    rintro _ ⟨x, rfl⟩
    have hdense : Dense (F.flag (1 : Fin (m + 2)))ᶜ := by
      rw [dense_iff_closure_eq, closure_compl, interior_firstFlag F, compl_empty]
    have hcl : x ∈ closure (F.flag (1 : Fin (m + 2)))ᶜ := hdense.closure_eq ▸ mem_univ x
    have himg : ι x ∈ closure (ι '' (F.flag (1 : Fin (m + 2)))ᶜ) :=
      mem_closure_image hι.continuous.continuousAt hcl
    refine closure_mono ?_ himg
    rintro _ ⟨y, hy, rfl⟩
    exact hoff y hy
  · -- `X' ⊆ ι(X)`: `μ⁻¹(X × {0} \ Z × {0}) ⊆ ι(X)`, and `ι(X)` is compact
    have hcompact : IsCompact (range ι) := isCompact_range hι.continuous
    refine closure_minimal ?_ hcompact.isClosed
    intro z hz
    refine ⟨(μ z).1, ?_⟩
    have hz0 : (μ z).2 = projectiveZero := (mem_centralBase_iff F).mp hz.1
    have hzC : μ (ι (μ z).1) ∉ deformationCentre F := by
      rw [hμι']
      intro h
      apply hz.2
      rw [mem_deformationCentre_iff] at h ⊢
      exact ⟨h.1, hz0⟩
    refine eq_of_map_eq_of_notMem F hμ hzC ?_
    rw [hμι', ← hz0]

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- **`X₀ = X' ∪ ℰ`**. -/
theorem centralFibre_eq_union (hμ : IsNormalConeDeformation F μ) :
    centralFibre F μ = strictCentralFibre F μ ∪ exceptionalSet F μ := by
  apply le_antisymm
  · intro z hz
    by_cases hzC : μ z ∈ deformationCentre F
    · exact Or.inr hzC
    · exact Or.inl (subset_closure ⟨hz, hzC⟩)
  · rintro z (hz | hz)
    · exact BlowupStrictSubmanifold.geoStrictTransform_subset_preimage hμ.continuous
        (isClosed_centralBase F) hz
    · exact deformationCentre_subset_centralBase F hz

omit [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳] [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- `X'` is closed. -/
theorem isClosed_strictCentralFibre : IsClosed (strictCentralFibre F μ) := isClosed_closure

/-- **`X'` is a submanifold of dimension `m + 1`** (TN: the strict transform of a submanifold
through the centre is a submanifold of the same dimension). -/
theorem regularAtDim_strictCentralFibre (hμ : IsNormalConeDeformation F μ) {z : 𝒳}
    (hz : z ∈ strictCentralFibre F μ) :
    RegularAtDim (n := m + 1 + 1) (strictCentralFibre F μ) z (m + 1) :=
  BlowupStrictSubmanifold.regularAtDim_geoStrictTransform hμ (isClosed_centralBase F)
    (fun _ hq => regularAtDim_centralBase F hq) (deformationCentre_subset_centralBase F) hz

omit [IsComplexManifold (m + 1 + 1) 𝒳] in
/-- `ℰ` is closed. -/
theorem isClosed_exceptionalSet (hμ : IsNormalConeDeformation F μ) :
    IsClosed (exceptionalSet F μ) :=
  (isClosed_deformationCentre F).preimage hμ.continuous

/-- **`ℰ` is a smooth hypersurface** (TN: the exceptional divisor `[π⁻¹ C]` is a simple normal
crossings divisor). -/
theorem regularAtDim_exceptionalSet (hμ : IsNormalConeDeformation F μ) {z : 𝒳}
    (hz : z ∈ exceptionalSet F μ) :
    RegularAtDim (n := m + 1 + 1) (exceptionalSet F μ) z (m + 1) :=
  SNCGlobalPrimeComponents.regularAtDim_member (BlowupSNCTransform.isSNCDivisor_preimage_centre hμ)
    ⟨0, by simp⟩ hz

end Deformation

/-! ### The geometry statement -/

/-- **`tok-wn:deformation`, geometry** (`DeformationGeometryStatement`). -/
theorem deformationGeometry : DeformationGeometryStatement F := by
  intro 𝒳 _ _ _ μ hμ
  exact ⟨⟨compactSpace_normalCone F hμ, connectedSpace_normalCone F hμ,
      nonempty_kahler_normalCone F hμ⟩,
    isIsomorphismOver_normalCone F hμ,
    fun _ hp => exists_fibreSection F hμ hp,
    exists_centralSection F hμ,
    centralFibre_eq_union F hμ,
    ⟨isClosed_strictCentralFibre F, fun _ hz => regularAtDim_strictCentralFibre F hμ hz⟩,
    ⟨isClosed_exceptionalSet F hμ, fun _ hz => regularAtDim_exceptionalSet F hμ hz⟩⟩

end SGPT.Okounkov.TranscendentalWN
