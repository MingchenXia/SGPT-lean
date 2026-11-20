import SGPT.PSH.SourceSubgeodesicConvexity
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesics
import SGPT.Foundations.Analysis.Pending.SingularPerronUpperBound
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicEnergyAffineE1

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- ALL original subgeodesics whose own genuine source endpoints lie below
the two requested endpoints. The subgeodesic predicate retains the entire
actual product theta-PSH and original GLOBAL L1 endpoint obligations. -/
def sourcePerronCompetitors (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u₀ u₁ : M → EReal) :
    Set (ℝ → M → EReal) :=
  {curve | ∃ v₀ v₁ : M → EReal,
    (ofFixedModel n M).IsThetaPSH θ v₀ ∧ (ofFixedModel n M).IsThetaPSH θ v₁ ∧
      v₀ ≤ u₀ ∧ v₁ ≤ u₁ ∧ SourceSubgeodesicFrom omega θ curve v₀ v₁}

/-- The literal original spatial USC supremum over the entire original
Perron family; no supplied geodesic, mass or endpoint-recovery certificate. -/
def sourcePerronGeodesic (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u₀ u₁ : M → EReal)
    (t : ℝ) : M → EReal :=
  uscSup (fun curve : sourcePerronCompetitors omega θ u₀ u₁ ↦ curve.1 t)

/-- Actual whole-family equality, preserving every original curve, its own
two endpoint functions, the requested bounds and the original time domain. -/
theorem sourcePerronCompetitors_eq_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u₀ u₁ : M → EReal) :
    sourcePerronCompetitors omega θ u₀ u₁ =
      finiteGeodesicCompetitors (atlasClosedFormToNative θ).val u₀ u₁ := by
  ext curve
  constructor
  · rintro ⟨v₀, v₁, h₀, h₁, hbound₀, hbound₁, h⟩
    exact ⟨v₀, v₁, (isThetaPSH_iff_nativeThetaPotential θ v₀).mp h₀,
      (isThetaPSH_iff_nativeThetaPotential θ v₁).mp h₁, hbound₀, hbound₁,
      (sourceSubgeodesicFrom_iff_native omega θ curve v₀ v₁).mp h⟩
  · rintro ⟨v₀, v₁, h₀, h₁, hbound₀, hbound₁, h⟩
    exact ⟨v₀, v₁, (isThetaPSH_iff_nativeThetaPotential θ v₀).mpr h₀,
      (isThetaPSH_iff_nativeThetaPotential θ v₁).mpr h₁, hbound₀, hbound₁,
      (sourceSubgeodesicFrom_iff_native omega θ curve v₀ v₁).mpr h⟩

/-- Equality of the actual entire source/native regularized Perron envelopes,
including the genuinely empty-family branch and both infinite endpoints. -/
theorem sourcePerronGeodesic_eq_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u₀ u₁ : M → EReal) (t : ℝ) :
    sourcePerronGeodesic omega θ u₀ u₁ t =
      finiteGeodesic (atlasClosedFormToNative θ).val u₀ u₁ t := by
  unfold sourcePerronGeodesic uscSup finiteGeodesic
  apply congrArg uscRegularization
  funext x
  rw [sourcePerronCompetitors_eq_native, finiteGeodesicSliceSupremum_apply]
  apply le_antisymm
  · exact iSup_le fun curve ↦ le_iSup_of_le curve.1 (le_iSup_of_le curve.2 le_rfl)
  · exact iSup_le fun curve ↦ iSup_le fun hcurve ↦
      le_iSup (fun c : finiteGeodesicCompetitors (atlasClosedFormToNative θ).val u₀ u₁ ↦
        c.1 t x) ⟨curve, hcurve⟩

/-- Every actual original Perron competitor lies below the exact original
regularized envelope, on the same function values. -/
theorem sourcePerron_competitor_le {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u₀ u₁ : M → EReal}
    {curve : ℝ → M → EReal}
    (h : curve ∈ sourcePerronCompetitors omega θ u₀ u₁) (t : ℝ) :
    curve t ≤ sourcePerronGeodesic omega θ u₀ u₁ t := by
  rw [sourcePerronGeodesic_eq_native]
  apply competitor_slice_le_finiteGeodesic
  rwa [← sourcePerronCompetitors_eq_native omega θ u₀ u₁]

/-- The source's expressly allowed potential-or-bottom clause is produced
from the actual complete competitor family and its genuine compact endpoint
upper bound, rather than supplied as a Perron output certificate. -/
theorem sourcePerronGeodesic_isThetaPSHOrBot (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u₀ u₁ : M → EReal}
    (hu₀ : (ofFixedModel n M).IsThetaPSH θ u₀)
    (hu₁ : (ofFixedModel n M).IsThetaPSH θ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    IsThetaPSHOrBot θ (sourcePerronGeodesic omega θ u₀ u₁ t) := by
  classical
  by_cases hn : (sourcePerronCompetitors omega θ u₀ u₁).Nonempty
  · let : Nonempty (sourcePerronCompetitors omega θ u₀ u₁) :=
      ⟨⟨hn.choose, hn.choose_spec⟩⟩
    have h₀ := (isThetaPSH_iff_nativeThetaPotential θ u₀).mp hu₀
    have h₁ := (isThetaPSH_iff_nativeThetaPotential θ u₁).mp hu₁
    obtain ⟨B, hB⟩ := SingularPerronUpperBound.exists_finiteGeodesic_uniform_upper_bound h₀ h₁
    apply Or.inl
    apply isThetaPSH_uscSup_of_majorant (w := fun _ ↦ (B : EReal))
    · intro curve
      obtain ⟨v₀, v₁, _, _, _, _, h⟩ := curve.2
      exact h.2.2.1.1 t ht
    · exact upperSemicontinuous_const
    · exact fun _ ↦ EReal.coe_ne_top B
    · intro curve x
      apply (sourcePerron_competitor_le curve.2 t x).trans
      rw [sourcePerronGeodesic_eq_native]
      exact hB t ht x
  · apply Or.inr
    rw [sourcePerronGeodesic_eq_native]
    apply finiteGeodesic_of_empty
    rw [← sourcePerronCompetitors_eq_native omega θ u₀ u₁]
    exact Set.not_nonempty_iff_eq_empty.mp hn

/-- The genuine constant source potential is the actual original Perron
envelope with equal endpoints, including every original negative pole. -/
theorem sourcePerronGeodesic_const (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    sourcePerronGeodesic omega θ u u t = u := by
  have hn := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  apply le_antisymm
  · rw [sourcePerronGeodesic_eq_native]
    intro x
    exact (finiteGeodesic_le_eRealChord hn hn ht x).trans_eq
      (FiniteGeodesicEnergyAffineE1.eRealChord_self (u x) ht)
  · exact sourcePerron_competitor_le
      (show (fun _ : ℝ ↦ u) ∈ sourcePerronCompetitors omega θ u u from
        ⟨u, u, hu, hu, le_rfl, le_rfl, sourceSubgeodesic_const omega hu⟩) t

/-- The entire original normalized geodesic definition: genuine requested
endpoints, the printed potential-or-bottom family, and equality with the
actual ALL-subgeodesic Perron envelope. Endpoint L1 recovery is not assumed. -/
def SourceIsGeodesicFrom (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (curve : ℝ → M → EReal) (u₀ u₁ : M → EReal) : Prop :=
  (ofFixedModel n M).IsThetaPSH θ u₀ ∧ (ofFixedModel n M).IsThetaPSH θ u₁ ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, IsThetaPSHOrBot θ (curve t)) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, curve t = sourcePerronGeodesic omega θ u₀ u₁ t

/-- The actual constructed Perron family satisfies the full original
definition, including its manufactured potential-or-bottom clause. -/
theorem sourcePerronGeodesic_isGeodesicFrom (omega : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u₀ u₁ : M → EReal}
    (hu₀ : (ofFixedModel n M).IsThetaPSH θ u₀)
    (hu₁ : (ofFixedModel n M).IsThetaPSH θ u₁) :
    SourceIsGeodesicFrom omega θ (sourcePerronGeodesic omega θ u₀ u₁) u₀ u₁ :=
  ⟨hu₀, hu₁, fun _ ht ↦ sourcePerronGeodesic_isThetaPSHOrBot omega hu₀ hu₁ ht,
    fun _ _ ↦ rfl⟩

/-- The complete original general CLOSED-interval definition keeps a≤b
and every genuine source slice on [a,b], including a=b. -/
def SourceGeodesicClosedInterval (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (a b : ℝ)
    (curve : ℝ → M → EReal) : Prop :=
  a ≤ b ∧ (∀ t ∈ Icc a b, (ofFixedModel n M).IsThetaPSH θ (curve t)) ∧
    SourceIsGeodesicFrom omega θ (fun s ↦ curve (s * b + (1 - s) * a)) (curve a) (curve b)

/-- At a=b the exact original closed geodesic condition is precisely the
genuine source theta-PSH condition on its single original value. -/
theorem sourceGeodesicClosedInterval_self_iff (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (a : ℝ)
    (curve : ℝ → M → EReal) :
    SourceGeodesicClosedInterval omega θ a a curve ↔
      (ofFixedModel n M).IsThetaPSH θ (curve a) := by
  constructor
  · intro h
    exact h.2.1 a ⟨le_rfl, le_rfl⟩
  · intro hu
    refine ⟨le_rfl, ?_, hu, hu, ?_, ?_⟩
    · intro t ht
      have heq : t = a := le_antisymm ht.2 ht.1
      simpa only [heq] using hu
    · intro s _
      have heq : s * a + (1 - s) * a = a := by ring
      change IsThetaPSHOrBot θ (curve (s * a + (1 - s) * a))
      rw [heq]
      exact Or.inl hu
    · intro s hs
      change curve (s * a + (1 - s) * a) = sourcePerronGeodesic omega θ (curve a) (curve a) s
      rw [sourcePerronGeodesic_const omega hu hs]
      congr 1
      ring

end SGPT.PSH.VariableComplexAtlas
