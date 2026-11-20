import SGPT.Foundations.Analysis.FirstPass.Subgeodesics
import SGPT.Foundations.Analysis.FirstPass.Envelopes

/-!
# Perron finite geodesics

This file implements Definition 4.2.1 of Xia's SGPT notes.  The endpoints are
arbitrary genuine theta-PSH potentials.  A Perron competitor is a genuine
subgeodesic whose own `L¹` endpoints lie below the requested endpoints.  The
slice supremum is then upper-semicontinuously regularized in the spatial
variable.

The definition does not assume that the envelope has the requested endpoint
limits or is itself theta-PSH.  Those are later analytic theorems, and in the
source they first hold for endpoints in the relative full-mass class.
-/

open Set

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Curves admitted in the Perron construction from requested upper endpoint
bounds `u₀,u₁`.  The actual `L¹` endpoints `v₀,v₁` of a competitor may be
strictly smaller than the requested bounds. -/
def finiteGeodesicCompetitors (θ : SmoothRealForm n M 2)
    (u₀ u₁ : M → EReal) : Set (ℝ → M → EReal) :=
  {curve | ∃ v₀ v₁ : M → EReal,
    IsThetaPshPotential θ v₀ ∧
    IsThetaPshPotential θ v₁ ∧
    v₀ ≤ u₀ ∧ v₁ ≤ u₁ ∧
    IsSubgeodesicFrom θ curve v₀ v₁}

theorem IsSubgeodesicFrom.mem_finiteGeodesicCompetitors
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    curve ∈ finiteGeodesicCompetitors θ u₀ u₁ :=
  ⟨u₀, u₁, h.left_endpoint, h.right_endpoint, le_rfl, le_rfl, h⟩

/-- Reversing time sends every Perron competitor to a competitor for the
oppositely ordered endpoints. -/
theorem timeReversedCurve_mem_finiteGeodesicCompetitors
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal}
    (hcurve : curve ∈ finiteGeodesicCompetitors θ u₀ u₁) :
    timeReversedCurve curve ∈ finiteGeodesicCompetitors θ u₁ u₀ := by
  rcases hcurve with ⟨v₀, v₁, hv₀, hv₁, hv₀u₀, hv₁u₁, hcurve⟩
  exact ⟨v₁, v₀, hv₁, hv₀, hv₁u₁, hv₀u₀, hcurve.timeReversed⟩

theorem timeReversedCurve_mem_finiteGeodesicCompetitors_iff
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} :
    timeReversedCurve curve ∈ finiteGeodesicCompetitors θ u₁ u₀ ↔
      curve ∈ finiteGeodesicCompetitors θ u₀ u₁ := by
  constructor
  · intro hcurve
    have h := timeReversedCurve_mem_finiteGeodesicCompetitors hcurve
    simpa using h
  · exact timeReversedCurve_mem_finiteGeodesicCompetitors

theorem finiteGeodesicCompetitors_nonempty_of_isSubgeodesicFrom
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    {u₀ u₁ : M → EReal} (h : IsSubgeodesicFrom θ curve u₀ u₁) :
    (finiteGeodesicCompetitors θ u₀ u₁).Nonempty :=
  ⟨curve, h.mem_finiteGeodesicCompetitors⟩

/-- The actual set of spatial slices occurring at time `t` among Perron
competitors. -/
def finiteGeodesicSlices (θ : SmoothRealForm n M 2) (u₀ u₁ : M → EReal)
    (t : ℝ) : Set (M → EReal) :=
  {v | ∃ curve ∈ finiteGeodesicCompetitors θ u₀ u₁, v = curve t}

/-- Pointwise supremum of all Perron slices before spatial USC
regularization.  If there are no competitors, this is the constant `⊥`
function. -/
def finiteGeodesicSliceSupremum (θ : SmoothRealForm n M 2)
    (u₀ u₁ : M → EReal) (t : ℝ) : M → EReal :=
  sSup (finiteGeodesicSlices θ u₀ u₁ t)

/-- The Perron finite geodesic slice `sup*` from SGPT (4.5). -/
def finiteGeodesic (θ : SmoothRealForm n M 2) (u₀ u₁ : M → EReal)
    (t : ℝ) : M → EReal :=
  uscRegularization (finiteGeodesicSliceSupremum θ u₀ u₁ t)

theorem finiteGeodesicSliceSupremum_apply (θ : SmoothRealForm n M 2)
    (u₀ u₁ : M → EReal) (t : ℝ) (x : M) :
    finiteGeodesicSliceSupremum θ u₀ u₁ t x =
      ⨆ curve ∈ finiteGeodesicCompetitors θ u₀ u₁, curve t x := by
  simp only [finiteGeodesicSliceSupremum, finiteGeodesicSlices, sSup_apply,
    iSup_subtype, mem_ofPred_eq]
  apply le_antisymm
  · apply iSup_le
    rintro v
    apply iSup_le
    rintro ⟨curve, hcurve, rfl⟩
    exact le_iSup_of_le curve (le_iSup_of_le hcurve le_rfl)
  · apply iSup_le
    intro curve
    apply iSup_le
    intro hcurve
    exact le_iSup_of_le (curve t) (le_iSup_of_le ⟨curve, hcurve, rfl⟩ le_rfl)

/-- The raw Perron slice supremum is equivariant under time reversal. -/
theorem finiteGeodesicSliceSupremum_timeReversal
    (θ : SmoothRealForm n M 2) (u₀ u₁ : M → EReal) (t : ℝ) :
    finiteGeodesicSliceSupremum θ u₁ u₀ t =
      finiteGeodesicSliceSupremum θ u₀ u₁ (1 - t) := by
  funext x
  rw [finiteGeodesicSliceSupremum_apply,
    finiteGeodesicSliceSupremum_apply]
  apply le_antisymm
  · apply iSup_le
    intro curve
    apply iSup_le
    intro hcurve
    exact le_iSup_of_le (timeReversedCurve curve)
      (le_iSup_of_le
        (timeReversedCurve_mem_finiteGeodesicCompetitors hcurve) (by
          simp [timeReversedCurve]))
  · apply iSup_le
    intro curve
    apply iSup_le
    intro hcurve
    exact le_iSup_of_le (timeReversedCurve curve)
      (le_iSup_of_le
        (timeReversedCurve_mem_finiteGeodesicCompetitors hcurve) (by
          simp [timeReversedCurve]))

/-- Perron finite geodesics are symmetric after reversing normalized time. -/
theorem finiteGeodesic_timeReversal
    (θ : SmoothRealForm n M 2) (u₀ u₁ : M → EReal) (t : ℝ) :
    finiteGeodesic θ u₁ u₀ t = finiteGeodesic θ u₀ u₁ (1 - t) := by
  unfold finiteGeodesic
  rw [finiteGeodesicSliceSupremum_timeReversal]

theorem finiteGeodesicSliceSupremum_le (θ : SmoothRealForm n M 2)
    (u₀ u₁ : M → EReal) (t : ℝ) :
    finiteGeodesicSliceSupremum θ u₀ u₁ t ≤ finiteGeodesic θ u₀ u₁ t :=
  le_uscRegularization _

theorem competitor_slice_le_finiteGeodesicSliceSupremum
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    {curve : ℝ → M → EReal}
    (hcurve : curve ∈ finiteGeodesicCompetitors θ u₀ u₁) (t : ℝ) :
    curve t ≤ finiteGeodesicSliceSupremum θ u₀ u₁ t :=
  le_sSup ⟨curve, hcurve, rfl⟩

theorem competitor_slice_le_finiteGeodesic
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    {curve : ℝ → M → EReal}
    (hcurve : curve ∈ finiteGeodesicCompetitors θ u₀ u₁) (t : ℝ) :
    curve t ≤ finiteGeodesic θ u₀ u₁ t :=
  (competitor_slice_le_finiteGeodesicSliceSupremum hcurve t).trans
  (finiteGeodesicSliceSupremum_le θ u₀ u₁ t)

theorem subgeodesic_slice_le_finiteGeodesic
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    {curve : ℝ → M → EReal}
    (hcurve : IsSubgeodesicFrom θ curve u₀ u₁) (t : ℝ) :
    curve t ≤ finiteGeodesic θ u₀ u₁ t :=
  competitor_slice_le_finiteGeodesic
    hcurve.mem_finiteGeodesicCompetitors t

/-- Any theta-PSH potential lying below both endpoints gives a constant
Perron competitor, hence a pointwise lower bound for every geodesic slice. -/
theorem le_finiteGeodesic_of_le_endpoints
    {θ : SmoothRealForm n M 2} {u₀ u₁ w : M → EReal}
    (hw : IsThetaPshPotential θ w) (hw₀ : w ≤ u₀) (hw₁ : w ≤ u₁)
    (t : ℝ) :
    w ≤ finiteGeodesic θ u₀ u₁ t := by
  have h := competitor_slice_le_finiteGeodesic
    (curve := fun _ : ℝ => w)
    (show (fun _ : ℝ => w) ∈ finiteGeodesicCompetitors θ u₀ u₁ from
      ⟨w, w, hw, hw, hw₀, hw₁, isSubgeodesicFrom_const hw⟩) t
  simpa using h

theorem upperSemicontinuous_finiteGeodesic (θ : SmoothRealForm n M 2)
    (u₀ u₁ : M → EReal) (t : ℝ) :
    UpperSemicontinuous (finiteGeodesic θ u₀ u₁ t) :=
  upperSemicontinuous_uscRegularization _

theorem finiteGeodesic_le_iff {θ : SmoothRealForm n M 2}
    {u₀ u₁ g : M → EReal} {t : ℝ} (hg : UpperSemicontinuous g) :
    finiteGeodesic θ u₀ u₁ t ≤ g ↔
      ∀ curve ∈ finiteGeodesicCompetitors θ u₀ u₁, curve t ≤ g := by
  rw [finiteGeodesic, uscRegularization_le_iff hg]
  constructor
  · intro h curve hcurve
    exact (competitor_slice_le_finiteGeodesicSliceSupremum hcurve t).trans h
  · intro h
    apply sSup_le
    rintro v ⟨curve, hcurve, rfl⟩
    exact h curve hcurve

theorem finiteGeodesicCompetitors_mono {θ : SmoothRealForm n M 2}
    {u₀ u₁ v₀ v₁ : M → EReal} (h₀ : u₀ ≤ v₀) (h₁ : u₁ ≤ v₁) :
    finiteGeodesicCompetitors θ u₀ u₁ ⊆
      finiteGeodesicCompetitors θ v₀ v₁ := by
  rintro curve ⟨w₀, w₁, hw₀, hw₁, hwu₀, hwu₁, hcurve⟩
  exact ⟨w₀, w₁, hw₀, hw₁, hwu₀.trans h₀, hwu₁.trans h₁, hcurve⟩

theorem finiteGeodesicSliceSupremum_mono {θ : SmoothRealForm n M 2}
    {u₀ u₁ v₀ v₁ : M → EReal} (h₀ : u₀ ≤ v₀) (h₁ : u₁ ≤ v₁)
    (t : ℝ) :
    finiteGeodesicSliceSupremum θ u₀ u₁ t ≤
      finiteGeodesicSliceSupremum θ v₀ v₁ t :=
  sSup_le_sSup fun _ ⟨curve, hcurve, hv⟩ =>
    ⟨curve, finiteGeodesicCompetitors_mono h₀ h₁ hcurve, hv⟩

theorem finiteGeodesic_mono {θ : SmoothRealForm n M 2}
    {u₀ u₁ v₀ v₁ : M → EReal} (h₀ : u₀ ≤ v₀) (h₁ : u₁ ≤ v₁)
    (t : ℝ) : finiteGeodesic θ u₀ u₁ t ≤ finiteGeodesic θ v₀ v₁ t :=
  uscRegularization_mono (finiteGeodesicSliceSupremum_mono h₀ h₁ t)

theorem finiteGeodesicSliceSupremum_of_empty
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal} {t : ℝ}
    (h : finiteGeodesicCompetitors θ u₀ u₁ = ∅) :
    finiteGeodesicSliceSupremum θ u₀ u₁ t = ⊥ := by
  have hs : finiteGeodesicSlices θ u₀ u₁ t = ∅ := by
    ext v
    simp [finiteGeodesicSlices, h]
  simp [finiteGeodesicSliceSupremum, hs]

theorem finiteGeodesic_of_empty {θ : SmoothRealForm n M 2}
    {u₀ u₁ : M → EReal} {t : ℝ}
    (h : finiteGeodesicCompetitors θ u₀ u₁ = ∅) :
    finiteGeodesic θ u₀ u₁ t = ⊥ := by
  unfold finiteGeodesic
  rw [finiteGeodesicSliceSupremum_of_empty h]
  exact uscRegularization_const ⊥

end

end SGPT.Foundations.Analysis.FirstPass
