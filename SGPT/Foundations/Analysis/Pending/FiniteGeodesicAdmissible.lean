import SGPT.Foundations.Analysis.Pending.SubgeodesicPerronStability
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesics

/-!
# Admissibility of the Perron finite geodesic

An actual subgeodesic with the requested endpoints makes the all-competitor
Perron envelope a subgeodesic with those same endpoints. Apply full Perron
stability to endpoint/curve triples, preserving every admissible endpoint
choice, and identify the regularized suprema with the existing definitions.

Source: Xia, SGPT Lemma 4.2.1, PDF page 0154.
-/

set_option autoImplicit false

open Set

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicAdmissible

open FirstPass FirstPass.PositiveClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- **Xia, SGPT Lemma 4.2.1.** An actual boundary subgeodesic supplies both
endpoints of the Perron finite geodesic. -/
theorem isSubgeodesicFrom_finiteGeodesic
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u₀ u₁ : M → EReal} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicFrom theta.val curve u₀ u₁) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ := by
  classical
  let S : Set ((M → EReal) × (M → EReal) × (ℝ → M → EReal)) :=
    {p | p.1 ≤ u₀ ∧ p.2.1 ≤ u₁ ∧ IsSubgeodesicFrom theta.val p.2.2 p.1 p.2.1}
  let b : S := ⟨(u₀, u₁, curve), le_rfl, le_rfl, h⟩
  have : Nonempty S := ⟨b⟩
  have hfamily : ∀ i : S, IsSubgeodesicFrom theta.val i.val.2.2 i.val.1 i.val.2.1 :=
    fun i => i.property.2.2
  obtain ⟨A, hA⟩ := h.left_endpoint.exists_global_upper_bound
  obtain ⟨B, hB⟩ := h.right_endpoint.exists_global_upper_bound
  have hsup := SubgeodesicPerronStability.isSubgeodesicFrom_uscRegularization_iSup_of_bounded_endpoints
    omega theta hfamily
    ⟨A, fun i x => (i.property.1 x).trans (hA x)⟩
    ⟨B, fun i x => (i.property.2.1 x).trans (hB x)⟩
  have hleft : uscRegularization (fun x => ⨆ i : S, i.val.1 x) = u₀ := by
    apply le_antisymm
    · exact uscRegularization_le h.left_endpoint.1.quasiPlurisubharmonic.upperSemicontinuous
        (fun x => iSup_le fun i => i.property.1 x)
    · intro x
      exact (show u₀ x ≤ ⨆ i : S, i.val.1 x from le_iSup_of_le b le_rfl).trans
        (le_uscRegularization (fun x => ⨆ i : S, i.val.1 x) x)
  have hright : uscRegularization (fun x => ⨆ i : S, i.val.2.1 x) = u₁ := by
    apply le_antisymm
    · exact uscRegularization_le h.right_endpoint.1.quasiPlurisubharmonic.upperSemicontinuous
        (fun x => iSup_le fun i => i.property.2.1 x)
    · intro x
      exact (show u₁ x ≤ ⨆ i : S, i.val.2.1 x from le_iSup_of_le b le_rfl).trans
        (le_uscRegularization (fun x => ⨆ i : S, i.val.2.1 x) x)
  have hcurve : (fun t => uscRegularization (fun x => ⨆ i : S, i.val.2.2 t x)) =
      finiteGeodesic theta.val u₀ u₁ := by
    funext t
    unfold finiteGeodesic
    congr 1
    funext x
    rw [finiteGeodesicSliceSupremum_apply]
    apply le_antisymm
    · apply iSup_le
      intro i
      have hi : i.val.2.2 ∈ finiteGeodesicCompetitors theta.val u₀ u₁ :=
        ⟨i.val.1, i.val.2.1, (hfamily i).left_endpoint, (hfamily i).right_endpoint,
          i.property.1, i.property.2.1, hfamily i⟩
      exact le_iSup_of_le i.val.2.2 (le_iSup_of_le hi le_rfl)
    · apply iSup_le
      intro c
      apply iSup_le
      rintro ⟨v₀, v₁, _, _, hv₀, hv₁, hc⟩
      exact le_iSup_of_le (⟨(v₀, v₁, c), hv₀, hv₁, hc⟩ : S) le_rfl
  rw [hleft, hright, hcurve] at hsup
  exact hsup

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicAdmissible
