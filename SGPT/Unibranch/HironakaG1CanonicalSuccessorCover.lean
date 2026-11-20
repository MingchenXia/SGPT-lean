import SGPT.Unibranch.HironakaG1CanonicalStageSuccessor

/-!
# The actual strict-window/off-centre cover of a genuine canonical successor

The preceding XStage need not have a full window cover. Its actual centre
is covered by centre images; the exact successor range equations lift those
windows, and the retained native off-centre isomorphism supplies the rest.

Blueprint FIRST: `hironaka-g1-canonical-successor-cover.tex`.
-/

set_option autoImplicit false

open Set CategoryTheory AlgebraicGeometry

namespace SGPT.Unibranch.HironakaG1CanonicalSuccessorCover

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending SourceReducedComplexSpace
  HironakaG11VanishingWindows HironakaG11VanishingPrincipalization HironakaG11CompatibleCanonicalTowers
  HironakaG11StrictTransformTowers HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11PresLineState HironakaG1CanonicalStageCentreIdeal
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism

noncomputable section

variable {X : SourceReducedComplexSpace} {N k : ℕ} {Λ : Type*} [LinearOrder Λ]
  {ι : Type*} (w : ι → DimEmbedding X N) (M : ∀ i, MarkedIdeal N (Amb w i))
  (B : BMInvariant N (fun {Y} A A' => LocWPEquiv (X := Y) A A') k Λ)
  (hD : ∀ i, ResolutionInvariantSpec.IsInvDomain k (M i)) (hClass : InitialClassData w M)
  (H : ι → ℕ → ℕ) (hState : ∀ i, NativeHSState (M i) (w i).carrier (H i))
  (K : ∀ i, Set (w i).ambient)
  (hCover : ∀ i (c : (w i).carrier), c.val ∈ (M i).cosupp →
    ∃ j, ∃ c' : (w j).carrier, c'.val ∈ K j ∧
      (w j).toLocalEmbedding.toPoint c' = (w i).toLocalEmbedding.toPoint c)
  {m : ℕ} (s : GStage B.toResolutionInvariant M (mapAdm w) m) (xs : XStage w s.T)
  [Finite ι] (hK : ∀ i, IsCompact (K i))
  (a : HironakaG1CanonicalStageSuccessor.Successor w M B hD hClass H hState K hCover s xs hK)

local notation "C" => support w M B hD hClass H hState K hCover s xs

/-- The actual windows cover every point above C; the SAME native off-centre
branch supplies all remaining points. No whole XStage cover is assumed. -/
theorem successor_window_or_offCentre (y : a.Y.obj.left) :
    (∃ i, ∃ z, (a.map i).hom.left.base z = y) ∨ a.p.hom.left.base y ∉ C := by
  classical
  by_cases hy : a.p.hom.left.base y ∈ C
  · obtain ⟨i, c, -, hcy⟩ :=
      (localCentres w M B hD hClass H hState K hCover s xs).mem_support.mp hy
    have hwin : a.p.hom.left.base y ∈ range (xs.map i).hom.left.base := ⟨c, hcy⟩
    have hlift : y ∈ range (a.map i).hom.left.base := by
      rw [a.range_map i]
      exact hwin
    obtain ⟨z, hz⟩ := hlift
    exact Or.inl ⟨i, z, hz⟩
  · exact Or.inr hy

/-- Exact whole-successor coverage by strict windows and the actual native
off-centre isomorphism branch retained by a.isIsoOver. -/
theorem successor_lift_cover :
    (⋃ i, range (a.map i).hom.left.base) ∪ a.p.hom.left.base ⁻¹' Cᶜ = univ := by
  apply eq_univ_of_forall
  intro y
  rcases successor_window_or_offCentre w M B hD hClass H hState K hCover s xs hK a y with h | h
  · obtain ⟨i, z, hz⟩ := h
    exact Or.inl (mem_iUnion.mpr ⟨i, z, hz⟩)
  · exact Or.inr h

end
end SGPT.Unibranch.HironakaG1CanonicalSuccessorCover
