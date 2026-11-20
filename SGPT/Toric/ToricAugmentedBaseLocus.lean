import SGPT.Toric.ToricStratumVolumeGeometry
import SGPT.Toric.BigToric2BaseLocus
import SGPT.Toric.ToricFaceDirectionLattice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The original augmented base locus, constructed from the common zero
sets of ALL actual holomorphic sections, with the actual reference ample
divisor. No face or Newton-body formula occurs in this definition. -/
def toricAugmentedBaseLocus (D : ToricDivisor γ hs) : Set (PolytopeToricVariety γ hs) :=
  ⋂ (N : ℕ) (_ : 0 < N),
    toricStableBaseLocus ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs)

/-- Fullness of the actual original face in the actual cone annihilator. -/
def ToricDivisorFaceFull (D : ToricDivisor γ hs) (R : Set (PolytopeToricRays γ hs)) : Prop :=
  (toricDivisorFace D R).Nonempty ∧
    vectorSpan ℝ (toricDivisorFace D R) = toricStratumRealSpace R

/-- The original strict affine-dimension inequality, with its essential
empty-face convention, including expected dimension zero. -/
def ToricDivisorFaceDeficient (D : ToricDivisor γ hs)
    (R : Set (PolytopeToricRays γ hs)) : Prop :=
  toricDivisorFace D R = ∅ ∨
    Module.finrank ℝ (vectorSpan ℝ (toricDivisorFace D R)) < n - Nat.card R

theorem not_mem_toricStableBaseLocus_iff_face_nonempty (D : ToricDivisor γ hs)
    (p : PolytopeToricVariety γ hs) :
    p ∉ toricStableBaseLocus D ↔ (toricDivisorFace D (orbitRays p)).Nonempty := by
  rw [mem_toricStableBaseLocus_iff_orbitRays]
  constructor
  · intro h
    push Not at h
    obtain ⟨x, hx, hh⟩ := h
    refine ⟨x, hx, ?_⟩
    intro ρ hρ
    have hle := hh ρ hρ
    have hge := hx ρ
    change -(D ρ : ℝ) ≤ latticeFunctional ρ.val x at hge
    linarith
  · rintro ⟨x, hx, hh⟩ h
    obtain ⟨ρ, hρ, hpos⟩ := h x hx
    rw [hh ρ hρ] at hpos
    linarith

theorem toricDivisorFace_mono_rays (D : ToricDivisor γ hs)
    {R S : Set (PolytopeToricRays γ hs)} (hRS : R ⊆ S) :
    toricDivisorFace D S ⊆ toricDivisorFace D R := by
  intro x hx
  exact ⟨hx.1, fun ρ hρ => hx.2 ρ (hRS hρ)⟩

theorem vectorSpan_toricDivisorFace_le (D : ToricDivisor γ hs)
    (R : Set (PolytopeToricRays γ hs)) :
    vectorSpan ℝ (toricDivisorFace D R) ≤ toricStratumRealSpace R := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, y, hy, rfl⟩ ρ hρ
  change latticeFunctional ρ.val (x - y) = 0
  rw [map_sub, hx.2 ρ hρ, hy.2 ρ hρ, sub_self]


theorem toricDivisorFaceFull_iff_not_deficient (D : ToricDivisor γ hs)
    {R : Set (PolytopeToricRays γ hs)} (hR : IsToricFanCone R) :
    ToricDivisorFaceFull D R ↔ ¬ ToricDivisorFaceDeficient D R := by
  obtain ⟨v, J, rfl⟩ := hR
  have hinj : Function.Injective (polytopeToricRay γ hs v) := by
    intro i j hij
    have hh := congrArg (fun ρ : PolytopeToricRays γ hs =>
      intPairing (originalPolytopeNativeBasis γ hs v i) ρ.val) hij
    change intPairing (originalPolytopeNativeBasis γ hs v i)
      (polytopeToricRayGenerator γ hs v i) =
      intPairing (originalPolytopeNativeBasis γ hs v i)
        (polytopeToricRayGenerator γ hs v j) at hh
    rw [intPairing_basis_rayGenerator, intPairing_basis_rayGenerator, if_pos rfl] at hh
    by_contra hne
    rw [if_neg hne] at hh
    norm_num at hh
  have hcard : Nat.card (polytopeToricRay γ hs v '' J) = Nat.card J :=
    Nat.card_congr (Equiv.Set.image _ _ hinj).symm
  have hdim : Module.finrank ℝ
      (toricStratumRealSpace (polytopeToricRay γ hs v '' J)) =
      n - Nat.card (polytopeToricRay γ hs v '' J) := by
    rw [finrank_toricStratumRealSpace, hcard, Nat.card_eq_fintype_card]
    simp [toricFaceDimension, Fintype.card_subtype_compl]
  have hle := vectorSpan_toricDivisorFace_le D (polytopeToricRay γ hs v '' J)
  unfold ToricDivisorFaceFull ToricDivisorFaceDeficient
  rw [not_or]
  constructor
  · rintro ⟨hne, heq⟩
    refine ⟨hne.ne_empty, ?_⟩
    rw [heq, hdim]
    exact lt_irrefl _
  · rintro ⟨hne, hdimle⟩
    refine ⟨Set.nonempty_iff_ne_empty.mpr hne, ?_⟩
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hdim]
    exact Nat.le_of_not_gt hdimle

theorem isClosed_toricAugmentedBaseLocus (D : ToricDivisor γ hs) :
    IsClosed (toricAugmentedBaseLocus D) :=
  isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_toricStableBaseLocus _

theorem polytopeToricAction_mem_toricAugmentedBaseLocus_iff (D : ToricDivisor γ hs)
    (a : Fin n → ℂˣ) (p : PolytopeToricVariety γ hs) :
    polytopeToricAction γ hs a p ∈ toricAugmentedBaseLocus D ↔
      p ∈ toricAugmentedBaseLocus D := by
  simp only [toricAugmentedBaseLocus, mem_iInter,
    polytopeToricAction_mem_toricStableBaseLocus_iff]

end SGPT.Toric
