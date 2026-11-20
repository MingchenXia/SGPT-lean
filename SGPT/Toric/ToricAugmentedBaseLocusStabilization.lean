import SGPT.Toric.ToricAugmentedBaseLocusSufficiency

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.PSH.VariableComplexAtlas
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem toricDivisorFace_add_nat_smul (A D : ToricDivisor γ hs) (N : ℕ)
    {R : Set (PolytopeToricRays γ hs)} {x y : E}
    (hx : x ∈ toricDivisorFace A R) (hy : y ∈ toricDivisorFace D R) :
    x + (N : ℝ) • y ∈ toricDivisorFace (A + (N : ℤ) • D) R := by
  refine ⟨?_, ?_⟩
  · intro ρ
    have hxρ := hx.1 ρ
    have hyρ := hy.1 ρ
    change -(A ρ : ℝ) ≤ latticeFunctional ρ.val x at hxρ
    change -(D ρ : ℝ) ≤ latticeFunctional ρ.val y at hyρ
    change -((A + (N : ℤ) • D) ρ : ℝ) ≤ latticeFunctional ρ.val (x + (N : ℝ) • y)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, map_add, map_smul]
    have hNN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  · intro ρ hρ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, map_add, map_smul, hx.2 ρ hρ, hy.2 ρ hρ]
    ring

theorem perturbed_toricDivisorFace_nonempty_mono (D : ToricDivisor γ hs)
    {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N)
    {R : Set (PolytopeToricRays γ hs)} (hR : IsToricFanCone R)
    (hface : (toricDivisorFace ((M : ℤ) • D - polytopeToricAmpleDivisor γ hs) R).Nonempty) :
    (toricDivisorFace ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) R).Nonempty := by
  obtain ⟨q, hq⟩ := hface
  obtain ⟨x, hx⟩ := (toricAmpleDivisorFace_full_of_fanCone hR).1
  have hD := toricDivisorFace_ample_perturbation D M hM hq hx
  have hnew := toricDivisorFace_add_nat_smul
    ((M : ℤ) • D - polytopeToricAmpleDivisor γ hs) D (N - M) hq hD
  have heq : ((M : ℤ) • D - polytopeToricAmpleDivisor γ hs) + ((N - M : ℕ) : ℤ) • D =
      (N : ℤ) • D - polytopeToricAmpleDivisor γ hs := by
    ext ρ
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Int.ofNat_sub hMN]
    ring
  rw [heq] at hnew
  exact ⟨_, hnew⟩

theorem perturbed_toricStableBaseLocus_antitone (D : ToricDivisor γ hs)
    {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N) :
    toricStableBaseLocus ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) ⊆
      toricStableBaseLocus ((M : ℤ) • D - polytopeToricAmpleDivisor γ hs) := by
  intro p hp
  by_contra hnot
  have hface := (not_mem_toricStableBaseLocus_iff_face_nonempty _ p).mp hnot
  have hfaceN := perturbed_toricDivisorFace_nonempty_mono D hM hMN
    (isToricFanCone_orbitRays p) hface
  exact (not_mem_toricStableBaseLocus_iff_face_nonempty _ p).mpr hfaceN hp

/-- Finite ORIGINAL ray sets, with actual section-base-locus exits, produce
a genuine finite integral stabilization. No Noetherianity or stabilization
certificate is incoming. -/
theorem exists_toricAugmentedBaseLocus_eq_toricStableBaseLocus (D : ToricDivisor γ hs) :
    ∃ N : ℕ, 0 < N ∧ toricAugmentedBaseLocus D =
      toricStableBaseLocus ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) := by
  let _ := (finite_polytopeToricRays γ hs).fintype
  have hchoose : ∀ R : Set (PolytopeToricRays γ hs), ∃ N : ℕ, 0 < N ∧
      ((∃ M : ℕ, 0 < M ∧
        (toricDivisorFace ((M : ℤ) • D - polytopeToricAmpleDivisor γ hs) R).Nonempty) →
        (toricDivisorFace ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) R).Nonempty) := by
    intro R
    by_cases hex : ∃ M : ℕ, 0 < M ∧
        (toricDivisorFace ((M : ℤ) • D - polytopeToricAmpleDivisor γ hs) R).Nonempty
    · obtain ⟨M, hM, hface⟩ := hex
      exact ⟨M, hM, fun _ => hface⟩
    · exact ⟨1, by omega, fun h => (hex h).elim⟩
  choose bound hboundpos hboundface using hchoose
  let N := Finset.univ.sup bound + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hbound (R : Set (PolytopeToricRays γ hs)) : bound R ≤ N :=
    (Finset.le_sup (f := bound) (Finset.mem_univ R)).trans (Nat.le_add_right _ _)
  refine ⟨N, hN, Set.Subset.antisymm ?_ ?_⟩
  · intro p hp
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hp N) hN
  · intro p hp
    simp only [toricAugmentedBaseLocus, mem_iInter]
    intro M hM
    by_contra hnot
    have hfaceM := (not_mem_toricStableBaseLocus_iff_face_nonempty _ p).mp hnot
    have hfaceBound := hboundface (orbitRays p) ⟨M, hM, hfaceM⟩
    have hfaceN := perturbed_toricDivisorFace_nonempty_mono D (hboundpos _)
      (hbound _) (isToricFanCone_orbitRays p) hfaceBound
    exact (not_mem_toricStableBaseLocus_iff_face_nonempty _ p).mpr hfaceN hp

/-- The ACTUAL augmented base locus is the common zero set of all genuine
sections in one actual finite integral ordinary section space. -/
theorem exists_toricAugmentedBaseLocus_eq_toricBaseLocus (D : ToricDivisor γ hs) :
    ∃ (N k : ℕ), 0 < N ∧ 0 < k ∧ toricAugmentedBaseLocus D =
      toricBaseLocus ((k : ℤ) • ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs)) := by
  obtain ⟨N, hN, heq⟩ := exists_toricAugmentedBaseLocus_eq_toricStableBaseLocus D
  obtain ⟨k, hk, heqk⟩ := exists_toricStableBaseLocus_eq_toricBaseLocus
    ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs)
  exact ⟨N, k, hN, hk, heq.trans heqk⟩

theorem hasAnalyticChartEquations_toricAugmentedBaseLocus (D : ToricDivisor γ hs) :
    (ofFixedModel n (PolytopeToricVariety γ hs)).HasAnalyticChartEquations
      (toricAugmentedBaseLocus D) := by
  obtain ⟨N, _, heq⟩ := exists_toricAugmentedBaseLocus_eq_toricStableBaseLocus D
  rw [heq]
  exact hasAnalyticChartEquations_toricStableBaseLocus _

end SGPT.Toric
