import SGPT.Toric.ToricAmpleFaceSpan

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

/-- Original inequalities give an actual point of the D-face, using a
point of the ND-H-face and ANY point of the same original H-face. -/
theorem toricDivisorFace_ample_perturbation (D : ToricDivisor γ hs)
    (N : ℕ) (hN : 0 < N) {R : Set (PolytopeToricRays γ hs)} {q x : E}
    (hq : q ∈ toricDivisorFace ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) R)
    (hx : x ∈ toricDivisorFace (polytopeToricAmpleDivisor γ hs) R) :
    (N : ℝ)⁻¹ • (q + x) ∈ toricDivisorFace D R := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_⟩
  · intro ρ
    have hqρ := hq.1 ρ
    have hxρ := hx.1 ρ
    change -(((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) ρ : ℝ) ≤
      latticeFunctional ρ.val q at hqρ
    change -((polytopeToricAmpleDivisor γ hs) ρ : ℝ) ≤
      latticeFunctional ρ.val x at hxρ
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast] at hqρ
    change -(D ρ : ℝ) ≤ latticeFunctional ρ.val ((N : ℝ)⁻¹ • (q + x))
    rw [map_smul, map_add, smul_eq_mul]
    apply (le_inv_mul_iff₀ hNR).mpr
    nlinarith
  · intro ρ hρ
    have hqρ := hq.2 ρ hρ
    have hxρ := hx.2 ρ hρ
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast] at hqρ
    rw [map_smul, map_add, smul_eq_mul, hqρ, hxρ]
    field_simp
    ring

/-- Differences of the actual translated H-face prove the FULL actual
annihilator span of D. This is a producer, not a fullness input. -/
theorem toricDivisorFace_full_of_ample_perturbation (D : ToricDivisor γ hs)
    (N : ℕ) (hN : 0 < N) {R : Set (PolytopeToricRays γ hs)}
    (hR : IsToricFanCone R)
    (hq : (toricDivisorFace ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) R).Nonempty) :
    ToricDivisorFaceFull D R := by
  obtain ⟨q, hq⟩ := hq
  obtain ⟨hHne, hHspan⟩ := toricAmpleDivisorFace_full_of_fanCone hR
  obtain ⟨x₀, hx₀⟩ := hHne
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨⟨_, toricDivisorFace_ample_perturbation D N hN hq hx₀⟩,
    le_antisymm (vectorSpan_toricDivisorFace_le D R) ?_⟩
  rw [← hHspan]
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, y, hy, rfl⟩
  have hdiff := vsub_mem_vectorSpan ℝ
    (toricDivisorFace_ample_perturbation D N hN hq hx)
    (toricDivisorFace_ample_perturbation D N hN hq hy)
  have hscale : (N : ℝ) •
      ((N : ℝ)⁻¹ • (q + x) - (N : ℝ)⁻¹ • (q + y)) = x - y := by
    ext i
    simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp
    ring
  have hscaled : (N : ℝ) •
      ((N : ℝ)⁻¹ • (q + x) - (N : ℝ)⁻¹ • (q + y)) ∈
      vectorSpan ℝ (toricDivisorFace D R) := Submodule.smul_mem _ (N : ℝ) hdiff
  rw [hscale] at hscaled
  exact hscaled

theorem toricDivisorFace_full_of_not_mem_perturbed_stableBaseLocus
    (D : ToricDivisor γ hs) (N : ℕ) (hN : 0 < N)
    {p : PolytopeToricVariety γ hs}
    (hp : p ∉ toricStableBaseLocus ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs))
    {R : Set (PolytopeToricRays γ hs)} (hR : IsToricFanCone R) (hRp : R ⊆ orbitRays p) :
    ToricDivisorFaceFull D R := by
  apply toricDivisorFace_full_of_ample_perturbation D N hN hR
  obtain ⟨q, hq⟩ := (not_mem_toricStableBaseLocus_iff_face_nonempty _ p).mp hp
  exact ⟨q, toricDivisorFace_mono_rays _ hRp hq⟩

/-- The original deficient-face union is contained in the ACTUAL augmented
base locus. The conclusion uses actual orbit closures and actual section
base loci, including empty faces and point strata. -/
theorem deficient_toricOrbitClosure_subset_augmentedBaseLocus
    (D : ToricDivisor γ hs) {R : Set (PolytopeToricRays γ hs)}
    (hR : IsToricFanCone R) (hdef : ToricDivisorFaceDeficient D R) :
    toricOrbitClosure R ⊆ toricAugmentedBaseLocus D := by
  intro p hp
  simp only [toricAugmentedBaseLocus, mem_iInter]
  intro N hN
  by_contra hexit
  have hfull := toricDivisorFace_full_of_not_mem_perturbed_stableBaseLocus
    D N hN hexit hR (mem_toricOrbitClosure_iff.mp hp)
  exact ((toricDivisorFaceFull_iff_not_deficient D hR).mp hfull) hdef

theorem deficient_toricOrbitClosure_union_subset_augmentedBaseLocus
    (D : ToricDivisor γ hs) :
    (⋃ (R : Set (PolytopeToricRays γ hs)) (_ : IsToricFanCone R)
      (_ : ToricDivisorFaceDeficient D R), toricOrbitClosure R) ⊆
      toricAugmentedBaseLocus D := by
  intro p hp
  simp only [mem_iUnion, exists_prop] at hp
  obtain ⟨R, hR, hdef, hp⟩ := hp
  exact deficient_toricOrbitClosure_subset_augmentedBaseLocus D hR hdef hp

end SGPT.Toric
