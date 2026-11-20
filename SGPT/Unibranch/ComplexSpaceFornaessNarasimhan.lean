import SGPT.Unibranch.ComplexSpaceThetaPSH
import SGPT.PSH.SubharmonicStrip

/-!
# The Fornæss--Narasimhan criterion on domains

Source `thm:FN`. The forward implication (1) ⇒ (2) holds on every complex space
(`IsPSH.fornaessNarasimhan_forward`). Here we prove the converse (2) ⇒ (1) when
the complex space is a domain `U ⊆ ℂ^n`: an upper semicontinuous function
`φ : U → [-∞, ∞)`, not identically `-∞` on the (unique) irreducible component of
`U`, whose pull-back by every holomorphic disc `f : Δ → U` with `f^*φ ≢ -∞` is
subharmonic, is plurisubharmonic. Together with the forward implication this is
the full equivalence of `thm:FN` on domains (`fornaessNarasimhan_domain`).

The holomorphic discs used are the affine discs `t ↦ x + R t v`, as morphisms of
complex spaces `Δ → U` (`discMorphism`).

Original source: Appendix B (`appendix_unibranch.tex`), `thm:FN`.
Blueprint: `claude-unibranch.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceMaps

namespace SGPT.Unibranch

noncomputable section

namespace SourceReducedComplexSpace

variable {n : ℕ}

/-- The holomorphic disc `Δ → U` of complex spaces induced by a holomorphic map
`F : ℂ^1 → ℂ^n` sending the unit disc into `U`. -/
def discMorphism (U : Opens (ComplexModel n)) (F : ComplexModel 1 → ComplexModel n)
    (hF : ContDiff ℂ ∞ F) (hmaps : ∀ z ∈ unitDiscOpens, F z ∈ U) :
    unitDisc ⟶ domainSpace U :=
  let f : unitDiscOpens → U := fun z => ⟨F z, hmaps z z.2⟩
  have hf : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff U f).mp
    have h : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel n) ∞
        (fun z : unitDiscOpens => F z.val) :=
      hF.contMDiff.comp contMDiff_subtype_val
    exact h
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap hf (C := (univ : Set unitDiscOpens)) (D := (univ : Set U))
      (fun _ _ => trivial))
    (actualSubspaceMap_point hf _))

@[simp] theorem discCoordinate_apply_zero (t : ℂ) : discCoordinate t 0 = t := by
  simp [discCoordinate]

theorem discCoordinate_mem_unitDiscOpens {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) :
    discCoordinate t ∈ unitDiscOpens := by
  simpa [unitDiscOpens, norm_discCoordinate] using ht

/-- The pull-back of a function on `U` by the disc `discMorphism U F`. -/
theorem discPullback_discMorphism {U : Opens (ComplexModel n)}
    {F : ComplexModel 1 → ComplexModel n} {hF : ContDiff ℂ ∞ F}
    {hmaps : ∀ z ∈ unitDiscOpens, F z ∈ U} (u : ComplexModel n → EReal) {t : ℂ}
    (ht : t ∈ ball (0 : ℂ) 1) :
    discPullback (discMorphism U F hF hmaps) (fun p : (univ : Set U) => u p.val.val) t =
      u (F (discCoordinate t)) := by
  have h := discCoordinate_mem_unitDiscOpens ht
  unfold discPullback modelPullback
  split_ifs
  rfl

theorem norm_le_of_mem_unitDiscOpens {z : ComplexModel 1} (hz : z ∈ unitDiscOpens) :
    ‖z 0‖ < 1 := by
  have h : ‖z‖ < 1 := by simpa [unitDiscOpens] using hz
  have hz' : ‖z‖ = ‖z 0‖ := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
  rwa [← hz']

/-- Source `thm:FN`, implication (2) ⇒ (1), on a domain `U ⊆ ℂ^n`. -/
theorem isPSH_domain_of_disc {U : Opens (ComplexModel n)}
    (hU : IsConnected (U : Set (ComplexModel n))) (u : ComplexModel n → EReal)
    (hne_top : ∀ z ∈ U, u z ≠ ⊤)
    (hcomp : ∀ Z : Set (domainSpace U).obj.left, (domainSpace U).IsIrreducibleComponent Z →
      ∃ z ∈ Z, (fun p : (univ : Set U) => u p.val.val) z ≠ ⊥)
    (husc : UpperSemicontinuous (fun p : (univ : Set U) => u p.val.val))
    (hdisc : ∀ f : unitDisc ⟶ domainSpace U,
      (∃ t ∈ ball (0 : ℂ) 1, discPullback f (fun p : (univ : Set U) => u p.val.val) t ≠ ⊥) →
        SGPT.PSH.SubharmonicOn (discPullback f (fun p : (univ : Set U) => u p.val.val))
          (ball (0 : ℂ) 1)) :
    (domainSpace U).IsPSH (fun p : (univ : Set U) => u p.val.val) := by
  rw [isPSH_model_univ_iff hU]
  refine ⟨⟨hne_top, ?_, ?_⟩, ?_⟩
  · -- upper semicontinuity on `U`
    intro z hz y hy
    let ι : ↥(univ : Set U) → ComplexModel n := fun p => p.val.val
    have hι : Topology.IsEmbedding ι :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    have hrange : range ι = (U : Set (ComplexModel n)) := by
      ext w
      constructor
      · rintro ⟨p, rfl⟩
        exact p.val.property
      · intro hw
        exact ⟨⟨⟨w, hw⟩, trivial⟩, rfl⟩
    have h := husc ⟨⟨z, hz⟩, trivial⟩ y hy
    have hmap := hι.map_nhds_eq (⟨⟨z, hz⟩, trivial⟩ : (univ : Set U))
    rw [hrange] at hmap
    change ∀ᶠ w in 𝓝[(U : Set (ComplexModel n))] (ι ⟨⟨z, hz⟩, trivial⟩), u w < y
    rw [← hmap]
    exact eventually_map.mpr h
  · -- the disc submean inequalities
    intro x v r hr hD C hC
    by_cases hv : v = 0
    · subst v
      simpa only [SGPT.Foundations.Analysis.circleDeficit, smul_zero, add_zero] using
        (SGPT.Foundations.Analysis.circleDeficit_const (u x) x (0 : ComplexModel n) r C).le
    let L : ℂ → ComplexModel n := fun t => x + t • v
    have hLc : Continuous L := by fun_prop
    have hballU : closedBall (0 : ℂ) r ⊆ L ⁻¹' (U : Set (ComplexModel n)) := by
      intro t ht
      exact hD ⟨t, ht, rfl⟩
    obtain ⟨δ, hδ, hthick⟩ := (isCompact_closedBall (0 : ℂ) r).exists_thickening_subset_open
      (U.isOpen.preimage hLc) hballU
    rw [thickening_closedBall hδ hr.le] at hthick
    set R : ℝ := r + δ / 2 with hRdef
    have hR : 0 < R := by positivity
    have hrR : r < R := by linarith
    let F : ComplexModel 1 → ComplexModel n := fun z => x + ((R : ℂ) * z 0) • v
    have hF : ContDiff ℂ ∞ F := by
      have h0 : ContDiff ℂ ∞ (fun z : ComplexModel 1 => z 0) :=
        (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).contDiff
      exact contDiff_const.add ((contDiff_const.mul h0).smul contDiff_const)
    have hmaps : ∀ z ∈ unitDiscOpens, F z ∈ U := by
      intro z hz
      have h1 := norm_le_of_mem_unitDiscOpens hz
      have h2 : (R : ℂ) * z 0 ∈ ball (0 : ℂ) (δ + r) := by
        rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
        calc R * ‖z 0‖ < R * 1 := mul_lt_mul_of_pos_left h1 hR
          _ = R := mul_one R
          _ < δ + r := by linarith
      exact hthick h2
    set f := discMorphism U F hF hmaps
    set w := discPullback f (fun p : (univ : Set U) => u p.val.val)
    have hw : ∀ t ∈ ball (0 : ℂ) 1, w t = u (x + ((R : ℂ) * t) • v) := by
      intro t ht
      change discPullback (discMorphism U F hF hmaps) (fun p : ↥(univ : Set U) => u p.val.val) t = _
      rw [discPullback_discMorphism u ht]
      simp [F]
    set ρ : ℝ := r / R with hρdef
    have hρ : 0 < ρ := div_pos hr hR
    have hρ1 : ρ < 1 := (div_lt_one hR).mpr hrR
    have hRρ : R * ρ = r := by rw [hρdef]; field_simp
    have hdisc0 : SGPT.Foundations.Analysis.affineClosedDisc (0 : ℂ) 1 ρ ⊆ ball (0 : ℂ) 1 := by
      rintro _ ⟨s, hs, rfl⟩
      rw [mem_ball_zero_iff]
      have := mem_closedBall_zero_iff.mp hs
      simp only [smul_eq_mul, mul_one, zero_add]
      linarith
    have hw0 : w 0 = u x := by
      rw [hw 0 (mem_ball_self one_pos)]
      simp
    by_cases hne : ∃ t ∈ ball (0 : ℂ) 1, w t ≠ ⊥
    · have hsub := (hdisc f hne).discPshOn
      have hbound : ∀ y ∈ SGPT.Foundations.Analysis.affineClosedDisc (0 : ℂ) 1 ρ, w y ≤ (C : EReal) := by
        intro y hy
        obtain ⟨s, hs, rfl⟩ := hy
        have hsball : (0 : ℂ) + s • (1 : ℂ) ∈ ball (0 : ℂ) 1 := hdisc0 ⟨s, hs, rfl⟩
        rw [hw _ hsball]
        apply hC
        refine ⟨(R : ℂ) * s, ?_, ?_⟩
        · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
          have := mem_closedBall_zero_iff.mp hs
          calc R * ‖s‖ ≤ R * ρ := mul_le_mul_of_nonneg_left this hR.le
            _ = r := hRρ
        · simp
      have hmean := hsub.submean 0 1 ρ hρ hdisc0 C hbound
      have hcirc : SGPT.Foundations.Analysis.circleDeficit w 0 1 ρ C =
          SGPT.Foundations.Analysis.circleDeficit u x v r C := by
        unfold SGPT.Foundations.Analysis.circleDeficit
        apply MeasureTheory.lintegral_congr
        intro θ
        have hmem : (0 : ℂ) + circleMap 0 ρ θ • (1 : ℂ) ∈ ball (0 : ℂ) 1 :=
          hdisc0 (SGPT.Foundations.Analysis.circle_mem_affineClosedDisc 0 1 hρ.le θ)
        rw [hw _ hmem]
        congr 3
        simp only [circleMap, smul_eq_mul, mul_one, zero_add]
        rw [← mul_assoc, ← Complex.ofReal_mul, hRρ]
      rw [← hcirc, ← hw0]
      exact hmean
    · simp only [not_exists, not_and, not_not] at hne
      have hux : u x = ⊥ := by
        rw [← hw0]
        exact hne 0 (mem_ball_self one_pos)
      rw [hux]
      have htop : ((C : EReal) - ⊥).toENNReal = ⊤ := by simp
      rw [htop, ENNReal.mul_top (by simp [Real.pi_pos])]
      exact le_top
  · obtain ⟨z, -, hz⟩ := hcomp univ ((isIrreducibleComponent_model_univ_iff hU univ).mpr rfl)
    exact ⟨z.val.val, z.val.property, hz⟩

/-- Source `thm:FN` on a domain `U ⊆ ℂ^n`: for `φ : U → [-∞, ∞)` not identically
`-∞` on the irreducible component of `U`, `φ` is plurisubharmonic iff it is upper
semicontinuous and its pull-back by every holomorphic disc `f : Δ → U` with
`f^*φ ≢ -∞` is subharmonic. -/
theorem fornaessNarasimhan_domain {U : Opens (ComplexModel n)}
    (hU : IsConnected (U : Set (ComplexModel n))) (u : ComplexModel n → EReal)
    (hne_top : ∀ z ∈ U, u z ≠ ⊤)
    (hcomp : ∀ Z : Set (domainSpace U).obj.left, (domainSpace U).IsIrreducibleComponent Z →
      ∃ z ∈ Z, (fun p : (univ : Set U) => u p.val.val) z ≠ ⊥) :
    (domainSpace U).IsPSH (fun p : (univ : Set U) => u p.val.val) ↔
      (UpperSemicontinuous (fun p : (univ : Set U) => u p.val.val) ∧
        ∀ f : unitDisc ⟶ domainSpace U,
          (∃ t ∈ ball (0 : ℂ) 1, discPullback f (fun p : (univ : Set U) => u p.val.val) t ≠ ⊥) →
            SGPT.PSH.SubharmonicOn (discPullback f (fun p : (univ : Set U) => u p.val.val))
              (ball (0 : ℂ) 1)) :=
  ⟨fun h => h.fornaessNarasimhan_forward,
    fun h => isPSH_domain_of_disc hU u hne_top hcomp h.1 h.2⟩

end SourceReducedComplexSpace

end

end SGPT.Unibranch
