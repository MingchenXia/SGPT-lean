import SGPT.Projective.NativeCITower
import SGPT.Bergman.SiuKodairaFiniteSections

/-!
# regular cuts in every sufficiently large power

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749).  The Snapper–Kleiman comparison needs
complete-intersection cuts of a positive line bundle `L` in two *consecutive* powers `L^d`,
`L^(d+1)` (the existing producer `exists_nativeRegularCut` gives one uncontrolled power).
Siu's uniform generation argument (`SGPT.Bergman.SiuKodaira`) works for every exponent
`K ≥ exponent D s` (`SGPT.Bergman.SiuUniformGeneration.goodPower_exponent`), so the same proofs give:

* `exists_positivePower_productGeneration_ge`, `exists_positivePower_baseGeneration_ge`,
  `exists_positivePower_generates_pointIdeals_ge`: uniform multiplier / point-ideal generation in
  every power `≥ d₀`;
* `exists_positivePower_sections_nonvanishing_ge`: `L^d` is base-point free for every `d ≥ d₀`;
* `exists_positivePower_smoothMember_ge`: Bertini (`SGPT.Trace.Bertini.interior_singularMemberSet`,
  which needs only a holomorphic map defined by generating sections) gives a smooth member of
  `|L^d|` for every `d ≥ d₀`;
* `exists_nativeRegularCut_power_ge`: a `NativeRegularCut` of prescribed power `d` for all `d ≥ d₀`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.BDivisor.BD3

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.SiuUniformGeneration
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.SiuGen SGPT.NAPotential.NAGaga
open SGPT.Trace.BertiniGlobalGeneration SGPT.Bergman.SiuKodaira
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open SGPT.Projective.NumEq.CompleteIntersections
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.AnalyticSectionProducts

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Siu's uniform product generation holds in EVERY power `ell + K` with `K ≥ K₀`
(the proof of `SiuKodaira.exists_positivePower_productGeneration`, with the exponent kept free). -/
theorem exists_positivePower_productGeneration_ge [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG)
    (hKah : θG.val.IsKahler) (ell : ℕ) :
    ∃ K₀ : ℕ, 0 < K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ φ : X → EReal,
      IsThetaPshPotential ((ell : ℝ) • θG).val φ →
      IsProdGloballyGenerated (positivePower G (ell + K - 1))
        (multiplierIdeal (n := n + 1) 1 (fun q : X × unitDisc => φ q.1)) := by
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  let omega : KahlerBackground n X := ⟨θG, hKah⟩
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  let D := fixedGeometry hμ G hG θG hθG hKah
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_siuPoleB hKah
  refine ⟨exponent D (((n : ℝ) + 3) * B), exponent_pos D _, fun K hK0 φ hφ => ?_⟩
  have hKpos : 0 < K := (exponent_pos D _).trans_le hK0
  have hK := goodPower_exponent D (((n : ℝ) + 3) * B) hK0
  have hd : 1 ≤ ell + K := by omega
  have hΦ := SGPT.Trace.ProductMultiplierRestriction.isThetaPshPotential_comp_fst
    (m := 1) (Y := unitDisc) ((ell : ℝ) • θG) hφ
  have hE := sourceNativePositivePower_smooth G hG (ell + K - 1)
  have hOwnE := positivePower_isOwnFirstChernForm G hG hθG (ell + K - 1)
  have hform : (((ell + K - 1 + 1 : ℕ) : ℝ) • θG) =
      (1 : ℝ) • ((ell : ℝ) • θG) + (K : ℝ) • θG := by
    rw [Nat.sub_add_cancel hd]
    push_cast
    module
  rw [hform] at hOwnE
  have hOwnE' : IsOwnFirstChernForm (positivePower G (ell + K - 1))
      (((1 : ℕ) : ℝ) • ((ell : ℝ) • θG) + (K : ℝ) • θG) := by
    simpa only [Nat.cast_one] using hOwnE
  have hcorr := hasProdCorrection_fixedCover D hG hE hθG hK (by norm_num : 0 < (1 : ℕ)) hOwnE' hΦ
  simpa only [Nat.cast_one] using isProdGloballyGenerated_of_fixedCover_correction hμ D hKah hB0 hBa
    (by norm_num : 0 < (1 : ℕ)) hΦ hcorr

/-- Uniform base generation of multiplier ideals in every power `ell + K`, `K ≥ K₀`. -/
theorem exists_positivePower_baseGeneration_ge [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG)
    (hKah : θG.val.IsKahler) (ell : ℕ) :
    ∃ K₀ : ℕ, 0 < K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ φ : X → EReal,
      IsThetaPshPotential ((ell : ℝ) • θG).val φ →
      IsBaseGloballyGenerated (positivePower G (ell + K - 1)) (multiplierIdeal (n := n) 1 φ) := by
  obtain ⟨K₀, hK₀, hgen⟩ := exists_positivePower_productGeneration_ge G hG θG hθG hKah ell
  exact ⟨K₀, hK₀, fun K hK φ hφ => isBaseGloballyGenerated_of_prod _ hφ.1.quasiPlurisubharmonic
    one_pos (hgen K hK φ hφ)⟩

/-- Every power `L^d`, `d ≥ d₀`, generates the ideal of every point. -/
theorem exists_positivePower_generates_pointIdeals_ge [CompactSpace X] (hn : 0 < n)
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG)
    (hKah : θG.val.IsKahler) :
    ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ p : X,
      IsBaseGloballyGenerated (positivePower G (d - 1)) (vanishingIdeal (n := n) ({p} : Set X)) := by
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  let omega : KahlerBackground n X := ⟨θG, hKah⟩
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  let D := fixedGeometry hμ G hG θG hθG hKah
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_siuPoleB hKah
  let ell : ℕ := ⌈(n : ℝ) * B⌉₊
  have hell : (n : ℝ) * B ≤ (ell : ℝ) := Nat.le_ceil _
  obtain ⟨K₀, hK₀, hgen⟩ := exists_positivePower_baseGeneration_ge G hG θG hθG hKah ell
  refine ⟨ell + K₀, by omega, fun d hd p => ?_⟩
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hd' : ell + K₀ + c = ell + (K₀ + c) := by omega
  rw [hd']
  have hne : ∑ a, D.χ a p ≠ 0 := by rw [D.sum_χ p]; exact one_ne_zero
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hpa := D.tsupport_χ a (subset_tsupport _ ha)
  have hx : p ∈ (D.chartX a).val.source := hpa.1
  have hp : (D.chartX a).val p ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a / 4) :=
    ball_subset_closedBall hpa.2
  obtain ⟨mω, hmω, hBm⟩ := hBa a
  have hφ := isThetaPshPotential_criticalPointWeight hn D hKah hB0 a hmω hBm hx hp
  have hsemi : (((ell : ℝ) - (n : ℝ) * B) • θG).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr hell)
  have hphi := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hφ.1 hsemi
  have hform : ((n : ℝ) * B) • θG + ((ell : ℝ) - (n : ℝ) * B) • θG = (ell : ℝ) • θG := by module
  rw [hform] at hphi
  have hφell : IsThetaPshPotential ((ell : ℝ) • θG).val (criticalPointWeight D a p) := ⟨hphi, hφ.2⟩
  have hgg := hgen (K₀ + c) (Nat.le_add_right _ _) (criticalPointWeight D a p) hφell
  rwa [multiplierIdeal_criticalPointWeight_eq_pointIdeal hn D hKah hB0 a hmω hBm hx hp] at hgg

/-- Every power `L^d`, `d ≥ d₀`, of a positive bundle is base-point free. -/
theorem exists_positivePower_sections_nonvanishing_ge [CompactSpace X] (hn : 0 < n)
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG)
    (hKah : θG.val.IsKahler) :
    ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ q : X,
      ∃ s : HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber, s q ≠ 0 := by
  obtain ⟨d₀, hd₀, hgen⟩ := exists_positivePower_generates_pointIdeals_ge hn G hG θG hθG hKah
  exact ⟨d₀, hd₀, fun d hd q => exists_section_nonzero_of_pointIdeals_generation _ hn (hgen d hd) q⟩

/-- Bertini in every large power: for every `d ≥ d₀` there is a finite generating family of
sections of `L^d` whose holomorphic map to projective space has a smooth hyperplane member. -/
theorem exists_positivePower_smoothMember_ge [CompactSpace X] (hn : 0 < n)
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG)
    (hKah : θG.val.IsKahler) :
    ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ d : ℕ, d₀ ≤ d → ∃ (N : ℕ)
      (s : Fin (N + 1) → HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber)
      (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N),
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) ∧
      IsSmoothHypersurfaceMember n
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) l := by
  obtain ⟨d₀, hd₀, hbpf⟩ := exists_positivePower_sections_nonvanishing_ge hn G hG θG hθG hKah
  refine ⟨d₀, hd₀, fun d hd => ?_⟩
  by_cases hX : Nonempty X
  · obtain ⟨N, b, hb⟩ := exists_finite_basis_generating (positivePower G (d - 1)) (hbpf d hd)
    let s : Fin (N + 1 + 1) → HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber :=
      Fin.cons (b 0) (fun j => b j)
    have hgen : ∀ x : X, ∃ j, s j x ≠ 0 := by
      intro x
      obtain ⟨j, hj⟩ := hb x
      exact ⟨j.succ, by simpa [s] using hj⟩
    have hp := sourceNativeFiniteSectionProjectiveMap_contMDiff (positivePower G (d - 1)) s hgen
    have hex : ∃ l : HyperplaneSpace (N + 1), IsSmoothHypersurfaceMember n
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) l := by
      by_contra h
      push Not at h
      have huniv : singularMemberSet n
          (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) = univ :=
        eq_univ_of_forall h
      have hint := interior_singularMemberSet
        (sourceNativeFiniteSectionProjectiveMap (positivePower G (d - 1)) s hgen) hp
        (Nat.le_add_left 1 N)
      rw [huniv, interior_univ] at hint
      exact univ_nonempty.ne_empty hint
    obtain ⟨l, hl⟩ := hex
    exact ⟨N + 1, s, hgen, l, hp, hl⟩
  · let s : Fin (0 + 1) → HolomorphicSections (n := n) (positivePower G (d - 1)).Fiber :=
      fun _ => 0
    have hgen : ∀ x : X, ∃ j, s j x ≠ 0 := fun x => (hX ⟨x⟩).elim
    exact ⟨0, s, hgen, affinePoint 0 0,
      sourceNativeFiniteSectionProjectiveMap_contMDiff (positivePower G (d - 1)) s hgen,
      fun x => (hX ⟨x⟩).elim⟩

/-- A positive native line has regular cuts in EVERY sufficiently large power. -/
theorem exists_nativeRegularCut_power_ge [CompactSpace X] (hn : 0 < n)
    (L : NativePositiveLine n X) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∃ D : NativeRegularCut L, D.power = d := by
  obtain ⟨d₀, hd₀, hcut⟩ := exists_positivePower_smoothMember_ge hn L.bundle L.smooth
    L.curvature L.own L.positive
  refine ⟨d₀, fun d hd => ?_⟩
  obtain ⟨N, s, hgen, l, hp, hl⟩ := hcut d hd
  exact ⟨⟨d, hd₀.trans_le hd, N, s, hgen, l, hp, hl⟩, rfl⟩

end SGPT.BDivisor.BD3
