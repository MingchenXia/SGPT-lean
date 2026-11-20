import SGPT.PSH.SiuGenPole
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive

/-!
# Fixed geometric data for the uniform exponent in Siu's lemma

The chart cover, partition, volume constants, positivity constants, and
isolated-pole weights in this file are constructed from `G` before any varying
line bundle `L` is introduced.  The cover is `SiuCover μ G G`, rather than
`SiuCover μ L G`.  This is genuine geometric data, not a uniform-generation
certificate.

Blueprint: `siu-uniform-generation.tex`, nodes `siu-uniform:geometry` and
`siu-uniform:exponent`.  The source theorem still requires actual holomorphic
frames of arbitrary `L` on these fixed balls and a gluing system using those
frames.  In particular this module does not claim
`SiuGlobalUniformGenerationStatement`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- A finite cover constructed solely from the positive bundle and the smooth
positive volume.  Both bundle entries are `G`; no varying `L` occurs. -/
def fixedGeometry [CompactSpace X] {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ)
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG)
    (hKah : θG.val.IsKahler) : SiuCover μ G G :=
  Classical.choice (exists_siuCover (L := G) hμ hG hθG hKah)

section Numerical

variable {μ : Measure X} {L G : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- An explicit threshold using only the geometric entries of a cover. -/
def exponent (D : SiuCover μ L G) (s : ℝ) : ℕ :=
  1 + ∑ a, ⌈(D.lam + s * D.cG a) / D.cG a⌉₊

omit [BorelSpace X] in
theorem exponent_pos (D : SiuCover μ L G) (s : ℝ) : 0 < exponent D s := by
  unfold exponent
  omega

omit [BorelSpace X] in
/-- The explicit threshold leaves all required positive curvature after the
pole curvature `s θG` has been spent. -/
theorem goodPower_exponent (D : SiuCover μ L G) (s : ℝ) {K : ℕ}
    (hK : exponent D s ≤ K) : D.GoodPower s K := by
  refine ⟨(exponent_pos D s).trans_le hK, fun a => ?_⟩
  have hpos : 0 < D.cG a := D.cG_pos a
  have hsingle : ⌈(D.lam + s * D.cG a) / D.cG a⌉₊ ≤
      ∑ b, ⌈(D.lam + s * D.cG b) / D.cG b⌉₊ :=
    Finset.single_le_sum (f := fun b => ⌈(D.lam + s * D.cG b) / D.cG b⌉₊)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hceil : ⌈(D.lam + s * D.cG a) / D.cG a⌉₊ ≤ K := by
    unfold exponent at hK
    omega
  have hreal : (D.lam + s * D.cG a) / D.cG a ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  exact (div_le_iff₀ hpos).mp hreal

omit [BorelSpace X] in
/-- A geometric upper bound on the contraction parameter.  It uses no frame
norm or transition-function estimate. -/
theorem lam_le_of_geometric_bounds (D : SiuCover μ L G) {N : ℕ} {M A : ℝ}
    (hN : D.m ≤ N) (hM : |D.M| ≤ M) (hA : D.Aμ ≤ A) :
    D.lam ≤ 8 * (N : ℝ) ^ 2 * M * A ^ 2 + 1 := by
  have hN' : (D.m : ℝ) ≤ N := by exact_mod_cast hN
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hA0 : 0 ≤ A := D.Aμ_pos.le.trans hA
  have hAμ0 : 0 ≤ D.Aμ := D.Aμ_pos.le
  unfold SiuCover.lam
  gcongr

omit [BorelSpace X] in
/-- A threshold may be chosen from upper bounds for the geometric costs and a
positive lower bound for the Levi constants.  This estimate is valid for every
cover satisfying those numerical bounds.  It asserts no existence of fixed-ball
frames of an arbitrary line bundle. -/
theorem goodPower_of_geometric_bounds (D : SiuCover μ L G)
    {N K : ℕ} {M A c s : ℝ} (hc : 0 < c)
    (hN : D.m ≤ N) (hM : |D.M| ≤ M) (hA : D.Aμ ≤ A)
    (hcG : ∀ a, c ≤ D.cG a) (hK : 1 ≤ K)
    (hthreshold : s + (8 * (N : ℝ) ^ 2 * M * A ^ 2 + 1) / c ≤ (K : ℝ)) :
    D.GoodPower s K := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hΛ0 : 0 < 8 * (N : ℝ) ^ 2 * M * A ^ 2 + 1 := by positivity
  have hlam := lam_le_of_geometric_bounds D hN hM hA
  have hq : (8 * (N : ℝ) ^ 2 * M * A ^ 2 + 1) / c ≤ (K : ℝ) - s := by
    linarith
  have hKs0 : 0 ≤ (K : ℝ) - s := (div_pos hΛ0 hc).le.trans hq
  have hΛ : 8 * (N : ℝ) ^ 2 * M * A ^ 2 + 1 ≤ ((K : ℝ) - s) * c :=
    (div_le_iff₀ hc).mp hq
  refine ⟨hK, fun a => ?_⟩
  have hmul := mul_le_mul_of_nonneg_left (hcG a) hKs0
  nlinarith

end Numerical

section OriginalGeometry

/-- All pole and exponent constants are produced from the actual Kähler
volume of `G`.  The quantifiers occur before any varying line bundle, weight,
or power of that line bundle. -/
theorem exists_fixedGeometry_constants [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG)
    (hKah : θG.val.IsKahler) :
    ∃ D : SiuCover (IntegrationCurrent.kahlerVolume (⟨θG, hKah⟩ : KahlerBackground n X)) G G,
      ∃ B : ℝ, 0 < B ∧
        (∀ a : Fin D.m, ∃ mω : ℝ,
          (∀ w ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a), ∀ v : ComplexModel n,
            mω * ‖v‖ ^ 2 ≤ θG.val.coeff (D.chartX a) w ![v, Complex.I • v]) ∧
          2 * poleK / D.siuPoleR a ^ 2 ≤ Real.pi * B * mω) ∧
        ∀ K : ℕ, exponent D (((n : ℝ) + 3) * B) ≤ K →
          D.GoodPower (((n : ℝ) + 3) * B) K := by
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume
    (⟨θG, hKah⟩ : KahlerBackground n X)
  let D := fixedGeometry hμ G hG θG hθG hKah
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_siuPoleB hKah
  exact ⟨D, B, hB0, hBa, fun K hK => goodPower_exponent D _ hK⟩

end OriginalGeometry

section PointPoles

variable {μ : Measure X} {G : HermitianHolomorphicLineBundle.{0, 0} n X}
  (D : SiuCover μ G G)

omit [BorelSpace X] in
/-- Every point lies in one of the smaller balls of the fixed geometric cover. -/
theorem exists_pointIndex (x : X) :
    ∃ a : Fin D.m, x ∈ (D.chartX a).val.source ∧
      (D.chartX a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a / 4) := by
  have hne : ∑ a, D.χ a x ≠ 0 := by rw [D.sum_χ x]; exact one_ne_zero
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨a, D.tsupport_χ a (subset_tsupport _ ha)⟩

/-- Choose the chart using only the fixed partition and the point. -/
def pointIndex (x : X) : Fin D.m := Classical.choose (exists_pointIndex D x)

omit [BorelSpace X] in
theorem pointIndex_spec (x : X) :
    x ∈ (D.chartX (pointIndex D x)).val.source ∧
      (D.chartX (pointIndex D x)).val x ∈
        ball (ctr (n := n) (D.pt (pointIndex D x))) (D.R (pointIndex D x) / 4) :=
  Classical.choose_spec (exists_pointIndex D x)

/-- A literal pole function at an arbitrary product point, constructed without
any varying bundle or singular weight. -/
def pointPole (q₀ : X × unitDisc) : X × unitDisc → EReal :=
  D.poleP (pointIndex D q₀.1) ((D.chartX (pointIndex D q₀.1)).val q₀.1) q₀.2.val

theorem pointPole_ne_top (q₀ q : X × unitDisc) : pointPole D q₀ q ≠ ⊤ :=
  D.poleP_ne_top (ball_subset_closedBall (pointIndex_spec D q₀.1).2)
    (mem_unitDisc.mp q₀.2.property) q

theorem pointPole_le (q₀ q : X × unitDisc) :
    pointPole D q₀ q ≤ ((((n : ℝ) + 3) * Real.log 4 : ℝ) : EReal) :=
  D.poleP_le (ball_subset_closedBall (pointIndex_spec D q₀.1).2)
    (mem_unitDisc.mp q₀.2.property) q

/-- The same curvature cost controls poles at every point of the product. -/
theorem pointPole_thetaPlurisubharmonic {θG : ClosedRealOneOneForm n X}
    (hKah : θG.val.IsKahler) {B : ℝ} (hB0 : 0 < B)
    (hBa : ∀ a : Fin D.m, ∃ mω : ℝ,
      (∀ w ∈ closedBall (ctr (n := n) (D.pt a)) (D.R a), ∀ v : ComplexModel n,
        mω * ‖v‖ ^ 2 ≤ θG.val.coeff (D.chartX a) w ![v, Complex.I • v]) ∧
      2 * poleK / D.siuPoleR a ^ 2 ≤ Real.pi * B * mω)
    (q₀ : X × unitDisc) :
    ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc))
        ((((n : ℝ) + 3) * B) • θG)).val (pointPole D q₀) := by
  obtain ⟨mω, hmω, hBm⟩ := hBa (pointIndex D q₀.1)
  exact D.thetaPlurisubharmonic_poleP hKah hB0 hmω hBm
    (ball_subset_closedBall (pointIndex_spec D q₀.1).2) q₀.2.val

/-- The literal logarithmic bound in the selected fixed product chart. -/
theorem pointPole_le_logNormSq (q₀ : X × unitDisc) {q : X × unitDisc}
    (hq : q.1 ∈ (D.chartX (pointIndex D q₀.1)).val.source)
    (hd : ‖(D.chartP (pointIndex D q₀.1)).val q -
      (D.chartP (pointIndex D q₀.1)).val q₀‖ ≤ D.siuPoleR (pointIndex D q₀.1)) :
    pointPole D q₀ q ≤ (((n : ℝ) + 3 : ℝ) : EReal) *
      logNormSq ((D.chartP (pointIndex D q₀.1)).val q -
        (D.chartP (pointIndex D q₀.1)).val q₀) := by
  rw [D.chartP_apply (pointIndex D q₀.1) q₀] at hd ⊢
  exact D.poleP_le_logNormSq q₀.2.val hq hd

theorem pointPole_self (q₀ : X × unitDisc) : pointPole D q₀ q₀ = ⊥ := by
  have h := pointPole_le_logNormSq D q₀ (pointIndex_spec D q₀.1).1
    (by simpa using (D.siuPoleR_pos (pointIndex D q₀.1)).le)
  have hpos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  simpa only [sub_self, logNormSq_zero, EReal.coe_mul_bot_of_pos hpos,
    le_bot_iff] using h

end PointPoles

end SGPT.Bergman.SiuUniformGeneration
