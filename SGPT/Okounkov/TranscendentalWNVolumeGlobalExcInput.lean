import SGPT.Okounkov.TranscendentalWNVolumeGlobalMain
import SGPT.Okounkov.TranscendentalWNVolumeExcFormula

/-!
# The Legendre input of the restricted volume along `ℰ` (package WN-VF2)

Blueprint `claude-tok-wn-vf2` (node `tok-wn-vf2:exc-input`), discharging the interface
`ExcLegendreInputStatement` (`tok-wn-vf3:legendre-input`) from `tok-wn-vf:punctured` and
`tok-wn-vf:legendre-bounds`; WN21 Propositions 4.2, 4.5 and the duality of §3.

The family is `û_λ = partialLegendre u λ` for WN21's `u(x, τ) = w(x, [τ : 1]) + b log (1 + |τ|²)`
(`affineTwist` of the base potential `w`, `exists_basePotential`):

* `û_λ` is `θ`-psh (Kiselman) and concave in `λ`;
* duality: on `X × ℂ*`, `ũ = sup_{λ ∈ [0, b]} (û_λ ∘ π_X + λ log N₀ + (b - λ) log N₁ - c log W)`,
  from `u = sup_{λ ∈ [0, b]} (û_λ + λ log |τ|²)` (`partialLegendre_duality_Icc_of_thetaPsh`,
  `û_λ ≡ -∞` off `[0, b]`) and `λ log N₀ + (b - λ) log N₁ = λ log |τ|² - b log (1 + |τ|²)`;
* `û_λ ≤ (c - λ)⁺ g + (b + c) log 2` off `Z` (`partialLegendre_le_off_support`);
* `V_{θ - (c - λ)η} + (c - λ) g ≤ û_λ` (`twistEnvelope_le_partialLegendre`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Toric

/-- Adding a real constant commutes with suprema in `EReal`. -/
def erealAddCoeIso (r : ℝ) : EReal ≃o EReal where
  toFun y := y + (r : EReal)
  invFun y := y - (r : EReal)
  left_inv y := ereal_add_sub_cancel y r
  right_inv y := ereal_sub_add_cancel y r
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      change x + (r : EReal) ≤ y + (r : EReal) at h
      have := add_le_add h (le_refl ((-r : ℝ) : EReal))
      rwa [MeteredDivisorPositivity.add_coe_add_neg_coe,
        MeteredDivisorPositivity.add_coe_add_neg_coe] at this
    · intro h; exact add_le_add h le_rfl

theorem iSup₂_add_coe {S : Set ℝ} (f : ℝ → EReal) (r : ℝ) :
    (⨆ lam ∈ S, f lam) + (r : EReal) = ⨆ lam ∈ S, (f lam + (r : EReal)) := by
  have h := (erealAddCoeIso r).map_iSup₂ (fun lam (_ : lam ∈ S) => f lam)
  exact h

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

section Deformation

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- **The explicit upper bound off `Z`**: `û_λ ≤ (c - λ)⁺ g + (b + c) log 2`. -/
theorem partialLegendre_le_off_support {E : MeteredEffectiveQDivisor (m + 1) F.carrier}
    (hE : IsFirstDivisorUnitMetric F E) (hE0 : ∀ x, E.weight x ≤ 0)
    (hμ : IsNormalConeDeformation F μ) {Eℰ : MeteredEffectiveQDivisor (m + 1 + 1) 𝒳}
    (hEℰ : IsDeformationExceptionalMetric F E hμ Eℰ) {θ : ClosedRealOneOneForm (m + 1) F.carrier}
    {b c : ℝ} (hc : 0 < c) (hcb : c < b) {w : F.carrier × ProjectiveLine → EReal}
    (hwμ : ∀ z ∉ exceptionalSet F μ, w (μ z) =
        thetaPshSupremum (deformationForm F hμ.contMDiff θ b c Eℰ).val z +
          ((c * (Eℰ.weight z).toReal : ℝ) : EReal))
    (lam : ℝ) {x : F.carrier} (hx : x ∉ E.support) :
    partialLegendre (affineTwist w b) lam x ≤
      ((max (c - lam) 0 * (E.weight x).toReal + (b + c) * Real.log 2 : ℝ) : EReal) := by
  have hb : 0 < b := hc.trans hcb
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hg0 : (E.weight x).toReal ≤ 0 := EReal.toReal_nonpos (hE0 x)
  rcases le_or_gt lam c with hl | hl
  · rw [max_eq_left (by linarith)]
    have hwt : E.weight x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hE0 x)
    set g := (E.weight x).toReal with hgdef
    have hg : E.weight x = (g : EReal) := (EReal.coe_toReal hwt hx).symm
    have hτ : Complex.exp ((g : ℂ) / 2) ≠ 0 := Complex.exp_ne_zero _
    refine (iInf_le _ (⟨_, hτ⟩ : puncturedPlane)).trans ?_
    have hq := notMem_centre_affinePoint F x hτ
    have h1 := basePotential_le F hE hμ hEℰ hwμ hq
    simp only [affineTwist]
    have h2 := log_baseExceptionalWeight_affine_exp F (E := E) x hg
    have h3 := log_one_add_exp_le_of_nonpos hg0
    rw [norm_exp_half_sq, logNormSq_exp_half]
    calc w (x, affinePoint (Complex.exp ((g : ℂ) / 2))) +
          ((b * Real.log (1 + Real.exp g) : ℝ) : EReal) - ((lam * g : ℝ) : EReal)
        ≤ ((c * Real.log (baseExceptionalWeight F E (x, affinePoint (Complex.exp ((g : ℂ) / 2)))) +
            b * Real.log (1 + Real.exp g) - lam * g : ℝ) : EReal) := by
          rw [sub_eq_add_neg, sub_eq_add_neg, EReal.coe_add, EReal.coe_add, EReal.coe_neg]
          exact add_le_add (add_le_add h1 le_rfl) le_rfl
      _ ≤ (((c - lam) * g + (b + c) * Real.log 2 : ℝ) : EReal) := by
          apply EReal.coe_le_coe_iff.mpr
          nlinarith [mul_le_mul_of_nonneg_left h2 hc.le, mul_le_mul_of_nonneg_left h3 hb.le]
  · rw [max_eq_right (by linarith), zero_mul, zero_add]
    refine (partialLegendre_affineTwist_le F hE hE0 hμ hEℰ hc.le hwμ lam x).trans
      (EReal.coe_le_coe_iff.mpr ?_)
    nlinarith

/-- **`ExcLegendreInputStatement`** (the interface `tok-wn-vf3:legendre-input`):
the partial Legendre transform of WN21's `u` is a Legendre family for `(θ, b, c)`. -/
theorem excLegendreInput : ExcLegendreInputStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc
  have := compactSpace_normalCone F hμ
  have hb : 0 < b := hc.trans hcb
  have hEs : E.support = F.flag (1 : Fin (m + 2)) := hE.choose_spec.2.1
  set Θt := deformationForm F hμ.contMDiff θ b c Eℰ with hΘt
  obtain ⟨hbigβ, -⟩ := betaBig F E hE 𝒳 μ hμ Eℰ hEℰ.isDivisorMetric θ b c hc hcb hξ hξc.1
  have hCc : (deformationCentre F)ᶜ.Nonempty := by
    rw [nonempty_compl]
    intro h
    have := interior_deformationCentre F
    rw [h, interior_univ] at this
    exact univ_nonempty.ne_empty this
  obtain ⟨q₀, hq₀⟩ := hCc
  obtain ⟨z₀, -, -⟩ := exists_preimage_of_notMem_centre F hμ hq₀
  have : Nonempty 𝒳 := ⟨z₀⟩
  have hũ : IsThetaPshPotential Θt.val (thetaPshSupremum Θt.val) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum Θt
      ((SGPT.PSH.BookCurrent.isBig_iff_isBigClass _).mp hbigβ)
  obtain ⟨w, hw, hwμ⟩ := exists_basePotential F hE0 hμ hEℰ θ hc.le hũ
  have hrot := basePotential_rotation F hE hμ hEℰ hw hwμ
  have hpsh := isPullbackThetaPshPunctured_affineTwist hw.1
  have hinv := isCircleInvariant_affineTwist b hrot
  have hbot : ∀ lam, lam ∉ Icc 0 b → ∀ x, partialLegendre (affineTwist w b) lam x = ⊥ :=
    fun lam hlam x => partialLegendre_eq_bot_of_le hb.le
      (fun x τ hτ => affineTwist_le_log F hE hE0 hμ hEℰ hc.le hwμ x hτ) hlam x
  refine ⟨fun lam => partialLegendre (affineTwist w b) lam,
    { psh := fun lam _ => thetaPlurisubharmonic_partialLegendre hpsh hinv lam
      concave := fun x => isConcaveFamilyAt_partialLegendre _ _ x
      duality := ?_
      upper := ⟨(b + c) * Real.log 2, fun lam hlam x hx =>
        partialLegendre_le_off_support F hE hE0 hμ hEℰ hc hcb hwμ lam (hEs ▸ hx)⟩
      lower := ?_ }⟩
  · -- duality on `X × ℂ*`
    intro z hz0 hzinf
    set x := (μ z).1
    set p := (μ z).2
    -- `p = [τ : 1]` with `τ ≠ 0`
    obtain ⟨p', hp'⟩ := projectiveLineHomeomorph.surjective p
    induction p' using OnePoint.rec with
    | infty => exact absurd hp'.symm hzinf
    | coe τ =>
      have hτ : τ ≠ 0 := by rintro rfl; exact hz0 hp'.symm
      have hpτ : p = affinePoint τ := by rw [affinePoint_eq, hp']
      have hzE : z ∉ exceptionalSet F μ := fun h =>
        hz0 ((mem_deformationCentre_iff F).mp h).2
      obtain ⟨hWpos, hwt⟩ := weight_eq_coe_of_notMem F hE hEℰ hzE
      have hdual := partialLegendre_duality_Icc_of_thetaPsh hpsh hinv (a := 0) (b := b) x
        (fun lam hlam => hbot lam hlam x) hτ
      have hμz : μ z = (x, affinePoint τ) := by rw [← hpτ]
      have hu : affineTwist w b x τ = thetaPshSupremum Θt.val z +
          ((c * Real.log (baseExceptionalWeight F E (μ z)) + b * Real.log (1 + ‖τ‖ ^ 2) : ℝ) :
            EReal) := by
        simp only [affineTwist]
        rw [← hμz, hwμ z hzE, hwt, EReal.toReal_coe, EReal.coe_add, add_assoc]
      set r := c * Real.log (baseExceptionalWeight F E (μ z)) + b * Real.log (1 + ‖τ‖ ^ 2)
      have hcorr : ∀ lam, (excCorrection F E b c lam (μ z) : EReal) =
          ((lam * logNormSq τ : ℝ) : EReal) + ((-r : ℝ) : EReal) := by
        intro lam
        rw [← EReal.coe_add]
        congr 1
        obtain ⟨h0, h1⟩ := projectiveLogWeight_affinePoint hτ
        rw [projectiveLogWeight_eq_coe (projectiveWeight_zero_pos (hpτ ▸ hz0)),
          EReal.coe_eq_coe_iff] at h0
        have hN1 : 0 < projectiveWeight 1 (affinePoint τ) := by
          rw [(projectiveWeight_affinePoint τ).2]; positivity
        rw [projectiveLogWeight_eq_coe hN1, EReal.coe_eq_coe_iff] at h1
        simp only [excCorrection, r]
        rw [hμz]
        simp only
        rw [h0, h1]
        ring
      have key : thetaPshSupremum Θt.val z =
          (⨆ lam ∈ Icc 0 b, partialLegendre (affineTwist w b) lam x +
            ((lam * logNormSq τ : ℝ) : EReal)) + ((-r : ℝ) : EReal) := by
        rw [← hdual, hu, MeteredDivisorPositivity.add_coe_add_neg_coe]
      rw [key, iSup₂_add_coe]
      simp only [hcorr, add_assoc]
  · -- the lower bound
    intro lam hlam x hx
    have hlam' : lam ∈ Icc 0 b := ⟨hlam.1, hlam.2.trans hcb.le⟩
    have hlev : legendreLevel c lam = c - lam := by
      rw [legendreLevel]; exact max_eq_left (by linarith [hlam.2])
    have ht := legendreLevel_mem_Icc hc hlam'
    obtain ⟨-, hVt⟩ := isThetaPshPotential_thetaPshSupremum_sub_smul F hξ hξc ht
    have h := twistEnvelope_le_partialLegendre F hE hE0 hμ hEℰ hc hcb hwμ hlam' hVt x
    rw [hlev] at h
    have hwt : E.weight x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top (hE0 x)
    have hg : E.weight x = ((E.weight x).toReal : EReal) :=
      (EReal.coe_toReal hwt (by rw [hEs]; exact hx : x ∉ E.support)).symm
    refine le_of_eq_of_le ?_ h
    rw [twistEnvelope, hg, ← EReal.coe_mul, EReal.toReal_coe]

end Deformation

end SGPT.Okounkov.TranscendentalWN
