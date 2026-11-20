import SGPT.NAPotential.SiuGenStep
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive

/-!
# Siu's global generation on `X × Δ` (`lma:Siu_global_uniform_generatedness`, `k = k(X, G, L)`)

Blueprint `claude-siu-gen.tex`, node `claude-siu-gen:main`.

Source `lma:Siu_global_uniform_generatedness` (`chapter_NApotential.tex`, `subsubsec:analytic_alg`):
*for `Φ ∈ PSH(X × Δ, p₁^*θ)` and `G` ample there is `k > 0`, depending only on `X` and `G`, such that
`p₁^*(G^k ⊗ L^m) ⊗ 𝓘(mΦ)` is globally generated for all `m > 0`.*

`siuGlobalGeneration_prod` proves the statement with `k` depending on `X`, `G` **and `L`** (with its
metric), but not on `Φ` or `m` (`SiuGlobalGenerationStatementL`): for every `G` with a smooth metric
of Kähler curvature and every `L` with a smooth metric, `θ = c₁(L, h_L)`, there is `k > 0` such that
for every `Φ ∈ PSH(X × Δ, p₁^*θ)` and every `m > 0` the sheaf `p₁^*(L^m ⊗ G^k) ⊗ 𝓘(mΦ)` is globally
generated on `X × Δ` (`IsProdGloballyGenerated`, the reading of the statement file
`SiuGenStatement`).  The book's uniformity of `k` in `L` (`SiuGlobalUniformGenerationStatement`)
remains open: the constant of the `L²` correction depends on `L` through the frame domains of a
finite chart cover of `X`.  The only use of the lemma in the book (`prop:PhiinducePSH`) has `L`
fixed.

Proof: `μ` the Kähler volume of `θ_G`, `D` a cover (`exists_siuCover`), `B` the uniform pole constant
of `D`, `K₀` the constant of `prodCutoffCorrectionGen` for `s = (n+3) B`; `k = max K₀ 1`.  Siu's step
(`exists_section_mod_maximal_prod`) gives, for every germ `g ∈ 𝓘(mΦ)_{q₀}`, a global section `S` of
`p₁^*E ⊗ 𝓘(mΦ)` with `g ≡ e(S) mod 𝔪_{q₀} 𝓘(mΦ)_{q₀}`; Nakayama's lemma in `𝒪_{X × Δ, q₀}`
(`isProdGloballyGenerated_of_step`) concludes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.SiuGen

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga SGPT.NAPotential.GAGAMult
open SGPT.Okounkov SGPT.PSH.IdealRestriction

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Global generation from Siu's step** (Nakayama).  If every germ `g ∈ 𝓘(cΦ)_{q₀}` is congruent,
in every frame `e` of `E` at `q₀.1`, to the `e`-coefficient of a global section of
`p₁^*E ⊗ 𝓘(cΦ)` modulo `𝔪_{q₀} 𝓘(cΦ)_{q₀}` (the centred coordinates of a chart at `q₀` times
germs of `𝓘(cΦ)_{q₀}`), then `p₁^*E ⊗ 𝓘(cΦ)` is globally generated. -/
theorem isProdGloballyGenerated_of_step {E : HermitianHolomorphicLineBundle.{0, 0} n X} {c : ℝ}
    {Φ : X × unitDisc → EReal}
    (hstep : ∀ (q₀ : X × unitDisc) (e : AtlasFrame E), q₀.1 ∈ e.val.baseSet →
      ∀ g : X × unitDisc → ℂ, (multiplierIdeal (n := n + 1) c Φ).mem q₀ g →
      ∃ S : (q : X × unitDisc) → E.Fiber q.1,
        IsProdSectionIn E (multiplierIdeal (n := n + 1) c Φ) S ∧
        ∃ d : ComplexChart (n + 1) (X × unitDisc), q₀ ∈ d.val.source ∧
        ∃ h : Fin (n + 1) → X × unitDisc → ℂ,
          (∀ i, (multiplierIdeal (n := n + 1) c Φ).mem q₀ (h i)) ∧
          ∀ᶠ q in 𝓝 q₀, g q - e.val.continuousLinearMapAt ℂ q.1 (S q) =
            ∑ i, centredCoords (d.val q₀) i (d.val q) * h i q) :
    IsProdGloballyGenerated E (multiplierIdeal (n := n + 1) c Φ) := by
  intro q₀ e he g hg
  have := e.property
  set Sp : (X × unitDisc → ℂ) → Prop := fun h => ∃ S : (q : X × unitDisc) → E.Fiber q.1,
    IsProdSectionIn E (multiplierIdeal (n := n + 1) c Φ) S ∧
      h = fun q' => e.val.continuousLinearMapAt ℂ q'.1 (S q') with hSp
  suffices hI : stalkIdeal (multiplierIdeal (n := n + 1) c Φ) q₀ ≤ spanGerms Sp q₀ from
    isInSpanAt_of_mk_mem_spanGerms hg.1 (hI (mk_mem_stalkIdeal hg.1 hg))
  apply le_of_le_sup_maximalIdeal_smul
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨g', hg', hmem, rfl⟩
  obtain ⟨S, hS, d, hq₀d, h, hh, hid⟩ := hstep q₀ e he g' hmem
  have hsx : HolomorphicAt (n + 1) (fun q => e.val.continuousLinearMapAt ℂ q.1 (S q)) q₀ :=
    hS.1 q₀ (mem_univ _) e he
  have hci : ∀ i, HolomorphicAt (n + 1) (fun q => centredCoords (d.val q₀) i (d.val q)) q₀ :=
    fun i => holomorphicAt_chartCoord d hq₀d i
  have hhi : ∀ i, HolomorphicAt (n + 1) (h i) q₀ := fun i => (hh i).1
  have hsum : HolomorphicAt (n + 1)
      (fun q => ∑ i, centredCoords (d.val q₀) i (d.val q) * h i q) q₀ :=
    HolomorphicAt.sum _ fun i _ => (hci i).mul (hhi i)
  have hlhs : HolomorphicAt (n + 1)
      (fun q => g' q - e.val.continuousLinearMapAt ℂ q.1 (S q)) q₀ :=
    (hg'.add (hsx.mono fun y hy => hy.neg)).congr (Eventually.of_forall fun y => by
      simp [sub_eq_add_neg])
  have hgerm : NativeHolGerm.mk g' hg' - NativeHolGerm.mk _ hsx =
      ∑ i, NativeHolGerm.mk _ (hci i) * NativeHolGerm.mk (h i) (hhi i) := by
    rw [← mk_sum_mul _ _ hci hhi hsum]
    have hl : NativeHolGerm.mk g' hg' - NativeHolGerm.mk _ hsx = NativeHolGerm.mk _ hlhs := rfl
    rw [hl]
    exact NativeHolGerm.mk_eq_mk_iff.mpr hid
  have hrepr : NativeHolGerm.mk g' hg' = NativeHolGerm.mk _ hsx +
      ∑ i, NativeHolGerm.mk _ (hci i) * NativeHolGerm.mk (h i) (hhi i) := by
    rw [← hgerm, add_sub_cancel]
  rw [hrepr]
  refine Submodule.add_mem_sup (mk_mem_spanGerms hsx ⟨S, hS, rfl⟩) ?_
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← smul_eq_mul]
  exact Submodule.smul_mem_smul (mk_mem_maximalIdeal (hci i) (centredCoords_self _ i))
    (mk_mem_stalkIdeal (hhi i) (hh i))

variable (n X) in
/-- **`lma:Siu_global_uniform_generatedness` with `k = k(X, G, L)`** (statement).  For every `G` with
a smooth metric of Kähler curvature `θ_G` and every holomorphic line bundle `L` with a smooth
metric, `θ = c₁(L, h_L)`, there is `k > 0` such that for every `Φ ∈ PSH(X × Δ, p₁^*θ)` and every
`m > 0` the sheaf `p₁^*(G^k ⊗ L^m) ⊗ 𝓘(mΦ)` is globally generated on `X × Δ`.  This differs from
the book's statement (`SiuGlobalUniformGenerationStatement`) only in the order of the quantifiers
`∃ k` and `∀ L`. -/
def SiuGlobalGenerationStatementL [CompactSpace X] : Prop :=
  ∀ G : HermitianHolomorphicLineBundle.{0, 0} n X, IsSourceSmoothHermitianMetric G →
  ∀ θG : ClosedRealOneOneForm n X, IsOwnFirstChernForm G θG → θG.val.IsKahler →
  ∀ L : HermitianHolomorphicLineBundle.{0, 0} n X, IsSourceSmoothHermitianMetric L →
  ∀ θ : ClosedRealOneOneForm n X, IsOwnFirstChernForm L θ →
  ∃ k : ℕ, 0 < k ∧
  ∀ Φ : X × unitDisc → EReal, IsThetaPshPotential
    (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ →
  ∀ m : ℕ, 0 < m →
    IsProdGloballyGenerated (twistedPower L (positivePower G (k - 1)) m)
      (multiplierIdeal (n := n + 1) (m : ℝ) Φ)

/-- **Siu's global generation on `X × Δ`, for all large `k`** (`claude-siu-gen:main`): there is
`k₀ > 0`, depending on `X`, `G` and `L` (with their metrics) but not on `Φ` or `m`, such that for
every `k ≥ k₀`, every `Φ ∈ PSH(X × Δ, p₁^*θ)` and every `m > 0` the sheaf
`p₁^*(G^k ⊗ L^m) ⊗ 𝓘(mΦ)` is globally generated on `X × Δ`. -/
theorem siuGlobalGeneration_prod_of_le [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG) (hKah : θG.val.IsKahler)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (θ : ClosedRealOneOneForm n X) (hθ : IsOwnFirstChernForm L θ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
    ∀ Φ : X × unitDisc → EReal, IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ →
    ∀ m : ℕ, 0 < m →
      IsProdGloballyGenerated (twistedPower L (positivePower G (k - 1)) m)
        (multiplierIdeal (n := n + 1) (m : ℝ) Φ) := by
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  set ωb : KahlerBackground n X := ⟨θG, hKah⟩ with hωb
  have hμ : IsSmoothPositiveVolume (n := n) (IntegrationCurrent.kahlerVolume ωb) :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  obtain ⟨D⟩ := exists_siuCover (L := L) hμ hG hθG hKah
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_siuPoleB hKah
  obtain ⟨K₀, hK₀⟩ := prodCutoffCorrectionGen hμ hL hG hθ hθG hKah (((n : ℝ) + 3) * B)
  refine ⟨max K₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun k hk Φ hΦ m hm => ?_⟩
  have hcorr : HasProdCorrection (IntegrationCurrent.kahlerVolume ωb)
      (twistedPower L (positivePower G (k - 1)) m) m Φ ((((n : ℝ) + 3) * B) • θG) :=
    fun Ψ hΨ hΨt U hU F hF χ hχ hχU K' hK' hK'U hconst hint =>
      hK₀ k ((le_max_left _ _).trans hk) m hm Φ hΦ Ψ hΨ hΨt U hU F hF χ hχ hχU K' hK' hK'U
        hconst hint
  refine isProdGloballyGenerated_of_step fun q₀ e he g hg => ?_
  obtain ⟨S, hS, a, hq₀, h, hh, hid⟩ :=
    exists_section_mod_maximal_prod hμ D hL hθ hKah hB0 hBa hm hΦ hcorr q₀ e he hg
  exact ⟨S, hS, D.chartP a, hq₀, h, hh, hid⟩

/-- **Siu's global generation on `X × Δ`** (`claude-siu-gen:main`): source
`lma:Siu_global_uniform_generatedness` with `k` depending on `X`, `G` and `L` (uniform in `Φ` and
`m`). -/
theorem siuGlobalGeneration_prod [CompactSpace X] : SiuGlobalGenerationStatementL n X := by
  intro G hG θG hθG hKah L hL θ hθ
  obtain ⟨k₀, hk₀, h⟩ := siuGlobalGeneration_prod_of_le G hG θG hθG hKah L hL θ hθ
  exact ⟨k₀, hk₀, h k₀ le_rfl⟩

end SGPT.NAPotential.SiuGen
