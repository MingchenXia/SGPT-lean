import SGPT.PSH.SiuL2System
import SGPT.NAPotential.GAGAMultSiuGerms

/-!
# Hörmander-type `L²` correction on `X × Δ` with a general quasi-psh weight

Blueprint `claude-siu-l2.tex`, node `claude-siu-l2:correction`.

`prodCutoffCorrection`: let `X` be a compact complex manifold with a smooth positive volume `μ`
(`SFinite`), `L, G` holomorphic line bundles with smooth metrics, `θ = c₁(L, h_L)`,
`θ_G = c₁(G, h_G)` a Kähler form, and `s ≥ 0`.  There is `K₀` such that for every `K ≥ K₀`, every
`m > 0`, every `Φ ∈ PSH(X × Δ, p₁^*θ)` (arbitrary singularities), every `ψ_X ∈ PSH(X, s θ_G)` and
every `ψ_Δ` psh on `Δ` (both never `+∞`): if `F` is a holomorphic section of
`p₁^*(L^m ⊗ G^K)` on an open `U ⊆ X × Δ`, `χ` a smooth function with `tsupport χ ⊆ U`, locally
constant on `U` off a compact `K' ⊆ U`, and `∫_{K'} |F|² e^{-(mΦ + ψ_X + ψ_Δ)} < ∞`, then there is
a holomorphic section `S` of `p₁^*(L^m ⊗ G^K)` on all of `X × Δ` with

`∫_{X × Δ} |χF - S|² e^{-(mΦ + ψ_X + ψ_Δ)} d(μ ⊗ λ) < ∞`.

`K₀` depends only on `X, μ, L, G, h_L, h_G, s` (through the cover `SiuCover`), not on `m, Φ, ψ_X,
ψ_Δ`.  The proof: the gluing system `SiuCover.toSystem` has contraction factor `≤ 1/4`; the datum
`χF` has smooth coefficients and finite `∂̄`-energy; `DomainGluingSystem.exists_correction` gives the
correction, holomorphic because it is given near every point by a holomorphic coefficient.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.SiuL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.NAPotential.NAGaga

/-! ### Holomorphy in charts -/

section Charts

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- A function holomorphic at `c⁻¹ z` is complex differentiable at `z` when read in the chart. -/
theorem differentiableAt_comp_symm_of_holomorphicAt (c : ComplexChart N M) {g : M → ℂ}
    {z : ComplexModel N} (hz : z ∈ c.val.target) (hg : HolomorphicAt N g (c.val.symm z)) :
    DifferentiableAt ℂ (fun w => g (c.val.symm w)) z := by
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ℂ) g (c.val.symm z) := hg.self_of_nhds
  have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel N) c.val.symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) (IsManifold.subset_maximalAtlas c.property)
      hz).mdifferentiableAt (by simp)
  exact mdifferentiableAt_iff_differentiableAt.mp (h1.comp z h2)

/-- A function holomorphic on an open set of a chart's model space, read through the chart, is
holomorphic near every point of the chart's source mapped into that set. -/
theorem holomorphicAt_comp_chart' (c : ComplexChart N M) {f : ComplexModel N → ℂ}
    {V : Set (ComplexModel N)} (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) {x : M}
    (hx : x ∈ c.val.source) (hxV : c.val x ∈ V) : HolomorphicAt N (fun y => f (c.val y)) x := by
  filter_upwards [c.val.isOpen_inter_preimage hV |>.mem_nhds ⟨hx, hxV⟩] with y hy
  have hsC : ContDiffAt ℂ ∞ f (c.val y) := contDiffAt_of_differentiableOn_complex hf hV hy.2
  exact (hsC.contMDiffAt.comp y (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas c.property) hy.1)).mdifferentiableAt (by simp)

theorem HolomorphicAt.mul' {f g : M → ℂ} {x : M} (hf : HolomorphicAt N f x)
    (hg : HolomorphicAt N g x) : HolomorphicAt N (fun y => f y * g y) x := by
  filter_upwards [hf, hg] with y hfy hgy
  exact hfy.mul hgy

end Charts

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Frame transitions are holomorphic on the product. -/
theorem holomorphicAt_transition_prod {E : HermitianHolomorphicLineBundle.{0, 0} n X}
    (e e' : AtlasFrame E) {q : X × unitDisc} (hq : q.1 ∈ e.val.baseSet)
    (hq' : q.1 ∈ e'.val.baseSet) :
    HolomorphicAt (n + 1) (fun q' : X × unitDisc =>
      e'.val.continuousLinearMapAt ℂ q'.1 (e.val.symm q'.1 1)) q := by
  have := e.property
  have := e'.property
  have hX : HolomorphicAt n (fun y : X => e'.val.continuousLinearMapAt ℂ y (e.val.symm y 1)) q.1 :=
    SGPT.NAPotential.GAGAMult.holomorphicAt_coef_of_mdifferentiableOn e'.val e.val.open_baseSet
      (by
        have h := SGPT.NAPotential.GAGAMult.isHolomorphicSectionOn_smul_frame (n := n) e.val
          (g := fun _ => (1 : ℂ)) (U := e.val.baseSet) (fun _ hy => hy)
          (fun y _ => mdifferentiableAt_const (I := 𝓘(ℂ, ComplexModel n)) (I' := 𝓘(ℂ, ℂ)))
        simpa using h) hq hq'
  have hfst : ContMDiff 𝓘(ℂ, ComplexModel (n + 1)) 𝓘(ℂ, ComplexModel n) ∞
      (Prod.fst : X × unitDisc → X) := contMDiff_fst (n := n) (m := 1)
  filter_upwards [hfst.continuous.continuousAt.eventually hX] with y hy
  exact hy.comp y (hfst.mdifferentiableAt (by simp))

variable [MeasurableSpace X] [BorelSpace X]

namespace SiuCover

variable {μ : Measure X} {L G : HermitianHolomorphicLineBundle.{0, 0} n X} (D : SiuCover μ L G)

section System

variable [SFinite μ] (hL : IsSourceSmoothHermitianMetric L)
  (hG : IsSourceSmoothHermitianMetric G) {θ θG : ClosedRealOneOneForm n X}
  (hθ : IsOwnFirstChernForm L θ) (hθG : IsOwnFirstChernForm G θG) {s : ℝ} {K m : ℕ}
  (hK : D.GoodPower s K) (hm : 0 < m) {Φ : X × unitDisc → EReal}
  (hΦ : IsThetaPshPotential
    (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ)
  {ψX : X → EReal} (hψX : ThetaPlurisubharmonic (s • θG).val ψX) (hψXt : ∀ x, ψX x ≠ ⊤)
  {ψT : ComplexModel 1 → EReal} (hψT : PlurisubharmonicOn ψT (ball 0 1)) (hψTt : ∀ t, ψT t ≠ ⊤)

include hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt in
/-- **The contraction factor is at most `1/4`.** -/
theorem kappa_toSystem_le :
    (D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt).kappa ≤ ENNReal.ofReal (1 / 4) := by
  simp only [DomainGluingSystem.kappa, toSystem, Fintype.card_fin]
  have hlam := D.lam_pos
  have hA := D.Aμ_pos
  calc (D.m : ℝ≥0∞) * (ENNReal.ofReal ((D.m : ℝ) * D.M) * (ENNReal.ofReal D.Aμ *
        (ENNReal.ofReal D.Aμ * ENNReal.ofReal (2 / D.lam))))
      ≤ ENNReal.ofReal (D.m : ℝ) * (ENNReal.ofReal ((D.m : ℝ) * |D.M|) * (ENNReal.ofReal D.Aμ *
        (ENNReal.ofReal D.Aμ * ENNReal.ofReal (2 / D.lam)))) := by
        rw [ENNReal.ofReal_natCast]
        gcongr
        exact le_abs_self _
    _ = ENNReal.ofReal ((D.m : ℝ) * ((D.m : ℝ) * |D.M| * (D.Aμ * (D.Aμ * (2 / D.lam))))) := by
        rw [← ENNReal.ofReal_mul hA.le, ← ENNReal.ofReal_mul hA.le,
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (D.m : ℝ) * |D.M|),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (D.m : ℝ))]
    _ ≤ ENNReal.ofReal (1 / 4) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hle : 8 * ((D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2) ≤ D.lam := by
          rw [lam]; linarith
        have : (D.m : ℝ) * ((D.m : ℝ) * |D.M| * (D.Aμ * (D.Aμ * (2 / D.lam)))) =
            2 * ((D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2) / D.lam := by
          field_simp
        rw [this, div_le_iff₀ hlam]
        linarith

include hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt in
/-- **A section given locally by holomorphic coefficients is holomorphic.** -/
theorem isHolomorphicProdSectionOn_of_local
    (S : (q : X × unitDisc) → (twistedPower L (positivePower G (K - 1)) m).Fiber q.1)
    (hS : ∀ a, ∃ σ : ComplexModel (n + 1) → ℂ,
      DifferentiableOn ℂ σ ((D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt).domr a) ∧
      ∀ q ∈ (D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt).small a,
        S q = σ ((D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt).chart a q) •
          (D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt).frame a q) :
    IsHolomorphicProdSectionOn (twistedPower L (positivePower G (K - 1)) m) S univ := by
  set GS := D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt with hGS
  intro q _ e hqe
  have := e.property
  obtain ⟨a, ha⟩ := GS.cover q
  have hqs : q ∈ GS.small a := GS.smaller_subset_small a ha
  obtain ⟨σ, hσ, hSa⟩ := hS a
  have hq1 := D.mem_of_chartP hqs.1 (GS.domr_sub a hqs.2)
  have hEa : q.1 ∈ (D.frameE K m a).val.baseSet := D.mem_frameE_baseSet K m hq1.1 hq1.2
  have h1 : HolomorphicAt (n + 1) (fun q' => σ ((D.chartP a).val q')) q :=
    holomorphicAt_comp_chart' (D.chartP a) (GS.isOpen_domr a) hσ hqs.1 hqs.2
  have h2 := holomorphicAt_transition_prod (D.frameE K m a) e hEa hqe
  refine (HolomorphicAt.mul' h1 h2).congr ?_
  have hO : IsOpen (GS.small a ∩ Prod.fst ⁻¹' e.val.baseSet) :=
    (GS.isOpen_small a).inter (e.val.open_baseSet.preimage continuous_fst)
  filter_upwards [hO.mem_nhds ⟨hqs, hqe⟩] with q' hq'
  change σ ((D.chartP a).val q') * e.val.continuousLinearMapAt ℂ q'.1
      ((D.frameE K m a).val.symm q'.1 1) = e.val.continuousLinearMapAt ℂ q'.1 (S q')
  rw [hSa q' hq'.1, map_smul, smul_eq_mul]
  rfl

section Datum

variable {U : Set (X × unitDisc)} (hU : IsOpen U)
  {F : (q : X × unitDisc) → (twistedPower L (positivePower G (K - 1)) m).Fiber q.1}
  (hF : IsHolomorphicProdSectionOn (twistedPower L (positivePower G (K - 1)) m) F U)
  {χ : X × unitDisc → ℝ} (hχ : ChartSmooth (n := n + 1) χ) (hχU : tsupport χ ⊆ U)
  {K' : Set (X × unitDisc)} (hK'U : K' ⊆ U) (hconst : ∀ q ∈ U \ K', ∀ᶠ q' in 𝓝 q, χ q' = χ q)
include hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt hU hF hχ hχU hK'U hconst

/-- The coefficient of `F` is holomorphic over `U`. -/
theorem differentiableOn_locCoef_F (l : Fin D.m) :
    DifferentiableOn ℂ ((D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt).locCoef l F)
      (prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∩ (D.chartP l).val.symm ⁻¹' U) := by
  intro w hw
  have hwt := D.prodDom_subset_target l hw.1
  have hq1 : ((D.chartP l).val.symm w).1 ∈ (D.frameE K m l).val.baseSet := by
    rw [D.symm_fst hw.1]
    have hz : projX n w ∈ ball (ctr (n := n) (D.pt l)) (D.R l) := hw.1.1
    have hs : (D.chartX l).val.symm (projX n w) ∈ (D.chartX l).val.source :=
      (D.chartX l).val.map_target (D.ball_subset_targetX l hz)
    exact D.mem_frameE_baseSet K m hs
      (by rw [(D.chartX l).val.right_inv (D.ball_subset_targetX l hz)]; exact hz)
  exact (differentiableAt_comp_symm_of_holomorphicAt (D.chartP l) hwt
    (hF _ hw.2 (D.frameE K m l) hq1)).differentiableWithinAt

/-- A uniform bound for `|∂̄(χ ∘ z_l⁻¹)|²` over the compact `K'`. -/
theorem exists_bound_dbar_χ (hK' : IsCompact K') (l : Fin D.m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1,
      (D.chartP l).val.symm z ∈ K' →
        dbarNormSq (fun z => ((χ ((D.chartP l).val.symm z) : ℝ) : ℂ)) z ≤ C := by
  -- `K'` lies over a smaller disc
  obtain ⟨ρ, hρ1, hρK⟩ : ∃ ρ : ℝ, ρ < 1 ∧ ∀ q ∈ K', ‖q.2.val‖ ≤ ρ := by
    rcases K'.eq_empty_or_nonempty with h | h
    · exact ⟨0, one_pos, fun q hq => by rw [h] at hq; exact absurd hq (notMem_empty _)⟩
    obtain ⟨q₀, hq₀, hmax⟩ := hK'.exists_isMaxOn h
      ((continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).continuousOn)
    exact ⟨‖q₀.2.val‖, mem_unitDisc.mp q₀.2.property, fun q hq => hmax hq⟩
  set Cl : Set (ComplexModel (n + 1)) :=
    (prodL n) '' (closedBall (ctr (n := n) (D.pt l)) (D.R l) ×ˢ closedBall (0 : ComplexModel 1) ρ)
    with hCl
  have hClc : IsCompact Cl :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (prodL n).continuous
  have hClt : Cl ⊆ (D.chartP l).val.target := by
    rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    rw [pChart_target, mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨(D.hball l ((closedBall_subset_ball (by linarith [D.R_pos l])) hz)).1, ?_⟩
    rw [mem_closedBall_zero_iff] at ht
    exact mem_unitDisc.mpr (lt_of_le_of_lt ht hρ1)
  have hs : ContDiffOn ℝ ∞ (fun z => ((χ ((D.chartP l).val.symm z) : ℝ) : ℂ))
      (D.chartP l).val.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ (D.chartP l))
  have hcont := continuousOn_dbarNormSq (D.chartP l).val.open_target
    (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
  obtain ⟨C, hC⟩ := hClc.exists_bound_of_continuousOn (hcont.mono hClt)
  refine ⟨|C|, abs_nonneg C, fun z hz hzK => ?_⟩
  have hzCl : z ∈ Cl := by
    refine ⟨((prodL n).symm z), ⟨ball_subset_closedBall hz.1, ?_⟩, (prodL n).apply_symm_apply z⟩
    rw [mem_closedBall_zero_iff]
    have := hρK _ hzK
    rwa [D.symm_snd hz] at this
  have := hC z hzCl
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_abs_self C))

/-- Smoothness and the `∂̄`-density bound of the datum `χF`. -/
theorem datum_spec (l : Fin D.m) {C : ℝ}
    (hC : ∀ z ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1, (D.chartP l).val.symm z ∈ K' →
      dbarNormSq (fun z => ((χ ((D.chartP l).val.symm z) : ℝ) : ℂ)) z ≤ C)
    (hC0 : 0 ≤ C) {z : ComplexModel (n + 1)} (hz : z ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1) :
    ContDiffAt ℝ ∞ ((D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt).locCoef l
        (fun q => ((χ q : ℝ) : ℂ) • F q)) z ∧
      dbarNormSq ((D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt).locCoef l
        (fun q => ((χ q : ℝ) : ℂ) • F q)) z ≤
        ((D.chartP l).val.symm ⁻¹' K').indicator
          (fun z => C * ‖(D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt).locCoef l F z‖ ^ 2) z := by
  set GS := D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt
  set g := GS.locCoef l F
  have hzt : z ∈ (D.chartP l).val.target := D.prodDom_subset_target l hz
  have hχs : ContDiffAt ℝ ∞ (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hχ (D.chartP l)).contDiffAt ((D.chartP l).val.open_target.mem_nhds hzt))
  rw [GS.locCoef_real_smul l χ F]
  change ContDiffAt ℝ ∞ (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) z ∧
    dbarNormSq (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) z ≤
      ((D.chartP l).val.symm ⁻¹' K').indicator (fun z => C * ‖g z‖ ^ 2) z
  by_cases hzU : (D.chartP l).val.symm z ∈ U
  · have hO : IsOpen (prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∩ (D.chartP l).val.symm ⁻¹' U) := by
      have := (D.chartP l).val.isOpen_inter_preimage_symm hU
      have heq : prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∩ (D.chartP l).val.symm ⁻¹' U =
          prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∩
            ((D.chartP l).val.target ∩ (D.chartP l).val.symm ⁻¹' U) := by
        ext y; simp only [mem_inter_iff, mem_preimage]
        exact ⟨fun h => ⟨h.1, D.prodDom_subset_target l h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rw [heq]; exact (isOpen_prodDom _ _ _).inter this
    have hgd := D.differentiableOn_locCoef_F hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt hU hF hχ hχU
      hK'U hconst l
    have hgC : ContDiffAt ℝ ∞ g z := contDiffAt_real_of_differentiableOn_complex hgd hO ⟨hz, hzU⟩
    have hgD : DifferentiableAt ℂ g z := hgd.differentiableAt (hO.mem_nhds ⟨hz, hzU⟩)
    refine ⟨hχs.mul hgC, ?_⟩
    have hdb : ∀ e : ComplexModel (n + 1),
        dbarDir e (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) z =
        dbarDir e (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ)) z * g z := by
      intro e
      rw [dbarDir_mul (hχs.differentiableAt (by simp)) (hgC.differentiableAt (by simp)),
        dbarDir_eq_zero_of_differentiableAt hgD, mul_zero, add_zero]
    have hsq : dbarNormSq (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) z =
        dbarNormSq (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ)) z * ‖g z‖ ^ 2 := by
      unfold dbarNormSq
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [hdb, norm_mul, mul_pow]
    rw [hsq]
    by_cases hzK : (D.chartP l).val.symm z ∈ K'
    · rw [indicator_of_mem (show z ∈ (D.chartP l).val.symm ⁻¹' K' from hzK)]
      exact mul_le_mul_of_nonneg_right (hC z hz hzK) (sq_nonneg _)
    · rw [indicator_of_notMem (show z ∉ (D.chartP l).val.symm ⁻¹' K' from hzK)]
      have hloc : ∀ᶠ y in 𝓝 z, χ ((D.chartP l).val.symm y) = χ ((D.chartP l).val.symm z) :=
        ((D.chartP l).val.continuousAt_symm hzt).eventually (hconst _ ⟨hzU, hzK⟩)
      have h0 : dbarNormSq (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ)) z = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [dbarDir_congr (g := fun _ => ((χ ((D.chartP l).val.symm z) : ℝ) : ℂ)), dbarDir_const,
          norm_zero]
        · norm_num
        · filter_upwards [hloc] with y hy; rw [hy]
      rw [h0, zero_mul]
  · have hns : (D.chartP l).val.symm z ∉ tsupport χ := fun h => hzU (hχU h)
    have h1 : ∀ᶠ y in 𝓝 z, χ ((D.chartP l).val.symm y) = 0 :=
      ((D.chartP l).val.continuousAt_symm hzt).eventually (notMem_tsupport_iff_eventuallyEq.mp hns)
    have heq : (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h1] with y hy; rw [hy, Complex.ofReal_zero, zero_mul]
    refine ⟨contDiffAt_const.congr_of_eventuallyEq heq, ?_⟩
    have h0 : dbarNormSq (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) z = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [dbarDir_congr heq, dbarDir_const, norm_zero]
      norm_num
    rw [h0]
    exact indicator_nonneg (fun _ _ => mul_nonneg hC0 (sq_nonneg _)) z

/-- The datum `χF` has finite `∂̄`-energy in every chart. -/
theorem energy_datum_lt_top (hK' : IsCompact K')
    (hint : ∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) *
      multiplierWeight 1 (thetaP m Φ ψX ψT q) ∂(prodMeasure μ) < ⊤) (l : Fin D.m) :
    (D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt).energy l
      (fun q => ((χ q : ℝ) : ℂ) • F q) < ⊤ := by
  set GS := D.toSystem hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt
  set g := GS.locCoef l F
  obtain ⟨C, hC0, hC⟩ := D.exists_bound_dbar_χ hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt hU hF hχ hχU
    hK'U hconst hK' l
  set f : X × unitDisc → ℝ≥0∞ := K'.indicator (GS.D F) with hf
  have hB : GS.domR l = prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 := rfl
  have hpt : ∀ z ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1,
      ENNReal.ofReal (dbarNormSq (GS.locCoef l (fun q => ((χ q : ℝ) : ℂ) • F q)) z) * GS.W l z ≤
        ENNReal.ofReal C * f ((D.chartP l).val.symm z) := by
    intro z hz
    have h := (D.datum_spec hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt hU hF hχ hχU hK'U hconst l
      hC hC0 hz).2
    by_cases hzK : (D.chartP l).val.symm z ∈ K'
    · rw [indicator_of_mem (show z ∈ (D.chartP l).val.symm ⁻¹' K' from hzK)] at h
      rw [hf, indicator_of_mem hzK]
      calc ENNReal.ofReal (dbarNormSq (GS.locCoef l (fun q => ((χ q : ℝ) : ℂ) • F q)) z) * GS.W l z
          ≤ ENNReal.ofReal (C * ‖g z‖ ^ 2) * GS.W l z :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h) zero_le
        _ = ENNReal.ofReal C * GS.D F ((D.chartP l).val.symm z) := by
            rw [show GS.D F ((D.chartP l).val.symm z) = ENNReal.ofReal (‖g z‖ ^ 2) * GS.W l z from
              GS.D_chart l F (by rw [hB]; exact hz), ENNReal.ofReal_mul hC0, mul_assoc]
    · rw [indicator_of_notMem (show z ∉ (D.chartP l).val.symm ⁻¹' K' from hzK)] at h
      have h0 : dbarNormSq (GS.locCoef l (fun q => ((χ q : ℝ) : ℂ) • F q)) z = 0 :=
        le_antisymm h (dbarNormSq_nonneg _ z)
      rw [h0, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
  -- measurability of the transferred integrand
  have hKc : IsClosed K' := hK'.isClosed
  set S' : Set (ComplexModel (n + 1)) := prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∩
    (D.chartP l).val.symm ⁻¹' K' with hS'
  have hS'm : MeasurableSet S' := by
    have hO := (D.chartP l).val.isOpen_inter_preimage_symm hKc.isOpen_compl
    have heq : S' = prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 \
        ((D.chartP l).val.target ∩ (D.chartP l).val.symm ⁻¹' K'ᶜ) := by
      ext z
      simp only [hS', mem_inter_iff, mem_preimage, Set.mem_sdiff, mem_compl_iff, not_and, not_not]
      exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 (D.prodDom_subset_target l h.1)⟩⟩
    rw [heq]
    exact (isOpen_prodDom _ _ _).measurableSet.diff hO.measurableSet
  have hfm : AEMeasurable (fun z => f ((D.chartP l).val.symm z))
      (volume.restrict (prodDom (ctr (n := n) (D.pt l)) (D.R l) 1)) := by
    have hgc : ContinuousOn g S' :=
      (D.differentiableOn_locCoef_F hL hG hθ hθG hK hm hΦ hψX hψXt hψT hψTt hU hF hχ hχU hK'U
        hconst l).continuousOn.mono fun z hz => ⟨hz.1, hK'U hz.2⟩
    have hind : AEMeasurable (S'.indicator fun z => ENNReal.ofReal (‖g z‖ ^ 2) * GS.W l z)
        (volume.restrict (prodDom (ctr (n := n) (D.pt l)) (D.R l) 1)) := by
      refine (aemeasurable_indicator_iff hS'm).mpr ?_
      rw [Measure.restrict_restrict hS'm, inter_eq_left.mpr inter_subset_left]
      refine (ENNReal.measurable_ofReal.comp_aemeasurable
        ((hgc.aestronglyMeasurable hS'm).norm.aemeasurable.pow_const 2)).mul ?_
      exact (GS.aemeasurable_W l).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    refine hind.congr ((ae_restrict_iff' (isOpen_prodDom _ _ _).measurableSet).mpr
      (Eventually.of_forall fun z hz => ?_))
    show _ = f ((D.chartP l).val.symm z)
    by_cases hzK : (D.chartP l).val.symm z ∈ K'
    · rw [indicator_of_mem (show z ∈ S' from ⟨hz, hzK⟩), hf,
        indicator_of_mem hzK, show GS.D F ((D.chartP l).val.symm z) = ENNReal.ofReal (‖g z‖ ^ 2) *
          GS.W l z from GS.D_chart l F (by rw [hB]; exact hz)]
    · rw [indicator_of_notMem (show z ∉ S' from fun h => hzK h.2), hf, indicator_of_notMem hzK]
  have hDle : ∫⁻ q in K', GS.D F q ∂(prodMeasure μ) < ⊤ := by
    refine lt_of_le_of_lt (setLIntegral_mono' hKc.measurableSet fun q _ => ?_) hint
    change ENNReal.ofReal (‖F q‖ ^ 2) * (multiplierWeight 1 (thetaP m Φ ψX ψT q) *
      ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)))) ≤ _
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    calc multiplierWeight 1 (thetaP m Φ ψX ψT q) *
          ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)))
        ≤ multiplierWeight 1 (thetaP m Φ ψX ψT q) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.exp_le_one_iff, neg_nonpos]
          have := D.lam_pos
          positivity
      _ = _ := mul_one _
  calc GS.energy l (fun q => ((χ q : ℝ) : ℂ) • F q)
      ≤ ∫⁻ z in prodDom (ctr (n := n) (D.pt l)) (D.R l) 1,
          ENNReal.ofReal C * (GS.A * (f ((D.chartP l).val.symm z) * GS.dens l z)) := by
        refine setLIntegral_mono' (isOpen_prodDom _ _ _).measurableSet fun z hz => (hpt z hz).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        calc f ((D.chartP l).val.symm z) = 1 * f ((D.chartP l).val.symm z) := (one_mul _).symm
          _ ≤ (GS.A * GS.dens l z) * f ((D.chartP l).val.symm z) :=
              mul_le_mul_of_nonneg_right (GS.one_le_A_mul_dens l z (by rw [hB]; exact hz)) zero_le
          _ = _ := by ring
    _ = ENNReal.ofReal C * (GS.A * ∫⁻ q in GS.region l, f q ∂(prodMeasure μ)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ GS.A_ne_top,
          DomainGluingSystem.region, GS.map_measure l f hfm]
        rfl
    _ ≤ ENNReal.ofReal C * (GS.A * ∫⁻ q in K', GS.D F q ∂(prodMeasure μ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ zero_le) zero_le
        rw [← lintegral_indicator hKc.measurableSet]
        exact setLIntegral_le_lintegral _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top
        (lt_top_iff_ne_top.mpr GS.A_ne_top) hDle)

end Datum

end System

end SiuCover

/-- **Hörmander-type `L²` correction on `X × Δ` with a general quasi-psh weight**
(`claude-siu-l2:correction`).  `X` compact, `μ` a smooth positive volume, `L, G` with smooth
metrics, `θ = c₁(L, h_L)`, `θ_G = c₁(G, h_G)` Kähler, `s ∈ ℝ`.  There is `K₀` such that for all
`K ≥ K₀`, `m > 0`, `Φ ∈ PSH(X × Δ, p₁^*θ)`, `ψ_X ∈ PSH(X, s θ_G)` and `ψ_Δ` psh on `Δ` (never `+∞`),
a cut-off `χF` of a holomorphic section `F` of `p₁^*(L^m ⊗ G^K)` over an open `U` (`χ` locally
constant on `U` off a compact `K' ⊆ U` with `∫_{K'} |F|² e^{-(mΦ + ψ_X + ψ_Δ)} < ∞`) is corrected to
a holomorphic section `S` over all of `X × Δ` with `∫_{X × Δ} |χF - S|² e^{-(mΦ + ψ_X + ψ_Δ)} < ∞`. -/
theorem prodCutoffCorrection [CompactSpace X] {μ : Measure X} [SFinite μ]
    (hμ : IsSmoothPositiveVolume (n := n) μ) {L G : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hG : IsSourceSmoothHermitianMetric G)
    {θ θG : ClosedRealOneOneForm n X} (hθ : IsOwnFirstChernForm L θ)
    (hθG : IsOwnFirstChernForm G θG) (hKah : θG.val.IsKahler) (s : ℝ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ m : ℕ, 0 < m →
    ∀ Φ : X × unitDisc → EReal, IsThetaPshPotential
      (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ →
    ∀ ψX : X → EReal, ThetaPlurisubharmonic (s • θG).val ψX → (∀ x, ψX x ≠ ⊤) →
    ∀ ψT : ComplexModel 1 → EReal, PlurisubharmonicOn ψT (ball 0 1) → (∀ t, ψT t ≠ ⊤) →
    ∀ U : Set (X × unitDisc), IsOpen U →
    ∀ F : (q : X × unitDisc) → (twistedPower L (positivePower G (K - 1)) m).Fiber q.1,
      IsHolomorphicProdSectionOn (twistedPower L (positivePower G (K - 1)) m) F U →
    ∀ χ : X × unitDisc → ℝ, ChartSmooth (n := n + 1) χ → tsupport χ ⊆ U →
    ∀ K' : Set (X × unitDisc), IsCompact K' → K' ⊆ U →
      (∀ q ∈ U \ K', ∀ᶠ q' in 𝓝 q, χ q' = χ q) →
      ∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) * multiplierWeight 1 (SiuCover.thetaP m Φ ψX ψT q)
        ∂(prodMeasure μ) < ⊤ →
    ∃ S : (q : X × unitDisc) → (twistedPower L (positivePower G (K - 1)) m).Fiber q.1,
      IsHolomorphicProdSectionOn (twistedPower L (positivePower G (K - 1)) m) S univ ∧
      ∫⁻ q, ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
        multiplierWeight 1 (SiuCover.thetaP m Φ ψX ψT q) ∂(prodMeasure μ) < ⊤ := by
  obtain ⟨D⟩ := exists_siuCover (L := L) hμ hG hθG hKah
  obtain ⟨K₀, hK₀⟩ := D.exists_goodPower s
  refine ⟨K₀, fun K hK m hm Φ hΦ ψX hψX hψXt ψT hψT hψTt U hU F hF χ hχ hχU K' hK' hK'U hconst
    hint => ?_⟩
  have hKg := hK₀ K hK
  set GS := D.toSystem hL hG hθ hθG hKg hm hΦ hψX hψXt hψT hψTt with hGS
  have hv : GS.IsSmooth (fun q => ((χ q : ℝ) : ℂ) • F q) := by
    intro l z hz
    obtain ⟨C, hC0, hC⟩ := D.exists_bound_dbar_χ hL hG hθ hθG hKg hm hΦ hψX hψXt hψT hψTt hU hF hχ
      hχU hK'U hconst hK' l
    exact (D.datum_spec hL hG hθ hθG hKg hm hΦ hψX hψXt hψT hψTt hU hF hχ hχU hK'U hconst l hC hC0
      hz).1.contDiffWithinAt
  have hE : GS.totalEnergy (fun q => ((χ q : ℝ) : ℂ) • F q) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun l _ =>
      D.energy_datum_lt_top hL hG hθ hθG hKg hm hΦ hψX hψXt hψT hψTt hU hF hχ hχU hK'U hconst hK'
        hint l).ne
  obtain ⟨S, hSloc, hSint⟩ := GS.exists_correction
    (D.kappa_toSystem_le hL hG hθ hθG hKg hm hΦ hψX hψXt hψT hψTt) hv hE
  refine ⟨S, D.isHolomorphicProdSectionOn_of_local hL hG hθ hθG hKg hm hΦ hψX hψXt hψT hψTt S hSloc,
    ?_⟩
  have hfin : (Fintype.card (Fin D.m) : ℝ≥0∞) *
      (GS.A * GS.K₀ (fun q => ((χ q : ℝ) : ℂ) • F q)) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr GS.A_ne_top) (lt_top_iff_ne_top.mpr (GS.K₀_ne_top hE)))
  have hlam := D.lam_pos
  calc ∫⁻ q, ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
        multiplierWeight 1 (SiuCover.thetaP m Φ ψX ψT q) ∂(prodMeasure μ)
      ≤ ∫⁻ q, ENNReal.ofReal (Real.exp D.lam) *
          GS.D (fun q => ((χ q : ℝ) : ℂ) • F q - S q) q ∂(prodMeasure μ) := by
        refine lintegral_mono fun q => ?_
        change _ ≤ ENNReal.ofReal (Real.exp D.lam) * (ENNReal.ofReal
          (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) * (multiplierWeight 1 (SiuCover.thetaP m Φ ψX ψT q) *
            ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)))))
        have h1 : 1 ≤ ENNReal.ofReal (Real.exp D.lam) *
            ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.one_le_exp_iff]
          have ht : ‖q.2.val‖ < 1 := mem_unitDisc.mp q.2.property
          have ht2 : ‖q.2.val‖ ^ 2 ≤ 1 := by
            have := norm_nonneg q.2.val
            nlinarith
          nlinarith
        calc ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
              multiplierWeight 1 (SiuCover.thetaP m Φ ψX ψT q)
            = ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
                multiplierWeight 1 (SiuCover.thetaP m Φ ψX ψT q) * 1 := (mul_one _).symm
          _ ≤ ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
                multiplierWeight 1 (SiuCover.thetaP m Φ ψX ψT q) * (ENNReal.ofReal (Real.exp D.lam) *
                ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)))) :=
              mul_le_mul_of_nonneg_left h1 zero_le
          _ = _ := by ring
    _ = ENNReal.ofReal (Real.exp D.lam) *
          ∫⁻ q, GS.D (fun q => ((χ q : ℝ) : ℂ) • F q - S q) q ∂(prodMeasure μ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hSint hfin)

end SGPT.PSH.SiuL2
