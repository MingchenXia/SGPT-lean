import SGPT.NAPotential.BJPrepDivisorialTransform
import SGPT.NAPotential.BJPrepNetMinimax
import SGPT.NAPotential.DecreasingInfimum
import SGPT.Envelopes.SourcePerturbedModelLimits
import SGPT.PSH.SourceSingularityDistanceConvergence
import SGPT.PSH.SourceGenericLelongModificationConvergence
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
import SGPT.Foundations.Analysis.Pending.DimZeroKahler

/-!
# Divisorial values of `Γ^An` along decreasing nets

Source `prop:anpreinf` (`chapter_NApotential.tex`, *The comparison theorem*): for a decreasing net
`(Γ_i)_{i ∈ I}` in `PSH^NA(X, θ)` satisfying `eq:decnetcontition`,
`(inf_i Γ_i)^An = inf_i Γ_i^An`.  By `thm:pshdetbydiv` this reduces to `X^Div`, and on
`v = t ord_E` the book's proof is: the slices `Γ_{i,τ}` decrease to `Γ_τ` with converging masses
(`lma:testcurinfcompatible`, `prop:vol_limit_model`), hence converge in `d_S` (`cor:decnetdS`),
hence `ν(Γ_τ, E) = lim_i ν(Γ_{i,τ}, E)` (`thm:Lelongcont`); then exchange the infimum with the
Legendre-type supremum in `τ` (`prop:Legendretranssup`).

We formalize this divisorial content in the Lelong-number form of `naDivisorialTransform`
(`SGPT.NAPotential.BJPrepDivisorialTransform`):

* `tendsto_presentationReader_decreasingInf`: `thm:Lelongcont` along the test-curve infimum of
  a decreasing net (`def:testcurinf`), for nets;
* `naDivisorialTransform_decreasingInf`: for every prime divisor `E` over `X` and `t > 0`,
  `(inf_i Γ_i)^An(t ord_E) = inf_i Γ_i^An(t ord_E)`.

The exchange of `inf_i` and `sup_τ` is `exists_index_legendre_le`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.BJPrep

universe u

open Set Filter
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- A background carrying a potential of positive non-pluripolar mass is big. -/
theorem isBigClass_of_sourceMass_pos (omega : KahlerBackground n M)
    {α : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH α u)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure α u hu univ) :
    IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative α)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact DimZeroKahler.isBigClass_of_dim_zero hn omega _
  · exact BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos hn omega _
      ((isThetaPSH_iff_nativeThetaPotential α u).mp hu) hpos

section Curve

variable {α : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- **`thm:Lelongcont` along a decreasing net of test curves.**  For the test-curve infimum
`Γ = inf_i Γ_i` of a decreasing net of positive `𝓘`-model test curves (`def:testcurinf`), every
slice Lelong number converges: `ν(Γ_{i,τ}, E) → ν(Γ_τ, E)` for `τ < Γ_max`. -/
theorem tendsto_presentationReader_decreasingInf (omega : KahlerBackground n M)
    (G : I → SourcePositiveIModelTestCurve α)
    (ha : ∀ i j, i ≤ j → SourceTestCurvePOrder (G j).val (G i).val)
    (hb : BddBelow (range fun i => (G i).val.max))
    (hm : SourceTestCurveInfMassCondition (fun i => (G i).val) hb)
    (p : PrimePresentation n M) {τ : ℝ}
    (hτ : τ < (SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm).val.max) :
    Tendsto (fun i => presentationReader ((G i).val.potential
        ⟨τ, hτ.trans_le (sourceTestCurveInfCutoff_le (fun i => (G i).val) hb i)⟩) p) atTop
      (𝓝 (presentationReader
        ((SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm).val.potential ⟨τ, hτ⟩)
        p)) := by
  set D := SourcePositiveIModelTestCurve.decreasingInf omega G ha hb hm with hD
  have hti : ∀ i, τ < (G i).val.max := fun i =>
    hτ.trans_le (sourceTestCurveInfCutoff_le (fun i => (G i).val) hb i)
  set u : I → M → EReal := fun i => (G i).val.potential ⟨τ, hti i⟩ with hu_def
  have hDpot : D.val.potential ⟨τ, hτ⟩ = fun x => ⨅ i, u i x := rfl
  -- masses converge (`prop:vol_limit_model`)
  set T : ClosedRealOneOneForm n M := atlasClosedFormToNative α with hT_def
  have hT0 : T + (0 : ℝ) • omega.form = T := by rw [zero_smul, add_zero]
  have hφ : ∀ i, IsThetaPshPotential (T + (0 : ℝ) • omega.form).val (u i) := fun i => by
    rw [hT0]
    exact (G i).val.native_thetaPSH _
  have hfix : ∀ i, singularityEnvelope (T + (0 : ℝ) • omega.form).val (u i) = u i := fun i => by
    rw [hT0, hT_def, ← sourceSingularityEnvelope_eq_native]
    exact (G i).val.fixedPoint _
  have hinf : IsThetaPshPotential T.val (fun x => ⨅ i, u i x) := D.val.native_thetaPSH ⟨τ, hτ⟩
  have hanti : Antitone u := fun i j hij x =>
    sourceTestCurveInfSlice_antitone omega (fun i => (G i).val) ha hb ⟨τ, hτ⟩ x hij
  have hlimM := SGPT.Envelopes.PerturbedModelLimit.tendsto_diagonalPotentialMass_iInf omega T
    (ε := fun _ : I => (0 : ℝ)) (φ := u) (fun _ => le_rfl) (fun _ _ _ => le_rfl)
    tendsto_const_nhds hanti hφ hfix hinf
  have hmass : Tendsto (fun i => sourcePotentialNonPluripolarMeasure α (u i)
      ((G i).val.thetaPSH _) univ) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure α (D.val.potential ⟨τ, hτ⟩)
        (D.val.thetaPSH ⟨τ, hτ⟩) univ)) := by
    refine hlimM.congr (fun i => ?_)
    exact sourceNA_diagonalMass_congr_form hT0 _ _
  -- convergence in `d_S` (`cor:decnetdS`)
  have hpos := D.val.mass_positive omega ⟨τ, hτ⟩
  have hbig := isBigClass_of_sourceMass_pos omega (D.val.thetaPSH ⟨τ, hτ⟩) hpos
  let w : I → SourceThetaPotentialL1 α := fun i => ⟨u i, (G i).val.thetaPSH _⟩
  let v : SourceThetaPotentialL1 α := ⟨D.val.potential ⟨τ, hτ⟩, D.val.thetaPSH ⟨τ, hτ⟩⟩
  have horder : ∀ i, SGPT.PSH.GlobalPComparison.sourcePOrder (n := n) v.val (w i).val := fun i =>
    SGPT.PSH.GlobalPComparison.sourcePOrder_of_moreSingular omega
      (D.val.native_thetaPSH ⟨τ, hτ⟩).quasiPshPotential
      ((G i).val.native_thetaPSH _).quasiPshPotential
      ⟨0, fun x _ => by
        rw [EReal.coe_zero, add_zero]
        exact iInf_le (fun i => u i x) i⟩
  have hdS := (tendsto_sourceSingularityTopology_iff_mass_of_sourcePOrder_of_positive_target
    omega α hbig atTop w v horder hpos).mpr hmass
  -- convergence of Lelong numbers (`thm:Lelongcont`)
  exact tendsto_sourceGenericLelong_comp_of_sourceSingularityTopology omega α hbig
    p.modification atTop w v hdS p.divisor

end Curve

section NA

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- **`prop:anpreinf` on `X^Div`, Lelong-number form.**  For a decreasing net `(Γ_i)` in
`PSH^NA(X, θ)` satisfying `eq:decnetcontition`, every prime divisor `E` over `X` and every
`t > 0`: `(inf_i Γ_i)^An(t ord_E) = inf_i Γ_i^An(t ord_E)`. -/
theorem naDivisorialTransform_decreasingInf (omega : KahlerBackground n M)
    (Γ : I → SourceNAPotential θ) (ha : ∀ i j, i ≤ j → SourceNAPOrder (Γ j) (Γ i))
    (hb : BddBelow (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (ω : SourceKahlerForm n M) (p : PrimePresentation n M) {t : ℝ} (ht : 0 < t) :
    naDivisorialTransform (SourceNAPotential.decreasingInf omega Γ ha hb) ω p t =
      ⨅ i, naDivisorialTransform (Γ i) ω p t := by
  apply le_antisymm
  · exact le_iInf fun i =>
      naDivisorialTransform_mono (SourceNAPotential.decreasingInf_le omega Γ ha hb i) ω p ht.le
  set K := sourceKahlerFormRepresentative ω with hK
  set G : I → SourcePositiveIModelTestCurve (sourceNAComponentBackground θ ω) :=
    fun i => (Γ i).component ω with hG
  have hGa := sourceNAFamily_component_antitone Γ ha ω
  have hGb := sourceNAFamily_component_bddBelow omega Γ hb ω
  have hGm := sourceNAFamily_component_massCondition omega Γ hb ω
  set D := SourcePositiveIModelTestCurve.decreasingInf K G hGa hGb hGm with hD
  have hcomp : (SourceNAPotential.decreasingInf omega Γ ha hb).component ω = D := rfl
  unfold naDivisorialTransform
  rw [hcomp]
  -- notation
  set m : I → ℝ := fun i => (G i).val.max with hm_def
  set m₀ : ℝ := D.val.max with hm₀_def
  set f : I → ℝ → ℝ := fun i => sliceLelong (G i).val.toSourceTestCurvePredata p with hf_def
  set F : ℝ → ℝ := sliceLelong D.val.toSourceTestCurvePredata p with hF_def
  have hm₀m : ∀ i, m₀ ≤ m i := fun i => sourceTestCurveInfCutoff_le (fun i => (G i).val) hGb i
  set TD := curveDivisorialTransform D.val.toSourceTestCurvePredata p t with hTD
  -- the transform of the infimum is a real number `R`
  have hTD_le : TD ≤ (m₀ : EReal) := by
    refine iSup₂_le fun τ h => ?_
    rw [curveDivisorialTransform_term _ p t h]
    have : 0 ≤ t * sliceLelong D.val.toSourceTestCurvePredata p τ :=
      mul_nonneg ht.le (sliceLelong_nonneg _ p τ)
    exact EReal.coe_le_coe_iff.mpr (by
      have h' : τ < m₀ := h
      linarith)
  have hTD_ge : ((m₀ - 1 - t * F (m₀ - 1) : ℝ) : EReal) ≤ TD := by
    have h : m₀ - 1 < D.val.max := by rw [← hm₀_def]; linarith
    rw [← curveDivisorialTransform_term _ p t h]
    exact le_curveDivisorialTransform _ p t h
  have hTD_ne_top : TD ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hTD_le
  have hTD_ne_bot : TD ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hTD_ge
  set R : ℝ := TD.toReal with hR_def
  have hTDR : TD = (R : EReal) := (EReal.coe_toReal hTD_ne_top hTD_ne_bot).symm
  have hR : ∀ τ < m₀, τ - t * F τ ≤ R := by
    intro τ hτ
    have h : ((τ - t * F τ : ℝ) : EReal) ≤ TD := by
      rw [hF_def, ← curveDivisorialTransform_term _ p t hτ]
      exact le_curveDivisorialTransform D.val.toSourceTestCurvePredata p t hτ
    rw [hTDR] at h
    exact EReal.coe_le_coe_iff.mp h
  -- hypotheses of the exchange lemma
  have hmanti : ∀ i j, i ≤ j → m j ≤ m i := fun i j hij => (hGa i j hij).cutoff_le
  have hmlim : ∀ ε > 0, ∃ i, m i ≤ m₀ + ε := by
    intro ε hε
    obtain ⟨b, ⟨i, rfl⟩, hb'⟩ := exists_lt_of_csInf_lt (range_nonempty m)
      (show sInf (range m) < m₀ + ε by
        change m₀ < m₀ + ε
        linarith)
    exact ⟨i, hb'.le⟩
  have hmono : ∀ i, MonotoneOn (f i) (Iio (m i)) := fun i =>
    sliceLelong_monotoneOn (G i).val.toSourceTestCurvePredata p
  have hnonneg : ∀ i τ, 0 ≤ f i τ := fun i τ => sliceLelong_nonneg _ p τ
  have hfanti : ∀ i j, i ≤ j → ∀ τ < m₀, f i τ ≤ f j τ := by
    intro i j hij τ hτ
    obtain ⟨hcut, hle⟩ := (sourceTestCurvePOrder_iff K (G j).val (G i).val).mp (hGa i j hij)
    have hτj : τ < (G j).val.max := hτ.trans_le (hm₀m j)
    have hτi : τ < (G i).val.max := hτ.trans_le (hm₀m i)
    simp only [hf_def]
    rw [sliceLelong_of_lt _ p hτi, sliceLelong_of_lt _ p hτj]
    exact ENNReal.toReal_mono (presentationReader_ne_top ((G j).val.thetaPSH _) p)
      (presentationReader_anti (hle τ hτj) p)
  have hlim : ∀ τ < m₀, ∀ ε > 0, ∃ i, F τ ≤ f i τ + ε := by
    intro τ hτ ε hε
    have hT := tendsto_presentationReader_decreasingInf K G hGa hGb hGm p (τ := τ) hτ
    have hfin := presentationReader_ne_top (D.val.thetaPSH ⟨τ, hτ⟩) p
    have hT' := (ENNReal.tendsto_toReal hfin).comp hT
    have hev := hT'.eventually_const_lt (show F τ - ε < (presentationReader
      (D.val.potential ⟨τ, hτ⟩) p).toReal by
        rw [hF_def, sliceLelong_of_lt _ p hτ]
        linarith)
    obtain ⟨i, hi⟩ := hev.exists
    refine ⟨i, ?_⟩
    simp only [Function.comp_apply] at hi
    simp only [hf_def]
    rw [sliceLelong_of_lt _ p (hτ.trans_le (hm₀m i))]
    linarith
  -- conclusion
  rw [hTDR]
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hRr, hr⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  have hRr' : R < r := EReal.coe_lt_coe_iff.mp hRr
  obtain ⟨i, hi⟩ := exists_index_legendre_le (I := I) ht hm₀m hmanti hmlim hmono hnonneg hfanti
    hlim hR (δ := r - R) (by linarith)
  have hTi : curveDivisorialTransform (G i).val.toSourceTestCurvePredata p t ≤ (r : EReal) := by
    refine iSup₂_le fun τ h => ?_
    rw [curveDivisorialTransform_term _ p t h]
    exact EReal.coe_le_coe_iff.mpr (by
      have := hi τ h
      linarith)
  exact absurd ((iInf_le _ i).trans hTi) (not_le.mpr hr)

end NA

end SGPT.NAPotential.BJPrep
