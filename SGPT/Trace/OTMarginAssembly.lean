import SGPT.Trace.OTMarginOverlap
import SGPT.Bergman.SourceMultiplierSectionGlobalMass
import SGPT.Foundations.Analysis.Pending.ChartPartition

/-!
# Assembly: a global section with the prescribed restriction

Blueprint `claude-ot3.tex`, node `claude-ot3:assembly`.

`exists_section_of_patches`: given local packages (`MarginPatch`) at all points of a compact
`W`, cover `W` by finitely many of them, glue the local sections with a chart-smooth partition of
unity into a datum `v₀` whose `∂̄`-energy for the weight `e^{-kφ'}`,
`e^{-kφ'} = e^{-kψ} e^{-rΛ}`, is finite (`energy_gluedDatum_le` and the overlap estimates), correct
it with `GluingSystem.exists_correction` to a global holomorphic section `σ`, and show
`∫ |σ|² e^{-kψ} < ∞` and `σ = s` on `W` (the correction `σ - S_j` has
`∫ |σ - S_j|² e^{-rΛ} < ∞` near `W`, so it vanishes there by `MarginPatch.crit`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTMargin

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.QuantizationDraft
  SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- `‖∑_a v_a‖² ≤ |ι| ∑_a ‖v_a‖²` in a normed space. -/
theorem norm_sum_sq_le_card {E : Type*} [SeminormedAddCommGroup E] {ι : Type*} [Fintype ι]
    (v : ι → E) : ‖∑ a, v a‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ a, ‖v a‖ ^ 2 := by
  have h1 : ‖∑ a, v a‖ ≤ ∑ a, ‖v a‖ := norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖v a‖)
  calc ‖∑ a, v a‖ ^ 2 ≤ (∑ a, ‖v a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by simpa using h2

/-- A function continuous on an open set, restricted to a closed subset, is measurable. -/
theorem measurable_indicator_closed_of_continuousOn {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {U K : Set Y} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : Y → ℝ≥0∞} (hf : ContinuousOn f U) : Measurable (K.indicator f) := by
  have h1 := measurable_indicator_of_continuousOn' hU hf
  have h2 : K.indicator f = K.indicator (U.indicator f) := by
    funext x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem (hKU hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  rw [h2]
  exact h1.indicator hK.measurableSet

variable [CompactSpace X] {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}

/-- **Assembly.** -/
theorem exists_section_of_patches (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (D : CoverData ωb μ L T θ δ) {k : ℕ} (_hk0 : 0 < k) (hkg : D.GoodPower k) {φ' : X → EReal}
    (hφ' : IsThetaPshPotential (θ - δ • ωb.form).val φ') {W : Set X} (hWc : IsCompact W)
    {Λ ψ : X → EReal} {c a r t b M : ℝ} {s : (y : W) → (twistedPower L T k).Fiber y}
    (P : ∀ p : W, MarginPatch (n := n) (twistedPower L T k).Fiber μ W Λ ψ c a r s p.1)
    (hmult : ∀ x, multiplierWeight (k : ℝ) (φ' x) =
      multiplierWeight (k : ℝ) (ψ x) * multiplierWeight r (Λ x))
    (hψq : IsGlobalQuasiPshPotential (n := n) ψ) (hψm : Measurable ψ) (hΛm : Measurable Λ)
    (hΛc : Continuous Λ) (hψM : ∀ x, ψ x ≤ (M : EReal)) (hΛ0 : ∀ x, Λ x ≤ 0)
    (hΛW : ∀ x, Λ x = ⊥ → x ∈ W) (ht : 1 < t) (hc : c = k * t) (ha : 0 ≤ a) (hb : 1 ≤ b)
    (hbr : b - 1 < r) (hr : a / t + b * (1 - 1 / t) = r) :
    ∃ σ : twistedSections L T k,
      σ ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
        (sourceDegreeMultiplierIdeal (n := n) k ψ) ∧ ∀ y : W, σ y = s y := by
  set V := (twistedPower L T k).Fiber with hV
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr0 : 0 ≤ r := by linarith
  -- a finite subcover of `W`
  obtain ⟨t₀, ht₀⟩ := hWc.elim_finite_subcover (fun p : W => (P p).B') (fun p => (P p).isOpen_B')
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, (P ⟨x, hx⟩).mem⟩)
  set J := {p : W // p ∈ t₀}
  set W₁ : Set X := ⋃ j : J, (P j.1).K' with hW₁
  set N₀ : Set X := ⋃ j : J, (P j.1).B' with hN₀
  have hW₁c : IsClosed W₁ := (isCompact_iUnion fun j : J => (P j.1).isCompact_K').isClosed
  have hN₀o : IsOpen N₀ := isOpen_iUnion fun j => (P j.1).isOpen_B'
  have hWN₀ : W ⊆ N₀ := by
    intro x hx
    obtain ⟨p, hpt, hxp⟩ := mem_iUnion₂.mp (ht₀ hx)
    exact mem_iUnion.mpr ⟨⟨p, hpt⟩, hxp⟩
  have hN₀W₁ : N₀ ⊆ W₁ := iUnion_mono fun j => (P j.1).B'_K'
  -- the cover of `X` and a partition of unity
  set Sop : Option J → TopologicalSpace.Opens X := fun o => match o with
    | none => ⟨W₁ᶜ, hW₁c.isOpen_compl⟩
    | some j => ⟨(P j.1).B, (P j.1).isOpen_B⟩ with hSop
  have hcover : ∀ x : X, ∃ o, x ∈ Sop o := by
    intro x
    by_cases hx : x ∈ W₁
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact ⟨some j, (P j.1).K'_B hj⟩
    · exact ⟨none, hx⟩
  obtain ⟨m', χ, idx, hχs, hχ0, hχS, -, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n) Sop hcover
  set sec : Fin m' → (x : X) → V x := fun a x => match idx a with
    | none => 0
    | some j => (P j.1).S x with hsec
  set U : Fin m' → Set X := fun a => (Sop (idx a) : Set X) with hUdef
  have hUo : ∀ a, IsOpen (U a) := fun a => (Sop (idx a)).isOpen
  have hχU : ∀ a, tsupport (χ a) ⊆ U a := hχS
  have hsech : ∀ a, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V (sec a) (U a) := by
    intro a
    simp only [hsec, hUdef]
    cases idx a with
    | none => exact isHolomorphicSectionOn_zero (n := n) V _
    | some j => exact (P j.1).hol
  have hsupp_none : ∀ a, idx a = none → tsupport (χ a) ⊆ W₁ᶜ := by
    intro a ha; have := hχU a; simp only [hUdef, ha] at this; exact this
  have hsupp_some : ∀ a (j : J), idx a = some j → tsupport (χ a) ⊆ (P j.1).B := by
    intro a j ha; have := hχU a; simp only [hUdef, ha] at this; exact this
  have hsec_some : ∀ a (j : J), idx a = some j → sec a = (P j.1).S := by
    intro a j ha; simp only [hsec, ha]
  have hsec_none : ∀ a, idx a = none → sec a = fun _ => 0 := by
    intro a ha; simp only [hsec, ha]
  -- the gluing system and the datum
  set G := D.toGluingSystem hL hT hkg hφ' with hG
  set v₀ := gluedDatum χ sec with hv₀
  have hv : G.IsSmooth v₀ := isSmooth_gluedDatum D hL hT hkg hφ' hχs hχ0 hsum hUo hχU hsech
  have hGD : ∀ (u : (x : X) → V x) x, G.D u x =
      ENNReal.ofReal (‖u x‖ ^ 2) * multiplierWeight (k : ℝ) (ψ x) * multiplierWeight r (Λ x) := by
    intro u x
    show ENNReal.ofReal (‖u x‖ ^ 2) * multiplierWeight (k : ℝ) (φ' x) = _
    rw [hmult, mul_assoc]
  -- `Λ` is bounded below off `N₀`
  obtain ⟨A, hAtop, hA⟩ : ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ x, x ∉ N₀ → multiplierWeight r (Λ x) ≤ A := by
    rcases (N₀ᶜ).eq_empty_or_nonempty with he | hne
    · exact ⟨0, ENNReal.zero_ne_top, fun x hx => absurd (he ▸ (show x ∈ N₀ᶜ from hx)) (by simp)⟩
    obtain ⟨x₀, hx₀, hmin⟩ := (hN₀o.isClosed_compl.isCompact).exists_isMinOn hne hΛc.continuousOn
    have hx₀W : x₀ ∉ W := fun h => hx₀ (hWN₀ h)
    have hne' : Λ x₀ ≠ ⊥ := fun h => hx₀W (hΛW x₀ h)
    have hnt : Λ x₀ ≠ ⊤ := fun h => by have := hΛ0 x₀; rw [h] at this; exact absurd this (by simp)
    refine ⟨multiplierWeight r (Λ x₀), ?_, fun x hx => multiplierWeight_antitone hr0 (hmin hx)⟩
    rw [← EReal.coe_toReal hnt hne', multiplierWeight_coe]; exact ENNReal.ofReal_ne_top
  have hKab : ∀ a b, IsCompact (tsupport (χ a) ∩ tsupport (χ b)) := fun a b =>
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact
  -- the pair integrals
  have hsingle : ∀ (j : J) (K₀ : Set X), K₀ ⊆ (P j.1).K →
      ∫⁻ x in K₀, ENNReal.ofReal (‖(P j.1).S x‖ ^ 2) * multiplierWeight (k : ℝ) (ψ x) ∂μ ≠ ⊤ :=
    fun j K₀ hK₀ => (P j.1).lintegral_single_ne_top hk' ht.le hc ha hψM hΛ0 hK₀
  have hpair : ∀ a b, ∫⁻ x in tsupport (χ a) ∩ tsupport (χ b),
      G.D (fun x => sec a x - sec b x) x ∂μ ≠ ⊤ := by
    intro a b
    simp only [hGD]
    -- the case of one patch and the outside
    have hone : ∀ (j : J) (K₀ : Set X), IsClosed K₀ → K₀ ⊆ (P j.1).K → K₀ ⊆ N₀ᶜ →
        ∫⁻ x in K₀, ENNReal.ofReal (‖(P j.1).S x‖ ^ 2) * multiplierWeight (k : ℝ) (ψ x) *
          multiplierWeight r (Λ x) ∂μ ≠ ⊤ := by
      intro j K₀ hK₀c hK₀ hK₀N
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (hsingle j K₀ hK₀) hAtop) ?_
      rw [← lintegral_mul_const' _ _ hAtop]
      exact setLIntegral_mono_ae' hK₀c.measurableSet
        (Eventually.of_forall fun x hx => mul_le_mul' le_rfl (hA x (hK₀N hx)))
    have hW₁N : W₁ᶜ ⊆ N₀ᶜ := compl_subset_compl.mpr hN₀W₁
    rcases hia : idx a with _ | i <;> rcases hib : idx b with _ | j
    · rw [hsec_none a hia, hsec_none b hib]; simp
    · rw [hsec_none a hia, hsec_some b j hib]
      simp only [zero_sub, norm_neg]
      exact hone j _ ((isClosed_tsupport _).inter (isClosed_tsupport _))
        (inter_subset_right.trans ((hsupp_some b j hib).trans (P j.1).B_K))
        (inter_subset_left.trans ((hsupp_none a hia).trans hW₁N))
    · rw [hsec_some a i hia, hsec_none b hib]
      simp only [sub_zero]
      exact hone i _ ((isClosed_tsupport _).inter (isClosed_tsupport _))
        (inter_subset_left.trans ((hsupp_some a i hia).trans (P i.1).B_K))
        (inter_subset_right.trans ((hsupp_none b hib).trans hW₁N))
    · rw [hsec_some a i hia, hsec_some b j hib]
      exact (P i.1).lintegral_overlap_ne_top (P j.1) hk' ht hc ha hb hbr hr hψm hΛm hψM hΛ0
        (hKab a b) fun x hx => ⟨hsupp_some a i hia hx.1, hsupp_some b j hib hx.2⟩
  -- finite energy, correction
  have hE : G.totalEnergy v₀ ≠ ⊤ := by
    refine ENNReal.sum_ne_top.mpr fun l _ => ?_
    obtain ⟨C, hC, hle⟩ := energy_gluedDatum_le D hL hT hkg hφ' hχs hχ0 hsum hUo hχU hsech l
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (ENNReal.sum_ne_top.mpr fun a _ =>
      ENNReal.sum_ne_top.mpr fun b _ => hpair a b)) hle
  obtain ⟨Sc, hSloc, hSint⟩ := G.exists_correction (D.kappa_le hL hT hkg hφ') hv hE
  obtain ⟨σ, hσ⟩ := D.exists_section_of_local hL hT hkg hφ' Sc hSloc
  have hfin : ∫⁻ x, G.D (fun x => v₀ x - σ x) x ∂μ ≠ ⊤ := by
    have : (Fintype.card (Fin D.m) : ℝ≥0∞) * (G.A * G.K₀ v₀) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top G.A_ne_top (G.K₀_ne_top hE))
    refine ne_top_of_le_ne_top this (le_of_eq_of_le ?_ hSint)
    refine lintegral_congr fun x => ?_
    simp only [GluingSystem.D, hσ x]
  have hσhol : ∀ U', SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V σ U' :=
    fun U' => isHolomorphicSectionOn_of_holomorphicSections (n := n) V σ U'
  have hwψ : Measurable fun x => multiplierWeight (k : ℝ) (ψ x) :=
    (multiplierWeight_antitone hk').measurable.comp hψm
  have hwΛ : Measurable fun x => multiplierWeight r (Λ x) :=
    (multiplierWeight_antitone hr0).measurable.comp hΛm
  have hχle : ∀ a x, χ a x ≤ 1 := fun a x => χ_le_one' hχ0 hsum a x
  have hχsq : ∀ a x (u : V x), ‖((χ a x : ℝ) : ℂ) • u‖ ^ 2 ≤
      (tsupport (χ a)).indicator (fun _ => (1 : ℝ)) x * ‖u‖ ^ 2 := by
    intro a x u
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 a x), mul_pow]
    by_cases hx : x ∈ tsupport (χ a)
    · rw [indicator_of_mem hx, one_mul]
      exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [hχ0 a x, hχle a x])
    · rw [indicator_of_notMem hx, zero_mul, image_eq_zero_of_notMem_tsupport hx]; simp
  refine ⟨σ, (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) V k hψq σ hμ).mpr ?_, ?_⟩
  · -- `∫ |σ|² e^{-kψ} < ∞`
    set g : X → ℝ≥0∞ := fun x => ∑ a, (tsupport (χ a)).indicator
      (fun x => ENNReal.ofReal (‖sec a x‖ ^ 2)) x * multiplierWeight (k : ℝ) (ψ x) with hg
    have hgm_a : ∀ a, Measurable fun x => (tsupport (χ a)).indicator
        (fun x => ENNReal.ofReal (‖sec a x‖ ^ 2)) x * multiplierWeight (k : ℝ) (ψ x) := fun a =>
      (measurable_indicator_closed_of_continuousOn (hUo a) (isClosed_tsupport _) (hχU a)
        (ENNReal.continuous_ofReal.comp_continuousOn
          ((continuousOn_norm_of_isHolomorphicSectionOn (n := n) V (hsech a)).pow 2))).mul hwψ
    have hgm : Measurable g := Finset.measurable_sum _ fun a _ => hgm_a a
    have hpt : ∀ x, originalSectionDensity (n := n) V ψ k σ x ≤
        2 * G.D (fun x => v₀ x - σ x) x + 2 * (Fintype.card (Fin m') : ℝ≥0∞) * g x := by
      intro x
      have h1 : ‖σ x‖ ^ 2 ≤ 2 * ‖v₀ x - σ x‖ ^ 2 + 2 * ‖v₀ x‖ ^ 2 := by
        have := norm_sub_le (v₀ x) (v₀ x - σ x)
        rw [sub_sub_cancel] at this
        have h2 : ‖σ x‖ ^ 2 ≤ (‖v₀ x‖ + ‖v₀ x - σ x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
        nlinarith [sq_nonneg (‖v₀ x‖ - ‖v₀ x - σ x‖)]
      have h3 : ‖v₀ x‖ ^ 2 ≤ (Fintype.card (Fin m') : ℝ) * ∑ a,
          (tsupport (χ a)).indicator (fun _ => (1 : ℝ)) x * ‖sec a x‖ ^ 2 :=
        (norm_sum_sq_le_card _).trans (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun a _ => hχsq a x _) (Nat.cast_nonneg _))
      have hw1 : multiplierWeight (k : ℝ) (ψ x) ≤ multiplierWeight (k : ℝ) (ψ x) *
          multiplierWeight r (Λ x) := le_mul_of_one_le_right zero_le (one_le_multiplierWeight hr0 (hΛ0 x))
      have hB : ENNReal.ofReal (∑ a, (tsupport (χ a)).indicator (fun _ => (1 : ℝ)) x * ‖sec a x‖ ^ 2) =
          ∑ a, (tsupport (χ a)).indicator (fun x => ENNReal.ofReal (‖sec a x‖ ^ 2)) x := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun a _ =>
          mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _))]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hx : x ∈ tsupport (χ a)
        · rw [indicator_of_mem hx, indicator_of_mem hx, one_mul]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul, ENNReal.ofReal_zero]
      have hBnn : 0 ≤ ∑ a, (tsupport (χ a)).indicator (fun _ => (1 : ℝ)) x * ‖sec a x‖ ^ 2 :=
        Finset.sum_nonneg fun a _ => mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
          (sq_nonneg _)
      have hDA : ENNReal.ofReal (‖v₀ x - σ x‖ ^ 2) * multiplierWeight (k : ℝ) (ψ x) ≤
          G.D (fun x => v₀ x - σ x) x := by
        rw [hGD, mul_assoc]; exact mul_le_mul' le_rfl hw1
      unfold originalSectionDensity
      calc ENNReal.ofReal (‖σ x‖ ^ 2) * multiplierWeight (k : ℝ) (ψ x)
          ≤ ENNReal.ofReal (2 * ‖v₀ x - σ x‖ ^ 2 + 2 * ((Fintype.card (Fin m') : ℝ) * ∑ a,
              (tsupport (χ a)).indicator (fun _ => (1 : ℝ)) x * ‖sec a x‖ ^ 2)) *
              multiplierWeight (k : ℝ) (ψ x) := by
            gcongr; linarith
        _ = 2 * (ENNReal.ofReal (‖v₀ x - σ x‖ ^ 2) * multiplierWeight (k : ℝ) (ψ x)) +
              2 * (Fintype.card (Fin m') : ℝ≥0∞) *
                ((∑ a, (tsupport (χ a)).indicator (fun x => ENNReal.ofReal (‖sec a x‖ ^ 2)) x) *
                  multiplierWeight (k : ℝ) (ψ x)) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (Nat.cast_nonneg _), hB]
            simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
            ring
        _ ≤ _ := by
            refine add_le_add (mul_le_mul' le_rfl hDA) (le_of_eq ?_)
            rw [hg, Finset.sum_mul]
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_add_right' _ ((hgm.const_mul _).aemeasurable), lintegral_const_mul' _ _
      (by norm_num), lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.natCast_ne_top _))]
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hfin),
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (ENNReal.natCast_lt_top _)) ?_⟩
    rw [hg]
    beta_reduce
    rw [lintegral_finsetSum' (f := fun a x => (tsupport (χ a)).indicator
      (fun x => ENNReal.ofReal (‖sec a x‖ ^ 2)) x * multiplierWeight (k : ℝ) (ψ x)) _
      fun a _ => (hgm_a a).aemeasurable]
    refine ENNReal.sum_lt_top.mpr fun a _ => lt_top_iff_ne_top.mpr ?_
    have hind : (fun x => (tsupport (χ a)).indicator (fun x => ENNReal.ofReal (‖sec a x‖ ^ 2)) x *
        multiplierWeight (k : ℝ) (ψ x)) = (tsupport (χ a)).indicator
          (fun x => ENNReal.ofReal (‖sec a x‖ ^ 2) * multiplierWeight (k : ℝ) (ψ x)) := by
      funext x
      by_cases hx : x ∈ tsupport (χ a)
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    rw [hind, lintegral_indicator (isClosed_tsupport _).measurableSet]
    rcases hia : idx a with _ | j
    · rw [hsec_none a hia]; simp
    · rw [hsec_some a j hia]
      exact hsingle j _ ((hsupp_some a j hia).trans (P j.1).B_K)
  · -- `σ = s` on `W`
    intro y
    obtain ⟨p, hpt, hyp⟩ := mem_iUnion₂.mp (ht₀ y.2)
    set j : J := ⟨p, hpt⟩
    set Pj := P j.1 with hPj
    have hB'B : Pj.B' ⊆ Pj.B := Pj.B'_K'.trans Pj.K'_B
    have hhol := isHolomorphicSectionOn_sub (n := n) V Pj.isOpen_B' (hσhol Pj.B')
      (Pj.hol.mono hB'B)
    suffices h0 : σ y - Pj.S y = 0 by
      rw [sub_eq_zero] at h0; rw [h0]; exact Pj.agree y (hB'B hyp)
    refine Pj.crit _ Pj.B' Pj.isOpen_B' hB'B hhol y hyp y.2 ?_
    -- the integral of `|σ - S_j|² e^{-rΛ}` over `B'_j`
    set g : X → ℝ≥0∞ := fun x => ∑ a, (tsupport (χ a) ∩ Pj.K').indicator
      (fun x => ENNReal.ofReal (‖sec a x - Pj.S x‖ ^ 2)) x * multiplierWeight (k : ℝ) (ψ x) *
        multiplierWeight r (Λ x) with hg
    have hcont_a : ∀ a, ContinuousOn (fun x => ENNReal.ofReal (‖sec a x - Pj.S x‖ ^ 2))
        (U a ∩ Pj.B) := fun a => ENNReal.continuous_ofReal.comp_continuousOn
      ((continuousOn_norm_of_isHolomorphicSectionOn (n := n) V (isHolomorphicSectionOn_sub (n := n) V
        ((hUo a).inter Pj.isOpen_B) ((hsech a).mono inter_subset_left)
        (Pj.hol.mono inter_subset_right))).pow 2)
    have hmeas_a : ∀ a, Measurable fun x => (tsupport (χ a) ∩ Pj.K').indicator
        (fun x => ENNReal.ofReal (‖sec a x - Pj.S x‖ ^ 2)) x * multiplierWeight (k : ℝ) (ψ x) *
          multiplierWeight r (Λ x) := fun a =>
      ((measurable_indicator_closed_of_continuousOn ((hUo a).inter Pj.isOpen_B)
        ((isClosed_tsupport _).inter Pj.isCompact_K'.isClosed)
        (fun x hx => ⟨hχU a hx.1, Pj.K'_B hx.2⟩) (hcont_a a)).mul hwψ).mul hwΛ
    have hgm : Measurable g := Finset.measurable_sum _ fun a _ => hmeas_a a
    have hpt : ∀ x ∈ Pj.B', ENNReal.ofReal (‖σ x - Pj.S x‖ ^ 2) * multiplierWeight r (Λ x) ≤
        ENNReal.ofReal (Real.exp (k * M)) * (2 * G.D (fun x => v₀ x - σ x) x +
          2 * (Fintype.card (Fin m') : ℝ≥0∞) * g x) := by
      intro x hx
      have hxK' : x ∈ Pj.K' := Pj.B'_K' hx
      have hdiff : v₀ x - Pj.S x = ∑ a, ((χ a x : ℝ) : ℂ) • (sec a x - Pj.S x) := by
        simp only [hv₀, gluedDatum, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
          ← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_smul]
      have h1 : ‖σ x - Pj.S x‖ ^ 2 ≤ 2 * ‖v₀ x - σ x‖ ^ 2 + 2 * ‖v₀ x - Pj.S x‖ ^ 2 := by
        have := norm_sub_le (v₀ x - Pj.S x) (v₀ x - σ x)
        rw [sub_sub_sub_cancel_left] at this
        have h2 : ‖σ x - Pj.S x‖ ^ 2 ≤ (‖v₀ x - Pj.S x‖ + ‖v₀ x - σ x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
        nlinarith [sq_nonneg (‖v₀ x - Pj.S x‖ - ‖v₀ x - σ x‖)]
      have h3 : ‖v₀ x - Pj.S x‖ ^ 2 ≤ (Fintype.card (Fin m') : ℝ) * ∑ a,
          (tsupport (χ a) ∩ Pj.K').indicator (fun x => ‖sec a x - Pj.S x‖ ^ 2) x := by
        rw [hdiff]
        refine (norm_sum_sq_le_card _).trans (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _))
        refine (hχsq a x _).trans (le_of_eq ?_)
        by_cases hxa : x ∈ tsupport (χ a)
        · rw [indicator_of_mem hxa, indicator_of_mem (show x ∈ tsupport (χ a) ∩ Pj.K' from
            ⟨hxa, hxK'⟩), one_mul]
        · rw [indicator_of_notMem hxa, indicator_of_notMem (fun h : x ∈ tsupport (χ a) ∩ Pj.K' =>
            hxa h.1), zero_mul]
      have hwk : 1 ≤ ENNReal.ofReal (Real.exp (k * M)) * multiplierWeight (k : ℝ) (ψ x) := by
        have := ofReal_exp_le_multiplierWeight hk' (hψM x)
        calc (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp (k * M)) * ENNReal.ofReal (Real.exp (-(k * M))) := by
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
                Real.exp_zero, ENNReal.ofReal_one]
          _ ≤ _ := mul_le_mul' le_rfl this
      have hB : ENNReal.ofReal (∑ a, (tsupport (χ a) ∩ Pj.K').indicator
            (fun x => ‖sec a x - Pj.S x‖ ^ 2) x) = ∑ a, (tsupport (χ a) ∩ Pj.K').indicator
            (fun x => ENNReal.ofReal (‖sec a x - Pj.S x‖ ^ 2)) x := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => indicator_nonneg (fun _ _ => sq_nonneg _) _)]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hxa : x ∈ tsupport (χ a) ∩ Pj.K'
        · rw [indicator_of_mem hxa, indicator_of_mem hxa]
        · rw [indicator_of_notMem hxa, indicator_of_notMem hxa, ENNReal.ofReal_zero]
      have hBnn : 0 ≤ ∑ a, (tsupport (χ a) ∩ Pj.K').indicator (fun x => ‖sec a x - Pj.S x‖ ^ 2) x :=
        Finset.sum_nonneg fun a _ => indicator_nonneg (fun _ _ => sq_nonneg _) _
      set E := ENNReal.ofReal (Real.exp (k * M)) with hEdef
      set wψ := multiplierWeight (k : ℝ) (ψ x)
      set wΛ := multiplierWeight r (Λ x)
      calc ENNReal.ofReal (‖σ x - Pj.S x‖ ^ 2) * wΛ
          ≤ ENNReal.ofReal (‖σ x - Pj.S x‖ ^ 2) * wΛ * (E * wψ) := le_mul_of_one_le_right zero_le hwk
        _ ≤ ENNReal.ofReal (2 * ‖v₀ x - σ x‖ ^ 2 + 2 * ((Fintype.card (Fin m') : ℝ) * ∑ a,
              (tsupport (χ a) ∩ Pj.K').indicator (fun x => ‖sec a x - Pj.S x‖ ^ 2) x)) *
              wΛ * (E * wψ) := by
            gcongr; linarith
        _ = E * (2 * (ENNReal.ofReal (‖v₀ x - σ x‖ ^ 2) * wψ * wΛ) +
              2 * (Fintype.card (Fin m') : ℝ≥0∞) * ((∑ a, (tsupport (χ a) ∩ Pj.K').indicator
                (fun x => ENNReal.ofReal (‖sec a x - Pj.S x‖ ^ 2)) x) * wψ * wΛ)) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (Nat.cast_nonneg _), hB]
            simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
            ring
        _ = _ := by
            rw [hGD, hg]
            simp only [Finset.sum_mul]
            rfl
    refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' Pj.isOpen_B'.measurableSet hpt)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    rw [lintegral_add_right' _ ((hgm.const_mul _).aemeasurable), lintegral_const_mul' _ _
      (by norm_num), lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.natCast_ne_top _))]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num)
      (ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _)),
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)) ?_⟩
    refine ne_top_of_le_ne_top ?_ (setLIntegral_le_lintegral _ _)
    rw [hg]
    beta_reduce
    rw [lintegral_finsetSum' (f := fun a x => (tsupport (χ a) ∩ Pj.K').indicator
      (fun x => ENNReal.ofReal (‖sec a x - Pj.S x‖ ^ 2)) x * multiplierWeight (k : ℝ) (ψ x) *
        multiplierWeight r (Λ x)) _ fun a _ => (hmeas_a a).aemeasurable]
    refine ENNReal.sum_ne_top.mpr fun a _ => ?_
    have hind : (fun x => (tsupport (χ a) ∩ Pj.K').indicator
        (fun x => ENNReal.ofReal (‖sec a x - Pj.S x‖ ^ 2)) x * multiplierWeight (k : ℝ) (ψ x) *
          multiplierWeight r (Λ x)) = (tsupport (χ a) ∩ Pj.K').indicator
          (fun x => ENNReal.ofReal (‖sec a x - Pj.S x‖ ^ 2) * multiplierWeight (k : ℝ) (ψ x) *
            multiplierWeight r (Λ x)) := by
      funext x
      by_cases hx : x ∈ tsupport (χ a) ∩ Pj.K'
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul, zero_mul]
    rw [hind, lintegral_indicator ((isClosed_tsupport _).inter Pj.isCompact_K'.isClosed).measurableSet]
    rcases hia : idx a with _ | i
    · have hempty : tsupport (χ a) ∩ Pj.K' = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun x hx => hsupp_none a hia hx.1 ?_
        exact mem_iUnion.mpr ⟨j, hx.2⟩
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
      exact ENNReal.zero_ne_top
    · rw [hsec_some a i hia]
      exact (P i.1).lintegral_overlap_ne_top Pj hk' ht hc ha hb hbr hr hψm hΛm hψM hΛ0
        ((isClosed_tsupport _).inter Pj.isCompact_K'.isClosed).isCompact
        fun x hx => ⟨hsupp_some a i hia hx.1, Pj.K'_B hx.2⟩

end SGPT.Trace.OTMargin
