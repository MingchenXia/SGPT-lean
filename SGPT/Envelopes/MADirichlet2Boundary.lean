import SGPT.Envelopes.MADirichlet2Equation
import SGPT.Foundations.Analysis.Pending.IdealFunctionMaxGluing

/-!
# Zero boundary values and uniqueness for the polydisk Dirichlet problem

Xia, *Foundations of pluripotential theory* (FPT), `thm:continuous-density-ball-dirichlet`
(Steps 1 and 5), on the unit polydisk `P` with zero boundary data, for densities `Fⁿ` with `F` of
class `C²` and compact support in `P` (route: `claude-ma-dir2.tex`):

* `tendsto_polydiskEnvelope_boundary`: the envelope `H_F` has boundary values `0`. The barrier
  (`exists_boundary_barrier`) is `max(C(|z|² - n), A max_j (|z_j|² - 1))`: it equals the
  subsolution `C(|z|² - n)` near the support of `F`, and it tends to `0` at `∂P` because one
  coordinate has modulus one there.
* `eq_polydiskEnvelope_of_ma_eq`: every locally bounded psh solution of `(ddᶜU)ⁿ = Fⁿ ηⁿ` on `P`
  with boundary values `0` is `H_F` (MA-DIR's uniqueness with finite measure data,
  `eq_of_ma_eq`).
* `polydisk_dirichlet_C2`: summary — the Dirichlet problem `(ddᶜU)ⁿ = Fⁿ ηⁿ` on `P`, `U = 0` on
  `∂P`, has a unique locally bounded psh solution, namely the envelope of the nonpositive
  subsolutions, and it is locally semiconcave (TN's `SemiconcaveTaylor` turns this into
  `C^{1,1}_loc` regularity; that consequence is not restated here).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- `z ↦ A(|zⱼ|² - 1)` is plurisubharmonic. -/
theorem plurisubharmonicOn_coord_normSq {A : ℝ} (hA : 0 < A) (j : Fin n) (U : Set (ComplexModel n)) :
    PlurisubharmonicOn (fun y : ComplexModel n => ((A * (‖y j‖ ^ 2 - 1) : ℝ) : EReal)) U := by
  have hq := (SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_mul_normSq
    (⊤ : Opens (ComplexModel n)) hA).1
  set Lj : ComplexModel n →L[ℂ] ComplexModel n :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).smulRight (coordinateVector j) with hLj
  have hlin : DifferentiableOn ℂ (fun y : ComplexModel n => Lj y) univ :=
    Lj.differentiable.differentiableOn
  have hpull := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic isOpen_univ hlin
    (mapsTo_univ _ _) (by simpa using hq)
  have hconst : PlurisubharmonicOn (fun _ : ComplexModel n => ((-A : ℝ) : EReal)) univ :=
    fun x _ => plurisubharmonicAt_const _ (by simp) x
  have hsum := hpull.add hconst
  refine fun x _ => (hsum x (mem_univ x)).congr (Eventually.of_forall fun y => ?_)
  have hnorm : ‖Lj y‖ = ‖y j‖ := by
    simp [hLj, coordinateVector, norm_smul]
  have e : ((A * (‖y j‖ ^ 2 - 1) : ℝ) : EReal) = ((A * ‖Lj y‖ ^ 2 : ℝ) : EReal) + ((-A : ℝ) : EReal) := by
    rw [← EReal.coe_add, hnorm]
    congr 1
    ring
  show ((A : EReal) * ((‖Lj y‖ : ℝ) : EReal) ^ 2 + ((-A : ℝ) : EReal)) =
    ((A * (‖y j‖ ^ 2 - 1) : ℝ) : EReal)
  rw [e]
  push_cast
  rfl

/-- **The boundary barrier** for a density with compact support in `P`. -/
theorem exists_boundary_barrier (hn : 0 < n) {F : ComplexModel n → ℝ} (hFc : Continuous F)
    (hF0 : ∀ z, 0 ≤ F z) (hK : HasCompactSupport F) (hKP : tsupport F ⊆ unitPolydisk n) :
    ∃ s ∈ polydiskSubsolutions F, ∃ A : ℝ, 0 < A ∧
      ∀ y ∈ unitPolydisk n, ∀ j, A * (‖y j‖ ^ 2 - 1) ≤ s y := by
  classical
  set P := unitPolydiskOpens n with hPdef
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_continuous hFc
  have hbar := normSq_barrier_mem (fun z _ => hF0 z) hC0 fun z hz => (le_abs_self _).trans (hC z hz)
  -- a uniform bound `m < 1` for the coordinates on the support
  obtain ⟨m, hm0, hm1, hmK⟩ : ∃ m : ℝ, 0 ≤ m ∧ m < 1 ∧ ∀ y ∈ tsupport F, ∀ j, ‖y j‖ ≤ m := by
    rcases (tsupport F).eq_empty_or_nonempty with he | hne
    · exact ⟨0, le_rfl, one_pos, fun y hy => by rw [he] at hy; exact absurd hy (notMem_empty y)⟩
    · have hmax : ∀ j : Fin n, ∃ y ∈ tsupport F, ∀ y' ∈ tsupport F, ‖y' j‖ ≤ ‖y j‖ := by
        intro j
        obtain ⟨y, hy, hymax⟩ := hK.exists_isMaxOn hne
          ((continuous_norm.comp ((EuclideanSpace.proj (𝕜 := ℂ) j).continuous)).continuousOn)
        exact ⟨y, hy, fun y' hy' => hymax hy'⟩
      choose y hyK hymax using hmax
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j => ‖y j j‖
      exact ⟨‖y j₀ j₀‖, norm_nonneg _, hKP (hyK j₀) j₀, fun y' hy' j =>
        (hymax j y' hy').trans (hj₀ j)⟩
  have hm2 : 0 < 1 - m ^ 2 := by nlinarith
  set A : ℝ := (C * n + 1) / (1 - m ^ 2) with hAdef
  have hA : 0 < A := div_pos (by positivity) hm2
  have hAm : A * (m ^ 2 - 1) = -(C * n + 1) := by
    rw [hAdef]; field_simp; ring
  -- the barrier in `EReal`
  set Ψ : ComplexModel n → EReal :=
    fun y => Finset.univ.sup fun j => ((A * (‖y j‖ ^ 2 - 1) : ℝ) : EReal) with hΨdef
  set S : ComplexModel n → EReal :=
    fun y => max ((C * (‖y‖ ^ 2 - n) : ℝ) : EReal) (Ψ y) with hSdef
  have hΨtop : ∀ y, Ψ y ≠ ⊤ := fun y =>
    ((Finset.sup_lt_iff (a := (⊤ : EReal)) (by simp)).mpr fun j _ => EReal.coe_lt_top _).ne
  have hSbot : ∀ y, S y ≠ ⊥ := fun y =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_left _ _)
  have hStop : ∀ y, S y ≠ ⊤ := fun y => (max_lt (EReal.coe_lt_top _) (hΨtop y).lt_top).ne
  set s : ComplexModel n → ℝ := fun y => (S y).toReal with hsdef
  have hsS : ∀ y, ((s y : ℝ) : EReal) = S y := fun y => EReal.coe_toReal (hStop y) (hSbot y)
  have hsle : ∀ y ∈ unitPolydisk n, s y ≤ 0 := by
    intro y hy
    have h1 : ((C * (‖y‖ ^ 2 - n) : ℝ) : EReal) ≤ 0 := by
      have := norm_sq_le_of_mem_unitPolydisk hy
      exact EReal.coe_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos hC0.le (by linarith))
    have h2 : Ψ y ≤ 0 := Finset.sup_le fun j _ => by
      have := hy j
      exact EReal.coe_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos hA.le (by nlinarith [norm_nonneg (y j)]))
    have : S y ≤ 0 := max_le h1 h2
    rw [← hsS] at this
    exact EReal.coe_nonpos.mp this
  have hsge : ∀ y, ∀ j, A * (‖y j‖ ^ 2 - 1) ≤ s y := by
    intro y j
    have : ((A * (‖y j‖ ^ 2 - 1) : ℝ) : EReal) ≤ S y :=
      (Finset.le_sup (f := fun j => ((A * (‖y j‖ ^ 2 - 1) : ℝ) : EReal))
        (Finset.mem_univ j)).trans (le_max_right _ _)
    rw [← hsS] at this
    exact EReal.coe_le_coe_iff.mp this
  have hsge' : ∀ y, C * (‖y‖ ^ 2 - n) ≤ s y := by
    intro y
    have : ((C * (‖y‖ ^ 2 - n) : ℝ) : EReal) ≤ S y := le_max_left _ _
    rw [← hsS] at this
    exact EReal.coe_le_coe_iff.mp this
  -- plurisubharmonicity
  have hSpsh : PlurisubharmonicOn S (P : Set (ComplexModel n)) := by
    intro y hy
    have hΨ : PlurisubharmonicAt Ψ y := IdealFunctionMaxGluing.plurisubharmonicAt_finset_sup Finset.univ
      fun j _ => plurisubharmonicOn_coord_normSq hA j univ y (mem_univ y)
    exact (hbar.1.1 y hy).max hΨ
  have hspsh : PlurisubharmonicOn (fun y => (s y : EReal)) (P : Set (ComplexModel n)) := by
    intro y hy
    exact (hSpsh y hy).congr (Eventually.of_forall fun z => (hsS z).symm)
  have hsB : IsLocallyBoundedPshOn P s := by
    refine ⟨hspsh, fun z hz => ⟨P, hz, le_rfl, C * n, fun w hw => ?_⟩⟩
    have h1 := hsle w hw
    have h2 := hsge' w
    have h3 : 0 ≤ ‖w‖ ^ 2 := by positivity
    rw [abs_le]
    constructor <;> nlinarith
  -- the Monge–Ampère lower bound
  set α : Measure (ComplexModel n) :=
    volume.withDensity fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n) with hαdef
  have hU₁open : IsOpen ((P : Set (ComplexModel n)) ∩
      ⋂ j : Fin n, {y | A * (‖y j‖ ^ 2 - 1) < C * (‖y‖ ^ 2 - n)}) :=
    P.isOpen.inter (isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) (by fun_prop))
  have hsU₁ : ∀ y ∈ (P : Set (ComplexModel n)) ∩
      ⋂ j : Fin n, {y | A * (‖y j‖ ^ 2 - 1) < C * (‖y‖ ^ 2 - n)}, s y = C * (‖y‖ ^ 2 - n) := by
    intro y hy
    have hlt : Ψ y < ((C * (‖y‖ ^ 2 - n) : ℝ) : EReal) :=
      (Finset.sup_lt_iff (EReal.bot_lt_coe _)).mpr fun j _ =>
        EReal.coe_lt_coe_iff.mpr (mem_iInter.mp hy.2 j)
    have : S y = ((C * (‖y‖ ^ 2 - n) : ℝ) : EReal) := max_eq_left hlt.le
    rw [← hsS] at this
    exact EReal.coe_injective this
  refine ⟨s, ⟨hsB, hsle, ?_⟩, A, hA, fun y _ j => hsge y j⟩
  rw [polydiskDensityMeasure_eq_restrict]
  have hglue := restrict_le_restrict_of_isLindelof
    (μ := α) (ν := canonicalBedfordTaylorMeasure P s hsB)
    (HereditarilyLindelofSpace.isLindelof (P : Set (ComplexModel n))) fun y hy => by
      by_cases hyK : y ∈ tsupport F
      · set W : Opens (ComplexModel n) := ⟨_, hU₁open⟩ with hWdef
        have hWP : W ≤ P := inter_subset_left
        have hyW : y ∈ (W : Set (ComplexModel n)) := by
          refine ⟨hy, mem_iInter.mpr fun j => ?_⟩
          show A * (‖y j‖ ^ 2 - 1) < C * (‖y‖ ^ 2 - n)
          have h1 : ‖y j‖ ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hmK y hyK j) 2
          have h2 : A * (‖y j‖ ^ 2 - 1) ≤ A * (m ^ 2 - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hA.le
          have h3 : 0 ≤ C * ‖y‖ ^ 2 := by positivity
          nlinarith
        refine ⟨W, W.isOpen, hyW, ?_⟩
        have heq : (canonicalBedfordTaylorMeasure P s hsB).restrict (W : Set (ComplexModel n)) =
            (canonicalBedfordTaylorMeasure P _ hbar.1).restrict (W : Set (ComplexModel n)) :=
          (isBTLimit_canonicalBedfordTaylorMeasure hsB).restrict_eq_of_eqOn
            (isBTLimit_canonicalBedfordTaylorMeasure hbar.1) hWP fun _ z hz => hsU₁ z hz
        rw [heq]
        have := Measure.restrict_mono (s := (W : Set (ComplexModel n))) subset_rfl hbar.2.2
        rwa [polydiskDensityMeasure_eq_restrict, Measure.restrict_restrict_of_subset hWP] at this
      · refine ⟨(P : Set (ComplexModel n)) \ tsupport F,
          P.isOpen.sdiff (isClosed_tsupport F), ⟨hy, hyK⟩, ?_⟩
        have h0 : α.restrict ((P : Set (ComplexModel n)) \ tsupport F) = 0 := by
          rw [hαdef, restrict_withDensity (P.isOpen.sdiff (isClosed_tsupport F)).measurableSet]
          refine (withDensity_congr_ae ?_).trans withDensity_zero
          filter_upwards [ae_restrict_mem (P.isOpen.sdiff (isClosed_tsupport F)).measurableSet]
            with z hz
          rw [image_eq_zero_of_notMem_tsupport hz.2]
          simp [zero_pow hn.ne']
        rw [h0]
        exact Measure.zero_le _
  exact hglue.trans Measure.restrict_le_self

/-- **Zero boundary values** (FPT `thm:continuous-density-ball-dirichlet`, Step 1, on the
polydisk): for `F` with compact support in `P`, `H_F(z) → 0` as `z → ∂P`. -/
theorem tendsto_polydiskEnvelope_boundary (hn : 0 < n) {F : ComplexModel n → ℝ}
    (hFc : Continuous F) (hF0 : ∀ z, 0 ≤ F z) (hK : HasCompactSupport F)
    (hKP : tsupport F ⊆ unitPolydisk n) {ζ : ComplexModel n}
    (hζ : ζ ∈ closedUnitPolydisk n \ unitPolydisk n) :
    Tendsto (polydiskEnvelope F) (𝓝[unitPolydisk n] ζ) (𝓝 0) := by
  obtain ⟨s, hs, A, hA, hsA⟩ := exists_boundary_barrier hn hFc hF0 hK hKP
  obtain ⟨j, hj⟩ := exists_norm_eq_one_of_mem_boundary hζ
  have hlow : Tendsto (fun y : ComplexModel n => A * (‖y j‖ ^ 2 - 1)) (𝓝[unitPolydisk n] ζ)
      (𝓝 0) := by
    have hc : Continuous fun y : ComplexModel n => A * (‖y j‖ ^ 2 - 1) := by fun_prop
    have := hc.tendsto ζ
    rw [hj] at this
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hsA y hy j).trans (le_polydiskEnvelope hn hFc hF0 hs hy)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact polydiskEnvelope_nonpos hFc hF0 hy

theorem frontier_unitPolydisk_subset :
    frontier (unitPolydisk n) ⊆ closedUnitPolydisk n \ unitPolydisk n := by
  intro ζ hζ
  refine ⟨?_, ?_⟩
  · have := frontier_subset_closure hζ
    exact (isClosed_closedUnitPolydisk.closure_subset_iff.mpr
      unitPolydisk_subset_closedUnitPolydisk) this
  · rw [isOpen_unitPolydisk.frontier_eq] at hζ
    exact hζ.2

/-- **Uniqueness** (FPT `thm:continuous-density-ball-dirichlet`, Step 5, on the polydisk): a
locally bounded psh solution of `(ddᶜU)ⁿ = Fⁿ ηⁿ` on `P` with boundary values `0` is `H_F`. -/
theorem eq_polydiskEnvelope_of_ma_eq (hn : 0 < n) {F : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 F)
    (hF0 : ∀ z, 0 ≤ F z) (hK : HasCompactSupport F) (hKP : tsupport F ⊆ unitPolydisk n)
    {U : ComplexModel n → ℝ} (hU : IsLocallyBoundedPshOn (unitPolydiskOpens n) U)
    (hUma : canonicalBedfordTaylorMeasure (unitPolydiskOpens n) U hU = polydiskDensityMeasure F)
    (hUbd : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n,
      Tendsto U (𝓝[unitPolydisk n] ζ) (𝓝 0)) :
    ∀ z ∈ unitPolydisk n, U z = polydiskEnvelope F z := by
  have hFc : Continuous F := hF.continuous
  obtain ⟨hH, hHeq⟩ := ma_polydiskEnvelope_eq hn hF hF0
  have hbdd : Bornology.IsBounded ((unitPolydiskOpens n : Opens (ComplexModel n)) :
      Set (ComplexModel n)) :=
    isBounded_closedUnitPolydisk.subset unitPolydisk_subset_closedUnitPolydisk
  obtain ⟨C, -, hC⟩ := exists_bound_of_continuous hFc
  have hfin : canonicalBedfordTaylorMeasure (unitPolydiskOpens n) U hU
      ((unitPolydiskOpens n : Opens (ComplexModel n)) : Set (ComplexModel n)) < ⊤ := by
    have hset : ((unitPolydiskOpens n : Opens (ComplexModel n)) : Set (ComplexModel n)) =
        unitPolydisk n := rfl
    rw [hset, hUma, polydiskDensityMeasure, withDensity_apply _ isOpen_unitPolydisk.measurableSet]
    refine lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal
      (mongeAmpereConst n * C ^ n)) measurable_const fun z hz => ?_) ?_
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ mongeAmpereConst_pos.le)
      calc F z ^ n ≤ |F z ^ n| := le_abs_self _
        _ = |F z| ^ n := abs_pow _ _
        _ ≤ C ^ n := pow_le_pow_left₀ (abs_nonneg _) (hC z hz) n
    · rw [setLIntegral_const]
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      rw [Measure.restrict_apply' isOpen_unitPolydisk.measurableSet, inter_self]
      exact (measure_mono unitPolydisk_subset_closedUnitPolydisk).trans_lt
        isCompact_closedUnitPolydisk.measure_lt_top
  have hHbd : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n,
      Tendsto (polydiskEnvelope F) (𝓝[unitPolydisk n] ζ) (𝓝 0) :=
    fun ζ hζ => tendsto_polydiskEnvelope_boundary hn hFc hF0 hK hKP hζ
  refine eq_of_ma_eq hn hbdd hU hH (fun ζ hζ δ hδ => ?_) hfin (hUma.trans hHeq.symm)
  have hζ' := frontier_unitPolydisk_subset hζ
  have h1 := (hUbd ζ hζ').sub (hHbd ζ hζ')
  rw [sub_zero] at h1
  filter_upwards [(h1.abs).eventually (gt_mem_nhds (by simpa using hδ))] with z hz
  simpa using hz

/-- **The Dirichlet problem `(ddᶜU)ⁿ = Fⁿ ηⁿ` on the polydisk with zero boundary values** (FPT
`thm:continuous-density-ball-dirichlet` for `C²` data and boundary values `0`, transposed to the
unit polydisk): for `F ≥ 0` of class `C²` with compact support in `P`, the envelope `H_F` of the
nonpositive subsolutions is a locally bounded, locally semiconcave psh solution with boundary
values `0`, and it is the only locally bounded psh solution with boundary values `0`. -/
theorem polydisk_dirichlet_C2 (hn : 0 < n) {F : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 F)
    (hF0 : ∀ z, 0 ≤ F z) (hK : HasCompactSupport F) (hKP : tsupport F ⊆ unitPolydisk n) :
    (∃ hH : IsLocallyBoundedPshOn (unitPolydiskOpens n) (polydiskEnvelope F),
      canonicalBedfordTaylorMeasure (unitPolydiskOpens n) _ hH = polydiskDensityMeasure F) ∧
    (∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n,
      Tendsto (polydiskEnvelope F) (𝓝[unitPolydisk n] ζ) (𝓝 0)) ∧
    IsLocallySemiconcaveOn (unitPolydiskOpens n) (polydiskEnvelope F) ∧
    (∀ v ∈ polydiskSubsolutions F, ∀ z ∈ unitPolydisk n, v z ≤ polydiskEnvelope F z) ∧
    ∀ (U : ComplexModel n → ℝ) (hU : IsLocallyBoundedPshOn (unitPolydiskOpens n) U),
      canonicalBedfordTaylorMeasure (unitPolydiskOpens n) U hU = polydiskDensityMeasure F →
      (∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, Tendsto U (𝓝[unitPolydisk n] ζ) (𝓝 0)) →
      ∀ z ∈ unitPolydisk n, U z = polydiskEnvelope F z :=
  ⟨ma_polydiskEnvelope_eq hn hF hF0,
    fun _ hζ => tendsto_polydiskEnvelope_boundary hn hF.continuous hF0 hK hKP hζ,
    isLocallySemiconcaveOn_polydiskEnvelope hn hF hF0,
    fun _ hv _ hz => le_polydiskEnvelope hn hF.continuous hF0 hv hz,
    fun _ hU hUma hUbd => eq_polydiskEnvelope_of_ma_eq hn hF hF0 hK hKP hU hUma hUbd⟩

end SGPT.Envelopes.MADirichlet
