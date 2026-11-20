import SGPT.Envelopes.MADirichlet2Transport
import SGPT.Envelopes.MADirichletEnvelope
import SGPT.Envelopes.MADirichletComparison
import SGPT.Foundations.Analysis.Pending.MaximalPshVanishingMass

/-!
# The envelope of subsolutions on the polydisk and its second differences

Xia, *Foundations of pluripotential theory* (FPT), `thm:continuous-density-ball-dirichlet`,
Steps 1 and 2, on the unit polydisk `P` with zero boundary data (route: `claude-ma-dir2.tex`).
For `F ≥ 0` let `𝒮_F` (`polydiskSubsolutions`) be the family of locally bounded plurisubharmonic
`v ≤ 0` on `P` with `(ddᶜv)ⁿ ≥ Fⁿ ηⁿ` on `P` (`ηⁿ = (n!/πⁿ) dV`), and `H_F` (`polydiskEnvelope`)
the upper semicontinuous regularization of its upper envelope.

* Step 1 (`polydiskEnvelope_mem`, `le_polydiskEnvelope`): for continuous `F ≥ 0`, `H_F ∈ 𝒮_F` and
  `H_F` is the largest member of `𝒮_F` (FPT: the envelope of subsolutions is a subsolution;
  MA-DIR's `ma_ge_regEnvelope`). The barrier `C(|z|² - n)` (`normSq_barrier_mem`) shows that
  `𝒮_F` is nonempty and `H_F ≥ C(|z|² - n)`.
* Step 2 (`polydiskEnvelope_secondDifference`): for `F` of class `C²`,
  `H_F(a + h) + H_F(a - h) - 2 H_F(a) ≤ K |h|²` uniformly for `a, a ± h` in a smaller polydisk.
  The competitor is `½ (H_F ∘ T_{a,h} + H_F ∘ T_{a,-h}) + M|h|² (|z|² - n)`, a member of `𝒮_F` by
  the transport of subsolutions (`ma_comp_polydiskAut_ge`), the subsolution algebra
  (`ma_ge_linComb`) and the estimate on the data (`exists_polydiskDensity_secondDifference`).
  Consequently `H_F` is locally semiconcave (`isLocallySemiconcaveOn_polydiskEnvelope`, TN's
  `IsLocallySemiconcaveOn`), the hypothesis of TN's `C^{1,1}` machinery.

On the polydisk `|z|² - n ≤ 0` plays the role of FPT's `ψ = |z|² - 1` on the ball: it is
nonpositive and has complex Hessian the identity, which is all that Step 2 uses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexConjugate ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.NPP.LogConcavityDinew

variable {n : ℕ}

/-- The measure `Fⁿ ηⁿ = (n!/πⁿ) Fⁿ dV` on the unit polydisk. -/
def polydiskDensityMeasure (F : ComplexModel n → ℝ) : Measure (ComplexModel n) :=
  (volume.restrict (unitPolydisk n)).withDensity
    fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)

/-- The nonpositive subsolutions of `(ddᶜv)ⁿ ≥ Fⁿ ηⁿ` on the unit polydisk. -/
def polydiskSubsolutions (F : ComplexModel n → ℝ) : Set (ComplexModel n → ℝ) :=
  {v | ∃ hv : IsLocallyBoundedPshOn (unitPolydiskOpens n) v, (∀ z ∈ unitPolydisk n, v z ≤ 0) ∧
    polydiskDensityMeasure F ≤ canonicalBedfordTaylorMeasure (unitPolydiskOpens n) v hv}

/-- The envelope `H_F`: the upper semicontinuous regularization of `sup 𝒮_F`. -/
def polydiskEnvelope (F : ComplexModel n → ℝ) : ComplexModel n → ℝ :=
  regEnvelope (polydiskSubsolutions F)

/-! ### Elementary facts -/

theorem canonicalBedfordTaylorMeasure_add_const {Ω : Opens (ComplexModel n)}
    {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn Ω v) (c : ℝ)
    (hvc : IsLocallyBoundedPshOn Ω fun z => v z + c) :
    canonicalBedfordTaylorMeasure Ω _ hvc = canonicalBedfordTaylorMeasure Ω v hv :=
  (isBTLimit_canonicalBedfordTaylorMeasure hvc).unique
    ((isBTLimit_canonicalBedfordTaylorMeasure hv).add_const_diag c)

theorem norm_sq_le_of_mem_unitPolydisk {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    ‖z‖ ^ 2 ≤ n := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖z i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by
          have h0 := norm_nonneg (z i)
          have h1 := (hz i).le
          nlinarith
    _ = n := by simp

theorem polydiskDensityMeasure_mono {F G : ComplexModel n → ℝ} (hF0 : ∀ z ∈ unitPolydisk n, 0 ≤ F z)
    (hFG : ∀ z ∈ unitPolydisk n, F z ≤ G z) :
    polydiskDensityMeasure F ≤ polydiskDensityMeasure G := by
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem isOpen_unitPolydisk.measurableSet] with z hz
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (hF0 z hz) (hFG z hz) n) mongeAmpereConst_pos.le)

theorem polydiskDensityMeasure_eq_restrict (F : ComplexModel n → ℝ) :
    polydiskDensityMeasure F = (volume.withDensity
      fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)).restrict
        (unitPolydiskOpens n : Set (ComplexModel n)) :=
  (restrict_withDensity isOpen_unitPolydisk.measurableSet _).symm

theorem withDensity_finite_of_bounded {F : ComplexModel n → ℝ} {C : ℝ}
    (hC : ∀ z ∈ unitPolydisk n, |F z| ≤ C) (K : Set (ComplexModel n)) (hK : IsCompact K)
    (hKP : K ⊆ (unitPolydiskOpens n : Set (ComplexModel n))) :
    volume.withDensity (fun z => ENNReal.ofReal (mongeAmpereConst n * F z ^ n)) K < ⊤ := by
  rw [withDensity_apply _ hK.measurableSet]
  refine lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal
    (mongeAmpereConst n * C ^ n)) measurable_const fun z hz => ?_) ?_
  · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ mongeAmpereConst_pos.le)
    calc F z ^ n ≤ |F z ^ n| := le_abs_self _
      _ = |F z| ^ n := abs_pow _ _
      _ ≤ C ^ n := pow_le_pow_left₀ (abs_nonneg _) (hC z (hKP hz)) n
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- **The barrier**: for `C > 0` with `F ≤ C` on `P`, `C(|z|² - n) ∈ 𝒮_F`. -/
theorem normSq_barrier_mem {F : ComplexModel n → ℝ} (hF0 : ∀ z ∈ unitPolydisk n, 0 ≤ F z)
    {C : ℝ} (hC : 0 < C) (hFC : ∀ z ∈ unitPolydisk n, F z ≤ C) :
    (fun z : ComplexModel n => C * (‖z‖ ^ 2 - n)) ∈ polydiskSubsolutions F := by
  set P := unitPolydiskOpens n
  have hq : IsLocallyBoundedPshOn P fun z => C * ‖z‖ ^ 2 :=
    SGPT.PSH.BookDeepDomination.isLocallyBoundedPshOn_mul_normSq P hC
  have e : (fun z : ComplexModel n => C * (‖z‖ ^ 2 - n)) =
      fun z => C * ‖z‖ ^ 2 + -(C * n) := by funext z; ring
  have hs : IsLocallyBoundedPshOn P fun z : ComplexModel n => C * (‖z‖ ^ 2 - n) := by
    rw [e]; exact IsLocallyBoundedPshOn.add_const hq _
  refine ⟨hs, fun z hz => mul_nonpos_of_nonneg_of_nonpos hC.le
    (by linarith [norm_sq_le_of_mem_unitPolydisk hz]), ?_⟩
  have hlim : IsBTLimit P (fun _ => fun z : ComplexModel n => C * (‖z‖ ^ 2 - n))
      ((ENNReal.ofReal C ^ n * ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n)) •
        volume.restrict (P : Set (ComplexModel n))) := by
    rw [e]; exact (SGPT.PSH.BookDeepDomination.isBTLimit_mul_normSq P hC.le).add_const_diag _
  rw [(isBTLimit_canonicalBedfordTaylorMeasure hs).unique hlim]
  have hconst : ENNReal.ofReal C ^ n * ENNReal.ofReal ((n.factorial : ℝ) / Real.pi ^ n) =
      ENNReal.ofReal (mongeAmpereConst n * C ^ n) := by
    rw [ENNReal.ofReal_mul mongeAmpereConst_pos.le, ENNReal.ofReal_pow hC.le, mul_comm,
      mongeAmpereConst]
  rw [hconst, ← withDensity_const]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem isOpen_unitPolydisk.measurableSet] with z hz
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (hF0 z hz) (hFC z hz) n) mongeAmpereConst_pos.le)

theorem exists_bound_of_continuous {F : ComplexModel n → ℝ} (hF : Continuous F) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ unitPolydisk n, |F z| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedUnitPolydisk (n := n)).exists_bound_of_continuousOn
    hF.continuousOn
  refine ⟨max C 1, by positivity, fun z hz => ?_⟩
  have := hC z fun i => (hz i).le
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-! ### Step 1: the envelope is a subsolution -/

section Envelope

variable {F : ComplexModel n → ℝ}

theorem max_mem_polydiskSubsolutions (hn : 0 < n) (hFc : Continuous F) {v w : ComplexModel n → ℝ}
    (hv : v ∈ polydiskSubsolutions F) (hw : w ∈ polydiskSubsolutions F) :
    (fun z => max (v z) (w z)) ∈ polydiskSubsolutions F := by
  obtain ⟨hv, hv0, hvα⟩ := hv
  obtain ⟨hw, hw0, hwα⟩ := hw
  obtain ⟨C, -, hC⟩ := exists_bound_of_continuous hFc
  have hm := IsLocallyBoundedPshOn.max hv hw
  refine ⟨hm, fun z hz => max_le (hv0 z hz) (hw0 z hz), ?_⟩
  rw [polydiskDensityMeasure_eq_restrict] at hvα hwα ⊢
  exact ma_ge_max hn hv hw (withDensity_finite_of_bounded hC) hvα hwα hm

theorem polydiskEnvelope_spec (hn : 0 < n) (hFc : Continuous F) (hF0 : ∀ z, 0 ≤ F z) :
    ∃ hH : IsLocallyBoundedPshOn (unitPolydiskOpens n) (polydiskEnvelope F),
      polydiskDensityMeasure F ≤ canonicalBedfordTaylorMeasure (unitPolydiskOpens n) _ hH ∧
      ∀ v ∈ polydiskSubsolutions F, ∀ z ∈ unitPolydisk n, v z ≤ polydiskEnvelope F z := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_continuous hFc
  have hs := normSq_barrier_mem (fun z _ => hF0 z) hC0 fun z hz => (le_abs_self _).trans (hC z hz)
  obtain ⟨hH, hHα, hHle⟩ := ma_ge_regEnvelope (Ω := unitPolydiskOpens n)
    (withDensity_finite_of_bounded hC) (𝒮 := polydiskSubsolutions F) (fun v hv => hv.1)
    (fun v hv => by rw [← polydiskDensityMeasure_eq_restrict]; exact hv.2.2)
    (fun v hv w hw => max_mem_polydiskSubsolutions hn hFc hv hw) hs
    (fun x hx => ⟨unitPolydisk n, isOpen_unitPolydisk.mem_nhds hx, 0,
      fun v hv y hy => hv.2.1 y hy⟩)
  refine ⟨hH, ?_, hHle⟩
  rw [polydiskDensityMeasure_eq_restrict]
  exact hHα

theorem le_polydiskEnvelope (hn : 0 < n) (hFc : Continuous F) (hF0 : ∀ z, 0 ≤ F z)
    {v : ComplexModel n → ℝ} (hv : v ∈ polydiskSubsolutions F) {z : ComplexModel n}
    (hz : z ∈ unitPolydisk n) : v z ≤ polydiskEnvelope F z :=
  (polydiskEnvelope_spec hn hFc hF0).2.2 v hv z hz

theorem polydiskEnvelope_nonpos (hFc : Continuous F) (hF0 : ∀ z, 0 ≤ F z)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) : polydiskEnvelope F z ≤ 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_continuous hFc
  have hs := normSq_barrier_mem (fun z _ => hF0 z) hC0 fun z hz => (le_abs_self _).trans (hC z hz)
  refine regEnvelope_le_of_eventually (g := fun _ => (0 : ℝ)) upperSemicontinuousAt_const ?_ ?_
  · filter_upwards [isOpen_unitPolydisk.mem_nhds hz] with y hy v hv using hv.2.1 y hy
  · refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot (C * (‖z‖ ^ 2 - n))) ?_
    exact (coe_le_sSup_erealFamily hs z).trans (le_uscRegularization _ z)

/-- **FPT Step 1**: the envelope `H_F` belongs to `𝒮_F`; it is therefore the largest member of
`𝒮_F`. -/
theorem polydiskEnvelope_mem (hn : 0 < n) (hFc : Continuous F) (hF0 : ∀ z, 0 ≤ F z) :
    polydiskEnvelope F ∈ polydiskSubsolutions F := by
  obtain ⟨hH, hHα, -⟩ := polydiskEnvelope_spec hn hFc hF0
  exact ⟨hH, fun z hz => polydiskEnvelope_nonpos hFc hF0 hz, hHα⟩

/-- The barrier bound `H_F ≥ C(|z|² - n)`. -/
theorem barrier_le_polydiskEnvelope (hn : 0 < n) (hFc : Continuous F) (hF0 : ∀ z, 0 ≤ F z)
    {C : ℝ} (hC : 0 < C) (hFC : ∀ z ∈ unitPolydisk n, F z ≤ C) {z : ComplexModel n}
    (hz : z ∈ unitPolydisk n) : C * (‖z‖ ^ 2 - n) ≤ polydiskEnvelope F z :=
  le_polydiskEnvelope hn hFc hF0 (normSq_barrier_mem (fun z _ => hF0 z) hC hFC) hz

end Envelope

/-! ### Step 2: second differences -/

theorem continuousOn_polydiskDensity {F : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 F)
    {a h : ComplexModel n} (ha : ∀ i, ‖a i‖ < 1) (hah : ∀ i, ‖a i + h i‖ < 1) :
    ContinuousOn (polydiskDensity F a h) (closedUnitPolydisk n) := by
  have hS : ContinuousOn (fun z : ComplexModel n => polydiskShift (-a, z)) (closedUnitPolydisk n) :=
    contDiffOn_polydiskShift.continuousOn.comp (Continuous.continuousOn (by fun_prop))
      fun z hz => mem_mobiusDomain (fun i => by simpa using ha i) hz
  have h1 : ContinuousOn (fun z : ComplexModel n => shiftDensity F (a + h, polydiskShift (-a, z)))
      (closedUnitPolydisk n) :=
    (contDiffOn_shiftDensity hF).continuousOn.comp (continuousOn_const.prodMk hS) fun z hz =>
      ⟨mem_mobiusDomain (fun i => by rw [complexModel_add_apply]; exact hah i)
        (polydiskShift_neg_mem_closedUnitPolydisk ha hz),
       fun i => by rw [complexModel_add_apply]; exact hah i⟩
  have h2 : ContinuousOn (fun z : ComplexModel n => shiftJac (-a, z) ^ ((n : ℝ)⁻¹))
      (closedUnitPolydisk n) :=
    (contDiffOn_shiftJac.continuousOn.comp (Continuous.continuousOn (by fun_prop))
      fun z hz => mem_mobiusDomain (fun i => by simpa using ha i) hz).rpow_const
        fun _ _ => Or.inr (by positivity)
  have := h1.mul h2
  refine this.congr fun z _ => ?_
  exact polydiskDensity_eq F a h z

theorem polydiskDensity_nonneg {F : ComplexModel n → ℝ} (hF0 : ∀ z, 0 ≤ F z) (a h z : ComplexModel n) :
    0 ≤ polydiskDensity F a h z :=
  mul_nonneg (hF0 _) (Real.rpow_nonneg (Complex.normSq_nonneg _) _)

/-- **FPT Step 2 on the polydisk: the second differences of the envelope.** -/
theorem polydiskEnvelope_secondDifference (hn : 0 < n) {F : ComplexModel n → ℝ}
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ z, 0 ≤ F z) {ρ : ℝ} (hρ : ρ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a h : ComplexModel n, (∀ i, ‖a i‖ ≤ ρ) → (∀ i, ‖a i + h i‖ ≤ ρ) →
      (∀ i, ‖a i - h i‖ ≤ ρ) →
        polydiskEnvelope F (a + h) + polydiskEnvelope F (a - h) - 2 * polydiskEnvelope F a ≤
          K * ‖h‖ ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_polydiskDensity_secondDifference hF hρ
  refine ⟨2 * M * n, by positivity, fun a h ha hah hah' => ?_⟩
  set P := unitPolydiskOpens n with hPdef
  set H := polydiskEnvelope F with hHdef
  have hFc : Continuous F := hF.continuous
  obtain ⟨hH, hH0, hHα⟩ := polydiskEnvelope_mem hn hFc hF0
  have haP : ∀ i, ‖a i‖ < 1 := fun i => lt_of_le_of_lt (ha i) hρ
  have hahP : ∀ i, ‖a i + h i‖ < 1 := fun i => lt_of_le_of_lt (hah i) hρ
  have hahP' : ∀ i, ‖a i + (-h) i‖ < 1 := fun i => by
    have : a i + (-h) i = a i - h i := by simp [sub_eq_add_neg]
    rw [this]; exact lt_of_le_of_lt (hah' i) hρ
  have hu := isLocallyBoundedPshOn_comp_polydiskAut hH haP hahP
  have hv := isLocallyBoundedPshOn_comp_polydiskAut hH haP hahP'
  have huα := ma_comp_polydiskAut_ge hn hH hHα haP hahP hu
  have hvα := ma_comp_polydiskAut_ge hn hH hHα haP hahP' hv
  set c : ℝ := M * ‖h‖ ^ 2 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hW := isLocallyBoundedPshOn_linComb hu hv (a := 1 / 2) (b := 1 / 2) (c := c)
    (by norm_num) (by norm_num) hc0
  have hWα := ma_ge_linComb hn hu hv
    ((continuousOn_polydiskDensity hF haP hahP).mono fun z hz i => (hz i).le)
    ((continuousOn_polydiskDensity hF haP hahP').mono fun z hz i => (hz i).le)
    (fun z _ => polydiskDensity_nonneg hF0 a h z) (fun z _ => polydiskDensity_nonneg hF0 a (-h) z)
    huα hvα (by norm_num) (by norm_num) hc0 hW
  set V : ComplexModel n → ℝ := fun z =>
    (1 / 2 * H (polydiskAut a h z) + 1 / 2 * H (polydiskAut a (-h) z) + c * ‖z‖ ^ 2) + -(c * n)
    with hVdef
  have hV : IsLocallyBoundedPshOn P V := IsLocallyBoundedPshOn.add_const hW _
  have hVmem : V ∈ polydiskSubsolutions F := by
    refine ⟨hV, fun z hz => ?_, ?_⟩
    · have h1 := hH0 _ (polydiskAut_mem_unitPolydisk haP hahP hz)
      have h2 := hH0 _ (polydiskAut_mem_unitPolydisk haP hahP' hz)
      have h3 := norm_sq_le_of_mem_unitPolydisk hz
      simp only [hVdef]
      nlinarith
    · rw [canonicalBedfordTaylorMeasure_add_const hW _ hV]
      refine le_trans (polydiskDensityMeasure_mono (fun z _ => hF0 z) fun z hz => ?_) hWα
      have := hM a h ha hah hah' z fun i => (hz i).le
      simp only [hcdef]
      linarith
  have hle := le_polydiskEnvelope hn hFc hF0 hVmem (show a ∈ unitPolydisk n from haP)
  have e1 : polydiskAut a h a = a + h := polydiskAut_self a h
  have e2 : polydiskAut a (-h) a = a - h := by rw [polydiskAut_self, sub_eq_add_neg]
  simp only [hVdef, e1, e2] at hle
  have hnorm : 0 ≤ ‖a‖ ^ 2 := by positivity
  have hcn : c * ‖a‖ ^ 2 ≥ 0 := mul_nonneg hc0 hnorm
  nlinarith

/-- The envelope is locally semiconcave on the polydisk (TN's `IsLocallySemiconcaveOn`). -/
theorem isLocallySemiconcaveOn_polydiskEnvelope (hn : 0 < n) {F : ComplexModel n → ℝ}
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ z, 0 ≤ F z) :
    IsLocallySemiconcaveOn (unitPolydiskOpens n) (polydiskEnvelope F) := by
  intro z hz
  obtain ⟨m, hm1, hm⟩ : ∃ m : ℝ, m < 1 ∧ ∀ i, ‖z i‖ ≤ m := by
    rcases isEmpty_or_nonempty (Fin n) with hE | hE
    · exact ⟨0, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖z i‖
      exact ⟨‖z i₀‖, hz i₀, hi₀⟩
  set r : ℝ := (1 - m) / 4 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hρ : m + 2 * r < 1 := by rw [hrdef]; linarith
  obtain ⟨K, hK0, hK⟩ := polydiskEnvelope_secondDifference hn hF hF0 hρ
  have hcoord : ∀ y ∈ closedBall z (2 * r), ∀ i, ‖y i‖ ≤ m + 2 * r := by
    intro y hy i
    have h1 : ‖y i - z i‖ ≤ ‖y - z‖ := by
      have := PiLp.norm_apply_le (y - z) i
      simpa using this
    have h2 : ‖y - z‖ ≤ 2 * r := by rw [← dist_eq_norm]; exact mem_closedBall.mp hy
    have h3 := norm_le_insert' (y i) (z i)
    linarith [hm i, norm_sub_norm_le (y i) (z i)]
  refine ⟨r, K, hr, hK0, fun y hy i => lt_of_le_of_lt (hcoord y hy i) hρ, ?_⟩
  intro y hy h hh
  have hy2 : y ∈ closedBall z (2 * r) := closedBall_subset_closedBall (by linarith) hy
  have hyp : y + h ∈ closedBall z (2 * r) := by
    rw [mem_closedBall, dist_eq_norm]
    have := mem_closedBall.mp hy
    rw [dist_eq_norm] at this
    calc ‖y + h - z‖ = ‖(y - z) + h‖ := by congr 1; abel
      _ ≤ ‖y - z‖ + ‖h‖ := norm_add_le _ _
      _ ≤ 2 * r := by linarith
  have hym : y - h ∈ closedBall z (2 * r) := by
    rw [mem_closedBall, dist_eq_norm]
    have := mem_closedBall.mp hy
    rw [dist_eq_norm] at this
    calc ‖y - h - z‖ = ‖(y - z) - h‖ := by congr 1; abel
      _ ≤ ‖y - z‖ + ‖h‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith
  exact hK y h (hcoord y hy2) (fun i => by rw [← complexModel_add_apply]; exact hcoord _ hyp i)
    (fun i => by rw [← complexModel_sub_apply]; exact hcoord _ hym i)

end SGPT.Envelopes.MADirichlet
