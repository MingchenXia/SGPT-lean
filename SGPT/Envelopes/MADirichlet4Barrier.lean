import SGPT.Envelopes.MADirichlet4Weights
import SGPT.PSH.BookDeepDomination
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus

/-!
# A barrier with zero boundary values on a polydisk

Xia, *Foundations of pluripotential theory* (FPT), Step 1 of the proof of
`thm:compact-bounded-subsolution-ball-dirichlet`, on a polydisk `Q = a + R·P` instead of a ball.

* `polydiskExhaustion a R hn`: `ρ_Q(z) = max_j (‖ξ_j‖² - 1)`, `ξ = (z - a)/R`: continuous,
  locally bounded plurisubharmonic, `-1 ≤ ρ_Q < 0` on `Q` and `ρ_Q = 0` on `∂Q`
  (FPT uses `|z - a|² - R²` on a ball).
* `canonicalBedfordTaylorMeasure_restrict_eq`, `canonicalBedfordTaylorMeasure_congr_eqOn`: the
  locality of the Monge–Ampère operator on open subsets (FPT `prop:bt-positive-recursion`).
* `exists_barrier`: if `b ≤ w ≤ b + M` is plurisubharmonic on `Q` and `K ⊆ Q` is compact, then
  `W = max(w - b - M - 1, A ρ_Q)` (for a suitable `A > 0`) is plurisubharmonic, `-M - 1 ≤ W ≤ 0`,
  `W → 0` at `∂Q`, and `W = w - b - M - 1` on an open neighborhood `N ⊆ Q` of `K`; hence
  `(ddᶜW)ⁿ ≥ α` for every `α ≤ (ddᶜw)ⁿ` carried by `K` (`restrict_le_ma_barrier`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Envelopes.MADirichlet

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-! ### Locality -/

/-- The canonical measure restricted to an open subset is the canonical measure there. -/
theorem canonicalBedfordTaylorMeasure_restrict_eq {Ω V : Opens (ComplexModel n)} (hVΩ : V ≤ Ω)
    {φ : ComplexModel n → ℝ} (hφ : IsLocallyBoundedPshOn Ω φ) (hφV : IsLocallyBoundedPshOn V φ) :
    (canonicalBedfordTaylorMeasure Ω φ hφ).restrict V = canonicalBedfordTaylorMeasure V φ hφV :=
  ((isBTLimit_canonicalBedfordTaylorMeasure hφ).restrict_opens hVΩ).unique
    (isBTLimit_canonicalBedfordTaylorMeasure hφV)

/-- Functions equal on the domain have the same canonical measure. -/
theorem canonicalBedfordTaylorMeasure_congr_eqOn {Ω : Opens (ComplexModel n)}
    {φ ψ : ComplexModel n → ℝ} (hφ : IsLocallyBoundedPshOn Ω φ) (hψ : IsLocallyBoundedPshOn Ω ψ)
    (h : EqOn φ ψ Ω) : canonicalBedfordTaylorMeasure Ω φ hφ = canonicalBedfordTaylorMeasure Ω ψ hψ :=
  ((isBTLimit_canonicalBedfordTaylorMeasure hφ).congr fun _ => h).unique
    (isBTLimit_canonicalBedfordTaylorMeasure hψ)

/-- If `W = w + c` on an open `N ⊆ Q` and `α` is carried by `N`, then `α ≤ (ddᶜw)ⁿ` implies
`α ≤ (ddᶜW)ⁿ`. -/
theorem restrict_le_ma_of_eqOn {Q : Opens (ComplexModel n)} {N : Set (ComplexModel n)}
    (hN : IsOpen N) (hNQ : N ⊆ Q) {w W : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn Q w)
    (hW : IsLocallyBoundedPshOn Q W) {c : ℝ} (hWw : ∀ z ∈ N, W z = w z + c)
    {α : Measure (ComplexModel n)} (hαN : α Nᶜ = 0)
    (hα : α.restrict Q ≤ canonicalBedfordTaylorMeasure Q w hw) :
    α.restrict Q ≤ canonicalBedfordTaylorMeasure Q W hW := by
  set N' : Opens (ComplexModel n) := ⟨N, hN⟩
  have hN'Q : N' ≤ Q := hNQ
  have hwN : IsLocallyBoundedPshOn N' w := IsLocallyBoundedPshOn.mono_opens hw hN'Q
  have hwcN : IsLocallyBoundedPshOn N' fun z => w z + c := IsLocallyBoundedPshOn.add_const hwN c
  have hWN : IsLocallyBoundedPshOn N' W := IsLocallyBoundedPshOn.mono_opens hW hN'Q
  have heq : canonicalBedfordTaylorMeasure N' W hWN = canonicalBedfordTaylorMeasure N' w hwN := by
    rw [canonicalBedfordTaylorMeasure_congr_eqOn hWN hwcN (fun z hz => hWw z hz)]
    exact canonicalBedfordTaylorMeasure_add_const hwN c hwcN
  refine Measure.le_iff.mpr fun E hE => ?_
  have h1 : α.restrict Q E = α.restrict Q (E ∩ N) := by
    rw [Measure.restrict_apply hE, Measure.restrict_apply (hE.inter hN.measurableSet)]
    refine (measure_congr ?_)
    have hae : ∀ᵐ x ∂α, x ∈ N := (measure_eq_zero_iff_ae_notMem.mp hαN).mono fun x hx => by
      simpa using hx
    filter_upwards [hae] with x hx
    show (x ∈ E ∩ (Q : Set (ComplexModel n))) = (x ∈ E ∩ N ∩ (Q : Set (ComplexModel n)))
    simp only [mem_inter_iff, eq_iff_iff]
    tauto
  calc α.restrict Q E = α.restrict Q (E ∩ N) := h1
    _ ≤ canonicalBedfordTaylorMeasure Q w hw (E ∩ N) := hα _
    _ = (canonicalBedfordTaylorMeasure Q w hw).restrict N' E := by
        rw [Measure.restrict_apply hE]; rfl
    _ = canonicalBedfordTaylorMeasure N' w hwN E := by
        rw [canonicalBedfordTaylorMeasure_restrict_eq hN'Q hw hwN]
    _ = canonicalBedfordTaylorMeasure N' W hWN E := by rw [heq]
    _ = (canonicalBedfordTaylorMeasure Q W hW).restrict N' E := by
        rw [canonicalBedfordTaylorMeasure_restrict_eq hN'Q hW hWN]
    _ ≤ canonicalBedfordTaylorMeasure Q W hW E := Measure.restrict_apply_le _ _

/-! ### The polydisk exhaustion -/

/-- The coordinate functions `‖ξ_j‖² - 1`, `ξ = (z - a)/R`. -/
def coordExhaustion (a : ComplexModel n) (R : ℝ) (j : Fin n) (z : ComplexModel n) : ℝ :=
  ‖affineFrom a R z j‖ ^ 2 - 1

theorem finset_univ_nonempty_of_pos (hn : 0 < n) : (Finset.univ : Finset (Fin n)).Nonempty :=
  Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩

/-- The polydisk exhaustion `ρ_Q = max_j (‖ξ_j‖² - 1)`. -/
def polydiskExhaustion (a : ComplexModel n) (R : ℝ) (hn : 0 < n) : ComplexModel n → ℝ :=
  Finset.univ.sup' (finset_univ_nonempty_of_pos hn) (coordExhaustion a R)

theorem polydiskExhaustion_apply (a : ComplexModel n) (R : ℝ) (hn : 0 < n) (z : ComplexModel n) :
    polydiskExhaustion a R hn z =
      Finset.univ.sup' (finset_univ_nonempty_of_pos hn) fun j => coordExhaustion a R j z := by
  rw [polydiskExhaustion, Finset.sup'_apply]

theorem continuous_coordExhaustion (a : ComplexModel n) (R : ℝ) (j : Fin n) :
    Continuous (coordExhaustion a R j) := by
  have h : Continuous fun z => affineFrom a R z j :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp (continuous_affineFrom a)
  exact (h.norm.pow 2).sub continuous_const

theorem continuous_polydiskExhaustion (a : ComplexModel n) (R : ℝ) (hn : 0 < n) :
    Continuous (polydiskExhaustion a R hn) := by
  refine Finset.sup'_induction _ _ (p := Continuous) (fun f hf g hg => hf.sup hg) ?_
  exact fun j _ => continuous_coordExhaustion a R j

theorem isLocallyBoundedPshOn_polydiskExhaustion (a : ComplexModel n) (R : ℝ) (hn : 0 < n)
    (Ω : Opens (ComplexModel n)) : IsLocallyBoundedPshOn Ω (polydiskExhaustion a R hn) := by
  have hcoord : ∀ j, IsLocallyBoundedPshOn Ω (coordExhaustion a R j) := by
    intro j
    refine LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_of_continuousOn ?_
      (continuous_coordExhaustion a R j).continuousOn
    have hpsh := plurisubharmonicOn_coord_normSq (n := n) one_pos j univ
    have hpull := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic isOpen_univ
      ((contDiff_affineFrom (n := n) a (R := R)).differentiable (by simp)).differentiableOn
      (mapsTo_univ _ _) hpsh
    refine fun x _ => (hpull x (mem_univ x)).congr (Eventually.of_forall fun y => ?_)
    simp [coordExhaustion]
  refine Finset.sup'_induction _ _ (p := IsLocallyBoundedPshOn Ω) (fun f hf g hg => ?_)
    (fun j _ => hcoord j)
  have h := IsLocallyBoundedPshOn.max hf hg
  convert h using 1
  funext z
  rfl

theorem polydiskExhaustion_neg {a z : ComplexModel n} {R : ℝ} (hn : 0 < n)
    (hz : z ∈ polydiskAt a R) : polydiskExhaustion a R hn z < 0 := by
  rw [polydiskExhaustion_apply, Finset.sup'_lt_iff]
  intro j _
  have hz' : affineFrom a R z ∈ unitPolydisk n := hz
  have h1 : ‖affineFrom a R z j‖ < 1 := hz' j
  have h0 : 0 ≤ ‖affineFrom a R z j‖ := norm_nonneg _
  simp only [coordExhaustion]
  nlinarith

theorem neg_one_le_polydiskExhaustion (a : ComplexModel n) (R : ℝ) (hn : 0 < n)
    (z : ComplexModel n) : -1 ≤ polydiskExhaustion a R hn z := by
  rw [polydiskExhaustion_apply]
  refine le_trans ?_ (Finset.le_sup' (fun j => coordExhaustion a R j z) (Finset.mem_univ ⟨0, hn⟩))
  simp only [coordExhaustion]
  nlinarith [norm_nonneg (affineFrom a R z ⟨0, hn⟩)]

theorem polydiskExhaustion_eq_zero_of_mem_frontier {a ζ : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (hn : 0 < n) (hζ : ζ ∈ frontier (polydiskAt a R)) : polydiskExhaustion a R hn ζ = 0 := by
  have hfr : affineFrom a R ζ ∈ frontier (unitPolydisk n) := by
    have h := (affineHomeomorph (n := n) a hR.ne').preimage_frontier (unitPolydisk n)
    have : ζ ∈ (affineHomeomorph (n := n) a hR.ne') ⁻¹' frontier (unitPolydisk n) := by
      rw [h]; exact hζ
    exact this
  obtain ⟨hcl, hnot⟩ := frontier_unitPolydisk_subset hfr
  rw [polydiskExhaustion_apply]
  refine le_antisymm (Finset.sup'_le _ _ fun j _ => ?_) ?_
  · have h1 : ‖affineFrom a R ζ j‖ ≤ 1 := hcl j
    have h0 : 0 ≤ ‖affineFrom a R ζ j‖ := norm_nonneg _
    simp only [coordExhaustion]
    nlinarith
  · have : ∃ j, 1 ≤ ‖affineFrom a R ζ j‖ := by
      by_contra h
      push Not at h
      exact hnot h
    obtain ⟨j, hj⟩ := this
    refine le_trans ?_ (Finset.le_sup' (fun j => coordExhaustion a R j ζ) (Finset.mem_univ j))
    simp only [coordExhaustion]
    nlinarith

/-! ### The barrier -/

/-- **The barrier** (FPT, Step 1 of `thm:compact-bounded-subsolution-ball-dirichlet`). -/
theorem exists_barrier (hn : 0 < n) (a : ComplexModel n) {R : ℝ} (hR : 0 < R)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKQ : K ⊆ polydiskAt a R)
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn (polydiskAtOpens a R) w) {b M : ℝ}
    (hM : 0 ≤ M) (hwb : ∀ z ∈ polydiskAt a R, b ≤ w z ∧ w z ≤ b + M) :
    ∃ (W : ComplexModel n → ℝ) (N : Set (ComplexModel n)),
      IsLocallyBoundedPshOn (polydiskAtOpens a R) W ∧
      (∀ z ∈ polydiskAt a R, -(M + 1) ≤ W z ∧ W z ≤ 0) ∧
      (∀ ζ ∈ frontier (polydiskAt a R), Tendsto W (𝓝[polydiskAt a R] ζ) (𝓝 0)) ∧
      IsOpen N ∧ K ⊆ N ∧ N ⊆ polydiskAt a R ∧ ∀ z ∈ N, W z = w z + (-(b + M) - 1) := by
  set Q := polydiskAtOpens a R with hQdef
  set ρ := polydiskExhaustion a R hn with hρdef
  have hρc : Continuous ρ := continuous_polydiskExhaustion a R hn
  -- a level below which `K` lies
  obtain ⟨η, hη, hKη⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K, ρ z < -η := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    obtain ⟨z₀, hz₀K, hmax⟩ := hK.exists_isMaxOn hne hρc.continuousOn
    have hneg := polydiskExhaustion_neg hn (hKQ hz₀K)
    refine ⟨-ρ z₀ / 2, by linarith, fun z hz => ?_⟩
    have := hmax hz
    simp only [mem_ofPred_eq] at this
    linarith
  set A : ℝ := (M + 2) / η with hAdef
  have hA : 0 < A := by positivity
  set w₀ : ComplexModel n → ℝ := fun z => w z + (-(b + M) - 1) with hw₀def
  set W : ComplexModel n → ℝ := fun z => max (w₀ z) (A * ρ z) with hWdef
  have hw₀ : IsLocallyBoundedPshOn Q w₀ := IsLocallyBoundedPshOn.add_const hw _
  have hAρ : IsLocallyBoundedPshOn Q fun z => A * ρ z :=
    isLocallyBoundedPshOn_const_mul (isLocallyBoundedPshOn_polydiskExhaustion a R hn Q) hA.le
  have hW : IsLocallyBoundedPshOn Q W := IsLocallyBoundedPshOn.max hw₀ hAρ
  set N : Set (ComplexModel n) := {z | z ∈ polydiskAt a R ∧ ρ z < -η} with hNdef
  have hNo : IsOpen N := (isOpen_polydiskAt a R).inter (isOpen_lt hρc continuous_const)
  refine ⟨W, N, hW, fun z hz => ⟨?_, ?_⟩, fun ζ hζ => ?_, hNo, fun z hz => ⟨hKQ hz, hKη z hz⟩,
    fun z hz => hz.1, fun z hz => ?_⟩
  · exact (by linarith [(hwb z hz).1] : -(M + 1) ≤ w₀ z).trans (le_max_left _ _)
  · refine max_le (by linarith [(hwb z hz).2]) ?_
    exact mul_nonpos_of_nonneg_of_nonpos hA.le (polydiskExhaustion_neg hn hz).le
  · have hρζ : ρ ζ = 0 := polydiskExhaustion_eq_zero_of_mem_frontier hR hn hζ
    have hlim : Tendsto (fun z => A * ρ z) (𝓝[polydiskAt a R] ζ) (𝓝 0) := by
      have hc : Continuous fun z => A * ρ z := continuous_const.mul hρc
      have := (hc.tendsto ζ).mono_left (nhdsWithin_le_nhds (s := polydiskAt a R))
      simpa [hρζ] using this
    have hev : ∀ᶠ z in 𝓝[polydiskAt a R] ζ, W z = A * ρ z := by
      filter_upwards [(tendsto_order.1 hlim).1 (-1) (by norm_num), self_mem_nhdsWithin] with z hz hzQ
      refine max_eq_right ?_
      linarith [(hwb z hzQ).2]
    exact hlim.congr' (hev.mono fun z hz => hz.symm)
  · refine max_eq_left ?_
    have h1 : A * ρ z < A * -η := mul_lt_mul_of_pos_left hz.2 hA
    have h2 : A * -η = -(M + 2) := by rw [hAdef]; field_simp
    linarith [(hwb z hz.1).1]

/-- The barrier dominates every measure carried by `K` and dominated by `(ddᶜw)ⁿ`. -/
theorem restrict_le_ma_barrier {Q : Opens (ComplexModel n)} {N : Set (ComplexModel n)}
    (hN : IsOpen N) (hNQ : N ⊆ Q) {K : Set (ComplexModel n)} (hKN : K ⊆ N)
    {w W : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn Q w) (hW : IsLocallyBoundedPshOn Q W)
    {c : ℝ} (hWw : ∀ z ∈ N, W z = w z + c) {α : Measure (ComplexModel n)} (hαK : α Kᶜ = 0)
    (hα : α.restrict Q ≤ canonicalBedfordTaylorMeasure Q w hw) :
    α.restrict Q ≤ canonicalBedfordTaylorMeasure Q W hW :=
  restrict_le_ma_of_eqOn hN hNQ hw hW hWw (measure_mono_null (compl_subset_compl.mpr hKN) hαK) hα

end SGPT.Envelopes.MADirichlet
