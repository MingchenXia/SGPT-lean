import SGPT.Foundations.Analysis.Pending.NonPluripolarLimit
import SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
import SGPT.Foundations.Analysis.Pending.BedfordTaylorDecreasingLimit
import SGPT.Foundations.Analysis.Pending.BedfordTaylorQuasiContinuity
import SGPT.Foundations.Analysis.Pending.VaguePortmanteau
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option autoImplicit false

/-!
# Lower semicontinuity of non-pluripolar measures along decreasing sequences

Let `v_j` be a pointwise decreasing sequence of plurisubharmonic functions on an
open set `Ω ⊆ ℂⁿ` with pointwise limit `V`, itself plurisubharmonic on `Ω`.  On
every open `O ⊆ Ω` the non-pluripolar Monge–Ampère measure of `V` is at most the
lower limit of those of the `v_j`:

  `⟨(ddᶜ V)ⁿ⟩(O) ≤ liminf_j ⟨(ddᶜ v_j)ⁿ⟩(O)`.

No boundedness is assumed: `V` and the `v_j` may take the value `-∞`.  This is
the decreasing half of the local form of the semicontinuity theorem for
non-pluripolar products (Darvas–Di Nezza–Lu, *The metric geometry of
singularity types*, Theorem 2.6; Xia, SGPT, Theorem 2.4.2,
`xia-sgpt:page-0074`).  The increasing half is
`IncreasingTruncationLimit.truncationLimitMeasure_le_liminf_of_monotone`.

## The proof

Fix a level `k` and a domain on which `v_0 ≤ c`.  Put `W = max(V, -k)` and
`w_j = max(v_j, -k)`: bounded plurisubharmonic functions with `w_j ↓ W`.  The
`k`-th truncation measure of `V` is `μ_W(O ∩ S)` with `S = {V > -k}`, and the
`k`-th truncation measure of `v_j` is `μ_{w_j}(O ∩ {v_j > -k})`, which dominates
`μ_{w_j}(O ∩ S)` because `V ≤ v_j`.

The set `S` is not open, so the open-set portmanteau inequality for the
Bedford–Taylor convergence theorem (decreasing case,
`BedfordTaylor.tendsto_integral_of_antitone_isBTLimit`) does not apply to it
directly.  Quasi-continuity of `W`
(`BedfordTaylor.IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn_diff`)
supplies an open `G` of relative capacity `< ε` off which `W` is continuous; then
`O ∩ S` agrees off `G` with an open set `O'`, and all the measures `μ_W`, `μ_{w_j}`
give `G` mass at most `(b - a)ⁿ ε`, the potentials lying in `[a, b]`
(`BedfordTaylor.canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds`).  Hence

  `μ_W(O ∩ S) ≤ liminf_j ⟨(ddᶜ v_j)ⁿ⟩(O) + 2 (b - a)ⁿ ε`

for every `ε > 0`.  The upper bound `c` is removed by exhausting `O` by compact
sets and restricting to thickenings of them, on which `v_0` is bounded above.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.DecreasingTruncationLimit

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere MongeAmpere MixedNonPluripolar

variable {n : ℕ}

/-! ### The truncations of a decreasing sequence -/

/-- Truncation at a fixed level preserves the pointwise decrease. -/
theorem truncationReal_antitone {Ω : Opens (ComplexModel n)}
    {v : ℕ → ComplexModel n → EReal} (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    (hanti : ∀ z ∈ Ω, Antitone fun j => v j z) (k : ℕ) :
    ∀ z ∈ Ω, Antitone fun j => truncationReal (v j) k z := by
  intro z hz i j hij
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncationReal (hv j) k hz, coe_truncationReal (hv i) k hz]
  exact max_le_max (hanti z hz hij) le_rfl

/-- Truncation at a fixed level preserves pointwise convergence. -/
theorem tendsto_truncationReal {Ω : Opens (ComplexModel n)}
    {v : ℕ → ComplexModel n → EReal} (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    {V : ComplexModel n → EReal} (hV : PlurisubharmonicOn V Ω)
    (hlim : ∀ z ∈ Ω, Tendsto (fun j => v j z) atTop (𝓝 (V z))) (k : ℕ) :
    ∀ z ∈ Ω, Tendsto (fun j => truncationReal (v j) k z) atTop
      (𝓝 (truncationReal V k z)) := by
  intro z hz
  have h2 : Tendsto (fun j => truncation (v j) k z) atTop (𝓝 (truncation V k z)) :=
    (hlim z hz).max tendsto_const_nhds
  have h3 : Tendsto (fun j => ((truncationReal (v j) k z : ℝ) : EReal)) atTop
      (𝓝 ((truncationReal V k z : ℝ) : EReal)) := by
    rw [coe_truncationReal hV k hz]
    exact h2.congr fun j => (coe_truncationReal (hv j) k hz).symm
  exact EReal.tendsto_coe.mp h3

/-- Two-sided bounds of a truncation whose potential is bounded above by `c`. -/
theorem truncationReal_mem_Icc {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u Ω) (k : ℕ) {c : ℝ} {z : ComplexModel n} (hz : z ∈ Ω)
    (hc : u z ≤ c) :
    -(k : ℝ) ≤ truncationReal u k z ∧ truncationReal u k z ≤ max c (-(k : ℝ)) + 1 := by
  constructor
  · apply EReal.coe_le_coe_iff.mp
    rw [coe_truncationReal hu k hz]
    exact truncation_lower_bound u k z
  · have h : truncationReal u k z ≤ max c (-(k : ℝ)) := by
      apply EReal.coe_le_coe_iff.mp
      rw [coe_truncationReal hu k hz]
      exact max_le (hc.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
        (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
    linarith

/-! ### Fixed level, bounded above -/

/-- **Fixed level on a domain where the sequence is bounded above.**  If
`v_j ↓ V` on `Ω` and `v_0 ≤ c` on `Ω`, then on every open `O ⊆ Ω` the `k`-th
truncation measure of `V` is at most `liminf_j ⟨(ddᶜ v_j)ⁿ⟩(O)`. -/
theorem truncationMeasure_le_liminf_of_antitone_of_le {Ω : Opens (ComplexModel n)}
    {v : ℕ → ComplexModel n → EReal} (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    (hanti : ∀ z ∈ Ω, Antitone fun j => v j z)
    {V : ComplexModel n → EReal} (hV : PlurisubharmonicOn V Ω)
    (hlim : ∀ z ∈ Ω, Tendsto (fun j => v j z) atTop (𝓝 (V z)))
    {c : ℝ} (hc : ∀ z ∈ Ω, v 0 z ≤ c)
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hOΩ : O ⊆ Ω) (k : ℕ) :
    truncationMeasure Ω V hV k O ≤
      liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) O) atTop := by
  classical
  have hW : IsLocallyBoundedPshOn Ω (truncationReal V k) :=
    truncationReal_isLocallyBoundedPshOn hV k
  have hw : ∀ j, IsLocallyBoundedPshOn Ω (truncationReal (v j) k) := fun j =>
    truncationReal_isLocallyBoundedPshOn (hv j) k
  -- order facts
  have hVle : ∀ j, ∀ z ∈ Ω, V z ≤ v j z := fun j z hz =>
    (hanti z hz).le_of_tendsto (hlim z hz) j
  have hvle : ∀ j, ∀ z ∈ Ω, v j z ≤ c := fun j z hz =>
    (hanti z hz (Nat.zero_le j)).trans (hc z hz)
  -- uniform two-sided bounds
  have hab : -(k : ℝ) < max c (-(k : ℝ)) + 1 := by
    linarith [le_max_right c (-(k : ℝ))]
  have hWb : ∀ z ∈ Ω, -(k : ℝ) ≤ truncationReal V k z ∧
      truncationReal V k z ≤ max c (-(k : ℝ)) + 1 := fun z hz =>
    truncationReal_mem_Icc hV k hz ((hVle 0 z hz).trans (hvle 0 z hz))
  have hwb : ∀ j, ∀ z ∈ Ω, -(k : ℝ) ≤ truncationReal (v j) k z ∧
      truncationReal (v j) k z ≤ max c (-(k : ℝ)) + 1 := fun j z hz =>
    truncationReal_mem_Icc (hv j) k hz (hvle j z hz)
  set D : ℝ≥0∞ := ENNReal.ofReal ((max c (-(k : ℝ)) + 1 - -(k : ℝ)) ^ n) with hD
  have hμG : ∀ G, canonicalBedfordTaylorMeasure Ω (truncationReal V k) hW G ≤
      D * BedfordTaylor.relCapacity Ω G :=
    BedfordTaylor.canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds hW hab hWb
  have hμsG : ∀ j G, canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k) (hw j) G ≤
      D * BedfordTaylor.relCapacity Ω G := fun j =>
    BedfordTaylor.canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds (hw j) hab (hwb j)
  -- the open-set portmanteau inequality for the bounded truncations
  have hport : ∀ O' : Set (ComplexModel n), IsOpen O' → O' ⊆ Ω →
      canonicalBedfordTaylorMeasure Ω (truncationReal V k) hW O' ≤
        liminf (fun j => canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k)
          (hw j) O') atTop := by
    intro O' hO' hO'Ω
    refine VaguePortmanteau.measure_le_liminf_of_tendsto_integral hO' hO'Ω
      (fun j K hK hKΩ => (BedfordTaylor.isBTLimit_canonicalBedfordTaylorMeasure (hw j)).2.1
        K hK hKΩ)
      (fun K hK hKΩ => (BedfordTaylor.isBTLimit_canonicalBedfordTaylorMeasure hW).2.1
        K hK hKΩ) ?_
    intro φ hφ hφc hφΩ
    exact BedfordTaylor.tendsto_integral_of_antitone_isBTLimit hw hW
      (truncationReal_antitone hv hanti k) (tendsto_truncationReal hv hV hlim k)
      (fun j => BedfordTaylor.isBTLimit_canonicalBedfordTaylorMeasure (hw j))
      (BedfordTaylor.isBTLimit_canonicalBedfordTaylorMeasure hW) hφ hφc hφΩ
  -- the strict locus of `V` lies in that of each `v j`
  have hstep : ∀ j, canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k) (hw j)
      (O ∩ strictTruncationLocus Ω V k) ≤ truncationLimitMeasure Ω (v j) (hv j) O := by
    intro j
    calc canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k) (hw j)
          (O ∩ strictTruncationLocus Ω V k)
        ≤ canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k) (hw j)
          (O ∩ strictTruncationLocus Ω (v j) k) :=
          measure_mono (inter_subset_inter_right _ fun z hz =>
            ⟨hz.1, hz.2.trans_le (hVle j z hz.1)⟩)
      _ = truncationMeasure Ω (v j) (hv j) k O := by
          rw [truncationMeasure, Measure.restrict_apply hO.measurableSet]
      _ ≤ truncationLimitMeasure Ω (v j) (hv j) O := truncationMeasure_le_limit (hv j) k O
  have hlhs : truncationMeasure Ω V hV k O =
      canonicalBedfordTaylorMeasure Ω (truncationReal V k) hW
        (O ∩ strictTruncationLocus Ω V k) := by
    rw [truncationMeasure, Measure.restrict_apply hO.measurableSet]
  rw [hlhs]
  set L := liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) O) atTop with hL
  -- the estimate with a capacity budget `ε`
  have hkey : ∀ ε : ℝ, 0 < ε →
      canonicalBedfordTaylorMeasure Ω (truncationReal V k) hW
          (O ∩ strictTruncationLocus Ω V k) ≤
        L + D * ENNReal.ofReal ε + D * ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨G, -, hGcap, hGcont⟩ :=
      BedfordTaylor.IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn_diff
        hW hε
    obtain ⟨U, hUo, hU⟩ := continuousOn_iff'.mp hGcont (Ioi (-(k : ℝ))) isOpen_Ioi
    have hO'o : IsOpen (O ∩ U) := hO.inter hUo
    have hO'Ω : O ∩ U ⊆ Ω := inter_subset_left.trans hOΩ
    have hi : O ∩ strictTruncationLocus Ω V k ⊆ (O ∩ U) ∪ G := by
      intro z hz
      by_cases hzG : z ∈ G
      · exact Or.inr hzG
      · left
        have hzΩ : z ∈ Ω := hOΩ hz.1
        have hlt : -(k : ℝ) < truncationReal V k z := by
          apply EReal.coe_lt_coe_iff.mp
          rw [coe_truncationReal hV k hzΩ]
          exact lt_max_of_lt_left hz.2.2
        have hmem : z ∈ truncationReal V k ⁻¹' Ioi (-(k : ℝ)) ∩
            ((Ω : Set (ComplexModel n)) \ G) := ⟨hlt, hzΩ, hzG⟩
        rw [hU] at hmem
        exact ⟨hz.1, hmem.1⟩
    have hii : O ∩ U ⊆ (O ∩ strictTruncationLocus Ω V k) ∪ G := by
      intro z hz
      by_cases hzG : z ∈ G
      · exact Or.inr hzG
      · left
        have hzΩ : z ∈ Ω := hOΩ hz.1
        have hmem : z ∈ U ∩ ((Ω : Set (ComplexModel n)) \ G) := ⟨hz.2, hzΩ, hzG⟩
        rw [← hU] at hmem
        have h1 : ((-(k : ℝ) : ℝ) : EReal) < truncation V k z := by
          rw [← coe_truncationReal hV k hzΩ]
          exact EReal.coe_lt_coe_iff.mpr hmem.1
        refine ⟨hz.1, hzΩ, ?_⟩
        rcases lt_max_iff.mp h1 with h | h
        · exact h
        · exact absurd h (lt_irrefl _)
    have hcapG : D * BedfordTaylor.relCapacity Ω G ≤ D * ENNReal.ofReal ε :=
      by gcongr
    have hliminf : liminf (fun j => canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k)
        (hw j) (O ∩ U)) atTop ≤ L + D * ENNReal.ofReal ε := by
      calc liminf (fun j => canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k)
            (hw j) (O ∩ U)) atTop
          ≤ liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) O +
              D * ENNReal.ofReal ε) atTop := by
            refine liminf_le_liminf (Eventually.of_forall fun j => ?_)
            calc canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k) (hw j) (O ∩ U)
                ≤ canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k) (hw j)
                    ((O ∩ strictTruncationLocus Ω V k) ∪ G) := measure_mono hii
              _ ≤ canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k) (hw j)
                    (O ∩ strictTruncationLocus Ω V k) +
                  canonicalBedfordTaylorMeasure Ω (truncationReal (v j) k) (hw j) G :=
                  measure_union_le _ _
              _ ≤ _ := add_le_add (hstep j) ((hμsG j G).trans hcapG)
        _ = L + D * ENNReal.ofReal ε :=
            liminf_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault)
    calc canonicalBedfordTaylorMeasure Ω (truncationReal V k) hW
          (O ∩ strictTruncationLocus Ω V k)
        ≤ canonicalBedfordTaylorMeasure Ω (truncationReal V k) hW ((O ∩ U) ∪ G) :=
          measure_mono hi
      _ ≤ canonicalBedfordTaylorMeasure Ω (truncationReal V k) hW (O ∩ U) +
          canonicalBedfordTaylorMeasure Ω (truncationReal V k) hW G := measure_union_le _ _
      _ ≤ (L + D * ENNReal.ofReal ε) + D * ENNReal.ofReal ε :=
          add_le_add ((hport _ hO'o hO'Ω).trans hliminf) ((hμG G).trans hcapG)
  -- let the budget tend to zero
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hpos : 0 < (max c (-(k : ℝ)) + 1 - -(k : ℝ)) ^ n := pow_pos (by linarith) n
  set ε : ℝ := (η : ℝ) / (2 * (max c (-(k : ℝ)) + 1 - -(k : ℝ)) ^ n) with hε
  have hεpos : 0 < ε := div_pos (by exact_mod_cast hη) (by positivity)
  have h := hkey ε hεpos
  have hcalc : D * ENNReal.ofReal ε + D * ENNReal.ofReal ε = (η : ℝ≥0∞) := by
    rw [hD, ← ENNReal.ofReal_mul hpos.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_coe_nnreal]
    congr 1
    rw [hε]
    field_simp
    ring
  rwa [add_assoc, hcalc] at h

/-! ### The general local statement -/

/-- **Lower semicontinuity of the non-pluripolar Monge–Ampère measure along
decreasing sequences** (DDNL, Theorem 2.6, local form; Xia, Theorem 2.4.2).  If
`v_j` decreases pointwise on `Ω` to a plurisubharmonic `V`, then on every open
`O ⊆ Ω`, `⟨(ddᶜ V)ⁿ⟩(O) ≤ liminf_j ⟨(ddᶜ v_j)ⁿ⟩(O)`. -/
theorem truncationLimitMeasure_le_liminf_of_antitone {Ω : Opens (ComplexModel n)}
    {v : ℕ → ComplexModel n → EReal} (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    (hanti : ∀ z ∈ Ω, Antitone fun j => v j z)
    {V : ComplexModel n → EReal} (hV : PlurisubharmonicOn V Ω)
    (hlim : ∀ z ∈ Ω, Tendsto (fun j => v j z) atTop (𝓝 (V z)))
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hOΩ : O ⊆ Ω) :
    truncationLimitMeasure Ω V hV O ≤
      liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) O) atTop := by
  rw [truncationLimitMeasure_apply]
  refine iSup_le fun k => ?_
  obtain ⟨Kc, hKc, -, hKO, hKmono, hKU⟩ := hO.exists_monotone_isCompact_iUnion_eq
  have hsup : truncationMeasure Ω V hV k O = ⨆ m, truncationMeasure Ω V hV k (Kc m) := by
    conv_lhs => rw [← hKU]
    exact hKmono.measure_iUnion
  rw [hsup]
  refine iSup_le fun m => ?_
  obtain ⟨δ, hδ, hδO⟩ := (hKc m).exists_cthickening_subset_open hO (hKO m)
  obtain ⟨C, -, hC⟩ := (hv 0).exists_nonnegative_compact_upper_bound
    (hKc m).cthickening (hδO.trans hOΩ)
  set U : Opens (ComplexModel n) := ⟨thickening δ (Kc m), isOpen_thickening⟩ with hU
  have hUO : (U : Set (ComplexModel n)) ⊆ O := (thickening_subset_cthickening δ _).trans hδO
  have hUΩ : U ≤ Ω := hUO.trans hOΩ
  have hvU : ∀ j, PlurisubharmonicOn (v j) U := fun j => (hv j).mono hUΩ
  have hVU : PlurisubharmonicOn V U := hV.mono hUΩ
  have hres : truncationMeasure Ω V hV k U = truncationMeasure U V hVU k U := by
    rw [← truncationMeasure_restrict_open hUΩ hV hVU k,
      Measure.restrict_apply U.isOpen.measurableSet, inter_self]
  have hresj : ∀ j, truncationLimitMeasure U (v j) (hvU j) U =
      truncationLimitMeasure Ω (v j) (hv j) U := by
    intro j
    rw [← truncationLimitMeasure_restrict_open hUΩ (hv j) (hvU j),
      Measure.restrict_apply U.isOpen.measurableSet, inter_self]
  calc truncationMeasure Ω V hV k (Kc m)
      ≤ truncationMeasure Ω V hV k U := measure_mono (self_subset_thickening hδ _)
    _ = truncationMeasure U V hVU k U := hres
    _ ≤ liminf (fun j => truncationLimitMeasure U (v j) (hvU j) U) atTop :=
        truncationMeasure_le_liminf_of_antitone_of_le hvU
          (fun z hz => hanti z (hUΩ hz)) hVU (fun z hz => hlim z (hUΩ hz))
          (fun z hz => hC z (thickening_subset_cthickening δ _ hz)) U.isOpen le_rfl k
    _ = liminf (fun j => truncationLimitMeasure Ω (v j) (hv j) U) atTop := by
        simp_rw [hresj]
    _ ≤ _ := liminf_le_liminf (Eventually.of_forall fun j => measure_mono hUO)

/-- The diagonal mixed form, in every dimension. -/
theorem mixedTruncationLimitMeasure_le_liminf_of_antitone
    {Ω : Opens (ComplexModel n)} {v : ℕ → ComplexModel n → EReal}
    (hv : ∀ j, PlurisubharmonicOn (v j) Ω)
    (hanti : ∀ z ∈ Ω, Antitone fun j => v j z)
    {V : ComplexModel n → EReal} (hV : PlurisubharmonicOn V Ω)
    (hlim : ∀ z ∈ Ω, Tendsto (fun j => v j z) atTop (𝓝 (V z)))
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hOΩ : O ⊆ Ω) :
    mixedTruncationLimitMeasure Ω (fun _ => V) (fun _ => hV) O ≤
      liminf (fun j => mixedTruncationLimitMeasure Ω (fun _ => v j) (fun _ => hv j) O)
        atTop := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hb : IsLocallyBoundedMixedPshOn Ω (fun i : Fin 0 => fun _ => (0 : ℝ)) :=
      fun i => Fin.elim0 i
    simp_rw [mixedTruncationLimitMeasure_zero_dim Ω _ _ _ hb]
    exact le_of_eq (liminf_const _).symm
  · simp_rw [mixedTruncationLimitMeasure_diagonal hn]
    exact truncationLimitMeasure_le_liminf_of_antitone hv hanti hV hlim hO hOΩ

end SGPT.Foundations.Analysis.Pending.DecreasingTruncationLimit
