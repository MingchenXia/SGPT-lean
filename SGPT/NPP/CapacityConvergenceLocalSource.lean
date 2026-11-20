import SGPT.NPP.CapacityConvergenceLocal
import SGPT.Toric.ThetaPSHExtension
import SGPT.NPP.BedfordTaylorTopDegree
import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
import SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc

/-!
# Local weak convergence under convergence in capacity (`thm:loc_conv_cap`)

Source `thm:loc_conv_cap` (chapter `chapter_npp.tex`; the book cites Guedj–Zeriahi,
Theorem 4.26; Xia, *Foundations of pluripotential theory*, `thm:bt-capacity-continuity`).

Let `X` be a compact Kähler manifold of dimension `n`, `θ_c` a closed real `(1,1)`-form of
big class (the reference of `Cap_{θ_c}`, `def:cap`), `U ⊆ X` open, and `θ_1, …, θ_p` closed real
smooth `(1,1)`-forms. Let `χ_i : U → [0, ∞)` be uniformly bounded quasi-continuous functions
converging in capacity to `χ : U → [0, ∞)`, and for each `j` let `φ_j^i` be uniformly bounded
`θ_j`-psh functions on `U` converging in capacity to a bounded `θ_j`-psh function `φ_j`. Then
`χ_i ⋀_j θ_{j,φ_j^i} ⇀ χ ⋀_j θ_{j,φ_j}` weakly as currents on `U`.

## Formalization

The current `⋀_j θ_{j,φ_j}` (bidegree `(p,p)`, bidimension `(q,q)`, `q + p = n`) on `U` is the
current whose expression on every coordinate patch `D ⊆ e(U)` carrying smooth local potentials
`ρ_j` of the `θ_j` (`dd^c ρ_j = θ_j` on `D`) is the Bedford–Taylor product
`dd^c(ρ_1 + φ_1 ∘ e⁻¹) ∧ ⋯ ∧ dd^c(ρ_p + φ_p ∘ e⁻¹)` of the locally bounded psh functions
`ρ_j + φ_j ∘ e⁻¹`; weak convergence of currents on `U` is weak convergence of all these local
expressions (weak convergence is local, `weakTendsto_of_local`). The theorem
`sourceLocConvCap` proves the weak convergence on **every** such patch, for **every** choice
of the local potentials.

The weighted current `χ T` of a positive current `T` of order zero is the multiplication of
its coefficient measures by `χ` (`mulBorel`, defined for locally bounded Borel weights). The
limit weight `χ` is only `[0, ∞)`-valued in the source; since `χ_i ≤ A`,
`sourceThetaCapacity_limit_gt_eq_zero` shows `Cap_{θ_c}({χ > A}) = 0`, so `χ = min(χ, A)`
quasi-everywhere and the current the source writes `χ ⋀_j θ_{j,φ_j}` is
`min(χ, A) ⋀_j θ_{j,φ_j}` (Bedford–Taylor products of bounded potentials do not charge sets of
capacity zero); this is the limit in `sourceLocConvCap`.

Proof: on small balls `V ⋐ D` carrying a local potential of the Kähler form, the potentials are
uniformly bounded; the products are tested on the products `β_1 ∧ ⋯ ∧ β_q` of constant
semipositive forms, which turns them into top-degree measures with the quadratic potentials of
the `β_k` in the remaining slots (`mulBorel_btProduct_apply_wedgeProd_of_ddc`); the source
convergence in `Cap_{θ_c}` gives convergence in Kähler capacity
(`exists_source_capacity_control`), hence in relative capacity on compact subsets
(`exists_compact_capacity_reverse`), and `local_tendsto_integral_moving` applies.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal Distributions

namespace SGPT.NPP.CapacityConvergence

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open ThetaCapacity CapacityWeightedConvergence BedfordTaylor MixedMongeAmpere ChartPartition
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The zero extension of a continuous chart test supported in the target is continuous. -/
theorem continuous_chartExtend_of_tsupport (e : ComplexChart n M)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ e.val.target) : Continuous (chartExtend e h) := by
  have hK : IsCompact (e.val.symm '' tsupport h) :=
    hk.image_of_continuousOn (e.val.symm.continuousOn.mono ht)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ e.val.symm '' tsupport h
  · obtain ⟨z, hz, hzx⟩ := hx
    have hxS : x ∈ e.val.source := hzx ▸ e.val.map_target (ht hz)
    have hh : ContinuousAt (fun y => h (e.val y)) x :=
      hc.continuousAt.comp (e.val.continuousAt hxS)
    apply hh.congr
    filter_upwards [e.val.open_source.mem_nhds hxS] with y hy
    exact (chartExtend_of_mem hy).symm
  · apply continuousAt_const.congr
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact (chartExtend_eq_zero_of_notMem_image hy).symm

/-- A source `θ`-psh function on `U`, read in a chart on a coordinate patch inside `U` carrying a
smooth local potential of `θ`, is psh after adding the potential. -/
theorem plurisubharmonicOn_chart_of_isThetaPSHOn
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {U : Set M} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSHOn θ φ U) (e : ComplexChart n M)
    {D : Set (ComplexModel n)} (hDU : ∀ z ∈ D, e.val.symm z ∈ U) {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e D ρ) :
    PlurisubharmonicOn (fun z => φ (e.val.symm z) + (ρ z : EReal)) D := by
  let V : Set M := e.val.source ∩ e.val ⁻¹' D
  have hg : (ofFixedModel n M).IsAtlasLocalPotential θ V (ρ ∘ e.val) :=
    coordinate_potential_isAtlasLocalPotential (A := ofFixedModel n M) θ e hρ.1 hρ.2.1
      hρ.2.2.1 hρ.2.2.2
  have hVU : V ⊆ U := by
    rintro x ⟨hxs, hxD⟩
    have := hDU _ hxD
    rwa [e.val.left_inv hxs] at this
  have hp := (hφ.2 V (ρ ∘ e.val) hVU hg).chartPlurisubharmonic e
  have hsub : D ⊆ e.val.target ∩ e.val.symm ⁻¹' V := by
    intro y hy
    refine ⟨hρ.2.1 hy, e.val.map_target (hρ.2.1 hy), ?_⟩
    change e.val (e.val.symm y) ∈ D
    rw [e.val.right_inv (hρ.2.1 hy)]
    exact hy
  exact SGPT.Foundations.Analysis.plurisubharmonicOn_congr hρ.1 (hp.mono hsub) (fun y hy => by
    change φ (e.val.symm y) + (ρ (e.val (e.val.symm y)) : EReal) =
      φ (e.val.symm y) + (ρ y : EReal)
    rw [e.val.right_inv (hρ.2.1 hy)])

/-- With a finite bound on `U`, the corrected chart read is a locally bounded psh function. -/
theorem isLocallyBoundedPshOn_chart_of_isThetaPSHOn
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {U : Set M} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSHOn θ φ U) {B : ℝ}
    (hφB : ∀ x ∈ U, ((-B : ℝ) : EReal) ≤ φ x ∧ φ x ≤ (B : EReal)) (e : ComplexChart n M)
    {D : Opens (ComplexModel n)} (hDU : ∀ z ∈ D, e.val.symm z ∈ U) {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e D ρ) :
    IsLocallyBoundedPshOn D (fun z => ρ z + (φ (e.val.symm z)).toReal) := by
  have hfin : ∀ z ∈ D, φ (e.val.symm z) = ((φ (e.val.symm z)).toReal : EReal) := fun z hz =>
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top B) (hφB _ (hDU z hz)).2)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hφB _ (hDU z hz)).1)).symm
  have hreal : ∀ z ∈ D, |(φ (e.val.symm z)).toReal| ≤ B := by
    intro z hz
    have h := hφB _ (hDU z hz)
    rw [hfin z hz] at h
    exact abs_le.mpr ⟨EReal.coe_le_coe_iff.mp h.1, EReal.coe_le_coe_iff.mp h.2⟩
  refine ⟨?_, fun z hz => ?_⟩
  · refine SGPT.Foundations.Analysis.plurisubharmonicOn_congr D.isOpen
      (plurisubharmonicOn_chart_of_isThetaPSHOn hφ e hDU hρ) (fun z hz => ?_)
    change φ (e.val.symm z) + (ρ z : EReal) = ((ρ z + (φ (e.val.symm z)).toReal : ℝ) : EReal)
    rw [EReal.coe_add, add_comm, ← hfin z hz]
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp D.isOpen z hz
    have hcb : IsCompact (Metric.closedBall z (r / 2)) := isCompact_closedBall z (r / 2)
    have hcbD : Metric.closedBall z (r / 2) ⊆ D :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨R, hR⟩ := hcb.exists_bound_of_continuousOn (hρ.2.2.1.continuousOn.mono hcbD)
    refine ⟨⟨Metric.ball z (r / 2), Metric.isOpen_ball⟩, Metric.mem_ball_self (by linarith),
      fun w hw => hcbD (Metric.ball_subset_closedBall hw), R + B, fun w hw => ?_⟩
    have hwD : w ∈ D := hcbD (Metric.ball_subset_closedBall hw)
    have h1 := hR w (Metric.ball_subset_closedBall hw)
    rw [Real.norm_eq_abs] at h1
    exact (abs_add_le _ _).trans (add_le_add h1 (hreal w hwD))

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Source convergence in capacity on `U` (for a big class) of real functions gives
convergence of the absolute gaps on `U` in Kähler capacity. -/
theorem kahler_gap_tendsto_of_source_on (ω : KahlerBackground n M)
    (θc : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θc)))
    (U : Opens M) {f : ℕ → M → ℝ} {g : M → ℝ}
    (h : SourceTendstoInCapacity θc U (fun i (x : U) => (f i x.1 : EReal)) atTop
      (fun x => (g x.1 : EReal))) :
    ∀ c : ℝ, 0 < c → Tendsto (fun i => thetaCapacity ω.form (fun _ => 0)
      {x | x ∈ U ∧ c < |f i x - g x|}) atTop (𝓝 0) := by
  intro c hc
  have hu := ((sourceTendstoInCapacity_iff_union θc U _ atTop _).mp h).2.2 c hc
  have hset (i : ℕ) :
      sourceCapacityUpperGap U (fun x : U => (f i x.1 : EReal)) (fun x => (g x.1 : EReal)) c ∪
        sourceCapacityLowerGap U (fun x : U => (f i x.1 : EReal)) (fun x => (g x.1 : EReal)) c =
        {x | x ∈ U ∧ c < |f i x - g x|} := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ U := by
        rcases hx with ⟨y, _, rfl⟩ | ⟨y, _, rfl⟩ <;> exact y.2
      exact ⟨hxU, (sourceCapacityGap_coe_iff U (fun y : U => f i y.1) (fun y : U => g y.1) c
        ⟨x, hxU⟩).mp hx⟩
    · rintro ⟨hxU, hx⟩
      exact (sourceCapacityGap_coe_iff U (fun y : U => f i y.1) (fun y : U => g y.1) c
        ⟨x, hxU⟩).mpr hx
  have hmeas (i : ℕ) : MeasurableSet {x | x ∈ U ∧ c < |f i x - g x|} := by
    rw [← hset i]
    exact (measurableSet_sourceCapacityUpperGap U (h.1 i) h.2.1 c).union
      (measurableSet_sourceCapacityLowerGap U (h.1 i) h.2.1 c)
  simp only [hset] at hu
  exact SGPT.NPP.source_capacity_tendsto_implies_kahler ω θc hbig _ hmeas hu

/-- A source quasi-continuous function on `U`, cut off by a continuous function supported in a
closed subset of `U`, is a Borel quasi-continuous function on the whole manifold for the
Kähler capacity. -/
theorem quasiContinuousFor_kahler_cutoff (ω : KahlerBackground n M)
    (θc : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θc)))
    (U : Opens M) {χ : M → ℝ} (hχ : SourceQuasiContinuousOn θc U (fun x => (χ x.1 : EReal)))
    {b : M → ℝ} (hb : Continuous b) {S : Set M} (hS : IsClosed S) (hSU : S ⊆ U)
    (hbS : tsupport b ⊆ S) :
    Measurable (fun x => b x * χ x) ∧
      QuasiContinuousFor (thetaCapacity ω.form (fun _ => 0)) (fun x => b x * χ x) := by
  have hb0 : ∀ x, x ∉ S → b x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hbS h))
  refine ⟨?_, ?_⟩
  · apply measurable_of_restrict_of_restrict_compl U.isOpen.measurableSet
    · have hχU : Measurable (fun x : U => χ x.1) := by
        have h := measurable_ereal_toReal.comp hχ.1
        simpa only [Function.comp_def, EReal.toReal_coe] using h
      exact (hb.measurable.comp measurable_subtype_coe).mul (hχU : _)
    · have heq : (U : Set M)ᶜ.domRestrict (fun x => b x * χ x) = fun _ => 0 := by
        funext x
        rw [Set.domRestrict_apply, hb0 x.1 (fun h => x.2 (hSU h)), zero_mul]
      rw [heq]
      exact measurable_const
  · intro η hη
    obtain ⟨r, _hr0, hrpos, hrη⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
    have hr : 0 < r := ENNReal.ofReal_pos.mp hrpos
    have hε : 0 < r / 2 := half_pos hr
    obtain ⟨Cc, hCc, hcontrol⟩ := SGPT.NPP.exists_source_capacity_control ω θc hbig hε
    obtain ⟨G, hGo, hGU, hGcap, hreal⟩ := hχ.2 (r / 2 / Cc) (div_pos hε hCc)
    refine ⟨G, hGo, ?_, ?_⟩
    · calc thetaCapacity ω.form (fun _ => 0) G
          ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal Cc * sourceThetaCapacity θc G :=
            hcontrol G hGo.measurableSet
        _ ≤ ENNReal.ofReal (r / 2) + ENNReal.ofReal Cc * ENNReal.ofReal (r / 2 / Cc) :=
            add_le_add le_rfl (mul_le_mul_right hGcap _)
        _ = ENNReal.ofReal r := by
            rw [← ENNReal.ofReal_mul hCc.le, mul_div_cancel₀ _ hCc.ne',
              ← ENNReal.ofReal_add hε.le hε.le, add_halves]
        _ < η := hrη
    · obtain ⟨g, hg, hfg⟩ := hreal
      intro x hx
      by_cases hxS : x ∈ S
      · have hxU : x ∈ U := hSU hxS
        -- on `Gᶜ ∩ U`, `χ` is the continuous representative `g`
        let T : Set (U : Set M) := {y | y.1 ∉ G}
        let ψ : ↥(Gᶜ ∩ (U : Set M)) → T := fun y => ⟨⟨y.1, y.2.2⟩, y.2.1⟩
        have hψ : Continuous ψ :=
          ((continuous_subtype_val.subtype_mk _).subtype_mk _)
        have hres : (Gᶜ ∩ (U : Set M)).domRestrict χ = fun y => T.domRestrict g (ψ y) := by
          funext y
          have h := hfg (show (⟨y.1, y.2.2⟩ : (U : Set M)) ∈ T from y.2.1)
          exact EReal.coe_injective h
        have hχc : ContinuousOn χ (Gᶜ ∩ (U : Set M)) := by
          rw [continuousOn_iff_continuous_domRestrict, hres]
          exact (continuousOn_iff_continuous_domRestrict.mp hg).comp hψ
        have hloc : ContinuousWithinAt (fun y => b y * χ y) (Gᶜ ∩ (U : Set M)) x :=
          hb.continuousAt.continuousWithinAt.mul (hχc x ⟨hx, hxU⟩)
        exact (continuousWithinAt_inter (U.isOpen.mem_nhds hxU)).mp hloc
      · apply ContinuousAt.continuousWithinAt
        apply continuousAt_const.congr
        filter_upwards [hS.isOpen_compl.mem_nhds hxS] with y hy
        rw [hb0 y hy, zero_mul]

omit [IsComplexManifold n M] [CompactSpace M] in
/-- A cut-off function measurable on `U` is measurable on the manifold. -/
theorem measurable_cutoff_mul (U : Opens M) {χ : M → ℝ}
    (hχ : Measurable (fun x : U => χ x.1)) {b : M → ℝ} (hb : Continuous b) {S : Set M}
    (hSU : S ⊆ U) (hbS : tsupport b ⊆ S) : Measurable (fun x => b x * χ x) := by
  have hb0 : ∀ x, x ∉ S → b x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hbS h))
  apply measurable_of_restrict_of_restrict_compl U.isOpen.measurableSet
  · exact (hb.measurable.comp measurable_subtype_coe).mul (hχ : _)
  · have heq : (U : Set M)ᶜ.domRestrict (fun x => b x * χ x) = fun _ => 0 := by
      funext x
      rw [Set.domRestrict_apply, hb0 x.1 (fun h => x.2 (hSU h)), zero_mul]
    rw [heq]
    exact measurable_const

omit [CompactSpace M] [IsComplexManifold n M] in
/-- The chart read of a function measurable on `U`, on a coordinate patch inside `U`, is
measurable. -/
theorem measurable_indicator_read_of_on (U : Opens M) {w : M → ℝ}
    (hw : Measurable (fun x : U => w x.1)) (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target) (hDU : ∀ z ∈ D, e.val.symm z ∈ U) :
    Measurable ((D : Set (ComplexModel n)).indicator fun z => w (e.val.symm z)) := by
  apply measurable_of_restrict_of_restrict_compl D.isOpen.measurableSet
  · have hc : Continuous (fun z : (D : Set (ComplexModel n)) =>
        (⟨e.val.symm z.1, hDU z.1 z.2⟩ : U)) :=
      ((e.val.continuousOn_symm.mono hDt).domRestrict).subtype_mk _
    have heq : (D : Set (ComplexModel n)).domRestrict
        ((D : Set (ComplexModel n)).indicator fun z => w (e.val.symm z)) =
        (fun x : U => w x.1) ∘ (fun z : (D : Set (ComplexModel n)) =>
          (⟨e.val.symm z.1, hDU z.1 z.2⟩ : U)) := by
      funext z
      simp only [Set.domRestrict_apply, Function.comp_apply, indicator_of_mem z.2]
    rw [heq]
    exact (hw : _).comp hc.measurable
  · have heq : (D : Set (ComplexModel n))ᶜ.domRestrict
        ((D : Set (ComplexModel n)).indicator fun z => w (e.val.symm z)) = fun _ => 0 := by
      funext z
      exact indicator_of_notMem z.2 _
    rw [heq]
    exact measurable_const

omit [BorelSpace M] in
/-- **The limit weight is bounded quasi-everywhere**: if `χ_i ≤ A` on `U` and `χ_i → χ` in
capacity, then `Cap_{θ_c}({x ∈ U : χ(x) > A}) = 0`. -/
theorem sourceThetaCapacity_limit_gt_eq_zero
    (θc : AtlasClosedRealOneOneForm (ofFixedModel n M)) (U : Opens M)
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} {A : ℝ} (hχA : ∀ i, ∀ x ∈ U, χ i x ≤ A)
    (hχcap : SourceTendstoInCapacity θc U (fun i (x : U) => (χ i x.1 : EReal)) atTop
      (fun x => (χ₀ x.1 : EReal))) :
    sourceThetaCapacity θc {x | x ∈ U ∧ A < χ₀ x} = 0 := by
  have hstep (δ : ℝ) (hδ : 0 < δ) : sourceThetaCapacity θc {x | x ∈ U ∧ A + δ < χ₀ x} = 0 := by
    have hlim := (hχcap.2.2 δ hδ).2
    refine le_antisymm (ge_of_tendsto hlim (Eventually.of_forall fun i => ?_)) zero_le
    refine sourceThetaCapacity_mono θc ?_
    rintro x ⟨hxU, hx⟩
    refine (mem_sourceCapacityLowerGap U _ _ δ ⟨x, hxU⟩).mpr ?_
    change ((χ i x : ℝ) : EReal) < (χ₀ x : EReal) - (δ : EReal)
    rw [← EReal.coe_sub, EReal.coe_lt_coe_iff]
    linarith [hχA i x hxU]
  have hunion : {x | x ∈ U ∧ A < χ₀ x} =
      ⋃ m : ℕ, {x | x ∈ U ∧ A + 1 / ((m : ℝ) + 1) < χ₀ x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hxU, hx⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < χ₀ x - A by linarith)
      exact ⟨m, hxU, by linarith⟩
    · rintro ⟨m, hxU, hx⟩
      have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      exact ⟨hxU, by linarith⟩
  rw [hunion, sourceThetaCapacity_eq_native]
  refine le_antisymm ((ThetaCapacity.thetaCapacity_iUnion_le _ _ _).trans ?_) zero_le
  have h0 (m : ℕ) : ThetaCapacity.thetaCapacityV (atlasClosedFormToNative θc)
      {x | x ∈ U ∧ A + 1 / ((m : ℝ) + 1) < χ₀ x} = 0 := by
    rw [← sourceThetaCapacity_eq_native]
    exact hstep _ (by positivity)
  simp only [ThetaCapacity.thetaCapacityV] at h0
  simp only [h0, tsum_zero, le_refl]

private theorem restrict_oneCurrentOf' {k : ℕ} {U V : Opens (ComplexModel n)} (hk : k = n)
    (hVU : V ≤ U) :
    LocalBedfordTaylorLocality.restrict hVU (LocalBedfordTaylorProducts.oneCurrentOf (U := U) hk) =
      LocalBedfordTaylorProducts.oneCurrentOf (U := V) hk := by
  subst hk
  exact SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc.restrict_oneCurrent hVU

open LocalBedfordTaylorProducts LocalProductCurrents LocalBedfordTaylorLocality in
/-- **`thm:loc_conv_cap`**: local weak convergence of the weighted products
`χ_i ⋀_j θ_{j,φ_j^i} ⇀ χ ⋀_j θ_{j,φ_j}` on `U`, tested on every coordinate patch `D ⊆ e(U)`
with every choice of smooth local potentials `ρ_j` of the `θ_j` (the local expression of
`⋀_j θ_{j,φ_j}` on `D` is `⋀_j dd^c(ρ_j + φ_j ∘ e⁻¹)`). The limit weight is `min(χ, A)`, which
equals `χ` quasi-everywhere (`sourceThetaCapacity_limit_gt_eq_zero`). -/
theorem sourceLocConvCap (ω : KahlerBackground n M)
    (θc : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θc)))
    (U : Opens M) {p q : ℕ} (hqp : q + p = n)
    (θ : Fin p → AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : ℕ → Fin p → M → EReal} {φ₀ : Fin p → M → EReal}
    (hφ : ∀ i j, (ofFixedModel n M).IsThetaPSHOn (θ j) (φ i j) U)
    (hφ₀ : ∀ j, (ofFixedModel n M).IsThetaPSHOn (θ j) (φ₀ j) U)
    {B B₀ : ℝ} (hφB : ∀ i j, ∀ x ∈ U, ((-B : ℝ) : EReal) ≤ φ i j x ∧ φ i j x ≤ (B : EReal))
    (hφ₀B : ∀ j, ∀ x ∈ U, ((-B₀ : ℝ) : EReal) ≤ φ₀ j x ∧ φ₀ j x ≤ (B₀ : EReal))
    (hφcap : ∀ j, SourceTendstoInCapacity θc U (fun i (x : U) => φ i j x.1) atTop
      (fun x => φ₀ j x.1))
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} {A : ℝ}
    (hχA : ∀ i, ∀ x ∈ U, 0 ≤ χ i x ∧ χ i x ≤ A) (hχ₀0 : ∀ x ∈ U, 0 ≤ χ₀ x)
    (hχqc : ∀ i, SourceQuasiContinuousOn θc U (fun x => (χ i x.1 : EReal)))
    (hχcap : SourceTendstoInCapacity θc U (fun i (x : U) => (χ i x.1 : EReal)) atTop
      (fun x => (χ₀ x.1 : EReal)))
    (e : ComplexChart n M) (D : Opens (ComplexModel n))
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target) (hDU : ∀ z ∈ D, e.val.symm z ∈ U)
    (ρ : Fin p → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential (atlasClosedFormToNative (θ j)).val e D (ρ j)) :
    LocalBedfordTaylorContinuity.WeakTendsto
      (fun i => mulBorel (btProduct p q (fun j z => ρ j z + (φ i j (e.val.symm z)).toReal)
          (oneCurrentOf (U := D) hqp))
        ((D : Set (ComplexModel n)).indicator fun z => χ i (e.val.symm z)))
      (mulBorel (btProduct p q (fun j z => ρ j z + (φ₀ j (e.val.symm z)).toReal)
          (oneCurrentOf (U := D) hqp))
        ((D : Set (ComplexModel n)).indicator fun z => min (χ₀ (e.val.symm z)) A)) := by
  classical
  subst hqp
  -- the potentials and weights on `D`
  let uu (i : ℕ) : Fin p → ComplexModel (q + p) → ℝ :=
    fun j z => ρ j z + (φ i j (e.val.symm z)).toReal
  let u0 : Fin p → ComplexModel (q + p) → ℝ := fun j z => ρ j z + (φ₀ j (e.val.symm z)).toReal
  have huuD (i : ℕ) : ∀ j, IsLocallyBoundedPshOn D (uu i j) := fun j =>
    isLocallyBoundedPshOn_chart_of_isThetaPSHOn (hφ i j) (hφB i j) e (D := D) hDU (hρ j)
  have hu0D : ∀ j, IsLocallyBoundedPshOn D (u0 j) := fun j =>
    isLocallyBoundedPshOn_chart_of_isThetaPSHOn (hφ₀ j) (hφ₀B j) e (D := D) hDU (hρ j)
  let g (i : ℕ) : ComplexModel (q + p) → ℝ :=
    (D : Set (ComplexModel (q + p))).indicator fun z => χ i (e.val.symm z)
  let g0 : ComplexModel (q + p) → ℝ :=
    (D : Set (ComplexModel (q + p))).indicator fun z => min (χ₀ (e.val.symm z)) A
  have hχm (i : ℕ) : Measurable (fun x : U => χ i x.1) := by
    have h := measurable_ereal_toReal.comp (hχqc i).1
    simpa only [Function.comp_def, EReal.toReal_coe] using h
  have hχ₀m : Measurable (fun x : U => χ₀ x.1) := by
    have h := measurable_ereal_toReal.comp hχcap.2.1
    simpa only [Function.comp_def, EReal.toReal_coe] using h
  have hχ₀mA : Measurable (fun x : U => min (χ₀ x.1) A) := hχ₀m.min measurable_const
  have hgm (i : ℕ) : Measurable (g i) := measurable_indicator_read_of_on U (hχm i) e hDt hDU
  have hg0m : Measurable g0 :=
    measurable_indicator_read_of_on U (w := fun x => min (χ₀ x) A) hχ₀mA e hDt hDU
  have hχabs (i : ℕ) (x : M) (hx : x ∈ U) : |χ i x| ≤ |A| := by
    rw [abs_of_nonneg (hχA i x hx).1]
    exact (hχA i x hx).2.trans (le_abs_self A)
  have hminabs (x : M) (hx : x ∈ U) : |min (χ₀ x) A| ≤ |A| := by
    rw [abs_le]
    constructor
    · exact le_min ((neg_nonpos.mpr (abs_nonneg A)).trans (hχ₀0 x hx)) (neg_abs_le A)
    · exact (min_le_right _ _).trans (le_abs_self A)
  have hgb (i : ℕ) (z : ComplexModel (q + p)) : |g i z| ≤ |A| := by
    by_cases hz : z ∈ D
    · simp only [g, indicator_of_mem hz]; exact hχabs i _ (hDU z hz)
    · simp only [g, indicator_of_notMem hz, abs_zero]; exact abs_nonneg A
  have hg0b (z : ComplexModel (q + p)) : |g0 z| ≤ |A| := by
    by_cases hz : z ∈ D
    · simp only [g0, indicator_of_mem hz]; exact hminabs _ (hDU z hz)
    · simp only [g0, indicator_of_notMem hz, abs_zero]; exact abs_nonneg A
  have hlb {S : Set (ComplexModel (q + p))} {f : ComplexModel (q + p) → ℝ}
      (hf : ∀ z, |f z| ≤ |A|) : LocalProductCurrents.IsLocallyBoundedOn f S :=
    fun _ _ _ => ⟨|A|, fun x _ => hf x⟩
  have hSD (w : Fin p → ComplexModel (q + p) → ℝ) (hw : ∀ j, IsLocallyBoundedPshOn D (w j)) :=
    isPositive_btProduct p q w (oneCurrentOf (U := D) rfl) (isPositive_oneCurrentOf _)
      (isClosedAny_oneCurrentOf _) hw
  -- localize to small balls carrying a Kähler potential
  refine LocalBedfordTaylorDecreasing.weakTendsto_of_local fun z₀ hz₀ => ?_
  obtain ⟨W, ρω, hz₀W, hρω⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials ω.form e z₀ (hDt hz₀)
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp (D.isOpen.inter hρω.1) z₀ ⟨hz₀, hz₀W⟩
  let V : Opens (ComplexModel (q + p)) := ⟨Metric.ball z₀ (r / 2), Metric.isOpen_ball⟩
  have hcl : Metric.closedBall z₀ (r / 2) ⊆ (D : Set (ComplexModel (q + p))) ∩ W :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrball
  have hVD : V ≤ D := fun z hz => (hcl (Metric.ball_subset_closedBall hz)).1
  have hVW : (V : Set (ComplexModel (q + p))) ⊆ W :=
    fun z hz => (hcl (Metric.ball_subset_closedBall hz)).2
  have hVt : (V : Set (ComplexModel (q + p))) ⊆ e.val.target := fun z hz => hDt (hVD hz)
  refine ⟨V, hVD, Metric.mem_ball_self (by linarith), fun γ ψ => ?_⟩
  -- restriction to `V`
  have hres (w : Fin p → ComplexModel (q + p) → ℝ) (hw : ∀ j, IsLocallyBoundedPshOn D (w j))
      (gg : ComplexModel (q + p) → ℝ) (hggm : Measurable gg) (hggb : ∀ z, |gg z| ≤ |A|) :
      mulBorel (btProduct p q w (oneCurrentOf (U := D) rfl)) gg γ (extTest hVD ψ) =
      mulBorel (btProduct p q w (oneCurrentOf (U := V) rfl)) gg γ ψ := by
    rw [← LocalBedfordTaylorLocality.restrict_apply hVD,
      ← LocalBedfordTaylorLocality.mulBorel_restrict (hSD w hw).1 hVD hggm (hlb hggb),
      ← LocalBedfordTaylorLocality.btProduct_restrict hVD p q w _ (isPositive_oneCurrentOf _)
        (isClosedAny_oneCurrentOf _) hw, restrict_oneCurrentOf']
  have huuV (i : ℕ) : ∀ j, IsLocallyBoundedPshOn V (uu i j) := fun j =>
    isLocallyBoundedPshOn_mono (huuD i j) hVD
  have hu0V : ∀ j, IsLocallyBoundedPshOn V (u0 j) := fun j => isLocallyBoundedPshOn_mono (hu0D j) hVD
  suffices key : LocalBedfordTaylorContinuity.WeakTendsto
      (fun i => mulBorel (btProduct p q (uu i) (oneCurrentOf (U := V) rfl)) (g i))
      (mulBorel (btProduct p q u0 (oneCurrentOf (U := V) rfl)) g0) by
    have h := key γ ψ
    rw [← hres u0 hu0D g0 hg0m hg0b] at h
    refine h.congr fun i => ?_
    exact (hres (uu i) (huuD i) (g i) (hgm i) (hgb i)).symm
  refine SGPT.NPP.BedfordTaylorTopDegree.weakTendsto_of_wedgeProd _ _ fun β hβ hP ψ => ?_
  let ℓ : Fin q → ComplexModel (q + p) → ℝ := fun k => SGPT.NPP.BedfordTaylorTopDegree.quadPot (β k)
  have hℓ : ∀ k, IsLocallyBoundedPshOn V (ℓ k) := fun k =>
    SGPT.NPP.BedfordTaylorTopDegree.isLocallyBoundedPshOn_quadPot (hβ k) V
  have hwedge (w : Fin p → ComplexModel (q + p) → ℝ) (hwV : ∀ j, IsLocallyBoundedPshOn V (w j))
      (gg : ComplexModel (q + p) → ℝ) (hggm : Measurable gg) (hggb : ∀ z, |gg z| ≤ |A|) :
      mulBorel (btProduct p q w (oneCurrentOf (U := V) rfl)) gg
          ⟨TopDegreeDensity.wedgeProd q β, hP⟩ ψ =
        ∫ x, ψ x * gg x ∂canonicalMixedBedfordTaylorMeasure V (Fin.append ℓ w)
          (SGPT.NPP.BedfordTaylorTopDegree.isLocallyBoundedPshOn_append hℓ hwV) := by
    rw [SGPT.NPP.BedfordTaylorTopDegree.mulBorel_btProduct_apply_wedgeProd_of_ddc p q w hwV β ℓ
      (fun k => (SGPT.NPP.BedfordTaylorTopDegree.contDiff_quadPot _).contDiffOn) hℓ
      (fun k x _ => SGPT.NPP.BedfordTaylorTopDegree.smoothDDC_quadPot (hβ k).1 x) hP hggm
      (hlb hggb) ψ]
    congr 1
    exact localMixedBedfordTaylorMeasure_unique
      (LocalBedfordTaylorCanonicalTraceMeasure.isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure _)
      (canonicalMixedBedfordTaylorMeasure_spec _ _ _)
  rw [hwedge u0 hu0V g0 hg0m hg0b]
  simp only [hwedge (uu _) (huuV _) (g _) (hgm _) (hgb _)]
  -- the cutoff
  have hKc : IsCompact (tsupport (ψ : ComplexModel (q + p) → ℝ)) := ψ.hasCompactSupport
  have hKV : tsupport (ψ : ComplexModel (q + p) → ℝ) ⊆ V := ψ.tsupport_subset
  obtain ⟨L, hLc, hKL, hLV⟩ := exists_compact_between hKc V.isOpen hKV
  obtain ⟨f, hf1, hf0, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hKc
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKL)
  have hfL : tsupport (f : ComplexModel (q + p) → ℝ) ⊆ L := by
    refine closure_minimal (fun z hz => ?_) hLc.isClosed
    by_contra hzL
    exact hz (hf0 (fun hzi => hzL (interior_subset hzi)))
  have hLt : L ⊆ e.val.target := hLV.trans hVt
  let bM : M → ℝ := chartExtend e f
  have hbM : Continuous bM :=
    continuous_chartExtend_of_tsupport e f.continuous hfc (hfL.trans hLt)
  let S : Set M := e.val.symm '' L
  have hSc : IsCompact S := hLc.image_of_continuousOn (e.val.continuousOn_symm.mono hLt)
  have hSU : S ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hDU z (hVD (hLV hz))
  have hbS : tsupport bM ⊆ S :=
    SGPT.Foundations.Analysis.Pending.SlotTestForms.tsupport_chartExtend_subset hLc hLt hfL
  have hbM01 (x : M) : 0 ≤ bM x ∧ bM x ≤ 1 := by
    by_cases hx : x ∈ e.val.source
    · simp only [bM, chartExtend_of_mem hx]; exact hf01 _
    · simp only [bM, chartExtend_of_notMem hx]; exact ⟨le_rfl, zero_le_one⟩
  have hbM0 (x : M) (hx : x ∉ S) : bM x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hbS h))
  have hbM1 (z : ComplexModel (q + p)) (hz : z ∈ tsupport (ψ : ComplexModel (q + p) → ℝ)) :
      bM (e.val.symm z) = 1 := by
    have hzt : z ∈ e.val.target := hVt (hKV hz)
    simp only [bM, chartExtend_of_mem (e.val.map_target hzt), e.val.right_inv hzt]
    exact hf1 hz
  let χt (i : ℕ) : M → ℝ := fun x => bM x * χ i x
  let χt₀ : M → ℝ := fun x => bM x * min (χ₀ x) A
  have hχtQC (i : ℕ) := quasiContinuousFor_kahler_cutoff ω θc hbig U (hχqc i) hbM hSc.isClosed
    hSU hbS
  have hχt₀m : Measurable χt₀ :=
    measurable_cutoff_mul U (χ := fun x => min (χ₀ x) A) hχ₀mA hbM hSU hbS
  have hcutabs {w : M → ℝ} (hw : ∀ x ∈ U, |w x| ≤ |A|) (x : M) : |bM x * w x| ≤ |A| := by
    by_cases hxS : x ∈ S
    · rw [abs_mul, abs_of_nonneg (hbM01 x).1]
      exact (mul_le_mul (hbM01 x).2 (hw x (hSU hxS)) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    · rw [hbM0 x hxS, zero_mul, abs_zero]; exact abs_nonneg A
  have hχtcap : ∀ c : ℝ, 0 < c → Tendsto (fun i => thetaCapacity ω.form (fun _ => 0)
      {x | c < |χt i x - χt₀ x|}) atTop (𝓝 0) := by
    intro c hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (kahler_gap_tendsto_of_source_on ω θc hbig U hχcap c hc) (fun _ => zero_le)
      (fun i => thetaCapacity_mono ?_)
    intro x hx
    change c < |bM x * χ i x - bM x * min (χ₀ x) A| at hx
    by_cases hxS : x ∈ S
    · have hxU := hSU hxS
      refine ⟨hxU, lt_of_lt_of_le hx ?_⟩
      rw [← mul_sub, abs_mul, abs_of_nonneg (hbM01 x).1]
      refine (mul_le_of_le_one_left (abs_nonneg _) (hbM01 x).2).trans ?_
      have h0 := (hχA i x hxU).1
      have h1 := (hχA i x hxU).2
      by_cases hmin : χ₀ x ≤ A
      · rw [min_eq_left hmin]
      · have hA' : A < χ₀ x := lt_of_not_ge hmin
        rw [min_eq_right hA'.le, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    · rw [hbM0 x hxS, zero_mul, zero_mul, sub_zero, abs_zero] at hx
      exact absurd hx (not_lt.mpr hc.le)
  -- the integrands
  have hint (gg : ComplexModel (q + p) → ℝ) (w : M → ℝ)
      (hgg : ∀ z ∈ V, gg z = w (e.val.symm z)) (μ : Measure (ComplexModel (q + p))) :
      (∫ x, ψ x * gg x ∂μ) = ∫ y, (fun x => bM x * w x) (e.val.symm y) * ψ y ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ tsupport (ψ : ComplexModel (q + p) → ℝ)
    · simp only [hgg y (hKV hy), hbM1 y hy, one_mul, mul_comm]
    · have hψ0 : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp only [hψ0, zero_mul, mul_zero]
  rw [hint g0 (fun x => min (χ₀ x) A) (fun z hz => indicator_of_mem (hVD hz) _)]
  simp only [hint (g _) (χ _) (fun z hz => indicator_of_mem (hVD hz) _)]
  -- uniform box bound on `V`
  have hcbV : Metric.closedBall z₀ (r / 2) ⊆ (D : Set (ComplexModel (q + p))) :=
    fun z hz => (hcl hz).1
  choose Rq hRq using fun k : Fin q => (isCompact_closedBall z₀ (r / 2)).exists_bound_of_continuousOn
    (SGPT.NPP.BedfordTaylorTopDegree.contDiff_quadPot (β k)).continuous.continuousOn
  choose Rρ hRρ using fun j : Fin p => (isCompact_closedBall z₀ (r / 2)).exists_bound_of_continuousOn
    ((hρ j).2.2.1.continuousOn.mono hcbV)
  let Bb : ℝ := ∑ k, |Rq k| + ∑ j, |Rρ j| + |B| + |B₀|
  have hBb : 0 ≤ Bb := by positivity
  have hRqB (k : Fin q) : |Rq k| ≤ ∑ k, |Rq k| :=
    Finset.single_le_sum (f := fun k => |Rq k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
  have hRρB (j : Fin p) : |Rρ j| ≤ ∑ j, |Rρ j| :=
    Finset.single_le_sum (f := fun j => |Rρ j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hφreal {w : M → EReal} {C : ℝ} (hw : ∀ x ∈ U, ((-C : ℝ) : EReal) ≤ w x ∧ w x ≤ (C : EReal))
      {x : M} (hx : x ∈ U) : |(w x).toReal| ≤ |C| := by
    have h := hw x hx
    have hfin : w x = ((w x).toReal : EReal) :=
      (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top C) h.2)
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h.1)).symm
    rw [hfin] at h
    exact (abs_le.mpr ⟨EReal.coe_le_coe_iff.mp h.1, EReal.coe_le_coe_iff.mp h.2⟩).trans
      (le_abs_self _) |>.trans (le_abs_self _) |> fun h' => by
        have := abs_le.mpr ⟨EReal.coe_le_coe_iff.mp h.1, EReal.coe_le_coe_iff.mp h.2⟩
        exact this.trans (le_abs_self C)
  have hbox (w : Fin p → ComplexModel (q + p) → ℝ) {C : ℝ} (hC : |C| ≤ |B| + |B₀|)
      (hw : ∀ j, ∀ z ∈ V, |w j z| ≤ |Rρ j| + |C|) :
      ∀ i, ∀ z ∈ V, -Bb ≤ Fin.append ℓ w i z ∧ Fin.append ℓ w i z ≤ Bb := by
    intro i z hz
    rw [← abs_le]
    refine Fin.addCases (fun k => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      have h := hRq k z (Metric.ball_subset_closedBall hz)
      rw [Real.norm_eq_abs] at h
      have := hRqB k
      have : 0 ≤ ∑ j, |Rρ j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith [le_abs_self (Rq k), abs_nonneg B, abs_nonneg B₀]
    · rw [Fin.append_right]
      have h := hw j z hz
      have := hRρB j
      have : 0 ≤ ∑ k, |Rq k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
  have hpot (w : M → EReal) {C : ℝ} (hwC : ∀ x ∈ U, ((-C : ℝ) : EReal) ≤ w x ∧ w x ≤ (C : EReal))
      (j : Fin p) : ∀ z ∈ V, |ρ j z + (w (e.val.symm z)).toReal| ≤ |Rρ j| + |C| := by
    intro z hz
    have h1 := hRρ j z (Metric.ball_subset_closedBall hz)
    rw [Real.norm_eq_abs] at h1
    exact (abs_add_le _ _).trans (add_le_add (h1.trans (le_abs_self _))
      (hφreal hwC (hDU z (hVD hz))))
  -- capacity convergence of the potentials on compact subsets of `V`
  have hcapV : ∀ i (V' : Opens (ComplexModel (q + p))), V' ≤ V → ∀ T : Set (ComplexModel (q + p)),
      IsCompact T → T ⊆ V' → ∀ a : ℝ, 0 < a → Tendsto (fun k => relCapacity V'
        {z | z ∈ T ∧ a < |Fin.append ℓ (uu k) i z - Fin.append ℓ u0 i z|}) atTop (𝓝 0) := by
    intro i V' hV'V T hT hTV' a ha
    refine Fin.addCases (fun k => ?_) (fun j => ?_) i
    · have hempty : ∀ k', {z | z ∈ T ∧ a < |Fin.append ℓ (uu k') (Fin.castAdd p k) z -
          Fin.append ℓ u0 (Fin.castAdd p k) z|} = ∅ := by
        intro k'
        ext z
        simp only [Fin.append_left, sub_self, abs_zero, mem_ofPred_eq, mem_empty_iff_false,
          iff_false, not_and, not_lt]
        exact fun _ => ha.le
      simp only [hempty, relCapacity_empty]
      exact tendsto_const_nhds
    · obtain ⟨Crev, hCrev, hrev⟩ :=
        ActualChartCapacityReverse.exists_compact_capacity_reverse ω e
          (fun z hz => hVt (hV'V hz)) (hρω.mono V'.isOpen (fun z hz => hVW (hV'V hz))) hT hTV'
      have hsrc : SourceTendstoInCapacity θc U
          (fun k (x : U) => (((φ k j x.1).toReal : ℝ) : EReal)) atTop
          (fun x => (((φ₀ j x.1).toReal : ℝ) : EReal)) := by
        have he1 : (fun k (x : U) => (((φ k j x.1).toReal : ℝ) : EReal)) =
            fun k (x : U) => φ k j x.1 := by
          funext k x
          have h := hφB k j x.1 x.2
          exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top B) h.2)
            (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h.1)
        have he0 : (fun (x : U) => (((φ₀ j x.1).toReal : ℝ) : EReal)) = fun x => φ₀ j x.1 := by
          funext x
          have h := hφ₀B j x.1 x.2
          exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top B₀) h.2)
            (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h.1)
        rw [he1, he0]
        exact hφcap j
      have hk := kahler_gap_tendsto_of_source_on ω θc hbig U
        (f := fun k x => (φ k j x).toReal) (g := fun x => (φ₀ j x).toReal) hsrc a ha
      have hk' := ENNReal.Tendsto.const_mul hk (Or.inr (ENNReal.ofReal_ne_top (r := Crev)))
      rw [mul_zero] at hk'
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hk' (fun _ => zero_le)
        (fun k => (hrev _ (fun z hz => hz.1)).trans (mul_le_mul_right (thetaCapacity_mono ?_) _))
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨hDU z (hVD (hV'V (hTV' hz.1))), ?_⟩
      have h := hz.2
      simp only [Fin.append_right, uu, u0, add_sub_add_left_eq_sub] at h
      exact h
  exact local_tendsto_integral_moving ω e hVt (hρω.mono V.isOpen hVW) hKc hKV
    (fun k => SGPT.NPP.BedfordTaylorTopDegree.isLocallyBoundedPshOn_append hℓ (huuV k))
    (SGPT.NPP.BedfordTaylorTopDegree.isLocallyBoundedPshOn_append hℓ hu0V) hBb
    (fun k => hbox (uu k) (C := B) (by linarith [abs_nonneg B₀])
      (fun j => hpot (φ k j) (hφB k j) j))
    (hbox u0 (C := B₀) (by linarith [abs_nonneg B]) (fun j => hpot (φ₀ j) (hφ₀B j) j)) hcapV (abs_nonneg A)
    (fun k => hcutabs (fun x hx => hχabs k x hx)) (hcutabs hminabs)
    (fun k => (hχtQC k).1) hχt₀m (fun k => (hχtQC k).2) hχtcap ψ.continuous
    ψ.hasCompactSupport subset_rfl

open LocalBedfordTaylorProducts LocalProductCurrents in
/-- **`thm:loc_conv_cap` for a bounded limit weight**: if the limit `χ` is bounded on `U`, the
limit current is literally `χ ⋀_j θ_{j,φ_j}`. -/
theorem sourceLocConvCap_of_bounded (ω : KahlerBackground n M)
    (θc : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θc)))
    (U : Opens M) {p q : ℕ} (hqp : q + p = n)
    (θ : Fin p → AtlasClosedRealOneOneForm (ofFixedModel n M))
    {φ : ℕ → Fin p → M → EReal} {φ₀ : Fin p → M → EReal}
    (hφ : ∀ i j, (ofFixedModel n M).IsThetaPSHOn (θ j) (φ i j) U)
    (hφ₀ : ∀ j, (ofFixedModel n M).IsThetaPSHOn (θ j) (φ₀ j) U)
    {B B₀ : ℝ} (hφB : ∀ i j, ∀ x ∈ U, ((-B : ℝ) : EReal) ≤ φ i j x ∧ φ i j x ≤ (B : EReal))
    (hφ₀B : ∀ j, ∀ x ∈ U, ((-B₀ : ℝ) : EReal) ≤ φ₀ j x ∧ φ₀ j x ≤ (B₀ : EReal))
    (hφcap : ∀ j, SourceTendstoInCapacity θc U (fun i (x : U) => φ i j x.1) atTop
      (fun x => φ₀ j x.1))
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} {A A₀ : ℝ}
    (hχA : ∀ i, ∀ x ∈ U, 0 ≤ χ i x ∧ χ i x ≤ A) (hχ₀A : ∀ x ∈ U, 0 ≤ χ₀ x ∧ χ₀ x ≤ A₀)
    (hχqc : ∀ i, SourceQuasiContinuousOn θc U (fun x => (χ i x.1 : EReal)))
    (hχcap : SourceTendstoInCapacity θc U (fun i (x : U) => (χ i x.1 : EReal)) atTop
      (fun x => (χ₀ x.1 : EReal)))
    (e : ComplexChart n M) (D : Opens (ComplexModel n))
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target) (hDU : ∀ z ∈ D, e.val.symm z ∈ U)
    (ρ : Fin p → ComplexModel n → ℝ)
    (hρ : ∀ j, IsSmoothLocalPotential (atlasClosedFormToNative (θ j)).val e D (ρ j)) :
    LocalBedfordTaylorContinuity.WeakTendsto
      (fun i => mulBorel (btProduct p q (fun j z => ρ j z + (φ i j (e.val.symm z)).toReal)
          (oneCurrentOf (U := D) hqp))
        ((D : Set (ComplexModel n)).indicator fun z => χ i (e.val.symm z)))
      (mulBorel (btProduct p q (fun j z => ρ j z + (φ₀ j (e.val.symm z)).toReal)
          (oneCurrentOf (U := D) hqp))
        ((D : Set (ComplexModel n)).indicator fun z => χ₀ (e.val.symm z))) := by
  have h := sourceLocConvCap ω θc hbig U hqp θ hφ hφ₀ hφB hφ₀B hφcap (A := max A A₀)
    (fun i x hx => ⟨(hχA i x hx).1, (hχA i x hx).2.trans (le_max_left _ _)⟩)
    (fun x hx => (hχ₀A x hx).1) hχqc hχcap e D hDt hDU ρ hρ
  have heq : ((D : Set (ComplexModel n)).indicator fun z => min (χ₀ (e.val.symm z)) (max A A₀)) =
      (D : Set (ComplexModel n)).indicator fun z => χ₀ (e.val.symm z) := by
    funext z
    by_cases hz : z ∈ D
    · simp only [indicator_of_mem hz]
      exact min_eq_left ((hχ₀A _ (hDU z hz)).2.trans (le_max_right _ _))
    · simp only [indicator_of_notMem hz]
  rwa [heq] at h

end SGPT.NPP.CapacityConvergence
