import SGPT.NPP.NonPluripolarCurrent3Currents

/-!
# Products on open submanifolds with their induced atlas

Source: `chapter_npp.tex`, `def:npp:L146` ("there exists an open covering `𝒰` of `X` such that on
each `U ∈ 𝒰`, we can find `φⱼ^U ∈ PSH(U)` such that `dd^c φⱼ^U = Tⱼ` and
`dd^c φ₁^U ∧ ⋯ ∧ dd^c φ_p^U` is well-defined", `eq:ppp5`
`(T₁ ∧ ⋯ ∧ T_p)|_U = dd^c φ₁^U ∧ ⋯ ∧ dd^c φ_p^U`), read with `def:npp:L69` on the complex manifold
`U`.

S29 states the conditions on a member `U` of the cover in the charts of the ambient manifold `M`
(coordinate expressions `chartDomain e U` of `U` in every atlas chart `e` of `M`). Here an open
`U ⊆ M` is regarded as a complex manifold in its own right, with mathlib's induced atlas
(`TopologicalSpace.Opens.instChartedSpace`: the charts of `U` are the restrictions
`(chartAt x).subtypeRestr` of the preferred charts of `M` at the points `x ∈ U`), and every
condition of `def:npp:L146` is shown to be the corresponding source notion **on the manifold
`U`**:

* `exists_eq_subtypeRestr`, `ambientChart` — every chart of `U` is the restriction of an atlas chart
  of `M`; `chartTarget_eq_chartDomain`, `coe_symm_eq_ambient` — its coordinate domain is the
  coordinate expression of `U` and its inverse is the inverse of the ambient chart.
* `manifoldPSH_opens_iff` — **`φ ∈ PSH(U)` for the manifold `U`** (`def:pshmfd` on `U`,
  `SGPT.PSH.ManifoldPSH` for the induced atlas, applied to `φ|_U`) **iff** S29's `IsPSHOn` (the
  project's `sgpt:source-psh-open-subset`).
* `isNonPluripolarWellDefined_opens_iff` — the chart condition of `def:npp:L69` in the charts of
  `U` iff S29's condition `IsNonPluripolarWellDefinedOn` in the charts of `M` (chart independence,
  biholomorphic invariance of the local condition).
* **`isNonPluripolarWellDefinedOnOpens_opens_iff`** — the source condition `eq:welldefinepluri`
  **on the manifold `U`, with the source's quantifiers** (all connected open subsets of `U`, all
  smooth semipositive `(1,1)`-forms on them, all compact subsets; S24's
  `IsNonPluripolarWellDefinedOnOpens` for `X = U`) iff `IsNonPluripolarWellDefinedOn`.
* `isDdcOn_iff_opens` — `dd^c φ = T` on `U` (S29's `IsDdcOn`, in the charts of `M`) iff, in every
  chart of `U`, the restriction of `T` equals the current `dd^c (φ|_U)` of the manifold `U`
  (`SGPT.NPP.ddcCurrent` on `U`).
* **`isCurrentProductWellDefined_iff_opens`** — `def:npp:L146` with every condition on the members
  `U` of the cover stated on the manifold `U`: functions `φⱼ^U : U → [-∞, ∞)`, psh on `U`, with
  `dd^c φⱼ^U = Tⱼ|_U` and `dd^c φ₁^U ∧ ⋯ ∧ dd^c φ_p^U` well defined on `U` in the sense of
  `def:npp:L69` (source quantifiers) on `U`.
* **`currentProduct_restrict_opens`** — `eq:ppp5` on the manifold `U`: in every chart of `U`, the
  restriction of `T₁ ∧ ⋯ ∧ T_p` is the non-pluripolar product (`def:npp:L69`, S24's
  `nonPluripolarProductOfOpens`) of the local potentials on the manifold `U`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.NPP

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullback
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc
open SGPT.NPP.NonPluripolarCurrent

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]

/-! ### The charts of an open submanifold -/

section Charts

variable (U : Opens M)

omit [ChartedSpace (ComplexModel (m + 1)) M] in
/-- The target of the restriction of a chart of `M` to `U` is the coordinate expression of `U`. -/
theorem subtypeRestr_target_eq (f : OpenPartialHomeomorph M (ComplexModel (m + 1)))
    (hU : Nonempty U) : (f.subtypeRestr hU).target = f.target ∩ f.symm ⁻¹' U := by
  simp only [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
    Opens.openPartialHomeomorphSubtypeCoe_target]

/-- **Every atlas chart of the open submanifold `U` is the restriction of the preferred chart of
`M` at some point of `U`** (mathlib's induced atlas). -/
theorem exists_eq_subtypeRestr (e : ComplexChart (m + 1) U) :
    ∃ x : U, e.val = (chartAt (ComplexModel (m + 1)) (x : M)).subtypeRestr ⟨x⟩ := by
  obtain ⟨_, ⟨x, rfl⟩, he⟩ := e.property
  exact ⟨x, mem_singleton_iff.mp he⟩

/-- A point of `U` whose preferred chart restricts to `e`. -/
def ambientPoint (e : ComplexChart (m + 1) U) : U := (exists_eq_subtypeRestr U e).choose

/-- The ambient atlas chart of `M` whose restriction to `U` is the chart `e` of `U`. -/
def ambientChart (e : ComplexChart (m + 1) U) : ComplexChart (m + 1) M :=
  complexChartAt ((ambientPoint U e : U) : M)

theorem ambientChart_spec (e : ComplexChart (m + 1) U) :
    e.val = (ambientChart U e).val.subtypeRestr ⟨ambientPoint U e⟩ :=
  (exists_eq_subtypeRestr U e).choose_spec

/-- The coordinate domain of a chart of `U` is the coordinate expression of `U` in the ambient
chart. -/
theorem chartTarget_eq_chartDomain (e : ComplexChart (m + 1) U) :
    chartTarget e = chartDomain (ambientChart U e) U := by
  ext z
  change z ∈ e.val.target ↔
    z ∈ (ambientChart U e).val.target ∩ (ambientChart U e).val.symm ⁻¹' U
  rw [ambientChart_spec U e, subtypeRestr_target_eq]

theorem target_eq_ambient (e : ComplexChart (m + 1) U) :
    e.val.target = (ambientChart U e).val.target ∩ (ambientChart U e).val.symm ⁻¹' U := by
  rw [ambientChart_spec U e, subtypeRestr_target_eq]

theorem chartTarget_le_ambient (e : ComplexChart (m + 1) U) :
    chartTarget e ≤ chartTarget (ambientChart U e) := by
  rw [chartTarget_eq_chartDomain U e]
  exact chartDomain_le _ U

/-- On its coordinate domain, the inverse of a chart of `U` is the inverse of the ambient chart. -/
theorem coe_symm_eq_ambient (e : ComplexChart (m + 1) U) {z : ComplexModel (m + 1)}
    (hz : z ∈ e.val.target) : ((e.val.symm z : U) : M) = (ambientChart U e).val.symm z := by
  have h := ambientChart_spec U e
  rw [h] at hz
  have := OpenPartialHomeomorph.subtypeRestr_symm_apply (ambientChart U e).val ⟨ambientPoint U e⟩ hz
  rw [← this, ← h]
  rfl

theorem mem_ambientChart_source (e : ComplexChart (m + 1) U) {x : U} (hx : x ∈ e.val.source) :
    (x : M) ∈ (ambientChart U e).val.source := by
  rw [ambientChart_spec U e, OpenPartialHomeomorph.subtypeRestr_source] at hx
  exact hx

theorem apply_eq_ambient (e : ComplexChart (m + 1) U) (x : U) :
    e.val x = (ambientChart U e).val x := by
  rw [ambientChart_spec U e, OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- The preferred chart of `U` at `x` is the restriction of the preferred chart of `M`. -/
theorem complexChartAt_opens_val (x : U) :
    (complexChartAt (n := m + 1) x).val =
      (complexChartAt (n := m + 1) (x : M)).val.subtypeRestr ⟨x⟩ := rfl

end Charts

/-! ### Psh functions on an open submanifold -/

section Psh

variable [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M] (U : Opens M)

theorem pshOn_congr' {d : ℕ} {u v : ComplexModel d → EReal} {V : Set (ComplexModel d)}
    (hu : SGPT.PSH.PSHOn u V) (h : EqOn u v V) : SGPT.PSH.PSHOn v V := by
  obtain ⟨z, hz, hne⟩ := hu.nontrivial
  exact ⟨hu.disc.congr h, z, hz, by rwa [← h hz]⟩

/-- **`φ ∈ PSH(U)` on the manifold `U`** (`def:pshmfd` for the induced atlas of `U`, applied to
the restriction `φ|_U`) **iff `φ` is psh on the open set `U`** in the project's sense
(`SGPT.PSH.VariableComplexAtlas.IsPSHOn`, used by S29 for `def:npp:L146`). -/
theorem manifoldPSH_opens_iff {u : M → EReal} :
    SGPT.PSH.ManifoldPSH (n := m + 1) (fun x : U => u x) ↔
      (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn u U := by
  constructor
  · intro hu x hx
    obtain ⟨e, hxe, V, hV, hc, hVe, hxV, huV⟩ := hu ⟨x, hx⟩
    refine ⟨ambientChart U e, mem_ambientChart_source U e hxe, V, hV, hc, fun z hz => ?_, ?_, ?_⟩
    · have := hVe hz
      rw [target_eq_ambient U e] at this
      exact this
    · change (ambientChart U e).val x ∈ V
      rw [← apply_eq_ambient U e ⟨x, hx⟩]
      exact hxV
    · refine pshOn_congr' huV fun z hz => ?_
      change u ((e.val.symm z : U) : M) = u ((ambientChart U e).val.symm z)
      rw [coe_symm_eq_ambient U e (hVe hz)]
  · intro hu x
    set f := complexChartAt (n := m + 1) (x : M)
    set e := complexChartAt (n := m + 1) x
    have hfx : f.val x ∈ chartDomain f U :=
      ⟨f.val.map_source (mem_complexChartAt_source _), by
        simp only [mem_preimage, f.val.left_inv (mem_complexChartAt_source (x : M))]
        exact x.2⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (chartDomain f U).isOpen _ hfx
    have hetarget : (chartTarget e : Set (ComplexModel (m + 1))) = chartDomain f U := by
      change (e.val.target : Set _) = f.val.target ∩ f.val.symm ⁻¹' U
      rw [complexChartAt_opens_val U x, subtypeRestr_target_eq]
    refine ⟨e, mem_complexChartAt_source x, Metric.ball (f.val x) r, Metric.isOpen_ball,
      Metric.isConnected_ball hr, fun z hz => ?_, ?_, ?_⟩
    · change z ∈ (chartTarget e : Set _)
      rw [hetarget]
      exact hball hz
    · change e.val x ∈ _
      rw [complexChartAt_opens_val U x, OpenPartialHomeomorph.subtypeRestr_coe]
      exact Metric.mem_ball_self hr
    · have h := SGPT.PSH.VariableComplexAtlas.IsPSHOn.coordinate_pshOn_of_connected hu U.isOpen f
        Metric.isOpen_ball (Metric.isConnected_ball hr) hball
      refine pshOn_congr' h fun z hz => ?_
      have hzt : z ∈ e.val.target := by
        change z ∈ (chartTarget e : Set _)
        rw [hetarget]
        exact hball hz
      change u (f.val.symm z) = u ((e.val.symm z : U) : M)
      rw [complexChartAt_opens_val U x] at hzt ⊢
      rw [← OpenPartialHomeomorph.subtypeRestr_symm_apply f.val ⟨x⟩ hzt]
      rfl

end Psh

/-! ### Well-definedness on an open submanifold -/

section WellDefined

variable [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M] (U : Opens M) {p q : ℕ}
  (hqp : q + p = m + 1)

omit [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M] in
/-- The local condition in a chart of `U` is the local condition on the coordinate expression of
`U` in the ambient chart. -/
theorem isWellDefinedOn_chartTarget_opens_iff (φ : Fin p → M → EReal)
    (e : ComplexChart (m + 1) U) :
    IsWellDefinedOn hqp (chartTarget e) (fun i z => φ i ((e.val.symm z : U) : M)) ↔
      IsWellDefinedOn hqp (chartDomain (ambientChart U e) U)
        fun i z => φ i ((ambientChart U e).val.symm z) := by
  have h := (nonPluripolarProduct_congr hqp (U := chartTarget e)
    (φ := fun i z => φ i ((e.val.symm z : U) : M))
    (φ' := fun i z => φ i ((ambientChart U e).val.symm z))
    fun i z hz => by rw [coe_symm_eq_ambient U e hz]).1
  rw [h, chartTarget_eq_chartDomain U e]

/-- **Biholomorphic transport of the local condition**: if the local condition holds on the
coordinate expression of `U` in the chart `g`, it holds on the part of the coordinate expression
of `U` in the chart `f` lying over `g.source`. -/
theorem isWellDefinedOn_preOpen_overlapDomain {φ : Fin p → M → EReal}
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) U)
    (f g : ComplexChart (m + 1) M)
    (hW : IsWellDefinedOn hqp (chartDomain g U) fun i z => φ i (g.val.symm z)) :
    IsWellDefinedOn hqp
      (preOpen (chartTransition_isBiholomorphicPair f g) (overlapDomain f g U))
      fun i z => φ i (f.val.symm z) := by
  have hh := chartTransition_isBiholomorphicPair f g
  have hV'B : overlapDomain f g U ≤ overlapTarget f g := overlapDomain_le f g U
  have hh' := isBiholomorphicPair_preOpen hh hV'B
  have hpshg : ∀ i, SGPT.Foundations.Analysis.PlurisubharmonicOn
      (fun y => φ i (g.val.symm y)) (chartDomain g U) := fun i =>
    (isL1PshOn_chartDomain (hφ i) g).psh
  have hV'g : overlapDomain f g U ≤ chartDomain g U := inf_le_right
  have hpsh : ∀ i, SGPT.Foundations.Analysis.PlurisubharmonicOn
      (fun y => φ i (g.val.symm y)) (overlapDomain f g U) := fun i => (hpshg i).mono hV'g
  have hWV' := isWellDefinedOn_restrict hqp hpshg hW hV'g
  have hpb := (pullback_nonPluripolarProduct hqp hh' hpsh hWV').1
  refine (nonPluripolarProduct_congr hqp (U := preOpen hh (overlapDomain f g U))
    (φ := fun i x => φ i (g.val.symm (chartTransition f g x)))
    (φ' := fun i z => φ i (f.val.symm z)) fun i x hx => ?_).1.mp hpb
  exact (chart_comp_transition (φ i) f g x ((mem_preOpen hh).mp hx).1).symm

/-- **The chart condition of `def:npp:L69` on the manifold `U`** (in the charts of `U`'s induced
atlas, for the restrictions `φᵢ|_U`) **is S29's condition `IsNonPluripolarWellDefinedOn`** (in
the charts of `M`, on the coordinate expressions of `U`). -/
theorem isNonPluripolarWellDefined_opens_iff {φ : Fin p → M → EReal}
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) U) :
    IsNonPluripolarWellDefined (M := U) hqp (fun i (x : U) => φ i x) ↔
      IsNonPluripolarWellDefinedOn hqp φ U := by
  constructor
  · intro h f
    have hcov : ∀ z : chartDomain f U, ∃ g : ComplexChart (m + 1) M,
        (f.val.symm z : M) ∈ g.val.source ∧
          IsWellDefinedOn hqp (chartDomain g U) fun i z => φ i (g.val.symm z) := by
      intro z
      set x : U := ⟨f.val.symm z, (mem_chartDomain.mp z.2).2⟩
      set e := complexChartAt (n := m + 1) x
      exact ⟨ambientChart U e, mem_ambientChart_source U e (mem_complexChartAt_source x),
        (isWellDefinedOn_chartTarget_opens_iff U hqp φ e).mp (h e)⟩
    choose g hg hWg using hcov
    refine isWellDefinedOn_of_cover hqp (fun i => (isL1PshOn_chartDomain (hφ i) f).psh)
      (fun z : chartDomain f U =>
        preOpen (chartTransition_isBiholomorphicPair f (g z)) (overlapDomain f (g z) U))
      (fun z w hw => (mem_preOpen_overlapDomain.mp hw).1) (fun z hz => ?_)
      fun z => isWellDefinedOn_preOpen_overlapDomain U hqp hφ f (g z) (hWg z)
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_preOpen_overlapDomain.mpr ⟨hz, hg ⟨z, hz⟩⟩⟩
  · intro h e
    exact (isWellDefinedOn_chartTarget_opens_iff U hqp φ e).mpr (h _)

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- **`def:npp:L69` on the open submanifold `U`, with the source's quantifiers**: the source
condition `eq:welldefinepluri` on the complex manifold `U` (for every connected open `V ⊆ U`, every
smooth semipositive `(1,1)`-form on `V` and every compact `K ⊆ V`; S24's
`IsNonPluripolarWellDefinedOnOpens` for `X = U` with its induced atlas, Borel structure and
Hausdorff topology) holds for the restrictions `φᵢ|_U` iff S29's chart condition
`IsNonPluripolarWellDefinedOn hqp φ U` holds. -/
theorem isNonPluripolarWellDefinedOnOpens_opens_iff {φ : Fin p → M → EReal}
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) U) :
    IsNonPluripolarWellDefinedOnOpens (M := U) hqp (fun i (x : U) => φ i x)
        (fun i => (manifoldPSH_opens_iff U).mpr (hφ i)) ↔
      IsNonPluripolarWellDefinedOn hqp φ U :=
  (isNonPluripolarWellDefinedOnOpens_iff hqp _).trans
    (isNonPluripolarWellDefined_opens_iff U hqp hφ)

end WellDefined

/-! ### `dd^c φ = T` on an open submanifold -/

section Ddc

variable [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M] (U : Opens M)

/-- Restriction along an equality of open sets. -/
theorem restrict_ddcL1_of_eq {W A : Opens (ComplexModel (m + 1))} (hWA : W ≤ A)
    {S : LocalProductCurrent (m + 1) A m} {W' : Opens (ComplexModel (m + 1))} (hW : W = W')
    (hW'A : W' ≤ A) {u : ComplexModel (m + 1) → EReal}
    (h : restrict hW'A S = ddcL1 W' u) : restrict hWA S = ddcL1 W u := by
  subst hW
  exact h

/-- **`dd^c φ = T` on `U`, read on the manifold `U`**: S29's `IsDdcOn T φ U` (in every chart of
`M`, `T|_{chartDomain e U} = dd^c (φ ∘ e⁻¹)`) holds iff, in every chart `e` of the open
submanifold `U`, the restriction of `T` to the coordinate domain of `e` is the chart expression of
the current `dd^c (φ|_U)` of the manifold `U` (`SGPT.NPP.ddcCurrent` on `U`). -/
theorem isDdcOn_iff_opens {T : PositiveCurrent (m + 1) M m} {φ : M → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn φ U) :
    IsDdcOn T φ U ↔ ∀ e : ComplexChart (m + 1) U,
      restrict (chartTarget_le_ambient U e) (T.inChart (ambientChart U e)) =
        (ddcCurrent m (fun x : U => φ x) ((manifoldPSH_opens_iff U).mpr hφ)).inChart e := by
  have hφU := (manifoldPSH_opens_iff U).mpr hφ
  constructor
  · intro h e
    rw [ddcCurrent_inChart]
    set g := ambientChart U e
    have hcongr : ddcL1 (chartTarget e) (fun z => φ ((e.val.symm z : U) : M)) =
        ddcL1 (chartTarget e) (fun z => φ (g.val.symm z)) :=
      ddcL1_congr (isL1PshOn_chart hφU e).locallyIntegrableOn
        (by rw [chartTarget_eq_chartDomain U e]
            exact (isL1PshOn_chartDomain hφ g).locallyIntegrableOn)
        fun z hz => by rw [coe_symm_eq_ambient U e hz]
    rw [hcongr]
    exact restrict_ddcL1_of_eq _ (chartTarget_eq_chartDomain U e) (chartDomain_le g U) (h g)
  · intro h f
    apply LocalBedfordTaylorCalculus.eq_of_local
    intro z hz
    set x : U := ⟨f.val.symm z, hz.2⟩
    set e := complexChartAt (n := m + 1) x
    set g := ambientChart U e
    have hh := chartTransition_isBiholomorphicPair f g
    have hV'B : overlapDomain f g U ≤ overlapTarget f g := overlapDomain_le f g U
    have hh' := isBiholomorphicPair_preOpen hh hV'B
    have hP : preOpen hh (overlapDomain f g U) ≤ chartDomain f U :=
      fun w hw => (mem_preOpen_overlapDomain.mp hw).1
    have hzP : z ∈ preOpen hh (overlapDomain f g U) :=
      mem_preOpen_overlapDomain.mpr ⟨hz, mem_ambientChart_source U e (mem_complexChartAt_source x)⟩
    refine ⟨preOpen hh (overlapDomain f g U), hP, hzP, ?_⟩
    -- the restriction of `T` to `chartDomain g U`
    have hTg : restrict (chartDomain_le g U) (T.inChart g) =
        ddcL1 (chartDomain g U) fun y => φ (g.val.symm y) := by
      have he := h e
      rw [ddcCurrent_inChart] at he
      have hcongr : ddcL1 (chartTarget e) (fun z => φ ((e.val.symm z : U) : M)) =
          ddcL1 (chartTarget e) (fun z => φ (g.val.symm z)) :=
        ddcL1_congr (isL1PshOn_chart hφU e).locallyIntegrableOn
          (by rw [chartTarget_eq_chartDomain U e]
              exact (isL1PshOn_chartDomain hφ g).locallyIntegrableOn)
          fun z hz => by rw [coe_symm_eq_ambient U e hz]
      rw [hcongr] at he
      exact restrict_ddcL1_of_eq _ (chartTarget_eq_chartDomain U e).symm
        (chartTarget_le_ambient U e) he
    have hgL := isL1PshOn_chartDomain hφ g
    have hV'g : overlapDomain f g U ≤ chartDomain g U := inf_le_right
    have hV'L : IsL1PshOn (overlapDomain f g U) fun y => φ (g.val.symm y) := hgL.mono hV'g
    -- the left-hand side
    have hfT := T.compatible f g
    have hL : restrict hP (restrict (chartDomain_le f U) (T.inChart f)) =
        ddcL1 (preOpen hh (overlapDomain f g U)) fun y => φ (f.val.symm y) := by
      rw [restrict_restrict]
      have hPA : preOpen hh (overlapDomain f g U) ≤ overlapSource f g := preOpen_le hh _
      rw [← restrict_restrict hPA (overlapSource_le f g), hfT,
        ← pullback_restrict hh _ hV'B]
      have e1 : restrict hV'B (restrict (overlapTarget_le f g) (T.inChart g)) =
          ddcL1 (overlapDomain f g U) fun y => φ (g.val.symm y) := by
        rw [restrict_restrict, ← restrict_restrict hV'g (chartDomain_le g U), hTg,
          restrict_ddcL1 hV'g hgL.locallyIntegrableOn]
      rw [SGPT.NPP.NonPluripolarCurrent.pullback_congr_current hh' _ hV'L.isPositive_ddcL1 e1,
        pullback_ddcL1 hh' hV'L]
      exact ddcL1_congr (hV'L.comp hh').locallyIntegrableOn
        ((isL1PshOn_chartDomain hφ f).mono hP).locallyIntegrableOn
        fun y hy => (chart_comp_transition φ f g y hy.1).symm
    rw [hL, restrict_ddcL1 hP (isL1PshOn_chartDomain hφ f).locallyIntegrableOn]

end Ddc

/-! ### `def:npp:L146` on the open submanifolds of the cover -/

section CurrentProduct

variable [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M] {p q : ℕ} (hqp : q + p = m + 1)

open Classical in
/-- An ambient representative of a function on the open set `U` (extended by `0`). -/
def extendOpens (U : Opens M) (φ : U → EReal) : M → EReal :=
  fun x => if h : x ∈ U then φ ⟨x, h⟩ else 0

theorem extendOpens_val (U : Opens M) (φ : U → EReal) (x : U) :
    extendOpens U φ x = φ x := by
  classical
  rw [extendOpens, dif_pos x.2]

theorem extendOpens_comp_val (U : Opens M) (φ : U → EReal) :
    (fun x : U => extendOpens U φ x) = φ :=
  funext (extendOpens_val U φ)

/-- `IsLocalPotential T U φ` read on the manifold `U`. -/
theorem isLocalPotential_iff_opens {T : Fin p → PositiveCurrent (m + 1) M m} {U : Opens M}
    {φ : Fin p → M → EReal} :
    IsLocalPotential T U φ ↔
      ∃ hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (fun x : U => φ i x),
        ∀ i (e : ComplexChart (m + 1) U),
          restrict (chartTarget_le_ambient U e) ((T i).inChart (ambientChart U e)) =
            (ddcCurrent m (fun x : U => φ i x) (hφ i)).inChart e := by
  constructor
  · intro h
    exact ⟨fun i => (manifoldPSH_opens_iff U).mpr (h.psh i), fun i =>
      (isDdcOn_iff_opens U (h.psh i)).mp (h.ddc i)⟩
  · rintro ⟨hφ, hddc⟩
    have hpsh := fun i => (manifoldPSH_opens_iff U).mp (hφ i)
    exact ⟨hpsh, fun i => (isDdcOn_iff_opens U (hpsh i)).mpr (hddc i)⟩

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- **`def:npp:L146` with every condition stated on the open submanifolds of the cover**:
`T₁ ∧ ⋯ ∧ T_p` is well defined (S29's `IsCurrentProductWellDefined`) iff there is an open
covering `𝒰` of `M` such that on each `U ∈ 𝒰` there are functions `φⱼ^U : U → [-∞,∞)` with
`φⱼ^U ∈ PSH(U)` (`def:pshmfd` on the complex manifold `U` with its induced atlas),
`dd^c φⱼ^U = Tⱼ` on `U` (in every chart of `U`, the restriction of `Tⱼ` is the chart expression of
the current `dd^c φⱼ^U` of the manifold `U`) and `dd^c φ₁^U ∧ ⋯ ∧ dd^c φ_p^U` well defined on `U`
in the sense of `def:npp:L69` on the manifold `U`, with the source's quantifiers
(`IsNonPluripolarWellDefinedOnOpens` for `X = U`). -/
theorem isCurrentProductWellDefined_iff_opens (T : Fin p → PositiveCurrent (m + 1) M m) :
    IsCurrentProductWellDefined hqp T ↔
      ∃ 𝒰 : Set (Opens M), (∀ x : M, ∃ U ∈ 𝒰, x ∈ U) ∧
        ∀ U ∈ 𝒰, ∃ φ : Fin p → U → EReal,
          ∃ hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i),
            (∀ i (e : ComplexChart (m + 1) U),
              restrict (chartTarget_le_ambient U e) ((T i).inChart (ambientChart U e)) =
                (ddcCurrent m (φ i) (hφ i)).inChart e) ∧
            IsNonPluripolarWellDefinedOnOpens (M := U) hqp φ hφ := by
  constructor
  · rintro ⟨𝒰, h𝒰, hU⟩
    refine ⟨𝒰, h𝒰, fun U hU𝒰 => ?_⟩
    obtain ⟨φ, hpot, hW⟩ := hU U hU𝒰
    obtain ⟨hφ, hddc⟩ := (isLocalPotential_iff_opens (U := U)).mp hpot
    exact ⟨fun i x => φ i x, hφ, hddc,
      (isNonPluripolarWellDefinedOnOpens_opens_iff U hqp hpot.psh).mpr hW⟩
  · rintro ⟨𝒰, h𝒰, hU⟩
    refine ⟨𝒰, h𝒰, fun U hU𝒰 => ?_⟩
    obtain ⟨φ, hφ, hddc, hW⟩ := hU U hU𝒰
    set ψ : Fin p → M → EReal := fun i => extendOpens U (φ i)
    have hψφ : (fun i (x : U) => ψ i x) = φ :=
      funext fun i => extendOpens_comp_val U (φ i)
    have key : ∀ (φ' : Fin p → U → EReal) (hφ' : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ' i)),
        φ' = (fun i (x : U) => ψ i x) →
        (∀ i (e : ComplexChart (m + 1) U),
          restrict (chartTarget_le_ambient U e) ((T i).inChart (ambientChart U e)) =
            (ddcCurrent m (φ' i) (hφ' i)).inChart e) →
        IsNonPluripolarWellDefinedOnOpens (M := U) hqp φ' hφ' →
        IsLocalPotential T U ψ ∧ IsNonPluripolarWellDefinedOn hqp ψ U := by
      rintro φ' hφ' rfl hddc' hW'
      have hpot := (isLocalPotential_iff_opens (U := U)).mpr ⟨hφ', hddc'⟩
      exact ⟨hpot, (isNonPluripolarWellDefinedOnOpens_opens_iff U hqp hpot.psh).mp hW'⟩
    exact ⟨ψ, key φ hφ hψφ.symm hddc hW⟩

/-- **`eq:ppp5` on the open submanifold `U`**: if `T₁ ∧ ⋯ ∧ T_p` is well defined and `φ` are local
potentials of `T` on `U`, then `dd^c φ₁|_U ∧ ⋯ ∧ dd^c φ_p|_U` is well defined on the manifold `U`
in the sense of `def:npp:L69` with the source's quantifiers, and in every chart `e` of `U` the
restriction of `T₁ ∧ ⋯ ∧ T_p` to the coordinate domain of `e` is the chart expression of the
non-pluripolar product (`def:npp:L69` on `U`, S24's `nonPluripolarProductOfOpens`) of the
`φᵢ|_U`. -/
theorem currentProduct_restrict_opens {T : Fin p → PositiveCurrent (m + 1) M m}
    (hT : IsCurrentProductWellDefined hqp T) {U : Opens M} {φ : Fin p → M → EReal}
    (hφ : IsLocalPotential T U φ) :
    ∃ hW : IsNonPluripolarWellDefinedOnOpens (M := U) hqp (fun i (x : U) => φ i x)
        (fun i => (manifoldPSH_opens_iff U).mpr (hφ.psh i)),
      ∀ e : ComplexChart (m + 1) U,
        restrict (chartTarget_le_ambient U e)
            ((currentProduct hqp T hT).inChart (ambientChart U e)) =
          (nonPluripolarProductOfOpens (M := U) hqp _ hW).inChart e := by
  have h := currentProduct_restrict hqp hT hφ
  refine ⟨(isNonPluripolarWellDefinedOnOpens_opens_iff U hqp hφ.psh).mpr h.1, fun e => ?_⟩
  set g := ambientChart U e
  change _ = NonPluripolarCurrent.nonPluripolarProduct hqp (chartTarget e)
    fun i z => φ i ((e.val.symm z : U) : M)
  rw [(nonPluripolarProduct_congr hqp (U := chartTarget e)
    (φ := fun i z => φ i ((e.val.symm z : U) : M)) (φ' := fun i z => φ i (g.val.symm z))
    fun i z hz => by rw [coe_symm_eq_ambient U e hz]).2]
  have key : ∀ (W : Opens (ComplexModel (m + 1))) (hW : W = chartDomain g U)
      (hWg : W ≤ chartTarget g),
      restrict hWg ((currentProduct hqp T hT).inChart g) =
        NonPluripolarCurrent.nonPluripolarProduct hqp W fun i z => φ i (g.val.symm z) := by
    rintro W rfl hWg
    exact h.2 g
  exact key _ (chartTarget_eq_chartDomain U e) _

end CurrentProduct

end SGPT.NPP
