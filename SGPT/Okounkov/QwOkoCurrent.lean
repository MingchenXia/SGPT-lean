import SGPT.Okounkov.ThetaPotentialCurrentSingularity
import SGPT.Currents.PluriharmonicPotential
import SGPT.GAGA.H0LOkounkov

/-!
# Partial Okounkov bodies depend only on the curvature current

Lane QW-OKO, blueprint `claude-qw-oko.tex`. Source: chapter *The theory of Okounkov bodies*,
subsection *Basic properties of partial Okounkov bodies*, `prop:Okocurrent`: "The partial Okounkov
body `Δ_ν(L, h)` depends only on `dd^c h`, not on the explicit choices of `L, h₀, h`."

The curvature current of a plurisubharmonic metric `h = h₀ e^{-φ}` is
`dd^c h = θ + dd^c φ` (`θ = c₁(L, h₀)`), the global current `thetaPotentialCurrent θ φ`.

## Global potentials of the difference of two presentations

Let `M` be a complex manifold, `θ, σ` smooth real `(1,1)`-forms, `u ∈ PSH(M, θ)`,
`v ∈ PSH(M, σ)` with `θ + dd^c u = σ + dd^c v` as currents.

* `exists_chart_smooth_difference_of_thetaPotentialCurrent_eq`: in every chart, near every
  point, `u = v + d` for a smooth `d` with `dd^c d = σ - θ` (the local potentials `ρ` of `θ` and
  `κ` of `σ` make `u + ρ`, `v + κ` psh with the same `dd^c`; Weyl's lemma gives a pluriharmonic
  `w` with `u + ρ = v + κ + w`; `d = κ + w - ρ`).
* `eq_of_add_eq_add_of_locallyNondegenerate`: two continuous local corrections `u = v + h₁`,
  `u = v + h₂` agree on the overlap (`v > -∞` on a dense set).
* `exists_chartSmooth_of_thetaPotentialCurrent_eq`: hence there is a global smooth `g` with
  `σ = θ + dd^c g` (chartwise) and `u = v + g`, i.e. `v = u - g`.

## `prop:Okocurrent`

* `partialOkounkovBody_eq_of_thetaPotentialCurrent_eq`: in the setting of lanes OKO-A /
  H0-GAGA3 (an integral smooth projective complex scheme `X` of dimension `m + 1` with a smooth
  flag, line bundles `L, L'` with atlases and smooth metrics `H, H'`), if `φ ∈ PSH(X, c₁(L, H))` and
  `φ' ∈ PSH(X, c₁(L', H'))` define the same current `c₁(L, H e^{-φ}) = c₁(L', H' e^{-φ'})` and
  `vol > 0`, then `Δ_ν(L, H e^{-φ}) = Δ_ν(L', H' e^{-φ'})` (for all large cube cones). This
  removes the presentation hypothesis (`θ' = θ + dd^c g`, `φ' = φ - g`) of
  `SGPT.GAGA.H0L.partialOkounkovBody_eq_of_sameCurrent`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.QwOko

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open ActualQuasiPshPotentialSmoothCompatibility ActualOriginalPotentialOverlapSmoothDifference
open NaturalThetaPshGeometricCurrent SourceTraceRepresentativeDefinition
open _root_.SGPT.Foundations.Analysis.LocalCurrents

/-! ### Local corrections agree on overlaps -/

/-- If `v` is finite on a dense set (it is `< ⊤` everywhere and every open set contains a point
where `v > -∞`), two continuous local corrections `u = v + h₁` on `O₁` and `u = v + h₂` on `O₂`
agree on `O₁ ∩ O₂`. -/
theorem eq_of_add_eq_add_of_locallyNondegenerate {M : Type*} [TopologicalSpace M]
    {u v : M → EReal}
    (hv : ∀ x : M, ∀ U : Set M, IsOpen U → x ∈ U → ∃ y ∈ U, v y ≠ ⊥) (hvt : ∀ x, v x ≠ ⊤)
    {O₁ O₂ : Set M} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) {h₁ h₂ : M → ℝ}
    (hc₁ : ContinuousOn h₁ O₁) (hc₂ : ContinuousOn h₂ O₂)
    (he₁ : ∀ x ∈ O₁, u x = v x + (h₁ x : EReal)) (he₂ : ∀ x ∈ O₂, u x = v x + (h₂ x : EReal))
    {x : M} (hx : x ∈ O₁ ∩ O₂) : h₁ x = h₂ x := by
  by_contra hne
  have hc : ContinuousOn (fun y => h₁ y - h₂ y) (O₁ ∩ O₂) :=
    (hc₁.mono inter_subset_left).sub (hc₂.mono inter_subset_right)
  have hV := hc.isOpen_inter_preimage (hO₁.inter hO₂) (isOpen_compl_singleton (x := (0 : ℝ)))
  have hxV : x ∈ (O₁ ∩ O₂) ∩ (fun y => h₁ y - h₂ y) ⁻¹' {(0 : ℝ)}ᶜ :=
    ⟨hx, fun h0 => hne (sub_eq_zero.mp h0)⟩
  obtain ⟨y, ⟨hyO, hy0⟩, hyb⟩ := hv x _ hV hxV
  apply hy0
  have e := (he₁ y hyO.1).symm.trans (he₂ y hyO.2)
  rw [← EReal.coe_toReal (hvt y) hyb, ← EReal.coe_add, ← EReal.coe_add] at e
  have := EReal.coe_injective e
  change h₁ y - h₂ y = 0
  linarith

section Manifold

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-! ### Local smooth differences -/

/-- **Local form**: if `θ + dd^c u = σ + dd^c v` (`u ∈ PSH(M, θ)`, `v ∈ PSH(M, σ)`), then in every
chart `e`, near every point `p` of its source, `u = v + d` for a function `d` smooth near `e p`
with `dd^c d = σ - θ` there. -/
theorem exists_chart_smooth_difference_of_thetaPotentialCurrent_eq
    {θ σ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent σ v hv)
    (e : ComplexChart (m + 1) M) (p : M) (hp : p ∈ e.val.source) :
    ∃ (W : Set (ComplexModel (m + 1))) (d : ComplexModel (m + 1) → ℝ), IsOpen W ∧
      e.val p ∈ W ∧ W ⊆ e.val.target ∧ ContDiffOn ℝ ∞ d W ∧
      (∀ z ∈ W, smoothDDC d z = σ.coeff e z - θ.coeff e z) ∧
      ∀ z ∈ W, u (e.val.symm z) = v (e.val.symm z) + (d z : EReal) := by
  obtain ⟨S, ρ, hpS, hρ, _hP, _hν⟩ := exists_psh_local_theta_reader hu e p hp
  obtain ⟨P, κ, hpP, hκ, _hQ, _hμ⟩ := exists_psh_local_theta_reader hv e p hp
  let U : Opens (ComplexModel (m + 1)) := ⟨S, hρ.1⟩
  let V : Opens (ComplexModel (m + 1)) := ⟨P, hκ.1⟩
  let F : ComplexModel (m + 1) → EReal :=
    fun z => chartFunction u e z + (ρ z : EReal)
  let G : ComplexModel (m + 1) → EReal :=
    fun z => chartFunction v e z + (κ z : EReal)
  obtain ⟨hFp, _hFfin, _hLF, hFc, _hFs, _hFpos⟩ :=
    ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader θ hu e (W := U) ρ hρ
  obtain ⟨hGp, _hGfin, _hLG, hGc, _hGs, _hGpos⟩ :=
    ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader σ hv e (W := V) κ hκ
  have hlocal {ψ : SmoothRealForm (m + 1) M 2} {f : M → EReal}
      (hf : IsThetaPshPotential ψ f) (R : Opens (ComplexModel (m + 1)))
      (hR : R ≤ chartTarget e) (r : ComplexModel (m + 1) → ℝ)
      (hr : PlurisubharmonicOn (fun z => chartFunction f e z + (r z : EReal)) R) :
      LocalQuasiPshPotentialOn (fun z => chartFunction f e z + (r z : EReal)) R := by
    refine ⟨R.isOpen, fun z hz => (hr z hz).quasiPlurisubharmonicAt, ?_⟩
    intro z hz B hB hzB
    obtain ⟨y, hy, hyfin⟩ := hf.2.exists_chart_ne_bot e (R.isOpen.inter hB)
      (fun w hw => hR hw.1) ⟨hz, hzB⟩
    exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hyfin, EReal.coe_ne_bot _⟩⟩
  let hF : LocalQuasiPshPotentialOn F U := hlocal hu U hρ.2.1 ρ hFp
  let hG : LocalQuasiPshPotentialOn G V := hlocal hv V hκ.2.1 κ hGp
  have hreadF : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
      (thetaPotentialCurrent θ u hu).coefficients (canonicalBasis (m + 1)) e w
        (TestFunction.monoCLM ℝ φ) = ddC (regularLocalQuasiPsh hF) w φ := by
    intro w φ
    exact congrArg (fun A => A w φ) hFc
  have hreadG : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(V, ℝ)),
      (thetaPotentialCurrent θ u hu).coefficients (canonicalBasis (m + 1)) e w
        (TestFunction.monoCLM ℝ φ) = ddC (regularLocalQuasiPsh hG) w φ := by
    intro w φ
    rw [heq]
    exact congrArg (fun A => A w φ) hGc
  let H := chartTransition e e
  have hcore : e.val p ∈ (U : Set _) ∩ (H.source ∩ H ⁻¹' V) := by
    refine ⟨hpS, ⟨e.val.map_source hp, ?_⟩, ?_⟩
    · change e.val.symm (e.val p) ∈ e.val.source
      rwa [e.val.left_inv hp]
    · change e.val (e.val.symm (e.val p)) ∈ P
      simpa only [e.val.left_inv hp] using hpP
  obtain ⟨_hFU, _hGH, _hddc, hdiff⟩ := exists_original_chart_smooth_difference
    (thetaPotentialCurrent θ u hu) e e hρ.2.1 hκ.2.1 hF hG hreadF hreadG
  obtain ⟨W, hW, h, hpW, hsm, _hLh, hEq, _hreg, hlevi⟩ := hdiff (e.val p) hcore
  have hWS : (W : Set _) ⊆ S := fun _ hy => (hW hy).1
  have hWP : (W : Set _) ⊆ P := by
    intro z hz
    have hzS : z ∈ e.val.target := hρ.2.1 (hWS hz)
    have hmem : e.val (e.val.symm z) ∈ P := (hW hz).2.2
    simpa only [e.val.right_inv hzS] using hmem
  have hWT : (W : Set _) ⊆ e.val.target := fun _ hz => hρ.2.1 (hWS hz)
  have hhs : ContDiffOn ℝ ∞ h W := hsm.contDiffOn
  have hκW : ContDiffOn ℝ ∞ κ W := hκ.2.2.1.mono hWP
  have hρW : ContDiffOn ℝ ∞ ρ W := hρ.2.2.1.mono hWS
  refine ⟨W, fun z => κ z + h z - ρ z, W.isOpen, hpW, hWT, (hκW.add hhs).sub hρW, ?_, ?_⟩
  · intro z hz
    have h2 : ContDiffAt ℝ 2 h z :=
      (hsm.of_le ENat.LEInfty.out).contDiffAt
    rw [smoothDDC_sub W.isOpen (hκW.add hhs) hρW hz, smoothDDC_add W.isOpen hκW hhs hz,
      SGPT.Currents.smoothDDC_eq_zero_of_leviForm_eq_zero h2 (hlevi z hz), add_zero,
      hκ.2.2.2 (hWP hz), hρ.2.2.2 (hWS hz)]
  · intro z hz
    have hzT : z ∈ e.val.target := hWT hz
    have hxy := hEq hz
    change chartFunction u e z + (ρ z : EReal) =
      (chartFunction v e (e.val (e.val.symm z)) + (κ (e.val (e.val.symm z)) : EReal)) +
        (h z : EReal) at hxy
    simp only [chartFunction, e.val.right_inv hzT] at hxy
    have hext : u (e.val.symm z) + (ρ z : EReal) =
        (v (e.val.symm z) + ((κ z + h z - ρ z : ℝ) : EReal)) + (ρ z : EReal) := by
      calc
        _ = (v (e.val.symm z) + (κ z : EReal)) + (h z : EReal) := hxy
        _ = v (e.val.symm z) + ((κ z + h z : ℝ) : EReal) := by
          rw [EReal.coe_add, add_assoc]
        _ = v (e.val.symm z) + ((κ z + h z - ρ z + ρ z : ℝ) : EReal) := by
          congr 2
          ring
        _ = _ := by
          rw [EReal.coe_add (κ z + h z - ρ z), add_assoc]
    exact le_antisymm
      ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp hext.le)
      ((EReal.addLECancellable_coe _).add_le_add_iff_right.mp hext.ge)

/-- A chart datum `u = v + d` on `W ⊆ e.target` is a manifold datum on `e⁻¹(W)`. -/
theorem chart_datum_toManifold {u v : M → EReal} (e : ComplexChart (m + 1) M)
    {W : Set (ComplexModel (m + 1))} (hWo : IsOpen W) {d : ComplexModel (m + 1) → ℝ}
    (hd : ContDiffOn ℝ ∞ d W)
    (hdeq : ∀ z ∈ W, u (e.val.symm z) = v (e.val.symm z) + (d z : EReal)) :
    IsOpen (e.val.source ∩ e.val ⁻¹' W) ∧
      ContinuousOn (fun x => d (e.val x)) (e.val.source ∩ e.val ⁻¹' W) ∧
      ∀ x ∈ e.val.source ∩ e.val ⁻¹' W, u x = v x + (d (e.val x) : EReal) := by
  refine ⟨e.val.isOpen_inter_preimage hWo, ?_, ?_⟩
  · exact hd.continuousOn.comp (e.val.continuousOn.mono inter_subset_left) fun _ hx => hx.2
  · intro x hx
    have h := hdeq (e.val x) hx.2
    rwa [e.val.left_inv hx.1] at h

/-- **Global form**: if `θ + dd^c u = σ + dd^c v` as currents (`u ∈ PSH(M, θ)`,
`v ∈ PSH(M, σ)`), there is a smooth function `g` with `σ = θ + dd^c g` in every chart and
`u = v + g`. -/
theorem exists_chartSmooth_of_thetaPotentialCurrent_eq
    {θ σ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent σ v hv) :
    ∃ g : M → ℝ, ChartSmooth (n := m + 1) g ∧
      (∀ (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)), z ∈ e.val.target →
        σ.coeff e z = θ.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z) ∧
      ∀ x, u x = v x + (g x : EReal) := by
  have hvq := hv.quasiPshPotential
  have hloc := exists_chart_smooth_difference_of_thetaPotentialCurrent_eq hu hv heq
  choose W d hWo hxW hWt hds hdd hdeq using
    fun x : M => hloc (complexChartAt (n := m + 1) x) x (mem_complexChartAt_source x)
  let g : M → ℝ := fun x => d x ((complexChartAt (n := m + 1) x).val x)
  -- every local chart datum agrees with `g`
  have hagree : ∀ (e : ComplexChart (m + 1) M) (W' : Set (ComplexModel (m + 1)))
      (d' : ComplexModel (m + 1) → ℝ), IsOpen W' → W' ⊆ e.val.target → ContDiffOn ℝ ∞ d' W' →
      (∀ z ∈ W', u (e.val.symm z) = v (e.val.symm z) + (d' z : EReal)) →
      ∀ y ∈ W', g (e.val.symm y) = d' y := by
    intro e W' d' hW'o hW't hd' hd'eq y hy
    set x := e.val.symm y with hxdef
    have hxs : x ∈ e.val.source := e.val.map_target (hW't hy)
    have hex : e.val x = y := e.val.right_inv (hW't hy)
    obtain ⟨hO₁, hc₁, he₁⟩ := chart_datum_toManifold e hW'o hd' hd'eq
    obtain ⟨hO₂, hc₂, he₂⟩ := chart_datum_toManifold (complexChartAt (n := m + 1) x) (hWo x)
      (hds x) (hdeq x)
    have hx₁ : x ∈ e.val.source ∩ e.val ⁻¹' W' := ⟨hxs, by rw [mem_preimage, hex]; exact hy⟩
    have hx₂ : x ∈ (complexChartAt (n := m + 1) x).val.source ∩
        (complexChartAt (n := m + 1) x).val ⁻¹' W x :=
      ⟨mem_complexChartAt_source x, hxW x⟩
    have h := eq_of_add_eq_add_of_locallyNondegenerate hvq.2 hvq.1.ne_top hO₁ hO₂ hc₁ hc₂ he₁ he₂
      ⟨hx₁, hx₂⟩
    rw [hex] at h
    exact h.symm
  refine ⟨g, fun e z hz => ?_, fun e z hz => ?_, fun x => ?_⟩
  · obtain ⟨W', d', hW'o, hzW', hW't, hd', _hdd', hd'eq⟩ := hloc e (e.val.symm z)
      (e.val.map_target hz)
    rw [e.val.right_inv hz] at hzW'
    have hev : (fun y => g (e.val.symm y)) =ᶠ[𝓝 z] d' :=
      Filter.eventually_of_mem (hW'o.mem_nhds hzW')
        fun y hy => hagree e W' d' hW'o hW't hd' hd'eq y hy
    exact ((hd' z hzW').contDiffAt (hW'o.mem_nhds hzW')).congr_of_eventuallyEq hev
      |>.contDiffWithinAt
  · obtain ⟨W', d', hW'o, hzW', hW't, hd', hdd', hd'eq⟩ := hloc e (e.val.symm z)
      (e.val.map_target hz)
    rw [e.val.right_inv hz] at hzW'
    have hev : (fun y => g (e.val.symm y)) =ᶠ[𝓝 z] d' :=
      Filter.eventually_of_mem (hW'o.mem_nhds hzW')
        fun y hy => hagree e W' d' hW'o hW't hd' hd'eq y hy
    rw [smoothDDC_congr hev, hdd' z hzW']
    abel
  · have h := hdeq x ((complexChartAt (n := m + 1) x).val x) (hxW x)
    rwa [(complexChartAt (n := m + 1) x).val.left_inv (mem_complexChartAt_source x)] at h

end Manifold

/-! ### `prop:Okocurrent` -/

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov.AlgPOB SGPT.LineBundle SGPT.PSH SGPT.AlmostSemigroup

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance qwOkoCurTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance qwOkoCurCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance qwOkoCurManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **Source `prop:Okocurrent`** (flag valuations): the partial Okounkov body `Δ_ν(L, h)` depends
only on the curvature current `dd^c h`. Let `(L, H)`, `(L', H')` be line bundles with atlases and
smooth metrics (`θ = c₁(L, H)`, `θ' = c₁(L', H')`) and `h = H e^{-φ}`, `h' = H' e^{-φ'}`
plurisubharmonic metrics (`φ ∈ PSH(X, θ)`, `φ' ∈ PSH(X, θ')`) with the same curvature current
`θ + dd^c φ = θ' + dd^c φ'` and `vol > 0`. Then `vol(θ', φ') > 0` and
`Δ_ν(L, h) = Δ_ν(L', h')` (for all large cube cones). -/
theorem partialOkounkovBody_eq_of_thetaPotentialCurrent_eq [Nonempty (SchemeComplexPoint f)]
    {L L' : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (a' : LineBundleAtlas L') (H' : SchemeLineBundleMetric f (m + 1) E L')
    {φ φ' : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hφ' : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H'.curvature a').val φ')
    (hcur : letI := E.isSeparated; letI := E.quasiCompact;
      thetaPotentialCurrent (H.curvature a).val φ hφ =
        thetaPotentialCurrent (H'.curvature a').val φ' hφ')
    (hpos : 0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H.curvature a) φ)) :
    0 < volume.real (PartialBody.generalPartialBody
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (H'.curvature a') φ') ∧
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a φ =
        partialOkounkovBody f (m + 1) E Y hY (cubeCone C) a' φ' := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨g, hg, hθθ', hug⟩ := exists_chartSmooth_of_thetaPotentialCurrent_eq hφ hφ' hcur
  have hφ'eq : φ' = fun x => φ x - (g x : EReal) := by
    funext x
    rw [hug x, EReal.add_sub_cancel_right]
  subst hφ'eq
  have hK := PartialBody.generalPartialBody_sub_smooth
    (F := schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hg hθθ' hφ
  refine ⟨?_, SGPT.GAGA.H0L.partialOkounkovBody_eq_of_sameCurrent f E Y hY a H a' H' hg hθθ' hφ
    hφ' hpos⟩
  exact lt_of_lt_of_eq hpos (congrArg (fun K => volume.real K) hK).symm

end SGPT.Okounkov.QwOko
