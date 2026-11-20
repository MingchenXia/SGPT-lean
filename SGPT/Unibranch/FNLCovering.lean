import SGPT.Unibranch.FNLBasic
import SGPT.Foundations.Analysis.Pending.AnalyticComplementConnected
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens

/-!
# FN80 §5: finite branched coverings, sheet numbers and the trace

Source: `[FN80]` (Fornæss–Narasimhan, Math. Ann. 248 (1980)), Lemma 5.1, used for SGPT
`thm:FN` (`appendix_unibranch.tex`).

Lemma 5.1 of `[FN80]` concerns a pure `k`-dimensional closed subvariety `X` of
`Δⁿ = Δᵏ × Δⁿ⁻ᵏ` such that the projection `π : X → Δᵏ` is a finite `λ`-sheeted branched
covering, and the trace `tr φ(z) = ∑_{p ∈ π⁻¹(z)} φ(p)`, "points on `π⁻¹(z)` being counted
with the right multiplicity".

`IsBranchedCovering X π D λ δ` is the standard notion of a finite analytic (branched)
covering of an open set `D ⊆ ℂᵏ` by `X ⊆ ℂⁿ` along a linear map `π` (Grauert–Remmert):
`π : X → D` is proper with finite fibres, there is a holomorphic function `δ` on `D`
(a discriminant), nowhere locally `≡ 0`, such that over `{δ ≠ 0}` every fibre has exactly
`λ` points and `X` is locally the graph of a holomorphic section of `π`, and
`π⁻¹{δ = 0}` is nowhere dense in `X` (this is where pure dimensionality enters).

The multiplicity of a point `p` of a fibre is its **sheet number** (`IsSheetNumber`,
`sheetNumber`): the number of points of a nearby generic fibre `π⁻¹(z)`, `δ(z) ≠ 0`,
lying in a small ball around `p`; `exists_isSheetNumber` proves that this number is
well defined (eventually constant as the ball shrinks and `z → π p`), using that the
complement of `{δ = 0}` in a ball is connected
(`SGPT.Foundations.Analysis.Pending.AnalyticComplementConnected`).  The trace is
`trace X π δ φ z = ∑ᶠ p ∈ π⁻¹(z), sheetNumber p • φ p`.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {n k : ℕ}

/-- The fibre `X ∩ π⁻¹(z)`. -/
def fibre (X : Set (ComplexModel n)) (π : ComplexModel n →L[ℂ] ComplexModel k)
    (z : ComplexModel k) : Set (ComplexModel n) :=
  X ∩ π ⁻¹' {z}

theorem mem_fibre {X : Set (ComplexModel n)} {π : ComplexModel n →L[ℂ] ComplexModel k}
    {z : ComplexModel k} {x : ComplexModel n} : x ∈ fibre X π z ↔ x ∈ X ∧ π x = z :=
  Iff.rfl

/-- `[FN80]` Lemma 5.1, hypothesis: `π : X → D` is a **finite `λ`-sheeted branched
covering** (analytic covering) with discriminant `δ`. -/
structure IsBranchedCovering (X : Set (ComplexModel n)) (π : ComplexModel n →L[ℂ] ComplexModel k)
    (D : Set (ComplexModel k)) (deg : ℕ) (δ : ComplexModel k → ℂ) : Prop where
  isOpen_base : IsOpen D
  mapsTo : MapsTo π X D
  /-- `π : X → D` is proper. -/
  isCompact_inter_preimage : ∀ K : Set (ComplexModel k), K ⊆ D → IsCompact K →
    IsCompact (X ∩ π ⁻¹' K)
  finite_fibre : ∀ z ∈ D, (fibre X π z).Finite
  differentiableOn_disc : DifferentiableOn ℂ δ D
  /-- The discriminant is nowhere locally identically zero. -/
  frequently_disc_ne : ∀ z ∈ D, ∃ᶠ w in 𝓝 z, δ w ≠ 0
  /-- Generic fibres have exactly `λ` points. -/
  ncard_fibre : ∀ z ∈ D, δ z ≠ 0 → (fibre X π z).ncard = deg
  /-- Over `{δ ≠ 0}`, `X` is locally the graph of a holomorphic section of `π`. -/
  local_graph : ∀ x ∈ X, δ (π x) ≠ 0 → ∃ (U : Set (ComplexModel k)) (V : Set (ComplexModel n))
    (g : ComplexModel k → ComplexModel n), IsOpen U ∧ IsOpen V ∧ π x ∈ U ∧ x ∈ V ∧ U ⊆ D ∧
      DifferentiableOn ℂ g U ∧ (∀ w ∈ U, g w ∈ X ∧ π (g w) = w) ∧
      ∀ y ∈ X ∩ V, π y ∈ U ∧ g (π y) = y
  /-- `π⁻¹{δ = 0}` is nowhere dense in `X` (pure dimensionality). -/
  subset_closure_generic : X ⊆ closure (X ∩ π ⁻¹' {w | δ w ≠ 0})

variable {X : Set (ComplexModel n)} {π : ComplexModel n →L[ℂ] ComplexModel k}
  {D : Set (ComplexModel k)} {deg : ℕ} {δ : ComplexModel k → ℂ}

/-- `m` is the **sheet number** (multiplicity) of `X → ℂᵏ` at `p`: for every small ball
around `p`, a generic fibre near `π p` has exactly `m` points in it. -/
def IsSheetNumber (X : Set (ComplexModel n)) (π : ComplexModel n →L[ℂ] ComplexModel k)
    (δ : ComplexModel k → ℂ) (p : ComplexModel n) (m : ℕ) : Prop :=
  ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] (π p), (fibre X π z ∩ ball p ε).ncard = m

open Classical in
/-- The sheet number of `X → ℂᵏ` at `p` (`0` if it is not defined). -/
def sheetNumber (X : Set (ComplexModel n)) (π : ComplexModel n →L[ℂ] ComplexModel k)
    (δ : ComplexModel k → ℂ) (p : ComplexModel n) : ℕ :=
  if h : ∃ m, IsSheetNumber X π δ p m then Classical.choose h else 0

/-- `[FN80]` Lemma 5.1: the **trace** `tr φ(z) = ∑_{p ∈ π⁻¹(z)} φ(p)`, the points of the
fibre counted with their sheet numbers. -/
def trace (X : Set (ComplexModel n)) (π : ComplexModel n →L[ℂ] ComplexModel k)
    (δ : ComplexModel k → ℂ) (φ : ComplexModel n → EReal) (z : ComplexModel k) : EReal :=
  ∑ᶠ p ∈ fibre X π z, sheetNumber X π δ p • φ p

theorem IsSheetNumber.unique {p : ComplexModel n} {m m' : ℕ}
    (hne : (𝓝[{w | δ w ≠ 0}] (π p)).NeBot) (h : IsSheetNumber X π δ p m)
    (h' : IsSheetNumber X π δ p m') : m = m' := by
  obtain ⟨ε, hε⟩ := (h.and h').exists
  obtain ⟨z, hz⟩ := (hε.1.and hε.2).exists
  exact hz.1.symm.trans hz.2

theorem sheetNumber_eq {p : ComplexModel n} {m : ℕ}
    (hne : (𝓝[{w | δ w ≠ 0}] (π p)).NeBot) (h : IsSheetNumber X π δ p m) :
    sheetNumber X π δ p = m := by
  have hex : ∃ m, IsSheetNumber X π δ p m := ⟨m, h⟩
  rw [sheetNumber, dif_pos hex]
  exact (Classical.choose_spec hex).unique hne h

namespace IsBranchedCovering

variable (hX : IsBranchedCovering X π D deg δ)
include hX

theorem exists_closedBall_subset {z₀ : ComplexModel k} (hz₀ : z₀ ∈ D) :
    ∃ r > 0, closedBall z₀ r ⊆ D := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hX.isOpen_base z₀ hz₀
  exact ⟨r / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hball⟩

theorem neBot_generic {z : ComplexModel k} (hz : z ∈ D) : (𝓝[{w | δ w ≠ 0}] z).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_iff_frequently.mpr (hX.frequently_disc_ne z hz))

theorem continuousAt_disc {z : ComplexModel k} (hz : z ∈ D) : ContinuousAt δ z :=
  (hX.differentiableOn_disc.differentiableAt (hX.isOpen_base.mem_nhds hz)).continuousAt

theorem mem_base {x : ComplexModel n} (hx : x ∈ X) : π x ∈ D := hX.mapsTo hx

/-- Properness: fibres over points near `z₀` lie near the fibre over `z₀`. -/
theorem eventually_fibre_subset {z₀ : ComplexModel k} (hz₀ : z₀ ∈ D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 z₀, fibre X π z ⊆ ⋃ p ∈ fibre X π z₀, ball p ε := by
  obtain ⟨r, hr, hrD⟩ := hX.exists_closedBall_subset hz₀
  set K := X ∩ π ⁻¹' closedBall z₀ r
  have hK : IsCompact K := hX.isCompact_inter_preimage _ hrD (isCompact_closedBall z₀ r)
  set O := ⋃ p ∈ fibre X π z₀, ball p ε
  have hO : IsOpen O := isOpen_biUnion fun p _ => isOpen_ball
  have hK' : IsCompact (K \ O) := hK.diff hO
  have hcl : IsClosed (π '' (K \ O)) := (hK'.image π.continuous).isClosed
  have hz : z₀ ∉ π '' (K \ O) := by
    rintro ⟨x, ⟨⟨hxX, -⟩, hxO⟩, hxz⟩
    exact hxO (mem_biUnion (show x ∈ fibre X π z₀ from ⟨hxX, hxz⟩) (mem_ball_self hε))
  filter_upwards [hcl.isOpen_compl.mem_nhds hz, closedBall_mem_nhds z₀ hr] with z hzK hzr
  intro x hx
  by_contra hxO
  have hπx : π x = z := hx.2
  refine hzK ⟨x, ⟨⟨hx.1, ?_⟩, hxO⟩, hπx⟩
  change π x ∈ closedBall z₀ r
  rw [hπx]
  exact hzr

/-- Over a neighbourhood of a generic point, the fibres are the values of `λ` holomorphic
sections. -/
theorem exists_local_sections {z₁ : ComplexModel k} (hz₁ : z₁ ∈ D) (hδ : δ z₁ ≠ 0) :
    ∃ W : Set (ComplexModel k), IsOpen W ∧ z₁ ∈ W ∧ W ⊆ D ∧ (∀ w ∈ W, δ w ≠ 0) ∧
      ∃ g : ComplexModel n → ComplexModel k → ComplexModel n,
        (∀ x ∈ fibre X π z₁, g x z₁ = x) ∧
        (∀ x ∈ fibre X π z₁, DifferentiableOn ℂ (g x) W) ∧
        ∀ w ∈ W, BijOn (fun x => g x w) (fibre X π z₁) (fibre X π w) := by
  classical
  set S := fibre X π z₁ with hSdef
  have hS : S.Finite := hX.finite_fibre z₁ hz₁
  have hloc : ∀ x : ComplexModel n, ∃ (U : Set (ComplexModel k)) (V : Set (ComplexModel n))
      (g : ComplexModel k → ComplexModel n), x ∈ S → (IsOpen U ∧ IsOpen V ∧ π x ∈ U ∧ x ∈ V ∧
        U ⊆ D ∧ DifferentiableOn ℂ g U ∧ (∀ w ∈ U, g w ∈ X ∧ π (g w) = w) ∧
        ∀ y ∈ X ∩ V, π y ∈ U ∧ g (π y) = y) := by
    intro x
    by_cases hx : x ∈ S
    · have hπx : π x = z₁ := hx.2
      obtain ⟨U, V, g, h⟩ := hX.local_graph x hx.1 (by rw [hπx]; exact hδ)
      exact ⟨U, V, g, fun _ => h⟩
    · exact ⟨∅, ∅, fun _ => 0, fun h => absurd h hx⟩
  choose U V g hg using hloc
  have hπ : ∀ x ∈ S, π x = z₁ := fun x hx => hx.2
  have hgx : ∀ x ∈ S, g x z₁ = x := fun x hx => by
    obtain ⟨-, -, -, hxV, -, -, -, huniq⟩ := hg x hx
    have h := (huniq x ⟨hx.1, hxV⟩).2
    rwa [hπ x hx] at h
  have hzU : ∀ x ∈ S, z₁ ∈ U x := fun x hx => by
    obtain ⟨-, -, hxU, -⟩ := hg x hx
    rwa [hπ x hx] at hxU
  have hcont : ∀ x ∈ S, ContinuousAt (g x) z₁ := fun x hx => by
    obtain ⟨hU, -, -, -, -, hgd, -, -⟩ := hg x hx
    exact (hgd.differentiableAt (hU.mem_nhds (hzU x hx))).continuousAt
  have hevU : ∀ᶠ w in 𝓝 z₁, ∀ x ∈ S, w ∈ U x :=
    (hS.eventually_all).mpr fun x hx => (hg x hx).1.mem_nhds (hzU x hx)
  have hevδ : ∀ᶠ w in 𝓝 z₁, w ∈ D ∧ δ w ≠ 0 :=
    Filter.Eventually.and (hX.isOpen_base.mem_nhds hz₁ : ∀ᶠ w in 𝓝 z₁, w ∈ D)
      ((hX.continuousAt_disc hz₁).eventually_ne hδ)
  have hevinj : ∀ᶠ w in 𝓝 z₁, ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → g x w ≠ g x' w := by
    refine (hS.eventually_all).mpr fun x hx => (hS.eventually_all).mpr fun x' hx' => ?_
    by_cases hxx : x = x'
    · exact Eventually.of_forall fun _ h => absurd hxx h
    · have h := ((hcont x hx).ne_iff_eventually_ne (hcont x' hx')).mp
        (by rw [hgx x hx, hgx x' hx']; exact hxx)
      exact h.mono fun w hw _ => hw
  obtain ⟨W, hWsub, hWo, hz₁W⟩ := _root_.mem_nhds_iff.mp (hevU.and (hevδ.and hevinj))
  refine ⟨W, hWo, hz₁W, fun w hw => (hWsub hw).2.1.1, fun w hw => (hWsub hw).2.1.2, g, hgx,
    fun x hx => (hg x hx).2.2.2.2.2.1.mono fun w hw => (hWsub hw).1 x hx, ?_⟩
  intro w hw
  have hmaps : MapsTo (fun x => g x w) S (fibre X π w) := fun x hx =>
    (hg x hx).2.2.2.2.2.2.1 w ((hWsub hw).1 x hx)
  have hinj : InjOn (fun x => g x w) S := fun x hx x' hx' h => by
    by_contra hne
    exact (hWsub hw).2.2 x hx x' hx' hne h
  refine ⟨hmaps, hinj, ?_⟩
  have hfin : (fibre X π w).Finite := hX.finite_fibre w (hWsub hw).2.1.1
  have himg : (fun x => g x w) '' S = fibre X π w := by
    refine Set.eq_of_subset_of_ncard_le hmaps.image_subset ?_ hfin
    rw [hinj.ncard_image, hX.ncard_fibre w (hWsub hw).2.1.1 (hWsub hw).2.1.2,
      hX.ncard_fibre z₁ hz₁ hδ]
  rw [← himg]
  exact surjOn_image _ _

/-- At a point over a generic base point, the sheet number is `1`. -/
theorem isSheetNumber_one {y : ComplexModel n} (hy : y ∈ X) (hδy : δ (π y) ≠ 0) :
    IsSheetNumber X π δ y 1 := by
  obtain ⟨U, V, g, hU, hV, hyU, hyV, -, hgd, hgX, huniq⟩ := hX.local_graph y hy hδy
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hV y hyV
  have hgy : g (π y) = y := (huniq y ⟨hy, hyV⟩).2
  have hgc : ContinuousAt g (π y) := (hgd.differentiableAt (hU.mem_nhds hyU)).continuousAt
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  apply Eventually.filter_mono nhdsWithin_le_nhds
  have hev : ∀ᶠ z in 𝓝 (π y), g z ∈ ball y ε :=
    hgc.preimage_mem_nhds (by rw [hgy]; exact ball_mem_nhds y hε.1)
  filter_upwards [hev, hU.mem_nhds hyU] with z hz hzU
  have hset : fibre X π z ∩ ball y ε = {g z} := by
    ext x
    constructor
    · rintro ⟨⟨hxX, hxz⟩, hxb⟩
      have hπx : π x = z := hxz
      have h := (huniq x ⟨hxX, hball (ball_subset_ball hε.2.le hxb)⟩).2
      rw [hπx] at h
      exact h.symm
    · rintro rfl
      exact ⟨⟨(hgX z hzU).1, (hgX z hzU).2⟩, hz⟩
  rw [hset, ncard_singleton]

theorem sheetNumber_eq_one {y : ComplexModel n} (hy : y ∈ X) (hδy : δ (π y) ≠ 0) :
    sheetNumber X π δ y = 1 :=
  sheetNumber_eq (hX.neBot_generic (hX.mem_base hy)) (hX.isSheetNumber_one hy hδy)

/-- The complement of `{δ = 0}` in a ball is connected. -/
theorem isPreconnected_ball_inter_generic {z₀ : ComplexModel k} {r : ℝ} (hr : 0 < r)
    (hrD : ball z₀ r ⊆ D) (hne : ∃ w ∈ ball z₀ r, δ w ≠ 0) :
    IsPreconnected (ball z₀ r ∩ {w | δ w ≠ 0}) := by
  let W : Opens (ComplexModel k) := ⟨ball z₀ r, isOpen_ball⟩
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp (isConnected_ball hr)
  let pres : ∀ x : ComplexModel k, x ∈ D →
      ComplexAnalyticPresentationAt (n := k) {w : ComplexModel k | δ w = 0} x :=
    fun x hx =>
    { generatorCount := 1
      generator := fun _ => δ
      coordinateNeighborhood := D
      isOpen_coordinateNeighborhood := hX.isOpen_base
      center_mem_coordinateNeighborhood := by
        simpa [complexChartAt, chartAt_self_eq] using hx
      coordinateNeighborhood_subset_target := by
        simp [complexChartAt, chartAt_self_eq]
      generator_holomorphic := fun _ => hX.differentiableOn_disc
      zeroLocus := by
        intro y _ _
        simp [complexChartAt, chartAt_self_eq] }
  have hT : IsComplexAnalyticSubset (n := k)
      (((↑) : W → ComplexModel k) ⁻¹' {w : ComplexModel k | δ w = 0}) := fun x =>
    ⟨AnalyticSubsetOpens.presentationPreimageVal x (pres x.val (hrD x.property))⟩
  obtain ⟨w, hw, hδw⟩ := hne
  have hTne : (((↑) : W → ComplexModel k) ⁻¹' {w : ComplexModel k | δ w = 0}) ≠ univ := by
    intro h
    have : (⟨w, hw⟩ : W) ∈ (((↑) : W → ComplexModel k) ⁻¹' {w : ComplexModel k | δ w = 0}) := by
      rw [h]; trivial
    exact hδw this
  have hpre := AnalyticComplementConnected.isPreconnected_compl hT hTne
  have himg := hpre.image ((↑) : W → ComplexModel k) continuous_subtype_val.continuousOn
  convert himg using 1
  ext z
  constructor
  · rintro ⟨hz, hδz⟩
    exact ⟨⟨z, hz⟩, hδz, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

/-- **Existence of sheet numbers** at every point of `X`. -/
theorem exists_isSheetNumber {p : ComplexModel n} (hp : p ∈ X) :
    ∃ m, IsSheetNumber X π δ p m := by
  classical
  set z₀ := π p with hz₀def
  have hz₀ : z₀ ∈ D := hX.mem_base hp
  set F₀ := fibre X π z₀ with hF₀def
  have hF₀ : F₀.Finite := hX.finite_fibre z₀ hz₀
  -- a separation radius
  have hsep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p' ∈ F₀, p' ≠ p → 2 * ε < dist p p' := by
    refine (hF₀.eventually_all).mpr fun p' _ => ?_
    by_cases hpp : p' = p
    · exact Eventually.of_forall fun _ h => absurd hpp h
    · have hd : 0 < dist p p' := dist_pos.mpr (Ne.symm hpp)
      filter_upwards [Ioo_mem_nhdsGT (half_pos hd)] with ε hε _
      linarith [hε.2]
  obtain ⟨ε₁, hε₁sep, hε₁pos⟩ := (hsep.and self_mem_nhdsWithin).exists
  have hε₁ : (0 : ℝ) < ε₁ := hε₁pos
  -- a radius on which all fibres lie near `F₀`
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    ((hX.eventually_fibre_subset hz₀ hε₁).and (hX.isOpen_base.mem_nhds hz₀))
  set c : ComplexModel k → ℕ := fun z => (fibre X π z ∩ ball p ε₁).ncard with hcdef
  set S := ball z₀ r ∩ {w | δ w ≠ 0} with hSdef
  -- local constancy of the count on `S`
  have hloc : ∀ z₁ ∈ S, ∀ᶠ w in 𝓝 z₁, c w = c z₁ := by
    intro z₁ hz₁
    have hz₁D : z₁ ∈ D := (hrsub hz₁.1).2
    obtain ⟨W, hWo, hz₁W, -, -, g, hgx, hgd, hbij⟩ :=
      hX.exists_local_sections hz₁D hz₁.2
    set S₁ := fibre X π z₁
    have hS₁ : S₁.Finite := hX.finite_fibre z₁ hz₁D
    have hcont : ∀ x ∈ S₁, ContinuousAt (g x) z₁ := fun x hx =>
      ((hgd x hx).differentiableAt (hWo.mem_nhds hz₁W)).continuousAt
    have hiff : ∀ᶠ w in 𝓝 z₁, ∀ x ∈ S₁, (g x w ∈ ball p ε₁ ↔ x ∈ ball p ε₁) := by
      refine (hS₁.eventually_all).mpr fun x hx => ?_
      by_cases hxb : x ∈ ball p ε₁
      · have h := (hcont x hx).preimage_mem_nhds (by rw [hgx x hx]; exact isOpen_ball.mem_nhds hxb)
        exact Filter.mem_of_superset h fun w hw => iff_of_true hw hxb
      · have hxU := (hrsub hz₁.1).1 hx
        obtain ⟨p', hp'F, hxp'⟩ := mem_iUnion₂.mp hxU
        have hp'p : p' ≠ p := by
          rintro rfl
          exact hxb hxp'
        have h := (hcont x hx).preimage_mem_nhds (by rw [hgx x hx]; exact isOpen_ball.mem_nhds hxp')
        refine Filter.mem_of_superset h fun w hw => iff_of_false ?_ hxb
        intro hwp
        have hd := hε₁sep p' hp'F hp'p
        have h1 : dist p (g x w) < ε₁ := by rw [dist_comm]; exact hwp
        have h2 : dist (g x w) p' < ε₁ := hw
        linarith [dist_triangle p (g x w) p']
    filter_upwards [hiff, hWo.mem_nhds hz₁W] with w hw hwW
    have hset : ∀ v ∈ W, (∀ x ∈ S₁, (g x v ∈ ball p ε₁ ↔ x ∈ ball p ε₁)) →
        fibre X π v ∩ ball p ε₁ = (fun x => g x v) '' (S₁ ∩ ball p ε₁) := by
      intro v hv hvi
      ext y
      constructor
      · rintro ⟨hy, hyb⟩
        obtain ⟨x, hx, rfl⟩ := (hbij v hv).2.2 hy
        exact ⟨x, ⟨hx, (hvi x hx).mp hyb⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hxb⟩, rfl⟩
        exact ⟨(hbij v hv).1 hx, (hvi x hx).mpr hxb⟩
    simp only [hcdef]
    rw [hset w hwW hw, ((hbij w hwW).2.1.mono inter_subset_left).ncard_image]
  have hcont : ContinuousOn c S := fun z hz => by
    have h : (fun _ : ComplexModel k => c z) =ᶠ[𝓝 z] c := (hloc z hz).mono fun w hw => hw.symm
    exact ContinuousAt.continuousWithinAt (tendsto_const_nhds.congr' h)
  have hSne : ∃ w ∈ ball z₀ r, δ w ≠ 0 := by
    obtain ⟨w, hw⟩ := ((hX.frequently_disc_ne z₀ hz₀).and_eventually
      (ball_mem_nhds z₀ hr)).exists
    exact ⟨w, hw.2, hw.1⟩
  have hSconn : IsPreconnected S :=
    hX.isPreconnected_ball_inter_generic hr (fun w hw => (hrsub hw).2) hSne
  obtain ⟨w₀, hw₀, hδw₀⟩ := hSne
  refine ⟨c w₀, ?_⟩
  -- comparison of radii
  filter_upwards [Ioc_mem_nhdsGT hε₁] with ε hε
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ ball z₀ r ∧ fibre X π z ⊆ ⋃ q ∈ F₀, ball q ε :=
    Filter.Eventually.and (ball_mem_nhds z₀ hr : ∀ᶠ z in 𝓝 z₀, z ∈ ball z₀ r)
      (hX.eventually_fibre_subset hz₀ hε.1)
  have hev' : ∀ᶠ z in 𝓝[{w | δ w ≠ 0}] z₀, δ z ≠ 0 := self_mem_nhdsWithin
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, hev'] with z hz hδz
  have hzS : z ∈ S := ⟨hz.1, hδz⟩
  have heq : fibre X π z ∩ ball p ε = fibre X π z ∩ ball p ε₁ := by
    ext y
    constructor
    · rintro ⟨hy, hyb⟩
      exact ⟨hy, ball_subset_ball hε.2 hyb⟩
    · rintro ⟨hy, hyb⟩
      refine ⟨hy, ?_⟩
      obtain ⟨q, hqF, hyq⟩ := mem_iUnion₂.mp (hz.2 hy)
      by_cases hqp : q = p
      · subst hqp
        exact hyq
      · exfalso
        have hd := hε₁sep q hqF hqp
        have h1 : dist p y < ε₁ := by rw [dist_comm]; exact hyb
        have h2 : dist y q < ε := hyq
        linarith [dist_triangle p y q, hε.2]
  rw [heq]
  exact hSconn.constant hcont hzS ⟨hw₀, hδw₀⟩

end IsBranchedCovering

end SGPT.Unibranch.FNL
