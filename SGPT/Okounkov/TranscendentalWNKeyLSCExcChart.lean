import SGPT.Okounkov.TranscendentalWNKeyLSCMonomial

/-!
# Monomial charts of the deformation near the exceptional divisor (package WN-KEY, lane WN-LSC)

Blueprint `claude-tok-wn-key`, node `tok-wn-key:fibre-limit-exceptional`, and `claude-tok-wn-lsc`,
nodes `tok-wn-lsc:exc-chart`, `tok-wn-lsc:exc-chart-inverse`, `tok-wn-lsc:exc-strict`;
source WN21 §5 (the charts `(w, z', τ)` with `z₁ = wτ`).

At a point `q ∈ ℰ` over `x₀ ∈ Z`, flatten the centre `Z × {0}` by the product flattening
`Ψ = (Φ_Z, τ - τ(0))` (`exists_prod_singleton_flattening`, `Φ_Z` a flattening of `Z` at `x₀`);
by TN `BlowupLocalSurjectivity.exists_monomialLocalInverse`, `q` lies in a monomial chart
`ℓ_j : T_j → 𝒳` (`j ∈ {m, m+1}`, the lift of the `j`-th monomial chart through `μ`) and has a
neighbourhood `O` with a holomorphic `W : O → ℂ^{m+2}` such that `ℓ_j ∘ W = id` and
`σ_j ∘ W = Ψ ∘ μ`.  The structure `ExcChart` bundles these data.

* `ExcChart.W_ℓ`: also `W ∘ ℓ_j = id` (off `ℰ` because `σ_j` is injective there, on `ℰ` by
  continuity, `ℰ ∩ T_j = {w_j = 0}` having empty interior);
* `ExcChart.mem_exceptional_iff`: `z ∈ ℰ ↔ (W z)_j = 0` on `O`;
* `ExcChart.tau_eq`: the coordinate `τ - τ(0)` of `μ z` is the last coordinate of `σ_j(W z)`;
* `ExcChart.W_idxT_eq_zero_of_mem_strict`, `ExcChart.eq_empty_of_idxT`: the strict transform
  `X'` meets `O` only where `(W z)_{m+1} = 0` (chart `j = m`) and not at all (chart `j = m+1`);
* `ExcChart.W_idxT_ne_zero`: at `q ∈ ℰ \ X'` in the chart `j = m`, `(W q)_{m+1} ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Okounkov.TranscendentalWN.LSC

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.BlowupLocalSurjectivity
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- The chart of `X × ℙ¹` at `(x₀, 0)`. -/
abbrev baseChart (x₀ : F.carrier) :
    OpenPartialHomeomorph (F.carrier × ProjectiveLine) (ComplexModel (m + 1 + 1)) :=
  chartAt (ComplexModel (m + 1 + 1)) (x₀, projectiveZero)

/-- The chart of `ℙ¹` at `0`. -/
abbrev zeroChart : OpenPartialHomeomorph ProjectiveLine (ComplexModel 1) :=
  chartAt (ComplexModel 1) projectiveZero

/-- **`tok-wn-lsc:exc-chart`**: the monomial chart data of the deformation at `q ∈ ℰ`. -/
structure ExcChart (μ : 𝒳 → F.carrier × ProjectiveLine) (q : 𝒳) where
  /-- the base point `μ(q) = (x₀, 0)` -/
  x₀ : F.carrier
  /-- the product flattening of the centre at `(x₀, 0)` -/
  Ψ : LocalHolomorphicEquivAt (n := m + 1 + 1) (baseChart F x₀ (x₀, projectiveZero))
  hΨsrc : Ψ.source ⊆ (baseChart F x₀).target
  hΨflat : ∀ {y : F.carrier × ProjectiveLine}, y ∈ (baseChart F x₀).source →
      baseChart F x₀ y ∈ Ψ.source →
        (y ∈ deformationCentre F ↔
          Ψ.toFun (baseChart F x₀ y) ∈ complexCoordinatePlane (m + 1 + 1) m)
  hΨτ : ∀ y ∈ flatDomain Ψ, ((splitL m).symm (Ψ.toFun (baseChart F x₀ y))).2 =
      zeroChart y.2 - zeroChart projectiveZero
  /-- the monomial chart index -/
  j : Fin (m + 1 + 1)
  hj : j = idxZ m ∨ j = idxT m
  /-- the lift of the `j`-th monomial chart through `μ` -/
  ℓ : LiftedOpen.{u} (monomialDomain Ψ m j) → 𝒳
  hℓ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ℓ
  hμℓ : μ ∘ ℓ = monomialChart Ψ m j
  /-- the neighbourhood of `q` and the local inverse of `ℓ` -/
  O : Set 𝒳
  hO : IsOpen O
  hqO : q ∈ O
  W : 𝒳 → ComplexModel (m + 1 + 1)
  hW : ∀ z ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ W z
  hWμ : ∀ z ∈ O, μ z ∈ flatDomain Ψ ∧ monomial m j (W z) = Ψ.toFun (baseChart F x₀ (μ z))
  hℓW : ∀ z ∈ O, ∀ hw : W z ∈ monomialDomain Ψ m j, ℓ (LiftedOpen.mk _ (W z) hw) = z

/-- **`tok-wn-lsc:exc-chart`**: every point of `ℰ` has monomial chart data. -/
theorem nonempty_excChart (hμ : IsNormalConeDeformation F μ) {q : 𝒳}
    (hq : q ∈ exceptionalSet F μ) : Nonempty (ExcChart F μ q) := by
  have hqC : μ q ∈ deformationCentre F := hq
  obtain ⟨hx₀, hq0⟩ := (mem_deformationCentre_iff F).mp hqC
  set x₀ := (μ q).1 with hx₀def
  have hμq : μ q = (x₀, projectiveZero) := Prod.ext rfl hq0
  obtain ⟨hkn, -, Φ, hΦsrc, hΦ0, hflat⟩ := F.firstDivisor.2.2 x₀ hx₀
  obtain ⟨Ψ, hΨsrc, -, hΨflat, hΨfun, -⟩ :=
    exists_prod_singleton_flattening (n' := 1) (A := F.flag (1 : Fin (m + 2)))
      (y := projectiveZero) hkn Φ hΦsrc hΦ0 hflat
  have hz : μ q ∈ flatDomain Ψ := by
    rw [hμq]
    exact ⟨mem_chart_source _ _, Ψ.center_mem_source⟩
  obtain ⟨j, hj, O, hO, hqO, W, hW, hWμ, hℓW, -⟩ :=
    exists_monomialLocalInverse hμ hΨsrc (fun hy hy' => hΨflat hy hy') hz
  obtain ⟨ℓ, ⟨hℓ, hμℓ⟩, -⟩ := existsUnique_monomialLift hμ hΨsrc (fun hy hy' => hΨflat hy hy') hj
  refine ⟨ExcChart.mk x₀ Ψ hΨsrc (fun hy hy' => hΨflat hy hy') ?_ j (le_iff_mem_normal.mp hj) ℓ hℓ
    hμℓ O hO hqO W hW hWμ (fun z hz hw => hℓW ℓ hℓ hμℓ z hz hw)⟩
  intro y _
  rw [hΨfun]
  simp only [baseChart, chartAt_prod, prodChart_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

namespace ExcChart

variable {F} {q : 𝒳} (C : ExcChart F μ q)

theorem hj_le : m ≤ C.j.1 := le_iff_mem_normal.mpr C.hj

/-- The flattened image of a monomial chart point is its monomial. -/
theorem flat_monomialChart (p : LiftedOpen.{u} (monomialDomain C.Ψ m C.j)) :
    C.Ψ.toFun (baseChart F C.x₀ (monomialChart C.Ψ m C.j p)) =
      monomial m C.j (LiftedOpen.toModel _ p) := by
  ext i
  exact flatCoord_monomialChart C.hΨsrc p i

theorem μ_ℓ (p : LiftedOpen.{u} (monomialDomain C.Ψ m C.j)) :
    μ (C.ℓ p) = monomialChart C.Ψ m C.j p := congrFun C.hμℓ p

theorem μ_ℓ_mem_flatDomain (p : LiftedOpen.{u} (monomialDomain C.Ψ m C.j)) :
    μ (C.ℓ p) ∈ flatDomain C.Ψ := by
  rw [C.μ_ℓ]
  exact monomialChart_mem_flatDomain C.hΨsrc p

theorem W_mem_monomialDomain {z : 𝒳} (hz : z ∈ C.O) : C.W z ∈ monomialDomain C.Ψ m C.j := by
  show monomial m C.j (C.W z) ∈ C.Ψ.target
  rw [(C.hWμ z hz).2]
  exact C.Ψ.mapsTo_toFun (C.hWμ z hz).1.2

/-- `ℓ_j ∘ W = id` on `O`, with the total lift. -/
theorem ℓ_W {p₀ : LiftedOpen.{u} (monomialDomain C.Ψ m C.j)} {z : 𝒳} (hz : z ∈ C.O) :
    C.ℓ (liftMk _ p₀ (C.W z)) = z := by
  have hw := C.W_mem_monomialDomain hz
  simp only [liftMk, hw, dite_true]
  exact C.hℓW z hz hw

/-- `σ_j ∘ W ∘ ℓ_j = σ_j`. -/
theorem monomial_W_ℓ {p₀ : LiftedOpen.{u} (monomialDomain C.Ψ m C.j)} {w : ComplexModel (m + 1 + 1)}
    (hw : w ∈ monomialDomain C.Ψ m C.j) (hO : C.ℓ (liftMk _ p₀ w) ∈ C.O) :
    monomial m C.j (C.W (C.ℓ (liftMk _ p₀ w))) = monomial m C.j w := by
  rw [(C.hWμ _ hO).2, C.μ_ℓ, C.flat_monomialChart, toModel_liftMk p₀ hw]

/-- **`tok-wn-lsc:exc-chart-inverse`**: `W ∘ ℓ_j = id` where defined. -/
theorem W_ℓ {p₀ : LiftedOpen.{u} (monomialDomain C.Ψ m C.j)} {w : ComplexModel (m + 1 + 1)}
    (hw : w ∈ monomialDomain C.Ψ m C.j) (hO : C.ℓ (liftMk _ p₀ w) ∈ C.O) :
    C.W (C.ℓ (liftMk _ p₀ w)) = w := by
  set U : Set (ComplexModel (m + 1 + 1)) :=
    (monomialDomain C.Ψ m C.j : Set (ComplexModel (m + 1 + 1))) ∩
      (fun v => C.ℓ (liftMk _ p₀ v)) ⁻¹' C.O with hU
  have hcont : ∀ v ∈ (monomialDomain C.Ψ m C.j : Set (ComplexModel (m + 1 + 1))),
      ContinuousAt (fun v => C.ℓ (liftMk _ p₀ v)) v := fun v hv =>
    ((C.hℓ _).comp v (contMDiffAt_liftMk p₀ hv)).continuousAt
  have hUo : IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr fun v hv => ?_
    exact inter_mem ((monomialDomain C.Ψ m C.j).isOpen.mem_nhds hv.1)
      ((hcont v hv.1).preimage_mem_nhds (C.hO.mem_nhds hv.2))
  have hoff : ∀ v ∈ U, v C.j ≠ 0 → C.W (C.ℓ (liftMk _ p₀ v)) = v := fun v hv hvj =>
    eq_of_monomial_eq (C.monomial_W_ℓ hv.1 hv.2) hvj
  by_cases hwj : w C.j ≠ 0
  · exact hoff w ⟨hw, hO⟩ hwj
  -- on `ℰ`: approach along the `j`-th coordinate direction
  push Not at hwj
  set v : ℂ → ComplexModel (m + 1 + 1) := fun ε => w + ε • EuclideanSpace.single C.j 1 with hv
  have hvc : Continuous v := continuous_const.add (continuous_id.smul continuous_const)
  have hv0 : v 0 = w := by simp [hv]
  have hvt : Tendsto v (𝓝[≠] 0) (𝓝 w) := by
    rw [← hv0]
    exact hvc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), C.W (C.ℓ (liftMk _ p₀ (v ε))) = v ε := by
    have h1 : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), v ε ∈ U := hvt.eventually (hUo.mem_nhds ⟨hw, hO⟩)
    filter_upwards [h1, self_mem_nhdsWithin] with ε hε hε0
    refine hoff _ hε ?_
    simpa [hv, hwj] using hε0
  have hlim1 : Tendsto (fun ε => C.W (C.ℓ (liftMk _ p₀ (v ε)))) (𝓝[≠] (0 : ℂ))
      (𝓝 (C.W (C.ℓ (liftMk _ p₀ w)))) := by
    have hWc : ContinuousAt (fun v => C.W (C.ℓ (liftMk _ p₀ v))) w :=
      ContinuousAt.comp (f := fun v => C.ℓ (liftMk _ p₀ v)) ((C.hW _ hO).continuousAt)
        (hcont w hw)
    exact hWc.tendsto.comp hvt
  exact tendsto_nhds_unique (hlim1.congr' hev) hvt

/-- **`ℰ` in the chart**: `z ∈ ℰ ↔ (W z)_j = 0` on `O`. -/
theorem mem_exceptional_iff {z : 𝒳} (hz : z ∈ C.O) :
    z ∈ exceptionalSet F μ ↔ C.W z C.j = 0 := by
  have hf := (C.hWμ z hz).1
  show μ z ∈ deformationCentre F ↔ _
  rw [C.hΨflat hf.1 hf.2, ← (C.hWμ z hz).2, monomial_mem_plane_iff C.hj_le]

/-- **The fibre coordinate**: `τ(μ z) - τ(0)` is the last coordinate of `σ_j(W z)`. -/
theorem tau_eq {z : 𝒳} (hz : z ∈ C.O) :
    ((splitL m).symm (monomial m C.j (C.W z))).2 =
      zeroChart (μ z).2 - zeroChart projectiveZero := by
  rw [(C.hWμ z hz).2]
  exact C.hΨτ _ (C.hWμ z hz).1

/-! ### The strict transform in the chart -/

/-- Over `X × {0} \ Z × {0}`, the chart `j = m + 1` is not met and in the chart `j = m` the
coordinate `w_{m+1}` vanishes. -/
theorem W_of_mem_centralBase_diff {z : 𝒳} (hz : z ∈ C.O)
    (hz' : μ z ∈ centralBase F \ deformationCentre F) :
    C.W z C.j ≠ 0 ∧ monomial m C.j (C.W z) (idxT m) = 0 := by
  have hf := (C.hWμ z hz).1
  refine ⟨fun h0 => hz'.2 ?_, ?_⟩
  · rw [C.hΨflat hf.1 hf.2, ← (C.hWμ z hz).2, monomial_mem_plane_iff C.hj_le]
    exact h0
  · have h := C.tau_eq hz
    have h0 : (μ z).2 = projectiveZero := (mem_centralBase_iff F).mp hz'.1
    rw [h0, sub_self] at h
    have := congrArg (fun v : ComplexModel 1 => v 0) h
    simpa using this

/-- **`tok-wn-lsc:exc-strict`** (chart `j = m + 1`): `O` does not meet `X'`. -/
theorem inter_strict_eq_empty (hj : C.j = idxT m) :
    C.O ∩ strictCentralFibre F μ = ∅ := by
  have hB : C.O ∩ μ ⁻¹' (centralBase F \ deformationCentre F) = ∅ := by
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨h1, h2⟩ := C.W_of_mem_centralBase_diff hz.1 hz.2
    rw [monomial_apply] at h2
    have : ¬ (m ≤ (idxT m).1 ∧ idxT m ≠ C.j) := by rw [hj]; simp
    rw [if_neg this, ← hj] at h2
    exact h1 h2
  have := C.hO.inter_closure (t := μ ⁻¹' (centralBase F \ deformationCentre F))
  rw [hB, closure_empty] at this
  exact subset_empty_iff.mp this

/-- **`tok-wn-lsc:exc-strict`** (chart `j = m`): on `O ∩ X'`, `w_{m+1} = 0`. -/
theorem W_idxT_eq_zero_of_mem_strict (hj : C.j = idxZ m) {z : 𝒳} (hz : z ∈ C.O)
    (hzX : z ∈ strictCentralFibre F μ) : C.W z (idxT m) = 0 := by
  set B := C.O ∩ μ ⁻¹' (centralBase F \ deformationCentre F) with hB
  have hzB : z ∈ closure B := C.hO.inter_closure ⟨hz, hzX⟩
  have hc : ContinuousAt (fun z => C.W z (idxT m)) z :=
    ((PiLp.continuous_apply 2 _ (idxT m)).continuousAt).comp (C.hW z hz).continuousAt
  have hsub : (fun z => C.W z (idxT m)) '' B ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := C.W_of_mem_centralBase_diff hy.1 hy.2
    have hc : m ≤ (idxT m).1 ∧ idxT m ≠ C.j := ⟨by simp, by rw [hj]; exact idxZ_ne_idxT.symm⟩
    rw [monomial_apply, if_pos hc] at h2
    exact mul_eq_zero.mp h2 |>.resolve_right h1
  have := closure_mono hsub (mem_closure_image hc hzB)
  rwa [closure_singleton] at this

/-- **`tok-wn-lsc:exc-strict`** (chart `j = m`): at `q ∈ ℰ \ X'`, `w_{m+1}(W q) ≠ 0`. -/
theorem W_idxT_ne_zero (hj : C.j = idxZ m) (hqE : q ∈ exceptionalSet F μ)
    (hqX : q ∉ strictCentralFibre F μ) : C.W q (idxT m) ≠ 0 := by
  intro h0
  set w := C.W q with hw
  have hwD := C.W_mem_monomialDomain C.hqO
  have hwZ : w (idxZ m) = 0 := by
    have := (C.mem_exceptional_iff C.hqO).mp hqE
    rwa [hj] at this
  set p₀ : LiftedOpen.{u} (monomialDomain C.Ψ m C.j) := LiftedOpen.mk _ w hwD
  set v : ℂ → ComplexModel (m + 1 + 1) := fun ε => w + ε • EuclideanSpace.single (idxZ m) 1
    with hv
  have hvc : Continuous v := continuous_const.add (continuous_id.smul continuous_const)
  have hv0 : v 0 = w := by simp [hv]
  have hvt : Tendsto v (𝓝[≠] 0) (𝓝 w) := by
    rw [← hv0]
    exact hvc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hℓc : ContinuousAt (fun v => C.ℓ (liftMk _ p₀ v)) w :=
    ((C.hℓ _).comp w (contMDiffAt_liftMk p₀ hwD)).continuousAt
  have hlim : Tendsto (fun ε => C.ℓ (liftMk _ p₀ (v ε))) (𝓝[≠] (0 : ℂ)) (𝓝 q) := by
    have := hℓc.tendsto.comp hvt
    rwa [show C.ℓ (liftMk _ p₀ w) = q from C.ℓ_W C.hqO] at this
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), C.ℓ (liftMk _ p₀ (v ε)) ∈ strictCentralFibre F μ := by
    have h1 : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), v ε ∈ monomialDomain C.Ψ m C.j :=
      hvt.eventually ((monomialDomain C.Ψ m C.j).isOpen.mem_nhds hwD)
    filter_upwards [h1, self_mem_nhdsWithin] with ε hε hε0
    refine subset_closure ?_
    set z := C.ℓ (liftMk _ p₀ (v ε))
    have hzf := C.μ_ℓ_mem_flatDomain (liftMk _ p₀ (v ε))
    have hflat : C.Ψ.toFun (baseChart F C.x₀ (μ z)) = monomial m C.j (v ε) := by
      rw [C.μ_ℓ, C.flat_monomialChart, toModel_liftMk p₀ hε]
    have hvZ : v ε (idxZ m) = ε := by simp [hv, hwZ]
    have hTZ : idxT m ≠ idxZ m := idxZ_ne_idxT.symm
    have hvT : v ε (idxT m) = 0 := by
      simp [hv, h0, hTZ]
    refine ⟨?_, ?_⟩
    · -- `μ z` lies over `0 ∈ ℙ¹`
      have hτ := C.hΨτ _ hzf
      rw [hflat] at hτ
      have h1 : ((splitL m).symm (monomial m C.j (v ε))).2 = 0 := by
        have hc : m ≤ (idxT m).1 ∧ idxT m ≠ C.j := ⟨by simp, by rw [hj]; exact hTZ⟩
        have h2 : monomial m C.j (v ε) (idxT m) = 0 := by
          rw [monomial_apply, if_pos hc, hvT, zero_mul]
        rw [splitL_symm_snd_eq, h2]
        ext i
        simp
      rw [h1, eq_comm, sub_eq_zero] at hτ
      have hsrc : (μ z).2 ∈ zeroChart.source := by
        have := hzf.1
        simp only [chartAt_prod, prodChart_source, mem_prod] at this
        exact this.2
      exact (mem_centralBase_iff F).mpr
        (zeroChart.injOn hsrc (mem_chart_source _ _) hτ)
    · -- `μ z` is off the centre
      rw [C.hΨflat hzf.1 hzf.2, hflat, monomial_mem_plane_iff C.hj_le, hj, hvZ]
      exact hε0
  exact hqX ((isClosed_closure).mem_of_tendsto hlim hev)

end ExcChart

end SGPT.Okounkov.TranscendentalWN.LSC
