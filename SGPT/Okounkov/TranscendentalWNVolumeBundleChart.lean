import SGPT.Okounkov.TranscendentalWNVolumeBundleFactor
import SGPT.Okounkov.TranscendentalWNKeyLSCSlice
import SGPT.Foundations.Analysis.Pending.MixedDensityRankOneSlot

/-!
# Bundle charts of the exceptional divisor (package WN-VF4)

Blueprint `claude-tok-wn-vf4`, node `tok-wn-vf4:bundle-chart`; source WN21 §4 (the chart
`(z̃₁, z', τ)` of the blow-up with `z₁ = z̃₁ τ`, restricted to `τ = 0`).

Fix `y₀ ∈ Z` and the flattening `Φ` of `Z` at `y₀` that defines the chart `e_Z` of `Z` at `y₀`
(`zFlat`).  The product flattening `Ψ = (Φ, τ)` of the centre `Z × {0}` of `μ`
(`exists_prod_singleton_flattening`) and the `τ`-monomial chart `σ_T(w', w_m, s) = (w', w_m s, s)`
lift through the blow-up to `ℓ_T` (TN `existsUnique_monomialLift`); the bundle chart is

  `Λ(ζ, w) = ℓ_T(ζ, w, 0)`,  `ζ ∈ e_Z(dom)`, `w ∈ ℂ`.

This file sets up these data (`BundleSetup`) and proves the basic identities.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
open SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
open SGPT.Foundations.Analysis.Pending.BlowupLocalSurjectivity
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalWN.LSC
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-! ### The chart of `Z` at `y₀` -/

/-- The flattening of `Z` at `y₀` used by the atlas chart of `Z` at `y₀`. -/
abbrev zFlat (y₀ : F.tail.carrier) :
    LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) y₀.1).val y₀.1) :=
  (F.firstDivisor.2.2 y₀.1 y₀.2).2.2.choose

theorem zFlat_spec (y₀ : F.tail.carrier) :
    (zFlat F y₀).source ⊆ (complexChartAt (n := m + 1) y₀.1).val.target ∧
      (zFlat F y₀).toFun ((complexChartAt (n := m + 1) y₀.1).val y₀.1) = 0 ∧
      ∀ {y : F.carrier}, y ∈ (complexChartAt (n := m + 1) y₀.1).val.source →
        (complexChartAt (n := m + 1) y₀.1).val y ∈ (zFlat F y₀).source →
          (y ∈ F.flag (1 : Fin (m + 2)) ↔
            (zFlat F y₀).toFun ((complexChartAt (n := m + 1) y₀.1).val y) ∈
              complexCoordinatePlane (m + 1) m) :=
  (F.firstDivisor.2.2 y₀.1 y₀.2).2.2.choose_spec

theorem chartAt_tail_target (y₀ : F.tail.carrier) :
    (chartAt (ComplexModel m) y₀).target =
      coordinateInclusion (m + 1) m ⁻¹' (zFlat F y₀).target := rfl

theorem chartAt_tail_symm (y₀ : F.tail.carrier) {ζ : ComplexModel m}
    (hζ : ζ ∈ (chartAt (ComplexModel m) y₀).target) :
    firstFlagInclusion F ((chartAt (ComplexModel m) y₀).symm ζ) =
      (chartAt (ComplexModel (m + 1)) y₀.1).symm
        ((zFlat F y₀).invFun (coordinateInclusion (m + 1) m ζ)) :=
  SubmanifoldChartedSpace.FlatData.invPoint_val _ hζ

theorem chartAt_tail_apply (y₀ : F.tail.carrier) (y : F.tail.carrier) :
    chartAt (ComplexModel m) y₀ y =
      coordinateProjection (m + 1) m
        ((zFlat F y₀).toFun (chartAt (ComplexModel (m + 1)) y₀.1 y.1)) := rfl

/-! ### The coordinate vectors -/

section Vec

open SGPT.Foundations.Analysis.Pending.MixedDensityRankOneSlot

theorem stripModelEquiv_symm_zero (ζ : ComplexModel m) :
    (stripModelEquiv m).symm (ζ, 0) = coordinateInclusion (m + 1) m ζ := by
  ext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · rw [stripModelEquiv_symm_apply_last]
    simp [coordinateInclusion]
  · rw [stripModelEquiv_symm_apply_castSucc]
    simp [coordinateInclusion]

theorem scaleLast_stripModelEquiv_symm (ζ : ComplexModel m) (w s : ℂ) :
    scaleLast ((stripModelEquiv m).symm (ζ, w)) s = (stripModelEquiv m).symm (ζ, w * s) := by
  ext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp only [scaleLast, if_true]
    rw [stripModelEquiv_symm_apply_last, stripModelEquiv_symm_apply_last]
  · simp only [scaleLast, Fin.castSucc_ne_last, if_false]
    rw [stripModelEquiv_symm_apply_castSucc, stripModelEquiv_symm_apply_castSucc]

/-- The point `(ζ, w, s)` of the `τ`-monomial chart (`z̃₁ = w`, `τ = s`). -/
def bvec (ζ : ComplexModel m) (w s : ℂ) : ComplexModel (m + 1 + 1) :=
  splitL m ((stripModelEquiv m).symm (ζ, w), EuclideanSpace.single 0 s)

theorem monomial_bvec (ζ : ComplexModel m) (w s : ℂ) :
    monomial m (idxT m) (bvec ζ w s) =
      splitL m ((stripModelEquiv m).symm (ζ, w * s), EuclideanSpace.single 0 s) := by
  rw [bvec, monomial_idxT_split]
  simp [scaleLast_stripModelEquiv_symm]

theorem continuous_bvec (ζ : ComplexModel m) (w : ℂ) : Continuous (bvec ζ w) := by
  unfold bvec
  refine (splitL m).continuous.comp (continuous_const.prodMk ?_)
  have : (EuclideanSpace.single (0 : Fin 1) : ℂ → ComplexModel 1) =
      fun s => s • EuclideanSpace.single (0 : Fin 1) (1 : ℂ) := by
    funext s; ext i; fin_cases i; simp
  rw [this]
  exact continuous_id.smul continuous_const

end Vec

/-! ### The setup at `y₀` -/

section Setup

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}

/-- The product flattening and the `τ`-monomial lift at `y₀ ∈ Z`. -/
structure BundleSetup (μ : 𝒳 → F.carrier × ProjectiveLine) (y₀ : F.tail.carrier) where
  Ψ : LocalHolomorphicEquivAt (n := m + 1 + 1) (baseChart F y₀.1 (y₀.1, projectiveZero))
  hΨsrc : Ψ.source ⊆ (baseChart F y₀.1).target
  hΨflat : ∀ {y : F.carrier × ProjectiveLine}, y ∈ (baseChart F y₀.1).source →
      baseChart F y₀.1 y ∈ Ψ.source →
        (y ∈ deformationCentre F ↔
          Ψ.toFun (baseChart F y₀.1 y) ∈ complexCoordinatePlane (m + 1 + 1) m)
  hΨfun : ∀ w, Ψ.toFun w = splitL m ((zFlat F y₀).toFun ((splitL m).symm w).1,
      ((splitL m).symm w).2 - zeroChart projectiveZero)
  hΨsrc_iff : ∀ w, w ∈ Ψ.source ↔ ((splitL m).symm w).1 ∈ (zFlat F y₀).source ∧
      ((splitL m).symm w).2 ∈ zeroChart.target
  ℓ : LiftedOpen.{u} (monomialDomain Ψ m (idxT m)) → 𝒳
  hℓ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ℓ
  hμℓ : μ ∘ ℓ = monomialChart Ψ m (idxT m)
  huniq : ∀ ℓ' : LiftedOpen.{u} (monomialDomain Ψ m (idxT m)) → 𝒳,
    ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ ℓ' →
      μ ∘ ℓ' = monomialChart Ψ m (idxT m) → ℓ' = ℓ

theorem nonempty_bundleSetup (hμ : IsNormalConeDeformation F μ) (y₀ : F.tail.carrier) :
    Nonempty (BundleSetup F μ y₀) := by
  obtain ⟨hΦsrc, hΦ0, hflat⟩ := zFlat_spec F y₀
  obtain ⟨Ψ, hΨsrc, -, hΨflat, hΨfun, hΨsrc_iff⟩ :=
    exists_prod_singleton_flattening (n' := 1) (A := F.flag (1 : Fin (m + 2)))
      (y := projectiveZero) (F.firstDivisor.2.2 y₀.1 y₀.2).1 (zFlat F y₀) hΦsrc hΦ0 hflat
  obtain ⟨ℓ, ⟨hℓ, hμℓ⟩, huniq⟩ :=
    existsUnique_monomialLift hμ hΨsrc (fun hy hy' => hΨflat hy hy') (j := idxT m) (by simp)
  exact ⟨⟨Ψ, hΨsrc, fun hy hy' => hΨflat hy hy', hΨfun, hΨsrc_iff, ℓ, hℓ, hμℓ,
    fun ℓ' h1 h2 => huniq ℓ' ⟨h1, h2⟩⟩⟩

end Setup

/-! ### The bundle map -/

section Bundle

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}
  {F} {y₀ : F.tail.carrier}

theorem projectiveAffine_projectiveZero : projectiveAffine projectiveZero = 0 := by
  have h := projectiveWeight_zero_projectiveZero
  unfold projectiveWeight at h
  have hD := (normSq_add_pos _ projectiveZero.rep_nonzero).ne'
  rw [div_eq_zero_iff, or_iff_left hD] at h
  have h0 : projectiveZero.rep 0 = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    exact norm_eq_zero.mp this
  simp [projectiveAffine, h0]

theorem zeroChart_apply_zero {p : ProjectiveLine} (hp : p ∈ zeroChart.source) :
    zeroChart p 0 = projectiveAffine p := by
  have h := chartAt_projectiveZero
  simp only [zeroChart] at hp ⊢
  rw [h] at hp ⊢
  exact projectiveModelChart_false_apply hp

theorem rep_one_ne_zero_of_mem_zeroChart {p : ProjectiveLine} (hp : p ∈ zeroChart.source) :
    p.rep 1 ≠ 0 := by
  simp only [zeroChart] at hp
  rw [chartAt_projectiveZero] at hp
  exact mem_projectiveModelChart_false_source.mp hp

namespace BundleSetup

variable (S : BundleSetup F μ y₀)

/-- Reading a point over the flattening domain in the product flattening. -/
theorem decode {q : F.carrier × ProjectiveLine} (hq : q ∈ flatDomain S.Ψ)
    {a : ComplexModel (m + 1)} {b : ComplexModel 1}
    (h : S.Ψ.toFun (baseChart F y₀.1 q) = splitL m (a, b)) :
    q.1 = (chartAt (ComplexModel (m + 1)) y₀.1).symm ((zFlat F y₀).invFun a) ∧
      (zFlat F y₀).toFun (chartAt (ComplexModel (m + 1)) y₀.1 q.1) = a ∧
      zeroChart q.2 = b + zeroChart projectiveZero ∧
      q.1 ∈ (chartAt (ComplexModel (m + 1)) y₀.1).source ∧ q.2 ∈ zeroChart.source := by
  have hbc : baseChart F y₀.1 q =
      splitL m (chartAt (ComplexModel (m + 1)) y₀.1 q.1, zeroChart q.2) := rfl
  have hsrc : q.1 ∈ (chartAt (ComplexModel (m + 1)) y₀.1).source ∧ q.2 ∈ zeroChart.source := by
    have := hq.1
    simp only [chartAt_prod, prodChart_source] at this
    exact this
  have hΦs := ((S.hΨsrc_iff _).mp hq.2).1
  rw [hbc, ContinuousLinearEquiv.symm_apply_apply] at hΦs
  rw [hbc, S.hΨfun, ContinuousLinearEquiv.symm_apply_apply] at h
  have h' := (splitL m).injective h
  simp only [Prod.mk.injEq] at h'
  refine ⟨?_, h'.1, by rw [← h'.2]; abel, hsrc.1, hsrc.2⟩
  rw [← h'.1, (zFlat F y₀).left_inv _ hΦs,
    (chartAt (ComplexModel (m + 1)) y₀.1).left_inv hsrc.1]

/-- `σ_T(ζ, w, s) ∈ Ψ.target` when `(ζ, ws) ∈ Φ.target`. -/
theorem bvec_mem {ζ : ComplexModel m} {w s : ℂ}
    (h1 : (stripModelEquiv m).symm (ζ, w * s) ∈ (zFlat F y₀).target)
    (h2 : EuclideanSpace.single 0 s + zeroChart projectiveZero ∈ zeroChart.target) :
    bvec ζ w s ∈ monomialDomain S.Ψ m (idxT m) := by
  show monomial m (idxT m) (bvec ζ w s) ∈ S.Ψ.target
  set u := splitL m ((zFlat F y₀).invFun ((stripModelEquiv m).symm (ζ, w * s)),
    EuclideanSpace.single 0 s + zeroChart projectiveZero) with hu
  have hus : u ∈ S.Ψ.source := by
    rw [S.hΨsrc_iff, hu, ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨(zFlat F y₀).mapsTo_invFun h1, h2⟩
  have hΨu : S.Ψ.toFun u = monomial m (idxT m) (bvec ζ w s) := by
    rw [S.hΨfun, hu, ContinuousLinearEquiv.symm_apply_apply, monomial_bvec]
    simp only [(zFlat F y₀).right_inv _ h1, add_sub_cancel_right]
  rw [← hΨu]
  exact S.Ψ.mapsTo_toFun hus

theorem single_zero' : (EuclideanSpace.single (0 : Fin 1) (0 : ℂ)) = 0 := by
  ext i; simp

theorem bvec_mem_zero {ζ : ComplexModel m} (hζ : ζ ∈ (chartAt (ComplexModel m) y₀).target)
    (w : ℂ) : bvec ζ w 0 ∈ monomialDomain S.Ψ m (idxT m) := by
  refine S.bvec_mem ?_ ?_
  · rw [mul_zero, stripModelEquiv_symm_zero]; exact hζ
  · rw [single_zero', zero_add]
    exact zeroChart.map_source (mem_chart_source _ _)

/-- A base point of the monomial domain. -/
def p₀ : LiftedOpen.{u} (monomialDomain S.Ψ m (idxT m)) :=
  LiftedOpen.mk _ _ (S.bvec_mem_zero (mem_chart_target (ComplexModel m) y₀) 0)

/-- **The bundle chart** `Λ(ζ, w) = ℓ_T(ζ, w, 0)`. -/
def Λ (ζ : ComplexModel m) (w : ℂ) : 𝒳 := S.ℓ (liftMk _ S.p₀ (bvec ζ w 0))

/-- The image of a monomial chart point in the flattening. -/
theorem flat_μ_ℓ (p : LiftedOpen.{u} (monomialDomain S.Ψ m (idxT m))) :
    μ (S.ℓ p) ∈ flatDomain S.Ψ ∧ S.Ψ.toFun (baseChart F y₀.1 (μ (S.ℓ p))) =
      monomial m (idxT m) (LiftedOpen.toModel _ p) := by
  have hμ : μ (S.ℓ p) = monomialChart S.Ψ m (idxT m) p := congrFun S.hμℓ p
  rw [hμ]
  refine ⟨monomialChart_mem_flatDomain S.hΨsrc p, ?_⟩
  ext i
  exact flatCoord_monomialChart S.hΨsrc p i

theorem μ_Λ {ζ : ComplexModel m} (hζ : ζ ∈ (chartAt (ComplexModel m) y₀).target) (w : ℂ) :
    μ (S.Λ ζ w) = (firstFlagInclusion F ((chartAt (ComplexModel m) y₀).symm ζ), projectiveZero) := by
  have hd := S.bvec_mem_zero hζ w
  obtain ⟨hf, hΨ⟩ := S.flat_μ_ℓ (liftMk _ S.p₀ (bvec ζ w 0))
  rw [toModel_liftMk S.p₀ hd, monomial_bvec, mul_zero, single_zero',
    stripModelEquiv_symm_zero] at hΨ
  obtain ⟨h1, -, h3, -, h5⟩ := S.decode hf hΨ
  refine Prod.ext ?_ ?_
  · change (μ (S.ℓ (liftMk _ S.p₀ (bvec ζ w 0)))).1 = _
    rw [h1, chartAt_tail_symm F y₀ hζ]
  · change (μ (S.ℓ (liftMk _ S.p₀ (bvec ζ w 0)))).2 = _
    rw [zero_add] at h3
    exact zeroChart.injOn h5 (mem_chart_source _ _) h3

theorem Λ_mem {ζ : ComplexModel m} (hζ : ζ ∈ (chartAt (ComplexModel m) y₀).target) (w : ℂ) :
    S.Λ ζ w ∈ exceptionalSet F μ := by
  show μ (S.Λ ζ w) ∈ deformationCentre F
  rw [S.μ_Λ hζ w, mem_deformationCentre_iff]
  exact ⟨((chartAt (ComplexModel m) y₀).symm ζ).2, rfl⟩

end BundleSetup

end Bundle

/-! ### The weights in the bundle chart -/

section Weights

open SGPT.Foundations.Analysis.Pending.MixedDensityRankOneSlot

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}
  {F} {y₀ : F.tail.carrier}

namespace BundleSetup

variable (S : BundleSetup F μ y₀)

/-- **The weights along the bundle chart** (`tok-wn-vf4:bundle-weights`):
`S₁(Λ(ζ, w)) = 1 / (|w|² G + 1)` and `S₂(Λ(ζ, w)) = |w|² G / (|w|² G + 1)`, `G = |s_Z|²_h / |z₁|²`
at `e_Z⁻¹ ζ` (limit `τ → 0` of `S₁ = |τ|² / (|s_Z|²_h + |τ|²)`, `S₂ = |s_Z|²_h (1 + |τ|²) /
(|s_Z|²_h + |τ|²)` along `z₁ = w τ`). -/
theorem weights_eq (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {N : Set F.carrier} (hN : IsOpen N) {G : F.carrier → ℝ} (hGpos : ∀ y ∈ N, 0 < G y)
    (hGc : ContinuousOn G N)
    (hfac : ∀ y ∈ N, (EReal.exp (E.weight y)).toReal =
      ‖flatCoord (zFlat F y₀) (Fin.last m) y‖ ^ 2 * G y)
    {ζ : ComplexModel m} (hζ : ζ ∈ (chartAt (ComplexModel m) y₀).target)
    (hxN : firstFlagInclusion F ((chartAt (ComplexModel m) y₀).symm ζ) ∈ N) (w : ℂ) :
    strictWeight F E μ (S.Λ ζ w) =
        1 / (‖w‖ ^ 2 * G (firstFlagInclusion F ((chartAt (ComplexModel m) y₀).symm ζ)) + 1) ∧
      zStrictWeight F E μ (S.Λ ζ w) =
        ‖w‖ ^ 2 * G (firstFlagInclusion F ((chartAt (ComplexModel m) y₀).symm ζ)) /
          (‖w‖ ^ 2 * G (firstFlagInclusion F ((chartAt (ComplexModel m) y₀).symm ζ)) + 1) := by
  set x := firstFlagInclusion F ((chartAt (ComplexModel m) y₀).symm ζ) with hx
  set f : ℂ → 𝒳 := fun s => S.ℓ (liftMk _ S.p₀ (bvec ζ w s)) with hfdef
  have hd0 := S.bvec_mem_zero hζ w
  have hdo := (monomialDomain S.Ψ m (idxT m)).isOpen
  have hfc : ContinuousAt f 0 :=
    (((S.hℓ _).comp _ (contMDiffAt_liftMk S.p₀ hd0)).continuousAt).comp
      (continuous_bvec ζ w).continuousAt
  have hx0 : (μ (f 0)).1 = x := by
    have := S.μ_Λ hζ w
    exact congrArg Prod.fst this
  have hxc : ContinuousAt (fun s => (μ (f s)).1) 0 :=
    (continuous_fst.comp hμ.continuous).continuousAt.comp hfc
  have hev1 : ∀ᶠ s in 𝓝 (0 : ℂ), bvec ζ w s ∈ monomialDomain S.Ψ m (idxT m) :=
    (continuous_bvec ζ w).continuousAt.eventually (hdo.mem_nhds hd0)
  have hev2 : ∀ᶠ s in 𝓝 (0 : ℂ), (μ (f s)).1 ∈ N :=
    hxc.preimage_mem_nhds (by rw [hx0]; exact hN.mem_nhds hxN)
  -- the values for `s ≠ 0`
  have hval : ∀ᶠ s in 𝓝[≠] (0 : ℂ),
      strictWeight F E μ (f s) = 1 / (‖w‖ ^ 2 * G (μ (f s)).1 + 1) ∧
      zStrictWeight F E μ (f s) =
        ‖w‖ ^ 2 * G (μ (f s)).1 * (1 + ‖s‖ ^ 2) / (‖w‖ ^ 2 * G (μ (f s)).1 + 1) := by
    filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin]
      with s hs1 hs2 hs0
    obtain ⟨hf, hΨ⟩ := S.flat_μ_ℓ (liftMk _ S.p₀ (bvec ζ w s))
    rw [toModel_liftMk S.p₀ hs1, monomial_bvec] at hΨ
    obtain ⟨-, h2, h3, -, h5⟩ := S.decode hf hΨ
    set q := μ (f s) with hq
    have hr1 := rep_one_ne_zero_of_mem_zeroChart h5
    have hτ : projectiveAffine q.2 = s := by
      rw [← zeroChart_apply_zero h5, h3]
      simp [zeroChart_apply_zero (mem_chart_source _ projectiveZero)]
    have hq2 : q.2 ≠ projectiveZero := by
      intro h0
      exact hs0 (show s = 0 by rw [← hτ, h0, projectiveAffine_projectiveZero])
    have hnot : f s ∉ exceptionalSet F μ := fun h =>
      hq2 ((mem_deformationCentre_iff F).mp h).2
    have hz₁ : flatCoord (zFlat F y₀) (Fin.last m) q.1 = w * s := by
      simp only [flatCoord]
      exact (congrArg (fun v : ComplexModel (m + 1) => v (Fin.last m)) h2).trans
        (stripModelEquiv_symm_apply_last _ _)
    have hwt := hfac q.1 hs2
    rw [hz₁] at hwt
    have hW := baseExceptionalWeight_eq_affine F E hr1
    have hN0 := projectiveWeight_zero_eq hr1
    have hN1 := projectiveWeight_one_eq hr1
    rw [hτ] at hW hN0 hN1
    have hGq := hGpos _ hs2
    have hs2' : 0 < ‖s‖ ^ 2 := by have := norm_pos_iff.mpr hs0; positivity
    have h1s : 0 < 1 + ‖s‖ ^ 2 := by positivity
    have hsn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs0
    constructor
    · rw [strictWeight_eq_of_notMem F hμ hE hnot, hW, hN0, hN1, hwt, norm_mul, mul_pow]
      field_simp
    · rw [zStrictWeight_eq_of_notMem F hμ hE hnot, hW, hwt, norm_mul, mul_pow]
      field_simp
  -- the limits
  have hGx : ContinuousAt (fun s => G (μ (f s)).1) 0 := by
    have := (hGc.continuousAt (hN.mem_nhds hxN))
    rw [← hx0] at this
    exact ContinuousAt.comp (f := fun s => (μ (f s)).1) this hxc
  have hS1c : ContinuousAt (fun s => strictWeight F E μ (f s)) 0 :=
    (continuous_strictWeight F hμ hE).continuousAt.comp hfc
  have hS2c : ContinuousAt (fun s => zStrictWeight F E μ (f s)) 0 :=
    (continuous_zStrictWeight F hμ hE).continuousAt.comp hfc
  have hGx0 : G (μ (f 0)).1 = G x := by rw [hx0]
  have hpos : 0 < ‖w‖ ^ 2 * G x + 1 := by have := hGpos x hxN; positivity
  have hlim1 : Tendsto (fun s => 1 / (‖w‖ ^ 2 * G (μ (f s)).1 + 1)) (𝓝[≠] (0 : ℂ))
      (𝓝 (1 / (‖w‖ ^ 2 * G x + 1))) := by
    have hden : ContinuousAt (fun s : ℂ => ‖w‖ ^ 2 * G (μ (f s)).1 + 1) 0 :=
      (continuousAt_const.mul hGx).add continuousAt_const
    have h := (hden.inv₀ (show ‖w‖ ^ 2 * G (μ (f 0)).1 + 1 ≠ 0 by
      rw [hGx0]; exact hpos.ne')).tendsto
    rw [Pi.inv_apply, hGx0] at h
    simp only [one_div]
    exact (h.mono_left nhdsWithin_le_nhds).congr fun s => by simp
  have hlim2 : Tendsto (fun s : ℂ => ‖w‖ ^ 2 * G (μ (f s)).1 * (1 + ‖s‖ ^ 2) /
      (‖w‖ ^ 2 * G (μ (f s)).1 + 1)) (𝓝[≠] (0 : ℂ))
      (𝓝 (‖w‖ ^ 2 * G x / (‖w‖ ^ 2 * G x + 1))) := by
    have hnum : ContinuousAt (fun s : ℂ => ‖w‖ ^ 2 * G (μ (f s)).1 * (1 + ‖s‖ ^ 2)) 0 :=
      (continuousAt_const.mul hGx).mul (continuousAt_const.add
        (continuous_norm.continuousAt.pow 2))
    have hden : ContinuousAt (fun s : ℂ => ‖w‖ ^ 2 * G (μ (f s)).1 + 1) 0 :=
      (continuousAt_const.mul hGx).add continuousAt_const
    have h := hnum.div hden (by rw [hGx0]; exact hpos.ne')
    have h0 : ‖w‖ ^ 2 * G (μ (f 0)).1 * (1 + ‖(0 : ℂ)‖ ^ 2) / (‖w‖ ^ 2 * G (μ (f 0)).1 + 1) =
        ‖w‖ ^ 2 * G x / (‖w‖ ^ 2 * G x + 1) := by
      rw [hGx0]; simp
    rw [← h0]
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · have h := hS1c.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    exact tendsto_nhds_unique (h.congr' (hval.mono fun s hs => hs.1)) hlim1
  · have h := hS2c.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    exact tendsto_nhds_unique (h.congr' (hval.mono fun s hs => hs.2)) hlim2

end BundleSetup

end Weights

/-! ### The strict transform and the `τ`-chart local inverse -/

section Inverse

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}
  {F} {y₀ : F.tail.carrier}

/-- `S₁ = 0` on the strict transform `X'`. -/
theorem strictWeight_eq_zero_of_mem_strict (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {z : 𝒳} (hz : z ∈ strictCentralFibre F μ) : strictWeight F E μ z = 0 := by
  have hcl : IsClosed {y : 𝒳 | strictWeight F E μ y = 0} :=
    isClosed_eq (continuous_strictWeight F hμ hE) continuous_const
  refine (closure_minimal (fun y hy => ?_) hcl) hz
  obtain ⟨hy1, hy2⟩ := hy
  have hyE : y ∉ exceptionalSet F μ := hy2
  show strictWeight F E μ y = 0
  rw [strictWeight_eq_of_notMem F hμ hE hyE, ((mem_centralBase_iff F).mp hy1),
    projectiveWeight_zero_projectiveZero, zero_div]

theorem notMem_strict_of_strictWeight_pos (hμ : IsNormalConeDeformation F μ)
    {E : MeteredEffectiveQDivisor (m + 1) F.carrier} (hE : IsFirstDivisorUnitMetric F E)
    {z : 𝒳} (hz : 0 < strictWeight F E μ z) : z ∉ strictCentralFibre F μ := fun h =>
  hz.ne' (strictWeight_eq_zero_of_mem_strict hμ hE h)

namespace BundleSetup

variable (S : BundleSetup F μ y₀)

theorem hΨτ : ∀ y ∈ flatDomain S.Ψ, ((splitL m).symm (S.Ψ.toFun (baseChart F y₀.1 y))).2 =
    zeroChart y.2 - zeroChart projectiveZero := by
  intro y _
  have hbc : baseChart F y₀.1 y =
      splitL m (chartAt (ComplexModel (m + 1)) y₀.1 y.1, zeroChart y.2) := rfl
  rw [S.hΨfun, hbc]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

/-- **The `τ`-chart local inverse** at a point of `ℰ \ X'` over the flattening domain: by TN's
local surjectivity the point lies in one of the two monomial charts; in the chart `j = m` the
coordinate `w_{m+1}` is a unit there, and `(w', 1 / w_{m+1}, w_m w_{m+1})` is a
`τ`-chart inverse (uniqueness of lifts through the blow-up). -/
theorem exists_tau_inverse (hμ : IsNormalConeDeformation F μ) {z : 𝒳}
    (hzf : μ z ∈ flatDomain S.Ψ) (hzE : z ∈ exceptionalSet F μ)
    (hzX : z ∉ strictCentralFibre F μ) :
    ∃ O : Set 𝒳, IsOpen O ∧ z ∈ O ∧ ∃ W : 𝒳 → ComplexModel (m + 1 + 1),
      (∀ z' ∈ O, ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
        W z') ∧
      (∀ z' ∈ O, μ z' ∈ flatDomain S.Ψ ∧
        monomial m (idxT m) (W z') = S.Ψ.toFun (baseChart F y₀.1 (μ z'))) ∧
      ∀ z' ∈ O, ∀ hw : W z' ∈ monomialDomain S.Ψ m (idxT m),
        S.ℓ (LiftedOpen.mk _ (W z') hw) = z' := by
  classical
  obtain ⟨j, hj, O, hO, hzO, W, hW, hWμ, hℓW, -⟩ :=
    exists_monomialLocalInverse hμ S.hΨsrc (fun hy hy' => S.hΨflat hy hy') hzf
  rcases le_iff_mem_normal.mp hj with hjZ | hjT
  · -- the chart `j = m`
    subst hjZ
    obtain ⟨ℓZ, ⟨hℓZ, hμℓZ⟩, -⟩ :=
      existsUnique_monomialLift hμ S.hΨsrc (fun hy hy' => S.hΨflat hy hy') hj
    let Cz : ExcChart F μ z := ⟨y₀.1, S.Ψ, S.hΨsrc, fun hy hy' => S.hΨflat hy hy', S.hΨτ,
      idxZ m, Or.inl rfl, ℓZ, hℓZ, hμℓZ, O, hO, hzO, W, hW, hWμ,
      fun z' hz' hw => hℓW ℓZ hℓZ hμℓZ z' hz' hw⟩
    have hT : W z (idxT m) ≠ 0 := Cz.W_idxT_ne_zero rfl hzE hzX
    have hWc : ∀ z' ∈ O, ContinuousAt (fun z' => W z' (idxT m)) z' := fun z' hz' =>
      ((PiLp.continuous_apply 2 _ (idxT m)).continuousAt).comp (hW z' hz').continuousAt
    set O' : Set 𝒳 := O ∩ {z' | W z' (idxT m) ≠ 0} with hO'def
    have hO' : IsOpen O' := by
      refine isOpen_iff_mem_nhds.mpr fun z' hz' => inter_mem (hO.mem_nhds hz'.1) ?_
      exact (hWc z' hz'.1).preimage_mem_nhds (isOpen_ne.mem_nhds hz'.2)
    set W'' : 𝒳 → ComplexModel (m + 1 + 1) := fun z' => WithLp.toLp 2 fun i =>
      if i = idxZ m then (W z' (idxT m))⁻¹ else
        if i = idxT m then W z' (idxT m) * W z' (idxZ m) else W z' i with hW''def
    have hmon : ∀ z' ∈ O', monomial m (idxT m) (W'' z') = monomial m (idxZ m) (W z') := by
      intro z' hz'
      have hT' : W z' (idxT m) ≠ 0 := hz'.2
      have hZT : idxZ m ≠ idxT m := idxZ_ne_idxT
      ext i
      by_cases hiZ : i = idxZ m
      · rw [hiZ]
        have hle : m ≤ (idxZ m).1 := by simp
        simp only [monomial_apply, hW''def, hle, hZT, hZT.symm, true_and, ne_eq,
          not_false_eq_true, if_true, if_false, not_true_eq_false, and_false]
        field_simp
      · by_cases hiT : i = idxT m
        · rw [hiT]
          have hle : m ≤ (idxT m).1 := by simp
          simp only [monomial_apply, hW''def, hle, hZT.symm, true_and, ne_eq, not_false_eq_true,
            if_true, if_false, not_true_eq_false, and_false]
        · have hi : ¬ m ≤ i.1 := fun h => (le_iff_mem_normal.mp h).elim hiZ hiT
          simp [monomial_apply, hW''def, hiZ, hiT, hi]
    have hW''s : ∀ z' ∈ O', ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1))
        𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ W'' z' := by
      intro z' hz'
      have hcomp : ∀ i : Fin (m + 1 + 1), ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ℂ) ∞
          (fun z' => W z' i) z' := fun i =>
        ((EuclideanSpace.proj i : ComplexModel (m + 1 + 1) →L[ℂ] ℂ).contMDiff.contMDiffAt).comp
          z' (hW z' hz'.1)
      have hpi : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, Fin (m + 1 + 1) → ℂ) ∞
          (fun z'' i => if i = idxZ m then (W z'' (idxT m))⁻¹ else
            if i = idxT m then W z'' (idxT m) * W z'' (idxZ m) else W z'' i) z' := by
        refine contMDiffAt_pi_space.2 fun i => ?_
        by_cases hiZ : i = idxZ m
        · simp only [hiZ, if_true]
          exact (hcomp (idxT m)).inv₀ hz'.2
        · by_cases hiT : i = idxT m
          · have hZT : idxT m ≠ idxZ m := idxZ_ne_idxT.symm
            have h := (hcomp (idxT m)).mul (hcomp (idxZ m))
            simp only [hiT, hZT, if_false, if_true]
            exact h
          · simp only [hiZ, hiT, if_false]
            exact hcomp i
      exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (m + 1 + 1) => ℂ)).symm.toContinuousLinearMap
        |>.contMDiff.contMDiffAt.comp z' hpi
    have hWμ'' : ∀ z' ∈ O', μ z' ∈ flatDomain S.Ψ ∧
        monomial m (idxT m) (W'' z') = S.Ψ.toFun (baseChart F y₀.1 (μ z')) := fun z' hz' =>
      ⟨(hWμ z' hz'.1).1, (hmon z' hz').trans (hWμ z' hz'.1).2⟩
    have hmem : ∀ z' ∈ O', W'' z' ∈ monomialDomain S.Ψ m (idxT m) := by
      intro z' hz'
      show monomial m (idxT m) (W'' z') ∈ S.Ψ.target
      rw [(hWμ'' z' hz').2]
      exact S.Ψ.mapsTo_toFun (hWμ'' z' hz').1.2
    refine ⟨O', hO', ⟨hzO, hT⟩, W'', hW''s, hWμ'', fun z' hz' hw => ?_⟩
    -- uniqueness of lifts on `O'`
    set Oo : TopologicalSpace.Opens 𝒳 := ⟨O', hO'⟩
    set wmap : Oo → LiftedOpen.{u} (monomialDomain S.Ψ m (idxT m)) := fun x =>
      LiftedOpen.mk _ (W'' x.1) (hmem x.1 x.2)
    have hwsm : ContMDiff 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ wmap :=
      fun x => LiftedOpen.contMDiffAt_of_toModel _
        (contMDiffAt_subtype_iff.mpr (hW''s x.1 x.2) :
          ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
            (fun x : Oo => W'' x.1) x)
    have huniq := hμ.2.2.2.2 (m + 1 + 1) Oo (μ ∘ Subtype.val)
      (hμ.contMDiff.comp contMDiff_subtype_val) (IsInvertible.pullback_comp_val Oo hμ.2.2.2.1)
    have hlift : μ ∘ (S.ℓ ∘ wmap) = μ ∘ Subtype.val := by
      funext x
      have := congrFun S.hμℓ (wmap x)
      simp only [Function.comp_apply] at this ⊢
      rw [this]
      show (chartAt (ComplexModel (m + 1 + 1)) (y₀.1, projectiveZero)).symm
        (S.Ψ.invFun (monomial m (idxT m) (W'' x.1))) = μ x.1
      rw [(hWμ'' x.1 x.2).2]
      exact flatInverse_flat S.Ψ (hWμ'' x.1 x.2).1
    have heq := huniq.unique ⟨S.hℓ.comp hwsm, hlift⟩ ⟨contMDiff_subtype_val, rfl⟩
    exact congrFun heq ⟨z', hz'⟩
  · -- the chart `j = m + 1`
    subst hjT
    exact ⟨O, hO, hzO, W, hW, hWμ, fun z' hz' hw => hℓW S.ℓ S.hℓ S.hμℓ z' hz' hw⟩

end BundleSetup

end Inverse

/-! ### Atlas charts of `ℰ` from the `τ`-chart -/

section FlatChart

variable {𝒳 : Type u} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳]
  [IsComplexManifold (m + 1 + 1) 𝒳] {μ : 𝒳 → F.carrier × ProjectiveLine}
  {F} {y₀ : F.tail.carrier}

theorem coordinateInclusion_eq_splitL (v : ComplexModel (m + 1)) :
    coordinateInclusion (m + 1 + 1) (m + 1) v = splitL m (v, 0) := by
  ext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · rw [show Fin.last (m + 1) = idxT m from rfl, splitL_last]
    simp [coordinateInclusion]
  · rw [splitL_castSucc]
    simp only [coordinateInclusion]
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      Fin.val_castSucc, i'.2, dite_true]

theorem bvec_strip (v : ComplexModel (m + 1)) :
    bvec (stripModelEquiv m v).1 (stripModelEquiv m v).2 0 = splitL m (v, 0) := by
  simp only [bvec, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  rw [BundleSetup.single_zero']

namespace BundleSetup

variable (S : BundleSetup F μ y₀)

/-- **An atlas chart of `ℰ` inverse to the `τ`-chart** near a point of `ℰ \ X'`
(`tok-wn-vf4:bundle-chart`, chart property): the flattening `W ∘ amb⁻¹` of `ℰ` in an ambient chart
`amb`, with inverse `amb ∘ ℓ_T`, is a `FlatData` of the submanifold `ℰ`, so its chart belongs to
the atlas of `ℰ`; its inverse is `v ↦ ℓ_T(v, 0)`. -/
theorem exists_flatChart (hμ : IsNormalConeDeformation F μ) {z : 𝒳}
    (hzf : μ z ∈ flatDomain S.Ψ) (hzE : z ∈ exceptionalSet F μ)
    (hzX : z ∉ strictCentralFibre F μ) :
    letI := exceptionalChartedSpace F hμ
    ∃ Ech : ComplexChart (m + 1) (exceptionalSet F μ),
      (∀ v ∈ Ech.val.target, ((Ech.val.symm v : exceptionalSet F μ) : 𝒳) =
        S.ℓ (liftMk _ S.p₀ (splitL m (v, 0)))) ∧
      ∀ v, splitL m (v, 0) ∈ monomialDomain S.Ψ m (idxT m) →
        S.ℓ (liftMk _ S.p₀ (splitL m (v, 0))) = z → v ∈ Ech.val.target := by
  classical
  obtain ⟨O, hO, hzO, W, hW, hWμ, hℓW⟩ := S.exists_tau_inverse hμ hzf hzE hzX
  let C : ExcChart F μ z := ⟨y₀.1, S.Ψ, S.hΨsrc, fun hy hy' => S.hΨflat hy hy', S.hΨτ,
    idxT m, Or.inr rfl, S.ℓ, S.hℓ, S.hμℓ, O, hO, hzO, W, hW, hWμ, hℓW⟩
  set amb : ComplexChart (m + 1 + 1) 𝒳 := complexChartAt z with hamb
  have hzamb : z ∈ amb.val.source := mem_complexChartAt_source z
  set Dm := monomialDomain S.Ψ m (idxT m)
  set L : ComplexModel (m + 1 + 1) → 𝒳 := fun v => S.ℓ (liftMk _ S.p₀ v) with hLdef
  have hLc : ∀ v ∈ (Dm : Set (ComplexModel (m + 1 + 1))),
      ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞ L v :=
    fun v hv => (S.hℓ _).comp v (contMDiffAt_liftMk S.p₀ hv)
  have hWO : ∀ a ∈ amb.val.target ∩ amb.val.symm ⁻¹' O,
      W (amb.val.symm a) ∈ (Dm : Set (ComplexModel (m + 1 + 1))) ∧
        L (W (amb.val.symm a)) = amb.val.symm a := fun a ha =>
    ⟨C.W_mem_monomialDomain ha.2, C.ℓ_W ha.2⟩
  let flat : OpenPartialHomeomorph (ComplexModel (m + 1 + 1)) (ComplexModel (m + 1 + 1)) :=
    { toFun := fun a => W (amb.val.symm a)
      invFun := fun v => amb.val (L v)
      source := amb.val.target ∩ amb.val.symm ⁻¹' O
      target := (Dm : Set (ComplexModel (m + 1 + 1))) ∩ L ⁻¹' (O ∩ amb.val.source)
      map_source' := fun a ha => by
        obtain ⟨h1, h2⟩ := hWO a ha
        refine ⟨h1, ?_⟩
        show L (W (amb.val.symm a)) ∈ O ∩ amb.val.source
        rw [h2]
        exact ⟨ha.2, amb.val.map_target ha.1⟩
      map_target' := fun v hv => by
        refine ⟨amb.val.map_source hv.2.2, ?_⟩
        show amb.val.symm (amb.val (L v)) ∈ O
        rw [amb.val.left_inv hv.2.2]
        exact hv.2.1
      left_inv' := fun a ha => by
        show amb.val (L (W (amb.val.symm a))) = a
        rw [(hWO a ha).2, amb.val.right_inv ha.1]
      right_inv' := fun v hv => by
        show W (amb.val.symm (amb.val (L v))) = v
        rw [amb.val.left_inv hv.2.2]
        exact C.W_ℓ hv.1 hv.2.1
      open_source := amb.val.isOpen_inter_preimage_symm hO
      open_target := by
        have hcont : ContinuousOn L Dm := fun v hv => (hLc v hv).continuousAt.continuousWithinAt
        exact hcont.isOpen_inter_preimage Dm.isOpen (hO.inter amb.val.open_source)
      continuousOn_toFun := by
        intro a ha
        exact ((hW _ ha.2).continuousAt.comp (amb.val.continuousAt_symm ha.1)).continuousWithinAt
      continuousOn_invFun := by
        intro v hv
        exact ((amb.val.continuousAt hv.2.2).comp (hLc v hv.1).continuousAt).continuousWithinAt }
  have hflat_diff : DifferentiableOn ℂ flat flat.source := by
    intro a ha
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel (m + 1 + 1)) 𝓘(ℂ, ComplexModel (m + 1 + 1)) ∞
        amb.val.symm a :=
      (contMDiffOn_chart_symm (n := ∞) (x := z)).contMDiffAt
        (amb.val.open_target.mem_nhds ha.1)
    have h2 := (hW _ ha.2).comp a h1
    exact (contMDiffAt_iff_contDiffAt.mp h2).differentiableAt (by simp)
      |>.differentiableWithinAt
  have hflat_symm_diff : DifferentiableOn ℂ flat.symm flat.target := by
    intro v hv
    exact (contDiffAt_chart_comp (hLc v hv.1) amb hv.2.2).differentiableAt (by simp)
      |>.differentiableWithinAt
  let Fd : SubmanifoldChartedSpace.FlatData (m + 1 + 1) (m + 1) 𝒳 (exceptionalSet F μ) :=
    { amb := amb
      flat := flat
      differentiableOn_flat := hflat_diff
      differentiableOn_flat_symm := hflat_symm_diff
      flat_source_subset := inter_subset_left
      mem_iff := fun y hy hyf => by
        have hyO : y ∈ O := by
          have := hyf.2
          rwa [mem_preimage, amb.val.left_inv hy] at this
        show y ∈ exceptionalSet F μ ↔ W (amb.val.symm (amb.val y)) ∈ _
        rw [amb.val.left_inv hy, C.mem_exceptional_iff hyO]
        constructor
        · intro h i hi
          have : i = idxT m := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
          rw [this]; exact h
        · intro h
          exact h (idxT m) (by simp)
      base := z
      base_mem := hzE }
  refine ⟨⟨Fd.chart (Nat.le_succ (m + 1)), ⟨Fd, rfl⟩⟩, fun v hv => ?_, fun v hv hvz => ?_⟩
  · change ((Fd.chart (Nat.le_succ (m + 1))).symm v : 𝒳) = _
    rw [SubmanifoldChartedSpace.FlatData.chart_symm_apply,
      SubmanifoldChartedSpace.FlatData.invPoint_val _ hv]
    change amb.val.symm (amb.val (L (coordinateInclusion (m + 1 + 1) (m + 1) v))) = _
    have hv' : coordinateInclusion (m + 1 + 1) (m + 1) v ∈ flat.target := hv
    rw [amb.val.left_inv hv'.2.2, coordinateInclusion_eq_splitL]
  · show coordinateInclusion (m + 1 + 1) (m + 1) v ∈ flat.target
    rw [coordinateInclusion_eq_splitL]
    refine ⟨hv, ?_⟩
    show L (splitL m (v, 0)) ∈ O ∩ amb.val.source
    rw [show L (splitL m (v, 0)) = z from hvz]
    exact ⟨hzO, hzamb⟩

end BundleSetup

end FlatChart

end SGPT.Okounkov.TranscendentalWN
