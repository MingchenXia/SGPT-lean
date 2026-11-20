import SGPT.Foundations.Analysis.Pending.MultiplierIdealUpperBound
import SGPT.Foundations.Analysis.Pending.HironakaHolomorphicPointJets
import SGPT.Foundations.Analysis.Pending.ManifoldFiniteSpanChartTransport
import SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
import SGPT.Foundations.Analysis.Pending.HironakaChowLemma

/-!
# Members of multiplier ideals with small multiplicity at a point

Source: chapter *The theory of Okounkov bodies*, `thm:nuOk` (the generic Lelong number
`ν(φ, E) = min_{x ∈ E} ν(φ, x)` of `def:pshfunctions:L1101`), through the classical inequality
`ord_x 𝓘(kφ) ≤ k ν(φ, x)` (Demailly's approximation / Ohsawa–Takegoshi, FPT q06): for every
point `x` and every `k > 0` there is a germ `F ∈ 𝓘(kφ)_x` whose multiplicity `a` at `x` satisfies
`2a ≤ k ν(φ, x)` (Lelong numbers in TN's normalization `lelongNumber`, twice the book's).

We read the multiplicity on the chart-translated analytic germ: `F` has multiplicity `≤ a` at `x`
iff its germ is not in `𝔪^{a+1}`. The analytic input is TN's
`MultiplierIdealUpperBound.exists_original_member_nonzero_jet_bound_of_finite` (local Bergman
kernels and the Ohsawa–Takegoshi lower bound), applied with the identity modification and the
**translation flattening** at `x` (the coordinate hyperplane through `x` in the preferred chart),
whose flattening coordinates are the chart coordinates centred at `x`.

## Main results

* `translationFlattening`: the flattening of the coordinate hyperplane through `x` by translation;
* `exists_multiplier_member_not_mem_pow`: `F ∈ 𝓘(pu)_x`, germ of `F` not in `𝔪^{a+1}`,
  `2a ≤ p ν(u, x)`;
* `chartTranslatedGerm_mem_of_isInSpanAt`: a holomorphic combination of functions whose germs lie
  in an ideal `I` of `𝒪_{ℂⁿ,0}` has its germ in `I`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF7

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open DemaillyApproximantDivisorialLelong HironakaHolomorphicJetRankLoci IsLocalRing

/-- The translation `w ↦ w - c` as a local biholomorphism centred at `c`, with source an open
set `T ∋ c`. -/
def translationEquivOn {n : ℕ} (c : ComplexModel n) (T : Set (ComplexModel n)) (hT : IsOpen T)
    (hc : c ∈ T) : LocalHolomorphicEquivAt (n := n) c where
  source := T
  target := (fun z => z + c) ⁻¹' T
  isOpen_source := hT
  isOpen_target := hT.preimage (continuous_add_const c)
  center_mem_source := hc
  toFun := fun w => w - c
  invFun := fun z => z + c
  toFun_holomorphic := (differentiable_id.sub_const c).differentiableOn
  invFun_holomorphic := (differentiable_id.add_const c).differentiableOn
  mapsTo_toFun := fun w hw => by
    change w - c + c ∈ T
    rwa [sub_add_cancel]
  mapsTo_invFun := fun z hz => hz
  left_inv := fun w _ => sub_add_cancel w c
  right_inv := fun z _ => add_sub_cancel_right z c

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]

/-- The coordinate hyperplane through `x` in the preferred chart at `x`. -/
def chartHyperplane (x : Y) : Set Y :=
  {y | ((complexChartAt (n := m + 1) x).val y - (complexChartAt (n := m + 1) x).val x)
    (Fin.last m) = 0}

/-- **The translation flattening at `x`**: the flattening of the coordinate hyperplane through
`x` whose coordinates are the chart coordinates centred at `x`. -/
def translationFlattening (x : Y) : DivisorFlattening (m := m) (chartHyperplane (m := m) x) x where
  Φ := translationEquivOn ((complexChartAt (n := m + 1) x).val x)
    (complexChartAt (n := m + 1) x).val.target (complexChartAt (n := m + 1) x).val.open_target
    ((complexChartAt (n := m + 1) x).val.map_source (mem_complexChartAt_source x))
  source_subset := subset_rfl
  map_center := sub_self _
  mem_iff := fun _ _ _ => Iff.rfl

theorem translationFlattening_point (x : Y) (z : ComplexModel (m + 1)) :
    (translationFlattening (m := m) x).point z =
      (chartAt (ComplexModel (m + 1)) x).symm (z + chartAt (ComplexModel (m + 1)) x x) :=
  rfl

variable [IsComplexManifold (m + 1) Y]

/-- **Demailly's inequality at a point, on germs: `ord_x 𝓘(pu) ≤ p ν(u, x)`.** For a quasi-psh
`u`, a point `x` with finite Lelong number and `p > 0`, there are `F ∈ 𝓘(pu)_x` and `a ∈ ℕ` with
`2a ≤ p ν(u, x)` such that the germ of `F` at `x` (chart translated) is not in `𝔪^{a+1}` (`F`
has multiplicity at most `a` at `x`). -/
theorem exists_multiplier_member_not_mem_pow {u : Y → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u) (x : Y) (p : ℕ) (hp : 0 < p)
    (hfin : lelongNumber (n := m + 1) u x ≠ ⊤) :
    ∃ (F : Y → ℂ) (hF : HolomorphicAt (m + 1) F x) (a : ℕ),
      (multiplierIdeal (n := m + 1) (p : ℝ) u).mem x F ∧
      chartTranslatedGerm x x (mem_chart_source _ x) F hF ∉
        maximalIdeal (HolGerm (ComplexModel (m + 1))) ^ (a + 1) ∧
      ENNReal.ofReal (2 * (a : ℝ)) ≤ ENNReal.ofReal (p : ℝ) * lelongNumber (n := m + 1) u x := by
  obtain ⟨F, a, hFmem, hjet, hbound⟩ :=
    MultiplierIdealUpperBound.exists_original_member_nonzero_jet_bound_of_finite
      (π := (id : Y → Y)) HironakaChowLemma.isAnalyticModification_id hu
      (translationFlattening (m := m) x) p hp hfin
  refine ⟨F, hFmem.1, a, hFmem, fun hmem => ?_, hbound⟩
  unfold chartTranslatedGerm translatedGerm at hmem
  rw [HironakaHolomorphicPointJets.mem_maximalIdeal_pow_iff_iteratedFDeriv] at hmem
  exact hjet (hmem a (Nat.lt_succ_self a))

/-- Eventually equal functions have the same chart-translated germ. -/
theorem chartTranslatedGerm_congr (x : Y) {F G : Y → ℂ} (hF : HolomorphicAt (m + 1) F x)
    (hG : HolomorphicAt (m + 1) G x) (h : F =ᶠ[𝓝 x] G) :
    chartTranslatedGerm x x (mem_chart_source _ x) F hF =
      chartTranslatedGerm x x (mem_chart_source _ x) G hG := by
  unfold chartTranslatedGerm translatedGerm
  apply HolGerm.mk_eq_mk_iff.mpr
  set e := chartAt (ComplexModel (m + 1)) x
  have h1 : Tendsto (fun z : ComplexModel (m + 1) => z + e x) (𝓝 0) (𝓝 (e x)) := by
    simpa only [zero_add] using (continuous_add_const (e x)).tendsto 0
  have h2 := (e.continuousAt_symm (e.map_source (mem_chart_source _ x))).tendsto.comp h1
  have ht : Tendsto (fun z : ComplexModel (m + 1) => e.symm (z + e x)) (𝓝 0) (𝓝 x) := by
    simpa only [Function.comp_def, e.left_inv (mem_chart_source _ x)] using h2
  exact ht.eventually h

/-- **Germs of holomorphic combinations.** If `F` is, near `x`, a holomorphic combination of
functions `h` with `S h`, each holomorphic at `x` with chart germ in the ideal `I`, then the chart
germ of `F` lies in `I`. -/
theorem chartTranslatedGerm_mem_of_isInSpanAt {S : (Y → ℂ) → Prop} {x : Y} {F : Y → ℂ}
    (hF : IsInSpanAt (n := m + 1) S x F) (I : Ideal (HolGerm (ComplexModel (m + 1))))
    (hS : ∀ h, S h → ∃ hh : HolomorphicAt (m + 1) h x,
      chartTranslatedGerm x x (mem_chart_source _ x) h hh ∈ I) :
    chartTranslatedGerm x x (mem_chart_source _ x) F hF.1 ∈ I := by
  obtain ⟨hFh, N, s, c, hs, hc, heq⟩ := hF
  have hsh : ∀ i, HolomorphicAt (m + 1) (s i) x := fun i => (hS _ (hs i)).1
  have hspan : IsInSpanAt (n := m + 1) (· ∈ range s) x F :=
    ⟨hFh, N, s, c, fun i => mem_range_self i, hc, heq⟩
  have h1 := (ManifoldFiniteSpanChartTransport.isInSpanAt_comp_chartSymm_iff
    (mem_chart_source (ComplexModel (m + 1)) x) s F).mp hspan
  have h2 := (isInSpanAt_iff_translatedGerm_mem
    (fun i z => s i ((chartAt (ComplexModel (m + 1)) x).symm z))
    ((chartAt (ComplexModel (m + 1)) x) x)
    (fun i => CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x) (hsh i))
    (CartanLocalReduction.holAt_comp_chart_symm (mem_chart_source _ x) hFh)).mp h1
  unfold translatedIdeal at h2
  refine (Ideal.span_le.mpr ?_) h2
  rintro _ ⟨i, rfl⟩
  exact (hS _ (hs i)).2

end SGPT.Okounkov.OF7
