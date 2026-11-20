import SGPT.Okounkov.TranscendentalWNKeyEasy
import SGPT.Okounkov.TranscendentalWNKeyFibre
import SGPT.Foundations.Analysis.Pending.FullSpacePatchMeasure
import SGPT.Foundations.Analysis.Pending.PatchOverlap
import SGPT.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# Local tools for the lower semicontinuity of fibre masses (package WN-KEY, lane WN-LSC)

Blueprint `claude-tok-wn-lsc`, nodes `tok-wn-lsc:density-measurable`,
`tok-wn-lsc:density-continuous`, `tok-wn-lsc:fatou`, `tok-wn-lsc:gentle-smooth`,
`tok-wn-lsc:measure-coordinates`; source WN21 §5 (the analytic core of the key easy inequality).

* `measurable_smoothDensity`: the coordinate Monge–Ampère density `n!/πⁿ · Re det(∂∂̄u)` of an
  arbitrary function is Borel measurable.
* `continuousAt_smoothDensity_param`: for a jointly smooth family `F(t, ·)`, the density of
  `F(t, ·)` at a fixed point depends continuously on the parameter `t`.
* `eventually_lintegral_le_add`: Fatou's lemma in the form used below — pointwise convergence of
  measurable densities gives `∫ g ≤ ∫ fᵢ + ε` eventually.
* `isOpen_ne_bot_of_gentle`, `eq_coe_toReal_of_gentle`, `contDiffOn_toReal_of_gentle`: a
  potential with gentle analytic singularities is smooth off its pole set (which is closed),
  because `e^{φ/c}` is smooth.
* `globalMixedMeasure_image_eq_lintegral` (**the non-pluripolar measure in holomorphic
  coordinates**): let `j : V → 𝒳` be holomorphic, `φ` a `Θ`-psh function with `φ ∘ j` a
  `j^*Θ`-psh potential, `ρ` a smooth local potential of `Θ` in a chart `d` of `𝒳` on which
  `φ + ρ` is psh, and `σ : A → D` a biholomorphism onto an open set `D` of a chart `e` of `V`
  over which `j` lands in the domain of `ρ`.  If `y ↦ φ(j(e⁻¹(σ y))) + ρ(d(j(e⁻¹(σ y))))` is a
  smooth (real) function `f` on `A`, then on every measurable `S ⊆ W` (`W` relatively compact in
  `A`), `⟨(j^*Θ + dd^c(φ ∘ j))ⁿ⟩(e⁻¹(σ(S))) = ∫_S (dd^c f)ⁿ`.  The proof transports the
  global non-pluripolar measure through the potential patch `(e, D, ρ ∘ d ∘ j ∘ e⁻¹)`, uses the
  holomorphic covariance of the truncation limit (`mixedTruncationLimitMeasure_comp_biholomorphic`)
  and its stabilization on smooth finite potentials
  (`mixedTruncationLimitMeasure_restrict_smooth_of_original`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Manifold ContDiff ENNReal

namespace SGPT.Okounkov.TranscendentalWN.LSC

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.LocalPotentialPullback
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.LocalNonPluripolarDensity

/-! ### The coordinate density -/

section Density

variable {n : ℕ}

/-- The determinant through the Leibniz formula, entrywise. -/
private theorem det_eq_sum (M : Matrix (Fin n) (Fin n) ℂ) :
    M.det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ∏ i, M (σ i) i := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]

/-- **`tok-wn-lsc:density-measurable`**: the coordinate density `smoothDensity u` is Borel
measurable for every function `u`. -/
theorem measurable_smoothDensity (u : ComplexModel n → ℝ) : Measurable (smoothDensity u) := by
  have hH : ∀ v w : ComplexModel n, Measurable fun z => realHessian u z v w := by
    intro v w
    simp_rw [realHessian_eq_fderiv]
    exact (ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp
      (measurable_fderiv_apply_const ℝ (fderiv ℝ u) v)
  have hE : ∀ j k : Fin n, Measurable fun z => complexHessian u z j k := by
    intro j k
    simp only [complexHessian]
    refine Measurable.add ?_ ?_
    · exact (Complex.measurable_ofReal.comp ((hH _ _).add (hH _ _))).div_const _
    · exact (measurable_const.mul (Complex.measurable_ofReal.comp
        ((hH _ _).sub (hH _ _)))).div_const _
  have hdet : Measurable fun z => (complexHessian u z).det := by
    simp_rw [det_eq_sum]
    refine Finset.measurable_sum _ fun σ _ => measurable_const.mul ?_
    exact Finset.measurable_prod _ fun i _ => hE _ _
  unfold smoothDensity
  exact measurable_const.mul (Complex.measurable_re.comp hdet)

/-- The parametric second derivative of a jointly smooth family is continuous in the parameter
(at a fixed point). -/
theorem continuousAt_realHessian_param {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {F : P → E → ℝ} {t₀ : P} {y : E}
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (t₀, y)) (v w : E) :
    ContinuousAt (fun t => realHessian (F t) y v w) t₀ := by
  -- the first derivative, as a function of `(t, y')`
  set G : P × E → E →L[ℝ] ℝ := fun x => fderiv ℝ (F x.1) x.2 with hG
  have hG1 : ContDiffAt ℝ ∞ G (t₀, y) := by
    have h := ContDiffAt.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (x₀ := (t₀, y))
      (f := fun (x : P × E) (y' : E) => F x.1 y') (g := Prod.snd) ?_ contDiffAt_snd
      (by simp)
    · exact h
    · change ContDiffAt ℝ ∞ (fun p : (P × E) × E => Function.uncurry F (p.1.1, p.2))
        ((t₀, y), y)
      exact hF.comp ((t₀, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hG2 : ContDiffAt ℝ ∞ (fun t => fderiv ℝ (fun y' => G (t, y')) y) t₀ := by
    have h := ContDiffAt.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (x₀ := t₀)
      (f := fun (t : P) (y' : E) => G (t, y')) (g := fun _ => y) ?_ contDiffAt_const
      (by simp)
    · exact h
    · exact hG1
  have hc := hG2.continuousAt
  have heq : (fun t => realHessian (F t) y v w) =
      fun t => fderiv ℝ (fun y' => G (t, y')) y v w := by
    funext t
    rw [realHessian_eq_fderiv]
  rw [heq]
  exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
    ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).continuous)).continuousAt.comp hc

/-- Continuity of the density from continuity of the second derivatives. -/
theorem continuousAt_smoothDensity_of {P : Type*} [TopologicalSpace P]
    {u : P → ComplexModel n → ℝ} {y : P → ComplexModel n} {t₀ : P}
    (h : ∀ v w, ContinuousAt (fun t => realHessian (u t) (y t) v w) t₀) :
    ContinuousAt (fun t => smoothDensity (u t) (y t)) t₀ := by
  have hE : ∀ j k : Fin n, ContinuousAt (fun t => complexHessian (u t) (y t) j k) t₀ := by
    intro j k
    simp only [complexHessian]
    refine ContinuousAt.add ?_ ?_
    · exact (Complex.continuous_ofReal.continuousAt.comp ((h _ _).add (h _ _))).div_const _
    · exact (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
        ((h _ _).sub (h _ _)))).div_const _
  have hdet : ContinuousAt (fun t => (complexHessian (u t) (y t)).det) t₀ := by
    simp_rw [det_eq_sum]
    refine tendsto_finsetSum _ fun σ _ => continuousAt_const.mul ?_
    exact tendsto_finsetProd _ fun i _ => hE _ _
  unfold smoothDensity
  exact continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hdet)

/-- **`tok-wn-lsc:density-continuous`**: for a jointly smooth family `F(t, ·)`, the density
`smoothDensity (F t) y` is continuous in `t` at `t₀`. -/
theorem continuousAt_smoothDensity_param {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : P → ComplexModel n → ℝ} {t₀ : P} {y : ComplexModel n}
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (t₀, y)) :
    ContinuousAt (fun t => smoothDensity (F t) y) t₀ :=
  continuousAt_smoothDensity_of (y := fun _ => y) fun v w => continuousAt_realHessian_param hF v w

/-- The density of a smooth function is continuous. -/
theorem continuousAt_smoothDensity {u : ComplexModel n → ℝ} {y : ComplexModel n}
    (hu : ContDiffAt ℝ ∞ u y) : ContinuousAt (smoothDensity u) y := by
  have hF : ContDiffAt ℝ ∞ (Function.uncurry fun (y' : ComplexModel n) (z : ComplexModel n) => u z)
      (y, y) := by
    change ContDiffAt ℝ ∞ (fun p : ComplexModel n × ComplexModel n => u p.2) (y, y)
    exact hu.comp (y, y) contDiffAt_snd
  have h : ∀ v w, ContinuousAt (fun y' => realHessian u y' v w) y := by
    intro v w
    have hG1 : ContDiffAt ℝ ∞ (fun y' => fderiv ℝ u y') y := by
      have h := ContDiffAt.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (x₀ := y)
        (f := fun (_ : ComplexModel n) (z : ComplexModel n) => u z) (g := id) hF contDiffAt_id
        (by simp)
      exact h
    have hG2 : ContinuousAt (fun y' => fderiv ℝ (fderiv ℝ u) y') y := by
      have h := ContDiffAt.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (x₀ := y)
        (f := fun (_ : ComplexModel n) (z : ComplexModel n) => fderiv ℝ u z) (g := id) ?_
        contDiffAt_id (by simp)
      · exact h.continuousAt
      · change ContDiffAt ℝ ∞ (fun p : ComplexModel n × ComplexModel n => fderiv ℝ u p.2) (y, y)
        exact hG1.comp (y, y) contDiffAt_snd
    simp_rw [realHessian_eq_fderiv]
    exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
      ((ContinuousLinearMap.apply ℝ (ComplexModel n →L[ℝ] ℝ) v).continuous)).continuousAt.comp hG2
  exact continuousAt_smoothDensity_of (u := fun _ => u) (y := id) h

/-- The density of a smooth function has finite integral over a subset of a compact set on
which it is smooth. -/
theorem setLIntegral_smoothDensity_lt_top {u : ComplexModel n → ℝ} {K T : Set (ComplexModel n)}
    (hK : IsCompact K) (hTK : T ⊆ K) (hu : ∀ y ∈ K, ContDiffAt ℝ ∞ u y) :
    ∫⁻ y in T, ENNReal.ofReal (smoothDensity u y) < ⊤ := by
  have hc : ContinuousOn (smoothDensity u) K := fun y hy =>
    (continuousAt_smoothDensity (hu y hy)).continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
  calc ∫⁻ y in T, ENNReal.ofReal (smoothDensity u y)
      ≤ ∫⁻ y in K, ENNReal.ofReal (smoothDensity u y) := lintegral_mono_set hTK
    _ ≤ ∫⁻ _ in K, ENNReal.ofReal C := by
        refine setLIntegral_mono_ae ?_ (Eventually.of_forall fun y hy => ?_) |>.trans le_rfl
        · exact measurable_const.aemeasurable
        · exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
            (by simpa [Real.norm_eq_abs] using hC _ ⟨y, hy, rfl⟩))
    _ = ENNReal.ofReal C * volume K := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end Density

/-! ### Fatou's lemma, eventually form -/

/-- **`tok-wn-lsc:fatou`**: if measurable `fᵢ → g` pointwise along a countably generated
nontrivial filter and `∫ g < ∞`, then for every `ε > 0`, eventually `∫ g ≤ ∫ fᵢ + ε`. -/
theorem eventually_lintegral_le_add {ι α : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {f : ι → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (hlim : ∀ a, Tendsto (fun i => f i a) l (𝓝 (g a)))
    (hfin : ∫⁻ a, g a ∂μ ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ i in l, ∫⁻ a, g a ∂μ ≤ ∫⁻ a, f i a ∂μ + ε := by
  have hfatou : ∫⁻ a, g a ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) l := by
    have h := lintegral_liminf_le (μ := μ) (u := l) hf
    have hg : (fun a => liminf (fun i => f i a) l) = g := funext fun a => (hlim a).liminf_eq
    rwa [hg] at h
  by_cases h0 : ∫⁻ a, g a ∂μ = 0
  · exact Eventually.of_forall fun i => by rw [h0]; exact bot_le
  have hlt : ∫⁻ a, g a ∂μ - ε < liminf (fun i => ∫⁻ a, f i a ∂μ) l :=
    (ENNReal.sub_lt_self hfin h0 hε.ne').trans_le hfatou
  filter_upwards [eventually_lt_of_lt_liminf hlt] with i hi
  exact tsub_le_iff_right.mp hi.le

/-- **`tok-wn-lsc:fatou`, density form**: for a jointly smooth family `F(t, ·)` near
`{t₀} × K`, `K` compact, and a measurable `T ⊆ K`, the integral of the density of `F(t, ·)` over
`T` is eventually at least that of `F(t₀, ·)`, up to `ε`, as `t → t₀`. -/
theorem eventually_setLIntegral_density_le {k : ℕ} {P ι : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {t : ι → P} {t₀ : P}
    (ht : Tendsto t l (𝓝 t₀)) {Fj : P → ComplexModel k → ℝ} {K T : Set (ComplexModel k)}
    (hK : IsCompact K) (hTK : T ⊆ K) (hT : MeasurableSet T)
    (hF : ∀ y ∈ K, ContDiffAt ℝ ∞ (Function.uncurry Fj) (t₀, y)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ i in l, ∫⁻ y in T, ENNReal.ofReal (smoothDensity (Fj t₀) y) ≤
      (∫⁻ y in T, ENNReal.ofReal (smoothDensity (Fj (t i)) y)) + ε := by
  have hF0 : ∀ y ∈ K, ContDiffAt ℝ ∞ (Fj t₀) y := fun y hy =>
    (hF y hy).comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hfin := setLIntegral_smoothDensity_lt_top hK hTK hF0
  rw [← lintegral_indicator hT] at hfin ⊢
  simp_rw [← lintegral_indicator hT]
  refine eventually_lintegral_le_add (l := l) (fun i => ?_) (fun y => ?_) hfin.ne hε
  · exact (ENNReal.measurable_ofReal.comp (measurable_smoothDensity _)).indicator hT
  · by_cases hy : y ∈ T
    · simp only [indicator_of_mem hy]
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        ((continuousAt_smoothDensity_param (hF y (hTK hy))).tendsto.comp ht)
    · simp only [indicator_of_notMem hy]
      exact tendsto_const_nhds

/-! ### Gentle potentials are smooth off their poles -/

section Gentle

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The positive smooth function `e^{φ/c}` of a potential with gentle analytic singularities. -/
private theorem exists_gentle_exp {φ : M → EReal} {θ : ClosedRealOneOneForm n M}
    (hφ : φ ∈ TranscendentalCore.gentleCurrents θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ g : M → ℝ, ChartSmooth (n := n) g ∧ (∀ x, 0 ≤ g x) ∧
      ∀ x, (φ x = ⊥ ↔ g x = 0) ∧ (φ x ≠ ⊥ → φ x = ((c * Real.log (g x) : ℝ) : EReal)) := by
  obtain ⟨-, c, 𝔞, -, hgen⟩ := hφ
  obtain ⟨hq, ⟨hc, -⟩, hne, hsm, -⟩ := hgen
  refine ⟨(c : ℝ), by exact_mod_cast hc, _, hsm, fun x => ENNReal.toReal_nonneg, fun x => ?_⟩
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hφtop : φ x ≠ ⊤ := hq.1.ne_top x
  set a : EReal := ((((c : ℝ)⁻¹ : ℝ) : EReal) * φ x) with ha
  have hne' : EReal.exp a ≠ ⊤ := hne x
  constructor
  · constructor
    · intro hx
      rw [ha, hx, EReal.mul_bot_of_pos (by exact_mod_cast inv_pos.mpr hcR), EReal.exp_bot]
      rfl
    · intro hx
      by_contra hxb
      -- `φ x` is real, so `exp(φ x / c) > 0`
      obtain ⟨r, hr⟩ : ∃ r : ℝ, φ x = r := ⟨(φ x).toReal, (EReal.coe_toReal hφtop hxb).symm⟩
      have : EReal.exp a = ENNReal.ofReal (Real.exp ((c : ℝ)⁻¹ * r)) := by
        rw [ha, hr, ← EReal.coe_mul, EReal.exp_coe]
      rw [this, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hx
      exact (Real.exp_pos _).ne' hx
  · intro hxb
    obtain ⟨r, hr⟩ : ∃ r : ℝ, φ x = r := ⟨(φ x).toReal, (EReal.coe_toReal hφtop hxb).symm⟩
    have : EReal.exp a = ENNReal.ofReal (Real.exp ((c : ℝ)⁻¹ * r)) := by
      rw [ha, hr, ← EReal.coe_mul, EReal.exp_coe]
    rw [this, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp, hr]
    congr 1
    field_simp

/-- **`tok-wn-lsc:gentle-smooth`** (closedness of the pole set): the finite locus of a
potential with gentle analytic singularities is open. -/
theorem isOpen_ne_bot_of_gentle {φ : M → EReal} {θ : ClosedRealOneOneForm n M}
    (hφ : φ ∈ TranscendentalCore.gentleCurrents θ) : IsOpen {x | φ x ≠ ⊥} := by
  obtain ⟨c, -, g, hg, -, hgφ⟩ := exists_gentle_exp hφ
  have hgc : Continuous g := ProductTestForms.ChartSmooth.continuous hg
  have : {x | φ x ≠ ⊥} = g ⁻¹' {0}ᶜ := by
    ext x
    simp [(hgφ x).1]
  rw [this]
  exact isOpen_compl_singleton.preimage hgc

/-- **`tok-wn-lsc:gentle-smooth`**: off its pole set a potential with gentle analytic
singularities is real and smooth in every chart. -/
theorem contDiffOn_toReal_of_gentle {φ : M → EReal} {θ : ClosedRealOneOneForm n M}
    (hφ : φ ∈ TranscendentalCore.gentleCurrents θ) (e : ComplexChart n M) :
    ContDiffOn ℝ ∞ (fun z => (φ (e.val.symm z)).toReal)
      (e.val.target ∩ e.val.symm ⁻¹' {x | φ x ≠ ⊥}) := by
  obtain ⟨c, -, g, hg, hg0, hgφ⟩ := exists_gentle_exp hφ
  have h1 : ContDiffOn ℝ ∞ (fun z => c * Real.log (g (e.val.symm z)))
      (e.val.target ∩ e.val.symm ⁻¹' {x | φ x ≠ ⊥}) := by
    refine contDiffOn_const.mul ((hg e).mono inter_subset_left |>.log ?_)
    intro z hz
    exact fun h => hz.2 ((hgφ _).1.mpr h)
  refine h1.congr fun z hz => ?_
  rw [(hgφ _).2 hz.2, EReal.toReal_coe]

/-- On the finite locus, a gentle potential is the coercion of its real part. -/
theorem eq_coe_toReal_of_ne_bot {φ : M → EReal} {θ : ClosedRealOneOneForm n M}
    (hφ : IsThetaPshPotential θ.val φ) {x : M} (hx : φ x ≠ ⊥) :
    φ x = ((φ x).toReal : EReal) :=
  (EReal.coe_toReal (hφ.1.quasiPlurisubharmonic.ne_top x) hx).symm

end Gentle


/-! ### Plurisubharmonicity on open sets -/

theorem plurisubharmonicOn_congr_of_isOpen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u w : E → EReal} {U : Set E} (hU : IsOpen U) (hu : PlurisubharmonicOn u U)
    (heq : EqOn u w U) : PlurisubharmonicOn w U :=
  fun x hx => (hu x hx).congr (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) heq)

/-! ### The non-pluripolar measure in holomorphic coordinates -/

section Coordinates

variable {k N : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V]
  {𝒳 : Type*} [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳]

/-- **`tok-wn-lsc:measure-coordinates`** (the non-pluripolar measure in holomorphic
coordinates).  Let `j : V → 𝒳` be holomorphic, `φ ∘ j` a `j^*Θ`-psh function, `ρ` a smooth
local potential of `Θ` on `Wd` in the chart `d` of `𝒳` with `φ + ρ` psh there, `e` a chart of
`V` and `σ : A → D` a biholomorphism (inverse `τ`) onto an open set `D` of `e`-coordinates over
which `j` lands in `d⁻¹(Wd)`.  If `f(y) = φ(j(e⁻¹(σ y))) + ρ(d(j(e⁻¹(σ y))))` is a smooth real
function on `A`, then for every measurable `S` inside an open `W` relatively compact in `A`,
`⟨(j^*Θ + dd^c(φ ∘ j))ⁿ⟩(e⁻¹(σ(S))) = ∫_S (dd^c f)ⁿ` (for the global diagonal
non-pluripolar measure, which is `diagonalPotentialMeasure` when `φ ∘ j` is nondegenerate). -/
theorem globalMixedMeasure_image_eq_lintegral (hk : 0 < k)
    {j : V → 𝒳} (hj : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ j)
    {Θ : ClosedRealOneOneForm N 𝒳} {φ : 𝒳 → EReal}
    (hw : ThetaPlurisubharmonic (ClosedRealOneOneForm.pullback hj Θ).val (fun x => φ (j x)))
    (d : ComplexChart N 𝒳) {Wd : Set (ComplexModel N)} {ρ : ComplexModel N → ℝ}
    (hρ : IsSmoothLocalPotential Θ.val d Wd ρ)
    (hpsh : PlurisubharmonicOn (fun z => chartFunction φ d z + (ρ z : EReal)) Wd)
    (e : ComplexChart k V) {A D : Opens (ComplexModel k)}
    {σ τ : ComplexModel k → ComplexModel k} (hστ : IsBiholomorphicPair A D σ τ)
    (hD : (D : Set (ComplexModel k)) ⊆ potentialDomain j e d Wd)
    {f : ComplexModel k → ℝ} (hf : ContDiffOn ℝ ∞ f A)
    (hfeq : ∀ y ∈ A, φ (j (e.val.symm (σ y))) + (ρ (d.val (j (e.val.symm (σ y)))) : EReal) =
      (f y : EReal))
    {W : Opens (ComplexModel k)} (hW : RelativelyCompactIn W A)
    {S : Set (ComplexModel k)} (hS : MeasurableSet S) (hSW : S ⊆ W) :
    globalMixedMeasure (fun _ : Fin k => ClosedRealOneOneForm.pullback hj Θ)
        (fun _ => fun x => φ (j x)) (fun _ => hw)
        (e.val.symm '' (σ '' S)) = ∫⁻ y in S, ENNReal.ofReal (smoothDensity f y) := by
  set θV := ClosedRealOneOneForm.pullback hj Θ with hθV
  set u : V → EReal := fun x => φ (j x) with hu
  have hDo : IsOpen (D : Set (ComplexModel k)) := D.isOpen
  have hPD : IsOpen (potentialDomain j e d Wd) := potentialDomain_isOpen hj e d hρ.1
  -- the local potential and plurisubharmonicity of the corrected potential on `D`
  have hloc : IsSmoothLocalPotential θV.val e D (ρ ∘ coordinateMap j e d) :=
    (isSmoothLocalPotential_pullback hj e hρ).mono hDo hD
  have hpshD : PlurisubharmonicOn
      (fun z => chartFunction u e z + ((ρ ∘ coordinateMap j e d) z : EReal)) D := by
    have hpull := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hPD
      (((coordinateMap_contDiffOn hj e d).mono inter_subset_left).differentiableOn
        (by simp)) (fun _ hy => hy.2) hpsh
    refine plurisubharmonicOn_congr_of_isOpen hDo (hpull.mono hD) fun z hz => ?_
    have hz' := hD hz
    change φ (d.val.symm (d.val (j (e.val.symm z)))) + (ρ (coordinateMap j e d z) : EReal) =
      φ (j (e.val.symm z)) + (ρ (coordinateMap j e d z) : EReal)
    rw [d.val.left_inv hz'.1.2]
  let P : Patch (fun _ : Fin k => θV) (fun _ => u) :=
    { chart := e
      domain := D
      domain_le_target := fun z hz => (hD hz).1.1
      potential := fun _ => ρ ∘ coordinateMap j e d
      localPotential := fun _ => hloc
      plurisubharmonic := fun _ => hpshD }
  -- the coordinate image
  have hSA : S ⊆ A := hSW.trans (subset_closure.trans hW.2)
  set T : Set (ComplexModel k) := σ '' S with hT
  have hTD : T ⊆ D := by rintro _ ⟨y, hy, rfl⟩; exact hστ.mapsTo (hSA hy)
  have hTeq : T = (D : Set (ComplexModel k)) ∩ τ ⁻¹' S := hστ.image_eq hSA
  have hTt : T ⊆ e.val.target := fun z hz => (hD (hTD hz)).1.1
  have hSP : e.val.symm '' T ⊆ (P.source : Set V) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨e.val.map_target (hTt hz), ?_⟩
    show e.val (e.val.symm z) ∈ D
    rw [e.val.right_inv (hTt hz)]
    exact hTD hz
  have himg : e.val '' (e.val.symm '' T ∩ (P.source : Set V)) = T := by
    rw [inter_eq_left.mpr hSP]
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      rw [e.val.right_inv (hTt hw)]
      exact hw
    · intro hz
      exact ⟨e.val.symm z, ⟨z, hz, rfl⟩, e.val.right_inv (hTt hz)⟩
  -- step 1: the global measure is the truncation limit on the patch
  have h1 : globalMixedMeasure (fun _ : Fin k => θV) (fun _ => u) (fun _ => hw)
      (e.val.symm '' T) =
      mixedTruncationLimitMeasure D P.corrected P.plurisubharmonic T := by
    have h := (Measure.restrict_eq_self
      (globalMixedMeasure (fun _ : Fin k => θV) (fun _ => u) (fun _ => hw)) hSP).symm
    rw [h, globalMixedMeasure_restrict_patch, patchMeasure,
      Patch.pushMeasure_apply_image, himg]
  -- step 2: holomorphic covariance
  have hvA : ∀ i, PlurisubharmonicOn (fun y => P.corrected i (σ y)) A := fun i =>
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic A.isOpen
      (hστ.holo.differentiableOn (by simp)) hστ.mapsTo (P.plurisubharmonic i)
  have hcov : mixedTruncationLimitMeasure A (fun i y => P.corrected i (σ y)) hvA =
      ((mixedTruncationLimitMeasure D P.corrected P.plurisubharmonic).restrict D).map τ :=
    mixedTruncationLimitMeasure_comp_biholomorphic hστ P.plurisubharmonic hvA
  have h2 : mixedTruncationLimitMeasure D P.corrected P.plurisubharmonic T =
      mixedTruncationLimitMeasure A (fun i y => P.corrected i (σ y)) hvA S := by
    rw [hcov, Measure.map_apply_of_aemeasurable
      (hστ.holo_inv.continuousOn.aemeasurable hDo.measurableSet) hS,
      Measure.restrict_apply' hDo.measurableSet, hTeq, inter_comm]
  -- step 3: stabilization on the smooth finite potential `f`
  have hcorr : ∀ i, ∀ y ∈ A, P.corrected i (σ y) = (f y : EReal) := by
    intro i y hy
    exact hfeq y hy
  have hpshf : PlurisubharmonicOn (fun z => (f z : EReal)) W :=
    plurisubharmonicOn_congr_of_isOpen W.isOpen ((hvA ⟨0, hk⟩).mono (subset_closure.trans hW.2))
      fun y hy => hcorr ⟨0, hk⟩ y (subset_closure.trans hW.2 hy)
  have hfW : IsSmoothPshOn W f := isSmoothPshOn_of_psh (hf.mono (subset_closure.trans hW.2)) hpshf
  have hdiag : IsSmoothMixedPshOn W (fun _ : Fin k => f) := IsSmoothMixedPshOn.diagonal hfW
  have heqW : ∀ i, EqOn (fun z => (P.corrected i (σ z)).toReal) f W := by
    intro i z hz
    simp only [hcorr i z (subset_closure.trans hW.2 hz), EReal.toReal_coe]
  have hsm : IsSmoothMixedPshOn W (fun i z => (P.corrected i (σ z)).toReal) :=
    isSmoothMixedPshOn_of_eqOn hdiag heqW
  -- a lower bound for `f` on the closure of `W`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ closure (W : Set (ComplexModel k)), -C < f z := by
    obtain ⟨C, hC⟩ := (hW.1.image_of_continuousOn
      (hf.continuousOn.mono hW.2)).isBounded.exists_norm_le
    exact ⟨C + 1, fun z hz => by
      have h := hC (f z) ⟨z, hz, rfl⟩
      rw [Real.norm_eq_abs, abs_le] at h
      linarith⟩
  obtain ⟨kk, hkk⟩ := exists_nat_gt C
  have hWk : (W : Set (ComplexModel k)) ⊆
      commonStrictLocus A (fun i y => P.corrected i (σ y)) kk := by
    intro z hz
    refine ⟨subset_closure.trans hW.2 hz, fun i => ?_⟩
    show _ < P.corrected i (σ z)
    rw [hcorr i z (subset_closure.trans hW.2 hz)]
    exact EReal.coe_lt_coe_iff.mpr (by linarith [hC z (subset_closure hz)])
  have h3 := mixedTruncationLimitMeasure_restrict_smooth_of_original hvA kk hW hWk hsm
  have h4 : mixedTruncationLimitMeasure A (fun i y => P.corrected i (σ y)) hvA S =
      smoothMeasure W f hfW S := by
    rw [← Measure.restrict_eq_self _ hSW, h3, smoothMixedMeasure_eq_of_eqOn hsm hdiag heqW,
      smoothMixedMeasure_diagonal W f hfW hdiag]
  rw [h1, h2, h4, smoothMeasure, withDensity_apply _ hS, Measure.restrict_restrict hS,
    inter_eq_left.mpr hSW]

end Coordinates

end SGPT.Okounkov.TranscendentalWN.LSC
