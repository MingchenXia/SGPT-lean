import SGPT.Foundations.Analysis.Pending.ConcentratedCurrent
import SGPT.Foundations.Analysis.Pending.GraphFibrePotentialLimit
import SGPT.Foundations.Analysis.Pending.GraphSupport
import SGPT.Foundations.Analysis.Pending.ProductMapMixedMeasure
import SGPT.Foundations.Analysis.Pending.YauTheoremInterface
import SGPT.Foundations.Analysis.Pending.NefBoundedMixedMass
import SGPT.Foundations.Analysis.Pending.BoucksomResolutionStep

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Tools for the uniform nef core of Boucksom 4.8 on `Y × X`

Source: Boucksom, proof of Theorem 4.8 and Lemma 4.10 (`bou02-volume:4.8`, `bou02-volume:4.10`);
Demailly--Păun, proof of Theorem 2.12 (`dp04-kahler-cone:2.12`).  TN.4 plan, §1 F6 "STATUS (run 0157
end)", steps U1(d) and U4.  These are the pieces the
assembly `UniformNefCore` needs beyond the proved graph route:

* **slot integrals** — `slotIntegral_eq_of_background`: `∫ θ₀ ∧ ⋯ ∧ θ_{N-1}` does not depend on the
  Kähler background used to integrate it; `slotIntegral_comp_perm` (symmetry);
  `slotIntegral_add_le_two_pow`: if every prefix integral `∫ aⁱ ∧ c^{N-i}` is `≤ C`, then
  `∫ (c + a)^N ≤ 2^N C` (binomial expansion).
* **the product formula on `V × X`** — `slotIntegral_prodForm`:
  `∫_{V×X} (p₁^*a + p₂^*c)^{2n} = C(2n, n) ∫_V aⁿ ∫_X cⁿ`.
* **the graph part** — `exists_isPositive_sub_smul_graphCurrent_of_le`: `Θ ≥ λ [Γ_μ]` with
  `λ ≥ σ_Θ(Γ_μ) / mass[Γ_μ]` (TN23's support theorem on a graph), and `mass_graphCurrent_eq`:
  `mass[Γ_μ] = ∫_V (ω_V + μ^*ω_X)ⁿ`.
* **Yau's theorem on `V × X`** — `exists_yau_prodForm`, from the TEMPORARY named input
  `YauTheorem.exists_kahler_mongeAmpere_eq_exp` through (Y-bou02).
* **the pulled-back concentration** — `isSemipositive_half_add_ddc_comp` and
  `le_globalMixedMeasure_concentrationSlot_comp`: for `ν = μ × id` and `ω_V ≥ μ^*ω`, the fixed
  concentration `(f, V_ε, δ)` on `X × X` gives `(1/2) W_V + ddᶜ(f ∘ ν) ≥ 0` and
  `∫_{ν⁻¹ S} (W_V + ddᶜ(f ∘ ν))ᵖ ∧ W_Vⁿ⁻ᵖ ≥ ∫_S (W + ddᶜf)ᵖ ∧ Wⁿ⁻ᵖ`
  (`ProductMapMixedMeasure` + slot monotonicity).
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal Manifold

universe u

namespace SGPT.Foundations.Analysis.Pending.UniformNefCoreSupport

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses FirstPass.BlowupSequences
  StronglyPositiveForms ProductTestForms PositiveProductCurrents IntegrationCurrent
  TopDegreeDensity SmoothCurrentTraceMeasure ManifoldTubePositivity MixedMassClassInvariance
  NefMixedMass GlobalNonPluripolar NefCoreKahlerCurrent
open scoped ProductComplexManifold
open ProductComplexManifold

/-! ### Slot integrals: background independence, symmetry, binomial bound -/

section Slots

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The Kähler volume of `w'` is the Kähler volume of `w` with density `w'^N / w^N`. -/
theorem withDensity_topRatio_formPow (w w' : KahlerBackground N M) :
    (kahlerVolume w).withDensity
        (fun x => ENNReal.ofReal (topRatio w.form.val (formPow w'.form.val N) x)) =
      kahlerVolume w' := by
  have hω' : ∀ _ : Fin N, ThetaPlurisubharmonic w'.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w'.form).mpr w'.isSemipositive).1
  have h := withDensity_topRatio_eq_globalMixedMeasure w (formPow w'.form.val N) hω'
    fun e z _ => by rw [formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]
  exact h

/-- **Slot integrals do not depend on the background.** -/
theorem slotIntegral_eq_of_background (w w' : KahlerBackground N M)
    (θ : Fin N → ClosedRealOneOneForm N M) : slotIntegral w' θ = slotIntegral w θ := by
  rw [slotIntegral, slotIntegral, ← withDensity_topRatio_formPow w w',
    integral_withDensity_eq_integral_toReal_smul
      (f := fun x => ENNReal.ofReal (topRatio w.form.val (formPow w'.form.val N) x))
      (ENNReal.measurable_ofReal.comp (continuous_topRatio w.isKahler.1 _).measurable)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hpos := topRatio_formPow_pos w w'.isKahler x
  have hz := (complexChartAt (n := N) x).val.map_source (mem_complexChartAt_source x)
  have hD := topDensity_formPow_pos w'.isKahler.1 hz
  simp only
  rw [ENNReal.toReal_ofReal hpos.le, smul_eq_mul]
  simp only [topRatio, chartRatio]
  field_simp

/-- **Slot integrals are symmetric.** -/
theorem slotIntegral_comp_perm (w : KahlerBackground N M) (θ : Fin N → ClosedRealOneOneForm N M)
    (σ : Equiv.Perm (Fin N)) : slotIntegral w (fun i => θ (σ i)) = slotIntegral w θ := by
  rw [slotIntegral, slotIntegral]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [topRatio, chartRatio]
  rw [topDensity_slotForm_coeff, topDensity_slotForm_coeff]
  congr 1
  exact actualMixedTopDensity_perm
    (fun i => (θ i).val.coeff (complexChartAt (n := N) x) ((complexChartAt (n := N) x).val x)) σ

/-- A permutation of `Fin N` sending the first `k` indices onto a given set of card `k`. -/
theorem exists_perm_prefix (T : Finset (Fin N)) :
    ∃ σ : Equiv.Perm (Fin N), ∀ j : Fin N, (σ j ∈ T ↔ (j : ℕ) < T.card) := by
  classical
  set P : Finset (Fin N) := Finset.univ.filter fun j : Fin N => (j : ℕ) < T.card with hP
  have hTN : T.card ≤ N := by
    simpa using Finset.card_le_univ T
  have hPcard : P.card = T.card := by
    rw [hP, Fin.card_filter_val_lt, min_eq_right hTN]
  have hc1 : Fintype.card {j // j ∈ P} = Fintype.card {j // j ∈ T} := by
    rw [Fintype.card_coe, Fintype.card_coe, hPcard]
  have hc2 : Fintype.card {j // ¬ j ∈ P} = Fintype.card {j // ¬ j ∈ T} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_coe, hPcard]
  set e₁ := Fintype.equivOfCardEq hc1
  set e₂ := Fintype.equivOfCardEq hc2
  refine ⟨Equiv.subtypeCongr e₁ e₂, fun j => ?_⟩
  have hjP : j ∈ P ↔ (j : ℕ) < T.card := by simp [hP]
  by_cases hj : j ∈ P
  · have h1 : Equiv.subtypeCongr e₁ e₂ j = e₁ ⟨j, hj⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hj]
    rw [h1]
    exact ⟨fun _ => hjP.mp hj, fun _ => (e₁ ⟨j, hj⟩).2⟩
  · have h2 : Equiv.subtypeCongr e₁ e₂ j = e₂ ⟨j, hj⟩ := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl, hj]
    rw [h2]
    exact ⟨fun h => absurd h (e₂ ⟨j, hj⟩).2, fun h => absurd (hjP.mpr h) hj⟩

/-- A two-valued family is a permutation of the prefix family with the same number of slots of
each kind. -/
theorem slotIntegral_piecewise_const (w : KahlerBackground N M) (a c : ClosedRealOneOneForm N M)
    (s : Finset (Fin N)) :
    slotIntegral w (s.piecewise (fun _ => c) (fun _ => a)) =
      slotIntegral w (fun j : Fin N => if (j : ℕ) < sᶜ.card then a else c) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_prefix (N := N) sᶜ
  rw [← slotIntegral_comp_perm w (s.piecewise (fun _ => c) (fun _ => a)) σ]
  congr 1
  funext j
  by_cases hj : (j : ℕ) < sᶜ.card
  · have hmem : σ j ∉ s := Finset.mem_compl.mp ((hσ j).mpr hj)
    rw [if_pos hj, Finset.piecewise_eq_of_notMem _ _ _ hmem]
  · have hmem : σ j ∈ s := by
      by_contra h
      exact hj ((hσ j).mp (Finset.mem_compl.mpr h))
    rw [if_neg hj, Finset.piecewise_eq_of_mem _ _ _ hmem]

/-- **Binomial bound**: if every prefix integral `∫ aⁱ ∧ c^{N-i}` (`i ≤ N`) is at most `C`, then
`∫ (c + a)^N ≤ 2^N C`. -/
theorem slotIntegral_add_le_two_pow (w : KahlerBackground N M) (a c : ClosedRealOneOneForm N M)
    {C : ℝ}
    (hC : ∀ i : ℕ, i ≤ N → slotIntegral w (fun j : Fin N => if (j : ℕ) < i then a else c) ≤ C) :
    slotIntegral w (fun _ => c + a) ≤ 2 ^ N * C := by
  classical
  have h := slotIntegral_add_smul_eq_sum w (fun _ => c) (fun _ => a) 1
  simp only [one_smul, ite_self, Finset.prod_const_one, one_mul] at h
  rw [h]
  calc ∑ s : Finset (Fin N), slotIntegral w (s.piecewise (fun _ => c) (fun _ => a))
      ≤ ∑ _s : Finset (Fin N), C := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [slotIntegral_piecewise_const]
        exact hC _ (by simpa using Finset.card_le_univ sᶜ)
    _ = 2 ^ N * C := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
        norm_cast

/-- `∫ (t a)^N = t^N ∫ a^N`. -/
theorem slotIntegral_const_smul (w : KahlerBackground N M) (a : ClosedRealOneOneForm N M) (t : ℝ) :
    slotIntegral w (fun _ => t • a) = t ^ N * slotIntegral w (fun _ => a) := by
  have h := BoucksomResolutionStep.slotIntegral_smul_prefix w a t N
  rw [min_self] at h
  rw [← h]
  congr 1
  funext j
  rw [if_pos j.isLt]

/-- `∫ ωᴺ` of the background is its volume. -/
theorem slotIntegral_form (w : KahlerBackground N M) :
    slotIntegral w (fun _ => w.form) = (kahlerVolume w).real univ := by
  rw [slotIntegral]
  simp_rw [← topRatio_formPow_eq_slotForm', topRatio_formPow w.isKahler.1]
  simp [integral_const]

end Slots

/-! ### The product formula on `V × X` -/

section Product

open FibrePushforwardProductForm ProductMixedMeasure

variable {q : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel (q + 1)) V]
  [IsComplexManifold (q + 1) V] {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (q + 1)) X] [IsComplexManifold (q + 1) X]

/-- `(p₁^*a + p₂^*c)^{2n}` over `(p₁^*ω_V + p₂^*ω_X)^{2n}` at `(x, y)` is the product of the ratios. -/
theorem topRatio_formPow_prodForm₂ (wV : KahlerBackground (q + 1) V)
    (wX : KahlerBackground (q + 1) X) (a : ClosedRealOneOneForm (q + 1) V)
    (c : ClosedRealOneOneForm (q + 1) X) (x : V) (y : X) :
    topRatio (prodKahlerBackground wV wX).form.val
        (formPow (prodForm a c).val ((q + 1) + (q + 1))) (x, y) =
      topRatio wV.form.val (formPow a.val (q + 1)) x *
        topRatio wX.form.val (formPow c.val (q + 1)) y := by
  set e := complexChartAt (n := q + 1) x
  set e' := complexChartAt (n := q + 1) y
  have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  have hz' : e'.val y ∈ e'.val.target := e'.val.map_source (mem_complexChartAt_source y)
  have hE : complexChartAt (n := (q + 1) + (q + 1)) (x, y) = prodComplexChart e e' := rfl
  have hEx : (prodComplexChart e e').val (x, y) =
      prodModelEquiv (q + 1) (q + 1) (e.val x, e'.val y) := rfl
  simp only [topRatio, chartRatio]
  rw [hE, hEx, prodKahlerBackground_form, topDensity_formPow_prodForm a c e e' hz hz',
    topDensity_formPow_prodForm wV.form wX.form e e' hz hz']
  have hC : ((((q + 1) + (q + 1)).choose (q + 1) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  rw [mul_assoc, mul_assoc, mul_div_mul_left _ _ hC, mul_div_mul_comm]

variable [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

/-- **The product formula**: `∫_{V×X} (p₁^*a + p₂^*c)^{2n} = C(2n, n) ∫_V aⁿ ∫_X cⁿ`. -/
theorem slotIntegral_prodForm (wV : KahlerBackground (q + 1) V) (wX : KahlerBackground (q + 1) X)
    (a : ClosedRealOneOneForm (q + 1) V) (c : ClosedRealOneOneForm (q + 1) X) :
    slotIntegral (prodKahlerBackground wV wX) (fun _ => prodForm a c) =
      ((((q + 1) + (q + 1)).choose (q + 1) : ℕ) : ℝ) * slotIntegral wV (fun _ => a) *
        slotIntegral wX (fun _ => c) := by
  rw [slotIntegral, slotIntegral, slotIntegral]
  simp_rw [← topRatio_formPow_eq_slotForm']
  rw [kahlerVolume_prodKahlerBackground, integral_smul_measure]
  have h : ∀ z : V × X, topRatio (prodKahlerBackground wV wX).form.val
      (formPow (prodForm a c).val ((q + 1) + (q + 1))) z =
      topRatio wV.form.val (formPow a.val (q + 1)) z.1 *
        topRatio wX.form.val (formPow c.val (q + 1)) z.2 := fun z =>
    topRatio_formPow_prodForm₂ wV wX a c z.1 z.2
  simp_rw [h]
  rw [integral_prod_mul, ENNReal.toReal_natCast, smul_eq_mul, mul_assoc]

end Product

/-! ### The graph part of the limit current -/

section Graph

open CurrentTraceMeasure CurrentRestriction ClosedProductCurrents GraphFibreIntegration

variable {q : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel (q + 1)) V]
  [IsComplexManifold (q + 1) V] [CompactSpace V] [MeasurableSpace V] [BorelSpace V]
  {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] {μ : V → X}

/-- **The mass of the graph current** is `∫_V (ω_V + μ^*ω_X)ⁿ`. -/
theorem mass_graphCurrent_eq (hμ : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ μ)
    (wV : KahlerBackground (q + 1) V) (wX : KahlerBackground (q + 1) X) :
    mass (prodKahlerBackground wV wX) (GraphSupport.graphCurrent (X := X) wV hμ) =
      slotIntegral wV (fun _ => wV.form + ClosedRealOneOneForm.pullback hμ wX.form) := by
  have h := mass_graphCurrent hμ wV wX
  rw [GraphSupport.graphCurrent, h, integrationCurrent_apply, slotIntegral]
  exact integral_congr_ae (Eventually.of_forall fun x =>
    topRatio_formPow_eq_slotForm' wV (graphKahler hμ wV wX).form x)

/-- **The graph part is bounded below by the mass on the graph** (`DiagonalLowerBound` for a
graph): for a closed positive current `Θ` of bidimension `(n, n)` on `V × X` with
`δ ≤ σ_Θ(Γ_μ)`, there is `c ≥ max(0, δ / mass[Γ_μ])` with `Θ - c [Γ_μ]` positive. -/
theorem exists_isPositive_sub_smul_graphCurrent_of_le [ConnectedSpace V]
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ μ)
    (wV : KahlerBackground (q + 1) V) (wX : KahlerBackground (q + 1) X)
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (V × X) (q + 1)} (hΘ : IsPositive Θ)
    (hΘc : IsClosedCurrent Θ) {δ : ℝ}
    (hδ : δ ≤ (traceMeasure (prodKahlerBackground wV wX) Θ hΘ).real {p : V × X | μ p.1 = p.2}) :
    ∃ c : ℝ, 0 ≤ c ∧
      δ / mass (prodKahlerBackground wV wX) (GraphSupport.graphCurrent (X := X) wV hμ) ≤ c ∧
      IsPositive (Θ - c • GraphSupport.graphCurrent (X := X) wV hμ) := by
  obtain ⟨c, hc0, hres, hpos⟩ :=
    GraphSupport.exists_restrictCurrent_graph_eq_smul hμ wV (prodKahlerBackground wV wX) hΘ hΘc
  refine ⟨c, hc0, ?_, hpos⟩
  have hmass := congrArg (mass (prodKahlerBackground wV wX)) hres
  rw [mass_restrictCurrent, mass_smul] at hmass
  set m := mass (prodKahlerBackground wV wX) (GraphSupport.graphCurrent (X := X) wV hμ) with hm
  have hm0 : 0 ≤ m := by
    rw [hm, mass_graphCurrent_eq hμ wV wX]
    exact slotIntegral_nonneg wV fun _ =>
      (KahlerBackground.isSemipositive (graphKahler hμ wV wX))
  rcases hm0.eq_or_lt with hm0' | hmpos
  · rw [← hm0', div_zero]
    exact hc0
  · rw [div_le_iff₀ hmpos]
    exact hδ.trans hmass.le

end Graph

/-! ### Yau's theorem in the classes `p₁^*a + p₂^*ω_X` on `V × X` -/

section Yau

variable {q : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel (q + 1)) V]
  [IsComplexManifold (q + 1) V] [CompactSpace V] [MeasurableSpace V] [BorelSpace V]
  {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

open scoped Manifold in
/-- Pull-back of closed forms is additive. -/
theorem pullback_add {k n : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
    [IsComplexManifold k Z] {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {f : Z → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a c : ClosedRealOneOneForm n M) :
    ClosedRealOneOneForm.pullback hf (a + c) =
      ClosedRealOneOneForm.pullback hf a + ClosedRealOneOneForm.pullback hf c := by
  apply ClosedRealOneOneForm.ext
  intro e z
  ext v
  rfl

/-- **Yau's theorem on `V × X`** for the class of `p₁^*a + p₂^*ω_X`, when `a + ddᶜh` is Kähler:
for every Kähler form `ω'` on `V × X` there are a chart-smooth `g` and `c > 0` with
`p₁^*a + p₂^*ω_X + ddᶜg` Kähler and `(p₁^*a + p₂^*ω_X + ddᶜg)^{2n} = c ω'^{2n}`.  From the TEMPORARY
named input through (Y-bou02) for the Kähler form `p₁^*(a + ddᶜh) + p₂^*ω_X`, `g = h ∘ p₁ + φ`. -/
theorem exists_yau_prodForm [ConnectedSpace V] [ConnectedSpace X]
    (wX : KahlerBackground (q + 1) X) (a : ClosedRealOneOneForm (q + 1) V) {h : V → ℝ}
    (hh : ChartSmooth (n := q + 1) h) (haK : (a + ddcClosedForm h hh).val.IsKahler)
    (ω' : KahlerBackground ((q + 1) + (q + 1)) (V × X)) :
    ∃ (g : V × X → ℝ) (hg : ChartSmooth (n := (q + 1) + (q + 1)) g) (c : ℝ), 0 < c ∧
      (prodForm a wX.form + ddcClosedForm g hg).val.IsKahler ∧
      ∀ (e : ComplexChart ((q + 1) + (q + 1)) (V × X)) (z : ComplexModel ((q + 1) + (q + 1))),
        z ∈ e.val.target →
          actualTopPowerDensity ((prodForm a wX.form + ddcClosedForm g hg).val.coeff e z) =
            c * actualTopPowerDensity (ω'.form.val.coeff e z) := by
  set A : KahlerBackground ((q + 1) + (q + 1)) (V × X) :=
    prodKahlerBackground ⟨_, haK⟩ wX with hAdef
  obtain ⟨φ, hφ, hK, hMA⟩ := YauTheorem.exists_kahler_mongeAmpere_eq_smul (by omega) A ω'
  have hh1 : ChartSmooth (n := (q + 1) + (q + 1)) (fun p : V × X => h p.1) :=
    chartSmooth_comp contMDiff_fst hh
  have hg : ChartSmooth (n := (q + 1) + (q + 1)) (fun p : V × X => h p.1 + φ p) :=
    fun e => (hh1 e).add (hφ e)
  have key : ∀ (e : ComplexChart ((q + 1) + (q + 1)) (V × X))
      (z : ComplexModel ((q + 1) + (q + 1))), z ∈ e.val.target →
        (prodForm a wX.form + ddcClosedForm _ hg).val.coeff e z =
          (A.form + ddcClosedForm φ hφ).val.coeff e z := by
    intro e z hz
    have hd1 :=
      SubmanifoldRestrictionPositivity.pullback_ddcClosedForm_coeff contMDiff_fst hh e hz
    have e1 : (ddcClosedForm (fun p : V × X => h p.1 + φ p) hg).val.coeff e z =
        (ddcClosedForm (fun p : V × X => h p.1) hh1).val.coeff e z +
          (ddcClosedForm φ hφ).val.coeff e z :=
      YauTheorem.ddcClosedForm_coeff_add hh1 hφ hg e hz
    have hA : A.form = prodForm (a + ddcClosedForm h hh) wX.form := by
      rw [hAdef, prodKahlerBackground_form]
    rw [hA]
    simp only [ClosedRealOneOneForm.coeff_add, e1, prodForm, pullback_add,
      ClosedRealOneOneForm.pullback_val, hd1]
    abel
  refine ⟨fun p => h p.1 + φ p, hg, (kahlerVolume A).real univ / (kahlerVolume ω').real univ,
    YauTheorem.kahlerVolume_div_pos (by omega) A ω', ?_, fun e z hz => ?_⟩
  · refine ⟨fun e z hz => ?_, (prodForm a wX.form + ddcClosedForm _ hg).property.1⟩
    rw [key e z hz]
    exact hK.1 e z hz
  · rw [key e z hz]
    exact hMA e z hz

/-- **The perturbed nef class is Kähler**: if `b` is nef with respect to `ω'` and `ω_V - ρ ω'` is
semipositive (`ρ > 0`), then for every `ε > 0` some `b + ε ω_V + ddᶜh` is Kähler. -/
theorem exists_isKahler_add_smul_of_nef {ω' wV : KahlerBackground (q + 1) V}
    {b : ClosedRealOneOneForm (q + 1) V} (hnef : NefWithRespectTo ω' b) {ρ : ℝ} (hρ : 0 < ρ)
    (hwV : (wV.form - ρ • ω'.form).val.IsSemipositive) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : V → ℝ) (hh : ChartSmooth (n := q + 1) h),
      (b + ε • wV.form + ddcClosedForm h hh).val.IsKahler := by
  obtain ⟨h, hh, hsemi⟩ := exists_isSemipositive_of_nef hnef (half_pos (mul_pos hε hρ))
  refine ⟨h, hh, ?_⟩
  have hs : (b + (ε * ρ / 2) • ω'.form + ddcClosedForm h hh +
      ε • (wV.form - ρ • ω'.form)).val.IsSemipositive := by
    have h2 := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive
      ((LocalPotentials.thetaPlurisubharmonic_zero_iff _).mpr hsemi)
      (b := ε • (wV.form - ρ • ω'.form)) (fun e z hz v => by
        have := hwV e z hz v
        simp only [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul]
        exact mul_nonneg hε.le this)
    exact (LocalPotentials.thetaPlurisubharmonic_zero_iff _).mp h2
  have hK := isKahler_add_smul_of_isSemipositive ω' hs (half_pos (mul_pos hε hρ))
  have heq : b + (ε * ρ / 2) • ω'.form + ddcClosedForm h hh + ε • (wV.form - ρ • ω'.form) +
      (ε * ρ / 2) • ω'.form = b + ε • wV.form + ddcClosedForm h hh := by
    module
  rwa [heq] at hK

end Yau

/-! ### The concentration pulled back along `μ × id` -/

section Concentration

open ProductMapMixedMeasure ModificationMassInvariance SubmanifoldMassConcentration

variable {q : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (q + 1)) Y]
  [IsComplexManifold (q + 1) Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] {μ : Y → X}

/-- `ν = μ × id` is holomorphic. -/
theorem contMDiff_prodMap_id
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ μ) :
    ContMDiff 𝓘(ℂ, ComplexModel ((q + 1) + (q + 1))) 𝓘(ℂ, ComplexModel ((q + 1) + (q + 1))) ∞
      (Prod.map μ (id : X → X)) :=
  contMDiff_prodMap hμ (contMDiff_id (I := 𝓘(ℂ, ComplexModel (q + 1))) (n := ∞))

/-- `(μ × id)^*(p₁^*a + p₂^*c) = p₁^*(μ^*a) + p₂^*c` geometrically. -/
theorem pullback_prodForm_geometricallyEq
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ μ)
    (a c : ClosedRealOneOneForm (q + 1) X) :
    (ClosedRealOneOneForm.pullback (contMDiff_prodMap_id hμ) (prodForm a c)).val.GeometricallyEq
      (prodForm (ClosedRealOneOneForm.pullback hμ a) c).val := by
  intro e z hz
  have h1 : (SmoothRealForm.pullback (contMDiff_prodMap_id hμ)
      (SmoothRealForm.pullback (contMDiff_fst (X := X) (Y := X)) a.val)).coeff e z =
      (SmoothRealForm.pullback (contMDiff_fst (X := Y) (Y := X))
        (SmoothRealForm.pullback hμ a.val)).coeff e z := by
    rw [← DiagonalFibreIntegration.pullback_comp_geometricallyEq contMDiff_fst
      (contMDiff_prodMap_id hμ) a.val e hz,
      ← DiagonalFibreIntegration.pullback_comp_geometricallyEq hμ contMDiff_fst a.val e hz]
  have h2 : (SmoothRealForm.pullback (contMDiff_prodMap_id hμ)
      (SmoothRealForm.pullback (contMDiff_snd (X := X) (Y := X)) c.val)).coeff e z =
      (SmoothRealForm.pullback (contMDiff_snd (X := Y) (Y := X)) c.val).coeff e z := by
    rw [← DiagonalFibreIntegration.pullback_comp_geometricallyEq contMDiff_snd
      (contMDiff_prodMap_id hμ) c.val e hz]
  simp only [prodForm, pullback_add, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.pullback_val] at h1 h2 ⊢
  rw [h1, h2]

/-- The difference of two product forms with the same second factor. -/
theorem prodForm_sub_coeff (a a' : ClosedRealOneOneForm (q + 1) Y)
    (c : ClosedRealOneOneForm (q + 1) X) (e : ComplexChart ((q + 1) + (q + 1)) (Y × X))
    (z : ComplexModel ((q + 1) + (q + 1))) :
    (prodForm a c).val.coeff e z =
      (prodForm a' c).val.coeff e z +
        (ClosedRealOneOneForm.pullback contMDiff_fst (a - a')).val.coeff e z := by
  simp only [prodForm, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.pullback_val]
  have : (SmoothRealForm.pullback (contMDiff_fst (X := Y) (Y := X)) (a - a').val).coeff e z =
      (SmoothRealForm.pullback (contMDiff_fst (X := Y) (Y := X)) a.val).coeff e z -
        (SmoothRealForm.pullback (contMDiff_fst (X := Y) (Y := X)) a'.val).coeff e z := by
    have h := congrArg (fun F : ClosedRealOneOneForm ((q + 1) + (q + 1)) (Y × X) => F.val.coeff e z)
      (pullback_add (contMDiff_fst (X := Y) (Y := X)) (a - a') a')
    simp only [sub_add_cancel, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.pullback_val] at h
    rw [h]
    abel
  rw [this]
  abel

/-- **The pulled-back concentration form stays above half the background**: for `ν = μ × id`,
`W = p₁^*ω + p₂^*ω`, `W_V = p₁^*ω_V + p₂^*ω` with `ω_V ≥ μ^*ω`, `(1/2) W + ddᶜf ≥ 0` gives
`(1/2) W_V + ddᶜ(f ∘ ν) ≥ 0`. -/
theorem isSemipositive_half_add_ddc_comp
    (hμ : ContMDiff 𝓘(ℂ, ComplexModel (q + 1)) 𝓘(ℂ, ComplexModel (q + 1)) ∞ μ)
    (w : KahlerBackground (q + 1) X) (wV : KahlerBackground (q + 1) Y)
    (hwV : (wV.form - ClosedRealOneOneForm.pullback hμ w.form).val.IsSemipositive)
    {f : X × X → ℝ} (hf : ChartSmooth (n := (q + 1) + (q + 1)) f)
    (hhalf : ((1 / 2 : ℝ) • (prodKahlerBackground w w).form + ddcClosedForm f hf).val.IsSemipositive) :
    ((1 / 2 : ℝ) • (prodKahlerBackground wV w).form +
      ddcClosedForm (fun p => f (Prod.map μ (id : X → X) p))
        (chartSmooth_comp (contMDiff_prodMap_id hμ) hf)).val.IsSemipositive := by
  intro e z hz v
  have h1 := ClosedRealOneOneForm.pullback_isSemipositive (contMDiff_prodMap_id hμ) hhalf e z hz v
  have h2 := ClosedRealOneOneForm.pullback_isSemipositive (contMDiff_fst (X := Y) (Y := X)) hwV
    e z hz v
  have hd := SubmanifoldRestrictionPositivity.pullback_ddcClosedForm_coeff
    (contMDiff_prodMap_id hμ) hf e hz
  have hP := pullback_prodForm_geometricallyEq hμ w.form w.form e hz
  have hS := prodForm_sub_coeff wV.form (ClosedRealOneOneForm.pullback hμ w.form) w.form e z
  rw [prodKahlerBackground_form] at h1 ⊢
  simp only [pullback_add, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.pullback_val] at h1 h2 ⊢
  have hPs : (SmoothRealForm.pullback (contMDiff_prodMap_id hμ)
      ((1 / 2 : ℝ) • prodForm w.form w.form).val).coeff e z =
      (1 / 2 : ℝ) • (prodForm (ClosedRealOneOneForm.pullback hμ w.form) w.form).val.coeff e z := by
    rw [← hP]
    rfl
  rw [hPs, hd] at h1
  rw [hS]
  simp only [ClosedRealOneOneForm.pullback_val, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1 h2 ⊢
  nlinarith

/-- The slots of the concentration forms are semipositive. -/
theorem isSemipositive_concentrationSlot {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] (W : KahlerBackground N M)
    {f : M → ℝ} (hf : ChartSmooth (n := N) f)
    (hhalf : ((1 / 2 : ℝ) • W.form + ddcClosedForm f hf).val.IsSemipositive) (p : ℕ) (i : Fin N) :
    (concentrationSlot W f hf p i).val.IsSemipositive := by
  simp only [concentrationSlot]
  split_ifs
  · have h := isKahler_add_smul_of_isSemipositive W hhalf (t := 1 / 2) (by norm_num)
    have heq : (1 / 2 : ℝ) • W.form + ddcClosedForm f hf + (1 / 2 : ℝ) • W.form =
        W.form + ddcClosedForm f hf := by
      module
    rw [heq] at h
    exact KahlerBackground.isSemipositive ⟨_, h⟩
  · exact W.isSemipositive

/-- **The pulled-back concentration keeps its mass** (step U1(d)): for a blowup sequence `μ`,
`ν = μ × id`, `ω_V ≥ μ^*ω` and `(1/2) W + ddᶜf ≥ 0` on `X × X`, the mixed measure of the
concentration slots `(W + ddᶜf)ᵖ ∧ Wⁿ⁻ᵖ` of any set `S` is at most that of the slots
`(W_V + ddᶜ(f ∘ ν))ᵖ ∧ W_Vⁿ⁻ᵖ` of `ν⁻¹ S`. -/
theorem le_globalMixedMeasure_concentrationSlot_comp (hμs : IsBlowupSequence (q + 1) X Y μ)
    (w : KahlerBackground (q + 1) X) (wV : KahlerBackground (q + 1) Y)
    (hwV : (wV.form - ClosedRealOneOneForm.pullback hμs.contMDiff w.form).val.IsSemipositive)
    {f : X × X → ℝ} (hf : ChartSmooth (n := (q + 1) + (q + 1)) f)
    (hhalf : ((1 / 2 : ℝ) • (prodKahlerBackground w w).form + ddcClosedForm f hf).val.IsSemipositive)
    (p : ℕ) (S : Set (X × X))
    (h₁ : ∀ i, ThetaPlurisubharmonic
      (concentrationSlot (prodKahlerBackground w w) f hf p i).val (fun _ => 0))
    (h₂ : ∀ i, ThetaPlurisubharmonic (concentrationSlot (prodKahlerBackground wV w)
      (fun z => f (Prod.map μ (id : X → X) z))
      (chartSmooth_comp (contMDiff_prodMap_id hμs.contMDiff) hf) p i).val (fun _ => 0)) :
    globalMixedMeasure (concentrationSlot (prodKahlerBackground w w) f hf p) (fun _ _ => 0) h₁ S ≤
      globalMixedMeasure (concentrationSlot (prodKahlerBackground wV w)
        (fun z => f (Prod.map μ (id : X → X) z))
        (chartSmooth_comp (contMDiff_prodMap_id hμs.contMDiff) hf) p) (fun _ _ => 0) h₂
        (Prod.map μ (id : X → X) ⁻¹' S) := by
  classical
  set hμ := hμs.contMDiff with hμdef
  set ν := Prod.map μ (id : X → X) with hνdef
  set hν := contMDiff_prodMap_id (X := X) hμ with hνdef'
  set θ := concentrationSlot (prodKahlerBackground w w) f hf p with hθdef
  have hθs : ∀ i, (θ i).val.IsSemipositive :=
    isSemipositive_concentrationSlot (prodKahlerBackground w w) hf hhalf p
  set θν := pullbackTuple hν θ with hθνdef
  have hθνs : ∀ i, (θν i).val.IsSemipositive := fun i =>
    ClosedRealOneOneForm.pullback_isSemipositive hν (hθs i)
  have hθν : ∀ i, ThetaPlurisubharmonic (θν i).val (fun _ => 0) := fun i =>
    thetaPlurisubharmonic_zero_of_isSemipositive (hθνs i)
  -- step 1: pull back along `ν`
  have step1 := le_globalMixedMeasure_preimage_prodMap_of_isBlowupSequence (W := X) (m := q + 1)
    hμs θ hθs h₁ hθν S
  -- step 2: the slots grow by `p₁^*(ω_V - μ^*ω) ≥ 0`
  set γ : ClosedRealOneOneForm ((q + 1) + (q + 1)) (Y × X) :=
    ClosedRealOneOneForm.pullback contMDiff_fst (wV.form - ClosedRealOneOneForm.pullback hμ w.form)
    with hγdef
  have hγ : γ.val.IsSemipositive := ClosedRealOneOneForm.pullback_isSemipositive contMDiff_fst hwV
  set θ'' : Fin ((q + 1) + (q + 1)) → ClosedRealOneOneForm ((q + 1) + (q + 1)) (Y × X) :=
    fun i => θν i + (1 : ℝ) • γ with hθ''def
  have hθ'' : ∀ i, ThetaPlurisubharmonic (θ'' i).val (fun _ => 0) := fun i =>
    thetaPlurisubharmonic_zero_of_isSemipositive (fun e z hz v => by
      have h1 := hθνs i e z hz v
      have h2 := hγ e z hz v
      simp only [hθ''def, one_smul, ClosedRealOneOneForm.coeff_add,
        ContinuousAlternatingMap.add_apply]
      linarith)
  have step2 : globalMixedMeasure θν (fun _ _ => 0) hθν ≤ globalMixedMeasure θ'' (fun _ _ => 0) hθ'' :=
    NefBoundedMixedMass.globalMixedMeasure_le_of_add_smul_on Finset.univ hγ one_pos
      (fun i => by simp [hθ''def]) hθν
      (fun i _ => (LocalPotentials.isThetaPshPotential_zero_iff _).mpr (hθνs i)) hθ''
  -- step 3: `θ''` is geometrically the concentration slot family on `Y × X`
  have hgeom : ∀ i, (θ'' i).val.GeometricallyEq (concentrationSlot (prodKahlerBackground wV w)
      (fun z => f (ν z)) (chartSmooth_comp hν hf) p i).val := by
    intro i e z hz
    have hP := pullback_prodForm_geometricallyEq hμ w.form w.form e hz
    have hS := prodForm_sub_coeff wV.form (ClosedRealOneOneForm.pullback hμ w.form) w.form e z
    have hd := SubmanifoldRestrictionPositivity.pullback_ddcClosedForm_coeff hν hf e hz
    simp only [hθ''def, hθνdef, hθdef, concentrationSlot, pullbackTuple]
    split_ifs
    · simp only [one_smul, pullback_add, ClosedRealOneOneForm.coeff_add,
        ClosedRealOneOneForm.pullback_val, prodKahlerBackground_form] at hP hd ⊢
      rw [hP, hd, hS, hγdef, ClosedRealOneOneForm.pullback_val]
      abel
    · simp only [one_smul, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.pullback_val,
        prodKahlerBackground_form] at hP ⊢
      rw [hP, hS, hγdef, ClosedRealOneOneForm.pullback_val]
  rw [globalMixedMeasure_congr_geometricallyEq hgeom hθ'' h₂] at step2
  exact step1.trans (step2 _)

end Concentration

end SGPT.Foundations.Analysis.Pending.UniformNefCoreSupport
