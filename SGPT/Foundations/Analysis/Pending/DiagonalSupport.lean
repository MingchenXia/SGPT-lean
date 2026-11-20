import SGPT.Foundations.Analysis.Pending.DiagonalTangentialReduction
import SGPT.Foundations.Analysis.Pending.ClosedTopCurrents

set_option autoImplicit false

/-!
# The support theorem on the diagonal

Let `X` be a compact connected complex manifold of dimension `n = q + 1` with a Kähler form `ω`,
and `Θ` a closed positive current of bidimension `(n, n)` on `X × X` carried by the diagonal `Δ`
(`σ_Θ(X × X \ Δ) = 0`).  Then

`Θ = λ [Δ]` with `λ ≥ 0`, `[Δ] = diag_*[X]` (`DiagonalFibreIntegration.diagonalCurrent ω`)

(`eq_smul_diagonalCurrent`; `bou:diagonal-support`, TN.4 step B4.4; `demailly-cadg:III.2.10`,
`III.2.13`, `III.2.14` for the smooth connected submanifold `Δ`).  For an arbitrary closed positive
`Θ` on `X × X`, `𝟙_Δ Θ` is closed (Skoda--El Mir, B4.3) and carried by `Δ`, so
`𝟙_Δ Θ = λ [Δ]` and `Θ - λ [Δ] = 𝟙_{X × X \ Δ} Θ` is positive
(`exists_restrictCurrent_diagonal_eq_smul`), the form consumed by
`DiagonalFibreIntegration.isPositive_fibrePushforward_sub`.

*Proof.*  The push-forward `μ = p₁_* Θ` is a positive current of top bidimension on `X`, closed
because pullback commutes with `Π₁₁ d(f dg)` (`IsClosedCurrent.pushforward`); hence
`μ = λ [X]` (`ClosedTopCurrents.eq_smul_integrationCurrent_of_isClosedCurrent`).  By the tangential
reduction (`DiagonalTangentialReduction.apply_pullback_diagProjMap_eq`)
`Θ φ = Θ(p₁^* diag^* φ) = μ(diag^* φ) = λ [X](diag^* φ) = λ [Δ] φ`.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.DiagonalSupport

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  StronglyPositiveForms ProductTestForms PositiveProductCurrents ClosedProductCurrents
  CurrentTraceMeasure CurrentRestriction TopDegreeDensity SmoothCurrentClosedness

/-! ### Push-forwards of closed currents are closed -/

section Pushforward

variable {k N : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] {f : V → M}

theorem wedgeProd_compCLM (L : ComplexModel k →L[ℝ] ComplexModel N) :
    ∀ (q : ℕ) (α : Fin q → RealForm N 2),
      (wedgeProd q α).compContinuousLinearMap L =
        wedgeProd q (fun i => (α i).compContinuousLinearMap L)
  | 0, _ => by ext v; rfl
  | q + 1, α => by
    rw [wedgeProd_succ, wedgeProd_succ, coordinateWedge_compContinuousLinearMap,
      wedgeProd_compCLM L q]

theorem comp_two' (L : ComplexModel k →L[ℝ] ComplexModel N) (u v : ComplexModel k) :
    (⇑L ∘ ![u, v]) = ![L u, L v] := by
  funext i
  fin_cases i <;> rfl

/-- `Π₁₁` commutes with pullback along a `ℂ`-linear map. -/
theorem pi11_compCLM (A : RealForm N 2) (L : ComplexModel k →L[ℝ] ComplexModel N)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    pi11 (A.compContinuousLinearMap L) = (pi11 A).compContinuousLinearMap L := by
  ext v
  rw [eq_vec_two v]
  simp only [pi11_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_two', hL]

/-- **Pullback of `d(F dG)`**: `f^* d(F dG) = d((F ∘ f) d(G ∘ f))` at every chart point. -/
theorem pullback_exactPair_coeff (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ f)
    {F G : M → ℝ} (hF : ChartSmooth (n := N) F) (hG : ChartSmooth (n := N) G)
    (e : ComplexChart k V) {z : ComplexModel k} (hz : z ∈ e.val.target) :
    (SmoothRealForm.pullback hf (exactPair F G hF hG)).coeff e z =
      (exactPair (fun x => F (f x)) (fun x => G (f x)) (chartSmooth_comp hf hF)
        (chartSmooth_comp hf hG)).coeff e z := by
  set d := complexChartAt (n := N) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  set Ψ := coordinateMap f e d with hΨdef
  have hΨ : DifferentiableAt ℝ Ψ z :=
    (coordinateMap_contDiffAt_real hf e d hzd).differentiableAt (by simp)
  have hw : Ψ z ∈ d.val.target := coordinateMap_mem_target hzd
  have hdiff : ∀ H : M → ℝ, ChartSmooth (n := N) H →
      DifferentiableAt ℝ (fun y => H (d.val.symm y)) (Ψ z) := fun H hH =>
    ((hH d).contDiffAt (d.val.open_target.mem_nhds hw)).differentiableAt (by simp)
  have hchain : ∀ H : M → ℝ, ChartSmooth (n := N) H →
      fderiv ℝ (fun y => H (f (e.val.symm y))) z =
        (fderiv ℝ (fun y => H (d.val.symm y)) (Ψ z)).comp (fderiv ℝ Ψ z) := by
    intro H hH
    have heq : (fun y => H (f (e.val.symm y))) =ᶠ[𝓝 z] (fun y => H (d.val.symm y)) ∘ Ψ := by
      filter_upwards [(coordinateDomain_isOpen hf e d).mem_nhds hzd] with y hy
      change H (f (e.val.symm y)) = H (d.val.symm (d.val (f (e.val.symm y))))
      rw [d.val.left_inv hy.2]
    rw [heq.fderiv_eq]
    exact fderiv_comp z (hdiff H hH) hΨ
  ext v
  rw [eq_vec_two v, SmoothRealForm.pullback_coeff hf _ e d hzd,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_two',
    exactPair_coeff_apply F G hF hG d hw,
    exactPair_coeff_apply _ _ (chartSmooth_comp hf hF) (chartSmooth_comp hf hG) e hz,
    hchain F hF, hchain G hG]
  rfl

/-- **Pullback of a closed test form** is the closed test form of the pulled-back data. -/
theorem pullback_closedTestForm_coeff
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ f)
    {F G : M → ℝ} (hF : ChartSmooth (n := N) F) (hG : ChartSmooth (n := N) G) (q : ℕ)
    (β : Fin q → ClosedRealOneOneForm N M) (e : ComplexChart k V) {z : ComplexModel k}
    (hz : z ∈ e.val.target) :
    (SmoothRealForm.pullback hf ((closedTestForm F G hF hG q β : testSpace N M (q + 1)) :
        SmoothRealForm N M (2 * (q + 1)))).coeff e z =
      ((closedTestForm (fun x => F (f x)) (fun x => G (f x)) (chartSmooth_comp hf hF)
        (chartSmooth_comp hf hG) q (fun j => ClosedRealOneOneForm.pullback hf (β j)) :
          testSpace k V (q + 1)) : SmoothRealForm k V (2 * (q + 1))).coeff e z := by
  set d := complexChartAt (n := N) (f (e.val.symm z))
  have hzd : z ∈ coordinateDomain f e d := ⟨hz, mem_complexChartAt_source _⟩
  have hL : ∀ v, fderiv ℝ (coordinateMap f e d) z (Complex.I • v) =
      Complex.I • fderiv ℝ (coordinateMap f e d) z v :=
    coordinateMap_fderiv_map_smul_complex hf e d hzd Complex.I
  rw [SmoothRealForm.pullback_coeff hf _ e d hzd, closedTestForm_coeff, closedTestForm_coeff,
    wedgeProd_compCLM]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    rw [← pi11_compCLM _ _ hL, ← SmoothRealForm.pullback_coeff hf _ e d hzd,
      pullback_exactPair_coeff hf hF hG e hz]
  · simp only [Fin.cons_succ, ClosedRealOneOneForm.pullback_val]
    rw [SmoothRealForm.pullback_coeff hf _ e d hzd]

/-- **The push-forward of a closed positive current along a holomorphic map is closed.** -/
theorem IsClosedCurrent.pushforward (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ f) :
    ∀ {q : ℕ} {T : ProductCurrent k V q}, IsPositive T → IsClosedCurrent T →
      IsClosedCurrent (PositiveProductCurrents.pushforward hf T)
  | 0, _, _, _ => trivial
  | q + 1, T, hT, hTc => fun F G hF hG β => by
    rw [pushforward_apply]
    rw [hT.apply_eq_of_coeff_eqOn (ψ := closedTestForm (fun x => F (f x)) (fun x => G (f x))
      (chartSmooth_comp hf hF) (chartSmooth_comp hf hG) q
      (fun j => ClosedRealOneOneForm.pullback hf (β j))) fun e z hz =>
        pullback_closedTestForm_coeff hf hF hG q β e hz]
    exact hTc _ _ _ _ _

end Pushforward

/-! ### The support theorem -/

section Support

open ProductComplexManifold DiagonalFibreIntegration DiagonalTangentialReduction
  ClosedTopCurrents IntegrationCurrent
open scoped ProductComplexManifold

variable {q : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The support theorem on the diagonal** (`bou:diagonal-support`): a closed positive current of
bidimension `(n, n)` on `X × X` carried by the diagonal is a nonnegative multiple of the current of
integration over the diagonal. -/
theorem eq_smul_diagonalCurrent [ConnectedSpace X] (w : KahlerBackground (q + 1) X)
    (w' : KahlerBackground ((q + 1) + (q + 1)) (X × X))
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (X × X) (q + 1)} (hΘ : IsPositive Θ)
    (hΘc : IsClosedCurrent Θ) (hcar : traceMeasure w' Θ hΘ (Set.diagonal X)ᶜ = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ Θ = c • diagonalCurrent w := by
  set μ := PositiveProductCurrents.pushforward contMDiff_fst Θ with hμ
  have hμp : IsPositive μ := hΘ.pushforward contMDiff_fst
  have hμc : IsClosedCurrent μ := IsClosedCurrent.pushforward contMDiff_fst hΘ hΘc
  obtain ⟨c, hc0, hμeq⟩ := eq_smul_integrationCurrent_of_isClosedCurrent w hμp hμc
  refine ⟨c, hc0, LinearMap.ext fun φ => ?_⟩
  rw [← apply_pullback_diagProjMap_eq w' hΘ hΘc hcar φ, LinearMap.smul_apply,
    diagonalCurrent_apply, ← LinearMap.smul_apply, ← hμeq, hμ, pushforward_apply]
  exact hΘ.apply_eq_of_coeff_eqOn fun e z hz =>
    pullback_comp_geometricallyEq contMDiff_diag contMDiff_fst _ e hz

/-- **The diagonal part of a closed positive current** (the form used by
`DiagonalFibreIntegration.isPositive_fibrePushforward_sub`): for every closed positive current `Θ`
of bidimension `(n, n)` on `X × X` there is `λ ≥ 0` with `𝟙_Δ Θ = λ [Δ]`, and then
`Θ - λ [Δ] = 𝟙_{X × X \ Δ} Θ` is positive. -/
theorem exists_restrictCurrent_diagonal_eq_smul [ConnectedSpace X] (w : KahlerBackground (q + 1) X)
    (w' : KahlerBackground ((q + 1) + (q + 1)) (X × X))
    {Θ : ProductCurrent ((q + 1) + (q + 1)) (X × X) (q + 1)} (hΘ : IsPositive Θ)
    (hΘc : IsClosedCurrent Θ) :
    ∃ c : ℝ, 0 ≤ c ∧ restrictCurrent w' Θ hΘ (Set.diagonal X) = c • diagonalCurrent w ∧
      IsPositive (Θ - c • diagonalCurrent w) := by
  have hΔm : MeasurableSet (Set.diagonal X) := isClosed_diagonal.measurableSet
  have hRp := isPositive_restrictCurrent w' Θ hΘ (Set.diagonal X)
  have hRc := (SkodaElMirSubmanifold.isClosedCurrent_restrictCurrent_diagonal w' hΘ hΘc).1
  have hcar : traceMeasure w' (restrictCurrent w' Θ hΘ (Set.diagonal X)) hRp
      (Set.diagonal X)ᶜ = 0 := by
    rw [traceMeasure_restrictCurrent w' Θ hΘ hΔm, Measure.restrict_apply hΔm.compl,
      compl_inter_self, measure_empty]
  obtain ⟨c, hc0, hceq⟩ := eq_smul_diagonalCurrent w w' hRp hRc hcar
  refine ⟨c, hc0, hceq, ?_⟩
  have hsplit := restrictCurrent_add_compl w' Θ hΘ hΔm
  have : Θ - c • diagonalCurrent w = restrictCurrent w' Θ hΘ (Set.diagonal X)ᶜ := by
    calc Θ - c • diagonalCurrent w =
        (restrictCurrent w' Θ hΘ (Set.diagonal X) + restrictCurrent w' Θ hΘ (Set.diagonal X)ᶜ) -
          restrictCurrent w' Θ hΘ (Set.diagonal X) := by rw [hsplit, hceq]
      _ = _ := add_sub_cancel_left _ _
  rw [this]
  exact isPositive_restrictCurrent w' Θ hΘ _

end Support

/-! ### Mass on a closed set in the limit -/

section MassLimit

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Mass on a closed set passes to weak limits along a shrinking family**: if positive currents
`Tᵢ → S` weakly with bounded masses and, for every `k`, eventually `σ_{Tᵢ}(F k) ≥ δ` for an antitone
family of closed sets `F k`, then `σ_S(⋂ₖ F k) ≥ δ` (closed-set upper semicontinuity,
`CurrentTraceMeasure.le_traceMeasure_of_tendsto`, and continuity from above).  With `F k` closed
tubes shrinking to `Δ`, this is the lower bound `σ_Θ(Δ) ≥ δ` that fixes `λ` in
`exists_restrictCurrent_diagonal_eq_smul`. -/
theorem le_traceMeasure_iInter_of_tendsto (w : KahlerBackground N M) {q : ℕ} {ι : Type*}
    {l : Filter ι} [l.NeBot] {T : ι → ProductCurrent N M q} (hT : ∀ i, IsPositive (T i))
    {S : ProductCurrent N M q} (hS : IsPositive S) {m : ℝ}
    (hm : ∀ᶠ i in l, mass w (T i) ≤ m) (hlim : ∀ φ, Tendsto (fun i => T i φ) l (𝓝 (S φ)))
    {F : ℕ → Set M} (hF : ∀ k, IsClosed (F k)) (hanti : Antitone F) {δ : ℝ}
    (hδ : ∀ k, ∀ᶠ i in l, δ ≤ (traceMeasure w (T i) (hT i)).real (F k)) :
    δ ≤ (traceMeasure w S hS).real (⋂ k, F k) := by
  have hk : ∀ k, δ ≤ (traceMeasure w S hS).real (F k) := fun k =>
    le_traceMeasure_of_tendsto w hT hS hm hlim (hF k) (hδ k)
  have htend := tendsto_measure_iInter_atTop (μ := traceMeasure w S hS)
    (fun k => (hF k).measurableSet.nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hreal : Tendsto (fun k => (traceMeasure w S hS).real (F k)) Filter.atTop
      (𝓝 ((traceMeasure w S hS).real (⋂ k, F k))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp htend
  exact ge_of_tendsto hreal (Eventually.of_forall hk)

end MassLimit

end SGPT.Foundations.Analysis.Pending.DiagonalSupport
