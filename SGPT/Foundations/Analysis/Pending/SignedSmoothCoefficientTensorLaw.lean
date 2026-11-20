import SGPT.Foundations.Analysis.Pending.LocalSmoothFormDensityGluing
import SGPT.Foundations.Analysis.Pending.ActualChartOverlapTestTransport
import SGPT.Foundations.Analysis.Pending.GlobalCurrents
import SGPT.Foundations.Analysis.Pending.CurrentPairing
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology

namespace SGPT.Foundations.Analysis.Pending.SignedSmoothCoefficientTensorLaw
open FirstPass FirstPass.HolomorphicMaps
open _root_.SGPT.Foundations.Analysis.LocalCurrents LelongPoincareDivisor

private def normalizedAlternation {n q : ℕ} :
    (ContinuousMultilinearMap ℝ (fun _ : Fin q => ComplexModel n) ℝ) →L[ℝ]
      (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :=
  (q.factorial : ℝ)⁻¹ • LinearMap.mkContinuous
    ({ toFun := ContinuousMultilinearMap.alternatization
       map_add' := fun a b => ContinuousMultilinearMap.alternatization.map_add a b
       map_smul' := by
         intro c a
         ext w
         simp only [ContinuousMultilinearMap.alternatization_apply_apply,
           smul_apply, ContinuousAlternatingMap.smul_apply,
           smul_eq_mul]
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro σ _
         rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h] } :
      (ContinuousMultilinearMap ℝ (fun _ : Fin q => ComplexModel n) ℝ) →ₗ[ℝ]
        (ComplexModel n [⋀^Fin q]→L[ℝ] ℝ))
    q.factorial (fun a => by
      change ‖∑ σ : Equiv.Perm (Fin q), Equiv.Perm.sign σ • a.domDomCongr σ‖ ≤ _
      refine (norm_sum_le _ _).trans_eq ?_
      have hterm (σ : Equiv.Perm (Fin q)) :
          ‖Equiv.Perm.sign σ • a.domDomCongr σ‖ = ‖a‖ := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul])

private theorem normalizedAlternation_eq {n q : ℕ}
    (γ : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :
    normalizedAlternation γ.toContinuousMultilinearMap = γ := by
  have h : ContinuousMultilinearMap.alternatization γ.toContinuousMultilinearMap =
      q.factorial • γ := by
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    simpa using AlternatingMap.coe_alternatization γ.toAlternatingMap
  ext w
  simp [normalizedAlternation, h, nsmul_eq_mul, Nat.factorial_ne_zero]


variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The genuine full variable-field pullback by the actual chart transition. -/
def chartPullbackField {r : ℕ} (e f : ComplexChart n M)
    (a : ComplexModel n → (ComplexModel n [⋀^Fin r]→L[ℝ] ℝ))
    (z : ComplexModel n) : ComplexModel n [⋀^Fin r]→L[ℝ] ℝ :=
  (a (chartTransition e f z)).compContinuousLinearMap (chartTransitionDerivative e f z)

/-- Smoothness is internal, with no pullback-field smoothness certificate. -/
theorem contDiffOn_chartPullbackField {r : ℕ} (e f : ComplexChart n M)
    {a : ComplexModel n → (ComplexModel n [⋀^Fin r]→L[ℝ] ℝ)}
    (ha : ContDiffOn ℝ ∞ a (chartTarget f)) :
    ContDiffOn ℝ ∞ (chartPullbackField e f a) (overlapSource e f) := by
  let F := chartTransition e f
  have hF : ContDiffOn ℝ ∞ F F.source :=
    fun z hz => (chartTransition_contDiffAt_real e f hz).contDiffWithinAt
  have hD : ContDiffOn ℝ ∞ (chartTransitionDerivative e f) F.source :=
    hF.fderiv_of_isOpen F.open_source (by simp)
  have hγ : ContDiffOn ℝ ∞ (fun z => a (F z)) F.source :=
    ha.comp hF (fun z hz => (F.map_source hz).1)
  let C : (ComplexModel n [⋀^Fin r]→L[ℝ] ℝ) →L[ℝ]
      (ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexModel n) ℝ) :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
  have hC : ContDiff ℝ ∞ C := C.contDiff
  have hm : ContDiffOn ℝ ∞
      (fun z => (a (F z)).toContinuousMultilinearMap) F.source :=
    hC.contDiffOn.comp hγ (fun _ _ => mem_univ _)
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexModel n →L[ℝ] ComplexModel n)
      ((ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexModel n) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexModel n) ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin r => ComplexModel n) (fun _ => ComplexModel n) ℝ
  have hA0 : ContDiff ℝ ∞ A := ContinuousMultilinearMap.contDiff
    (𝕜 := ℝ) (E := fun _ : Fin r => ComplexModel n →L[ℝ] ComplexModel n)
    (F := (ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexModel n) ℝ) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin r => ComplexModel n) ℝ) (n := ∞) A
  have hA : ContDiffOn ℝ ∞ (fun z =>
      A (fun _ => chartTransitionDerivative e f z) (a (F z)).toContinuousMultilinearMap)
      F.source :=
    (hA0.contDiffOn.comp (contDiffOn_pi.mpr fun _ => hD)
      (fun _ _ => mem_univ _)).clm_apply hm
  have hN := (normalizedAlternation (n := n) (q := r)).contDiff.contDiffOn.comp hA
    (fun _ _ => mem_univ _)
  convert hN using 1
  · funext z
    change (a (F z)).compContinuousLinearMap (chartTransitionDerivative e f z) =
      normalizedAlternation ((a (F z)).compContinuousLinearMap
        (chartTransitionDerivative e f z)).toContinuousMultilinearMap
    exact (normalizedAlternation_eq _).symm
  · rfl

variable [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]

private def fieldWedgeDensity
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} {Ω : Opens (ComplexModel n)}
    (a : ComplexModel n → (ComplexModel n [⋀^Fin k.val]→L[ℝ] ℝ))
    (η : TestForm Ω (Module.finrank ℝ (ComplexModel n) - k.val)) (x : ComplexModel n) : ℝ :=
  ∑ s : Equiv.Perm.ModSumCongr (Fin k.val)
      (Fin (Module.finrank ℝ (ComplexModel n) - k.val)),
    ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
      (a x (fun i => currentPairingBasis b k (s.out (Sum.inl i))) *
        η x (fun j => currentPairingBasis b k (s.out (Sum.inr j))))

private theorem regular_pairing_eq_integral
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} {Ω : Opens (ComplexModel n)}
    (a : ComplexModel n → (ComplexModel n [⋀^Fin k.val]→L[ℝ] ℝ))
    (ha : LocallyIntegrableOn a Ω b.addHaar)
    (η : TestForm Ω (Module.finrank ℝ (ComplexModel n) - k.val)) :
    toLocalCurrent b k (regularFormDistribution b.addHaar a ha) η =
      ∫ x, fieldWedgeDensity b a η x ∂b.addHaar := by
  change wedgePairing (currentPairingBasis b k) (regularFormDistribution b.addHaar a ha) η = _
  rw [wedgePairing_apply]
  simp only [Units.smul_def, zsmul_eq_mul]
  have hvec (s : Equiv.Perm.ModSumCongr (Fin k.val)
      (Fin (Module.finrank ℝ (ComplexModel n) - k.val))) :
      Integrable (fun x =>
        (testCoefficientCLM (fun j => currentPairingBasis b k (s.out (Sum.inr j))) η x) •
          a x) b.addHaar :=
    TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) ha
      (testCoefficientCLM (fun j => currentPairingBasis b k (s.out (Sum.inr j))) η)
  have hterm (s : Equiv.Perm.ModSumCongr (Fin k.val)
      (Fin (Module.finrank ℝ (ComplexModel n) - k.val))) :
      ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (regularFormDistribution b.addHaar a ha)
            (fun i => currentPairingBasis b k (s.out (Sum.inl i)))
            (testCoefficientCLM
              (fun j => currentPairingBasis b k (s.out (Sum.inr j))) η) =
        ∫ x, ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (a x (fun i => currentPairingBasis b k (s.out (Sum.inl i))) *
            η x (fun j => currentPairingBasis b k (s.out (Sum.inr j)))) ∂b.addHaar := by
    rw [regularFormDistribution_apply]
    change ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
        formEvaluationCLM (fun i => currentPairingBasis b k (s.out (Sum.inl i)))
          (∫ x, (testCoefficientCLM
              (fun j => currentPairingBasis b k (s.out (Sum.inr j))) η x) • a x ∂b.addHaar) = _
    rw [← (formEvaluationCLM
      (fun i => currentPairingBasis b k (s.out (Sum.inl i)))).integral_comp_comm (hvec s)]
    rw [← integral_const_mul]
    congr 1
    funext x
    simp [mul_comm]
  simp_rw [hterm]
  rw [← integral_finsetSum Finset.univ]
  · simp only [fieldWedgeDensity]
  · intro s _
    have hs := (formEvaluationCLM
      (fun i => currentPairingBasis b k (s.out (Sum.inl i)))).integrable_comp (hvec s)
    exact (hs.const_mul ((Equiv.Perm.sign s.out : ℤ) : ℝ)).congr
      (Filter.Eventually.of_forall fun x => by simp [mul_comm])
private def scalarWedge {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {r q : ℕ} (α : E [⋀^Fin r]→L[ℝ] ℝ) (β : E [⋀^Fin q]→L[ℝ] ℝ) :
    E [⋀^(Fin r ⊕ Fin q)]→ₗ[ℝ] ℝ :=
  (LinearMap.mul' ℝ ℝ).compAlternatingMap
    (α.toAlternatingMap.domCoprod β.toAlternatingMap)

/-- Evaluation of the scalar exterior product is the normalized shuffle sum,
including the endpoint degrees. -/
private theorem scalarWedge_apply {E : Type*} [TopologicalSpace E]
    [AddCommGroup E] [Module ℝ E]
    {r q : ℕ} (α : E [⋀^Fin r]→L[ℝ] ℝ) (β : E [⋀^Fin q]→L[ℝ] ℝ)
    (v : Fin r ⊕ Fin q → E) :
    scalarWedge α β v =
      ∑ s : Equiv.Perm.ModSumCongr (Fin r) (Fin q),
        ((Equiv.Perm.sign s.out : ℤ) : ℝ) *
          (α (fun i ↦ v (s.out (Sum.inl i))) *
            β (fun j ↦ v (s.out (Sum.inr j)))) := by
  rw [scalarWedge, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  conv_lhs => rw [← Quotient.out_eq s, AlternatingMap.domCoprod.summand_mk'']
  rcases Int.units_eq_one_or (Equiv.Perm.sign s.out) with hs | hs
  · rw [hs]
    simp [LinearMap.mul'_apply]
  · rw [hs]
    simp [LinearMap.mul'_apply]


omit [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
private theorem fieldWedgeDensity_eq_scalarWedge
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} {Ω : Opens (ComplexModel n)}
    (a : ComplexModel n → (ComplexModel n [⋀^Fin k.val]→L[ℝ] ℝ))
    (η : TestForm Ω (Module.finrank ℝ (ComplexModel n) - k.val)) (x : ComplexModel n) :
    fieldWedgeDensity b a η x = scalarWedge (a x) (η x) (currentPairingBasis b k) := by
  rw [scalarWedge_apply]
  rfl

omit [IsComplexManifold n M] [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
private theorem fieldWedgeDensity_pullback
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n}
    (a : ComplexModel n → (ComplexModel n [⋀^Fin k.val]→L[ℝ] ℝ))
    (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (θ : TestForm (overlapTarget e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (h : OverlapTestRelated e f η θ) (x : ComplexModel n)
    (hx : x ∈ (chartTransition e f).source) :
    fieldWedgeDensity b (chartPullbackField e f a) η x =
      (chartTransitionDerivative e f x).det * fieldWedgeDensity b a θ (chartTransition e f x) := by
  rw [fieldWedgeDensity_eq_scalarWedge, fieldWedgeDensity_eq_scalarWedge]
  let D := chartTransitionDerivative e f x
  let B := currentPairingBasis b k
  let W := scalarWedge (a (chartTransition e f x)) (θ (chartTransition e f x))
  have hpull (v : Fin k.val ⊕
      Fin (Module.finrank ℝ (ComplexModel n) - k.val) → ComplexModel n) :
      scalarWedge (chartPullbackField e f a x) (η x) v = W (D ∘ v) := by
    rw [scalarWedge_apply, scalarWedge_apply]
    apply Finset.sum_congr rfl
    intro s _
    rw [chartPullbackField, ContinuousAlternatingMap.compContinuousLinearMap_apply, h x hx]
    rfl
  rw [hpull B]
  have htop := congrArg
    (fun A : (ComplexModel n) [⋀^(Fin k.val ⊕
        Fin (Module.finrank ℝ (ComplexModel n) - k.val))]→ₗ[ℝ] ℝ ↦ A (D ∘ B))
    (W.eq_smul_basis_det B)
  have hdet : B.det (D ∘ B) = LinearMap.det D.toLinearMap := by
    change B.det (D.toLinearMap ∘ B) = LinearMap.det D.toLinearMap
    rw [B.det_comp, B.det_self, mul_one]
  calc
    W (D ∘ B) = ((W B) • B.det) (D ∘ B) := htop
    _ = W B * B.det (D ∘ B) := by simp
    _ = W B * LinearMap.det D.toLinearMap := by rw [hdet]
    _ = LinearMap.det D.toLinearMap * W B := mul_comm _ _

/-- Actual signed full regular pairings satisfy geometric chart pullback. -/
theorem regular_pairing_chart_pullback
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (e f : ComplexChart n M)
    (a : ComplexModel n → (ComplexModel n [⋀^Fin k.val]→L[ℝ] ℝ))
    (ha : ContDiffOn ℝ ∞ a (chartTarget f))
    (η : TestForm (overlapSource e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (θ : TestForm (overlapTarget e f) (Module.finrank ℝ (ComplexModel n) - k.val))
    (h : OverlapTestRelated e f η θ) :
    toLocalCurrent b k (regularFormDistribution b.addHaar (chartPullbackField e f a)
      ((contDiffOn_chartPullbackField e f ha).continuousOn.locallyIntegrableOn
        (overlapSource e f).isOpen.measurableSet)) η =
    toLocalCurrent b k (regularFormDistribution b.addHaar a
      ((ha.continuousOn.locallyIntegrableOn (chartTarget f).isOpen.measurableSet).mono_set
        (overlapTarget_le e f))) θ := by
  rw [regular_pairing_eq_integral, regular_pairing_eq_integral]
  let F := chartTransition e f
  let D := chartTransitionDerivative e f
  let gS := fun x => fieldWedgeDensity b (chartPullbackField e f a) η x
  let gT := fun x => fieldWedgeDensity b a θ x
  have hzeroS {x : ComplexModel n} (hx : x ∉ F.source) : gS x = 0 := by
    have hη : η x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (η.tsupport_subset ht))
    simp [gS, fieldWedgeDensity, hη]
  have hzeroT {x : ComplexModel n} (hx : x ∉ F.target) : gT x = 0 := by
    have hθ : θ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (θ.tsupport_subset ht))
    simp [gT, fieldWedgeDensity, hθ]
  have hfullS : (∫ x, gS x ∂b.addHaar) = ∫ x in F.source, gS x ∂b.addHaar := by
    rw [← integral_indicator F.open_source.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ F.source
    · simp [hx]
    · simp [hx, hzeroS hx]
  have hfullT : (∫ x, gT x ∂b.addHaar) = ∫ x in F.target, gT x ∂b.addHaar := by
    rw [← integral_indicator F.open_target.measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ F.target
    · simp [hx]
    · simp [hx, hzeroT hx]
  have hderiv (x : ComplexModel n) (hx : x ∈ F.source) : HasFDerivAt F (D x) x :=
    ((chartTransition_contDiffAt_real e f hx).differentiableAt (by simp)).hasFDerivAt
  have hchange := integral_target_eq_integral_abs_det_fderiv_smul b.addHaar hderiv gT
  have hsource : (∫ x in F.source, gS x ∂b.addHaar) =
      ∫ x in F.source, |(D x).det| • gT (F x) ∂b.addHaar := by
    apply setIntegral_congr_fun F.open_source.measurableSet
    intro x hx
    change gS x = |(D x).det| * gT (F x)
    rw [abs_of_nonneg (GlobalCurrents.chartTransitionDerivative_det_nonneg e f hx)]
    exact fieldWedgeDensity_pullback b a e f η θ h x hx
  calc
    (∫ x, gS x ∂b.addHaar) = ∫ x in F.source, gS x ∂b.addHaar := hfullS
    _ = ∫ x in F.source, |(D x).det| • gT (F x) ∂b.addHaar := hsource
    _ = ∫ x in F.target, gT x ∂b.addHaar := hchange.symm
    _ = ∫ x, gT x ∂b.addHaar := hfullT.symm

private theorem restrict_regularForm {r : ℕ} {Ω V : Opens (ComplexModel n)}
    (μ : Measure (ComplexModel n))
    {a : ComplexModel n → (ComplexModel n [⋀^Fin r]→L[ℝ] ℝ)}
    (ha : LocallyIntegrableOn a Ω μ) (hV : V ≤ Ω) :
    restrictForm (regularFormDistribution μ a ha) hV =
      regularFormDistribution μ a (ha.mono_set hV) := by
  ext v φ
  rw [restrictForm_apply, regularFormDistribution_apply, regularFormDistribution_apply]
  rw [testFunction_inclusion_coe hV φ]

private theorem restrictChart_eq_regular
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (T : GlobalCurrent n M k) (e : ComplexChart n M)
    {Ω : Opens (ComplexModel n)} (hΩ : Ω ≤ chartTarget e)
    {a : ComplexModel n → (ComplexModel n [⋀^Fin k.val]→L[ℝ] ℝ)}
    (ha : LocallyIntegrableOn a (chartTarget e) b.addHaar)
    (heq : T.coefficients b e = regularFormDistribution b.addHaar a ha) :
    T.restrictChart e hΩ = toLocalCurrent b k
      (regularFormDistribution b.addHaar a (ha.mono_set hΩ)) := by
  have hh : fromLocalCurrent b k (T.restrictChart e hΩ) =
      restrictForm (T.coefficients b e) hΩ := by
    ext v φ
    exact T.coefficients_restrictChart b e hΩ v φ
  rw [heq, restrict_regularForm] at hh
  calc
    T.restrictChart e hΩ = toLocalCurrent b k (fromLocalCurrent b k (T.restrictChart e hΩ)) :=
      (CurrentPairing.toLocalCurrent_fromLocalCurrent b k _).symm
    _ = _ := congrArg (toLocalCurrent b k) hh


omit [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)] in
private theorem exists_related_counterpart {q : ℕ} (e f : ComplexChart n M)
    (φ : 𝓓(overlapSource e f, ℝ)) (γ : ComplexModel n [⋀^Fin q]→L[ℝ] ℝ) :
    ∃ ζ : TestForm (overlapTarget e f) q,
      OverlapTestRelated e f (constantTestFormCLM γ φ) ζ := by
  let F := chartTransition e f
  have hU : (⟨(⊤ : Opens (ComplexModel n)) ∩
      (F.source ∩ F ⁻¹' (⊤ : Opens (ComplexModel n))),
      (⊤ : Opens (ComplexModel n)).isOpen.inter
        (F.isOpen_inter_preimage (⊤ : Opens (ComplexModel n)).isOpen)⟩ :
      Opens (ComplexModel n)) = overlapSource e f := by
    ext z
    change z ∈ (Set.univ ∩ (F.source ∩ F ⁻¹' Set.univ)) ↔ z ∈ F.source
    simp only [preimage_univ, inter_univ, univ_inter]
  have hcounter := ActualChartOverlapTestTransport.exists_constant_form_counterpart e f ⊤ ⊤ q
  dsimp only at hcounter
  rw [hU, top_inf_eq] at hcounter
  obtain ⟨ζ, _hsupp, _hζ, hrel⟩ := hcounter φ γ
  refine ⟨ζ, ?_⟩
  intro z hz v
  rw [constantTestFormCLM_apply, ContinuousAlternatingMap.smul_apply]
  exact hrel z hz v

private theorem regularForms_eq_of_original_readings
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (T : GlobalCurrent n M k)
    (a : ComplexChart n M → ComplexModel n → (ComplexModel n [⋀^Fin k.val]→L[ℝ] ℝ))
    (ha : ∀ e, ContDiffOn ℝ ∞ (a e) (chartTarget e))
    (hread : ∀ e, T.coefficients b e = regularFormDistribution b.addHaar (a e)
      ((ha e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet))
    (e f : ComplexChart n M) :
    regularFormDistribution b.addHaar (a e)
      (((ha e).continuousOn.locallyIntegrableOn
        (chartTarget e).isOpen.measurableSet).mono_set (overlapSource_le e f)) =
    regularFormDistribution b.addHaar (chartPullbackField e f (a f))
      ((contDiffOn_chartPullbackField e f (ha f)).continuousOn.locallyIntegrableOn
        (overlapSource e f).isOpen.measurableSet) := by
  let hLe : LocallyIntegrableOn (a e) (overlapSource e f) b.addHaar :=
    ((ha e).continuousOn.locallyIntegrableOn
      (chartTarget e).isOpen.measurableSet).mono_set (overlapSource_le e f)
  let hLf : LocallyIntegrableOn (a f) (overlapTarget e f) b.addHaar :=
    ((ha f).continuousOn.locallyIntegrableOn
      (chartTarget f).isOpen.measurableSet).mono_set (overlapTarget_le e f)
  let hLp : LocallyIntegrableOn (chartPullbackField e f (a f))
      (overlapSource e f) b.addHaar :=
    (contDiffOn_chartPullbackField e f (ha f)).continuousOn.locallyIntegrableOn
      (overlapSource e f).isOpen.measurableSet
  have he : T.restrictChart e (overlapSource_le e f) =
      toLocalCurrent b k (regularFormDistribution b.addHaar (a e) hLe) :=
    restrictChart_eq_regular b T e (overlapSource_le e f) _ (hread e)
  have hf : T.restrictChart f (overlapTarget_le e f) =
      toLocalCurrent b k (regularFormDistribution b.addHaar (a f) hLf) :=
    restrictChart_eq_regular b T f (overlapTarget_le e f) _ (hread f)
  ext w φ
  let γ := contractVolume (basisVolume (currentPairingBasis b k)) w
  obtain ⟨ζ, htest⟩ := exists_related_counterpart e f φ γ
  have hp := T.overlap e f (constantTestFormCLM γ φ) ζ htest
  rw [he, hf] at hp
  have hpb := regular_pairing_chart_pullback b e f (a f) (ha f)
    (constantTestFormCLM γ φ) ζ htest
  have heval : toLocalCurrent b k (regularFormDistribution b.addHaar (a e) hLe)
      (constantTestFormCLM γ φ) =
    toLocalCurrent b k (regularFormDistribution b.addHaar
      (chartPullbackField e f (a f)) hLp) (constantTestFormCLM γ φ) := hp.trans hpb.symm
  have hi₁ := congrArg (fun A : DistributionForm (overlapSource e f) k.val => A w φ)
    (CurrentPairing.fromLocalCurrent_toLocalCurrent b k
      (regularFormDistribution b.addHaar (a e) hLe))
  have hi₂ := congrArg (fun A : DistributionForm (overlapSource e f) k.val => A w φ)
    (CurrentPairing.fromLocalCurrent_toLocalCurrent b k
      (regularFormDistribution b.addHaar (chartPullbackField e f (a f)) hLp))
  exact hi₁.symm.trans (heval.trans hi₂)
/-- Original signed current overlaps internally force the complete pointwise tensor law. -/
theorem tensor_law_of_smooth_coefficient_readings
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    {k : CurrentDegree n} (T : GlobalCurrent n M k)
    (a : ComplexChart n M → ComplexModel n → (ComplexModel n [⋀^Fin k.val]→L[ℝ] ℝ))
    (ha : ∀ e, ContDiffOn ℝ ∞ (a e) (chartTarget e))
    (hread : ∀ e, T.coefficients b e = regularFormDistribution b.addHaar (a e)
      ((ha e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet))
    (e f : ComplexChart n M) (x : ComplexModel n) (hx : x ∈ (chartTransition e f).source)
    (v : Fin k.val → ComplexModel n) :
    a e x v = a f (chartTransition e f x)
      (fun i => chartTransitionDerivative e f x (v i)) := by
  have hpe := contDiffOn_chartPullbackField e f (ha f)
  have hLe : LocallyIntegrableOn (a e) (overlapSource e f) b.addHaar :=
    ((ha e).continuousOn.locallyIntegrableOn
      (chartTarget e).isOpen.measurableSet).mono_set (overlapSource_le e f)
  have hLp : LocallyIntegrableOn (chartPullbackField e f (a f))
      (overlapSource e f) b.addHaar :=
    hpe.continuousOn.locallyIntegrableOn (overlapSource e f).isOpen.measurableSet
  have hforms : regularFormDistribution b.addHaar (a e) hLe =
      regularFormDistribution b.addHaar (chartPullbackField e f (a f)) hLp :=
    regularForms_eq_of_original_readings b T a ha hread e f
  have hsame : EqOn (a e) (chartPullbackField e f (a f)) (overlapSource e f) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq
      (ActualLocallyIntegrableFormDensityUniqueness.ae_eq_of_regularFormDistribution_eq
        b.addHaar hLe hLp hforms) (overlapSource e f).isOpen
      ((ha e).continuousOn.mono (overlapSource_le e f)) hpe.continuousOn
  have hvalue := congrArg (fun A : ComplexModel n [⋀^Fin k.val]→L[ℝ] ℝ => A v) (hsame hx)
  simpa only [chartPullbackField, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def] using hvalue

end SGPT.Foundations.Analysis.Pending.SignedSmoothCoefficientTensorLaw
