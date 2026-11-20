import SGPT.Okounkov.TranscendentalWNConv6Product

/-!
# The inner region: Fubini over the fibres (WN21 Proposition 6.4; lane WN-CONV6)

Blueprint `tok-wn-conv6:inner` (chapter `claude-tok-wn-conv6`).  For `0 < ε` and every `k`,

`∫_{R_ε} ⟨(θ̃ + ddᶜu_k)^{n+1}⟩ ≤ |θ̃^{n+1}|(R_ε \ X₀) + (n + 1) ∫_ℂ I_k dω_k`

(`envelopeMeasure_inner_le`), where `R_ε = 𝒳 \ O_ε = {|τ| ≤ ε}`.  The region `R_ε \ X₀` is covered
by the images `coord e_j '' K_j` of product-coordinate boxes `K_j = e_j(A_j) × B_ε`
(`A_j` a countable measurable partition of `X` subordinate to charts `e_j`,
`B_ε = {0 < |w| ≤ ε}`); on each, the change of variables (`ChangeVar.topFormMeasure_image`), the
density bound on the contact set (`MCData.topDensity_chartPull_le`), Tonelli
(`lintegral_prod_le`) and the chart formula on `X` give the claim; `X₀` carries no
non-pluripolar mass.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity
open scoped SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Toric
open SGPT.Okounkov.TranscendentalMain

/-! ### A countable measurable partition subordinate to charts -/

section Partition

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [Nonempty M]

theorem exists_chart_partition [MeasurableSpace M] [BorelSpace M] :
    ∃ (e : ℕ → ComplexChart n M) (A : ℕ → Set M), (∀ j, MeasurableSet (A j)) ∧
      (∀ j, A j ⊆ (e j).val.source) ∧ Pairwise (Function.onFun Disjoint A) ∧ (⋃ j, A j) = univ := by
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : M => (complexChartAt (n := n) x).val.source) fun x => (complexChartAt x).val.open_source
  have hTcov : (⋃ x ∈ T, (complexChartAt (n := n) x).val.source) = univ := by
    rw [hTU]; exact eq_univ_of_forall fun x => mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩
  have hTne : T.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h] at hTcov
    simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at hTcov
    obtain ⟨x⟩ := (inferInstance : Nonempty M)
    exact (eq_empty_iff_forall_notMem.mp hTcov.symm x) (mem_univ x)
  obtain ⟨xs, rfl⟩ := hTc.exists_eq_range hTne
  refine ⟨fun j => complexChartAt (xs j), disjointed fun j => (complexChartAt (n := n) (xs j)).val.source,
    MeasurableSet.disjointed fun j => (complexChartAt (xs j)).val.open_source.measurableSet,
    fun j => disjointed_subset _ j, disjoint_disjointed _, ?_⟩
  rw [iUnion_disjointed]
  rw [← hTcov]
  ext x; simp

end Partition

namespace MCData

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 1)} {𝒳 : Type u} [TopologicalSpace 𝒳]
  [ChartedSpace (ComplexModel (m + 1 + 1)) 𝒳] [IsComplexManifold (m + 1 + 1) 𝒳]
  (D : MCData F 𝒳)

/-- `B_ε = {0 < |w| ≤ ε}`. -/
def ballPunct (ε : ℝ) : Set (ComplexModel 1) := {w | w 0 ≠ 0 ∧ ‖w 0‖ ≤ ε}

/-- The box `e(A) × B_ε` in product coordinates. -/
def box (e : ComplexChart (m + 1) F.carrier) (A : Set F.carrier) (ε : ℝ) :
    Set (ComplexModel (m + 1 + 1)) :=
  prodModelEquiv (m + 1) 1 '' ((e.val '' A) ×ˢ ballPunct ε)

theorem mem_box {e : ComplexChart (m + 1) F.carrier} {A : Set F.carrier} {ε : ℝ}
    {y : ComplexModel (m + 1 + 1)} :
    y ∈ box e A ε ↔ zc y ∈ e.val '' A ∧ wc y ∈ ballPunct ε := by
  constructor
  · rintro ⟨⟨z, w⟩, ⟨hz, hw⟩, rfl⟩
    rw [zc_pme, wc_pme]; exact ⟨hz, hw⟩
  · intro h
    exact ⟨(zc y, wc y), h, pme_zc_wc y⟩

theorem box_subset {e : ComplexChart (m + 1) F.carrier} {A : Set F.carrier} (hA : A ⊆ e.val.source)
    (ε : ℝ) : box e A ε ⊆ coordDomain e := by
  intro y hy
  obtain ⟨⟨x, hx, hxz⟩, hw⟩ := mem_box.mp hy
  exact ⟨by rw [← hxz]; exact e.val.map_source (hA hx), hw.1⟩

theorem measurableSet_ballPunct (ε : ℝ) : MeasurableSet (ballPunct ε) := by
  have hc : Continuous fun w : ComplexModel 1 => w 0 :=
    (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).continuous
  exact (isOpen_ne_fun hc continuous_const).measurableSet.inter
    (isClosed_le hc.norm continuous_const).measurableSet

theorem measurableSet_chartImage [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    (e : ComplexChart (m + 1) F.carrier) {A : Set F.carrier} (hAm : MeasurableSet A)
    (hA : A ⊆ e.val.source) : MeasurableSet (e.val '' A) := by
  rw [e.val.image_eq_target_inter_inv_preimage hA]
  exact SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
    e.val.open_target.measurableSet e.val.continuousOn_symm hAm

theorem measurableSet_box [MeasurableSpace F.carrier] [BorelSpace F.carrier]
    (e : ComplexChart (m + 1) F.carrier) {A : Set F.carrier} (hAm : MeasurableSet A)
    (hA : A ⊆ e.val.source) (ε : ℝ) : MeasurableSet (box e A ε) := by
  have h := ((measurableSet_chartImage e hAm hA).prod (measurableSet_ballPunct ε))
  exact (prodModelEquiv (m + 1) 1).toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr h

/-! ### The estimate on one box -/

section Piece

variable [CompactSpace 𝒳] [ConnectedSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]

/-- The fibre density `(s_τ^*θ̃)ⁿ` in the chart `e` at `zc y` (`0` off `w ≠ 0`). -/
def fibreDensity (e : ComplexChart (m + 1) F.carrier) (y : ComplexModel (m + 1 + 1)) : ℝ :=
  if h : wc y 0 = 0 then 0 else
    actualTopPowerDensity ((ClosedRealOneOneForm.pullback (D.contMDiff_sec h) D.form).val.coeff e
      (zc y))

omit [CompactSpace 𝒳] [ConnectedSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳] in
theorem pullback_sec_congr {τ τ' : ℂ} (h : τ = τ') (hτ : τ ≠ 0) (hτ' : τ' ≠ 0)
    (α : ClosedRealOneOneForm (m + 1 + 1) 𝒳) :
    ClosedRealOneOneForm.pullback (D.contMDiff_sec hτ) α =
      ClosedRealOneOneForm.pullback (D.contMDiff_sec hτ') α := by
  subst h; rfl

omit [CompactSpace 𝒳] [ConnectedSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳] in
theorem fibreDensity_pme (e : ComplexChart (m + 1) F.carrier) {z : ComplexModel (m + 1)}
    {w : ComplexModel 1} (hw0 : w 0 ≠ 0) :
    D.fibreDensity e (prodModelEquiv (m + 1) 1 (z, w)) =
      actualTopPowerDensity ((ClosedRealOneOneForm.pullback (D.contMDiff_sec hw0) D.form).val.coeff
        e z) := by
  have hne : wc (prodModelEquiv (m + 1) 1 (z, w)) 0 ≠ 0 := by rw [wc_pme]; exact hw0
  rw [fibreDensity, dif_neg hne, D.pullback_sec_congr (by rw [wc_pme]) hne hw0, zc_pme]

/-- The fibre mass of a piece `A ⊆ X` over `w`. -/
def pieceMass (k : ℕ) (A : Set F.carrier) (w : ComplexModel 1) : ℝ≥0∞ :=
  if h : w 0 = 0 then 0 else
    letI : MeasurableSpace F.carrier := borel F.carrier
    haveI : BorelSpace F.carrier := ⟨rfl⟩
    SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure F.omega
      (ClosedRealOneOneForm.pullback (D.contMDiff_sec h) D.form) (A ∩ D.sec h ⁻¹' D.contact k)

theorem measurableSet_contact (k : ℕ) : MeasurableSet (D.contact k) :=
  (isClosed_contact (D.isThetaPshPotential_envelope k).1 (D.chartSmooth_obstacle k)
    (D.envelope_le_obstacle k)).measurableSet

omit [MeasurableSpace 𝒳] [BorelSpace 𝒳] in
theorem isClosed_contact' (k : ℕ) : IsClosed (D.contact k) :=
  isClosed_contact (D.isThetaPshPotential_envelope k).1 (D.chartSmooth_obstacle k)
    (D.envelope_le_obstacle k)

/-- **Tonelli and the chart formula on `X`** for the second term. -/
theorem lintegral_box_fibre_le (e : ComplexChart (m + 1) F.carrier) {A : Set F.carrier}
    (hAm : MeasurableSet[borel F.carrier] A) (hA : A ⊆ e.val.source) (ε : ℝ) (k : ℕ) :
    ∫⁻ y in box e A ε ∩ D.coord e ⁻¹' D.contact k,
        ENNReal.ofReal (D.fibreDensity e y) * ENNReal.ofReal (cutoffLineDensity D.χ k (wc y)) ≤
      ∫⁻ w, (ballPunct ε).indicator (fun w => ENNReal.ofReal (cutoffLineDensity D.χ k w) *
        D.pieceMass k A w) w := by
  let : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  set K := box e A ε ∩ D.coord e ⁻¹' D.contact k with hK
  have hKm : MeasurableSet K := by
    have h1 := SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
      (isOpen_coordDomain e).measurableSet (D.continuousOn_coord e) (D.measurableSet_contact k)
    have h2 : K = box e A ε ∩ (coordDomain e ∩ D.coord e ⁻¹' D.contact k) := by
      rw [hK]; ext y; constructor
      · rintro ⟨hy1, hy2⟩; exact ⟨hy1, box_subset hA ε hy1, hy2⟩
      · rintro ⟨hy1, -, hy2⟩; exact ⟨hy1, hy2⟩
    rw [h2]; exact (measurableSet_box e hAm hA ε).inter h1
  set G : ComplexModel (m + 1 + 1) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (D.fibreDensity e y) * ENNReal.ofReal (cutoffLineDensity D.χ k (wc y))
  rw [← lintegral_indicator hKm]
  -- product coordinates `(w, z) ↦ (z, w)`
  set Ψ : ComplexModel 1 × ComplexModel (m + 1) → ComplexModel (m + 1 + 1) :=
    fun p => prodModelEquiv (m + 1) 1 (p.2, p.1) with hΨ
  have hΨmp : MeasurePreserving Ψ (volume.prod volume) volume :=
    (ProductMixedMeasure.measurePreserving_prodModelEquiv (m + 1) 1).comp
      (Measure.measurePreserving_swap)
  have hΨe : MeasurableEmbedding Ψ :=
    (MeasurableEquiv.prodComm.trans
      (prodModelEquiv (m + 1) 1).toHomeomorph.toMeasurableEquiv).measurableEmbedding
  rw [← hΨmp.lintegral_comp_emb hΨe]
  refine (lintegral_prod_le _).trans (lintegral_mono fun w => ?_)
  by_cases hw : w ∈ ballPunct ε
  · rw [indicator_of_mem hw]
    have hw0 : w 0 ≠ 0 := hw.1
    set s := D.sec hw0 with hs
    have hsc : Continuous s := (D.contMDiff_sec hw0).continuous
    set S := A ∩ s ⁻¹' D.contact k with hS
    have hSm : MeasurableSet S := hAm.inter ((D.isClosed_contact' k).preimage hsc).measurableSet
    have hSsrc : S ⊆ e.val.source := fun x hx => hA hx.1
    -- the slice of the indicator
    have hslice : ∀ z, K.indicator G (Ψ (w, z)) =
        ENNReal.ofReal (cutoffLineDensity D.χ k w) *
          (e.val '' S).indicator (fun z => ENNReal.ofReal (actualTopPowerDensity
            ((ClosedRealOneOneForm.pullback (D.contMDiff_sec hw0) D.form).val.coeff e z))) z := by
      intro z
      have hzc : zc (Ψ (w, z)) = z := zc_pme z w
      have hwc : wc (Ψ (w, z)) = w := wc_pme z w
      by_cases hz : z ∈ e.val '' S
      · obtain ⟨x, hx, rfl⟩ := hz
        have hmemb : Ψ (w, e.val x) ∈ box e A ε :=
          mem_box.mpr ⟨by rw [zc_pme]; exact mem_image_of_mem _ hx.1, by rw [wc_pme]; exact hw⟩
        have hmemK : Ψ (w, e.val x) ∈ K := by
          refine ⟨hmemb, ?_⟩
          have hdom : Ψ (w, e.val x) ∈ coordDomain e := box_subset hA ε hmemb
          show D.coord e (Ψ (w, e.val x)) ∈ D.contact k
          rw [D.coord_eq_sec hdom, D.sec_congr (τ' := w 0) (by rw [hwc]) hdom.2 hw0, hzc,
            e.val.left_inv (hA hx.1)]
          exact hx.2
        rw [indicator_of_mem hmemK, indicator_of_mem (mem_image_of_mem _ hx)]
        show ENNReal.ofReal (D.fibreDensity e (prodModelEquiv (m + 1) 1 (e.val x, w))) *
          ENNReal.ofReal (cutoffLineDensity D.χ k (wc (prodModelEquiv (m + 1) 1 (e.val x, w)))) = _
        rw [D.fibreDensity_pme e hw0, wc_pme, mul_comm]
      · rw [indicator_of_notMem hz, mul_zero]
        refine indicator_of_notMem (fun hK' => hz ?_) _
        obtain ⟨hb, hc⟩ := hK'
        obtain ⟨⟨x, hxA, hxz⟩, -⟩ := mem_box.mp hb
        rw [hzc] at hxz
        refine ⟨x, ⟨hxA, ?_⟩, hxz⟩
        have hdom : Ψ (w, z) ∈ coordDomain e := box_subset hA ε hb
        have hc' : D.coord e (Ψ (w, z)) ∈ D.contact k := hc
        rw [D.coord_eq_sec hdom, D.sec_congr (τ' := w 0) (by rw [hwc]) hdom.2 hw0, hzc,
          ← hxz, e.val.left_inv (hA hxA)] at hc'
        exact hc'
    refine (lintegral_congr hslice).trans_le ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator
      (measurableSet_chartImage e hSm hSsrc)]
    gcongr
    -- the chart formula on `X`
    have himg : e.val.symm '' (e.val '' S) = S := by
      rw [image_image]
      exact (image_congr fun x hx => e.val.left_inv (hSsrc hx)).trans (image_id S)
    have hform := topFormMeasure_image_eq F.omega
      (ProductTestForms.formPow (ClosedRealOneOneForm.pullback (D.contMDiff_sec hw0) D.form).val
        (m + 1)) e (measurableSet_chartImage e hSm hSsrc)
      (by rintro _ ⟨x, hx, rfl⟩; exact e.val.map_source (hSsrc hx))
    rw [himg] at hform
    rw [pieceMass, dif_neg hw0]
    apply le_of_eq
    rw [show SGPT.Okounkov.TranscendentalWNReg.positiveTopMeasure F.omega
        (ClosedRealOneOneForm.pullback (D.contMDiff_sec hw0) D.form) S =
      topFormMeasure F.omega (ProductTestForms.formPow
        (ClosedRealOneOneForm.pullback (D.contMDiff_sec hw0) D.form).val (m + 1)) S from rfl, hform]
    refine setLIntegral_congr_fun (measurableSet_chartImage e hSm hSsrc) fun z _ => ?_
    rw [ProductTestForms.formPow_coeff, topDensity_formPower]
  · rw [indicator_of_notMem hw]
    have h0 : ∀ z, K.indicator G (Ψ (w, z)) = 0 := by
      intro z
      refine indicator_of_notMem (fun hK' => hw ?_) _
      have := (mem_box.mp hK'.1).2
      rwa [wc_pme] at this
    exact ((lintegral_congr h0).trans lintegral_zero).le

/-- The total variation `|θ̃^{n+1}|` of the top power of `θ̃`, as `(θ̃^{n+1})₊ + (-θ̃^{n+1})₊`. -/
def totalVar (w : KahlerBackground (m + 1 + 1) 𝒳) : Measure 𝒳 :=
  topFormMeasure w (ProductTestForms.formPow D.form.val (m + 1 + 1)) +
    topFormMeasure w (-ProductTestForms.formPow D.form.val (m + 1 + 1))

omit [CompactSpace 𝒳] [ConnectedSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳] in
theorem topDensity_coordPullback_neg (Φ : SmoothRealForm (m + 1 + 1) 𝒳 (2 * (m + 1 + 1)))
    (φ : ComplexModel (m + 1 + 1) → 𝒳) (y : ComplexModel (m + 1 + 1)) :
    topDensity (ChangeVar.coordPullback (-Φ) φ y) = -topDensity (ChangeVar.coordPullback Φ φ y) := by
  have h : ChangeVar.coordPullback (-Φ) φ y = -ChangeVar.coordPullback Φ φ y := by
    ext v; rfl
  rw [h, show -ChangeVar.coordPullback Φ φ y = 0 - ChangeVar.coordPullback Φ φ y by abel,
    topDensity_sub, topDensity_zero, zero_sub]

/-- **The estimate on one box** (`tok-wn-conv6:inner`, one chart piece). -/
theorem envelopeMeasure_box_le (w : KahlerBackground (m + 1 + 1) 𝒳) (e : ComplexChart (m + 1) F.carrier)
    {A : Set F.carrier} (hAm : MeasurableSet[borel F.carrier] A) (hA : A ⊆ e.val.source) (ε : ℝ)
    (k : ℕ) :
    diagonalPotentialMeasure D.form (D.envelope k) (D.isThetaPshPotential_envelope k)
        (D.coord e '' box e A ε) ≤
      D.totalVar w (D.coord e '' box e A ε) + ((m + 1 + 1 : ℕ) : ℝ≥0∞) *
        ∫⁻ w, (ballPunct ε).indicator (fun w => ENNReal.ofReal (cutoffLineDensity D.χ k w) *
          D.pieceMass k A w) w := by
  set φ := D.coord e with hφ
  set U := coordDomain e with hU
  set K := box e A ε with hK
  have hUo : IsOpen U := isOpen_coordDomain e
  have hKU : K ⊆ U := box_subset hA ε
  have hKm : MeasurableSet K := by
    let : MeasurableSpace F.carrier := borel F.carrier
    have : BorelSpace F.carrier := ⟨rfl⟩
    exact measurableSet_box e hAm hA ε
  have hφc := D.continuousOn_coord e
  have hφd : ∀ (f : ComplexChart (m + 1 + 1) 𝒳), ∀ y ∈ U, φ y ∈ f.val.source →
      DifferentiableAt ℂ (fun y' => f.val (φ y')) y := fun f y hy hf => D.differentiableAt_coord f hy hf
  have hφd' : ∀ (f : ComplexChart (m + 1 + 1) 𝒳), ∀ y ∈ U, φ y ∈ f.val.source →
      ContDiffAt ℂ ∞ (fun y' => f.val (φ y')) y := fun f y hy hf => D.contDiffAt_coord_chart f hy hf
  have hinj := D.injOn_coord e
  set C := D.contact k with hC
  have hCm : MeasurableSet C := D.measurableSet_contact k
  set K' := K ∩ φ ⁻¹' C with hK'
  have hK'U : K' ⊆ U := fun y hy => hKU hy.1
  have hK'm : MeasurableSet K' := by
    have h1 := SmoothMixedMeasureDensity.measurableSet_inter_preimage_of_continuousOn
      hUo.measurableSet hφc hCm
    have h2 : K' = K ∩ (U ∩ φ ⁻¹' C) := by
      ext y; constructor
      · rintro ⟨hy1, hy2⟩; exact ⟨hy1, hKU hy1, hy2⟩
      · rintro ⟨hy1, -, hy2⟩; exact ⟨hy1, hy2⟩
    rw [h2]; exact hKm.inter h1
  set Φk := ProductTestForms.formPow
    (D.form + ddcClosedForm (D.obstacle k) (D.chartSmooth_obstacle k)).val (m + 1 + 1)
  set Φ0 := ProductTestForms.formPow D.form.val (m + 1 + 1)
  -- step 1: the contact bound and the change of variables
  have h1 : diagonalPotentialMeasure D.form (D.envelope k) (D.isThetaPshPotential_envelope k)
      (φ '' K) ≤ topFormMeasure w Φk (φ '' K') := by
    have h := diagonalPotentialMeasure_rooftopEnvelope_le_contact w D.form
      (D.chartSmooth_obstacle k) (D.isThetaPshPotential_envelope k)
    calc _ ≤ ((topFormMeasure w Φk).restrict C) (φ '' K) := h _
      _ = topFormMeasure w Φk (φ '' K') := by
          rw [Measure.restrict_apply' hCm, hK', image_inter_preimage]
  rw [ChangeVar.topFormMeasure_image w Φk hUo hφc hφd hinj hK'm hK'U] at h1
  refine h1.trans ?_
  -- step 2: the pointwise bound
  set b : ComplexModel (m + 1 + 1) → ℝ := fun y => topDensity (ChangeVar.coordPullback Φ0 φ y)
  set F1 : ComplexModel (m + 1 + 1) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (b y) + ENNReal.ofReal (-b y)
  set F2 : ComplexModel (m + 1 + 1) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal ((m + 1 + 1 : ℕ) : ℝ) *
      (ENNReal.ofReal (D.fibreDensity e y) * ENNReal.ofReal (cutoffLineDensity D.χ k (wc y)))
  have hpt : ∀ y ∈ K', ENNReal.ofReal (topDensity (ChangeVar.coordPullback Φk φ y)) ≤ F1 y + F2 y := by
    intro y hy
    have hyU := hK'U hy
    have hle := D.topDensity_chartPull_le (complexChartAt (n := m + 1 + 1) (φ y)) hyU
      (mem_complexChartAt_source _) hy.2
    have hfd : D.fibreDensity e y = actualTopPowerDensity
        ((ClosedRealOneOneForm.pullback (D.contMDiff_sec hyU.2) D.form).val.coeff e (zc y)) := by
      rw [fibreDensity, dif_neg hyU.2]
    rw [← hfd] at hle
    have hρ := cutoffLineDensity_nonneg D.hχ k (wc y)
    calc ENNReal.ofReal (topDensity (ChangeVar.coordPullback Φk φ y))
        ≤ ENNReal.ofReal (b y + ((m + 1 + 1 : ℕ) : ℝ) * D.fibreDensity e y *
            cutoffLineDensity D.χ k (wc y)) := ENNReal.ofReal_le_ofReal hle
      _ ≤ ENNReal.ofReal (b y) + ENNReal.ofReal (((m + 1 + 1 : ℕ) : ℝ) * D.fibreDensity e y *
            cutoffLineDensity D.χ k (wc y)) := ENNReal.ofReal_add_le
      _ ≤ F1 y + F2 y := by
          refine add_le_add (le_self_add) (le_of_eq ?_)
          rw [mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul' hρ]
  -- step 3: integrate
  have hcont : ContinuousOn F1 U := by
    have hb := ChangeVar.continuousOn_topDensity_coordPullback Φ0 hUo hφc hφd'
    have hb' := ChangeVar.continuousOn_topDensity_coordPullback (-Φ0) hUo hφc hφd'
    have hb'' : ContinuousOn (fun y => -b y) U := by
      refine hb'.congr fun y _ => ?_
      exact (topDensity_coordPullback_neg Φ0 φ y).symm
    exact (ENNReal.continuous_ofReal.comp_continuousOn hb).add
      (ENNReal.continuous_ofReal.comp_continuousOn hb'')
  calc ∫⁻ y in K', ENNReal.ofReal (topDensity (ChangeVar.coordPullback Φk φ y))
      ≤ ∫⁻ y in K', (F1 y + F2 y) := setLIntegral_mono' hK'm hpt
    _ = (∫⁻ y in K', F1 y) + ∫⁻ y in K', F2 y :=
        lintegral_add_left' ((hcont.mono hK'U).aemeasurable hK'm) _
    _ ≤ (∫⁻ y in K, F1 y) + ((m + 1 + 1 : ℕ) : ℝ≥0∞) *
          ∫⁻ w, (ballPunct ε).indicator (fun w => ENNReal.ofReal (cutoffLineDensity D.χ k w) *
            D.pieceMass k A w) w := by
        refine add_le_add (lintegral_mono_set inter_subset_left) ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_natCast]
        gcongr
        exact D.lintegral_box_fibre_le e hAm hA ε k
    _ = D.totalVar w (φ '' K) + _ := by
        congr 1
        have hf1 : AEMeasurable (fun y => ENNReal.ofReal (b y)) (volume.restrict K) :=
          ((ENNReal.continuous_ofReal.comp_continuousOn
            (ChangeVar.continuousOn_topDensity_coordPullback Φ0 hUo hφc hφd')).mono hKU).aemeasurable
            hKm
        rw [show (∫⁻ y in K, F1 y) = (∫⁻ y in K, ENNReal.ofReal (b y)) +
            ∫⁻ y in K, ENNReal.ofReal (-b y) from lintegral_add_left' hf1 _, totalVar,
          Measure.add_apply,
          ChangeVar.topFormMeasure_image w Φ0 hUo hφc hφd hinj hKm hKU,
          ChangeVar.topFormMeasure_image w (-Φ0) hUo hφc hφd hinj hKm hKU]
        congr 1

end Piece

/-! ### Summation over the partition -/

theorem tsum_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (g : ℕ → α → ℝ≥0∞) :
    ∑' j, ∫⁻ a, g j a ∂μ ≤ ∫⁻ a, ∑' j, g j a ∂μ := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  have h : ∀ N, ∑ j ∈ Finset.range N, ∫⁻ a, g j a ∂μ ≤ ∫⁻ a, ∑ j ∈ Finset.range N, g j a ∂μ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      simp_rw [Finset.sum_range_succ]
      exact (add_le_add ih le_rfl).trans (le_lintegral_add _ _)
  exact (h N).trans (lintegral_mono fun a => ENNReal.sum_le_tsum _)

theorem continuous_cutoffLineDensity {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) :
    Continuous (cutoffLineDensity χ k) := by
  have h2 := (contDiff_cutoffLineProfile hχ k).continuous_iteratedFDeriv (m := 2) two_le_top'
  have hev : ∀ a b : ComplexModel 1, Continuous fun z =>
      realHessian (cutoffLineProfile χ k) z a b := fun a b =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ComplexModel 1) ℝ ![a, b]).continuous.comp h2
  have hH : Continuous fun z => complexHessian (cutoffLineProfile χ k) z := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [complexHessian]
    have h1 := hev (coordinateVector i) (coordinateVector j)
    have h2 := hev (Complex.I • coordinateVector i) (Complex.I • coordinateVector j)
    have h3 := hev (coordinateVector i) (Complex.I • coordinateVector j)
    have h4 := hev (Complex.I • coordinateVector i) (coordinateVector j)
    fun_prop
  unfold cutoffLineDensity smoothDensity
  exact continuous_const.mul (Complex.continuous_re.comp hH.matrix_det)

theorem centralFibre_measure_zero [CompactSpace 𝒳] [ConnectedSpace 𝒳] [MeasurableSpace 𝒳]
    [BorelSpace 𝒳] (k : ℕ) :
    diagonalPotentialMeasure D.form (D.envelope k) (D.isThetaPshPotential_envelope k)
      (centralFibre F D.μ) = 0 :=
  GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar _ _
    (ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset
      D.isComplexAnalyticSubset_centralFibre D.interior_centralFibre)

theorem weight_affine_le_iff {ε : ℝ} (hε : 0 < ε) (τ : ℂ) :
    affineLinePoint τ ∉ outerLine ε ↔ ‖τ‖ ≤ ε := by
  simp only [outerLine, mem_ofPred_eq, not_lt, projectiveWeight_zero_affineLinePoint]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  constructor
  · intro h
    exact (sq_le_sq₀ (norm_nonneg τ) hε.le).mp (by nlinarith)
  · intro h
    have := (sq_le_sq₀ (norm_nonneg τ) hε.le).mpr h
    nlinarith

/-- **`tok-wn-conv6:inner`** (WN21 Proposition 6.4): for `ε > 0` and every `k`,
`∫_{R_ε} ⟨(θ̃ + ddᶜu_k)^{n+1}⟩ ≤ |θ̃^{n+1}|(R_ε \ X₀) + (n + 1) ∫_ℂ I_k dω_k`. -/
theorem envelopeMeasure_inner_le [CompactSpace 𝒳] [ConnectedSpace 𝒳] [MeasurableSpace 𝒳]
    [BorelSpace 𝒳] (w : KahlerBackground (m + 1 + 1) 𝒳) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    diagonalPotentialMeasure D.form (D.envelope k) (D.isThetaPshPotential_envelope k)
        (D.outer ε)ᶜ ≤
      D.totalVar w ((D.outer ε)ᶜ \ centralFibre F D.μ) + ((m + 1 + 1 : ℕ) : ℝ≥0∞) *
        ∫⁻ τ, D.fibreMass k τ ∂cutoffLineMeasure D.χ k := by
  let : MeasurableSpace F.carrier := borel F.carrier
  have : BorelSpace F.carrier := ⟨rfl⟩
  obtain ⟨e, A, hAm, hAe, hAd, hAU⟩ := exists_chart_partition (n := m + 1) (M := F.carrier)
  set img : ℕ → Set 𝒳 := fun j => D.coord (e j) '' box (e j) (A j) ε with himg
  set MA := diagonalPotentialMeasure D.form (D.envelope k) (D.isThetaPshPotential_envelope k)
  -- the images lie in `R_ε \ X₀`
  have hsub : ∀ j, img j ⊆ (D.outer ε)ᶜ \ centralFibre F D.μ := by
    rintro j _ ⟨y, hy, rfl⟩
    have hyU := box_subset (hAe j) ε hy
    have hw := (mem_box.mp hy).2
    have hμy := D.μ_coord hyU
    refine ⟨fun hO => ?_, fun hX => ?_⟩
    · have : (D.μ (D.coord (e j) y)).2 ∈ outerLine ε := hO
      rw [hμy] at this
      exact ((weight_affine_le_iff hε _).mpr hw.2) this
    · have h0 := (D.mem_centralFibre_iff _).mp hX
      rw [weight0, hμy] at h0
      exact (projectiveWeight_zero_pos (affineLinePoint_ne_projectiveZero hw.1)).ne' h0
  -- the images cover `R_ε \ X₀`
  have hcov : (D.outer ε)ᶜ ⊆ centralFibre F D.μ ∪ ⋃ j, img j := by
    intro z hz
    by_cases hzX : z ∈ centralFibre F D.μ
    · exact Or.inl hzX
    right
    set p := (D.μ z).2 with hp
    have hp0 : p ≠ projectiveZero := fun h => hzX ((D.mem_centralFibre_iff z).mpr (by
      rw [weight0, ← hp, h, projectiveWeight_zero_projectiveZero]))
    have hpinf : p ≠ projectiveInfinity := by
      intro h
      apply hz
      show (D.μ z).2 ∈ outerLine ε
      rw [← hp, h]
      show ε ^ 2 / (1 + ε ^ 2) < projectiveWeight 0 projectiveInfinity
      rw [projectiveWeight_zero_infinity, div_lt_one (by positivity)]
      linarith
    set τ := projectiveAffine p with hτ
    have hpτ : p = affineLinePoint τ := eq_affineLinePoint_of_ne_infinity hpinf
    have hτ0 : τ ≠ 0 := fun h => hp0 (by rw [hpτ, h, affineLinePoint_zero])
    have hτε : ‖τ‖ ≤ ε := by
      rw [← weight_affine_le_iff hε, ← hpτ]; exact hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hAU ▸ mem_univ (D.μ z).1)
    refine mem_iUnion.mpr ⟨j, prodModelEquiv (m + 1) 1 ((e j).val (D.μ z).1,
      projectiveModelEquiv τ), ?_, ?_⟩
    · refine mem_box.mpr ⟨by rw [zc_pme]; exact mem_image_of_mem _ hj, ?_⟩
      rw [wc_pme]
      refine ⟨by rw [projectiveModelEquiv_apply_zero]; exact hτ0, by
        rw [projectiveModelEquiv_apply_zero]; exact hτε⟩
    · rw [coord, pchart_symm, zc_pme, wc_pme, projectiveModelEquiv_apply_zero,
        (e j).val.left_inv (hAe j hj), ← hpτ]
      have hz' : D.μ z ∉ deformationCentre F := fun h =>
        hp0 ((mem_deformationCentre_iff F).mp h).2
      exact D.inv_μ hz'
  -- the images are disjoint and measurable
  have hdisj : Pairwise (Function.onFun Disjoint img) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    have h1 := D.μ_coord (box_subset (hAe i) ε hy)
    have h2 := D.μ_coord (box_subset (hAe j) ε hy')
    rw [← hyy', h2] at h1
    have hx := congrArg Prod.fst h1
    simp only at hx
    obtain ⟨⟨x, hx1, hx2⟩, -⟩ := mem_box.mp hy
    obtain ⟨⟨x', hx1', hx2'⟩, -⟩ := mem_box.mp hy'
    rw [← hx2, ← hx2', (e i).val.left_inv (hAe i hx1), (e j).val.left_inv (hAe j hx1')] at hx
    exact disjoint_left.mp (hAd hij) hx1 (hx ▸ hx1')
  have himgm : ∀ j, MeasurableSet (img j) := fun j =>
    ChangeVar.measurableSet_image (isOpen_coordDomain (e j)) (D.continuousOn_coord (e j))
      (fun f y hy hf => D.differentiableAt_coord f hy hf) (D.injOn_coord (e j))
      (measurableSet_box (e j) (hAm j) (hAe j) ε) (box_subset (hAe j) ε)
  -- the total variation term
  have hTV : ∑' j, D.totalVar w (img j) ≤ D.totalVar w ((D.outer ε)ᶜ \ centralFibre F D.μ) := by
    rw [← measure_iUnion hdisj himgm]
    exact measure_mono (iUnion_subset hsub)
  -- the fibre term
  set G : ℕ → ComplexModel 1 → ℝ≥0∞ := fun j => (ballPunct ε).indicator fun w =>
    ENNReal.ofReal (cutoffLineDensity D.χ k w) * D.pieceMass k (A j) w
  have hsumG : ∀ w, ∑' j, G j w ≤ ENNReal.ofReal (cutoffLineDensity D.χ k w) *
      D.fibreMass k (w 0) := by
    intro w
    by_cases hw : w ∈ ballPunct ε
    · simp only [G, indicator_of_mem hw]
      rw [ENNReal.tsum_mul_left]
      refine le_of_eq ?_
      congr 1
      have hw0 : w 0 ≠ 0 := hw.1
      simp only [pieceMass, dif_neg hw0, fibreMass, fibreContactMass]
      rw [← measure_iUnion (fun i j hij => (hAd hij).mono inter_subset_left inter_subset_left)
        (fun j => (hAm j).inter (((D.isClosed_contact' k).preimage
          (D.contMDiff_sec hw0).continuous).measurableSet)), ← iUnion_inter, hAU, univ_inter]
      rfl
    · simp only [G, indicator_of_notMem hw, tsum_zero]
      exact zero_le
  have hfib : ∑' j, ∫⁻ w, G j w ≤ ∫⁻ τ, D.fibreMass k τ ∂cutoffLineMeasure D.χ k := by
    refine (tsum_lintegral_le G).trans ((lintegral_mono hsumG).trans ?_)
    -- transport to `ℂ`
    have hmp := measurePreserving_projectiveModelRealIsometry
    have hemb : MeasurableEmbedding projectiveModelRealIsometry :=
      projectiveModelRealIsometry.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    rw [← hmp.lintegral_comp_emb hemb]
    have hfm : Measurable fun τ : ℂ =>
        ENNReal.ofReal (cutoffLineDensity D.χ k (projectiveModelEquiv τ)) :=
      ENNReal.measurable_ofReal.comp ((continuous_cutoffLineDensity D.hχ k).comp
        projectiveModelEquiv.continuous).measurable
    rw [cutoffLineMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hfm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine le_of_eq (lintegral_congr fun τ => ?_)
    have h1 : projectiveModelRealIsometry τ = projectiveModelEquiv τ := rfl
    simp only [Pi.mul_apply]
    rw [h1, projectiveModelEquiv_apply_zero]
  -- assembly
  calc MA (D.outer ε)ᶜ ≤ MA (centralFibre F D.μ ∪ ⋃ j, img j) := measure_mono hcov
    _ ≤ MA (centralFibre F D.μ) + ∑' j, MA (img j) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
    _ = ∑' j, MA (img j) := by rw [D.centralFibre_measure_zero k, zero_add]
    _ ≤ ∑' j, (D.totalVar w (img j) + ((m + 1 + 1 : ℕ) : ℝ≥0∞) * ∫⁻ w, G j w) :=
        ENNReal.tsum_le_tsum fun j => D.envelopeMeasure_box_le w (e j) (hAm j) (hAe j) ε k
    _ = ∑' j, D.totalVar w (img j) + ((m + 1 + 1 : ℕ) : ℝ≥0∞) * ∑' j, ∫⁻ w, G j w := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ _ := by gcongr

end MCData

end SGPT.Okounkov.TranscendentalWN
