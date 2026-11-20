import SGPT.Foundations.Analysis.FirstPass.RegularPatchNeighborhood
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetNull

set_option autoImplicit false

/-!
# Analytic sets are null in regular-patch parameters

Source: CT22, Section 2 (a proper analytic subset of `V_reg` is Lebesgue-null); Copy-4,
`eq:def-restricted-volume`; blueprint `ana:rv-birational-blowup`.

Let `P` be a regular patch of `V` with parametrization `γ : ℂ^k ⊇ D → M`, and `A ⊆ M` an
analytic subset that contains no nonempty relatively open part of `V`.  Then
`S = D ∩ γ⁻¹ A` is Lebesgue-null.  Near each point of `S`, `A` is the common zero set of
finitely many holomorphic functions `h_j`, so `S` is locally the common zero set of the
holomorphic functions `h_j ∘ γ` on a ball.  `γ` maps open subsets of `D` onto relatively
open subsets of `V`, so `S` has empty interior, and on a ball around the point some
`h_j ∘ γ` is not identically zero.  The zero set of a holomorphic function on a ball that
is not identically zero is null.  A countable cover finishes the argument.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.PatchParameterNull

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
open FirstPass.AdmissibleCurrentFormPositivity

noncomputable section

/-- The projection `ℂ^n → ℂ^k` onto the first `k` coordinates. -/
def planeProjection (k n : ℕ) : ComplexModel n → ComplexModel k :=
  fun z => WithLp.toLp 2 (fun i : Fin k => if h : i.1 < n then z ⟨i.1, h⟩ else 0)

theorem continuous_planeProjection (k n : ℕ) : Continuous (planeProjection k n) := by
  unfold planeProjection
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  by_cases h : i.1 < n
  · simp only [h, dif_pos]
    exact PiLp.continuous_apply 2 _ _
  · simp only [h, dif_neg, not_false_eq_true]
    exact continuous_const

theorem planeProjection_planeInclusion {k n : ℕ} (hk : k ≤ n) (w : ComplexModel k) :
    planeProjection k n (planeInclusion k n w) = w := by
  ext i
  simp [planeProjection, planeInclusion, lt_of_lt_of_le i.2 hk]

theorem planeInclusion_planeProjection {k n : ℕ} {z : ComplexModel n}
    (hz : z ∈ complexCoordinatePlane n k) :
    planeInclusion k n (planeProjection k n z) = z := by
  ext i
  by_cases h : i.1 < k
  · simp [planeProjection, planeInclusion, h]
  · simp only [planeInclusion, h, dif_neg, not_false_eq_true]
    exact (hz i (not_lt.mp h)).symm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The patch parametrization maps an open set of parameters onto a relatively open part
of `V`: there is an open `U ⊆ M` containing the image whose trace on `V` lies in the
image. -/
theorem exists_isOpen_carrier_inter_subset_image
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V)
    {Ω : Set (ComplexModel V.dim)} (hΩo : IsOpen Ω) (hΩ : Ω ⊆ P.parameterDomain) :
    ∃ U : Set M, IsOpen U ∧ P.toManifold '' Ω ⊆ U ∧ V.carrier ∩ U ⊆ P.toManifold '' Ω := by
  set d := (complexChartAt (n := n) P.center).val with hd
  set Φ := P.flattening with hΦ
  have hopen : IsOpen (Φ.source ∩ Φ.toFun ⁻¹' (planeProjection V.dim n ⁻¹' Ω)) :=
    Φ.toFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_source
      (hΩo.preimage (continuous_planeProjection V.dim n))
  refine ⟨d.source ∩ d ⁻¹' (Φ.source ∩ Φ.toFun ⁻¹' (planeProjection V.dim n ⁻¹' Ω)),
    d.isOpen_inter_preimage hopen, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨RegularPatch.toManifold_mem_chart_source P (hΩ hw), ?_, ?_⟩
    · rw [RegularPatch.chart_toManifold P (hΩ hw)]
      exact RegularPatch.coordinateParametrization_mem_source P (hΩ hw)
    · rw [RegularPatch.chart_toManifold P (hΩ hw)]
      change planeProjection V.dim n (Φ.toFun (Φ.invFun (planeInclusion V.dim n w))) ∈ Ω
      rw [Φ.right_inv _ (hΩ hw), planeProjection_planeInclusion V.dim_le]
      exact hw
  · rintro y ⟨hyV, hyd, hyΦ, hyΩ⟩
    have hplane := (P.flattens hyd hyΦ).1 hyV
    refine ⟨planeProjection V.dim n (Φ.toFun (d y)), hyΩ, ?_⟩
    change d.symm (Φ.invFun (planeInclusion V.dim n
      (planeProjection V.dim n (Φ.toFun (d y))))) = y
    rw [planeInclusion_planeProjection hplane, Φ.left_inv _ hyΦ, d.left_inv hyd]

/-- The parameters of a regular patch landing in an analytic set that contains no
nonempty relatively open part of `V` form a Lebesgue-null set. -/
theorem volume_parameterDomain_inter_preimage_eq_zero
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A)
    (hV : ∀ U : Set M, IsOpen U → (V.carrier ∩ U).Nonempty → ¬ V.carrier ∩ U ⊆ A) :
    volume (P.parameterDomain ∩ P.toManifold ⁻¹' A) = 0 := by
  set S := P.parameterDomain ∩ P.toManifold ⁻¹' A with hS
  have hint : ∀ Ω : Set (ComplexModel V.dim), IsOpen Ω → Ω.Nonempty →
      Ω ⊆ P.parameterDomain → ¬ Ω ⊆ S := by
    intro Ω hΩo hne hΩ hΩS
    obtain ⟨U, hUo, himU, hVU⟩ := exists_isOpen_carrier_inter_subset_image P hΩo hΩ
    obtain ⟨w, hw⟩ := hne
    refine hV U hUo ⟨P.toManifold w, RegularPatch.toManifold_mem_carrier P (hΩ hw),
      himU ⟨w, hw, rfl⟩⟩ ?_
    intro y hy
    obtain ⟨w', hw', rfl⟩ := hVU hy
    exact (hΩS hw').2
  refine measure_null_of_locally_null S fun w hw => ?_
  obtain ⟨p⟩ := hA (P.toManifold w)
  set x := P.toManifold w with hx
  set e := (complexChartAt (n := n) x).val with he
  set d := (complexChartAt (n := n) P.center).val with hd
  set T := chartTransition (complexChartAt (n := n) P.center) (complexChartAt (n := n) x)
    with hT
  have hTsource : T.source = d.target ∩ d.symm ⁻¹' e.source := by
    simp [hT, chartTransition, hd, he]
  have hTapply : ∀ z, T z = e (d.symm z) := fun z => rfl
  set cP := P.coordinateParametrization with hcP
  set W : Set (ComplexModel V.dim) :=
    P.parameterDomain ∩ cP ⁻¹' (T.source ∩ T ⁻¹' p.coordinateNeighborhood) with hW
  have hcPcont : ContinuousOn cP P.parameterDomain := fun w' hw' =>
    (RegularPatchDerivative.differentiableAt_coordinateParametrization P hw').continuousAt
      |>.continuousWithinAt
  have hWo : IsOpen W :=
    hcPcont.isOpen_inter_preimage (RegularPatchDerivative.isOpen_parameterDomain P)
      (T.isOpen_inter_preimage p.isOpen_coordinateNeighborhood)
  have hwW : w ∈ W := by
    refine ⟨hw.1, ?_, ?_⟩
    · rw [hTsource]
      refine ⟨P.source_subset (RegularPatch.coordinateParametrization_mem_source P hw.1), ?_⟩
      change P.toManifold w ∈ e.source
      exact mem_complexChartAt_source _
    · rw [mem_preimage, hTapply]
      exact p.center_mem_coordinateNeighborhood
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hWo w hwW
  have hzero : ∀ w' ∈ Metric.ball w r,
      (P.toManifold w' ∈ A ↔ ∀ i, p.generator i (T (cP w')) = 0) := by
    intro w' hw'
    have hw'W := hrW hw'
    have hsrc := hw'W.2.1
    rw [hTsource] at hsrc
    exact p.zeroLocus hsrc.2 hw'W.2.2
  have hFd : ∀ i, DifferentiableOn ℂ (fun w' => p.generator i (T (cP w'))) (Metric.ball w r) := by
    intro i
    have hTd : DifferentiableOn ℂ T T.source :=
      differentiableOn_chartTransition _ _
    have hcPd : DifferentiableOn ℂ cP (Metric.ball w r) := fun w' hw' =>
      (RegularPatchDerivative.differentiableAt_coordinateParametrization P
        (hrW hw').1).differentiableWithinAt
    exact (p.generator_holomorphic i).comp (hTd.comp hcPd fun w' hw' => (hrW hw').2.1)
      fun w' hw' => (hrW hw').2.2
  have hex : ∃ i, ∃ w₁ ∈ Metric.ball w r, p.generator i (T (cP w₁)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hint (Metric.ball w r) Metric.isOpen_ball ⟨w, Metric.mem_ball_self hr⟩
      (fun w' hw' => (hrW hw').1) ?_
    intro w' hw'
    exact ⟨(hrW hw').1, (hzero w' hw').2 fun i => hcon i w' hw'⟩
  obtain ⟨i, w₁, hw₁, hne⟩ := hex
  refine ⟨S ∩ Metric.ball w r, inter_mem_nhdsWithin _ (Metric.ball_mem_nhds w hr), ?_⟩
  refine measure_mono_null ?_
    (HolomorphicZeroSetNull.measure_ball_inter_preimage_zero_eq_zero volume (hFd i) hw₁ hne)
  rintro w' ⟨hw'S, hw'b⟩
  exact ⟨hw'b, (hzero w' hw'b).1 hw'S.2 i⟩

end

end SGPT.Foundations.Analysis.Pending.PatchParameterNull
