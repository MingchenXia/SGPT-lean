import SGPT.Foundations.Analysis.Pending.SingularPerronCompactSupport

set_option autoImplicit false

/-! # Actual singular boundary maximum symmetrization -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularPerronSymmetrization

open FirstPass FirstPass.HolomorphicMaps FiniteGeodesicMaximality SingularBoundaryCompetitor
  SingularPerronChartModification SingularPerronCompactSupport

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- Actual imaginary translation pulls back the genuine corrected PSH function. -/
theorem plurisubharmonicOn_imaginary_translate {F : M → ℂ → EReal}
    (e : ComplexChart n M) {ρ : ComplexModel n → ℝ} {W : Set (ComplexModel n)}
    (hpsh : PlurisubharmonicOn (stripChartFunction F e ρ) (geodesicChartDomain W))
    (s : ℝ) :
    PlurisubharmonicOn
      (stripChartFunction (fun x τ => F x (τ + (s : ℂ) * Complex.I)) e ρ)
      (geodesicChartDomain W) := by
  have h := hpsh.comp_affine (ContinuousLinearMap.id ℂ (ComplexModel n × ℂ))
    ((0 : ComplexModel n), (s : ℂ) * Complex.I)
  have heq : (fun p : ComplexModel n × ℂ => stripChartFunction F e ρ
      (((0 : ComplexModel n), (s : ℂ) * Complex.I) +
        ContinuousLinearMap.id ℂ (ComplexModel n × ℂ) p)) =
      stripChartFunction (fun x τ => F x (τ + (s : ℂ) * Complex.I)) e ρ := by
    funext p
    simp only [stripChartFunction, ContinuousLinearMap.id_apply, Prod.fst_add,
      Prod.snd_add, zero_add, add_comm ((s : ℂ) * Complex.I)]
  rw [heq] at h
  refine h.mono fun p hp => ?_
  simp only [mem_preimage, ContinuousLinearMap.id_apply, geodesicChartDomain,
    mem_prod, Prod.fst_add, Prod.snd_add, zero_add]
  exact ⟨hp.1, by simpa using hp.2⟩

variable [IsComplexManifold n M]

/-- Actual compact support and genuine chart transitions produce one common witness for all translates in every chart. -/
theorem boundaryModification_strip_witness
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (hcurve : IsSubgeodesicInterior θ curve) (e : ComplexChart n M)
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction curve e ρ)
      (geodesicChartDomain W))
    {D : Set (ComplexModel n × ℂ)} (hD : IsOpen D)
    (hDc : IsCompact (closure D)) (hDW : closure D ⊆ geodesicChartDomain W)
    {v : ComplexModel n × ℂ → EReal}
    (hv : PlurisubharmonicOn v D) (hvusc : UpperSemicontinuousOn v (closure D))
    (hvu : ∀ p ∈ geodesicChartDomain W ∩ frontier D,
      v p ≤ subgeodesicChartFunction curve e ρ p) :
    ∀ (d : ComplexChart n M) (z : ComplexModel n), z ∈ d.val.target →
      ∃ (V : Set (ComplexModel n)) (σ : ComplexModel n → ℝ),
        z ∈ V ∧ IsSmoothLocalPotential θ d V σ ∧
        ∀ s : ℝ, PlurisubharmonicOn
          (stripChartFunction (fun x τ => boundaryModification curve e ρ D v x
            (τ + (s : ℂ) * Complex.I)) d σ) (geodesicChartDomain V) := by
  have hWt := hρ.2.1
  have hKc := isCompact_manifoldSupport e hDc hDW hWt
  have hKsrc := manifoldSupport_subset_source e hDW hWt
  have hKxW := spatialProjection_subset hDW
  have hlocal := plurisubharmonicOn_corrected_boundaryModification curve e hρ.1 hWt
    ρ hD hpsh hv hvusc hvu
  have htranslate := fun s : ℝ => plurisubharmonicOn_imaginary_translate e hlocal s
  intro d z hz
  by_cases hzK : d.val.symm z ∈ manifoldSupport e D
  · have hxe := hKsrc hzK
    obtain ⟨y, hyK, hy⟩ := hzK
    have hcd : coordinateMap id d e z ∈ W := by
      change e.val (id (d.val.symm z)) ∈ W
      rw [id, ← hy, e.val.right_inv (hWt (hKxW hyK))]
      exact hKxW hyK
    exact ⟨LocalPotentialPullback.potentialDomain id d e W, ρ ∘ coordinateMap id d e,
      ⟨⟨hz, hxe⟩, hcd⟩, (stripWitness_of_chart d e hρ (htranslate 0)).1,
      fun s => (stripWitness_of_chart d e hρ (htranslate s)).2⟩
  · obtain ⟨W₁, ρ₁, hzW₁, hρ₁, hpsh₁⟩ := hcurve.complexified_psh d hz
    let O := d.val.target ∩ d.val.symm ⁻¹' (manifoldSupport e D)ᶜ
    have hO : IsOpen O := d.val.continuousOn_symm.isOpen_inter_preimage
      d.val.open_target hKc.isClosed.isOpen_compl
    have hV : IsOpen (W₁ ∩ O) := hρ₁.1.inter hO
    refine ⟨W₁ ∩ O, ρ₁, ⟨hzW₁, hz, hzK⟩, hρ₁.mono hV inter_subset_left, ?_⟩
    intro s p hp
    refine ((hpsh₁.mono (prod_mono inter_subset_left subset_rfl)) p hp).congr ?_
    filter_upwards [(isOpen_geodesicChartDomain hV).mem_nhds hp] with q hq
    have hnot : ¬ (d.val.symm q.1 ∈ e.val.source ∧
        (e.val (d.val.symm q.1), q.2 + (s : ℂ) * Complex.I) ∈ D) := by
      rintro ⟨hx, hmod⟩
      have hsp : e.val (d.val.symm q.1) ∈ spatialProjection D :=
        ⟨_, subset_closure hmod, rfl⟩
      exact hq.1.2.2 ⟨_, hsp, e.val.left_inv hx⟩
    simp only [stripChartFunction, boundaryModification_eq_outside curve e ρ D v hnot,
      subgeodesicChartFunction, chartFunction]
    congr 2
    simp

omit [IsComplexManifold n M] in
/-- Actual time support forces equality with the original curve near both strip ends. -/
theorem boundaryModification_eq_near_ends (curve : ℝ → M → EReal)
    (e : ComplexChart n M) (ρ : ComplexModel n → ℝ)
    {D : Set (ComplexModel n × ℂ)} (v : ComplexModel n × ℂ → EReal)
    {a b : ℝ} (htime : ∀ p ∈ closure D, a ≤ p.2.re ∧ p.2.re ≤ b)
    (x : M) (τ : ℂ) (hτ : τ.re < a ∨ b < τ.re) :
    boundaryModification curve e ρ D v x τ = curve τ.re x := by
  apply boundaryModification_eq_outside
  rintro ⟨_, hp⟩
  have h := htime _ (subset_closure hp)
  rcases hτ with hτ | hτ
  · exact (not_lt_of_ge h.1) hτ
  · exact (not_lt_of_ge h.2) hτ

/-- The actual boundary modification internally produces every hypothesis of genuine upper-bounded Perron symmetrization. -/
theorem isSubgeodesicFrom_symmetrized_boundaryModification
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ curve u₀ u₁) (e : ComplexChart n M)
    {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction curve e ρ)
      (geodesicChartDomain W))
    {D : Set (ComplexModel n × ℂ)} (hD : IsOpen D)
    (hDc : IsCompact (closure D)) (hDW : closure D ⊆ geodesicChartDomain W)
    (hne : D.Nonempty) {v : ComplexModel n × ℂ → EReal}
    (hv : PlurisubharmonicOn v D) (hvusc : UpperSemicontinuousOn v (closure D))
    (hvu : ∀ p ∈ geodesicChartDomain W ∩ frontier D,
      v p ≤ subgeodesicChartFunction curve e ρ p)
    {C : ℝ} (hC : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, curve t x ≤ (C : EReal)) :
    IsSubgeodesicFrom θ (symmetrizedCurve (boundaryModification curve e ρ D v)) u₀ u₁ := by
  classical
  obtain ⟨a, b, ha, hab, hb, htime⟩ := exists_time_bounds hDc hDW hne
  obtain ⟨ρmin, hρmin⟩ := exists_potential_lower_bound hDc hDW hne
    hρ.2.2.1.continuousOn
  obtain ⟨Cv, hCv⟩ := exists_boundary_competitor_upper_bound hD hpsh hv hvusc hvu hDc hDW
  have hbound : ∀ x τ, τ.re ∈ Ioo (0 : ℝ) 1 →
      boundaryModification curve e ρ D v x τ ≤ ((max C (Cv - ρmin) : ℝ) : EReal) := by
    intro x τ hτ
    by_cases hx : x ∈ e.val.source ∧ (e.val x, τ) ∈ D
    · simp only [boundaryModification, if_pos hx]
      apply max_le
      · exact (hC _ hτ x).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
      · have hm := modification_mem_support e htime hx.1 hx.2
        have hs := EReal.sub_le_sub (hCv _ (subset_closure hx.2))
          (EReal.coe_le_coe_iff.mpr (hρmin _ hm.2.1))
        have hs' : (Cv : EReal) - (ρmin : EReal) ≤ ((max C (Cv - ρmin) : ℝ) : EReal) := by
          rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
          exact le_max_right _ _
        exact hs.trans hs'
    · simp only [boundaryModification, if_neg hx]
      exact (hC _ hτ x).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  exact isSubgeodesicFrom_symmetrizedCurve hsub (boundaryModification_ge curve e ρ D v)
    ha hab hb (boundaryModification_eq_near_ends curve e ρ v htime)
    (boundaryModification_strip_witness hsub.2.2.1 e hρ hpsh hD hDc hDW hv hvusc hvu) hbound

end

end SGPT.Foundations.Analysis.Pending.SingularPerronSymmetrization
