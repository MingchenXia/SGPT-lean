import SGPT.NPP.RelativeNonPluripolarCurrents
import SGPT.NPP.NonPluripolarCurrent4Opens

/-! Body-preserving consolidation PLAN ONLY. Fresh proper-name checking is
required; private flat objects are provenance, never providers for this file. -/

-- Exact frozen body: RelativeSourceMassDraft
section OriginalFragment_01

/-! The literal relative extension of the source connected-open/smooth-positive
form mass condition, equivalent to the SAME actual compact uniform trace mass. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology Distributions ContDiff ENNReal
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
open LocalBedfordTaylorLocality LocalBedfordTaylorCalculus
open SGPT.NPP.NonPluripolarCurrent
variable {n p r : ℕ} {U : Opens (ComplexModel n)}
local notation "E" => ComplexModel n

/-- ALL original connected open subdomains, ALL original smooth semipositive
forms and ALL compact subsets, evaluated on the SAME actual relative currents. -/
def IsRelativeWellDefinedOn (T : LocalProductCurrent n U (r + p))
    (φ : Fin p → E → EReal) : Prop :=
  ∀ (V : Opens E) (hVU : V ≤ U), IsConnected (V : Set E) →
    ∀ α : E → RealForm n 2, ContDiffOn ℝ ∞ α V → (∀ x ∈ V, IsSemipositiveOneOne (α x)) →
      ∀ K : Set E, IsCompact K → K ⊆ V →
        ⨆ k, wedgePowerMeasure (restrict hVU (relativeTruncatedBT U φ T k)) α
          (K ∩ BedfordTaylorTopDegree.strictLocus U φ k) < ⊤

/-- The literal source quantifiers agree with the actual original relative
compact uniform trace condition. The original base may charge pluripolar sets. -/
theorem isRelativeWellDefinedOn_iff
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (φ : Fin p → E → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) :
    IsRelativeWellDefinedOn T φ ↔ HasFiniteRelativeMass T hT hTc φ hφ := by
  let hF := isTruncationFamily_relative T hT hTc φ hφ
  let O := BedfordTaylorTopDegree.strictLocus U φ
  change IsRelativeWellDefinedOn T φ ↔
    ∀ K : Set E, IsCompact K → K ⊆ U → ⨆ k, (hF.isPositive k).traceMeasure (K ∩ O k) < ⊤
  have hres : ∀ (V : Opens E) (hVU : V ≤ U) (k : ℕ) (A : Set E), MeasurableSet A → A ⊆ V →
      (LocalBedfordTaylorLocality.isPositive_restrict (hF.isPositive k) hVU).traceMeasure A =
        (hF.isPositive k).traceMeasure A := fun V hVU k A hA hAV => by
    rw [LocalBedfordTaylorLocality.traceMeasure_restrict, Measure.restrict_apply hA,
      inter_eq_left.mpr hAV]
  constructor
  · intro hW K hK hKU
    have hε : ∀ x : E, ∃ ε > (0 : ℝ), x ∈ U → Metric.ball x ε ⊆ U := fun x => by
      by_cases hx : x ∈ U
      · obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.mp U.isOpen x hx
        exact ⟨ε, hε, fun _ => h⟩
      · exact ⟨1, one_pos, fun h => absurd h hx⟩
    choose ε hεpos hεU using hε
    obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun x => Metric.closedBall x (ε x / 2))
      fun x _ => Metric.closedBall_mem_nhds x (half_pos (hεpos x))
    let V : E → Opens E := fun x => ⟨Metric.ball x (ε x), Metric.isOpen_ball⟩
    have hVU : ∀ x ∈ t, V x ≤ U := fun x hx => hεU x (hKU (htK x hx))
    have hKV : ∀ x, K ∩ Metric.closedBall x (ε x / 2) ⊆ V x := fun x y hy =>
      Metric.closedBall_subset_ball (half_lt_self (hεpos x)) hy.2
    have hKc : ∀ x, IsCompact (K ∩ Metric.closedBall x (ε x / 2)) := fun x =>
      hK.inter_right Metric.isClosed_closedBall
    have hbound : ∀ x (hx : x ∈ t), ⨆ k, (hF.isPositive k).traceMeasure
        (K ∩ Metric.closedBall x (ε x / 2) ∩ O k) < ⊤ := fun x hx => by
      have h := hW (V x) (hVU x hx) ((convex_ball x (ε x)).isConnected
        (Metric.nonempty_ball.mpr (hεpos x))) (fun _ => kahlerForm n) contDiffOn_const
        (fun _ _ => isSemipositiveOneOne_kahlerForm) _ (hKc x) (hKV x)
      simp_rw [wedgePowerMeasure_kahlerForm (LocalBedfordTaylorLocality.isPositive_restrict
        (hF.isPositive _) (hVU x hx))] at h
      refine lt_of_le_of_lt (iSup_mono fun k => ?_) h
      rw [hres (V x) (hVU x hx) k _ ((hKc x).measurableSet.inter (hF.measurableSet k))
        (inter_subset_left.trans (hKV x))]
    refine lt_of_le_of_lt (iSup_le fun k => ?_) (ENNReal.sum_lt_top.mpr fun x hx =>
      hbound x hx)
    have hsub : K ∩ O k ⊆ ⋃ x ∈ t, K ∩ Metric.closedBall x (ε x / 2) ∩ O k := by
      rintro y ⟨hyK, hyO⟩
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hKt hyK)
      exact mem_iUnion₂.mpr ⟨x, hx, ⟨hyK, hyx⟩, hyO⟩
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun x hx => le_iSup (fun k => (hF.isPositive k).traceMeasure
        (K ∩ Metric.closedBall x (ε x / 2) ∩ O k)) k))
  · intro hm V hVU _ α hαs hαp K hK hKV
    obtain ⟨c, -, hc⟩ := exists_smul_kahlerForm_sub hK (hαs.continuousOn.mono hKV)
      fun x hx => (hαp x (hKV hx)).1
    have hle : ∀ k, wedgePowerMeasure (LocalBedfordTaylorLocality.restrict hVU
        (relativeTruncatedBT U φ T k)) α (K ∩ O k) ≤
          ENNReal.ofReal (c ^ r) * (hF.isPositive k).traceMeasure (K ∩ O k) := fun k => by
      refine (wedgePowerMeasure_le (LocalBedfordTaylorLocality.isPositive_restrict
        (hF.isPositive k) hVU) hK.measurableSet (hF.measurableSet k)
        (fun x hx => hαp x (hKV hx)) hc).trans ?_
      rw [hres V hVU k _ (hK.measurableSet.inter (hF.measurableSet k))
        (inter_subset_left.trans hKV)]
    refine lt_of_le_of_lt (iSup_le fun k => (hle k).trans
      (mul_le_mul_of_nonneg_left (le_iSup (fun k => (hF.isPositive k).traceMeasure (K ∩ O k)) k)
        (zero_le)))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hm K hK (hKV.trans hVU)))

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeWellDefinedOn
#check @SGPT.NPP.RelativeNonPluripolar.isRelativeWellDefinedOn_iff
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeWellDefinedOn
#print axioms SGPT.NPP.RelativeNonPluripolar.isRelativeWellDefinedOn_iff

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_01

-- Exact frozen body: RelativeOrderingDraft
section OriginalFragment_02

/-! Genuine symmetry of actual relative mass/current and original intrinsic
current factors. The SAME arbitrary original closed positive base is retained. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentL1Ddc
open SGPT.NPP.NonPluripolarCurrent

/-- Symmetry of the SAME actual relative BT truncations and original strict
loci; no tuple of output currents or permutation equality is supplied. -/
theorem relativeTruncation_comp_perm {n p r : ℕ} {U : Opens (ComplexModel n)}
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (φ : Fin p → ComplexModel n → EReal) (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (σ : Equiv.Perm (Fin p)) :
    relativeTruncatedBT U (φ ∘ σ) T = relativeTruncatedBT U φ T ∧
      BedfordTaylorTopDegree.strictLocus U (φ ∘ σ) = BedfordTaylorTopDegree.strictLocus U φ := by
  constructor
  · funext k
    exact btProduct_comp_perm p r T hT hTc (fun i => truncationReal (φ i) k)
      (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k) σ
  · funext k
    ext x
    simp only [BedfordTaylorTopDegree.strictLocus,mem_ofPred_eq,Function.comp_apply]
    exact ⟨fun ⟨hx,hv⟩ => ⟨hx,fun i => by simpa using hv (σ.symm i)⟩,
      fun ⟨hx,hv⟩ => ⟨hx,fun i => hv (σ i)⟩⟩

/-- Ordering preserves actual finite relative mass and the SAME genuine
relative current in all ambient and tuple/base degrees, including zero. -/
theorem relative_product_comp_perm {n p r : ℕ} {U : Opens (ComplexModel n)}
    (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (φ : Fin p → ComplexModel n → EReal) (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (σ : Equiv.Perm (Fin p)) :
    (HasFiniteRelativeMass T hT hTc (φ ∘ σ) (fun i => hφ (σ i)) ↔
      HasFiniteRelativeMass T hT hTc φ hφ) ∧
    ∀ (hmσ : HasFiniteRelativeMass T hT hTc (φ ∘ σ) (fun i => hφ (σ i)))
      (hm : HasFiniteRelativeMass T hT hTc φ hφ),
      (relativeNonPluripolarProduct T hT hTc (φ ∘ σ) (fun i => hφ (σ i)) hmσ).val =
        (relativeNonPluripolarProduct T hT hTc φ hφ hm).val := by
  have h := relativeTruncation_comp_perm T hT hTc φ hφ σ
  have he : truncAt (relativeTruncatedBT U (φ ∘ σ) T) (BedfordTaylorTopDegree.strictLocus U (φ ∘ σ)) =
      truncAt (relativeTruncatedBT U φ T) (BedfordTaylorTopDegree.strictLocus U φ) := by
    rw [h.1,h.2]
  refine ⟨?_,?_⟩
  · calc
      HasFiniteRelativeMass T hT hTc (φ ∘ σ) (fun i => hφ (σ i)) ↔
          ∃ S, LocalBedfordTaylorContinuity.WeakTendsto
            (truncAt (relativeTruncatedBT U (φ ∘ σ) T) (BedfordTaylorTopDegree.strictLocus U (φ ∘ σ))) S :=
        hasFiniteRelativeMass_iff_exists_weak_limit T hT hTc (φ ∘ σ) (fun i => hφ (σ i))
      _ ↔ ∃ S, LocalBedfordTaylorContinuity.WeakTendsto
          (truncAt (relativeTruncatedBT U φ T) (BedfordTaylorTopDegree.strictLocus U φ)) S := by rw [he]
      _ ↔ HasFiniteRelativeMass T hT hTc φ hφ :=
        (hasFiniteRelativeMass_iff_exists_weak_limit T hT hTc φ hφ).symm
  · intro hmσ hm
    have hconv := weakTendsto_relativeTruncations T hT hTc (φ ∘ σ) (fun i => hφ (σ i)) hmσ
    rw [he] at hconv
    ext γ ψ
    exact tendsto_nhds_unique (hconv γ ψ) (weakTendsto_relativeTruncations T hT hTc φ hφ hm γ ψ)

variable {m p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

/-- The ORIGINAL potential cover and actual masses internally produce the
permuted source data for the same original current factors and base B. -/
theorem isRelativeCurrentProductWellDefined_comp_perm
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) (hW : IsRelativeCurrentProductWellDefined B hBc T)
    (σ : Equiv.Perm (Fin p)) : IsRelativeCurrentProductWellDefined B hBc (T ∘ σ) := by
  obtain ⟨C,hC,hdata⟩ := hW
  refine ⟨C,hC,fun O hO => ?_⟩
  obtain ⟨φ,hφ,hm⟩ := hdata O hO
  have hp : IsLocalPotential (T ∘ σ) O (φ ∘ σ) :=
    ⟨fun i => hφ.psh (σ i),fun i => hφ.ddc (σ i)⟩
  refine ⟨φ ∘ σ,hp,fun e => ?_⟩
  exact (relative_product_comp_perm (restrict (chartDomain_le e O) (B.inChart e))
    (isPositive_restrict (B.isPositive e) (chartDomain_le e O))
    (isClosedAny_restrict (hBc e) (chartDomain_le e O))
    (fun i z => φ i (e.val.symm z)) (hφ.chartPsh e) σ).1.mpr (hm e)

/-- Original-current relative well-definedness is independent of ordering. -/
theorem isRelativeCurrentProductWellDefined_comp_perm_iff
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) (σ : Equiv.Perm (Fin p)) :
    IsRelativeCurrentProductWellDefined B hBc (T ∘ σ) ↔ IsRelativeCurrentProductWellDefined B hBc T := by
  constructor
  · intro hW
    simpa only [Function.comp_def,Equiv.apply_symm_apply] using
      isRelativeCurrentProductWellDefined_comp_perm B hBc (T ∘ σ) hW σ.symm
  · intro hW
    exact isRelativeCurrentProductWellDefined_comp_perm B hBc T hW σ

/-- The SAME genuine intrinsic relative current is independent of factor
ordering. Actual original potential readbacks and local symmetry prove the
equality; no output permutation-equality certificate is supplied. -/
theorem relativeCurrentProduct_comp_perm
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) (σ : Equiv.Perm (Fin p))
    (hW : IsRelativeCurrentProductWellDefined B hBc T)
    (hWσ : IsRelativeCurrentProductWellDefined B hBc (T ∘ σ)) :
    relativeCurrentProduct B hBc (T ∘ σ) hWσ = relativeCurrentProduct B hBc T hW := by
  apply eq_relativeCurrentProduct B hBc T hW hW.cover_spec hW.pot hW.potential hW.potMass
  intro O e
  have hp : IsLocalPotential (T ∘ σ) O.1 (hW.pot O ∘ σ) :=
    ⟨fun i => (hW.potential O).psh (σ i),fun i => (hW.potential O).ddc (σ i)⟩
  obtain ⟨hm,hread⟩ := relativeCurrentProduct_restrict B hBc (T ∘ σ) hWσ hp
  exact (hread e).trans ((relative_product_comp_perm (restrict (chartDomain_le e O.1) (B.inChart e))
    (isPositive_restrict (B.isPositive e) (chartDomain_le e O.1))
    (isClosedAny_restrict (hBc e) (chartDomain_le e O.1))
    (fun i z => hW.pot O i (e.val.symm z)) ((hW.potential O).chartPsh e) σ).2 (hm e) (hW.potMass O e))

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.relativeTruncation_comp_perm
#check @SGPT.NPP.RelativeNonPluripolar.relative_product_comp_perm
#check @SGPT.NPP.RelativeNonPluripolar.isRelativeCurrentProductWellDefined_comp_perm
#check @SGPT.NPP.RelativeNonPluripolar.isRelativeCurrentProductWellDefined_comp_perm_iff
#check @SGPT.NPP.RelativeNonPluripolar.relativeCurrentProduct_comp_perm
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeTruncation_comp_perm
#print axioms SGPT.NPP.RelativeNonPluripolar.relative_product_comp_perm
#print axioms SGPT.NPP.RelativeNonPluripolar.isRelativeCurrentProductWellDefined_comp_perm
#print axioms SGPT.NPP.RelativeNonPluripolar.isRelativeCurrentProductWellDefined_comp_perm_iff
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeCurrentProduct_comp_perm

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_02

-- Exact frozen body: PositiveCurrentOpensDraft
section OriginalFragment_03

/-! Exact restriction of ORIGINAL positive coefficient currents to arbitrary
open submanifolds, retaining original tensor-test pullback and closedness. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending LocalProductCurrents LocalBedfordTaylorProducts
open LocalBedfordTaylorLocality LocalBedfordTaylorCalculus LocalCurrentPullback
open LocalCurrentPullbackDdc BedfordTaylor
open SGPT.NPP.NonPluripolarCurrent

/-- Genuine positive-current pullbacks agree when their actual inverse maps
agree on the ORIGINAL target domain, by the actual inverse-tensor-test integral. -/
theorem pullback_eq_of_inverse_eqOn {n q : ℕ} {A B : Opens (ComplexModel n)}
    {τ σ τ' σ' : ComplexModel n → ComplexModel n}
    (h : IsBiholomorphicPair A B τ σ) (h' : IsBiholomorphicPair A B τ' σ')
    {T : LocalProductCurrent n B q} (hT : IsPositive T) (he : EqOn σ σ' B) :
    pullback h hT = pullback h' hT := by
  ext γ φ
  rw [pullback_apply h hT,pullback_apply h' hT]
  apply setIntegral_congr_fun B.isOpen.measurableSet
  intro y hy
  have hnear : σ =ᶠ[𝓝 y] σ' := Filter.eventually_of_mem (B.isOpen.mem_nhds hy) fun z hz => he hz
  change φ (σ y) * LocalCurrentLebesgue.densityForm hT y (pullSpan q (fderiv ℂ σ y) γ) =
    φ (σ' y) * LocalCurrentLebesgue.densityForm hT y (pullSpan q (fderiv ℂ σ' y) γ)
  rw [he hy,hnear.fderiv_eq]

/-- Actual pullback restriction to an ORIGINAL biholomorphic subpair, with
the source-domain equality and all base restrictions manufactured internally. -/
theorem pullback_restrict_of_subpair {n q : ℕ}
    {A B A₀ B₀ : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}
    (h₀ : IsBiholomorphicPair A₀ B₀ τ σ) (h : IsBiholomorphicPair A B τ σ)
    (hAA : A ≤ A₀) (hBB : B ≤ B₀) {T : LocalProductCurrent n B₀ q} (hT : IsPositive T) :
    pullback h (isPositive_restrict hT hBB) = restrict hAA (pullback h₀ hT) := by
  have hpre : preOpen h₀ B = A := by
    ext x
    change (x ∈ A₀ ∧ τ x ∈ B) ↔ x ∈ A
    constructor
    · rintro ⟨hx,hτx⟩
      have hs := h.mapsTo_inv hτx
      rwa [h₀.left_inv x hx] at hs
    · intro hx
      exact ⟨hAA hx,h.mapsTo hx⟩
  cases hpre
  exact pullback_restrict h₀ hT hBB

variable {m q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

omit [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M] in
private theorem opens_transition_eq_ambient (U : Opens M)
    (e f : ComplexChart (m + 1) U) {x : ComplexModel (m + 1)} (hx : x ∈ overlapSource e f) :
    chartTransition e f x = chartTransition (ambientChart U e) (ambientChart U f) x := by
  change f.val (e.val.symm x) = (ambientChart U f).val ((ambientChart U e).val.symm x)
  rw [apply_eq_ambient U f,coe_symm_eq_ambient U e (overlapSource_le e f hx)]

omit [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M] in
private theorem opens_inverse_transition_eq_ambient (U : Opens M)
    (e f : ComplexChart (m + 1) U) {y : ComplexModel (m + 1)} (hy : y ∈ overlapTarget e f) :
    (chartTransition e f).symm y = (chartTransition (ambientChart U e) (ambientChart U f)).symm y := by
  change e.val (f.val.symm y) = (ambientChart U e).val ((ambientChart U f).val.symm y)
  rw [apply_eq_ambient U e,coe_symm_eq_ambient U f (overlapTarget_le e f hy)]

omit [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M] in
private theorem opens_overlapSource_le_ambient (U : Opens M) (e f : ComplexChart (m + 1) U) :
    overlapSource e f ≤ overlapSource (ambientChart U e) (ambientChart U f) := by
  intro x hx
  have hx' : x ∈ (chartTransition e f).source := hx
  simp only [chartTransition,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
    mem_inter_iff,mem_preimage] at hx'
  change x ∈ (ambientChart U e).val.target ∧
    (ambientChart U e).val.symm x ∈ (ambientChart U f).val.source
  have hs := mem_ambientChart_source U f hx'.2
  rw [coe_symm_eq_ambient U e hx'.1] at hs
  exact ⟨chartTarget_le_ambient U e hx'.1,hs⟩

/-- The SAME original positive current on the genuine open submanifold U.
All induced-chart compatibility is manufactured from original base overlap. -/
def positiveCurrentOnOpens (B : PositiveCurrent (m + 1) M q) (U : Opens M) :
    PositiveCurrent (m + 1) U q where
  inChart e := restrict (chartTarget_le_ambient U e) (B.inChart (ambientChart U e))
  isPositive e := isPositive_restrict (B.isPositive (ambientChart U e)) (chartTarget_le_ambient U e)
  compatible e f := by
    let E := ambientChart U e
    let F := ambientChart U f
    let h₀ := chartTransition_isBiholomorphicPair E F
    let hO := chartTransition_isBiholomorphicPair e f
    have hAA : overlapSource e f ≤ overlapSource E F := opens_overlapSource_le_ambient U e f
    have hBB : overlapTarget e f ≤ overlapTarget E F := by
      exact opens_overlapSource_le_ambient U f e
    have hsub : IsBiholomorphicPair (overlapSource e f) (overlapTarget e f)
        (chartTransition E F) (chartTransition E F).symm := {
      holo := h₀.holo.mono hAA
      holo_inv := h₀.holo_inv.mono hBB
      mapsTo := fun x hx => by
        rw [← opens_transition_eq_ambient U e f hx]
        exact hO.mapsTo hx
      mapsTo_inv := fun y hy => by
        rw [← opens_inverse_transition_eq_ambient U e f hy]
        exact hO.mapsTo_inv hy
      left_inv := fun x hx => h₀.left_inv x (hAA hx)
      right_inv := fun y hy => h₀.right_inv y (hBB hy) }
    calc
      restrict (overlapSource_le e f) (restrict (chartTarget_le_ambient U e) (B.inChart E)) =
        restrict hAA (restrict (overlapSource_le E F) (B.inChart E)) := by
          simp only [restrict_restrict]
      _ = restrict hAA (pullback h₀ (isPositive_restrict (B.isPositive F) (overlapTarget_le E F))) :=
        congrArg (restrict hAA) (B.compatible E F)
      _ = pullback hsub (isPositive_restrict
          (isPositive_restrict (B.isPositive F) (overlapTarget_le E F)) hBB) :=
        (pullback_restrict_of_subpair h₀ hsub hAA hBB
          (isPositive_restrict (B.isPositive F) (overlapTarget_le E F))).symm
      _ = pullback hsub (isPositive_restrict
          (isPositive_restrict (B.isPositive F) (chartTarget_le_ambient U f)) (overlapTarget_le e f)) :=
        pullback_congr_current hsub _ _ (by simp only [restrict_restrict])
      _ = pullback hO (isPositive_restrict
          (isPositive_restrict (B.isPositive F) (chartTarget_le_ambient U f)) (overlapTarget_le e f)) :=
        (pullback_eq_of_inverse_eqOn hO hsub _
          (fun y hy => opens_inverse_transition_eq_ambient U e f hy)).symm

/-- EVERY induced chart retains its exact ORIGINAL ambient scalar/tensor values. -/
theorem positiveCurrentOnOpens_inChart (B : PositiveCurrent (m + 1) M q) (U : Opens M)
    (e : ComplexChart (m + 1) U) :
    (positiveCurrentOnOpens B U).inChart e =
      restrict (chartTarget_le_ambient U e) (B.inChart (ambientChart U e)) := rfl

/-- Original global closedness survives arbitrary open restriction in every degree. -/
theorem isClosed_positiveCurrentOnOpens (B : PositiveCurrent (m + 1) M q) (hBc : B.IsClosed)
    (U : Opens M) : (positiveCurrentOnOpens B U).IsClosed := fun e =>
  isClosedAny_restrict (hBc (ambientChart U e)) (chartTarget_le_ambient U e)

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.pullback_eq_of_inverse_eqOn
#check @SGPT.NPP.RelativeNonPluripolar.pullback_restrict_of_subpair
#check @SGPT.NPP.RelativeNonPluripolar.positiveCurrentOnOpens
#check @SGPT.NPP.RelativeNonPluripolar.positiveCurrentOnOpens_inChart
#check @SGPT.NPP.RelativeNonPluripolar.isClosed_positiveCurrentOnOpens
#print axioms SGPT.NPP.RelativeNonPluripolar.pullback_eq_of_inverse_eqOn
#print axioms SGPT.NPP.RelativeNonPluripolar.pullback_restrict_of_subpair
#print axioms SGPT.NPP.RelativeNonPluripolar.positiveCurrentOnOpens
#print axioms SGPT.NPP.RelativeNonPluripolar.positiveCurrentOnOpens_inChart
#print axioms SGPT.NPP.RelativeNonPluripolar.isClosed_positiveCurrentOnOpens

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_03

-- Exact frozen body: RelativeGlobalBTTruncationsDraft
section OriginalFragment_04

/-! Actual UNWEIGHTED globally compatible relative BT truncations, needed by
the literal full source integral on K intersect O_k for arbitrary open domains. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor
open SGPT.NPP.NonPluripolarCurrent
variable {n p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

/-- Every actual UNWEIGHTED bounded truncation is a globally compatible positive current.
The only base data is the ORIGINAL global positive closed T; its other-chart
closedness manufactures actual pullback-closedness on every overlap. -/
def relativeGlobalBTTruncations (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (k : ℕ) : PositiveCurrent n M r where
  inChart e := relativeTruncatedBT (chartTarget e)
    (fun i z => φ i (e.val.symm z)) (T.inChart e) k
  isPositive e := (isTruncationFamily_relative (T.inChart e) (T.isPositive e) (hTc e)
    (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e)).isPositive k
  compatible e f := by
    have hh := chartTransition_isBiholomorphicPair e f
    have hAe := overlapSource_le e f
    have hBf := overlapTarget_le e f
    let TB := restrict hBf (T.inChart f)
    have hTB : IsPositive TB := isPositive_restrict (T.isPositive f) hBf
    have hTBc : IsClosedAny (r + p) TB := isClosedAny_restrict (hTc f) hBf
    have hcomp : restrict hAe (T.inChart e) = pullback hh hTB := T.compatible e f
    have hTBpc : IsClosedAny (r + p) (pullback hh hTB) := by
      rw [← hcomp]
      exact isClosedAny_restrict (hTc e) hAe
    have hφB : ∀ i, PlurisubharmonicOn (fun z => φ i (f.val.symm z)) (overlapTarget e f) :=
      fun i => (chartPlurisubharmonicOn hφ f i).mono hBf
    have eB := relativeTruncatedBT_restrict (T.inChart f) (T.isPositive f) (hTc f)
      (fun i z => φ i (f.val.symm z)) (chartPlurisubharmonicOn hφ f) hBf k
    rw [← relativeTruncatedBT_restrict (T.inChart e) (T.isPositive e) (hTc e)
      (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e) hAe k,
      pullback_congr_current hh _
        ((isTruncationFamily_relative TB hTB hTBc
          (fun i z => φ i (f.val.symm z)) hφB).isPositive k) eB.symm,
      relativeTruncatedBT_pullback hh TB hTB hTBc hTBpc
        (fun i z => φ i (f.val.symm z)) hφB k, ← hcomp]
    apply LocalBedfordTaylorDecreasing.btProduct_congr p r _ _ _
    intro i x hx
    have hx' : x ∈ (chartTransition e f).source := hx
    have hxf : e.val.symm x ∈ f.val.source := by
      simp only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage] at hx'
      exact hx'.2
    unfold truncationReal truncation
    simp only [chartTransition, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      f.val.left_inv hxf]

/-- Exact ORIGINAL local unweighted relative BT-current readback. -/
theorem relativeGlobalBTTruncations_inChart
    (T : PositiveCurrent n M (r + p)) (hTc : T.IsClosed)
    (φ : Fin p → M → EReal) (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))
    (k : ℕ) (e : ComplexChart n M) :
    (relativeGlobalBTTruncations T hTc φ hφ k).inChart e =
      relativeTruncatedBT (chartTarget e) (fun i z => φ i (e.val.symm z)) (T.inChart e) k := rfl
end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.relativeGlobalBTTruncations
#check @SGPT.NPP.RelativeNonPluripolar.relativeGlobalBTTruncations_inChart
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeGlobalBTTruncations
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeGlobalBTTruncations_inChart

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_04

-- Exact frozen body: RelativeGlobalSourceMassDraft
section OriginalFragment_05

/-! The literal L69 relative mass criterion on ALL connected opens of the
ORIGINAL manifold, with ALL original smooth forms and compact subsets. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
open LocalBedfordTaylorLocality LocalBedfordTaylorCalculus LocalCurrentPullback
open LocalCurrentPullbackDdc BedfordTaylor
open SGPT.NPP.NonPluripolarCurrent
variable {n p q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] [MeasurableSpace M] [BorelSpace M] [T2Space M]
variable (B : PositiveCurrent n M (q + p)) (hBc : B.IsClosed)

/-- The LITERAL relative extension of original L69: ALL connected opens U
of the original manifold, ALL smooth semipositive forms on U, ALL compact K
inside U; actual intrinsic relative unweighted BT currents on K intersect O_k. -/
def IsRelativeWellDefinedOnGlobalOpens (φ : Fin p → M → EReal)
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) : Prop :=
  ∀ U : Opens M, IsConnected (U : Set M) → ∀ θ : SemipositiveFormOn n U,
    ∀ (K : Set M) (hK : IsCompact K), K ⊆ U →
      ⨆ k, wedgeMeasureOn (relativeGlobalBTTruncations B hBc φ hφ k) θ hK (strictLocusM φ k) < ⊤

variable {φ : Fin p → M → EReal} (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i))

omit [T2Space M] in
theorem chartWedgeMeasure_relative_trunc_le {U : Opens M} (θ : SemipositiveFormOn n U)
    (e : ComplexChart n M) (z₀ : ComplexModel n) (r : ℝ) (k : ℕ) :
    chartWedgeMeasure (relativeGlobalBTTruncations B hBc φ hφ k) θ e
        ((e.val.source ∩ e.val ⁻¹' Metric.ball z₀ (r / 2)) ∩ strictLocusM φ k) ≤
      wedgePowerMeasure ((relativeGlobalBTTruncations B hBc φ hφ k).inChart e) (θ.coeff e)
        (Metric.closedBall z₀ (r / 2) ∩
          BedfordTaylorTopDegree.strictLocus (chartTarget e) (fun i z => φ i (e.val.symm z)) k) := by
  have hWm : MeasurableSet ((e.val.source ∩ e.val ⁻¹' Metric.ball z₀ (r / 2)) ∩ strictLocusM φ k) :=
    ((e.val.continuousOn.isOpen_inter_preimage e.val.open_source
      Metric.isOpen_ball).measurableSet).inter (measurableSet_strictLocusM hφ k)
  have hCm : MeasurableSet (Metric.closedBall z₀ (r / 2) ∩
      BedfordTaylorTopDegree.strictLocus (chartTarget e) (fun i z => φ i (e.val.symm z)) k) :=
    Metric.isClosed_closedBall.measurableSet.inter
      (BedfordTaylorTopDegree.measurableSet_strictLocus (chartPlurisubharmonicOn hφ e) k)
  rw [chartWedgeMeasure_apply _ θ e hWm]
  refine measure_mono fun w hw => ?_
  obtain ⟨⟨⟨-, hw1⟩, hw2⟩, hwD⟩ := hw
  have hwt : w ∈ e.val.target := hwD.1
  rw [chartInv_of_mem hwt] at hw1 hw2
  rw [mem_preimage, e.val.right_inv hwt] at hw1
  exact ⟨Metric.ball_subset_closedBall hw1, hwt, fun i => hw2 i⟩

/-- **The chart condition implies the source condition**: if `eq:welldefinepluri` holds in
coordinates in every chart (`IsNonPluripolarWellDefined`), it holds for all connected open
`U ⊆ M`, forms on `U` and compact `K ⊆ U`. -/
theorem relative_global_source_mass_of_chart (hW : HasFiniteGlobalRelativeMass B hBc φ hφ) :
    IsRelativeWellDefinedOnGlobalOpens B hBc φ hφ := by
  have hSource (e : ComplexChart n M) : IsRelativeWellDefinedOn (B.inChart e)
      (fun i z => φ i (e.val.symm z)) :=
    (isRelativeWellDefinedOn_iff (B.inChart e) (B.isPositive e) (hBc e)
      (fun i z => φ i (e.val.symm z)) (chartPlurisubharmonicOn hφ e)).mpr (hW e)
  intro U _ θ K hK hKU
  have hloc : ∀ x ∈ K, ∃ r > (0 : ℝ),
      Metric.ball ((complexChartAt (n := n) x).val x) r ⊆
        (chartDomain (complexChartAt (n := n) x) U : Set (ComplexModel n)) := by
    intro x hx
    have hmem : (complexChartAt (n := n) x).val x ∈ chartDomain (complexChartAt x) U :=
      ⟨(complexChartAt x).val.map_source (mem_complexChartAt_source x), by
        rw [mem_preimage, (complexChartAt x).val.left_inv (mem_complexChartAt_source x)]
        exact hKU hx⟩
    exact Metric.isOpen_iff.mp (chartDomain _ U).isOpen _ hmem
  choose! r hr hball using hloc
  set W : M → Set M := fun x => (complexChartAt (n := n) x).val.source ∩
    (complexChartAt (n := n) x).val ⁻¹' Metric.ball ((complexChartAt (n := n) x).val x) (r x / 2)
  have hWn : ∀ x ∈ K, W x ∈ 𝓝 x := fun x hx =>
    ((complexChartAt (n := n) x).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_source Metric.isOpen_ball).mem_nhds
      ⟨mem_complexChartAt_source x, Metric.mem_ball_self (half_pos (hr x hx))⟩
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover W hWn
  -- the local bounds
  have hbound : ∀ x ∈ t, ⨆ k, wedgePowerMeasure
      ((relativeGlobalBTTruncations B hBc φ hφ k).inChart (complexChartAt (n := n) x))
      (θ.coeff (complexChartAt x))
      (Metric.closedBall ((complexChartAt (n := n) x).val x) (r x / 2) ∩
        BedfordTaylorTopDegree.strictLocus (chartTarget (complexChartAt (n := n) x))
          (fun i z => φ i ((complexChartAt (n := n) x).val.symm z)) k) < ⊤ := by
    intro x hx
    have hxK := htK x hx
    set e := complexChartAt (n := n) x
    have hVe : (⟨Metric.ball (e.val x) (r x), Metric.isOpen_ball⟩ : Opens (ComplexModel n)) ≤
        chartTarget e := fun z hz => (chartDomain_le _ U) (hball x hxK hz)
    have h := hSource e ⟨Metric.ball _ (r x), Metric.isOpen_ball⟩ hVe
      ((convex_ball _ _).isConnected (Metric.nonempty_ball.mpr (hr x hxK)))
      (θ.coeff _) ((θ.smooth _).mono (hball x hxK))
      (fun z hz => θ.semipositive _ z (hball x hxK hz)) _ (isCompact_closedBall _ _)
      (Metric.closedBall_subset_ball (half_lt_self (hr x hxK)))
    refine lt_of_le_of_lt (le_of_eq (iSup_congr fun k => ?_)) h
    rw [wedgePowerMeasure_restrict (T := relativeTruncatedBT (chartTarget e)
        (fun i z => φ i (e.val.symm z)) (B.inChart e) k) ((relativeGlobalBTTruncations B hBc φ hφ k).isPositive e) hVe,
      Measure.restrict_apply (Metric.isClosed_closedBall.measurableSet.inter
        (BedfordTaylorTopDegree.measurableSet_strictLocus (chartPlurisubharmonicOn hφ e) k))]
    congr 1
    refine (inter_eq_left.mpr ?_).symm
    exact inter_subset_left.trans (Metric.closedBall_subset_ball (half_lt_self (hr x hxK)))
  refine lt_of_le_of_lt (iSup_le fun k => ?_) (ENNReal.sum_lt_top.mpr hbound)
  set μ := wedgeMeasureOn (relativeGlobalBTTruncations B hBc φ hφ k) θ hK
  have hμK : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem
    ((measure_eq_zero_iff_ae_notMem.mp (wedgeMeasureOn_compl _ θ hK)).mono fun x hx => by
      simpa using hx)
  calc μ (strictLocusM φ k) = μ (strictLocusM φ k ∩ K) := by
        conv_lhs => rw [← hμK]
        rw [Measure.restrict_apply' hK.isClosed.measurableSet]
    _ ≤ μ (⋃ x ∈ t, W x ∩ strictLocusM φ k) := by
        refine measure_mono fun y hy => ?_
        obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hKt hy.2)
        exact mem_iUnion₂.mpr ⟨x, hx, hyx, hy.1⟩
    _ ≤ ∑ x ∈ t, μ (W x ∩ strictLocusM φ k) := measure_biUnion_finset_le _ _
    _ ≤ _ := Finset.sum_le_sum fun x hx => by
        refine (wedgeMeasureOn_le_chart _ θ hK (complexChartAt x)
          (inter_subset_left.trans inter_subset_left)).trans ?_
        exact (chartWedgeMeasure_relative_trunc_le B hBc hφ θ _ _ (r x) k).trans
          (le_iSup (fun k => wedgePowerMeasure
            ((relativeGlobalBTTruncations B hBc φ hφ k).inChart (complexChartAt (n := n) x))
            (θ.coeff (complexChartAt x))
            (Metric.closedBall ((complexChartAt (n := n) x).val x) (r x / 2) ∩
              BedfordTaylorTopDegree.strictLocus (chartTarget (complexChartAt (n := n) x))
                (fun i z => φ i ((complexChartAt (n := n) x).val.symm z)) k)) k)

/-- The full original global-open source condition manufactures actual relative
trace mass on EVERY original coordinate ball, retaining the SAME base B. -/
theorem relative_chart_mass_ball_of_global_source
    (hG : IsRelativeWellDefinedOnGlobalOpens B hBc φ hφ)
    (f : ComplexChart n M) {z₀ : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hV : Metric.ball z₀ r ⊆ f.val.target) :
    HasFiniteRelativeMass (restrict (show (⟨Metric.ball z₀ r,Metric.isOpen_ball⟩ : Opens (ComplexModel n)) ≤ chartTarget f from hV) (B.inChart f))
      (isPositive_restrict (B.isPositive f) hV)
      (isClosedAny_restrict (hBc f) hV)
      (fun i z => φ i (f.val.symm z)) (fun i => (chartPlurisubharmonicOn hφ f i).mono hV) := by
  set V : Opens (ComplexModel n) := ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩
  have hVt : V ≤ chartTarget f := hV
  have hφf := chartPlurisubharmonicOn hφ f
  have hφV : ∀ i, PlurisubharmonicOn (fun z => φ i (f.val.symm z)) V :=
    fun i => (hφf i).mono hVt
  intro K' hK' hK'V
  -- the open set `f⁻¹(V)`, the form and the compact set on the manifold
  set U : Opens M := ⟨f.val.source ∩ f.val ⁻¹' V,
    f.val.continuousOn.isOpen_inter_preimage f.val.open_source V.isOpen⟩
  have hUf : (U : Set M) ⊆ f.val.source := inter_subset_left
  have hUconn : IsConnected (U : Set M) := by
    have h := ((convex_ball z₀ r).isConnected (Metric.nonempty_ball.mpr hr)).image f.val.symm
      (f.val.continuousOn_symm.mono hV)
    have e : f.val.symm '' Metric.ball z₀ r = (U : Set M) := by
      rw [← inter_eq_right.mpr hV, f.val.symm_image_target_inter_eq]
      ext x
      change x ∈ f.val.source ∩ f.val ⁻¹' (f.val.target ∩ Metric.ball z₀ r) ↔
        x ∈ f.val.source ∩ f.val ⁻¹' Metric.ball z₀ r
      simp only [mem_inter_iff, mem_preimage]
      exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, f.val.map_source h1, h2⟩⟩
    rwa [e] at h
  set θ := SemipositiveFormOn.ofChart f hUf (fun _ => kahlerForm n) contDiffOn_const
    (fun _ _ => isSemipositiveOneOne_kahlerForm)
  set K := f.val.symm '' K'
  have hK : IsCompact K := hK'.image_of_continuousOn
    (f.val.continuousOn_symm.mono (hK'V.trans hV))
  have hKU : K ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    have hzt := hV (hK'V hz)
    exact ⟨f.val.map_target hzt, by rw [mem_preimage, f.val.right_inv hzt]; exact hK'V hz⟩
  have hKf : K ⊆ f.val.source := hKU.trans hUf
  have h := hG U hUconn θ K hK hKU
  refine lt_of_le_of_lt (iSup_mono fun k => ?_) h
  set T := relativeGlobalBTTruncations B hBc φ hφ k
  have hOk := measurableSet_strictLocusM hφ k (M := M)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hOK : MeasurableSet (strictLocusM φ k ∩ K) := hOk.inter hKm
  -- the value of the glued measure on the chart piece
  have e1 : wedgeMeasureOn T θ hK (strictLocusM φ k ∩ f.val.source) =
      chartWedgeMeasure T θ f (strictLocusM φ k ∩ K) := by
    have h2 := congrArg (fun μ : Measure M => μ (strictLocusM φ k))
      (wedgeMeasureOn_restrict_source T θ hK f)
    rw [Measure.restrict_apply' f.val.open_source.measurableSet,
      Measure.restrict_apply hOk] at h2
    rw [h2, inter_eq_left.mpr hKf]
  have hO' := BedfordTaylorTopDegree.measurableSet_strictLocus hφf k
  have hK'm : MeasurableSet K' := hK'.isClosed.measurableSet
  calc ((isTruncationFamily_relative (restrict hVt (B.inChart f))
          (isPositive_restrict (B.isPositive f) hVt) (isClosedAny_restrict (hBc f) hVt)
          (fun i z => φ i (f.val.symm z)) hφV).isPositive k).traceMeasure
          (K' ∩ BedfordTaylorTopDegree.strictLocus V (fun i z => φ i (f.val.symm z)) k)
        ≤ (T.isPositive f).traceMeasure
          (K' ∩ BedfordTaylorTopDegree.strictLocus (chartTarget f)
            (fun i z => φ i (f.val.symm z)) k) := by
          have hB : relativeTruncatedBT V (fun i z => φ i (f.val.symm z)) (restrict hVt (B.inChart f)) k =
              restrict hVt (T.inChart f) := relativeTruncatedBT_restrict (B.inChart f) (B.isPositive f) (hBc f) (fun i z => φ i (f.val.symm z)) hφf hVt k
          rw [traceMeasure_congr _ (isPositive_restrict (T.isPositive f) hVt) hB,
            traceMeasure_restrict, Measure.restrict_apply (hK'm.inter
              (BedfordTaylorTopDegree.measurableSet_strictLocus hφV k)),
            NonPluripolarCurrent.strictLocus_restrict hVt k]
          refine measure_mono fun z hz => ?_
          exact ⟨hz.1.1, hz.1.2.1⟩
      _ = wedgePowerMeasure (T.inChart f) (θ.coeff f)
          (K' ∩ BedfordTaylorTopDegree.strictLocus (chartTarget f)
            (fun i z => φ i (f.val.symm z)) k) :=
          (wedgePowerMeasure_eq_traceMeasure_of_eqOn (T.isPositive f) (hK'm.inter hO')
            fun z hz => SemipositiveFormOn.ofChart_coeff_self f hUf _ _ _ (hV (hK'V hz.1))).symm
      _ ≤ chartWedgeMeasure T θ f (strictLocusM φ k ∩ K) := by
          rw [chartWedgeMeasure_apply T θ f hOK]
          refine measure_mono fun z hz => ?_
          have hzt := hV (hK'V hz.1)
          refine ⟨?_, hzt, ?_⟩
          · rw [mem_preimage, chartInv_of_mem hzt]
            exact ⟨fun i => hz.2.2 i, z, hz.1, rfl⟩
          · exact ⟨f.val.map_target hzt, by rw [mem_preimage, f.val.right_inv hzt]; exact hK'V hz.1⟩
      _ = wedgeMeasureOn T θ hK (strictLocusM φ k ∩ f.val.source) := e1.symm
      _ ≤ wedgeMeasureOn T θ hK (strictLocusM φ k) := measure_mono inter_subset_left

/-- BOTH directions of the literal full-manifold relative source mass
condition, with no compactness of the original manifold. -/
theorem relative_global_source_mass_iff :
    IsRelativeWellDefinedOnGlobalOpens B hBc φ hφ ↔ HasFiniteGlobalRelativeMass B hBc φ hφ := by
  constructor
  · intro hG f
    have hball : ∀ z : chartTarget f, ∃ r > (0 : ℝ), Metric.ball (z : ComplexModel n) r ⊆
        f.val.target := fun z => Metric.isOpen_iff.mp f.val.open_target z z.2
    choose r hr hsub using hball
    apply hasFiniteRelativeMass_of_cover (B.inChart f) (B.isPositive f) (hBc f)
      (fun i z => φ i (f.val.symm z)) (chartPlurisubharmonicOn hφ f)
      (fun z : chartTarget f => ⟨Metric.ball (z : ComplexModel n) (r z),Metric.isOpen_ball⟩)
      (fun z => hsub z)
    · intro z hz
      exact mem_iUnion.mpr ⟨⟨z,hz⟩,Metric.mem_ball_self (hr ⟨z,hz⟩)⟩
    · intro z
      exact relative_chart_mass_ball_of_global_source B hBc hφ hG f (hr z) (hsub z)
  · exact relative_global_source_mass_of_chart B hBc hφ

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeWellDefinedOnGlobalOpens
#check @SGPT.NPP.RelativeNonPluripolar.chartWedgeMeasure_relative_trunc_le
#check @SGPT.NPP.RelativeNonPluripolar.relative_global_source_mass_of_chart
#check @SGPT.NPP.RelativeNonPluripolar.relative_chart_mass_ball_of_global_source
#check @SGPT.NPP.RelativeNonPluripolar.relative_global_source_mass_iff
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeWellDefinedOnGlobalOpens
#print axioms SGPT.NPP.RelativeNonPluripolar.chartWedgeMeasure_relative_trunc_le
#print axioms SGPT.NPP.RelativeNonPluripolar.relative_global_source_mass_of_chart
#print axioms SGPT.NPP.RelativeNonPluripolar.relative_chart_mass_ball_of_global_source
#print axioms SGPT.NPP.RelativeNonPluripolar.relative_global_source_mass_iff

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_05

-- Exact frozen body: RelativeInducedMassDraft
section OriginalFragment_06

/-! BOTH directions of actual relative mass on arbitrary induced open
manifolds, retaining the SAME original base current and source potentials. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor
open SGPT.NPP.NonPluripolarCurrent

/-- Pointwise ORIGINAL potential equality preserves actual mass and the SAME
actual relative current, without supplying an output/current equality. -/
theorem relative_mass_product_congr {n p r : ℕ} {A : Opens (ComplexModel n)}
    (T : LocalProductCurrent n A (r + p)) (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (φ ψ : Fin p → ComplexModel n → EReal)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) A) (hψ : ∀ i, PlurisubharmonicOn (ψ i) A)
    (he : ∀ i, ∀ x ∈ A, φ i x = ψ i x) :
    (HasFiniteRelativeMass T hT hTc φ hφ ↔ HasFiniteRelativeMass T hT hTc ψ hψ) ∧
    ∀ (hmφ : HasFiniteRelativeMass T hT hTc φ hφ) (hmψ : HasFiniteRelativeMass T hT hTc ψ hψ),
      (relativeNonPluripolarProduct T hT hTc φ hφ hmφ).val =
        (relativeNonPluripolarProduct T hT hTc ψ hψ hmψ).val := by
  have hseq : truncAt (relativeTruncatedBT A φ T) (BedfordTaylorTopDegree.strictLocus A φ) =
      truncAt (relativeTruncatedBT A ψ T) (BedfordTaylorTopDegree.strictLocus A ψ) := by
    funext k
    exact relativeTruncAt_congr T φ ψ he k
  refine ⟨?_,?_⟩
  · rw [hasFiniteRelativeMass_iff_exists_weak_limit T hT hTc φ hφ,
      hasFiniteRelativeMass_iff_exists_weak_limit T hT hTc ψ hψ,hseq]
  · intro hmφ hmψ
    have hconv := weakTendsto_relativeTruncations T hT hTc φ hφ hmφ
    rw [hseq] at hconv
    ext γ χ
    exact tendsto_nhds_unique (hconv γ χ) (weakTendsto_relativeTruncations T hT hTc ψ hψ hmψ γ χ)

/-- Source-compatible ORIGINAL bases manufacture transported actual mass as
well as the actual relative current. No mass on the target or closed-pullback
certificate is supplied; original target-base closedness supplies the latter. -/
theorem exists_relative_product_of_base_compatible
    {n p r : ℕ} {A B : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}
    (h : IsBiholomorphicPair A B τ σ)
    (T : LocalProductCurrent n B (r + p)) (hT : IsPositive T) (hTc : IsClosedAny (r + p) T)
    (R : LocalProductCurrent n A (r + p)) (hR : IsPositive R) (hRc : IsClosedAny (r + p) R)
    (hbase : R = pullback h hT)
    (φ : Fin p → ComplexModel n → EReal) (hφ : ∀ i, PlurisubharmonicOn (φ i) B)
    (ψ : Fin p → ComplexModel n → EReal) (hψ : ∀ i, PlurisubharmonicOn (ψ i) A)
    (he : ∀ i, ∀ x ∈ A, φ i (τ x) = ψ i x)
    (hmφ : HasFiniteRelativeMass T hT hTc φ hφ) :
    ∃ hmψ : HasFiniteRelativeMass R hR hRc ψ hψ,
      pullback h (relativeNonPluripolarProduct T hT hTc φ hφ hmφ).property =
        (relativeNonPluripolarProduct R hR hRc ψ hψ hmψ).val := by
  have hTpc : IsClosedAny (r + p) (pullback h hT) := by rw [← hbase]; exact hRc
  have hseq (k : ℕ) :
      pullback h ((isTruncationFamily_relative T hT hTc φ hφ).isPositive_trunc k) =
        truncAt (relativeTruncatedBT A ψ R) (BedfordTaylorTopDegree.strictLocus A ψ) k := by
    rw [relativeTruncAt_pullback h T hT hTc hTpc φ hφ k,← hbase]
    exact relativeTruncAt_congr R (fun i x => φ i (τ x)) ψ he k
  have hconv := weakTendsto_pullback h
    (fun k => (isTruncationFamily_relative T hT hTc φ hφ).isPositive_trunc k)
    (relativeNonPluripolarProduct T hT hTc φ hφ hmφ).property
    (weakTendsto_relativeTruncations T hT hTc φ hφ hmφ)
  simp_rw [hseq] at hconv
  have hmψ := (hasFiniteRelativeMass_iff_exists_weak_limit R hR hRc ψ hψ).mpr ⟨_,hconv⟩
  exact ⟨hmψ,relative_product_pullback_of_base_compatible h T hT hTc R hR hRc hbase
    φ hφ ψ hψ he hmφ hmψ⟩

variable {m p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

private theorem mass_restrict_domain_congr {n p r : ℕ} {U A A' : Opens (ComplexModel n)}
    (he : A = A') (T : LocalProductCurrent n U (r + p)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + p) T) (hAU : A ≤ U) (hA'U : A' ≤ U)
    (φ : Fin p → ComplexModel n → EReal)
    (hφA : ∀ i, PlurisubharmonicOn (φ i) A) (hφA' : ∀ i, PlurisubharmonicOn (φ i) A') :
    HasFiniteRelativeMass (restrict hAU T) (isPositive_restrict hT hAU)
      (isClosedAny_restrict hTc hAU) φ hφA ↔
    HasFiniteRelativeMass (restrict hA'U T) (isPositive_restrict hT hA'U)
      (isClosedAny_restrict hTc hA'U) φ hφA' := by
  cases he
  rfl

private theorem ambient_mass_of_induced_chart
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed) (O : Opens M)
    (φ : Fin p → M → EReal)
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) O)
    (hm : HasFiniteGlobalRelativeMass (positiveCurrentOnOpens B O) (isClosed_positiveCurrentOnOpens B hBc O)
      (fun i (x : O) => φ i x) (fun i => (manifoldPSH_opens_iff O).mpr (hφ i)))
    (e : ComplexChart (m + 1) O) :
    HasFiniteRelativeMass (restrict (chartDomain_le (ambientChart O e) O) (B.inChart (ambientChart O e)))
      (isPositive_restrict (B.isPositive (ambientChart O e)) (chartDomain_le (ambientChart O e) O))
      (isClosedAny_restrict (hBc (ambientChart O e)) (chartDomain_le (ambientChart O e) O))
      (fun i z => φ i ((ambientChart O e).val.symm z))
      (fun i => (isL1PshOn_chartDomain (hφ i) (ambientChart O e)).psh) := by
  have hA : chartTarget e ≤ chartDomain (ambientChart O e) O := by rw [chartTarget_eq_chartDomain O e]
  have hpA := fun i => (isL1PshOn_chartDomain (hφ i) (ambientChart O e)).psh.mono hA
  have hcong := relative_mass_product_congr ((positiveCurrentOnOpens B O).inChart e)
    ((positiveCurrentOnOpens B O).isPositive e) (isClosed_positiveCurrentOnOpens B hBc O e)
    (fun i z => φ i ((e.val.symm z : O) : M)) (fun i z => φ i ((ambientChart O e).val.symm z))
    (chartPlurisubharmonicOn (fun i => (manifoldPSH_opens_iff O).mpr (hφ i)) e) hpA
    (fun i z hz => by rw [coe_symm_eq_ambient O e hz])
  have hmass := hcong.1.mp (hm e)
  change HasFiniteRelativeMass (restrict (chartTarget_le_ambient O e) (B.inChart (ambientChart O e)))
    (isPositive_restrict (B.isPositive (ambientChart O e)) (chartTarget_le_ambient O e))
    (isClosedAny_restrict (hBc (ambientChart O e)) (chartTarget_le_ambient O e))
    (fun i z => φ i ((ambientChart O e).val.symm z)) hpA at hmass
  exact (mass_restrict_domain_congr (chartTarget_eq_chartDomain O e)
    (B.inChart (ambientChart O e)) (B.isPositive (ambientChart O e)) (hBc (ambientChart O e))
    (chartTarget_le_ambient O e) (chartDomain_le (ambientChart O e) O)
    (fun i z => φ i ((ambientChart O e).val.symm z)) hpA
    (fun i => (isL1PshOn_chartDomain (hφ i) (ambientChart O e)).psh)).mp hmass

private theorem mass_on_original_preOpen_overlap
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed) (O : Opens M)
    (φ : Fin p → M → EReal)
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) O)
    (f g : ComplexChart (m + 1) M)
    (hm : HasFiniteRelativeMass (restrict (chartDomain_le g O) (B.inChart g))
      (isPositive_restrict (B.isPositive g) (chartDomain_le g O))
      (isClosedAny_restrict (hBc g) (chartDomain_le g O))
      (fun i z => φ i (g.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) g).psh)) :
    let hh := chartTransition_isBiholomorphicPair f g
    let V := overlapDomain f g O
    let hA : preOpen hh V ≤ chartDomain f O := fun _ hx => (mem_preOpen_overlapDomain.mp hx).1
    HasFiniteRelativeMass (restrict (hA.trans (chartDomain_le f O)) (B.inChart f))
      (isPositive_restrict (B.isPositive f) (hA.trans (chartDomain_le f O)))
      (isClosedAny_restrict (hBc f) (hA.trans (chartDomain_le f O)))
      (fun i z => φ i (f.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) f).psh.mono hA) := by
  let hh := chartTransition_isBiholomorphicPair f g
  let V := overlapDomain f g O
  have hVB : V ≤ overlapTarget f g := inf_le_left
  have hVG : V ≤ chartDomain g O := inf_le_right
  have hA : preOpen hh V ≤ chartDomain f O := fun _ hx => (mem_preOpen_overlapDomain.mp hx).1
  let RA := restrict (hA.trans (chartDomain_le f O)) (B.inChart f)
  let RB := restrict (hVG.trans (chartDomain_le g O)) (B.inChart g)
  have hRA : IsPositive RA := isPositive_restrict (B.isPositive f) _
  have hRB : IsPositive RB := isPositive_restrict (B.isPositive g) _
  have hRAc : IsClosedAny (r + p) RA := isClosedAny_restrict (hBc f) _
  have hRBc : IsClosedAny (r + p) RB := isClosedAny_restrict (hBc g) _
  let h' := isBiholomorphicPair_preOpen hh hVB
  have hbase : RA = pullback h' hRB := by
    calc
      RA = restrict (preOpen_le hh V) (restrict (overlapSource_le f g) (B.inChart f)) := by rw [restrict_restrict]
      _ = restrict (preOpen_le hh V) (pullback hh
          (isPositive_restrict (B.isPositive g) (overlapTarget_le f g))) :=
        congrArg (restrict (preOpen_le hh V)) (B.compatible f g)
      _ = pullback h' (isPositive_restrict
          (isPositive_restrict (B.isPositive g) (overlapTarget_le f g)) hVB) :=
        (pullback_restrict hh (isPositive_restrict (B.isPositive g) (overlapTarget_le f g)) hVB).symm
      _ = pullback h' hRB := pullback_congr_current h' _ _
        (restrict_restrict hVB (overlapTarget_le f g) (B.inChart g))
  have hmB : HasFiniteRelativeMass RB hRB hRBc (fun i z => φ i (g.val.symm z))
      (fun i => (isL1PshOn_chartDomain (hφ i) g).psh.mono hVG) := by
    simpa only [restrict_restrict] using hasFiniteRelativeMass_restrict
      (restrict (chartDomain_le g O) (B.inChart g))
      (isPositive_restrict (B.isPositive g) (chartDomain_le g O))
      (isClosedAny_restrict (hBc g) (chartDomain_le g O))
      (fun i z => φ i (g.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) g).psh) hm hVG
  exact (exists_relative_product_of_base_compatible h' RB hRB hRBc RA hRA hRAc hbase
    (fun i z => φ i (g.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) g).psh.mono hVG)
    (fun i z => φ i (f.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) f).psh.mono hA)
    (fun i x hx => (chart_comp_transition (φ i) f g x hx.1).symm) hmB).choose

/-- BOTH directions: actual mass on the open manifold with its induced atlas
is the SAME actual ambient-chart mass on the ORIGINAL open subset. No output
current, chart compatibility or local mass-transport certificate is supplied. -/
theorem hasFiniteGlobalRelativeMass_opens_iff
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed) (O : Opens M)
    (φ : Fin p → M → EReal)
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) O) :
    HasFiniteGlobalRelativeMass (positiveCurrentOnOpens B O) (isClosed_positiveCurrentOnOpens B hBc O)
      (fun i (x : O) => φ i x) (fun i => (manifoldPSH_opens_iff O).mpr (hφ i)) ↔
      HasFiniteRelativeMassOn B hBc φ O hφ := by
  constructor
  · intro hm f
    have hcov : ∀ z : chartDomain f O, ∃ g : ComplexChart (m + 1) M,
        f.val.symm z ∈ g.val.source ∧
        HasFiniteRelativeMass (restrict (chartDomain_le g O) (B.inChart g))
          (isPositive_restrict (B.isPositive g) (chartDomain_le g O))
          (isClosedAny_restrict (hBc g) (chartDomain_le g O))
          (fun i z => φ i (g.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) g).psh) := by
      intro z
      let x : O := ⟨f.val.symm z,(mem_chartDomain.mp z.2).2⟩
      let e := complexChartAt (n := m + 1) x
      exact ⟨ambientChart O e,mem_ambientChart_source O e (mem_complexChartAt_source x),
        ambient_mass_of_induced_chart B hBc O φ hφ hm e⟩
    choose g hg hmg using hcov
    apply hasFiniteRelativeMass_of_cover (restrict (chartDomain_le f O) (B.inChart f))
      (isPositive_restrict (B.isPositive f) (chartDomain_le f O))
      (isClosedAny_restrict (hBc f) (chartDomain_le f O))
      (fun i z => φ i (f.val.symm z)) (fun i => (isL1PshOn_chartDomain (hφ i) f).psh)
      (fun z : chartDomain f O => preOpen (chartTransition_isBiholomorphicPair f (g z))
        (overlapDomain f (g z) O))
      (fun _ _ hx => (mem_preOpen_overlapDomain.mp hx).1)
    · intro z hz
      exact mem_iUnion.mpr ⟨⟨z,hz⟩,mem_preOpen_overlapDomain.mpr ⟨hz,hg ⟨z,hz⟩⟩⟩
    · intro z
      simpa only [restrict_restrict] using mass_on_original_preOpen_overlap B hBc O φ hφ f (g z) (hmg z)
  · intro hm e
    have hA : chartTarget e ≤ chartDomain (ambientChart O e) O := by rw [chartTarget_eq_chartDomain O e]
    have hpA := fun i => (isL1PshOn_chartDomain (hφ i) (ambientChart O e)).psh.mono hA
    have hmass := relativeMassOn_chart_restrict B hBc φ O hφ hm (ambientChart O e) hA
    exact (relative_mass_product_congr ((positiveCurrentOnOpens B O).inChart e)
      ((positiveCurrentOnOpens B O).isPositive e) (isClosed_positiveCurrentOnOpens B hBc O e)
      (fun i z => φ i ((ambientChart O e).val.symm z)) (fun i z => φ i ((e.val.symm z : O) : M))
      hpA (chartPlurisubharmonicOn (fun i => (manifoldPSH_opens_iff O).mpr (hφ i)) e)
      (fun i z hz => by rw [coe_symm_eq_ambient O e hz])).1.mp hmass

/-- The FULL original connected-open/smooth-form source condition on EVERY
original induced open manifold is equivalent to actual ambient-chart mass. -/
theorem relative_global_source_mass_opens_iff [MeasurableSpace M] [BorelSpace M] [T2Space M]
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed) (O : Opens M)
    (φ : Fin p → M → EReal)
    (hφ : ∀ i, (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn (φ i) O) :
    IsRelativeWellDefinedOnGlobalOpens (positiveCurrentOnOpens B O) (isClosed_positiveCurrentOnOpens B hBc O)
      (fun i (x : O) => φ i x) (fun i => (manifoldPSH_opens_iff O).mpr (hφ i)) ↔
      HasFiniteRelativeMassOn B hBc φ O hφ :=
  (relative_global_source_mass_iff (positiveCurrentOnOpens B O) (isClosed_positiveCurrentOnOpens B hBc O)
    (fun i => (manifoldPSH_opens_iff O).mpr (hφ i))).trans
    (hasFiniteGlobalRelativeMass_opens_iff B hBc O φ hφ)

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.relative_mass_product_congr
#check @SGPT.NPP.RelativeNonPluripolar.exists_relative_product_of_base_compatible
#check @SGPT.NPP.RelativeNonPluripolar.hasFiniteGlobalRelativeMass_opens_iff
#check @SGPT.NPP.RelativeNonPluripolar.relative_global_source_mass_opens_iff
#print axioms SGPT.NPP.RelativeNonPluripolar.relative_mass_product_congr
#print axioms SGPT.NPP.RelativeNonPluripolar.exists_relative_product_of_base_compatible
#print axioms SGPT.NPP.RelativeNonPluripolar.hasFiniteGlobalRelativeMass_opens_iff
#print axioms SGPT.NPP.RelativeNonPluripolar.relative_global_source_mass_opens_iff

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_06

-- Exact frozen body: RelativeSourceOpensCurrentDraft
section OriginalFragment_07

/-! Literal original potential-cover source condition on INDUCED open
manifolds, with both mass directions and exact actual relative-current readback. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold
namespace SGPT.NPP.RelativeNonPluripolar
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
open LocalBedfordTaylorCalculus LocalCurrentL1Ddc
open SGPT.NPP.NonPluripolarCurrent

variable {m p r : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

/-- The ORIGINAL local-potential equations are exactly equality of actual
positive currents on the open submanifold, with no supplied output dictionary. -/
theorem isLocalPotential_iff_actual_opens
    {T : Fin p → PositiveCurrent (m + 1) M m} {O : Opens M} {φ : Fin p → M → EReal} :
    IsLocalPotential T O φ ↔
      ∃ hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (fun x : O => φ i x),
        ∀ i, positiveCurrentOnOpens (T i) O = ddcCurrent m (fun x : O => φ i x) (hφ i) := by
  constructor
  · intro hpot
    obtain ⟨hφ,hddc⟩ := (isLocalPotential_iff_opens (T := T) (U := O)).mp hpot
    refine ⟨hφ,fun i => ?_⟩
    ext1 e
    exact hddc i e
  · rintro ⟨hφ,hddc⟩
    apply (isLocalPotential_iff_opens (T := T) (U := O)).mpr
    exact ⟨hφ,fun i e => congrArg (fun S : PositiveCurrent (m + 1) O m => S.inChart e) (hddc i)⟩

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- LITERAL original potential-cover criterion: the potentials live on EACH
original induced open manifold, their ACTUAL ddc currents are the original
factor restrictions, and the mass condition has ALL original connected opens,
ALL actual smooth semipositive forms and ALL compact subsets of that manifold. -/
def IsRelativeCurrentProductSourceWellDefined
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) : Prop :=
  ∃ C : Set (Opens M), (∀ x : M, ∃ O ∈ C, x ∈ O) ∧
    ∀ O ∈ C, ∃ φ : Fin p → O → EReal,
      ∃ hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ i),
        (∀ i, positiveCurrentOnOpens (T i) O = ddcCurrent m (φ i) (hφ i)) ∧
        IsRelativeWellDefinedOnGlobalOpens (positiveCurrentOnOpens B O)
          (isClosed_positiveCurrentOnOpens B hBc O) φ hφ

/-- BOTH directions of the literal L146 relative source definition on every
original induced potential-cover domain, with no compact ambient hypothesis. -/
theorem isRelativeCurrentProductWellDefined_iff_sourceOpens
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) :
    IsRelativeCurrentProductWellDefined B hBc T ↔ IsRelativeCurrentProductSourceWellDefined B hBc T := by
  constructor
  · rintro ⟨C,hC,hdata⟩
    refine ⟨C,hC,fun O hO => ?_⟩
    obtain ⟨φ,hpot,hm⟩ := hdata O hO
    obtain ⟨hφ,hddc⟩ := (isLocalPotential_iff_actual_opens (T := T) (O := O)).mp hpot
    exact ⟨fun i x => φ i x,hφ,hddc,(relative_global_source_mass_opens_iff B hBc O φ hpot.psh).mpr hm⟩
  · rintro ⟨C,hC,hdata⟩
    refine ⟨C,hC,fun O hO => ?_⟩
    obtain ⟨φ,hφ,hddc,hm⟩ := hdata O hO
    let ψ : Fin p → M → EReal := fun i => extendOpens O (φ i)
    have hψφ : (fun i (x : O) => ψ i x) = φ := funext fun i => extendOpens_comp_val O (φ i)
    have key : ∀ (φ' : Fin p → O → EReal)
        (hφ' : ∀ i, SGPT.PSH.ManifoldPSH (n := m + 1) (φ' i)),
        φ' = (fun i (x : O) => ψ i x) →
        (∀ i, positiveCurrentOnOpens (T i) O = ddcCurrent m (φ' i) (hφ' i)) →
        IsRelativeWellDefinedOnGlobalOpens (positiveCurrentOnOpens B O)
          (isClosed_positiveCurrentOnOpens B hBc O) φ' hφ' →
        ∃ hpot : IsLocalPotential T O ψ, HasFiniteRelativeMassOn B hBc ψ O hpot.psh := by
      rintro φ' hφ' rfl hddc' hm'
      have hpot := (isLocalPotential_iff_actual_opens (T := T) (O := O)).mpr ⟨hφ',hddc'⟩
      exact ⟨hpot,(relative_global_source_mass_opens_iff B hBc O ψ hpot.psh).mp hm'⟩
    exact ⟨ψ,key φ hφ hψφ.symm hddc hm⟩

/-- The SAME intrinsic relative current restricts to the genuine relative
product on EVERY original potential-cover domain with its induced atlas.
Both the full source mass and the actual output readback are manufactured. -/
theorem relativeCurrentProduct_restrict_opens
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m) (hW : IsRelativeCurrentProductWellDefined B hBc T)
    {O : Opens M} {φ : Fin p → M → EReal} (hpot : IsLocalPotential T O φ) :
    ∃ hSource : IsRelativeWellDefinedOnGlobalOpens (positiveCurrentOnOpens B O)
        (isClosed_positiveCurrentOnOpens B hBc O) (fun i (x : O) => φ i x)
        (fun i => (manifoldPSH_opens_iff O).mpr (hpot.psh i)),
      positiveCurrentOnOpens (relativeCurrentProduct B hBc T hW) O =
        globalRelativeNonPluripolarProduct (positiveCurrentOnOpens B O)
          (isClosed_positiveCurrentOnOpens B hBc O) (fun i (x : O) => φ i x)
          (fun i => (manifoldPSH_opens_iff O).mpr (hpot.psh i))
          ((relative_global_source_mass_iff (positiveCurrentOnOpens B O)
            (isClosed_positiveCurrentOnOpens B hBc O)
            (fun i => (manifoldPSH_opens_iff O).mpr (hpot.psh i))).mp hSource) := by
  obtain ⟨hmOn,hread⟩ := relativeCurrentProduct_restrict B hBc T hW hpot
  have hSource := (relative_global_source_mass_opens_iff B hBc O φ hpot.psh).mpr hmOn
  have hmU := (relative_global_source_mass_iff (positiveCurrentOnOpens B O)
    (isClosed_positiveCurrentOnOpens B hBc O)
    (fun i => (manifoldPSH_opens_iff O).mpr (hpot.psh i))).mp hSource
  refine ⟨hSource,?_⟩
  ext1 e
  let E := ambientChart O e
  have hA : chartTarget e ≤ chartDomain E O := by rw [chartTarget_eq_chartDomain O e]
  have hpA := fun i => (hpot.chartPsh E i).mono hA
  have hmA := relativeMassOn_chart_restrict B hBc φ O hpot.psh hmOn E hA
  let RA := restrict (chartTarget_le_ambient O e) (B.inChart E)
  have hRA : IsPositive RA := isPositive_restrict (B.isPositive E) (chartTarget_le_ambient O e)
  have hRAc : IsClosedAny (r + p) RA := isClosedAny_restrict (hBc E) (chartTarget_le_ambient O e)
  have hL : restrict (chartTarget_le_ambient O e) ((relativeCurrentProduct B hBc T hW).inChart E) =
      (relativeNonPluripolarProduct RA hRA hRAc (fun i z => φ i (E.val.symm z)) hpA hmA).val := by
    calc
      _ = restrict hA (restrict (chartDomain_le E O) ((relativeCurrentProduct B hBc T hW).inChart E)) := by
        rw [restrict_restrict]
      _ = restrict hA (relativeNonPluripolarProduct (restrict (chartDomain_le E O) (B.inChart E))
          (isPositive_restrict (B.isPositive E) (chartDomain_le E O))
          (isClosedAny_restrict (hBc E) (chartDomain_le E O))
          (fun i z => φ i (E.val.symm z)) (hpot.chartPsh E) (hmOn E)).val := congrArg (restrict hA) (hread E)
      _ = _ := relativeProductOn_chart_restrict B hBc φ O hpot.psh hmOn E hA
  exact hL.trans ((relative_mass_product_congr RA hRA hRAc
    (fun i z => φ i (E.val.symm z)) (fun i z => φ i ((e.val.symm z : O) : M)) hpA
    (chartPlurisubharmonicOn (fun i => (manifoldPSH_opens_iff O).mpr (hpot.psh i)) e)
    (fun i z hz => by rw [coe_symm_eq_ambient O e hz])).2 hmA (hmU e))

/-- The relative product under the LITERAL original source criterion. It is
built from the SAME original B and factors, through the proved source dictionary. -/
def relativeCurrentProductOfSourceOpens
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m)
    (hSource : IsRelativeCurrentProductSourceWellDefined B hBc T) : PositiveCurrent (m + 1) M r :=
  relativeCurrentProduct B hBc T ((isRelativeCurrentProductWellDefined_iff_sourceOpens B hBc T).mpr hSource)

/-- The source-defined genuine relative current is closed in EVERY output degree. -/
theorem isClosed_relativeCurrentProductOfSourceOpens
    (B : PositiveCurrent (m + 1) M (r + p)) (hBc : B.IsClosed)
    (T : Fin p → PositiveCurrent (m + 1) M m)
    (hSource : IsRelativeCurrentProductSourceWellDefined B hBc T) :
    (relativeCurrentProductOfSourceOpens B hBc T hSource).IsClosed :=
  isClosed_relativeCurrentProduct B hBc T ((isRelativeCurrentProductWellDefined_iff_sourceOpens B hBc T).mpr hSource)

end SGPT.NPP.RelativeNonPluripolar
#check @SGPT.NPP.RelativeNonPluripolar.isLocalPotential_iff_actual_opens
#check @SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductSourceWellDefined
#check @SGPT.NPP.RelativeNonPluripolar.isRelativeCurrentProductWellDefined_iff_sourceOpens
#check @SGPT.NPP.RelativeNonPluripolar.relativeCurrentProduct_restrict_opens
#check @SGPT.NPP.RelativeNonPluripolar.relativeCurrentProductOfSourceOpens
#check @SGPT.NPP.RelativeNonPluripolar.isClosed_relativeCurrentProductOfSourceOpens
#print axioms SGPT.NPP.RelativeNonPluripolar.isLocalPotential_iff_actual_opens
#print axioms SGPT.NPP.RelativeNonPluripolar.IsRelativeCurrentProductSourceWellDefined
#print axioms SGPT.NPP.RelativeNonPluripolar.isRelativeCurrentProductWellDefined_iff_sourceOpens
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeCurrentProduct_restrict_opens
#print axioms SGPT.NPP.RelativeNonPluripolar.relativeCurrentProductOfSourceOpens
#print axioms SGPT.NPP.RelativeNonPluripolar.isClosed_relativeCurrentProductOfSourceOpens

-- Close original EOF sections, then restore this fragment scope.
end
end OriginalFragment_07
