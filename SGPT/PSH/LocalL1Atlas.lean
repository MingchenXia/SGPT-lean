import SGPT.PSH.LocalL1Tails
import SGPT.PSH.SupremumPluripolar
import SGPT.PSH.CountablePluripolar
import SGPT.Foundations.Analysis.PlurisubharmonicIntegrability

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.LocalL1Recovery
open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- Literal real local L1 convergence of the original PSH representatives
on compact subsets of every actual source chart. -/
def L1LocallyTendsto (u : ℕ → X → EReal) (v : X → EReal) : Prop :=
  ∀ (i : A.Index) (K : Set (ComplexModel (A.dimension i))),
    IsCompact K → K ⊆ (A.chart i).target →
      Tendsto (fun j => ∫ z in K,
        ‖(A.coordinate (u j) i z).toReal - (A.coordinate v i z).toReal‖ ∂volume)
        atTop (𝓝 0)

/-- Local canonical L1 convergence on every compact subset
of every actual source chart, with its genuine chart Lebesgue measure. -/
def CanonicalL1LocallyTendsto (u : ℕ → X → EReal) (v : X → EReal) : Prop :=
  ∀ (i : A.Index) (K : Set (ComplexModel (A.dimension i))),
    IsCompact K → K ⊆ (A.chart i).target →
      Tendsto (fun j => ∫⁻ z in K,
        canonicalERealAbsDiff (A.coordinate (u j) i z) (A.coordinate v i z) ∂volume)
        atTop (𝓝 0)

variable {A}

/-- Actual nondegenerate source PSH data produce the genuine main-branch
integrability locus in every chart, without a connected chart assumption. -/
theorem IsPSH.coordinate_integrabilityLocus {v : X → EReal}
    (hv : A.IsPSH v) (i : A.Index) :
    (A.chart i).target ⊆ pshIntegrabilityLocus (A.coordinate v i) volume := by
  intro z hz
  obtain ⟨r, hr, hBT⟩ := Metric.isOpen_iff.mp (A.chart i).open_target z hz
  have hnb := LocallyNondegenerate.exists_coordinate_ne_bot hv.locallyNondegenerate
    (A.chart i) isOpen_ball hBT (mem_ball_self hr)
  exact ((hv.chartPlurisubharmonic i).mono hBT).subset_pshIntegrabilityLocus
    volume (convex_ball z r).isPreconnected hnb (mem_ball_self hr)

/-- Local integrability is produced from actual source PSH germs and
their genuine non-bottom witnesses in each small connected ball. -/
theorem IsPSH.locallyIntegrableOn_coordinate_toReal {v : X → EReal}
    (hv : A.IsPSH v) (i : A.Index) :
    LocallyIntegrableOn (fun z => (A.coordinate v i z).toReal)
      (A.chart i).target volume := by
  intro z hz
  obtain ⟨V, hV, hzV, _hae, hI⟩ := hv.coordinate_integrabilityLocus i hz
  exact ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hzV), hI⟩

/-- The constructed actual locus gives almost-everywhere finiteness on
arbitrary chart compact sets, retaining all original exceptional poles. -/
theorem IsPSH.ae_finite_coordinate_on_compact {v : X → EReal}
    (hv : A.IsPSH v) (i : A.Index) {K : Set (ComplexModel (A.dimension i))}
    (hK : IsCompact K) (hKT : K ⊆ (A.chart i).target) :
    ∀ᵐ z ∂volume.restrict K, A.coordinate v i z ≠ ⊤ ∧ A.coordinate v i z ≠ ⊥ := by
  refine IsCompact.induction_on hK (by simp) ?_ ?_ ?_
  · intro s t hst ht
    exact ae_restrict_of_ae_restrict_of_subset hst ht
  · intro s t hs ht
    exact (ae_restrict_union_iff s t _).mpr ⟨hs, ht⟩
  · intro z hz
    obtain ⟨V, hV, hzV, hae, _hI⟩ := hv.coordinate_integrabilityLocus i (hKT hz)
    exact ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hzV), hae⟩

/-- Literal real L1 convergence implies canonical extended-value L1
convergence. Finiteness and integrability of the original functions are
produced internally; no exceptional-set or L1 certificate is assumed. -/
theorem canonicalL1LocallyTendsto_of_localL1
    {u : ℕ → X → EReal} {v : X → EReal}
    (hu : ∀ j, A.IsPSH (u j)) (hv : A.IsPSH v)
    (hlim : A.L1LocallyTendsto u v) : A.CanonicalL1LocallyTendsto u v := by
  intro i K hK hKT
  have hIu (j : ℕ) :=
    ((hu j).locallyIntegrableOn_coordinate_toReal i).integrableOn_compact_subset hKT hK
  have hIv := (hv.locallyIntegrableOn_coordinate_toReal i).integrableOn_compact_subset hKT hK
  have heq (j : ℕ) :
      (∫⁻ z in K, canonicalERealAbsDiff (A.coordinate (u j) i z) (A.coordinate v i z) ∂volume) =
      ENNReal.ofReal (∫ z in K,
        ‖(A.coordinate (u j) i z).toReal - (A.coordinate v i z).toReal‖ ∂volume) := by
    have hreal :
        ENNReal.ofReal (∫ z in K,
          ‖(A.coordinate (u j) i z).toReal - (A.coordinate v i z).toReal‖ ∂volume) =
        ∫⁻ z in K, ‖(A.coordinate (u j) i z).toReal - (A.coordinate v i z).toReal‖ₑ ∂volume := by
      simpa only [Pi.sub_apply] using
        ofReal_integral_norm_eq_lintegral_enorm ((hIu j).sub hIv)
    rw [hreal]
    apply lintegral_congr_ae
    filter_upwards [(hu j).ae_finite_coordinate_on_compact i hK hKT,
      hv.ae_finite_coordinate_on_compact i hK hKT] with z hzj hzv
    have hj := EReal.coe_toReal hzj.1 hzj.2
    have hvz := EReal.coe_toReal hzv.1 hzv.2
    conv_lhs => rw [← hj, ← hvz]
    simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff,
      ← EReal.coe_sub, EReal.abs_def, Real.enorm_eq_ofReal_abs]
  simpa only [heq, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (hlim i K hK hKT)

/-- Original local L1 convergence internally supplies genuine local uniform
upper bounds for the entire source family on the original manifold. -/
theorem locallyUniformlyBoundedAbove_of_canonicalL1
    {u : ℕ → X → EReal} {v : X → EReal}
    (hu : ∀ j, A.IsPSH (u j)) (hv : A.IsPSH v)
    (hlim : A.CanonicalL1LocallyTendsto u v) :
    FirstPass.LocallyUniformlyBoundedAbove (range u) univ := by
  intro p _hp
  obtain ⟨i, hp⟩ := A.cover p
  have hz := (A.chart i).map_source hp
  obtain ⟨r, hr, _hBT, C, hC⟩ := exists_local_uniform_upper_bound_of_localL1
    (fun j => (hu j).chartPlurisubharmonic i |>.discPshOn)
    ((hv.chartPlurisubharmonic i).discPshOn) (A.chart i).open_target volume
    (hlim i) hz
  let O := (A.chart i).source ∩ (A.chart i) ⁻¹' ball (A.chart i p) r
  have hO : IsOpen O := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hpO : p ∈ O := ⟨hp, mem_ball_self hr⟩
  refine ⟨O, by simpa only [nhdsWithin_univ] using hO.mem_nhds hpO, C, ?_⟩
  rintro f ⟨j, rfl⟩ q ⟨hq, _⟩
  have h := hC j (A.chart i q) hq.2
  simpa only [coordinate, Function.comp_apply, (A.chart i).left_inv hq.1] using h

/-- Literal whole source regularized-tail identity on the actual atlas;
chart dimensions may vary and original poles are retained. -/
theorem iInf_uscSup_tail_eq_of_canonicalL1
    {u : ℕ → X → EReal} {v : X → EReal}
    (hu : ∀ j, A.IsPSH (u j)) (hv : A.IsPSH v)
    (hlim : A.CanonicalL1LocallyTendsto u v) :
    (fun p => ⨅ N : ℕ, uscSup (fun j => u (j + N)) p) = v := by
  funext p
  obtain ⟨i, hp⟩ := A.cover p
  have hz := (A.chart i).map_source hp
  have h := iInf_uscSup_tail_eq_of_localL1
    (fun j => (hu j).chartPlurisubharmonic i |>.discPshOn)
    ((hv.chartPlurisubharmonic i).discPshOn) (A.chart i).open_target volume
    (hlim i) hz
  have htail (N : ℕ) :
      uscSup (fun j => A.coordinate (u (j + N)) i) (A.chart i p) =
        uscSup (fun j => u (j + N)) p := by
    rw [A.uscSup_coordinateFamily (fun j => u (j + N)) i hz]
    simp only [coordinate, Function.comp_apply, (A.chart i).left_inv hp]
  exact (iInf_congr fun N => (htail N).symm).trans
    (h.trans (by simp only [coordinate, Function.comp_apply, (A.chart i).left_inv hp]))

/-- The whole original discrepancy set has genuine source PSH pole witnesses;
it is contained in a countable union of the actual tail exceptional sets. -/
theorem locallyPluripolar_limsup_discrepancy_of_canonicalL1
    {u : ℕ → X → EReal} {v : X → EReal}
    (hu : ∀ j, A.IsPSH (u j)) (hv : A.IsPSH v)
    (hlim : A.CanonicalL1LocallyTendsto u v) :
    A.LocallyPluripolar {p | v p ≠ limsup (fun j => u j p) atTop} := by
  classical
  let S : ℕ → Set X := fun N => {p | (⨆ j, u (j + N) p) < uscSup (fun j => u (j + N)) p}
  have hb := locallyUniformlyBoundedAbove_of_canonicalL1 hu hv hlim
  have htailBound (N : ℕ) : FirstPass.LocallyUniformlyBoundedAbove
      (range (fun j => u (j + N))) univ := by
    intro p hp
    obtain ⟨O, hO, C, hC⟩ := hb p hp
    refine ⟨O, hO, C, ?_⟩
    rintro f ⟨j, rfl⟩ q hq
    exact hC (u (j + N)) (mem_range_self (j + N)) q hq
  have hS : ∀ N, A.LocallyPluripolar (S N) :=
    fun N => locallyPluripolar_sup_exceptional (fun j => hu (j + N)) (htailBound N)
  apply (LocallyPluripolar.iUnion hS).mono
  intro p hp
  by_contra hnot
  have ht (N : ℕ) : (⨆ j, u (j + N) p) = uscSup (fun j => u (j + N)) p := by
    apply le_antisymm (le_uscRegularization (fun q => ⨆ j, u (j + N) q) p)
    apply le_of_not_gt
    exact fun h => hnot (mem_iUnion.mpr ⟨N, h⟩)
  have hpoint := congrFun (iInf_uscSup_tail_eq_of_canonicalL1 hu hv hlim) p
  have hraw : limsup (fun j => u j p) atTop = v p := by
    rw [limsup_eq_iInf_iSup_of_nat']
    exact (iInf_congr ht).trans hpoint
  exact hp hraw.symm

/-- Literal whole regularized-tail identity from the original real local
L1 hypothesis on an atlas whose dimensions may vary. -/
theorem iInf_uscSup_tail_eq_of_localL1
    {u : ℕ → X → EReal} {v : X → EReal}
    (hu : ∀ j, A.IsPSH (u j)) (hv : A.IsPSH v)
    (hlim : A.L1LocallyTendsto u v) :
    (fun p => ⨅ N : ℕ, uscSup (fun j => u (j + N)) p) = v :=
  iInf_uscSup_tail_eq_of_canonicalL1 hu hv
    (canonicalL1LocallyTendsto_of_localL1 hu hv hlim)

/-- Both clauses of the original local L1 corollary, from its literal real
L1 assumption: the whole regularized-tail identity and genuine source
pluripolar pole witnesses for the complete raw-limsup discrepancy set. -/
theorem localL1_regularized_tails_and_pluripolar_discrepancy
    {u : ℕ → X → EReal} {v : X → EReal}
    (hu : ∀ j, A.IsPSH (u j)) (hv : A.IsPSH v)
    (hlim : A.L1LocallyTendsto u v) :
    (fun p => ⨅ N : ℕ, uscSup (fun j => u (j + N)) p) = v ∧
      A.LocallyPluripolar {p | v p ≠ limsup (fun j => u j p) atTop} := by
  have hcanonical := canonicalL1LocallyTendsto_of_localL1 hu hv hlim
  exact ⟨iInf_uscSup_tail_eq_of_canonicalL1 hu hv hcanonical,
    locallyPluripolar_limsup_discrepancy_of_canonicalL1 hu hv hcanonical⟩

end SGPT.PSH.VariableComplexAtlas
