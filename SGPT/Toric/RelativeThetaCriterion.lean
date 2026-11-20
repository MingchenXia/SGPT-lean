import SGPT.Toric.ThetaPSHExtension
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff Classical
variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Actual preferred potentials give every original relative source test. -/
theorem isThetaPSHOn_of_chart_corrected
    {θ : AtlasClosedRealOneOneForm A} {u : X → EReal} {U : Set X}
    (ρ : (i : A.Index) → ComplexModel (A.dimension i) → ℝ)
    (hρ : ∀ i, ContDiffOn ℝ ∞ (ρ i) (A.chart i).target)
    (hform : ∀ i, EqOn (smoothDDC (ρ i)) (θ.coeff i) (A.chart i).target)
    (hpsh : ∀ i, PlurisubharmonicOn
      (fun z ↦ A.coordinate u i z + (ρ i z : EReal))
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U))
    (htop : ∀ x ∈ U, u x ≠ ⊤)
    (hnd : LocallyNondegenerateOn u U) : A.IsThetaPSHOn θ u U := by
  refine ⟨htop, ?_⟩
  intro V g hVU hg
  apply (isPSHOn_iff_chart_and_nondegenerate hg.1).mpr
  constructor
  · intro i
    let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' V
    let σ := g ∘ (A.chart i).symm
    have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hg.1
    have hρD : ContDiffOn ℝ ∞ (ρ i) D := (hρ i).mono inter_subset_left
    have hσ : ContDiffOn ℝ ∞ σ D := hg.2.1 i
    have hzero : ∀ z ∈ D, smoothDDC (fun y ↦ σ y - ρ i y) z = 0 := by
      intro z hz
      rw [PositiveClasses.smoothDDC_sub hD hσ hρD hz,
        hg.2.2 i hz, hform i hz.1, sub_self]
    have hdiff := plurisubharmonicOn_coe_of_smoothDDC_eq_zero hD
      (hσ.sub hρD) hzero
    have hp : PlurisubharmonicOn
        (fun z ↦ A.coordinate u i z + (ρ i z : EReal)) D :=
      (hpsh i).mono (fun _ hz ↦ ⟨hz.1, hVU hz.2⟩)
    have hadd := hp.add hdiff
    intro z hz
    apply (hadd z hz).congr
    exact Eventually.of_forall fun y ↦ corrected_add_sub (u ((A.chart i).symm y))
      (ρ i y) (g ((A.chart i).symm y))
  · intro x hx O hO hxO
    obtain ⟨y, hy, hfin⟩ := hnd x (hVU hx) (V ∩ O) (hg.1.inter hO) ⟨hx, hxO⟩
    refine ⟨y, hy.2, ?_⟩
    intro hb
    rcases EReal.add_eq_bot_iff.mp hb with hb | hb
    · exact hfin hb
    · exact EReal.coe_ne_bot (g y) hb

/-- Existing whole-space API becomes a specialization of this single proof. -/
theorem isThetaPSH_global_from_relative
    {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (ρ : (i : A.Index) → ComplexModel (A.dimension i) → ℝ)
    (hρ : ∀ i, ContDiffOn ℝ ∞ (ρ i) (A.chart i).target)
    (hform : ∀ i, EqOn (smoothDDC (ρ i)) (θ.coeff i) (A.chart i).target)
    (hpsh : ∀ i, PlurisubharmonicOn
      (fun z ↦ A.coordinate u i z + (ρ i z : EReal)) (A.chart i).target)
    (htop : ∀ x, u x ≠ ⊤)
    (hnd : LocallyNondegenerateOn u univ) : A.IsThetaPSH θ u := by
  have hp := isThetaPSHOn_of_chart_corrected ρ hρ hform
    (fun i ↦ by simpa only [preimage_univ, inter_univ] using hpsh i)
    (fun x _ ↦ htop x) hnd
  exact ⟨htop, fun V g hg ↦ hp.2 V g (subset_univ _) hg⟩
/-- Original universal local tests genuinely produce non-bottom witnesses. -/
theorem IsThetaPSH.locallyNondegenerate
    {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hu : A.IsThetaPSH θ u) : LocallyNondegenerateOn u univ := by
  intro x _ O hO hxO
  obtain ⟨U, g, hxU, hg⟩ := exists_atlas_local_potential θ x
  obtain ⟨y, hy, hfin⟩ := ((hu.2 U g hg).locallyNondegenerate hg.1)
    x hxU O hO hxO
  refine ⟨y, ⟨mem_univ y, hy.2⟩, ?_⟩
  intro hb
  apply hfin
  change u y + (g y : EReal) = ⊥
  simp [hb]

/-- Genuine preferred whole-form potentials give corrected chart PSH
from the original universal source condition, rather than from a certificate. -/
theorem IsThetaPSH.preferred_chart_corrected
    {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hu : A.IsThetaPSH θ u) (i : A.Index)
    {ρ : ComplexModel (A.dimension i) → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ (A.chart i).target)
    (hform : EqOn (smoothDDC ρ) (θ.coeff i) (A.chart i).target) :
    PlurisubharmonicOn (fun z ↦ A.coordinate u i z + (ρ z : EReal))
      (A.chart i).target := by
  let U := (A.chart i).source ∩ (A.chart i) ⁻¹' (A.chart i).target
  have hg : A.IsAtlasLocalPotential θ U (ρ ∘ (A.chart i)) :=
    coordinate_potential_isAtlasLocalPotential θ i (A.chart i).open_target
      Subset.rfl hρ hform
  have hp := hu.2 U (ρ ∘ (A.chart i)) hg
  intro z hz
  have hx : (A.chart i).symm z ∈ U := by
    refine ⟨(A.chart i).map_target hz, ?_⟩
    change (A.chart i) ((A.chart i).symm z) ∈ (A.chart i).target
    rwa [(A.chart i).right_inv hz]
  apply (hp.chartPlurisubharmonic i z ⟨hz, hx⟩).congr
  filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy
  change u ((A.chart i).symm y) + (ρ ((A.chart i) ((A.chart i).symm y)) : EReal) =
    u ((A.chart i).symm y) + (ρ y : EReal)
  rw [(A.chart i).right_inv hy]

/-- The actual original universal theta tests give ordinary upper semicontinuity, including poles. -/
theorem IsThetaPSH.upperSemicontinuous
    {θ : AtlasClosedRealOneOneForm A} {u : X → EReal} (hu : A.IsThetaPSH θ u) :
    UpperSemicontinuous u := by
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  let e := A.chart i
  have hp := hu.chart_quasiPSH i (e x) (e.mapsTo hi)
  have hs := hp.upperSemicontinuousAt.comp (e.continuousAt hi)
  intro b hb
  have hb' : A.coordinate u i (e x) < b := by
    change u (e.symm (e x)) < b
    rwa [e.left_inv hi]
  have hv := hs b hb'
  filter_upwards [hv, e.open_source.mem_nhds hi] with y hy hyS
  change u (e.symm (e y)) < b at hy
  rwa [e.left_inv hyS] at hy

end SGPT.PSH.VariableComplexAtlas
