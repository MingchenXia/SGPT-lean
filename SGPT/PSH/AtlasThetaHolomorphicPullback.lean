import SGPT.PSH.AtlasLocalPotentialPullback
import SGPT.PSH.QuasiPSHIdentity
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-! # Original theta-PSH pullback and exact component qualification -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- The actual target quasi-PSH decomposition transports on the genuine
coordinate domain, without any source finite-point hypothesis. -/
theorem IsThetaPSH.chart_quasiPSH_comp_holomorphic
    {θ : AtlasClosedRealOneOneForm B} {u : Y → EReal} (hu : B.IsThetaPSH θ u)
    {f : X → Y} (hf : A.IsHolomorphic B f) (i : A.Index) :
    QuasiPlurisubharmonicOn (A.coordinate (u ∘ f) i) (A.chart i).target := by
  intro z hz
  obtain ⟨j, hj⟩ := B.cover (f ((A.chart i).symm z))
  have hzj : z ∈ atlasCoordinateDomain A B f i j := ⟨hz, hj⟩
  have hp := Pending.HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic
    (atlasCoordinateDomain_isOpen hf i j) (atlasCoordinateMap_contDiffOn hf i j) hzj
    (hu.chart_quasiPSH j _ (atlasCoordinateMap_mem_target hzj))
  apply hp.congr
  filter_upwards [(atlasCoordinateDomain_isOpen hf i j).mem_nhds hzj] with y hy
  change u ((B.chart j).symm ((B.chart j) (f ((A.chart i).symm y)))) =
    u (f ((A.chart i).symm y))
  rw [(B.chart j).left_inv hy.2]

/-- Every actual source local potential gives the original corrected PSH
germs. Zero-ddc smooth differences are proved from the whole tensor equalities. -/
theorem IsThetaPSH.chart_corrected_comp_holomorphic
    {θ : AtlasClosedRealOneOneForm B} {u : Y → EReal} (hu : B.IsThetaPSH θ u)
    {f : X → Y} (hf : A.IsHolomorphic B f) {U : Set X} {g : X → ℝ}
    (hg : A.IsAtlasLocalPotential (θ.holomorphicPullback hf) U g) (i : A.Index) :
    PlurisubharmonicOn (A.coordinate (fun x => u (f x) + (g x : EReal)) i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
  intro z hz
  obtain ⟨j, hj⟩ := B.cover (f ((A.chart i).symm z))
  have hzj : z ∈ atlasCoordinateDomain A B f i j := ⟨hz.1, hj⟩
  obtain ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩ :=
    exists_chart_local_potential θ j (atlasCoordinateMap_mem_target hzj)
  let V := (B.chart j).source ∩ (B.chart j) ⁻¹' W
  let b := ρ ∘ (B.chart j)
  have hb : B.IsAtlasLocalPotential θ V b :=
    coordinate_potential_isAtlasLocalPotential θ j hW hWe hρ heq
  have hpV := hu.2 V b hb
  have hbF := hb.comp_holomorphic hf
  let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ f ⁻¹' V)
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm
    (hg.1.inter (hb.1.preimage hf.1))
  have hzV : f ((A.chart i).symm z) ∈ V := ⟨hj, hzW⟩
  have hzD : z ∈ D := ⟨hz.1, hz.2, hzV⟩
  have hpT : PlurisubharmonicAt (B.coordinate (fun y => u y + (b y : EReal)) j)
      (atlasCoordinateMap A B f i j z) := by
    apply hpV.chartPlurisubharmonic j _
    refine ⟨atlasCoordinateMap_mem_target hzj, ?_⟩
    change (B.chart j).symm ((B.chart j) (f ((A.chart i).symm z))) ∈ V
    rw [(B.chart j).left_inv hj]
    exact hzV
  have hp := Pending.HolomorphicPullback.plurisubharmonicAt_comp_holomorphic
    (atlasCoordinateDomain_isOpen hf i j) (hf.2 i j) hzj hpT
  have hpF : PlurisubharmonicAt
      (fun y => u (f ((A.chart i).symm y)) + (b (f ((A.chart i).symm y)) : EReal)) z := by
    apply hp.congr
    filter_upwards [(atlasCoordinateDomain_isOpen hf i j).mem_nhds hzj] with y hy
    change u ((B.chart j).symm ((B.chart j) (f ((A.chart i).symm y)))) +
        (b ((B.chart j).symm ((B.chart j) (f ((A.chart i).symm y)))) : EReal) = _
    rw [(B.chart j).left_inv hy.2]
  have hgD : ContDiffOn ℝ ∞ (g ∘ (A.chart i).symm) D :=
    (hg.2.1 i).mono (fun _ hy => ⟨hy.1, hy.2.1⟩)
  have hbD : ContDiffOn ℝ ∞ ((b ∘ f) ∘ (A.chart i).symm) D :=
    (hbF.2.1 i).mono (fun _ hy => ⟨hy.1, hy.2.2⟩)
  have hzero : ∀ y ∈ D, smoothDDC (fun t =>
      g ((A.chart i).symm t) - b (f ((A.chart i).symm t))) y = 0 := by
    intro y hy
    change smoothDDC (fun t => (g ∘ (A.chart i).symm) t -
      ((b ∘ f) ∘ (A.chart i).symm) t) y = 0
    rw [PositiveClasses.smoothDDC_sub hD hgD hbD hy,
      hg.2.2 i ⟨hy.1, hy.2.1⟩, hbF.2.2 i ⟨hy.1, hy.2.2⟩, sub_self]
  have hpDiff := plurisubharmonicOn_coe_of_smoothDDC_eq_zero hD (hgD.sub hbD) hzero
  apply (hpF.add (hpDiff z hzD)).congr
  exact Eventually.of_forall fun y => corrected_add_sub
    (u (f ((A.chart i).symm y))) (b (f ((A.chart i).symm y))) (g ((A.chart i).symm y))

/-- Exact original component qualification, producing source nondegeneracy
and every original corrected PSH witness internally. -/
theorem IsThetaPSH.comp_holomorphic_iff_component_nonbot
    {θ : AtlasClosedRealOneOneForm B} {u : Y → EReal} (hu : B.IsThetaPSH θ u)
    {f : X → Y} (hf : A.IsHolomorphic B f) :
    A.IsThetaPSH (θ.holomorphicPullback hf) (u ∘ f) ↔
      ∀ x : X, ∃ y ∈ connectedComponent x, u (f y) ≠ ⊥ := by
  constructor
  · intro hp x
    exact (IsQPSH.locallyNondegenerate ⟨θ.holomorphicPullback hf, hp⟩) x
      (connectedComponent x) (A.isOpen_component x) mem_connectedComponent
  · intro hn
    have hnd : LocallyNondegenerate (u ∘ f) :=
      locallyNondegenerate_of_component_nonbot_of_chart_quasiPSH
        (hu.chart_quasiPSH_comp_holomorphic hf) hn
    refine ⟨fun x => hu.1 (f x), ?_⟩
    intro U g hg
    apply (isPSHOn_iff_chart_and_nondegenerate hg.1).mpr
    refine ⟨hu.chart_corrected_comp_holomorphic hf hg, ?_⟩
    intro x hx O hO hxO
    obtain ⟨y, hy, hny⟩ := hnd x (U ∩ O) (hg.1.inter hO) ⟨hx, hxO⟩
    exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hny, EReal.coe_ne_bot _⟩⟩

/-- The same exact criterion applies to the original existential global
background definition; the entire actual pulled background is supplied. -/
theorem IsQPSH.comp_holomorphic_iff_component_nonbot {u : Y → EReal}
    (hu : B.IsQPSH u) {f : X → Y} (hf : A.IsHolomorphic B f) :
    A.IsQPSH (u ∘ f) ↔ ∀ x : X, ∃ y ∈ connectedComponent x, u (f y) ≠ ⊥ := by
  constructor
  · intro hp x
    exact hp.locallyNondegenerate x (connectedComponent x)
      (A.isOpen_component x) mem_connectedComponent
  · intro hn
    obtain ⟨θ, hθ⟩ := hu
    exact ⟨θ.holomorphicPullback hf, (hθ.comp_holomorphic_iff_component_nonbot hf).mpr hn⟩

end SGPT.PSH.VariableComplexAtlas
