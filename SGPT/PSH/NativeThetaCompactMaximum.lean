import SGPT.PSH.IntrinsicRationalAnalytic
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Preserve every coefficient of the original native closed form in ALL charts. -/
def nativeClosedFormToAtlas (θ : ClosedRealOneOneForm n M) :
    AtlasClosedRealOneOneForm (ofFixedModel n M) where
  coeff := θ.val.coeff
  smooth := θ.val.smooth
  compatible := θ.val.compatible
  closed := θ.property.1
  typeOneOne := θ.property.2

/-- The original all-chart tensor, closedness and type fields are the native fields. -/
def atlasClosedFormToNative (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    ClosedRealOneOneForm n M :=
  ⟨{ coeff := θ.coeff, smooth := θ.smooth, compatible := θ.compatible },
    θ.closed, θ.typeOneOne⟩

private theorem atlas_native_inverse (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    nativeClosedFormToAtlas (atlasClosedFormToNative θ) = θ := by
  cases θ
  rfl

private theorem native_atlas_inverse (θ : ClosedRealOneOneForm n M) :
    atlasClosedFormToNative (nativeClosedFormToAtlas θ) = θ := by
  rcases θ with ⟨θ, hθ⟩
  cases θ
  rfl

/-- Genuine produced local potentials and the actual ANY-potential mother identify
the whole original universal criterion with the same native nondegenerate one. -/
theorem isThetaPSH_iff_nativeThetaPotential
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal) :
    (ofFixedModel n M).IsThetaPSH θ u ↔
      IsThetaPshPotential (atlasClosedFormToNative θ).val u := by
  let A := ofFixedModel n M
  constructor
  · intro hu
    refine ⟨?_, (IsQPSH.locallyNondegenerate ⟨θ, hu⟩)⟩
    intro e z hz
    obtain ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩ := exists_chart_local_potential θ e hz
    let U := e.val.source ∩ e.val ⁻¹' W
    let g := ρ ∘ e.val
    have hg : A.IsAtlasLocalPotential θ U g :=
      coordinate_potential_isAtlasLocalPotential θ e hW hWe hρ heq
    have hp := (hu.2 U g hg).chartPlurisubharmonic e
    refine ⟨W, ρ, hzW, ⟨hW, hWe, hρ, heq⟩, ?_⟩
    have hsub : W ⊆ e.val.target ∩ e.val.symm ⁻¹' U := by
      intro y hy
      refine ⟨hWe hy, e.val.map_target (hWe hy), ?_⟩
      change e.val (e.val.symm y) ∈ W
      simpa only [ofFixedModel, e.val.right_inv (hWe hy)] using hy
    exact plurisubharmonicOn_congr hW (hp.mono hsub) (fun y hy => by
      change u (e.val.symm y) + (ρ (e.val (e.val.symm y)) : EReal) =
        u (e.val.symm y) + (ρ y : EReal)
      rw [e.val.right_inv (hWe hy)])
  · intro hu
    refine ⟨hu.1.quasiPlurisubharmonic.ne_top, ?_⟩
    intro U g hg
    apply (isPSHOn_iff_chart_and_nondegenerate hg.1).mpr
    refine ⟨?_, ?_⟩
    · intro e
      let D := e.val.target ∩ e.val.symm ⁻¹' U
      have hD : IsOpen D := e.val.isOpen_inter_preimage_symm hg.1
      have hl : IsSmoothLocalPotential (atlasClosedFormToNative θ).val e D
          (g ∘ e.val.symm) := ⟨hD, inter_subset_left, hg.2.1 e, hg.2.2 e⟩
      exact ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
        hu.1 e hl
    · intro x hx O hO hxO
      obtain ⟨y, hy, hn⟩ := hu.2 x (O ∩ U) (hO.inter hg.1) ⟨hxO, hx⟩
      exact ⟨y, ⟨hy.2, hy.1⟩, EReal.add_ne_bot_iff.mpr ⟨hn, EReal.coe_ne_bot _⟩⟩

variable [CompactSpace M]

/-- The true finite-family domination producer manufactures ONE original background. -/
theorem exists_common_nativeKahler_background (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : (ofFixedModel n M).IsQPSH u)
    (hv : (ofFixedModel n M).IsQPSH v) :
    ∃ C : ℝ, 0 < C ∧
      (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas (C • omega.form)) u ∧
      (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas (C • omega.form)) v := by
  obtain ⟨θ, hθ⟩ := hu
  obtain ⟨η, hη⟩ := hv
  let a := atlasClosedFormToNative θ
  let b := atlasClosedFormToNative η
  have ha : IsThetaPshPotential a.val u := (isThetaPSH_iff_nativeThetaPotential θ u).mp hθ
  have hb : IsThetaPshPotential b.val v := (isThetaPSH_iff_nativeThetaPotential η v).mp hη
  obtain ⟨C, hC, h⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega
    (fun i : Bool => if i then -b else -a)
  have hsa : (-a + C • omega.form).val.IsSemipositive := by simpa using h false
  have hsb : (-b + C • omega.form).val.IsSemipositive := by simpa using h true
  have hpa := LocalPotentials.isThetaPshPotential_add_of_semipositive ha hsa
  have hpb := LocalPotentials.isThetaPshPotential_add_of_semipositive hb hsb
  have hea : a + (-a + C • omega.form) = C • omega.form := by abel
  have heb : b + (-b + C • omega.form) = C • omega.form := by abel
  rw [hea] at hpa
  rw [heb] at hpb
  refine ⟨C, hC, ?_, ?_⟩
  · apply (isThetaPSH_iff_nativeThetaPotential (nativeClosedFormToAtlas (C • omega.form)) u).mpr
    simpa only [native_atlas_inverse] using hpa
  · apply (isThetaPSH_iff_nativeThetaPotential (nativeClosedFormToAtlas (C • omega.form)) v).mpr
    simpa only [native_atlas_inverse] using hpb

/-- The SAME internally produced whole background gives original universal maximum. -/
theorem IsQPSH.max_compactKahler (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : (ofFixedModel n M).IsQPSH u)
    (hv : (ofFixedModel n M).IsQPSH v) :
    (ofFixedModel n M).IsQPSH (fun x => max (u x) (v x)) := by
  obtain ⟨C, _hC, hθ, hη⟩ := exists_common_nativeKahler_background omega hu hv
  exact ⟨nativeClosedFormToAtlas (C • omega.form), hθ.max hη⟩

/-- Pair the actual compact global maximum with unchanged original intrinsic closure. -/
theorem IsQPSH.max_intrinsic_compactKahler (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : (ofFixedModel n M).IsQPSH u)
    (hv : (ofFixedModel n M).IsQPSH v)
    (hanU : (ofFixedModel n M).HasRationalAnalyticType u)
    (hanV : (ofFixedModel n M).HasRationalAnalyticType v) :
    (ofFixedModel n M).IsQPSH (fun x => max (u x) (v x)) ∧
      (ofFixedModel n M).HasRationalAnalyticType (fun x => max (u x) (v x)) :=
  ⟨hu.max_compactKahler omega hv, hanU.max hanV⟩

end SGPT.PSH.VariableComplexAtlas
