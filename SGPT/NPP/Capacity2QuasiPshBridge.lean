import SGPT.NPP.Capacity2LocalQuasiContinuity
import SGPT.PSH.AtlasOpenRestriction
import SGPT.Toric.ThetaPSHExtension

/-!
# Quasi-psh functions on an open subset: from the source definition to the local form

Source `def:qpsh` applied to the complex manifold `U` (an open subset of `X` with its inherited
atlas `openRestriction`): `f : U → [-∞, ∞)` is quasi-psh if `f ∈ PSH(U, θ')` for some closed real
smooth `(1,1)`-form `θ'` on `U`.  We show that such an `f` (extended arbitrarily outside `U`) is
quasi-psh on `U` in the local form `IsLocalQuasiPshOn`, and deduce the source statement
`ex:psh_qc` for the open subset `U`.  The same is shown for `θ`-psh functions on `U` for a form
`θ` on `X` (`IsThetaPSHOn`, the convention of `thm:loc_conv_cap`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Extension of a function on an open subset by `-∞`. -/
def extendBot (U : Set M) (f : U → EReal) : M → EReal := by
  classical
  exact fun x => if h : x ∈ U then f ⟨x, h⟩ else ⊥

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
@[simp] theorem extendBot_val (U : Set M) (f : U → EReal) (x : U) :
    extendBot U f x.1 = f x := by
  classical
  simp [extendBot]

omit [IsComplexManifold n M] in
/-- Germs of quasi-psh functions transfer along eventual equality. -/
theorem quasiPlurisubharmonicAt_congr {u v : ComplexModel n → EReal} {z : ComplexModel n}
    (hu : QuasiPlurisubharmonicAt u z) (huv : u =ᶠ[𝓝 z] v) : QuasiPlurisubharmonicAt v z := by
  obtain ⟨p, h, hp, hh, heq⟩ := hu
  exact ⟨p, h, hp, hh, huv.symm.trans heq⟩

/-- **Bridge from the source `def:qpsh` on `U`.**  A quasi-psh function on the complex manifold
`U` (some closed real smooth `(1,1)`-form on `U`) is quasi-psh on `U` in the local form. -/
theorem isLocalQuasiPshOn_of_openRestriction_isQPSH (U : Opens M) {f : U → EReal}
    (hf : ((ofFixedModel n M).openRestriction U).IsQPSH f) :
    IsLocalQuasiPshOn (n := n) (U : Set M) (extendBot U f) := by
  classical
  by_cases hU : Nonempty U
  swap
  · refine ⟨fun e z hz => absurd ⟨⟨_, hz.2⟩⟩ hU, fun x hx => absurd ⟨⟨x, hx⟩⟩ hU⟩
  obtain ⟨θ', hθ'⟩ := hf
  revert θ' hθ'
  unfold openRestriction
  rw [dif_pos hU]
  intro θ' hθ'
  constructor
  · intro e z hz
    have hzt : z ∈ (e.val.subtypeRestr hU).target := by
      have hps : (⟨e.val.symm z, hz.2⟩ : U).val ∈ e.val.source := e.val.map_target hz.1
      have h := e.val.map_subtype_source hU hps
      simpa only [e.val.right_inv hz.1] using h
    have h1 := hθ'.chart_quasiPSH e z hzt
    refine quasiPlurisubharmonicAt_congr h1 ?_
    filter_upwards [(e.val.subtypeRestr hU).open_target.mem_nhds hzt] with y hy
    change f ((e.val.subtypeRestr hU).symm y) = extendBot (U : Set M) f (e.val.symm y)
    rw [← e.val.subtypeRestr_symm_apply hU hy]
    exact (extendBot_val (U : Set M) f _).symm
  · intro x hx W hW hxW
    obtain ⟨V, g, hxV, hg⟩ := exists_atlas_local_potential θ' (⟨x, hx⟩ : U)
    have hpsh := hθ'.2 V g hg
    obtain ⟨y, ⟨-, hyW⟩, hyb⟩ := hpsh.locallyNondegenerate hg.1 ⟨x, hx⟩ hxV
      (Subtype.val ⁻¹' W) (hW.preimage continuous_subtype_val) hxW
    refine ⟨y.1, ⟨hyW, y.2⟩, fun hbot => hyb ?_⟩
    have : f y = ⊥ := by simpa only [extendBot_val] using hbot
    change f y + (g y : EReal) = ⊥
    rw [this, EReal.bot_add]

/-- **Bridge from `PSH(U, θ)` for a form `θ` on `X`** (`IsThetaPSHOn`, the convention used for
`thm:loc_conv_cap`): such functions are quasi-psh on `U` in the local form. -/
theorem isLocalQuasiPshOn_of_isThetaPSHOn {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {U : Set M} (hUo : IsOpen U) {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSHOn θ u U) : IsLocalQuasiPshOn (n := n) U u := by
  constructor
  · intro e z hz
    obtain ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩ := exists_chart_local_potential θ e hz.1
    have hWU : IsOpen (W ∩ (e.val.target ∩ e.val.symm ⁻¹' U) : Set (ComplexModel n)) :=
      hW.inter (e.val.isOpen_inter_preimage_symm hUo)
    let V := e.val.source ∩ e.val ⁻¹' (W ∩ (e.val.target ∩ e.val.symm ⁻¹' U))
    have hg : (ofFixedModel n M).IsAtlasLocalPotential θ V (ρ ∘ e.val) :=
      coordinate_potential_isAtlasLocalPotential θ e hWU (fun y hy => hy.2.1)
        (hρ.mono inter_subset_left) (heq.mono inter_subset_left)
    have hVU : V ⊆ U := fun y hy => by
      have := hy.2.2.2
      rwa [mem_preimage, e.val.left_inv hy.1] at this
    have hpsh := hu.2 V (ρ ∘ e.val) hVU hg
    have hzV : e.val.symm z ∈ V := by
      refine ⟨e.val.map_target hz.1, ?_⟩
      change e.val (e.val.symm z) ∈ W ∩ (e.val.target ∩ e.val.symm ⁻¹' U)
      rw [e.val.right_inv hz.1]
      exact ⟨hzW, hz⟩
    refine ⟨(ofFixedModel n M).coordinate (fun x ↦ u x + ((ρ ∘ e.val) x : EReal)) e,
      fun y ↦ -ρ y, hpsh.chartPlurisubharmonic e z ⟨hz.1, hzV⟩, ?_, ?_⟩
    · filter_upwards [hW.mem_nhds hzW] with y hy
      exact ((hρ.neg) y hy).contDiffAt (hW.mem_nhds hy)
    · filter_upwards [hW.mem_nhds hzW] with y hy
      change u (e.val.symm y) =
        (u (e.val.symm y) + (ρ (e.val (e.val.symm y)) : EReal)) + ((-ρ y : ℝ) : EReal)
      rw [e.val.right_inv (hWe hy), add_assoc, ← EReal.coe_add, add_neg_cancel,
        EReal.coe_zero, add_zero]
  · intro x hx W hW hxW
    obtain ⟨V₀, g, hxV₀, hg₀⟩ := exists_atlas_local_potential θ x
    have hg : (ofFixedModel n M).IsAtlasLocalPotential θ (V₀ ∩ U) g :=
      hg₀.mono (hg₀.1.inter hUo) inter_subset_left
    have hpsh := hu.2 (V₀ ∩ U) g inter_subset_right hg
    obtain ⟨y, ⟨⟨-, hyU⟩, hyW⟩, hyb⟩ := hpsh.locallyNondegenerate hg.1 x ⟨hxV₀, hx⟩ W hW hxW
    refine ⟨y, ⟨hyW, hyU⟩, fun hbot => hyb ?_⟩
    change u y + (g y : EReal) = ⊥
    rw [hbot, EReal.bot_add]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **Source `ex:psh_qc`, first claim, for an open subset `U ⊆ X`.**  A quasi-psh function on the
complex manifold `U` (`def:qpsh` for `U`) is quasi-continuous on `U` (`def:qc_fun`, capacity of
any big form). -/
theorem sourceQuasiContinuousOn_of_openRestriction_isQPSH (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {f : U → EReal} (hf : ((ofFixedModel n M).openRestriction U).IsQPSH f) :
    SourceQuasiContinuousOn θ U f := by
  have h := sourceQuasiContinuousOn_of_isLocalQuasiPshOn omega θ hbig U
    (isLocalQuasiPshOn_of_openRestriction_isQPSH U hf)
  simpa only [extendBot_val] using h

/-- **Source `ex:psh_qc`, second claim, for an open subset `U ⊆ X`.**  For quasi-psh `φ, ψ` on
the complex manifold `U`, the function equal to `φ - ψ` where `φ ∨ ψ ≠ -∞` and to `+∞`
elsewhere is quasi-continuous on `U`. -/
theorem sourceQuasiContinuousOn_qpshDifference_of_openRestriction
    (omega : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (U : Opens M) {φ ψ : U → EReal} (hφ : ((ofFixedModel n M).openRestriction U).IsQPSH φ)
    (hψ : ((ofFixedModel n M).openRestriction U).IsQPSH ψ) :
    SourceQuasiContinuousOn θ U (qpshDifference φ ψ) := by
  have h := sourceQuasiContinuousOn_qpshDifference_of_isLocalQuasiPshOn omega θ hbig U
    (isLocalQuasiPshOn_of_openRestriction_isQPSH U hφ)
    (isLocalQuasiPshOn_of_openRestriction_isQPSH U hψ)
  have he : (fun x : U => qpshDifference (extendBot (U : Set M) φ) (extendBot (U : Set M) ψ) x.1)
      = qpshDifference φ ψ := by
    funext x
    simp only [qpshDifference, extendBot_val]
  rwa [he] at h

end SGPT.NPP
