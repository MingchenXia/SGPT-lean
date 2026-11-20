import SGPT.Unibranch.ComplexSpaceFormConstantFiber
import SGPT.Unibranch.ComplexSpaceThetaPSHPullbackFinite
import SGPT.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-! Actual theta-PSH restriction to genuine smooth probes in a literal
fiber, with gauge zero-ddc manufactured from the original form pullback.
Blueprint: complex-space-theta-fiber-domain.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.SourceReducedComplexSpace

private theorem modelPullback_at {X : SourceReducedComplexSpace} {m : ℕ}
    {U : Opens (ComplexModel m)} (F : domainSpace U ⟶ X) (φ : X.obj.left → EReal)
    (c : (univ : Set U)) : modelPullback F.hom.left φ c.val.val = φ (F.hom.left.base c) := by
  dsimp only [modelPullback]
  split_ifs with hc
  · rfl
  · exact False.elim (hc c.val.property)

/-- The actual uncorrected fiber restriction satisfies every genuine disc
inequality on every original smooth domain probe. The local gauge's zero
ddc is produced from actual constant-composite form naturality. -/
theorem IsThetaPSH.discPshOn_modelPullback_of_constant
    {X Y : SourceReducedComplexSpace} {m : ℕ} (θ : SpaceForm X 2) (π : Y ⟶ X)
    {ψ : Y.obj.left → EReal} (hψ : Y.IsThetaPSH (SpaceForm.pullback θ π) ψ)
    {U : Opens (ComplexModel m)} (F : domainSpace U ⟶ Y) (x : X.obj.left)
    (hF : ∀ c : (univ : Set U),π.hom.left.base (F.hom.left.base c) = x) :
    DiscPshOn (modelPullback F.hom.left ψ) U := by
  apply SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn
  intro z hz
  let c : (univ : Set U) := ⟨⟨z,hz⟩,trivial⟩
  obtain ⟨e,he,-,g,hg,hres,hpsh⟩ := hψ (F.hom.left.base c)
  obtain ⟨W,hW,hzW,hWU,G,hG,hmaps,hfac⟩ :=
    LocalEmbedding.exists_contDiffOn_factor F.hom.left (Over.w F.hom) e c he
  let V : Opens (ComplexModel m) := ⟨W,hW⟩
  have hcarrier : ∀ a : (univ : Set V),
      (⟨G a.val.val,hmaps a.val.property⟩ : e.ambient) ∈ e.carrier := by
    intro a
    obtain ⟨b,hb,-⟩ := hfac ⟨⟨a.val.val,hWU a.val.property⟩,trivial⟩ a.val.property
    have hval : (⟨G a.val.val,hmaps a.val.property⟩ : e.ambient) = b.val := Subtype.ext hb.symm
    rw [hval]
    exact b.property
  let M := analyticModelMorphism isComplexAnalyticSubset_univ e.analytic G hG hmaps hcarrier
  let corrected : e.carrier → EReal := fun b => (g b.val.val : EReal) + ψ (e.toPoint b)
  have hcorrected := discPshOn_modelPullback hpsh.2 M.hom.left (Over.w M.hom)
  have hrep : ∀ w ∈ W,modelPullback M.hom.left corrected w =
      (g (G w) : EReal) + modelPullback F.hom.left ψ w := by
    intro w hw
    let a : (univ : Set V) := ⟨⟨w,hw⟩,trivial⟩
    let b : (univ : Set U) := ⟨⟨w,hWU hw⟩,trivial⟩
    rw [modelPullback_at M corrected a,modelPullback_at F ψ b]
    obtain ⟨q,hq,hpq⟩ := hfac b hw
    have hMq : M.hom.left.base a = q := by
      apply Subtype.ext
      apply Subtype.ext
      exact hq.symm
    change (g ((M.hom.left.base a).val.val) : EReal) + ψ (e.toPoint (M.hom.left.base a)) = _
    rw [hMq,hq,hpq]
    rfl
  have hpCorr : PlurisubharmonicOn
      (fun w => (g (G w) : EReal) + modelPullback F.hom.left ψ w) W :=
    (hcorrected.congr hrep).plurisubharmonicOn hW
  have hgG : ContDiffOn ℝ ∞ (g ∘ G) W := hg.comp (hG.restrict_scalars ℝ) hmaps
  have hzDDC : ∀ w ∈ W,smoothDDC (g ∘ G) w = 0 := by
    intro w hw
    exact SpaceForm.smoothDDC_comp_eq_zero_of_constant θ π hg hres F x hF hW hWU hG hfac hw
  have hneg : PlurisubharmonicOn (fun w => ((-(g ∘ G) w : ℝ) : EReal)) W := by
    apply plurisubharmonicOn_coe_of_smoothDDC_eq_zero hW hgG.neg
    intro w hw
    rw [smoothDDC_neg hW hgG hw,hzDDC w hw,neg_zero]
  apply ((hpCorr z hzW).add (hneg z hzW)).congr
  exact Eventually.of_forall fun w => by
    change ((g (G w) : EReal) + modelPullback F.hom.left ψ w) +
      ((-g (G w) : ℝ) : EReal) = modelPullback F.hom.left ψ w
    exact (congrArg (fun a : EReal => a + ((-g (G w) : ℝ) : EReal))
      (add_comm (g (G w) : EReal) (modelPullback F.hom.left ψ w))).trans (by
        simpa only [zero_sub,EReal.coe_zero,add_zero] using
          corrected_add_sub (modelPullback F.hom.left ψ w) (g (G w)) 0)

end SGPT.Unibranch.SourceReducedComplexSpace
