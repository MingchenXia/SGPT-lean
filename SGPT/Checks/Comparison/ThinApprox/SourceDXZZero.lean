import SGPT.Checks.Comparison.SourceRationalHullImage
import SGPT.Checks.Comparison.SourceAnalytificationMap
import SGPT.Checks.Comparison.SourceDXZPOrder
import SGPT.NAPotential.Homogeneous
import SGPT.NPP.DimensionZero

/-! Actual original order and preimages in dimension zero, without point-trace imports.
Blueprint: thin-source-dxz-all.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
noncomputable section
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZZero

open Set AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.NativePicard SGPT.Foundations.Envelope

section Order
variable {V : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel 0) V]
  [IsComplexManifold 0 V] [MeasurableSpace V] [BorelSpace V]
  [CompactSpace V] [ConnectedSpace V]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 V)}

theorem sourcePEquivalent_of_finite (omegaV : KahlerBackground 0 V)
    {u v : V → EReal} (hu : ∀ y, u y ≠ ⊤ ∧ u y ≠ ⊥)
    (hv : ∀ y, v y ≠ ⊤ ∧ v y ≠ ⊥) : SourcePEquivalent (n := 0) u v := by
  let : Subsingleton V := SGPT.NPP.subsingleton_of_dim_zero
  have hups : IsThetaPshPotential omegaV.form.val u :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials omegaV.form)
      (fun z => (hu z).1) (fun z => (hu z).2)
  have hvps : IsThetaPshPotential omegaV.form.val v :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials omegaV.form)
      (fun z => (hv z).1) (fun z => (hv z).2)
  have hmore (a b : V → EReal) (ha : ∀ y, a y ≠ ⊤ ∧ a y ≠ ⊥)
      (hb : ∀ y, b y ≠ ⊤ ∧ b y ≠ ⊥) : MoreSingularOn a b Set.univ := by
    by_cases hV : Nonempty V
    · obtain ⟨y⟩ := hV
      have haco : ((a y).toReal : EReal) = a y := EReal.coe_toReal (ha y).1 (ha y).2
      have hbco : ((b y).toReal : EReal) = b y := EReal.coe_toReal (hb y).1 (hb y).2
      refine ⟨(a y).toReal - (b y).toReal, ?_⟩
      intro z _
      rw [Subsingleton.elim z y, ← haco, ← hbco, ← EReal.coe_add]
      exact_mod_cast (by linarith : (a y).toReal ≤
        (b y).toReal + ((a y).toReal - (b y).toReal))
    · exact ⟨0, fun z _ => (hV ⟨z⟩).elim⟩
  exact ⟨sourcePOrder_of_moreSingularOn omegaV omegaV.form omegaV.form hups hvps
      (hmore u v hu hv),
    sourcePOrder_of_moreSingularOn omegaV omegaV.form omegaV.form hvps hups
      (hmore v u hv hu)⟩

theorem sourceNAPOrder_iff_max_le (Γ Γ' : SourceNAPotential θ)
    (ω : SourceKahlerForm 0 V) :
    SourceNAPOrder Γ Γ' ↔ (Γ.component ω).val.max ≤ (Γ'.component ω).val.max := by
  rw [sourceNAPOrder_iff_component Γ Γ' ω]
  refine ⟨fun h => h.cutoff_le, fun h => ⟨h, fun r hr => ?_⟩⟩
  have hfin : ∀ (G : SourceNAPotential θ) (s : ℝ) (hs : s < (G.component ω).val.max) (y : V),
      (G.component ω).val.potential ⟨s, hs⟩ y ≠ ⊤ ∧
        (G.component ω).val.potential ⟨s, hs⟩ y ≠ ⊥ := fun G s hs =>
    (SGPT.NPP.isThetaPSH_iff_finite_of_dim_zero _ _).mp ((G.component ω).val.thetaPSH ⟨s, hs⟩)
  exact (sourcePEquivalent_of_finite (sourceKahlerFormRepresentative ω)
    (hfin Γ r hr) (hfin Γ' r (hr.trans_le h))).1
end Order

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 0 f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]
local instance : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 0
local instance : IsComplexManifold 0 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 0
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}

theorem sourceNAPOrder_iff_naPotentialAnAt_le (Γ Γ' : SourceNAPotential θ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    SourceNAPOrder Γ Γ' ↔ ∀ v : BerkovichPoint f,
      naPotentialAnAt 0 E Γ ω v ≤ naPotentialAnAt 0 E Γ' ω v := by
  simp_rw [SGPT.NAPotential.BJ.SourceZeroModels.naPotentialAnAt_eq_of_dim_zero,
    EReal.coe_le_coe_iff]
  rw [sourceNAPOrder_iff_max_le Γ Γ' ω]
  exact ⟨fun h _ => h, fun h => h (BerkovichPoint.trivial f)⟩

theorem exists_eq_const {Λ : RationalPicardSpace X} {ψ : BerkovichPoint f → EReal}
    (hψ : IsModuleTopologyPSH.{0} f Λ ψ) : ∃ c : ℝ, ψ = fun _ => (c : EReal) := by
  have := SGPT.NAPotential.BJ.GfIm.RationalHull.NarrowDimensionZero.berkovichPoint_subsingleton_of_dim_zero f
  obtain ⟨v, hv⟩ := hψ.1
  have htop : ψ v ≠ ⊤ := IsPSHForNumericalTopology.ne_top f hψ v
  refine ⟨(ψ v).toReal, funext fun w => ?_⟩
  rw [Subsingleton.elim w v, EReal.coe_toReal htop hv]

theorem component_max_translate_homogeneous (c : ℝ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    (((SourceNAPotential.homogeneous (SGPT.NPP.isThetaPSH_const_of_dim_zero θ 0)).translate c).component
      ω).val.max = c := by
  rw [← sourceNAPotentialCutoff_eq_component (sourceKahlerFormRepresentative ω),
    sourceNAPotentialCutoff_translate, sourceNAPotentialCutoff_homogeneous, zero_add]

variable {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f 0 E M) {m : ℕ}
  (hm : 0 < m)
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
theorem naAnalytification_surjective (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    Function.Surjective (SGPT.NAPotential.BJ.SourceNet.naAnalytification (θ := θ) f 0 E b HM hm hθ ω) := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨c, rfl⟩ := exists_eq_const f hψ
  refine ⟨(SourceNAPotential.homogeneous (SGPT.NPP.isThetaPSH_const_of_dim_zero θ 0)).translate c,
    Subtype.ext (funext fun v => ?_)⟩
  rw [SGPT.NAPotential.BJ.SourceNet.naAnalytification_apply,
    SGPT.NAPotential.BJ.SourceZeroModels.naPotentialAnAt_eq_of_dim_zero,
    component_max_translate_homogeneous f]

include hm hθ in
theorem source_DXZ (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) :
    (∀ Γ Γ' : SourceNAPotential θ, SourceNAPOrder Γ Γ' ↔
      ∀ v, (SGPT.NAPotential.BJ.SourceNet.naAnalytification f 0 E b HM hm hθ ω Γ).1 v ≤
        (SGPT.NAPotential.BJ.SourceNet.naAnalytification f 0 E b HM hm hθ ω Γ').1 v) ∧
      Function.Bijective (SGPT.NAPotential.BJ.SourceNet.naAnalytification (θ := θ) f 0 E b HM hm hθ ω) := by
  refine ⟨fun Γ Γ' => sourceNAPOrder_iff_naPotentialAnAt_le f E Γ Γ' ω, ?_,
    naAnalytification_surjective f E b HM hm hθ ω⟩
  intro Γ Γ' h
  have he := congrArg Subtype.val h
  exact SourceNAPOrder.antisymm
    ((sourceNAPOrder_iff_naPotentialAnAt_le f E Γ Γ' ω).mpr fun v => (congrFun he v).le)
    ((sourceNAPOrder_iff_naPotentialAnAt_le f E Γ' Γ ω).mpr fun v => (congrFun he v).ge)
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZZero
