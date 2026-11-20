import SGPT.PSH.AtlasLogComponentIntegral
import SGPT.PSH.AtlasLogSingularities
import SGPT.PSH.AtlasGeometricQOpenCompatibility
import SGPT.PSH.AtlasNativeComponentInclusion

/-! ORIGINAL logarithmic input alone manufactures the actual local native
Cartier/product presentation on its actual component. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open scoped Topology Manifold ContDiff Classical
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

omit [T2Space X] [ParacompactSpace X] in
/-- Original QPSH restricts to EVERY genuine original open, including every
component of that open. Nondegeneracy is manufactured from the original input. -/
theorem original_qpsh_openRestriction {u : X → EReal} (hu : A.IsQPSH u) (U : Opens X) :
    (A.openRestriction U).IsQPSH (fun y : U => u y.val) := by
  apply (hu.comp_holomorphic_iff_component_nonbot
    (A.openRestriction_inclusion_isHolomorphic U)).mpr
  intro p
  let B := A.openRestriction U
  let O : Set X := Subtype.val '' (connectedComponent p)
  have hO : IsOpen O := U.isOpen.isOpenMap_subtype_val _ (B.isOpen_component p)
  have hp : p.val∈O := ⟨p,mem_connectedComponent,rfl⟩
  obtain ⟨q,hq,hfin⟩ := hu.locallyNondegenerate p.val O hO hp
  obtain ⟨r,hr,rfl⟩ := hq
  exact ⟨r,hr,hfin⟩

/-- The ORIGINAL literal log predicate constructs every actual local native
Cartier/product/coefficients/QPSH/remainder field. No native logarithmic or
compatibility certificate, uniform dimension or compactness is an input. -/
theorem original_log_local_component_integral
    {D : AtlasEffectiveGeometricQDivisor A} {u : X → EReal}
    (hu : SourceHasLogSingularitiesAlong D u) (x : X) :
    ∃ (U : Opens X) (hx : x∈U),
      letI := A.openRestriction_paracompactSpace U
      let B := A.openRestriction U
      let p : U := ⟨x,hx⟩
      letI := B.componentChartedSpace p
      letI := B.componentComplexManifold_of_paracompact p
      ∃ (d : ℕ) (H : EffectiveDivisor (B.pointDimension p) (B.componentOpen p))
        (G : B.componentOpen p → ℂ) (R : B.componentOpen p → ℝ) (C : ℝ),
        0<d ∧ (ofFixedModel (B.pointDimension p) (B.componentOpen p)).IsQPSH
          (fun q : B.componentOpen p => u q.val.val) ∧
        0≤C ∧ (∀ q,|R q|≤C) ∧
        (∀ Q : GeometricPrimeCarrier (B.pointDimension p) (B.componentOpen p),
          (D.nativeOpenRestrictionComponent U p).coefficient Q=
            (nativeCartierCoefficientAny H Q : ℚ)/(d : ℚ)) ∧
        (∀ q,HolomorphicAt (B.pointDimension p) G q ∧ ∀ g,
          H.ideal.mem q g ↔ IsInSpanAt (n := B.pointDimension p) (· = G) q g) ∧
        ∀ q : B.componentOpen p,u q.val.val=
          (((1/(d : ℚ) : ℚ) : ℝ) : EReal)*logNormSq (G q)+(R q : EReal) := by
  obtain ⟨U,hx,r,W,w,f,R0,C,_hW,hw,hf,hgen,hcoeff,hC,hR,hlog⟩ := hu.2 x
  let := A.openRestriction_paracompactSpace U
  let B := A.openRestriction U
  let p : U := ⟨x,hx⟩
  let := B.componentChartedSpace p
  let := B.componentComplexManifold_of_paracompact p
  let uU : U → EReal := fun y => u y.val
  obtain ⟨d,H,G,hd,hcoef,hH,hG⟩ := original_finite_logs_component_integral
    (D.openRestriction U) uU W w hw f hf hgen hcoeff R0 hlog p
  have hq := (original_qpsh_openRestriction hu.1 U).nativeComponent p
  refine ⟨U,hx,d,H,G,(fun q => R0 q.val),C,hd,hq,hC,(fun q => hR q.val),?_,hH,hG⟩
  intro Q
  rw [←nativeComponent_openRestriction_actual]
  exact hcoef Q

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
