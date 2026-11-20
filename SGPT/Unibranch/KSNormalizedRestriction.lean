import SGPT.Unibranch.KSNormalizedSubvariety
import SGPT.Unibranch.ComplexSpaceThetaPSHPullbackFinite
import SGPT.Unibranch.ComplexSpacePSHDensePullback
import SGPT.Unibranch.ComplexSpaceModelComponents

/-!
# Restriction of `θ`-psh functions of the ambient manifold to the normalization `Ỹ`

Lane KS (infrastructure for the trace chapter, `chapter_trace.tex`, where `φ_j|_{Ỹ}` is the
restriction of quasi-psh functions of `X` to the normalization `Ỹ` of `Y`).

`isThetaPSH_restrict_of_dense`: if `φ` is a `θ`-psh potential on the complex manifold `M` and the
finite locus of `φ ∘ p` is dense in `Ỹ` (`p : Ỹ → Y ⊆ M` the normalization), then
`φ|_Ỹ := φ ∘ p ∈ PSH(Ỹ, θ|_Ỹ)` in the sense of `def:unibranch:L105`.  The density hypothesis is the
book's `φ|_Y ≢ -∞` read on the unibranch space `Ỹ` (it is automatic for instance when `φ` is
finite on a dense subset of a resolution of `Ỹ`, `dense_of_resolution`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex

namespace SGPT.Unibranch.KSNormalizedSubvariety

open SourceReducedComplexSpace OriginalNativeModification

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)

/-- **Restriction to `Ỹ`.** A `θ`-psh potential `φ` on `M` whose restriction to `Ỹ` has a dense
finite locus restricts to a `θ|_Ỹ`-psh function on `Ỹ`. -/
theorem isThetaPSH_restrict_of_dense {θ : SmoothRealForm n M 2} {φ : M → EReal}
    (hφ : IsThetaPshPotential θ φ)
    (hd : Dense {y : (normalization C hC).obj.left |
      φ ((normalizationMap C hC).hom.left.base y).val ≠ ⊥}) :
    (normalization C hC).IsThetaPSH (restrictForm C hC θ)
      (fun y => φ ((normalizationMap C hC).hom.left.base y).val) := by
  intro y
  let p := normalizationMap C hC
  let x : M := (p.hom.left.base y).val
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxs
  obtain ⟨W, ρ, hzW, ⟨hWo, hWU, hρs, hρddc⟩, hpsh⟩ := hφ.1 e (e.val x) hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hWo (e.val x) hzW
  let B : Opens (ComplexModel n) := ⟨ball (e.val x) r, isOpen_ball⟩
  have hBW : (B : Set (ComplexModel n)) ⊆ W := hball
  let E₀ := LocalEmbedding.ofChart C hC x
  have hE₀pt : ∀ b : E₀.carrier, (E₀.toPoint b).val = e.val.symm b.val.val := fun _ => rfl
  have hyE₀ : p.hom.left.base y ∈ range E₀.toPoint :=
    mem_range_chartModelMap (n := n) C (p.hom.left.base y).property
  obtain ⟨A₀, ⟨c, hc⟩⟩ := SpaceForm.morphismChartLift_cover p E₀ y hyE₀
  -- the lift sends the base point to the chart centre
  have hliftc : A₀.lift c.val.val = e.val x := by
    obtain ⟨b, hb, hpb⟩ := A₀.factor c
    rw [← hb]
    have h1 : e.val.symm b.val.val = x := by
      have h2 := congrArg Subtype.val (hpb.trans (congrArg p.hom.left.base hc))
      exact h2
    have hbt : b.val.val ∈ e.val.target := b.val.property
    rw [← h1, e.val.right_inv hbt]
  -- shrink the source chart so that the lift lands in the ball `B`
  let W₀ : Set (ComplexModel A₀.source.dim) :=
    A₀.source.ambient ∩ A₀.lift ⁻¹' (B : Set (ComplexModel n))
  have hW₀ : IsOpen W₀ :=
    A₀.holomorphic.continuousOn.isOpen_inter_preimage A₀.source.ambient.isOpen B.isOpen
  have hcW₀ : c.val.val ∈ W₀ := ⟨c.val.property, by
    change A₀.lift c.val.val ∈ ball (e.val x) r
    rw [hliftc]
    exact mem_ball_self hr⟩
  obtain ⟨s, hs, hsball⟩ := Metric.isOpen_iff.mp hW₀ c.val.val hcW₀
  let T : Opens (ComplexModel A₀.source.dim) := ⟨ball c.val.val s, isOpen_ball⟩
  have hT : T ≤ A₀.source.ambient := fun w hw => (hsball hw).1
  have hTB : MapsTo A₀.lift (T : Set (ComplexModel A₀.source.dim)) (B : Set (ComplexModel n)) :=
    fun w hw => (hsball hw).2
  let A := A₀.source.restrict T hT
  have hApt : ∀ c' : A.carrier, A.toPoint c' =
      A₀.source.toPoint ⟨Opens.inclusion hT c'.val, c'.property⟩ := fun _ => rfl
  have hfacA : ∀ c' : A.carrier, ∃ b : E₀.carrier,
      b.val.val = A₀.lift c'.val.val ∧ E₀.toPoint b = p.hom.left.base (A.toPoint c') := by
    intro c'
    rw [hApt]
    exact A₀.factor ⟨Opens.inclusion hT c'.val, c'.property⟩
  have hvalue : ∀ c' : A.carrier,
      (p.hom.left.base (A.toPoint c')).val = e.val.symm (A₀.lift c'.val.val) := by
    intro c'
    obtain ⟨b, hb, hpb⟩ := hfacA c'
    rw [← hpb, hE₀pt, hb]
  have hholT : ContDiffOn ℂ ∞ A₀.lift (A.ambient : Set (ComplexModel A.dim)) :=
    A₀.holomorphic.mono hT
  have hmapsW : MapsTo A₀.lift (A.ambient : Set (ComplexModel A.dim)) W :=
    fun w hw => hBW (hTB hw)
  have hTconn : IsConnected (A.ambient : Set (ComplexModel A.dim)) :=
    (convex_ball _ _).isConnected (Metric.nonempty_ball.mpr hs)
  refine ⟨A, ⟨⟨⟨c.val.val, mem_ball_self hs⟩, c.property⟩, ?_⟩, hTconn,
    fun w => ρ (A₀.lift w), ?_, ?_, ?_⟩
  · rw [hApt]
    exact hc
  · exact hρs.comp (hholT.restrict_scalars ℝ) hmapsW
  · -- `θ|_Ỹ = ddᶜ (ρ ∘ lift)` on `A`
    have h1 := SpaceForm.pullback_restrictsTo_of_lift (SpaceForm.ofClosedAnalytic C hC θ) p
      (SpaceForm.ofClosedAnalytic_restrictsTo C hC θ x) A hholT
      (fun w hw => hWU (hmapsW hw)) hfacA
    refine SpaceForm.restrictsTo_congr h1 ?_
    intro w hw
    rw [HolomorphicDDC.smoothDDC_comp A.ambient.isOpen hWo hholT hρs hmapsW hw,
      hρddc (hmapsW hw)]
    rfl
  · -- plurisubharmonicity on the local model
    let f : (A.carrier → EReal) := fun c' =>
      (ρ (A₀.lift c'.val.val) : EReal) + φ (p.hom.left.base (A.toPoint c')).val
    change (sourceReducedComplexSpaceModel A.ambient A.carrier A.analytic).IsPSH f
    -- density of the finite locus on the local model
    have hdA : Dense {c' : A.carrier | f c' ≠ ⊥} := by
      have h := hd.preimage A.isOpenEmbedding_toPoint.isOpenMap
      refine Dense.mono ?_ h
      intro c' hc'
      exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hc'⟩
    -- the ambient psh function on the ball
    let ψ : ComplexModel n → EReal := fun w => (ρ w : EReal) + φ (e.val.symm w)
    have hψ : SGPT.PSH.PSHOn ψ B := by
      refine ⟨?_, ?_⟩
      · have hB' : SGPT.Foundations.Analysis.PlurisubharmonicOn
            (fun w => chartFunction φ e w + (ρ w : EReal)) B := fun w hw => hpsh w (hBW hw)
        refine hB'.discPshOn.congr ?_
        intro w _
        change φ (e.val.symm w) + (ρ w : EReal) = (ρ w : EReal) + φ (e.val.symm w)
        exact add_comm _ _
      · have hO : IsOpen (e.val.source ∩ e.val ⁻¹' (B : Set (ComplexModel n))) :=
          e.val.isOpen_inter_preimage B.isOpen
        obtain ⟨y', hyO, hy'⟩ := hφ.2 x _ hO ⟨hxs, mem_ball_self hr⟩
        refine ⟨e.val y', hyO.2, ?_⟩
        change (ρ (e.val y') : EReal) + φ (e.val.symm (e.val y')) ≠ ⊥
        rw [e.val.left_inv hyO.1]
        intro hbot
        exact hy' ((EReal.add_eq_bot_iff.mp hbot).resolve_left (EReal.coe_ne_bot _))
    let Φ : (domainSpace B).obj.left → EReal := fun w => ψ w.val.val
    have hΦ : ∀ w, (domainSpace B).IsLocallyAmbientPSHAt Φ w := by
      intro w
      exact ⟨domainChart B, ⟨w, rfl⟩, (convex_ball _ _).isConnected (Metric.nonempty_ball.mpr hr),
        ψ, hψ, fun _ => rfl⟩
    let F := analyticModelMorphism (V := B) (D := univ) A.analytic isComplexAnalyticSubset_univ
      A₀.lift hholT (fun w hw => hTB hw) (fun _ => trivial)
    have hfF : (fun z => Φ (F.hom.left.base z)) = f := by
      funext c'
      change (ρ (A₀.lift c'.val.val) : EReal) + φ (e.val.symm (A₀.lift c'.val.val)) = f c'
      change _ = (ρ (A₀.lift c'.val.val) : EReal) + φ (p.hom.left.base (A.toPoint c')).val
      rw [hvalue]
    have hfF' : ∀ z, Φ (F.hom.left.base z) = f z := fun z => congrFun hfF z
    have hdF : Dense {z | Φ (F.hom.left.base z) ≠ ⊥} := by
      refine Dense.mono ?_ hdA
      intro z hz
      change Φ (F.hom.left.base z) ≠ ⊥
      rw [hfF' z]
      exact hz
    have hloc := locallyAmbientPSH_pullback_of_dense_finite hΦ F hdF
    rw [← hfF]
    exact ⟨componentNondegenerate_model_of_dense_finite hdF, hloc⟩

/-- Density on `Ỹ` from density on a resolution: if `π : V → Ỹ` is surjective and continuous and
`φ ∘ p ∘ π` has a dense finite locus, then `φ ∘ p` has a dense finite locus. -/
theorem dense_of_resolution {Z : SourceReducedComplexSpace} (π : Z ⟶ normalization C hC)
    (hπ : Function.Surjective π.hom.left.base) {φ : M → EReal}
    (hd : Dense {z : Z.obj.left |
      φ ((normalizationMap C hC).hom.left.base (π.hom.left.base z)).val ≠ ⊥}) :
    Dense {y : (normalization C hC).obj.left |
      φ ((normalizationMap C hC).hom.left.base y).val ≠ ⊥} := by
  have h := hπ.denseRange.dense_image π.hom.left.base.hom.continuous hd
  refine Dense.mono ?_ h
  rintro _ ⟨z, hz, rfl⟩
  exact hz

end SGPT.Unibranch.KSNormalizedSubvariety
