import SGPT.Unibranch.ComplexSpaceFornaessNarasimhan
import SGPT.Unibranch.Resolution
import SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure
import SGPT.Foundations.Analysis.FirstPass.AnalyticSubsetTopology
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens

/-!
# The Fornæss--Narasimhan criterion on complex manifolds

Source `thm:FN` (Appendix B, `appendix_unibranch.tex`), implication (2) ⇒ (1) on complex spaces
which are locally domains, in particular on every complex manifold `M`, viewed as the complex
space `(M, 𝒪_M)` (`SourceReducedComplexSpace.ofClosedAnalytic univ`, the whole model of `M`).

A complex space `X` *has domain charts* (`HasDomainCharts`) if every point has, inside any open
neighbourhood, an open immersion of a connected domain `U ⊆ ℂ^d` (with its full sheaf of
holomorphic functions). For such `X` we prove:

* `pshOn_domainPullback`: if `φ` is usc and satisfies the disc criterion of `thm:FN`(2), then in
  every domain chart `F : U → X` the pull-back `φ ∘ F` is in `PSH(U)` as soon as it is not
  identically `-∞` (the holomorphic discs of `U` are composed with `F`);
* `isClosed_setOf_eventually_eq_bot`: the set where `φ` is locally identically `-∞` is open and
  closed (sub-mean value property on connected chart domains);
* `isAnalyticSubset_inter_of_isClopen`, `isClosed_interior_of_isAnalyticSubset`: clopen subsets
  are analytic, and analytic subsets have closed interior (identity theorem in domain charts);
* `isIrreducibleComponent_connectedComponent`: the connected components of `X` are irreducible
  components of `X`;
* `isPSH_of_disc_of_hasDomainCharts`, `fornaessNarasimhan_of_hasDomainCharts`: **`thm:FN` on `X`**;
* `hasDomainCharts_ofClosedAnalytic_univ`, `fornaessNarasimhan_manifold`: **`thm:FN` on every
  complex manifold**.

-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
open SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex

namespace SGPT.Unibranch

noncomputable section

namespace SourceReducedComplexSpace

variable {X : SourceReducedComplexSpace}

/-! ### Pull-backs along domain charts -/

section DomainCharts

variable {d : ℕ} {U : Opens (ComplexModel d)}

/-- The morphism of complex spaces `U → X` induced by a morphism, over the complex point, from
the domain model `(U, 𝒪_U)` to `X`. -/
def domainMorphism (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (hF : F ≫ X.obj.hom = (modelOver U (univ : Set U)).hom) : domainSpace U ⟶ X :=
  ObjectProperty.homMk (Over.homMk F hF)

open Classical in
/-- The pull-back of `φ` along a domain chart `F : U → X`, as a function on `ℂ^d`
(`-∞` outside `U`). -/
def domainPullback (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (φ : X.obj.left → EReal) : ComplexModel d → EReal := fun z =>
  if h : z ∈ U then φ (F.base (⟨⟨z, h⟩, trivial⟩ : (univ : Set U))) else ⊥

theorem domainPullback_apply (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (φ : X.obj.left → EReal) (p : (univ : Set U)) :
    domainPullback F φ p.val.val = φ (F.base p) := by
  simp only [domainPullback, dif_pos p.val.property]

theorem discPullback_comp_domainMorphism (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (hF : F ≫ X.obj.hom = (modelOver U (univ : Set U)).hom) (f : unitDisc ⟶ domainSpace U)
    (φ : X.obj.left → EReal) :
    discPullback (f ≫ domainMorphism F hF) φ =
      discPullback f (fun p : (univ : Set U) => domainPullback F φ p.val.val) := by
  funext t
  simp only [discPullback, modelPullback, domainPullback_apply]
  split_ifs
  · rfl
  · rfl

/-- **Source `thm:FN`, (2) ⇒ (1), in a domain chart.** If `φ` is upper semicontinuous on `X` and
its pull-back by every holomorphic disc `f : Δ → X` with `f^*φ ≢ -∞` is subharmonic, then the
pull-back of `φ` along any domain chart `F : U → X` (`U` connected) is plurisubharmonic on `U`
as soon as it is not identically `-∞`. -/
theorem pshOn_domainPullback (hU : IsConnected (U : Set (ComplexModel d)))
    (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (hF : F ≫ X.obj.hom = (modelOver U (univ : Set U)).hom) {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤) (husc : UpperSemicontinuous φ)
    (hdisc : ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
      SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1))
    (hne : ∃ p : (univ : Set U), φ (F.base p) ≠ ⊥) :
    SGPT.PSH.PSHOn (domainPullback F φ) U := by
  have hfun : (fun p : (univ : Set U) => domainPullback F φ p.val.val) =
      fun p => φ (F.base p) := funext fun p => domainPullback_apply F φ p
  rw [← isPSH_model_univ_iff hU]
  refine isPSH_domain_of_disc hU _ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [domainPullback, dif_pos hz]
    exact hne_top _
  · intro Z hZ
    rw [isIrreducibleComponent_model_univ_iff hU] at hZ
    subst hZ
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, trivial, by rw [hfun]; exact hp⟩
  · rw [hfun]
    intro p y hy
    exact (F.base.hom.continuous.continuousAt (x := p)).tendsto.eventually (husc _ y hy)
  · intro f hf
    rw [← discPullback_comp_domainMorphism F hF] at hf ⊢
    exact hdisc _ hf

end DomainCharts

/-! ### Complex spaces which are locally domains -/

/-- A complex space *has domain charts* if every point has, inside every open neighbourhood, an
open immersion over the complex point of a connected domain `U ⊆ ℂ^d` with its full sheaf of
holomorphic functions (the reduced model `(U, U)`). Complex manifolds have domain charts
(`hasDomainCharts_ofClosedAnalytic_univ`). -/
def HasDomainCharts (X : SourceReducedComplexSpace) : Prop :=
  ∀ (x : X.obj.left) (N : Set X.obj.left), IsOpen N → x ∈ N →
    ∃ (d : ℕ) (U : Opens (ComplexModel d)) (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left),
      LocallyRingedSpace.IsOpenImmersion F ∧ F ≫ X.obj.hom = (modelOver U (univ : Set U)).hom ∧
        IsConnected (U : Set (ComplexModel d)) ∧ x ∈ range F.base ∧ range F.base ⊆ N

/-- The local embedding of `X` given by a domain chart. -/
def domainEmbedding {d : ℕ} (U : Opens (ComplexModel d))
    (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (hFo : LocallyRingedSpace.IsOpenImmersion F)
    (hF : F ≫ X.obj.hom = (modelOver U (univ : Set U)).hom) : LocalEmbedding X where
  dim := d
  ambient := U
  carrier := univ
  analytic := isComplexAnalyticSubset_univ
  map := F
  isOpenImmersion := hFo
  overPoint := hF

theorem isOpen_range_domainChart {d : ℕ} {U : Opens (ComplexModel d)}
    {F : (modelOver U (univ : Set U)).left ⟶ X.obj.left}
    (hFo : LocallyRingedSpace.IsOpenImmersion F) : IsOpen (range F.base) :=
  hFo.base_open.isOpen_range

theorem isConnected_range_domainChart {d : ℕ} {U : Opens (ComplexModel d)}
    (hU : IsConnected (U : Set (ComplexModel d)))
    (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left) : IsConnected (range F.base) := by
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp hU
  have h : ConnectedSpace (univ : Set U) := isConnected_iff_connectedSpace.mp
    (isConnected_univ (α := U))
  exact @isConnected_range _ _ _ _ h _ F.base.hom.continuous


/-- The inclusion of the points of a domain model `(U, U)` into `ℂ^d` is an open embedding. -/
theorem isOpenEmbedding_domainPoint {d : ℕ} (U : Opens (ComplexModel d)) :
    Topology.IsOpenEmbedding (fun p : (univ : Set U) => (p.val.val : ComplexModel d)) :=
  U.isOpen.isOpenEmbedding_subtypeVal.comp isOpen_univ.isOpenEmbedding_subtypeVal

/-- **Propagation of poles in a domain chart.** If `φ` satisfies the hypotheses of `thm:FN`(2)
and is identically `-∞` near one point of a connected domain chart, then it is identically `-∞`
on the whole chart. -/
theorem eq_bot_of_eventually_eq_bot {d : ℕ} {U : Opens (ComplexModel d)}
    (hU : IsConnected (U : Set (ComplexModel d)))
    (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (hF : F ≫ X.obj.hom = (modelOver U (univ : Set U)).hom) {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤) (husc : UpperSemicontinuous φ)
    (hdisc : ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
      SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1))
    {p : (univ : Set U)} (hp : ∀ᶠ y in 𝓝 (F.base p), φ y = ⊥) (q : (univ : Set U)) :
    φ (F.base q) = ⊥ := by
  by_contra hq
  have hpsh := pshOn_domainPullback hU F hF hne_top husc hdisc ⟨q, hq⟩
  set P : Set (univ : Set U) := {r | φ (F.base r) = ⊥} with hPdef
  have hP : P ∈ 𝓝 p := (F.base.hom.continuous.continuousAt (x := p)).preimage_mem_nhds hp
  set ι : ↥(univ : Set U) → ComplexModel d := fun r => r.val.val
  have hι : Topology.IsOpenEmbedding ι := isOpenEmbedding_domainPoint U
  set W : Set (ComplexModel d) := ι '' interior P
  have hWo : IsOpen W := hι.isOpenMap _ isOpen_interior
  have hWne : W.Nonempty := ⟨ι p, p, mem_interior_iff_mem_nhds.mpr hP, rfl⟩
  have hWU : W ⊆ U := by
    rintro _ ⟨r, -, rfl⟩
    exact r.val.property
  have hpl : SGPT.Foundations.Analysis.PlurisubharmonicOn (domainPullback F φ) U :=
    fun z hz => ⟨U, U.isOpen, hz, hpsh.disc⟩
  obtain ⟨b, ⟨r, hr, rfl⟩, hb⟩ :=
    SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure.exists_ne_bot_of_isOpen_subset hpl
      hU.isPreconnected hpsh.nontrivial hWo hWne hWU
  apply hb
  rw [domainPullback_apply]
  exact (interior_subset hr : r ∈ P)

/-- **The pole-propagation set is closed.** On a complex space with domain charts, the set of
points near which `φ` is identically `-∞` is closed, for `φ` as in `thm:FN`(2). -/
theorem isClosed_setOf_eventually_eq_bot (hX : X.HasDomainCharts) {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤) (husc : UpperSemicontinuous φ)
    (hdisc : ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
      SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) :
    IsClosed {x : X.obj.left | ∀ᶠ y in 𝓝 x, φ y = ⊥} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨d, U, F, hFo, hF, hU, hxF, -⟩ := hX x univ isOpen_univ trivial
  have hR := isOpen_range_domainChart hFo
  obtain ⟨y, ⟨p, rfl⟩, hy⟩ := (mem_closure_iff.mp hx _ hR hxF)
  have hall : ∀ q, φ (F.base q) = ⊥ :=
    eq_bot_of_eventually_eq_bot hU F hF hne_top husc hdisc hy
  refine Filter.mem_of_superset (hR.mem_nhds hxF) ?_
  rintro _ ⟨q, rfl⟩
  exact hall q

/-! ### Analytic subsets in domain charts -/

/-- The trace of an analytic subset of `X` on a domain chart `F : U → X` is an analytic subset of
`U`. -/
theorem isComplexAnalyticSubset_domainTrace {d : ℕ} {U : Opens (ComplexModel d)}
    (F : (modelOver U (univ : Set U)).left ⟶ X.obj.left)
    (hF : F ≫ X.obj.hom = (modelOver U (univ : Set U)).hom) {A : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) :
    IsComplexAnalyticSubset (n := d) {u : U | F.base (⟨u, trivial⟩ : (univ : Set U)) ∈ A} := by
  apply SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens.isComplexAnalyticSubset_of_forall_opens
  intro u
  obtain ⟨e₂, hc, A', hA', hpre⟩ := hA (F.base (⟨u, trivial⟩ : (univ : Set U)))
  obtain ⟨O, huO, f, hf, hfac⟩ := LocalEmbedding.exists_contMDiff_factor F hF e₂ ⟨u, trivial⟩ hc
  refine ⟨O, huO, ?_⟩
  have heq : ((↑) ⁻¹' {u : U | F.base (⟨u, trivial⟩ : (univ : Set U)) ∈ A} : Set O) =
      f ⁻¹' A' := by
    ext o
    obtain ⟨z, hz, hzF⟩ := hfac ⟨o.val, trivial⟩ o.property
    change F.base (⟨o.val, trivial⟩ : (univ : Set U)) ∈ A ↔ f o ∈ A'
    rw [← hzF]
    change z ∈ e₂.toPoint ⁻¹' A ↔ _
    rw [hpre]
    change z.val ∈ A' ↔ _
    rw [hz]
  rw [heq]
  exact SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf
    hA'

/-- On a complex space with domain charts, the intersection of an analytic subset with a clopen
subset is analytic. -/
theorem isAnalyticSubset_inter_of_isClopen (hX : X.HasDomainCharts) {A W : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) (hW : IsClopen W) : X.IsAnalyticSubset (A ∩ W) := by
  intro x
  by_cases hxW : x ∈ W
  · obtain ⟨d, U, F, hFo, hF, hU, hxF, hFW⟩ := hX x W hW.isOpen hxW
    refine ⟨domainEmbedding U F hFo hF, hxF, _, isComplexAnalyticSubset_domainTrace F hF hA, ?_⟩
    ext p
    have hpW : F.base p ∈ W := hFW ⟨p, rfl⟩
    change F.base p ∈ A ∩ W ↔ F.base (⟨p.val, trivial⟩ : (univ : Set U)) ∈ A
    exact ⟨fun h => h.1, fun h => ⟨h, hpW⟩⟩
  · obtain ⟨d, U, F, hFo, hF, hU, hxF, hFW⟩ := hX x Wᶜ hW.isClosed.isOpen_compl hxW
    refine ⟨domainEmbedding U F hFo hF, hxF, ∅, isComplexAnalyticSubset_empty, ?_⟩
    ext p
    have hpW : F.base p ∉ W := hFW ⟨p, rfl⟩
    change F.base p ∈ A ∩ W ↔ False
    exact ⟨fun h => hpW h.2, False.elim⟩

/-- On a complex space with domain charts, clopen subsets are analytic. -/
theorem isAnalyticSubset_of_isClopen (hX : X.HasDomainCharts) {W : Set X.obj.left}
    (hW : IsClopen W) : X.IsAnalyticSubset W := by
  simpa using isAnalyticSubset_inter_of_isClopen hX isAnalyticSubset_univ hW

/-- **Identity theorem.** On a complex space with domain charts, the interior of an analytic
subset is closed. -/
theorem isClosed_interior_of_isAnalyticSubset (hX : X.HasDomainCharts) {A : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) : IsClosed (interior A) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨d, U, F, hFo, hF, hU, hxF, -⟩ := hX x univ isOpen_univ trivial
  have : ConnectedSpace U := isConnected_iff_connectedSpace.mp hU
  have hR := isOpen_range_domainChart hFo
  set AU : Set U := {u : U | F.base (⟨u, trivial⟩ : (univ : Set U)) ∈ A}
  have hAU : IsComplexAnalyticSubset (n := d) AU := isComplexAnalyticSubset_domainTrace F hF hA
  obtain ⟨y, ⟨p, rfl⟩, hyA⟩ := mem_closure_iff.mp hx _ hR hxF
  -- the points of `U` mapped into the interior of `A`
  set V : Set U := {u : U | F.base (⟨u, trivial⟩ : (univ : Set U)) ∈ interior A}
  have hVo : IsOpen V := isOpen_interior.preimage
    (F.base.hom.continuous.comp (continuous_id.subtype_mk fun _ => trivial))
  have hVA : V ⊆ AU := fun u (hu : F.base (⟨u, trivial⟩ : (univ : Set U)) ∈ interior A) =>
    (interior_subset hu : F.base (⟨u, trivial⟩ : (univ : Set U)) ∈ A)
  have hint : (interior AU).Nonempty :=
    ⟨p.val, interior_maximal hVA hVo (by simpa [V] using hyA)⟩
  have huniv := hAU.eq_univ_of_interior_nonempty hint
  have hRA : range F.base ⊆ A := by
    rintro _ ⟨q, rfl⟩
    have : q.val ∈ AU := by rw [huniv]; trivial
    exact this
  exact interior_maximal hRA hR hxF


/-! ### Connected components are irreducible components -/

/-- On a complex space with domain charts, connected components are open. -/
theorem isOpen_connectedComponent_of_hasDomainCharts (hX : X.HasDomainCharts) (x : X.obj.left) :
    IsOpen (connectedComponent x) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨d, U, F, hFo, hF, hU, hyF, -⟩ := hX y univ isOpen_univ trivial
  refine ⟨range F.base, ?_, isOpen_range_domainChart hFo, hyF⟩
  rw [connectedComponent_eq hy]
  exact (isConnected_range_domainChart hU F).isPreconnected.subset_connectedComponent hyF

/-- On a complex space with domain charts (e.g. a complex manifold), every connected component is
an irreducible component. -/
theorem isIrreducibleComponent_connectedComponent (hX : X.HasDomainCharts) (x : X.obj.left) :
    X.IsIrreducibleComponent (connectedComponent x) := by
  have hK : IsClopen (connectedComponent x) :=
    ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_hasDomainCharts hX x⟩
  have hirr : X.IsIrreducibleAnalyticSubset (connectedComponent x) := by
    refine ⟨isAnalyticSubset_of_isClopen hX hK, ⟨x, mem_connectedComponent⟩, ?_⟩
    intro B C hB hC hBK hCK hBC
    by_cases h : connectedComponent x ⊆ B
    · exact Or.inl (Subset.antisymm h hBK)
    · right
      obtain ⟨p, hpK, hpB⟩ := not_subset.mp h
      have hpint : p ∈ interior C := by
        refine mem_interior.mpr ⟨connectedComponent x ∩ Bᶜ, fun z hz => ?_,
          hK.isOpen.inter hB.isClosed.isOpen_compl, hpK, hpB⟩
        have : z ∈ B ∪ C := hBC ▸ hz.1
        exact this.resolve_left hz.2
      have hint : IsClopen (interior C) :=
        ⟨isClosed_interior_of_isAnalyticSubset hX hC, isOpen_interior⟩
      have hsub := hint.connectedComponent_subset hpint
      rw [← connectedComponent_eq hpK] at hsub
      exact Subset.antisymm (hsub.trans interior_subset) hCK
  refine ⟨hirr, fun D hD hKD => ?_⟩
  have hD1 := isAnalyticSubset_inter_of_isClopen hX hD.1 hK
  have hD2 := isAnalyticSubset_inter_of_isClopen hX hD.1 hK.compl
  have hunion : D = D ∩ connectedComponent x ∪ D ∩ (connectedComponent x)ᶜ := by
    rw [← inter_union_distrib_left, union_compl_self, inter_univ]
  rcases hD.2.2 _ _ hD1 hD2 inter_subset_left inter_subset_left hunion with h | h
  · have hDK : D ⊆ connectedComponent x := by
      rw [h]
      exact inter_subset_right
    exact Subset.antisymm hDK hKD
  · exfalso
    have hx : x ∈ D := hKD mem_connectedComponent
    rw [h] at hx
    exact hx.2 mem_connectedComponent

/-! ### The Fornæss--Narasimhan theorem on complex spaces with domain charts -/

/-- **Source `thm:FN`, (2) ⇒ (1), on complex spaces with domain charts.** Let
`φ : X → [-∞, ∞)` be not identically `-∞` on any irreducible component of `X`. If `φ` is upper
semicontinuous and for every holomorphic disc `f : Δ → X` with `f^*φ ≢ -∞` the pull-back `f^*φ` is
subharmonic, then `φ` is plurisubharmonic. -/
theorem isPSH_of_disc_of_hasDomainCharts (hX : X.HasDomainCharts) {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤)
    (hcomp : ∀ Z : Set X.obj.left, X.IsIrreducibleComponent Z → ∃ z ∈ Z, φ z ≠ ⊥)
    (husc : UpperSemicontinuous φ)
    (hdisc : ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
      SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) :
    X.IsPSH φ := by
  set S : Set X.obj.left := {x | ∀ᶠ y in 𝓝 x, φ y = ⊥}
  have hSc : IsClopen S :=
    ⟨isClosed_setOf_eventually_eq_bot hX hne_top husc hdisc, isOpen_setOfPred_eventually_nhds⟩
  have hS : ∀ x, x ∉ S := by
    intro x hx
    obtain ⟨z, hzK, hz⟩ := hcomp _ (isIrreducibleComponent_connectedComponent hX x)
    exact hz (hSc.connectedComponent_subset hx hzK).self_of_nhds
  refine ⟨hcomp, fun x => ?_⟩
  obtain ⟨d, U, F, hFo, hF, hU, hxF, -⟩ := hX x univ isOpen_univ trivial
  have hne : ∃ p : (univ : Set U), φ (F.base p) ≠ ⊥ := by
    by_contra h
    push Not at h
    apply hS x
    refine Filter.mem_of_superset ((isOpen_range_domainChart hFo).mem_nhds hxF) ?_
    rintro _ ⟨q, rfl⟩
    exact h q
  exact ⟨domainEmbedding U F hFo hF, hxF, hU, domainPullback F φ,
    pshOn_domainPullback hU F hF hne_top husc hdisc hne,
    fun c => (domainPullback_apply F φ c).symm⟩

/-- **Source `thm:FN` on complex spaces with domain charts**: for `φ : X → [-∞, ∞)` not
identically `-∞` on any irreducible component, `φ` is plurisubharmonic iff it is upper
semicontinuous and its pull-back by every holomorphic disc `f : Δ → X` with `f^*φ ≢ -∞` is
subharmonic. -/
theorem fornaessNarasimhan_of_hasDomainCharts (hX : X.HasDomainCharts) {φ : X.obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤)
    (hcomp : ∀ Z : Set X.obj.left, X.IsIrreducibleComponent Z → ∃ z ∈ Z, φ z ≠ ⊥) :
    X.IsPSH φ ↔
      (UpperSemicontinuous φ ∧
        ∀ f : unitDisc ⟶ X, (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
          SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) :=
  ⟨fun h => h.fornaessNarasimhan_forward,
    fun h => isPSH_of_disc_of_hasDomainCharts hX hne_top hcomp h.1 h.2⟩

/-! ### Complex manifolds -/

section Manifold

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A complex manifold `M`, as the complex space `(M, 𝒪_M)`, has domain charts: restrictions of
its holomorphic charts to small balls. -/
theorem hasDomainCharts_ofClosedAnalytic_univ :
    (ofClosedAnalytic (univ : Set M) (isComplexAnalyticSubset_univ (n := n))).HasDomainCharts := by
  intro x N hN hxN
  set e₀ := LocalEmbedding.ofChart (univ : Set M) (isComplexAnalyticSubset_univ (n := n)) x.val
  obtain ⟨c, hc⟩ : x ∈ range e₀.toPoint :=
    mem_range_chartModelMap (n := n) (univ : Set M) x.property
  have hS : IsOpen (e₀.toPoint ⁻¹' N) := hN.preimage e₀.isOpenEmbedding_toPoint.continuous
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hS
  have hct : c.val ∈ t := by
    have : c ∈ e₀.toPoint ⁻¹' N := by
      change e₀.toPoint c ∈ N
      rw [hc]
      exact hxN
    rw [← hts] at this
    exact this
  have hopen : IsOpen ((Subtype.val : e₀.ambient → ComplexModel e₀.dim) '' t) :=
    e₀.ambient.isOpen.isOpenMap_subtype_val t ht
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen c.val.val ⟨c.val, hct, rfl⟩
  let T : Opens (ComplexModel e₀.dim) := ⟨Metric.ball c.val.val r, Metric.isOpen_ball⟩
  have hT : T ≤ e₀.ambient := by
    intro z hz
    obtain ⟨u, -, rfl⟩ := hball hz
    exact u.property
  have hC' : ∀ z, z ∈ (univ : Set T) ↔ Opens.inclusion hT z ∈ e₀.carrier :=
    fun _ => iff_of_true trivial trivial
  refine ⟨e₀.dim, T, (e₀.restrictWith T hT univ hC').map,
    (e₀.restrictWith T hT univ hC').isOpenImmersion, (e₀.restrictWith T hT univ hC').overPoint,
    (convex_ball _ _).isConnected (Metric.nonempty_ball.mpr hr), ?_, ?_⟩
  · refine ⟨⟨⟨c.val.val, Metric.mem_ball_self hr⟩, trivial⟩, ?_⟩
    change (e₀.restrictWith T hT univ hC').toPoint _ = x
    rw [LocalEmbedding.restrictWith_toPoint]
    exact hc
  · rintro _ ⟨z, rfl⟩
    change (e₀.restrictWith T hT univ hC').toPoint z ∈ N
    rw [LocalEmbedding.restrictWith_toPoint]
    have hz : Opens.inclusion hT z.val ∈ t := by
      obtain ⟨u, hu, hu'⟩ := hball z.val.property
      have : u = Opens.inclusion hT z.val := Subtype.ext hu'
      rw [← this]
      exact hu
    have : (⟨Opens.inclusion hT z.val, (hC' z.val).mp z.property⟩ : e₀.carrier) ∈
        e₀.toPoint ⁻¹' N := by
      rw [← hts]
      exact hz
    exact this

/-- **Source `thm:FN` on complex manifolds.** Let `M` be a complex manifold, viewed as the complex
space `(M, 𝒪_M)`, and `φ : M → [-∞, ∞)` a function which is not identically `-∞` on any
irreducible component of `M`. Then `φ` is plurisubharmonic iff it is upper semicontinuous and for
every holomorphic disc `f : Δ → M` with `f^*φ ≢ -∞` the pull-back `f^*φ` is subharmonic. -/
theorem fornaessNarasimhan_manifold
    {φ : (ofClosedAnalytic (univ : Set M) (isComplexAnalyticSubset_univ (n := n))).obj.left → EReal}
    (hne_top : ∀ x, φ x ≠ ⊤)
    (hcomp : ∀ Z, (ofClosedAnalytic (univ : Set M)
      (isComplexAnalyticSubset_univ (n := n))).IsIrreducibleComponent Z → ∃ z ∈ Z, φ z ≠ ⊥) :
    (ofClosedAnalytic (univ : Set M) (isComplexAnalyticSubset_univ (n := n))).IsPSH φ ↔
      (UpperSemicontinuous φ ∧
        ∀ f : unitDisc ⟶ ofClosedAnalytic (univ : Set M) (isComplexAnalyticSubset_univ (n := n)),
          (∃ t ∈ ball (0 : ℂ) 1, discPullback f φ t ≠ ⊥) →
            SGPT.PSH.SubharmonicOn (discPullback f φ) (ball (0 : ℂ) 1)) :=
  fornaessNarasimhan_of_hasDomainCharts hasDomainCharts_ofClosedAnalytic_univ hne_top hcomp

end Manifold

end SourceReducedComplexSpace

end

end SGPT.Unibranch
