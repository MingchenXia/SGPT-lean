import SGPT.Unibranch.PD3CoverBound
import SGPT.Unibranch.PD3GRexten2
import SGPT.Unibranch.FNPChart
import SGPT.Unibranch.ComplexSpaceUnibranchComplement
import SGPT.Foundations.Analysis.Pending.FiniteMapDimension
import SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex
import SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceSingular
import SGPT.Foundations.Analysis.Pending.GermComponentDimension

/-!
# The Grauert--Remmert extension theorem on unibranch complex spaces

Source `thm:GRexten2` (Appendix B, `appendix_unibranch.tex`), both items. Let `X` be a unibranch
complex space, `Z ⊆ X` an analytic subset and `φ ∈ PSH(X \ Z)`. Then `φ` has a psh extension to
`X` if (1) `Z` has codimension at least `2` everywhere, or (2) `Z` has codimension at least `1`
everywhere and `φ` is locally bounded from above near `Z`; in both cases it is unique and given by
`eq:GRextvarphi`.

*Codimension.* In a local embedding `(Ω, C) ⊆ ℂ^N` of `X` the dimension of `Z` (resp. `X`) near a
point is the largest dimension of its regular points nearby. `HasCodimAtLeastTwo X Z` says: near
every point of `Z` there is a local embedding in which every regular point `w` of the trace of `Z`,
of dimension `k`, has regular points of `C` of dimension `≥ k + 2` arbitrarily close
(`dim_w Z ≤ dim_w X - 2` at the regular points of `Z`, which is equivalent to the same inequality
at all points of `Z`, since `dim Z` is attained at regular points and `dim X` is upper
semicontinuous). Codimension `≥ 1` everywhere is `interior Z = ∅`; codimension `≥ 2` implies it
(`HasCodimAtLeastTwo.interior_eq_empty`).

*Proof of item (1)* (book: local description of complex spaces as branched coverings; it suffices
to show that `φ` is locally bounded above near `Z`, then item (2) applies):

* a unibranch space is locally pure dimensional (`exists_isPureDim_of_isUnibranch`: the regular
  part of a small neighbourhood is connected, by the unibranch connectedness of complements);
* by the local parametrization theorem (lane FNP, `FNP.localCoveringCharts`) a neighbourhood of a
  point of `Z` is a finite branched covering of a domain of `ℂ^d` after a linear change of
  coordinates; the trace of `Z` has dimension `≤ d - 2` there;
* `exists_bound_of_isBranchedCovering` (lane PD3, via `[FN80]` Lemma 5.1 and the codimension-two
  bound on manifolds) gives the local upper bound (`exists_bound_of_hasCodimAtLeastTwo`).

Main results: `grauertRemmert_extension_codimTwo` (item (1)) and `grauertRemmert_extension`
(both items, with uniqueness and `eq:GRextvarphi`).

Lane PD3, blueprint `pd3.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

noncomputable section

namespace SGPT.Unibranch.PD3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Unibranch.FNL SGPT.Unibranch.FNR SourceReducedComplexSpace
open SGPT.PSH.VariableComplexAtlas (analyticExtension)

/-! ### Traces in local embeddings and codimension -/

/-- The trace in the ambient space `ℂ^N` of a set `A ⊆ X` under a local embedding. -/
def ambientTrace {X : SourceReducedComplexSpace} (e : LocalEmbedding X) (A : Set X.obj.left) :
    Set (ComplexModel e.dim) :=
  {w | ∃ a : e.carrier, a.val.val = w ∧ e.toPoint a ∈ A}

theorem ambientTrace_univ {X : SourceReducedComplexSpace} (e : LocalEmbedding X) :
    ambientTrace e univ = Subtype.val '' e.carrier := by
  ext w
  constructor
  · rintro ⟨a, rfl, -⟩
    exact ⟨a.val, a.property, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl, trivial⟩

theorem ambientTrace_eq {X : SourceReducedComplexSpace} (e : LocalEmbedding X)
    (A : Set X.obj.left) :
    ambientTrace e A = Subtype.val '' (Subtype.val '' (e.toPoint ⁻¹' A)) := by
  ext w
  constructor
  · rintro ⟨a, rfl, ha⟩
    exact ⟨a.val, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, rfl, ha⟩

/-- **Codimension at least two everywhere** (`thm:GRexten2` (1)) for an analytic subset `Z` of a
(possibly singular) complex space `X`: near every point of `Z` there is a local embedding
`(Ω, C) ⊆ ℂ^N` in which every regular point `w` of the trace of `Z`, of dimension `k`, satisfies
`dim_w C ≥ k + 2` (`LocDimGE`: regular points of `C` of dimension `≥ k + 2` arbitrarily close to
`w`). On a complex manifold this is `VariableComplexAtlas.HasChartCodimAtLeastTwo`. -/
def HasCodimAtLeastTwo (X : SourceReducedComplexSpace) (Z : Set X.obj.left) : Prop :=
  ∀ z ∈ Z, ∃ e : LocalEmbedding X, z ∈ range e.toPoint ∧
    ∀ (w : ComplexModel e.dim) (k : ℕ),
      RegularAtDim (n := e.dim) (M := ComplexModel e.dim) (ambientTrace e Z) w k →
        AnalyticDimensionBasics.LocDimGE (n := e.dim) (M := ComplexModel e.dim)
          (ambientTrace e univ) w (k + 2)

/-- The condition of `HasCodimAtLeastTwo` in every local embedding (the chart-free form) implies
`HasCodimAtLeastTwo`. -/
theorem HasCodimAtLeastTwo.of_forall {X : SourceReducedComplexSpace} {Z : Set X.obj.left}
    (h : ∀ e : LocalEmbedding X, ∀ (w : ComplexModel e.dim) (k : ℕ),
      RegularAtDim (n := e.dim) (M := ComplexModel e.dim) (ambientTrace e Z) w k →
        AnalyticDimensionBasics.LocDimGE (n := e.dim) (M := ComplexModel e.dim)
          (ambientTrace e univ) w (k + 2)) :
    HasCodimAtLeastTwo X Z :=
  fun z _ => ⟨LocalEmbedding.ofPoint X z, LocalEmbedding.mem_range_ofPoint X z, h _⟩

/-- Codimension `≥ 2` everywhere implies codimension `≥ 1` everywhere: empty interior. -/
theorem HasCodimAtLeastTwo.interior_eq_empty {X : SourceReducedComplexSpace}
    {Z : Set X.obj.left} (hcodim : HasCodimAtLeastTwo X Z) : interior Z = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨e, ⟨c, rfl⟩, hcd⟩ := hcodim _ (interior_subset hz)
  have hK : IsOpen (e.toPoint ⁻¹' interior Z) :=
    isOpen_interior.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨O, hO, hOK⟩ := isOpen_induced_iff.mp hK
  have hcO : c.val ∈ O := by
    have : c ∈ e.toPoint ⁻¹' interior Z := hz
    rw [← hOK] at this
    exact this
  obtain ⟨b, hbO, j, hbreg⟩ :=
    RegularLocusDense.exists_regularAtDim_mem_nhds e.analytic c.property (hO.mem_nhds hcO)
  set Ω' : Set (ComplexModel e.dim) := Subtype.val '' O with hΩ'def
  have hΩ' : IsOpen Ω' := e.ambient.isOpen.isOpenMap_subtype_val O hO
  have hreg1 : RegularAtDim (n := e.dim) (M := ComplexModel e.dim) (ambientTrace e univ) b.val j := by
    rw [ambientTrace_univ]
    exact AnalyticSubsetOpens.regularAtDim_image_val_iff.mpr hbreg
  have hset : ambientTrace e univ ∩ Ω' = ambientTrace e Z ∩ Ω' := by
    ext w
    constructor
    · rintro ⟨⟨a, rfl, -⟩, ⟨b', hb'O, hb'⟩⟩
      refine ⟨⟨a, rfl, ?_⟩, ⟨b', hb'O, hb'⟩⟩
      have hab : b' = a.val := Subtype.ext hb'
      have : a ∈ Subtype.val ⁻¹' O := by
        change a.val ∈ O
        rw [← hab]
        exact hb'O
      rw [hOK] at this
      exact interior_subset this
    · rintro ⟨⟨a, rfl, -⟩, h⟩
      exact ⟨⟨a, rfl, trivial⟩, h⟩
  have hreg2 : RegularAtDim (n := e.dim) (M := ComplexModel e.dim) (ambientTrace e Z) b.val j :=
    RegularPointDimension.regularAtDim_of_inter_eq hΩ' ⟨b, hbO, rfl⟩ hset hreg1
  have hge := hcd _ _ hreg2
  have hle := AnalyticDimensionBasics.locDimLE_of_regularAtDim hreg1
  have := hge.le_of_locDimLE hle
  omega

/-! ### Unibranch spaces are locally pure dimensional -/

/-- **A unibranch complex space is locally pure dimensional.** In every local embedding, near
every point, all regular points of the carrier have the same dimension. -/
theorem exists_isPureDim_of_isUnibranch {X : SourceReducedComplexSpace} (hX : X.IsUnibranch)
    (e : LocalEmbedding X) (c : e.carrier) :
    ∃ Ω' : Set (ComplexModel e.dim), IsOpen Ω' ∧ c.val.val ∈ Ω' ∧
      Ω' ⊆ (e.ambient : Set (ComplexModel e.dim)) ∧ ∃ d : ℕ,
        AnalyticDimensionBasics.IsPureDim (n := e.dim) (M := ComplexModel e.dim)
          (ambientTrace e univ ∩ Ω') d := by
  classical
  set Sing : Set e.ambient := HironakaEmbeddedAnalytic.singularSet (n := e.dim) e.carrier
    with hSingdef
  have hSing : IsComplexAnalyticSubset (n := e.dim) Sing :=
    HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet e.analytic
  set Zs : Set X.obj.left := e.toPoint '' {a | a.val ∈ Sing} with hZsdef
  have hrep : e.toPoint ⁻¹' Zs = Subtype.val ⁻¹' Sing := by
    ext a
    constructor
    · rintro ⟨b, hb, hba⟩
      rw [← e.toPoint_injective hba]
      exact hb
    · intro h
      exact ⟨a, h, rfl⟩
  have hZsi : interior Zs = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨a, -, rfl⟩ := interior_subset hy
    have hO : IsOpen (e.toPoint ⁻¹' interior Zs) :=
      isOpen_interior.preimage e.isOpenEmbedding_toPoint.continuous
    obtain ⟨b, hbO, hbreg⟩ :=
      (HironakaResolutionSpaceComplex.dense_regular e.analytic).inter_open_nonempty _ hO ⟨a, hy⟩
    have hbZ0 : e.toPoint b ∈ Zs := interior_subset hbO
    have hbZ : b ∈ e.toPoint ⁻¹' Zs := hbZ0
    rw [hrep] at hbZ
    exact hbreg hbZ
  obtain ⟨V, hV, hcV, hVr, -, hVc⟩ :=
    e.exists_connected_neighborhood_diff hX c hZsi Sing hSing hrep e.isOpen_range_toPoint
      ⟨c, rfl⟩
  have hK : IsOpen (e.toPoint ⁻¹' V) := hV.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨O, hO, hOK⟩ := isOpen_induced_iff.mp hK
  set Ω' : Set (ComplexModel e.dim) := Subtype.val '' O with hΩ'def
  have hΩ' : IsOpen Ω' := e.ambient.isOpen.isOpenMap_subtype_val O hO
  -- the sets of points of given regular dimension
  set R : ℕ → Set X.obj.left := fun k =>
    e.toPoint '' {a | RegularAtDim (n := e.dim) e.carrier a.val k} with hRdef
  have hRopen : ∀ k, IsOpen (R k) := by
    intro k
    apply e.isOpenEmbedding_toPoint.isOpenMap
    rw [isOpen_iff_mem_nhds]
    intro a ha
    have hev := RegularPatchNeighborhood.eventually_regularAtDim ha
    have hev' := (continuous_subtype_val.continuousAt (x := a)).eventually hev
    filter_upwards [hev'] with b hb
    exact hb b.property
  have hRdisj : ∀ j k, j ≠ k → Disjoint (R j) (R k) := by
    intro j k hjk
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    rw [e.toPoint_injective hab] at hb
    exact hjk (RegularPointDimension.eq_of_regularAtDim ha hb)
  have hcover : V \ Zs ⊆ ⋃ k, R k := by
    rintro y ⟨hyV, hyZ⟩
    obtain ⟨a, rfl⟩ := hVr hyV
    have ha : a.val ∉ Sing := fun h => hyZ ⟨a, h, rfl⟩
    rw [HironakaEmbeddedAnalytic.mem_singularSet_iff] at ha
    push Not at ha
    obtain ⟨k, hk⟩ := ha a.property
    exact mem_iUnion.mpr ⟨k, a, hk, rfl⟩
  obtain ⟨y₀, hy₀⟩ := hVc.nonempty
  obtain ⟨d, hd⟩ := mem_iUnion.mp (hcover hy₀)
  set Rest : Set X.obj.left := ⋃ k, ⋃ (_ : k ≠ d), R k with hRestdef
  have hRestOpen : IsOpen Rest := by
    rw [hRestdef]
    exact isOpen_iUnion fun k => isOpen_iUnion fun _ => hRopen k
  have hsub : V \ Zs ⊆ R d := by
    refine IsPreconnected.subset_left_of_subset_union (v := Rest) (hRopen d) hRestOpen ?_ ?_
      ⟨y₀, hy₀, hd⟩ hVc.isPreconnected
    · rw [hRestdef, Set.disjoint_iUnion_right]
      intro k
      rw [Set.disjoint_iUnion_right]
      intro hk
      exact hRdisj d k (Ne.symm hk)
    · intro y hy
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover hy)
      by_cases hkd : k = d
      · exact Or.inl (hkd ▸ hk)
      · right
        rw [hRestdef]
        exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hkd, hk⟩⟩
  refine ⟨Ω', hΩ', ⟨c.val, ?_, rfl⟩, ?_, d, ?_⟩
  · have : c ∈ e.toPoint ⁻¹' V := hcV
    rw [← hOK] at this
    exact this
  · rintro _ ⟨b, -, rfl⟩
    exact b.property
  · intro y j hy
    obtain ⟨hyC, hyΩ⟩ := hy.2.1
    have hyreg : RegularAtDim (n := e.dim) (M := ComplexModel e.dim) (ambientTrace e univ) y j :=
      RegularPointDimension.regularAtDim_of_inter_eq hΩ' hyΩ (by rw [inter_assoc, inter_self]) hy
    obtain ⟨b, hbO, rfl⟩ := hyΩ
    rw [ambientTrace_univ] at hyreg
    have hbreg : RegularAtDim (n := e.dim) e.carrier b j :=
      AnalyticSubsetOpens.regularAtDim_image_val_iff.mp hyreg
    let a : e.carrier := ⟨b, hbreg.2.1⟩
    have haV : e.toPoint a ∈ V := by
      have : a ∈ Subtype.val ⁻¹' O := hbO
      rw [hOK] at this
      exact this
    have haZ : e.toPoint a ∉ Zs := by
      intro h
      have h' : a ∈ e.toPoint ⁻¹' Zs := h
      rw [hrep] at h'
      have h'' := (HironakaEmbeddedAnalytic.mem_singularSet_iff.mp h').2 j
      exact h'' hbreg
    obtain ⟨a', ha'reg, ha'⟩ := hsub ⟨haV, haZ⟩
    have haa : a' = a := e.toPoint_injective ha'
    rw [haa] at ha'reg
    exact RegularPointDimension.eq_of_regularAtDim hbreg ha'reg

/-! ### The local upper bound near a set of codimension two -/

/-- A finite set has no accumulation points. -/
theorem not_accPt_of_finite {α : Type*} [TopologicalSpace α] [T1Space α] {F : Set α}
    (hF : F.Finite) (x : α) : ¬ AccPt x (𝓟 F) := by
  rw [accPt_iff_nhds]
  push Not
  refine ⟨(F \ {x})ᶜ, ((hF.subset sdiff_subset).isClosed).isOpen_compl.mem_nhds
    (fun h => h.2 rfl), ?_⟩
  intro y hy
  by_contra hyx
  exact hy.1 ⟨hy.2, hyx⟩

/-- Local equations transported by a linear automorphism. -/
theorem hasLocalEquationsOn_image_inter {N : ℕ} {A Ω P : Set (ComplexModel N)}
    (hA : HasLocalEquationsOn A Ω) (T : ComplexModel N ≃L[ℂ] ComplexModel N) (hP : IsOpen P)
    (hPΩ : ∀ w ∈ P, T.symm w ∈ Ω) : HasLocalEquationsOn (T '' A ∩ P) P := by
  intro x hx
  obtain ⟨W, hW, hxW, m, g, hg, hgA⟩ := hA (T.symm x) (hPΩ x hx)
  refine ⟨T.symm ⁻¹' W ∩ P, (hW.preimage T.symm.continuous).inter hP, ⟨hxW, hx⟩, m,
    fun i y => g i (T.symm y), fun i => ?_, ?_⟩
  · exact (hg i).comp (T.symm : ComplexModel N →L[ℂ] ComplexModel N).differentiable.differentiableOn
      (fun y hy => hy.1)
  · intro y hy
    rw [← hgA (T.symm y) hy.1]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, -⟩
      simpa using ha
    · intro h
      exact ⟨⟨T.symm y, h, by simp⟩, hy.2⟩

/-- A point map from the ambient space of a local embedding: `w ↦` the point of `X` with
coordinate `w` (an arbitrary point `x₀` off the carrier). -/
def ambientPoint {X : SourceReducedComplexSpace} (e : LocalEmbedding X) (x₀ : X.obj.left)
    (w : ComplexModel e.dim) : X.obj.left :=
  open Classical in
  if h : ∃ a : e.carrier, a.val.val = w then e.toPoint h.choose else x₀

theorem ambientPoint_val {X : SourceReducedComplexSpace} (e : LocalEmbedding X)
    (x₀ : X.obj.left) (a : e.carrier) : ambientPoint e x₀ a.val.val = e.toPoint a := by
  have h : ∃ a' : e.carrier, a'.val.val = a.val.val := ⟨a, rfl⟩
  rw [ambientPoint, dif_pos h]
  congr 1
  exact Subtype.ext (Subtype.ext h.choose_spec)

/-- **Local boundedness near a set of codimension two** (the main step of `thm:GRexten2` (1)). On
a unibranch complex space, a function satisfying condition 2 of `def:unibranch:L105` off an
analytic subset `Z` of codimension `≥ 2` everywhere is bounded above near every point of `Z`, off
`Z`. -/
theorem exists_bound_of_hasCodimAtLeastTwo {X : SourceReducedComplexSpace} (hX : X.IsUnibranch)
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (hcodim : HasCodimAtLeastTwo X Z)
    {φ : X.obj.left → EReal} (hφ : ∀ x, x ∉ Z → X.IsLocallyAmbientPSHAt φ x) :
    ∀ z ∈ Z, ∃ Nb ∈ 𝓝 z, ∃ C : ℝ, ∀ y ∈ Nb, y ∉ Z → φ y ≤ C := by
  classical
  intro z hz
  obtain ⟨e, ⟨c, rfl⟩, hcd⟩ := hcodim _ hz
  set Ct := ambientTrace e univ with hCtdef
  set Zt := ambientTrace e Z with hZtdef
  have hZtC : Zt ⊆ Ct := by
    rintro _ ⟨a, rfl, -⟩
    exact ⟨a, rfl, trivial⟩
  have hCeq : HasLocalEquationsOn Ct e.ambient := by
    rw [hCtdef, ambientTrace_univ]
    exact hasLocalEquationsOn_of_isComplexAnalyticSubset e.analytic
  have hZeq : HasLocalEquationsOn Zt e.ambient := by
    rw [hZtdef, ambientTrace_eq]
    apply hasLocalEquationsOn_of_isComplexAnalyticSubset
    exact isComplexAnalyticSubset_image_of_isAnalyticSubset_model
      (hZ.preimage (PD.embeddingMorphism e))
  obtain ⟨Ω', hΩ', hcΩ', hΩ'sub, d, hpure⟩ := exists_isPureDim_of_isUnibranch hX e c
  have hcC : c.val.val ∈ Ct := ⟨c, rfl, trivial⟩
  obtain ⟨T, d', -, r, D, deg, δ, hr, hPsub, -, hcov, hXeq⟩ :=
    FNP.localCoveringCharts e.dim d Ct Ω' c.val.val hΩ' hcC hcΩ' (hCeq.mono hΩ'sub) hpure Ω' hΩ'
      hcΩ'
  set P : Set (ComplexModel e.dim) := pdisc (T c.val.val) r with hPdef
  have hPo : IsOpen P := isOpen_pdisc _ _
  have hPΩ' : ∀ w ∈ P, T.symm w ∈ Ω' := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hPsub hw
    simpa using hv
  have hcP : T c.val.val ∈ P := fun i => by simpa using hr i
  set X' := T '' Ct ∩ P with hX'def
  set Zh := T '' Zt ∩ P with hZhdef
  have hZhX : Zh ⊆ X' := fun w hw => ⟨image_mono hZtC hw.1, hw.2⟩
  have hZheq : HasLocalEquationsOn Zh P :=
    hasLocalEquationsOn_image_inter hZeq T hPo (fun w hw => hΩ'sub (hPΩ' w hw))
  -- pure dimension `d` of the covering and `d ≤ d'`
  have hpureX : ∀ y ∈ P, ∀ j, RegularAtDim (n := e.dim) (M := ComplexModel e.dim) (T '' Ct) y j →
      j = d := by
    intro y hyP j hy
    rw [T.image_eq_preimage_symm] at hy
    have h2 := (GermComponentDimension.regularAtDim_preimage_iff T.symm Ct y).mp hy
    exact hpure _ _ (RegularPointDimension.regularAtDim_of_inter_eq hΩ' (hPΩ' y hyP)
      (by rw [inter_assoc, inter_self]) h2)
  have hdd' : d ≤ d' := by
    let PO : Opens (ComplexModel e.dim) := ⟨P, hPo⟩
    have hXa : IsComplexAnalyticSubset (n := e.dim) ((Subtype.val : PO → ComplexModel e.dim) ⁻¹' X') :=
      FNA.isComplexAnalyticSubset_of_hasLocalEquationsOn (Ω := PO) hXeq
    have hcX : (⟨T c.val.val, hcP⟩ : PO) ∈ (Subtype.val : PO → ComplexModel e.dim) ⁻¹' X' :=
      ⟨⟨c.val.val, hcC, rfl⟩, hcP⟩
    obtain ⟨y, -, j, hy⟩ := RegularLocusDense.exists_regularAtDim_mem_nhds hXa hcX univ_mem
    have hy' := AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hy
    have hyP : y.val ∈ P := y.property
    have hj : j = d := hpureX y.val hyP j (RegularPointDimension.regularAtDim_of_inter_eq hPo hyP
      (by rw [hX'def, inter_assoc, inter_self]) hy')
    have hdimX : AnalyticDimensionBasics.DimLE (n := e.dim) (M := ComplexModel e.dim) X' d' := by
      refine FiniteMapDimension.dimLE_of_discrete_fibres
        (G := RegularLocusDense.coordinateProjection e.dim d')
        (mdifferentiable_iff_differentiable.mpr
          (RegularLocusDense.coordinateProjection e.dim d').differentiable)
        ?_ (D := univ) isComplexAnalyticSubset_univ (subset_univ _) ?_
      · intro y hy
        exact not_accPt_of_finite (hcov.finite_fibre _ (hcov.mem_base hy)) y
      · intro y k hy
        exact hy.1
    have := hdimX y.val j hy'
    omega
  have hZhdim : ∀ w k, RegularAtDim (n := e.dim) (M := ComplexModel e.dim) Zh w k → k + 2 ≤ d' := by
    intro w k hw
    have hwP : w ∈ P := hw.2.1.2
    have h1 : RegularAtDim (n := e.dim) (M := ComplexModel e.dim) (T '' Zt) w k :=
      RegularPointDimension.regularAtDim_of_inter_eq hPo hwP (by rw [hZhdef, inter_assoc, inter_self])
        hw
    rw [T.image_eq_preimage_symm] at h1
    have h2 := (GermComponentDimension.regularAtDim_preimage_iff T.symm Zt w).mp h1
    obtain ⟨y, hyΩ', j, hkj, hyreg⟩ := hcd _ _ h2 Ω' (hΩ'.mem_nhds (hPΩ' w hwP))
    have hj : j = d := hpure y j (RegularPointDimension.regularAtDim_of_inter_eq hΩ' hyΩ'
      (by rw [inter_assoc, inter_self]) hyreg)
    omega
  -- the function in the covering chart
  set f : ComplexModel e.dim → EReal := fun w => φ (ambientPoint e (e.toPoint c) (T.symm w))
    with hfdef
  have hf : ∀ x ∈ X', x ∉ Zh → ∃ O : Set (ComplexModel e.dim), IsOpen O ∧ x ∈ O ∧
      ∃ ψ : ComplexModel e.dim → EReal, PlurisubharmonicOn ψ O ∧ ∀ y ∈ X' ∩ O, f y = ψ y := by
    rintro x ⟨⟨_, ⟨a, rfl, -⟩, rfl⟩, hxP⟩ hxZ
    have haZ : e.toPoint a ∉ Z := fun h => hxZ ⟨⟨a.val.val, ⟨a, rfl, h⟩, rfl⟩, hxP⟩
    obtain ⟨W, hW, haW, -, ψ, hψ, hφψ⟩ := exists_ambient_of_morphism_at e.map e.overPoint a
      (hφ _ haZ)
    refine ⟨T.symm ⁻¹' W, hW.preimage T.symm.continuous, by simpa using haW,
      fun y => ψ (T.symm y), ?_, ?_⟩
    · exact HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
        (hW.preimage T.symm.continuous)
        (T.symm : ComplexModel e.dim →L[ℂ] ComplexModel e.dim).differentiable.differentiableOn
        (fun y hy => hy) (hψ.plurisubharmonicOn hW)
    · rintro y ⟨⟨⟨_, ⟨b, rfl, -⟩, rfl⟩, -⟩, hyW⟩
      have hbW : b.val.val ∈ W := by simpa using hyW
      simp only [hfdef, ContinuousLinearEquiv.symm_apply_apply, ambientPoint_val]
      exact hφψ b hbW
  obtain ⟨U, hU, C, hC⟩ := exists_bound_of_isBranchedCovering hcov hPo inter_subset_right hXeq
    hZhX hZheq hZhdim hf (p := T c.val.val) ⟨⟨c.val.val, hcC, rfl⟩, hcP⟩
  -- back to `X`
  set K : Set e.carrier := {a | T a.val.val ∈ interior U ∩ P} with hKdef
  have hK : IsOpen K := ((isOpen_interior.inter hPo).preimage T.continuous).preimage
    (continuous_subtype_val.comp continuous_subtype_val)
  have hcK : c ∈ K := ⟨mem_interior_iff_mem_nhds.mpr hU, hcP⟩
  refine ⟨e.toPoint '' K, (e.isOpenEmbedding_toPoint.isOpenMap _ hK).mem_nhds ⟨c, hcK, rfl⟩, C,
    ?_⟩
  rintro _ ⟨a, haK, rfl⟩ haZ
  have hx : T a.val.val ∈ X' ∩ U := ⟨⟨⟨a.val.val, ⟨a, rfl, trivial⟩, rfl⟩, haK.2⟩,
    interior_subset haK.1⟩
  have hxZ : T a.val.val ∉ Zh := by
    rintro ⟨⟨w, ⟨b, rfl, hbZ⟩, hbw⟩, -⟩
    have hba : b.val.val = a.val.val := T.injective hbw
    have hb : b = a := Subtype.ext (Subtype.ext hba)
    rw [hb] at hbZ
    exact haZ hbZ
  have h := hC _ hx hxZ
  simpa only [hfdef, ContinuousLinearEquiv.symm_apply_apply, ambientPoint_val] using h

/-! ### The Grauert--Remmert extension theorem -/

/-- **Source `thm:GRexten2`, item (1), with uniqueness and `eq:GRextvarphi`.** Let `X` be a
unibranch complex space, `Z ⊆ X` an analytic subset of codimension `≥ 2` everywhere, `j : W → X`
the open subspace `X \ Z` and `φ` with `φ ∘ j ∈ PSH(W)` (i.e. `φ ∈ PSH(X \ Z)`). Then
`analyticExtension Z φ` is psh on `X` and extends `φ`, every psh extension of `φ` equals it, and its
value at every `x` is `limsup_{X \ Z ∋ y → x} φ(y)`. -/
theorem grauertRemmert_extension_codimTwo {X W : SourceReducedComplexSpace} (hX : X.IsUnibranch)
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (hcodim : HasCodimAtLeastTwo X Z)
    (j : W ⟶ X) (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (hjr : range j.hom.left.base = Zᶜ) {φ : X.obj.left → EReal}
    (hφ : W.IsPSH (fun w => φ (j.hom.left.base w))) :
    X.IsPSH (analyticExtension Z φ) ∧ EqOn (analyticExtension Z φ) φ Zᶜ ∧
      (∀ η : X.obj.left → EReal, X.IsPSH η → EqOn η φ Zᶜ → η = analyticExtension Z φ) ∧
      ∀ x, analyticExtension Z φ x = limsup φ (𝓝[Zᶜ] x) := by
  have hloc : ∀ x, x ∉ Z → X.IsLocallyAmbientPSHAt φ x := fun x hx =>
    isLocallyAmbientPSHAt_of_isPSH_openImmersion j hj hφ (by rw [hjr]; exact hx)
  exact grauertRemmert_extension_bounded hX hZ hcodim.interior_eq_empty j hj hjr hφ
    (exists_bound_of_hasCodimAtLeastTwo hX hZ hcodim hloc)

/-- **Source `thm:GRexten2` (Grauert--Remmert), both items.** Let `X` be a unibranch complex space,
`Z ⊆ X` an analytic subset, `j : W → X` the open subspace `X \ Z`, and `φ ∈ PSH(X \ Z)`
(`φ ∘ j ∈ PSH(W)`). Assume (1) `Z` has codimension at least `2` everywhere, or (2) `Z` has
codimension at least `1` everywhere (`interior Z = ∅`) and `φ` is locally bounded from above near
`Z`. Then `φ` admits an extension to `PSH(X)`; the extension is unique and is given by
`eq:GRextvarphi`: `φ(x) = limsup_{X \ Z ∋ y → x} φ(y)` (= `analyticExtension Z φ x`). -/
theorem grauertRemmert_extension {X W : SourceReducedComplexSpace} (hX : X.IsUnibranch)
    {Z : Set X.obj.left} (hZ : X.IsAnalyticSubset Z) (j : W ⟶ X)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (hjr : range j.hom.left.base = Zᶜ)
    {φ : X.obj.left → EReal} (hφ : W.IsPSH (fun w => φ (j.hom.left.base w)))
    (hcase : HasCodimAtLeastTwo X Z ∨
      (interior Z = ∅ ∧ ∀ x ∈ Z, ∃ Nb ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ Nb, y ∉ Z → φ y ≤ C)) :
    (∃ η : X.obj.left → EReal, X.IsPSH η ∧ EqOn η φ Zᶜ) ∧
      (∀ η₁ η₂ : X.obj.left → EReal, X.IsPSH η₁ → EqOn η₁ φ Zᶜ → X.IsPSH η₂ →
        EqOn η₂ φ Zᶜ → η₁ = η₂) ∧
      ∀ η : X.obj.left → EReal, X.IsPSH η → EqOn η φ Zᶜ →
        ∀ x, η x = limsup φ (𝓝[Zᶜ] x) := by
  have h := hcase.elim (fun h => grauertRemmert_extension_codimTwo hX hZ h j hj hjr hφ)
    (fun h => grauertRemmert_extension_bounded hX hZ h.1 j hj hjr hφ h.2)
  obtain ⟨hpsh, heq, huniq, hform⟩ := h
  refine ⟨⟨_, hpsh, heq⟩, fun η₁ η₂ h₁ e₁ h₂ e₂ => (huniq η₁ h₁ e₁).trans (huniq η₂ h₂ e₂).symm,
    fun η hη hηφ x => ?_⟩
  rw [huniq η hη hηφ, hform x]

end SGPT.Unibranch.PD3
