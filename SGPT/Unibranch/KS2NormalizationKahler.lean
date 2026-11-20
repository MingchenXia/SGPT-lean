import SGPT.Unibranch.KS2LeviEstimate
import SGPT.Unibranch.KSNormalizedSubvariety
import SGPT.Unibranch.NativeNov16FiniteFibreLocalPotential
import SGPT.Unibranch.NativeNov16ClosedSetAmbientPartition
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# A Kähler form on the normalization `Ỹ`

Source: footnote of `def:traceop` (`chapter_trace.tex`): "We can find a closed smooth real
`(1,1)`-form `θ` on `X` such that `φ ∈ PSH(X, θ)`. Then there is a Kähler form such that
`ω + θ + ddᶜ φ_j ≥ 0` for all `j ≥ 1`. **Take a Kähler form `ω̃` on `Ỹ` so that
`ω̃ ≥ (θ + ω)|_Ỹ`** and `ψ ∈ PSH(Ỹ, ω̃)`." Here `Y ⊆ X` is an analytic subset of the compact
Kähler manifold `X` and `p : Ỹ → Y` its normalization (`sec:trace_def`: "`Ỹ` is a normal Kähler
space [GK20, Prop. 3.6]").

The pull-back `p^*ω` of a Kähler form is NOT Kähler in general (cusp). We formalize the standard
construction for finite maps (Varouchas; [GK20, Prop. 3.6]):

* `WindowData`: finitely many windows `V_j` of `Y` over which `Ỹ` carries fibre potentials `ρ_j`,
  locally `‖z‖²` in local embeddings of `Ỹ` (PR #273,
  `NativeNov16FiniteFibreLocalPotential.exists_window_potential`), and a smooth cutoff partition
  `(χ_a)` on `X` subordinate to ambient open sets `U_j` with `U_j ∩ Y = V_j`;
* `WindowData.potential`: the glued potential `Ρ = Σ_a χ_a(p) ρ_{j(a)}`, a smooth function on
  `Ỹ` (`potential_isSmoothFunction`);
* `kahlerForm D ω B = (B ω)|_Ỹ + ddᶜ Ρ`, a `SpaceForm` on `Ỹ` (`KS2KahlerSpace.add`, `ddcOf`);
* `exists_kahlerChart`: near every point of `Ỹ`, in ONE local embedding, `p` is induced by a
  holomorphic `P`, `Ρ` is `R = χ₀(P z)‖z‖² + Σ χ_a(P z)‖G_a z‖²`, and `ddᶜ R + B·P^*ω` is
  strictly positive for all `B ≥ B₀` (`KS2LeviEstimate.exists_isStrictlyPositive_near`);
* `exists_pos_forall_isKahler`: by compactness of `Ỹ`, ONE `B₀` works everywhere:
  **`kahlerForm D ω B` is a Kähler form on `Ỹ` for all `B ≥ B₀`** (`SpaceForm.IsKahler`);
* **`exists_kahler_dominating`: for every closed real `(1,1)`-form `θ` on `X` there is a Kähler
  form `ω̃` on `Ỹ` with `ω̃ ≥ θ|_Ỹ`** (`SpaceForm.Dominates`), and
  `exists_kahler_dominating_add`: `ω̃ ≥ (θ + ω)|_Ỹ`, the footnote's statement;
* `normalization_isKahlerSpace`: `Ỹ` is a Kähler space.

Blueprint: `blueprint/src/KS2.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.RegularLocusCutoffPartitionReduction
open SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces

namespace SGPT.Unibranch.KS2NormalizationKahler

open SourceReducedComplexSpace KSNormalizedSubvariety

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)

/-- The point of `M` under a point of `Ỹ`. -/
abbrev base (y : (normalization C hC).obj.left) : M :=
  ((normalizationMap C hC).hom.left.base y).val

theorem ofChart_toPoint_val (x : M) (b : (LocalEmbedding.ofChart C hC x).carrier) :
    ((LocalEmbedding.ofChart C hC x).toPoint b).val =
      (complexChartAt (n := n) x).val.symm b.val.val := rfl

/-- Data for the glued potential: windows of `Y` with fibre potentials `ρ_j` (locally `‖z‖²` in
local embeddings of `Ỹ`) and a cutoff partition on `M` subordinate to `U_j`, `U_j ∩ Y = V_j`. -/
structure WindowData where
  r : ℕ
  V : Fin r → Opens (ofClosedAnalytic C hC).obj.left
  U : Fin r → Opens M
  P : CompactCutoffPartition (n := n) C U
  rho : Fin r → (normalization C hC).obj.left → ℝ
  pre : ∀ j, (Subtype.val : C → M) ⁻¹' (U j : Set M) =
    (V j : Set (ofClosedAnalytic C hC).obj.left)
  window : ∀ j (y : (normalization C hC).obj.left),
    (normalizationMap C hC).hom.left.base y ∈ V j →
      ∃ e : LocalEmbedding (normalization C hC), y ∈ range e.toPoint ∧
        ∀ c : e.carrier, rho j (e.toPoint c) = ‖c.val.val‖ ^ 2

theorem windowData_nonempty [CompactSpace M] : Nonempty (WindowData C hC) := by
  classical
  choose W hmem rho _hrho hlocal using fun x : C =>
    NativeNov16FiniteFibreLocalPotential.exists_window_potential (normalizationMap C hC)
      (normalizationMap_isProperMap C hC) x (normalizationMap_finite_fibres C hC x)
  obtain ⟨r, idx, U, hpre, ⟨P⟩⟩ :=
    NativeNov16ClosedSetAmbientPartition.exists_ambient_partition (n := n) C hC.isClosed
      (fun x : C => W x) (fun x => ⟨x, hmem x⟩)
  refine ⟨⟨r, fun j => W (idx j), U, P, fun j => rho (idx j), hpre, ?_⟩⟩
  intro j y hy
  obtain ⟨e, he, -, -, -, hread⟩ := hlocal (idx j) y hy
  exact ⟨e, he, hread⟩

variable {C hC}

namespace WindowData

variable (D : WindowData C hC)

/-- The `a`-th term `χ_a(p y) ρ_{j(a)}(y)` of the glued potential. -/
def term (a : Fin D.P.size) (y : (normalization C hC).obj.left) : ℝ :=
  match D.P.index a with
  | some j => D.P.cutoff a (base C hC y) * D.rho j y
  | none => 0

/-- The glued potential `Ρ = Σ_a χ_a(p) ρ_{j(a)}` on `Ỹ`. -/
def potential (y : (normalization C hC).obj.left) : ℝ := ∑ a, D.term a y

/-- The cutoff `χ_a` read in the chart of `M` at `x`. -/
def chartCutoff (x : M) (a : Fin D.P.size) : ComplexModel n → ℝ :=
  fun w => D.P.cutoff a ((complexChartAt (n := n) x).val.symm w)

end WindowData

/-- The normalization map is induced, near every point of every local embedding of `Ỹ`, by a
holomorphic map into a chart of `M`. -/
theorem exists_lift (e : LocalEmbedding (normalization C hC)) (c : e.carrier) (x : M)
    (hx : (normalizationMap C hC).hom.left.base (e.toPoint c) ∈
      range (LocalEmbedding.ofChart C hC x).toPoint) :
    ∃ W : Set (ComplexModel e.dim), IsOpen W ∧ c.val.val ∈ W ∧ W ⊆ e.ambient ∧
      ∃ P : ComplexModel e.dim → ComplexModel n, ContDiffOn ℂ ∞ P W ∧
        MapsTo P W (complexChartAt (n := n) x).val.target ∧
        ∀ c' : e.carrier, c'.val.val ∈ W → ∃ b : (LocalEmbedding.ofChart C hC x).carrier,
          b.val.val = P c'.val.val ∧
          (LocalEmbedding.ofChart C hC x).toPoint b =
            (normalizationMap C hC).hom.left.base (e.toPoint c') := by
  have hover : (e.map ≫ (normalizationMap C hC).hom.left) ≫ (ofClosedAnalytic C hC).obj.hom =
      (modelOver e.ambient e.carrier).hom := by
    rw [Category.assoc, Over.w (normalizationMap C hC).hom, e.overPoint]
  obtain ⟨W, hW, hcW, hWU, G, hG, hmaps, hfac⟩ :=
    LocalEmbedding.exists_contDiffOn_factor (e.map ≫ (normalizationMap C hC).hom.left) hover
      (LocalEmbedding.ofChart C hC x) c hx
  exact ⟨W, hW, hcW, hWU, G, hG, fun w hw => hmaps hw, fun c' hc' => hfac c' hc'⟩

/-- The lift computes the base point: `p(e c) = φ⁻¹(P c)`. -/
theorem base_eq_of_factor {e : LocalEmbedding (normalization C hC)} {x : M}
    {P : ComplexModel e.dim → ComplexModel n} {c : e.carrier}
    (hfac : ∃ b : (LocalEmbedding.ofChart C hC x).carrier, b.val.val = P c.val.val ∧
      (LocalEmbedding.ofChart C hC x).toPoint b =
        (normalizationMap C hC).hom.left.base (e.toPoint c)) :
    base C hC (e.toPoint c) = (complexChartAt (n := n) x).val.symm (P c.val.val) := by
  obtain ⟨b, hb, hpb⟩ := hfac
  have h := congrArg Subtype.val hpb
  rw [ofChart_toPoint_val, hb] at h
  exact h.symm

/-- Local form of each term of the glued potential in a fixed local embedding. -/
theorem exists_term_local (D : WindowData C hC) (e : LocalEmbedding (normalization C hC))
    (c₀ : e.carrier) {x : M} (hx : base C hC (e.toPoint c₀) = x)
    {WP : Set (ComplexModel e.dim)} (hWP : IsOpen WP) (hc₀WP : c₀.val.val ∈ WP)
    {P : ComplexModel e.dim → ComplexModel n} (hP : ContDiffOn ℂ ∞ P WP)
    (hmaps : MapsTo P WP (complexChartAt (n := n) x).val.target)
    (hfac : ∀ c' : e.carrier, c'.val.val ∈ WP → ∃ b : (LocalEmbedding.ofChart C hC x).carrier,
      b.val.val = P c'.val.val ∧
      (LocalEmbedding.ofChart C hC x).toPoint b =
        (normalizationMap C hC).hom.left.base (e.toPoint c'))
    (a : Fin D.P.size) :
    ∃ W : Set (ComplexModel e.dim), IsOpen W ∧ c₀.val.val ∈ W ∧ ∃ m : ℕ,
      ∃ G : ComplexModel e.dim → ComplexModel m, ContDiffOn ℂ ∞ G W ∧
        ∀ c : e.carrier, c.val.val ∈ W → c.val.val ∈ WP →
          D.term a (e.toPoint c) = D.chartCutoff x a (P c.val.val) * ‖G c.val.val‖ ^ 2 := by
  cases ha : D.P.index a with
  | none =>
    refine ⟨univ, isOpen_univ, mem_univ _, 0, fun _ => 0, contDiffOn_const, ?_⟩
    intro c _ _
    simp [WindowData.term, ha]
  | some j =>
    by_cases hxs : x ∈ tsupport (D.P.cutoff a)
    · have hyV : (normalizationMap C hC).hom.left.base (e.toPoint c₀) ∈ D.V j := by
        have h1 : (normalizationMap C hC).hom.left.base (e.toPoint c₀) ∈
            (Subtype.val : C → M) ⁻¹' (D.U j : Set M) := by
          change base C hC (e.toPoint c₀) ∈ (D.U j : Set M)
          rw [hx]
          exact D.P.support_some a j ha hxs
        rw [D.pre j] at h1
        exact h1
      obtain ⟨e', ⟨c', hc'⟩, hread⟩ := D.window j (e.toPoint c₀) hyV
      obtain ⟨W, hW, hcW, -, G, hG, -, hfacG⟩ :=
        e.exists_contDiff_transition e' c₀ ⟨c', hc'⟩
      refine ⟨W, hW, hcW, e'.dim, G, hG, ?_⟩
      intro c hcW' hcP
      obtain ⟨z, hz, hzc⟩ := hfacG c hcW'
      simp only [WindowData.term, ha]
      rw [← hzc, hread z, hz, hzc, base_eq_of_factor (hfac c hcP)]
      rfl
    · let φ := complexChartAt (n := n) x
      let O' : Set (ComplexModel n) := φ.val.target ∩ φ.val.symm ⁻¹' (tsupport (D.P.cutoff a))ᶜ
      have hO' : IsOpen O' := φ.val.isOpen_inter_preimage_symm (isClosed_tsupport _).isOpen_compl
      let W : Set (ComplexModel e.dim) := WP ∩ P ⁻¹' O'
      have hW : IsOpen W := hP.continuousOn.isOpen_inter_preimage hWP hO'
      have hc₀W : c₀.val.val ∈ W := by
        refine ⟨hc₀WP, hmaps hc₀WP, ?_⟩
        change φ.val.symm (P c₀.val.val) ∉ tsupport (D.P.cutoff a)
        rw [← base_eq_of_factor (hfac c₀ hc₀WP), hx]
        exact hxs
      refine ⟨W, hW, hc₀W, 0, fun _ => 0, contDiffOn_const, ?_⟩
      intro c hcW' hcP
      have hzero : D.P.cutoff a (base C hC (e.toPoint c)) = 0 := by
        rw [base_eq_of_factor (hfac c hcP)]
        exact image_eq_zero_of_notMem_tsupport hcW'.2.2
      simp only [WindowData.term, ha, hzero, zero_mul]
      simp

/-- **Kähler charts of `Ỹ`.** Near every point of `Ỹ` there are a local embedding `e`, a
holomorphic `P` inducing `p` into the chart of `M` at `x`, a smooth ambient extension `R` of the
glued potential, and `B₀` such that `ddᶜ R + B · P^*ω` is strictly positive on the whole ambient
open set of `e` for every `B ≥ B₀`. -/
theorem exists_kahlerChart (D : WindowData C hC) (omega : KahlerBackground n M)
    (y : (normalization C hC).obj.left) :
    ∃ (e : LocalEmbedding (normalization C hC)) (x : M)
      (P : ComplexModel e.dim → ComplexModel n) (R : ComplexModel e.dim → ℝ) (B₀ : ℝ),
      y ∈ range e.toPoint ∧ ContDiffOn ℂ ∞ P e.ambient ∧
      MapsTo P e.ambient (complexChartAt (n := n) x).val.target ∧
      (∀ c : e.carrier, ∃ b : (LocalEmbedding.ofChart C hC x).carrier,
        b.val.val = P c.val.val ∧
        (LocalEmbedding.ofChart C hC x).toPoint b =
          (normalizationMap C hC).hom.left.base (e.toPoint c)) ∧
      ContDiffOn ℝ ∞ R e.ambient ∧ (∀ c : e.carrier, R c.val.val = D.potential (e.toPoint c)) ∧
      ∀ B : ℝ, B₀ ≤ B → ∀ z ∈ e.ambient,
        IsStrictlyPositive (smoothDDC R z +
          B • pullbackForm P (omega.form.val.coeff (complexChartAt (n := n) x)) z) := by
  classical
  -- a cutoff which is positive at `p(y)`
  have hsum := D.P.sum_eq_one_on (base C hC y) ((normalizationMap C hC).hom.left.base y).property
  obtain ⟨a₀, ha₀mem, ha₀ne⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  have ha₀pos : 0 < D.P.cutoff a₀ (base C hC y) :=
    lt_of_le_of_ne (D.P.nonneg a₀ _) (Ne.symm ha₀ne)
  obtain ⟨j₀, hj₀⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp ha₀mem).2
  have hyV : (normalizationMap C hC).hom.left.base y ∈ D.V j₀ := by
    have h1 : (normalizationMap C hC).hom.left.base y ∈
        (Subtype.val : C → M) ⁻¹' (D.U j₀ : Set M) :=
      D.P.support_some a₀ j₀ hj₀ (subset_tsupport _ ha₀ne)
    rw [D.pre j₀] at h1
    exact h1
  -- the window embedding at `y`, on which `ρ_{j₀} = ‖z‖²`
  obtain ⟨e, ⟨c₀, hc₀⟩, hread₀⟩ := D.window j₀ y hyV
  subst hc₀
  set x : M := base C hC (e.toPoint c₀) with hxdef
  obtain ⟨WP, hWP, hc₀WP, hWPe, P, hP, hmaps, hfac⟩ := exists_lift e c₀ x
    (mem_range_chartModelMap (n := n) C
      ((normalizationMap C hC).hom.left.base (e.toPoint c₀)).property)
  -- local forms of all terms
  have hterm := fun a => exists_term_local D e c₀ hxdef.symm hWP hc₀WP hP hmaps hfac a
  choose Wa hWa hc₀Wa m G hG hGeq using hterm
  let T : Set (ComplexModel e.dim) := WP ∩ ⋂ a, Wa a
  have hT : IsOpen T := hWP.inter (isOpen_iInter_of_finite hWa)
  have hc₀T : c₀.val.val ∈ T := ⟨hc₀WP, mem_iInter.mpr hc₀Wa⟩
  have hTWP : T ⊆ WP := inter_subset_left
  have hTWa : ∀ a, T ⊆ Wa a := fun a z hz => mem_iInter.mp hz.2 a
  let s : Finset (Fin D.P.size) := Finset.univ.erase a₀
  let R : ComplexModel e.dim → ℝ :=
    KS2LeviEstimate.potential s P (D.chartCutoff x a₀) (D.chartCutoff x) G
  have hχ : ∀ a, ContDiffOn ℝ ∞ (D.chartCutoff x a) (complexChartAt (n := n) x).val.target :=
    fun a => D.P.smooth a (complexChartAt (n := n) x)
  have hReq : ∀ c : e.carrier, c.val.val ∈ T → R c.val.val = D.potential (e.toPoint c) := by
    intro c hc
    have h0 : D.term a₀ (e.toPoint c) = D.chartCutoff x a₀ (P c.val.val) * ‖c.val.val‖ ^ 2 := by
      simp only [WindowData.term, hj₀]
      rw [hread₀ c, base_eq_of_factor (hfac c (hTWP hc))]
      rfl
    have hrest : ∑ a ∈ s, D.term a (e.toPoint c) =
        ∑ a ∈ s, D.chartCutoff x a (P c.val.val) * ‖G a c.val.val‖ ^ 2 :=
      Finset.sum_congr rfl fun a _ => hGeq a c (hTWa a hc) (hTWP hc)
    simp only [R, KS2LeviEstimate.potential, WindowData.potential]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a₀), h0, hrest]
  -- the positivity estimate
  have hχ₀b : 0 < D.chartCutoff x a₀ (P c₀.val.val) := by
    change 0 < D.P.cutoff a₀ ((complexChartAt (n := n) x).val.symm (P c₀.val.val))
    rw [← base_eq_of_factor (hfac c₀ hc₀WP)]
    exact ha₀pos
  obtain ⟨B₀, -, U, hU, hbU, hUT, hB⟩ := KS2LeviEstimate.exists_isStrictlyPositive_near s hT
    (complexChartAt (n := n) x).val.open_target (hP.mono hTWP) (fun z hz => hmaps (hTWP hz))
    (omega.form.val.smooth _) (fun z hz => (omega.isKahler.1 _ z hz).2) (hχ a₀) hχ
    (fun a z _ => D.P.nonneg a _) (fun a => (hG a).mono (hTWa a)) hc₀T hχ₀b
  -- restrict the embedding to `U`
  let U' : Opens (ComplexModel e.dim) := ⟨U, hU⟩
  have hUWP : U ⊆ WP := fun z hz => hTWP (hUT hz)
  have hU'e : U' ≤ e.ambient := fun z hz => hWPe (hUWP hz)
  refine ⟨e.restrict U' hU'e, x, P, R, B₀, ⟨⟨⟨c₀.val.val, hbU⟩, c₀.property⟩, rfl⟩,
    hP.mono hUWP, fun z hz => hmaps (hUWP hz), ?_, ?_, ?_, ?_⟩
  · intro c
    exact hfac ⟨Opens.inclusion hU'e c.val, c.property⟩ (hUWP c.val.property)
  · exact (KS2LeviEstimate.potential_contDiffOn s (hP.mono hTWP) (fun z hz => hmaps (hTWP hz))
      (hχ a₀) hχ (fun a => (hG a).mono (hTWa a))).mono hUT
  · intro c
    exact hReq ⟨Opens.inclusion hU'e c.val, c.property⟩ (hUT c.val.property)
  · intro B hB' z hz
    exact hB B hB' z hz

/-- The glued potential is a smooth function on `Ỹ`. -/
theorem potential_isSmoothFunction (D : WindowData C hC) (omega : KahlerBackground n M) :
    (normalization C hC).IsSmoothFunction D.potential := by
  intro y
  obtain ⟨e, -, -, R, -, hy, -, -, -, hR, hReq, -⟩ := exists_kahlerChart D omega y
  exact ⟨e, hy, R, hR, hReq⟩

/-- **The candidate Kähler form** `(B ω)|_Ỹ + ddᶜ Ρ` on `Ỹ`. -/
def kahlerForm (D : WindowData C hC) (omega : KahlerBackground n M) (B : ℝ) :
    SpaceForm (normalization C hC) 2 :=
  (restrictForm C hC (B • omega.form).val).add
    (SpaceForm.ddcOf D.potential (potential_isSmoothFunction D omega))

/-- The ambient representatives of `kahlerForm` in a Kähler chart. -/
theorem kahlerForm_restrictsTo (D : WindowData C hC) (omega : KahlerBackground n M) (B : ℝ)
    {e : LocalEmbedding (normalization C hC)} {x : M} {P : ComplexModel e.dim → ComplexModel n}
    {R : ComplexModel e.dim → ℝ} (hP : ContDiffOn ℂ ∞ P e.ambient)
    (hmaps : MapsTo P e.ambient (complexChartAt (n := n) x).val.target)
    (hfac : ∀ c : e.carrier, ∃ b : (LocalEmbedding.ofChart C hC x).carrier,
      b.val.val = P c.val.val ∧
      (LocalEmbedding.ofChart C hC x).toPoint b =
        (normalizationMap C hC).hom.left.base (e.toPoint c))
    (hR : ContDiffOn ℝ ∞ R e.ambient)
    (hReq : ∀ c : e.carrier, R c.val.val = D.potential (e.toPoint c))
    (θ : SmoothRealForm n M 2) :
    (restrictForm C hC θ).RestrictsTo e (pullbackForm P (θ.coeff (complexChartAt (n := n) x))) ∧
    ContDiffOn ℝ ∞ (pullbackForm P (θ.coeff (complexChartAt (n := n) x))) e.ambient ∧
    (kahlerForm D omega B).RestrictsTo e
      (pullbackForm P ((B • omega.form).val.coeff (complexChartAt (n := n) x)) + smoothDDC R) := by
  have hpull : ∀ θ' : SmoothRealForm n M 2,
      (restrictForm C hC θ').RestrictsTo e (pullbackForm P (θ'.coeff (complexChartAt (n := n) x))) ∧
      ContDiffOn ℝ ∞ (pullbackForm P (θ'.coeff (complexChartAt (n := n) x))) e.ambient := by
    intro θ'
    refine ⟨SpaceForm.pullback_restrictsTo_of_lift _ (normalizationMap C hC)
      (SpaceForm.ofClosedAnalytic_restrictsTo C hC θ' x) e hP (fun z hz => hmaps hz) hfac, ?_⟩
    exact SmoothRealForm.contDiffOn_compContinuousLinearMap
      ((θ'.smooth _).comp (hP.restrict_scalars ℝ) hmaps)
      ((hP.restrict_scalars ℝ).fderiv_of_isOpen e.ambient.isOpen (by simp))
  refine ⟨(hpull θ).1, (hpull θ).2, ?_⟩
  exact SpaceForm.restrictsTo_add (hpull _).2
    (Pending.LogWeightFactorization.smoothDDC_contDiffOn e.ambient.isOpen hR) (hpull _).1
    (SpaceForm.restrictsTo_ddcOf _ hR hReq)

/-- Nonnegativity on complex lines of a strictly positive form. -/
theorem quad_nonneg_of_isStrictlyPositive {N : ℕ}
    {a : (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ} (ha : IsStrictlyPositive a) (u : ComplexModel N) :
    0 ≤ a ![u, Complex.I • u] := by
  by_cases hu : u = 0
  · subst hu
    rw [a.map_coord_zero (0 : Fin 2) rfl]
  · exact (ha u hu).le

/-- **One constant for all of `Ỹ`.** There is `B₀ > 0` such that `kahlerForm D ω B` is a Kähler
form on `Ỹ` for every `B ≥ B₀`; moreover every point lies in a Kähler chart of `exists_kahlerChart`
whose constant is at most `B₀`. -/
theorem exists_uniform_kahlerChart [CompactSpace M] (D : WindowData C hC)
    (omega : KahlerBackground n M) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ y : (normalization C hC).obj.left,
      ∃ (e : LocalEmbedding (normalization C hC)) (x : M)
        (P : ComplexModel e.dim → ComplexModel n) (R : ComplexModel e.dim → ℝ),
        y ∈ range e.toPoint ∧ ContDiffOn ℂ ∞ P e.ambient ∧
        MapsTo P e.ambient (complexChartAt (n := n) x).val.target ∧
        (∀ c : e.carrier, ∃ b : (LocalEmbedding.ofChart C hC x).carrier,
          b.val.val = P c.val.val ∧
          (LocalEmbedding.ofChart C hC x).toPoint b =
            (normalizationMap C hC).hom.left.base (e.toPoint c)) ∧
        ContDiffOn ℝ ∞ R e.ambient ∧
        (∀ c : e.carrier, R c.val.val = D.potential (e.toPoint c)) ∧
        ∀ B : ℝ, B₀ ≤ B → ∀ z ∈ e.ambient,
          IsStrictlyPositive (smoothDDC R z +
            B • pullbackForm P (omega.form.val.coeff (complexChartAt (n := n) x)) z) := by
  classical
  have hcpt : CompactSpace (normalization C hC).obj.left := normalization_compactSpace C hC
  choose e x P R B hy hP hmaps hfac hR hReq hB using exists_kahlerChart D omega
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => range (e y).toPoint)
    (fun y => (e y).isOpen_range_toPoint) (fun y _ => mem_iUnion.mpr ⟨y, hy y⟩)
  refine ⟨1 + ∑ y ∈ t, |B y|, by positivity, fun y' => ?_⟩
  obtain ⟨y, hyt, hy'⟩ := mem_iUnion₂.mp (ht (mem_univ y'))
  refine ⟨e y, x y, P y, R y, hy', hP y, hmaps y, hfac y, hR y, hReq y, fun B' hB' z hz => ?_⟩
  refine hB y B' ?_ z hz
  have h1 : |B y| ≤ ∑ y ∈ t, |B y| :=
    Finset.single_le_sum (f := fun y => |B y|) (fun _ _ => abs_nonneg _) hyt
  linarith [le_abs_self (B y)]

/-- **`Ỹ` carries Kähler forms**: `(B ω)|_Ỹ + ddᶜ Ρ` is Kähler for all `B ≥ B₀`. -/
theorem exists_pos_forall_isKahler [CompactSpace M] (D : WindowData C hC)
    (omega : KahlerBackground n M) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B → (kahlerForm D omega B).IsKahler := by
  obtain ⟨B₀, hB₀, hchart⟩ := exists_uniform_kahlerChart D omega
  refine ⟨B₀, hB₀, fun B hB y => ?_⟩
  obtain ⟨e, x, P, R, hy, hP, hmaps, hfac, hR, hReq, hpos⟩ := hchart y
  obtain ⟨-, -, hres⟩ :=
    kahlerForm_restrictsTo D omega B hP hmaps hfac hR hReq (omega.form.val)
  let w := omega.form.val.coeff (complexChartAt (n := n) x)
  have hw : (B • omega.form).val.coeff (complexChartAt (n := n) x) = B • w := by
    funext z
    exact ClosedRealOneOneForm.coeff_smul B omega.form _ z
  refine ⟨e, hy, _, ?_, ?_, ?_, hres⟩
  · exact (SmoothRealForm.contDiffOn_compContinuousLinearMap
      (((B • omega.form).val.smooth _).comp (hP.restrict_scalars ℝ) hmaps)
      ((hP.restrict_scalars ℝ).fderiv_of_isOpen e.ambient.isOpen (by simp))).add
      (Pending.LogWeightFactorization.smoothDDC_contDiffOn e.ambient.isOpen hR)
  · intro z hz
    exact KS2LeviEstimate.extDeriv_pullback_add_ddc e.ambient.isOpen
      (complexChartAt (n := n) x).val.open_target hP hmaps ((B • omega.form).val.smooth _)
      (fun z' hz' => (B • omega.form).property.1 _ z' hz') hR hz
  · intro z hz
    refine ⟨KS2LeviEstimate.isOneOne_pullback_add_ddc e.ambient.isOpen hP hmaps
      (fun z' hz' => (B • omega.form).property.2 _ z' hz') hR hz, ?_⟩
    have h := hpos B hB z hz
    rw [hw, pullbackForm_smul]
    simpa only [Pi.add_apply, Pi.smul_apply, add_comm] using h

variable (C hC) in
/-- **`Ỹ` is a Kähler space** (`sec:trace_def`, [GK20, Prop. 3.6]). -/
theorem normalization_isKahlerSpace [CompactSpace M] (omega : KahlerBackground n M) :
    (normalization C hC).IsKahlerSpace := by
  obtain ⟨D⟩ := windowData_nonempty C hC
  obtain ⟨B₀, -, h⟩ := exists_pos_forall_isKahler D omega
  exact ⟨_, h B₀ le_rfl⟩

variable (C hC) in
/-- **The footnote of `def:traceop`: for every closed real `(1,1)`-form `θ` on the compact Kähler
manifold `X` there is a Kähler form `ω̃` on `Ỹ` with `ω̃ ≥ θ|_Ỹ`.** -/
theorem exists_kahler_dominating [CompactSpace M] (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) :
    ∃ omt : SpaceForm (normalization C hC) 2, omt.IsKahler ∧
      omt.Dominates (restrictForm C hC θ.val) := by
  obtain ⟨D⟩ := windowData_nonempty C hC
  obtain ⟨B₀, hB₀, hchart⟩ := exists_uniform_kahlerChart D omega
  obtain ⟨K, hK, hsemi⟩ := Pending.KahlerDomination.exists_pos_isSemipositive_add_smul omega (-θ)
  obtain ⟨B₁, -, hkahler⟩ := exists_pos_forall_isKahler D omega
  refine ⟨kahlerForm D omega (max B₀ B₁ + K), hkahler _ (by
    linarith [le_max_right B₀ B₁]), fun y => ?_⟩
  obtain ⟨e, x, P, R, hy, hP, hmaps, hfac, hR, hReq, hpos⟩ := hchart y
  obtain ⟨hθres, hθsmooth, hres⟩ :=
    kahlerForm_restrictsTo D omega (max B₀ B₁ + K) hP hmaps hfac hR hReq θ.val
  refine ⟨e, hy, _, _, ?_, hθsmooth, hres, hθres, ?_⟩
  · exact (SmoothRealForm.contDiffOn_compContinuousLinearMap
      ((((max B₀ B₁ + K) • omega.form).val.smooth _).comp (hP.restrict_scalars ℝ) hmaps)
      ((hP.restrict_scalars ℝ).fderiv_of_isOpen e.ambient.isOpen (by simp))).add
      (Pending.LogWeightFactorization.smoothDDC_contDiffOn e.ambient.isOpen hR)
  · intro z hz
    let φ := complexChartAt (n := n) x
    let c := max B₀ B₁ + K
    have hcoeff : (c • omega.form - θ).val.coeff φ =
        (c • omega.form).val.coeff φ - θ.val.coeff φ := by
      funext z'
      simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
        Pi.add_apply, Pi.neg_apply]
    have hvw : pullbackForm P ((c • omega.form).val.coeff φ) + smoothDDC R -
        pullbackForm P (θ.val.coeff φ) =
        pullbackForm P ((c • omega.form - θ).val.coeff φ) + smoothDDC R := by
      rw [hcoeff, pullbackForm_sub]
      abel
    refine ⟨?_, ?_, fun u => ?_⟩
    · rw [hvw]
      exact KS2LeviEstimate.extDeriv_pullback_add_ddc e.ambient.isOpen φ.val.open_target hP hmaps
        ((c • omega.form - θ).val.smooth _)
        (fun z' hz' => (c • omega.form - θ).property.1 _ z' hz') hR hz
    · rw [hvw]
      exact KS2LeviEstimate.isOneOne_pullback_add_ddc e.ambient.isOpen hP hmaps
        (fun z' hz' => (c • omega.form - θ).property.2 _ z' hz') hR hz
    have hPz : DifferentiableAt ℂ P z :=
      (hP.differentiableOn (by simp)).differentiableAt (e.ambient.isOpen.mem_nhds hz)
    have h0 := quad_nonneg_of_isStrictlyPositive (hpos B₀ le_rfl z hz) u
    rw [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      pullbackForm_apply_complexLine hPz] at h0
    have hs := hsemi φ (P z) (hmaps hz) (fderiv ℝ P z u)
    simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at hs
    rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, pullbackForm_apply_complexLine hPz,
      pullbackForm_apply_complexLine hPz, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have hmax : B₀ ≤ max B₀ B₁ := le_max_left _ _
    have hωnn : 0 ≤ omega.form.val.coeff φ (P z)
        ![fderiv ℝ P z u, Complex.I • fderiv ℝ P z u] :=
      quad_nonneg_of_isStrictlyPositive ((omega.isKahler.1 φ (P z) (hmaps hz)).2) _
    nlinarith [mul_nonneg (sub_nonneg.mpr hmax) hωnn]

variable (C hC) in
/-- The footnote's form: a Kähler form `ω̃` on `Ỹ` with `ω̃ ≥ (θ + ω)|_Ỹ`. -/
theorem exists_kahler_dominating_add [CompactSpace M] (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) :
    ∃ omt : SpaceForm (normalization C hC) 2, omt.IsKahler ∧
      omt.Dominates (restrictForm C hC (θ + omega.form).val) :=
  exists_kahler_dominating C hC omega (θ + omega.form)

end SGPT.Unibranch.KS2NormalizationKahler

end
