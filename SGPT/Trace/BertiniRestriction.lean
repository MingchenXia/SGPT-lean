import SGPT.Trace.BertiniSmooth
import SGPT.Trace.BertiniRestrictionChart
import SGPT.PSH.NativeQPSHPullback

/-!
# Generic restrictions of quasi-psh functions to members of a linear system

Source: `chapter_trace.tex`, Section "Analytic Bertini theorems", `cor:qpshgeneralres`:

> In the sequel of this section, we fix a base point free linear system `Λ` on `X`. [...]
> **Corollary.** Let `φ ∈ QPSH(X)`. Then for quasi-every `H ∈ Λ`, we have `φ|_H ≢ -∞`.

Here `X` is a connected compact complex manifold (the section assumes it projective; this is not
used), the base-point-free linear system is given by its morphism `p : X → ℙᴺ`, which is
nondegenerate (`IsNondegenerate p`: `p(X)` lies in no hyperplane, since `V → H⁰(X, L)` is
injective), `N ≥ 1`, and the members are `H ∩ X = p⁻¹(H_ℓ)`, `ℓ ∈ Λ = |𝒪_{ℙᴺ}(1)|`
(`rmk:trace:L787`). Blueprint: `claude-bertini:qpshgeneralres` (`blueprint/src/claude-bertini.tex`).

The book deduces the corollary from `thm:Bert` (whose multiplier-ideal clause is not formalized);
the proof here is direct, by slicing the incidence variety:

* `locallyPluripolar_poleInteriorSet`: the set of `ℓ` for which `φ ≡ -∞` on a nonempty open piece
  of `p⁻¹(H_ℓ)` around a smooth point is pluripolar: countably many slice charts
  (`SGPT.Trace.Bertini.exists_sliceChart`, second countability of `Λ × X`) and the product-slice
  lemma (`SliceChart.locallyPluripolar_image_badSet`);
* generic smoothness (`SGPT.Trace.Bertini.locallyPluripolar_singularMemberSet`) and nonemptiness of
  the members (`SGPT.Trace.Bertini.member_nonempty`).

Main results, for `φ ∈ QPSH(X)` (`(ofFixedModel n X).IsQPSH φ`, source `def:qpsh`):

* `coPluripolar_restriction_strong`: for quasi-every `ℓ`, `p⁻¹(H_ℓ)` is a nonempty smooth
  hypersurface and `φ` is not `-∞` on any nonempty relatively open subset of it;
* `coPluripolar_restriction_ne_bot` (source `cor:qpshgeneralres`, literal form): for quasi-every
  `ℓ`, `φ|_{p⁻¹(H_ℓ)} ≢ -∞`;
* `coPluripolar_isQPSH_restriction`: for quasi-every `ℓ`, `p⁻¹(H_ℓ)` is a smooth hypersurface and
  `φ|_{p⁻¹(H_ℓ)} ∈ QPSH(p⁻¹(H_ℓ))` on the `(n-1)`-dimensional manifold `p⁻¹(H_ℓ)` (equivalently,
  `φ|_H ≢ -∞` on every connected component of `H`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.Bertini

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending
  SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
  SGPT.PSH.VariableComplexAtlas

/-- Countable unions of pluripolar sets are pluripolar (source `prop:pluripolarunion`, for an
arbitrary countable index type). -/
theorem locallyPluripolar_iUnion_of_countable {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] {ι : Type*} [Countable ι]
    {S : ι → Set M} (h : ∀ i, (ofFixedModel k M).LocallyPluripolar (S i)) :
    (ofFixedModel k M).LocallyPluripolar (⋃ i, S i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [iUnion_of_empty]
    exact locallyPluripolar_of_in_chart (A := ofFixedModel k M)
      (fun e => manifoldLocallyPluripolar_empty (n := k) (M := M) e)
  · obtain ⟨f, hf⟩ := exists_surjective_nat ι
    rw [← hf.iUnion_comp S]
    exact LocallyPluripolar.iUnion fun j => h (f j)

theorem locallyPluripolar_union {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] {S T : Set M}
    (hS : (ofFixedModel k M).LocallyPluripolar S) (hT : (ofFixedModel k M).LocallyPluripolar T) :
    (ofFixedModel k M).LocallyPluripolar (S ∪ T) := by
  rw [union_eq_iUnion]
  exact locallyPluripolar_iUnion_of_countable fun b => by cases b <;> assumption

variable {N n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N)

variable (n) in
/-- The set of `ℓ ∈ Λ` for which `φ ≡ -∞` on a neighbourhood, in `p⁻¹(H_ℓ)`, of a point at which
`p⁻¹(H_ℓ)` is smooth. -/
def poleInteriorSet (φ : X → EReal) : Set (HyperplaneSpace N) :=
  {l | ∃ x ∈ member p l, ¬ IsSingularPointOfMember n p l x ∧
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W ∩ member p l, φ y = ⊥}

/-- **Slicing the incidence variety** (blueprint `claude-bertini:qpshgeneralres`, first part): if
`φ` is quasi-psh and not `-∞` on any nonempty open subset of `X`, the set of `ℓ` for which `φ ≡ -∞`
on a nonempty open piece of the smooth part of `p⁻¹(H_ℓ)` is pluripolar. -/
theorem locallyPluripolar_poleInteriorSet
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (hnd : LocallyNondegenerate φ) :
    (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (poleInteriorSet n p φ) := by
  let ι := {q : HyperplaneSpace N × X //
    q.2 ∈ member p q.1 ∧ ¬ IsSingularPointOfMember n p q.1 q.2}
  have hex : ∀ q : ι, ∃ c : SliceChart n p φ, q.1 ∈ c.domain :=
    fun q => exists_sliceChart p φ hp hφ q.2.1 q.2.2
  choose c hc using hex
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun q => (c q).domain)
    (fun q => (c q).isOpen_domain)
  have hTc' : Countable T := hTc.to_subtype
  set 𝓑 := TopologicalSpace.countableBasis (ComplexModel n) with h𝓑
  have h𝓑c : Countable 𝓑 := (TopologicalSpace.countable_countableBasis (ComplexModel n)).to_subtype
  let S : T × 𝓑 → Set (HyperplaneSpace N) :=
    fun i => (affineChart (c i.1.1).i).symm '' (c i.1.1).badSet i.2.1
  have hS : ∀ i, (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (S i) := fun i =>
    (c i.1.1).locallyPluripolar_image_badSet hp hnd
      (TopologicalSpace.isOpen_of_mem_countableBasis i.2.2)
  refine (locallyPluripolar_iUnion_of_countable hS).mono ?_
  rintro l ⟨x, hx, hns, W, hW, hxW, hpole⟩
  have hq : (l, x) ∈ ⋃ q : ι, (c q).domain := mem_iUnion.mpr ⟨⟨(l, x), hx, hns⟩, hc _⟩
  rw [← hTU] at hq
  obtain ⟨q, hqT, hqd⟩ := mem_iUnion₂.mp hq
  obtain ⟨B, hB, hlB⟩ := (c q).exists_mem_image_badSet hqd hx hW hxW hpole
  exact mem_iUnion.mpr ⟨(⟨q, hqT⟩, ⟨B, hB⟩), hlB⟩

/-- A function in `QPSH(X)` (source `def:qpsh`) is quasi-psh in every chart. -/
theorem IsQPSH.manifoldQuasiPlurisubharmonic' {φ : X → EReal}
    (hφ : (ofFixedModel n X).IsQPSH φ) : ManifoldQuasiPlurisubharmonic (n := n) φ := by
  obtain ⟨θ, hθ⟩ := hφ
  exact ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hθ).quasiPshPotential.1

variable [CompactSpace X]

/-- **Source `cor:qpshgeneralres`, strong form.** Let `X` be a compact connected complex manifold,
`p : X → ℙᴺ` (`N ≥ 1`) the morphism of a base-point-free linear system (nondegenerate) and
`φ ∈ QPSH(X)`. For quasi-every `ℓ ∈ Λ = |𝒪_{ℙᴺ}(1)|`, the member `p⁻¹(H_ℓ)` is a nonempty smooth
hypersurface and `φ` is not identically `-∞` on any nonempty relatively open subset of it. -/
theorem coPluripolar_restriction_strong [ConnectedSpace X]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (hnd : IsNondegenerate p)
    (hN : 1 ≤ N) {φ : X → EReal} (hφ : (ofFixedModel n X).IsQPSH φ) :
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | IsSmoothHypersurfaceMember n p l ∧ (member p l).Nonempty ∧
        ∀ W : Set X, IsOpen W → (W ∩ member p l).Nonempty → ∃ y ∈ W ∩ member p l, φ y ≠ ⊥} := by
  refine (locallyPluripolar_union (locallyPluripolar_singularMemberSet p hp hN)
    (locallyPluripolar_poleInteriorSet p hp (IsQPSH.manifoldQuasiPlurisubharmonic' hφ)
      hφ.locallyNondegenerate)).mono ?_
  intro l hl
  simp only [mem_compl_iff, mem_ofPred_eq, not_and, not_forall, not_exists, not_not] at hl
  by_cases hsm : IsSmoothHypersurfaceMember n p l
  · right
    obtain ⟨W, hW, ⟨x, hxW, hx⟩, hpole⟩ := hl hsm (member_nonempty p hp hnd hN l)
    exact ⟨x, hx, (isSmoothHypersurfaceMember_iff p hp l).mp hsm x, W, hW, hxW,
      fun y hy => hpole y hy⟩
  · exact Or.inl hsm

/-- **Source `cor:qpshgeneralres`.** Let `φ ∈ QPSH(X)`. Then for quasi-every member `H = p⁻¹(H_ℓ)`
of the base-point-free linear system `Λ`, `φ|_H ≢ -∞`. -/
theorem coPluripolar_restriction_ne_bot [ConnectedSpace X]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (hnd : IsNondegenerate p)
    (hN : 1 ≤ N) {φ : X → EReal} (hφ : (ofFixedModel n X).IsQPSH φ) :
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar {l | ∃ x ∈ member p l, φ x ≠ ⊥} := by
  refine LocallyPluripolar.mono (coPluripolar_restriction_strong p hp hnd hN hφ) ?_
  rintro l hl ⟨-, hne, hW⟩
  obtain ⟨y, hy, hφy⟩ := hW univ isOpen_univ (by simpa using hne)
  exact hl ⟨y, hy.2, hφy⟩

/-- **Source `cor:qpshgeneralres`, restriction form.** For quasi-every `ℓ ∈ Λ`, the member
`H = p⁻¹(H_ℓ)` is a smooth hypersurface and the restriction `φ|_H` belongs to `QPSH(H)` (source
`def:qpsh` on the `(n - 1)`-dimensional complex manifold `H`, with the complex structure of a
closed submanifold of `X`); equivalently, `φ|_H ≢ -∞` on every connected component of `H`. -/
theorem coPluripolar_isQPSH_restriction [ConnectedSpace X]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (hnd : IsNondegenerate p)
    (hN : 1 ≤ N) {φ : X → EReal} (hφ : (ofFixedModel n X).IsQPSH φ) :
    (ofFixedModel N (HyperplaneSpace N)).CoPluripolar
      {l | ∃ hl : IsSmoothHypersurfaceMember n p l,
        letI := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le n 1)
          (fun _ hx => regularAtDim_member p hp hl hx)
        haveI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.sub_le n 1)
          (fun _ hx => regularAtDim_member p hp hl hx)
        (ofFixedModel (n - 1) (member p l)).IsQPSH (fun y : member p l => φ y.1)} := by
  refine LocallyPluripolar.mono (coPluripolar_restriction_strong p hp hnd hN hφ) ?_
  rintro l hl ⟨hsm, -, hW⟩
  apply hl
  refine ⟨hsm, ?_⟩
  have hreg : ∀ x ∈ member p l, RegularAtDim (n := n) (member p l) x (n - 1) :=
    fun _ hx => regularAtDim_member p hp hsm hx
  let := SubmanifoldChartedSpace.chartedSpace (Nat.sub_le n 1) hreg
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.sub_le n 1) hreg
  have : LocallyConnectedSpace (member p l) :=
    ChartedSpace.locallyConnectedSpace (ComplexModel (n - 1)) (member p l)
  have hval := SubmanifoldChartedSpace.contMDiff_val (Nat.sub_le n 1) hreg
  refine (IsQPSH.comp_native_holomorphic_iff hφ hval).mpr fun x => ?_
  obtain ⟨W, hWo, hWc⟩ := isOpen_induced_iff.mp (isOpen_connectedComponent (x := x))
  have hxW : x.1 ∈ W := by
    have : x ∈ Subtype.val ⁻¹' W := hWc ▸ mem_connectedComponent
    exact this
  obtain ⟨y, hy, hφy⟩ := hW W hWo ⟨x.1, hxW, x.2⟩
  refine ⟨⟨y, hy.2⟩, ?_, hφy⟩
  rw [← hWc]
  exact hy.1

/-- Non-vacuity of the hypotheses: the identity of `ℙᴺ` is nondegenerate (the linear system
`|𝒪_{ℙᴺ}(1)|` is base-point free): the point `[ℓ̄]` does not lie on `H_ℓ`, as
`⟨ℓ, ℓ̄⟩ = ∑ |ℓᵢ|² ≠ 0`. -/
theorem isNondegenerate_id :
    IsNondegenerate (id : ComplexProjectiveSpace N → ComplexProjectiveSpace N) := by
  intro l
  have hne : star l.rep ≠ 0 := fun h => l.rep_ne_zero (star_eq_zero.mp h)
  refine ⟨mk (star l.rep) hne, fun hmem => ?_⟩
  have h := (mem_hyperplane_mk_iff l hne).mp hmem
  have hsum : ∑ i, ((‖l.rep i‖ ^ 2 : ℝ) : ℂ) = 0 := by
    rw [← h, pairing]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
  have hsum' : ∑ i, ‖l.rep i‖ ^ 2 = 0 := by exact_mod_cast hsum
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖l.rep i‖).mp hsum'
  exact l.rep_ne_zero (funext fun i => by simpa using hzero i (Finset.mem_univ i))

end SGPT.Trace.Bertini
