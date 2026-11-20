import SGPT.Trace.BertiniSetting
import SGPT.Foundations.Analysis.Pending.DerivativeIdeal
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.RankDegeneracy

/-!
# The conormal set of a linear system

Source: `chapter_trace.tex`, Section "Analytic Bertini theorems" (Step 1.1 of the proof of
`thm:Bert`: the general member of a base-point-free linear system is smooth). Blueprint:
`claude-bertini:conormal`, `claude-bertini:conormal-analytic`, `claude-bertini:conormal-rank`
(`blueprint/src/claude-bertini.tex`) and `blueprint/src/claude-bertini-bc.tex`.

Let `p : X → ℙᴺ` be holomorphic. This file contains the coordinate algebra of the local equations
`s_{ℓ,j} = memberEquation p ℓ j` of the members `p⁻¹(H_ℓ)`:

* `affineLift_affineChart_eq_smul`, `hyperplaneEquation_eq_mul`: changing the affine chart `U_j`
  of `ℙᴺ` multiplies the local equation by the nowhere vanishing function `Z_k/Z_j`;
* `rep_eq_smul_affineLift`: the chosen homogeneous representative of `ℓ ∈ U_i` is a nonzero
  multiple of the normalized representative `insertNth i 1 (affineChart i ℓ)`;
* `chartDeriv_memberEquation_eq_zero`: at a point of `p⁻¹(H_ℓ)`, the vanishing of all partial
  derivatives of the local equation does not depend on the chart of `X` nor on the chart of `ℙᴺ`
  (chain rule and product rule);
* `isSmoothHypersurfaceMember_iff`: `p⁻¹(H_ℓ)` is a smooth hypersurface iff at every point the
  local equation in the preferred charts has a nonzero differential.

It then studies the **conormal set** `C = conormalSet n p ⊆ Λ × X` (the pairs `(ℓ, x)` such that
`p⁻¹(H_ℓ)` is singular at `x`), with `Λ × X` the product complex manifold modelled on `ℂ^{N+n}`
(`SGPT.Foundations.Analysis.Pending.ProductComplexManifold`):

* `image_fst_conormalSet`: `pr₁(C)` is the set of hyperplanes with a singular member;
* `isComplexAnalyticSubset_conormalSet`: in the product chart `U_i × e`, `C` is the common zero set
  of the local equation `G(ζ, z) = ⟨insertNth i 1 ζ, chartLift z⟩` of the incidence variety and of
  its `n` partial derivatives in `z` (`conormalGenerator`, `conormalGenerator_prodChart_iff`);
* `rankAt_fst_le` (the **conormal rank bound**): at every point of a subset `A ⊆ C`, the image of
  the tangent space of `A` under `d pr₁` has dimension `≤ N - 1`, because `dG = λ ∘ d pr₁` there with
  `λ ≠ 0` (`hasFDerivAt_conormalGenerator_zero`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.Bertini

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

variable {N : ℕ}

/-! ### Coordinate algebra -/

theorem pairing_comm (l v : Fin (N + 1) → ℂ) : pairing l v = pairing v l := by
  simp only [pairing, mul_comm]

/-- `⟨insertNth i 1 ζ, v⟩ = v_i + ∑ₖ ζₖ v_{i.succAbove k}`. -/
theorem pairing_affineLift_left (i : Fin (N + 1)) (ζ : ComplexModel N) (v : Fin (N + 1) → ℂ) :
    pairing (affineLift i ζ) v = v i + ∑ k : Fin N, v (i.succAbove k) * ζ k := by
  rw [pairing_comm, pairing_affineLift]

/-- On `U_i`, the chosen homogeneous representative is `ℓ_i • insertNth i 1 (affineChart i ℓ)`. -/
theorem rep_eq_smul_affineLift (i : Fin (N + 1)) {l : ComplexProjectiveSpace N}
    (hl : l ∈ (affineChart i).source) :
    l.rep = l.rep i • affineLift i (affineChart i l) := by
  have hli : l.rep i ≠ 0 := (mem_affineChart_source_iff i l).mp hl
  have h1 : affineChart i l = affineRatio i l.rep := by
    conv_lhs => rw [← mk_rep l]
    exact affineChart_mk i l.rep_ne_zero hli
  rw [h1, affineLift_affineRatio i hli, smul_smul, mul_inv_cancel₀ hli, one_smul]

/-- On `U_j ∩ U_k`, `insertNth k 1 (affineChart k z) = (Z_k/Z_j)⁻¹ • insertNth j 1 (affineChart j z)`. -/
theorem affineLift_affineChart_eq_smul {j k : Fin (N + 1)} {z : ComplexProjectiveSpace N}
    (hj : z ∈ (affineChart j).source) (hk : z ∈ (affineChart k).source) :
    affineLift k (affineChart k z) =
      (affineLift j (affineChart j z) k)⁻¹ • affineLift j (affineChart j z) := by
  set v := affineLift j (affineChart j z) with hv
  have hz : z = mk v (affineLift_ne_zero j _) := eq_mk_affineLift_affineChart j hj
  have hvk : v k ≠ 0 := by
    have := hk
    rw [hz] at this
    exact (mk_mem_affineChart_source_iff k _).mp this
  have h1 : affineChart k z = affineRatio k v := by
    rw [hz]
    exact affineChart_mk k _ hvk
  rw [h1, affineLift_affineRatio k hvk]

/-- On `U_j ∩ U_k`, the `k`-th coordinate of `insertNth j 1 (affineChart j z)` is nonzero. -/
theorem affineLift_affineChart_apply_ne_zero {j k : Fin (N + 1)} {z : ComplexProjectiveSpace N}
    (hj : z ∈ (affineChart j).source) (hk : z ∈ (affineChart k).source) :
    affineLift j (affineChart j z) k ≠ 0 := by
  have hz : z = mk (affineLift j (affineChart j z)) (affineLift_ne_zero j _) :=
    eq_mk_affineLift_affineChart j hj
  rw [hz] at hk
  exact (mk_mem_affineChart_source_iff k _).mp hk

/-- Change of the affine chart of `ℙᴺ`: `g_j = (Z_k/Z_j) g_k` on `U_j ∩ U_k`. -/
theorem hyperplaneEquation_eq_mul (l : HyperplaneSpace N) {j k : Fin (N + 1)}
    {z : ComplexProjectiveSpace N} (hj : z ∈ (affineChart j).source)
    (hk : z ∈ (affineChart k).source) :
    hyperplaneEquation l j z = affineLift j (affineChart j z) k * hyperplaneEquation l k z := by
  have hne := affineLift_affineChart_apply_ne_zero hj hk
  simp only [hyperplaneEquation]
  rw [affineLift_affineChart_eq_smul hj hk, pairing_smul_right, ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]

/-- At a zero of the affine equation, some linear coefficient `v_{i.succAbove k}` of the
homogeneous vector `v ≠ 0` is nonzero (the vector form of
`exists_coeff_ne_zero_of_pairing_affineLift_eq_zero`). -/
theorem exists_succAbove_ne_zero_of_pairing_eq_zero {v : Fin (N + 1) → ℂ} (hv : v ≠ 0)
    {i : Fin (N + 1)} {ζ : ComplexModel N} (h : pairing (affineLift i ζ) v = 0) :
    ∃ k : Fin N, v (i.succAbove k) ≠ 0 := by
  rw [pairing_comm] at h
  exact exists_coeff_ne_zero_of_pairing_affineLift_eq_zero hv h

/-! ### Independence of the charts -/

section Member

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N)

open DerivativeIdeal

omit [IsComplexManifold n X] in
/-- The homogeneous coordinates `x ↦ (Z_m/Z_j)(p x)` are holomorphic on `p⁻¹(U_j)`. -/
theorem holomorphicAt_affineLift_affineChart_comp
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (j m : Fin (N + 1)) {x : X}
    (hx : p x ∈ (affineChart j).source) :
    HolomorphicAt n (fun y => affineLift j (affineChart j (p y)) m) x := by
  have hU : IsOpen (p ⁻¹' (affineChart j).source) :=
    (affineChart j).open_source.preimage hp.continuous
  filter_upwards [hU.mem_nhds hx] with y hy
  have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N)
      (fun y => affineChart j (p y)) y :=
    ((contMDiffAt_affineChart j hy).comp y hp.contMDiffAt).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ℂ)
      (fun w : ComplexModel N => affineLift j w m) (affineChart j (p y)) :=
    (differentiable_affineLift_apply j m _).mdifferentiableAt
  exact MDifferentiableAt.comp (g := fun w : ComplexModel N => affineLift j w m) y h2 h1

/-- **Chart independence of the singular points of a member.** At a point `x` of `p⁻¹(H_ℓ)`, if all
partial derivatives of the local equation `s_{ℓ,j}` in the chart `e` of `X` vanish, then all
partial derivatives of `s_{ℓ,k}` in any other chart `e'` vanish: the chain rule changes `e`, and
`s_{ℓ,j} = (Z_k/Z_j) s_{ℓ,k}` with `s_{ℓ,k}(x) = 0` changes `j`. -/
theorem chartDeriv_memberEquation_eq_zero
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (l : HyperplaneSpace N)
    {x : X} (hx : x ∈ member p l) {j k : Fin (N + 1)} (hj : p x ∈ (affineChart j).source)
    (hk : p x ∈ (affineChart k).source) {e e' : ComplexChart n X} (he : x ∈ e.val.source)
    (he' : x ∈ e'.val.source) (h : ∀ v, chartDeriv e v (memberEquation p l j) x = 0)
    (v : ComplexModel n) : chartDeriv e' v (memberEquation p l k) x = 0 := by
  have h' : ∀ w, chartDeriv e' w (memberEquation p l j) x = 0 := by
    intro w
    have := (chartDeriv_eventuallyEq_sum e e' (v := w) he he'
      (holomorphicAt_memberEquation p hp l j hj)).self_of_nhds
    rw [this]
    simp [h]
  set u : X → ℂ := fun y => affineLift j (affineChart j (p y)) k with hu
  have hUjk : IsOpen (p ⁻¹' ((affineChart j).source ∩ (affineChart k).source)) :=
    ((affineChart j).open_source.inter (affineChart k).open_source).preimage hp.continuous
  have hjk : memberEquation p l j =ᶠ[𝓝 x] fun y =>
      ∑ i : Fin 1, (fun _ => u) i y * (fun _ => memberEquation p l k) i y := by
    filter_upwards [hUjk.mem_nhds ⟨hj, hk⟩] with y hy
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, memberEquation, u]
    exact hyperplaneEquation_eq_mul l hy.1 hy.2
  have hprod := (chartDeriv_eventuallyEq_sum_mul (v := v) he'
    (fun _ => holomorphicAt_affineLift_affineChart_comp p hp j k hj)
    (fun _ => holomorphicAt_memberEquation p hp l k hk) hjk).self_of_nhds
  have hsk : memberEquation p l k x = 0 := (mem_member_iff_memberEquation p l k hk).mp hx
  rw [h' v] at hprod
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, hsk, mul_zero,
    zero_add] at hprod
  have hux : u x ≠ 0 := affineLift_affineChart_apply_ne_zero hj hk
  exact (mul_eq_zero.mp hprod.symm).resolve_left hux

variable (n) in
/-- `p⁻¹(H_ℓ)` is singular at `x`: `x ∈ p⁻¹(H_ℓ)` and the local equation in the preferred charts
(`U_{chartIndex (p x)}` of `ℙᴺ`, the preferred chart of `X` at `x`) has vanishing differential. -/
def IsSingularPointOfMember (l : HyperplaneSpace N) (x : X) : Prop :=
  x ∈ member p l ∧ ∀ v, chartDeriv (complexChartAt (n := n) x) v
    (memberEquation p l (chartIndex (p x))) x = 0

/-- A member is a smooth hypersurface iff it has no singular point. -/
theorem isSmoothHypersurfaceMember_iff
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (l : HyperplaneSpace N) :
    IsSmoothHypersurfaceMember n p l ↔ ∀ x, ¬ IsSingularPointOfMember n p l x := by
  constructor
  · rintro hl x ⟨hx, hsing⟩
    obtain ⟨e, v, he, hv⟩ := hl x hx (chartIndex (p x)) (mem_affineChart_chartIndex (p x))
    exact hv (chartDeriv_memberEquation_eq_zero p hp l hx (mem_affineChart_chartIndex (p x))
      (mem_affineChart_chartIndex (p x)) (mem_complexChartAt_source x) he hsing v)
  · intro hl x hx j hj
    by_contra hcon
    push Not at hcon
    refine hl x ⟨hx, fun v => ?_⟩
    have h0 : ∀ v, chartDeriv (complexChartAt (n := n) x) v (memberEquation p l j) x = 0 :=
      fun v => hcon _ v (mem_complexChartAt_source x)
    exact chartDeriv_memberEquation_eq_zero p hp l hx hj (mem_affineChart_chartIndex (p x))
      (mem_complexChartAt_source x) (mem_complexChartAt_source x) h0 v

end Member

/-! ### The homogeneous lift of `p` in a chart of `X` -/

section Lift

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N)

open DerivativeIdeal

/-- The homogeneous lift `z ↦ insertNth j 1 (affineChart j (p (e⁻¹ z)))` of `p` read in the chart
`e` of `X` and the chart `U_j` of `ℙᴺ`. -/
def chartLift (e : ComplexChart n X) (j : Fin (N + 1)) (z : ComplexModel n) : Fin (N + 1) → ℂ :=
  affineLift j (affineChart j (p (e.val.symm z)))

/-- The open set of `z ∈ e(e.source)` with `p(e⁻¹ z) ∈ U_j`, where `chartLift p e j` is holomorphic. -/
def chartLiftDomain (e : ComplexChart n X) (j : Fin (N + 1)) : Set (ComplexModel n) :=
  e.val.target ∩ e.val.symm ⁻¹' (p ⁻¹' (affineChart j).source)

omit [IsComplexManifold n X] in
theorem isOpen_chartLiftDomain (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (e : ComplexChart n X) (j : Fin (N + 1)) : IsOpen (chartLiftDomain p e j) :=
  e.val.isOpen_inter_preimage_symm ((affineChart j).open_source.preimage hp.continuous)

omit [IsComplexManifold n X] in
theorem mem_chartLiftDomain_iff {e : ComplexChart n X} {j : Fin (N + 1)} {x : X}
    (hx : x ∈ e.val.source) :
    e.val x ∈ chartLiftDomain p e j ↔ p x ∈ (affineChart j).source := by
  simp only [chartLiftDomain, mem_inter_iff, mem_preimage, e.val.left_inv hx,
    e.val.map_source hx, true_and]

omit [IsComplexManifold n X] in
theorem chartLift_chart {e : ComplexChart n X} {j : Fin (N + 1)} {x : X} (hx : x ∈ e.val.source) :
    chartLift p e j (e.val x) = affineLift j (affineChart j (p x)) := by
  simp only [chartLift, e.val.left_inv hx]

omit [IsComplexManifold n X] in
/-- The local equation of the member read in a chart: `s_{ℓ,j} ∘ e⁻¹ = ⟨ℓ, chartLift⟩`. -/
theorem memberEquation_comp_symm (e : ComplexChart n X) (l : HyperplaneSpace N) (j : Fin (N + 1)) :
    memberEquation p l j ∘ e.val.symm = fun z => pairing l.rep (chartLift p e j z) := rfl

theorem differentiableAt_chartLift_apply
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) {e : ComplexChart n X}
    {j : Fin (N + 1)} {z : ComplexModel n} (hz : z ∈ chartLiftDomain p e j) (m : Fin (N + 1)) :
    DifferentiableAt ℂ (fun z => chartLift p e j z m) z := by
  have hx : e.val.symm z ∈ e.val.source := e.val.map_target hz.1
  have h := (eventually_differentiableAt_comp_symm e hx
    (holomorphicAt_affineLift_affineChart_comp p hp j m hz.2)).self_of_nhds
  rw [e.val.right_inv hz.1] at h
  exact h

theorem differentiableOn_chartLift_apply
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (e : ComplexChart n X)
    (j m : Fin (N + 1)) :
    DifferentiableOn ℂ (fun z => chartLift p e j z m) (chartLiftDomain p e j) :=
  fun _ hz => (differentiableAt_chartLift_apply p hp hz m).differentiableWithinAt

/-- The partial derivatives `∂_v (chartLift)` of the homogeneous lift. -/
def chartLiftDeriv (e : ComplexChart n X) (j : Fin (N + 1)) (z v : ComplexModel n) :
    Fin (N + 1) → ℂ :=
  fun m => fderiv ℂ (fun z => chartLift p e j z m) z v

theorem differentiableOn_chartLiftDeriv_apply
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (e : ComplexChart n X)
    (j : Fin (N + 1)) (v : ComplexModel n) (m : Fin (N + 1)) :
    DifferentiableOn ℂ (fun z => chartLiftDeriv p e j z v m) (chartLiftDomain p e j) :=
  FirstPass.differentiableOn_fderiv_apply_of_isOpen (differentiableOn_chartLift_apply p hp e j m)
    (isOpen_chartLiftDomain p hp e j) v

/-- `∂_v ⟨l, chartLift⟩ = ⟨l, ∂_v chartLift⟩`. -/
theorem hasFDerivAt_pairing_chartLift
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) {e : ComplexChart n X}
    {j : Fin (N + 1)} {z : ComplexModel n} (hz : z ∈ chartLiftDomain p e j)
    (l : Fin (N + 1) → ℂ) :
    HasFDerivAt (fun z => pairing l (chartLift p e j z))
      (∑ m : Fin (N + 1), l m • fderiv ℂ (fun z => chartLift p e j z m) z) z := by
  simp only [pairing]
  exact HasFDerivAt.fun_sum fun m _ =>
    ((differentiableAt_chartLift_apply p hp hz m).hasFDerivAt.const_mul (l m))

theorem fderiv_pairing_chartLift_apply
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) {e : ComplexChart n X}
    {j : Fin (N + 1)} {z : ComplexModel n} (hz : z ∈ chartLiftDomain p e j)
    (l : Fin (N + 1) → ℂ) (v : ComplexModel n) :
    fderiv ℂ (fun z => pairing l (chartLift p e j z)) z v = pairing l (chartLiftDeriv p e j z v) := by
  rw [(hasFDerivAt_pairing_chartLift p hp hz l).fderiv]
  simp [pairing, chartLiftDeriv]

omit [IsComplexManifold n X] in
/-- The partial derivatives in the direction `v` are combinations of the coordinate ones. -/
theorem chartLiftDeriv_eq_sum (e : ComplexChart n X) (j : Fin (N + 1)) (z v : ComplexModel n) :
    chartLiftDeriv p e j z v =
      ∑ m : Fin n, v m • chartLiftDeriv p e j z (EuclideanSpace.single m 1) := by
  funext k
  simp only [chartLiftDeriv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  conv_lhs => rw [← DerivativeIdeal.sum_smul_single v]
  rw [map_sum]
  simp [map_smul, smul_eq_mul]

end Lift

/-! ### The conormal set in `Λ × X` -/

section Conormal

open scoped ProductComplexManifold
open ProductComplexManifold DerivativeIdeal

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N)

variable (n) in
/-- The **conormal set** `C = {(ℓ, x) ∈ Λ × X : p⁻¹(H_ℓ) is singular at x}` (blueprint
`claude-bertini:conormal`). -/
def conormalSet : Set (HyperplaneSpace N × X) := {q | IsSingularPointOfMember n p q.1 q.2}

/-- The hyperplanes with a singular member are the image of the conormal set. -/
theorem image_fst_conormalSet (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) :
    Prod.fst '' conormalSet n p = {l | ¬ IsSmoothHypersurfaceMember n p l} := by
  ext l
  simp only [mem_image, Set.mem_ofPred_eq, isSmoothHypersurfaceMember_iff p hp, not_forall,
    not_not]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩
  · rintro ⟨x, hx⟩
    exact ⟨(l, x), hx, rfl⟩

/-- `⟨l, ∑ₘ cₘ wₘ⟩ = ∑ₘ cₘ ⟨l, wₘ⟩`. -/
theorem pairing_sum_smul_right {ι : Type*} (s : Finset ι) (l : Fin (N + 1) → ℂ) (c : ι → ℂ)
    (w : ι → Fin (N + 1) → ℂ) :
    pairing l (∑ m ∈ s, c m • w m) = ∑ m ∈ s, c m * pairing l (w m) := by
  simp only [pairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The generators of the conormal set in the product chart `U_i × e`: the local equation
`⟨insertNth i 1 ζ, chartLift z⟩` of the incidence variety and its partial derivatives in `z`. -/
def conormalGenerator (i : Fin (N + 1)) (e : ComplexChart n X) (j : Fin (N + 1)) :
    Fin (n + 1) → ComplexModel (N + n) → ℂ :=
  Fin.cons (fun w => pairing (affineLift i ((prodModelEquiv N n).symm w).1)
      (chartLift p e j ((prodModelEquiv N n).symm w).2))
    (fun m w => pairing (affineLift i ((prodModelEquiv N n).symm w).1)
      (chartLiftDeriv p e j ((prodModelEquiv N n).symm w).2 (EuclideanSpace.single m 1)))

/-- The coordinate neighbourhood of the generators. -/
def conormalDomain (e : ComplexChart n X) (j : Fin (N + 1)) : Set (ComplexModel (N + n)) :=
  (prodModelEquiv N n).symm ⁻¹' (univ ×ˢ chartLiftDomain p e j)

omit [IsComplexManifold n X] in
theorem isOpen_conormalDomain (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (e : ComplexChart n X) (j : Fin (N + 1)) : IsOpen (conormalDomain p e j) :=
  (isOpen_univ.prod (isOpen_chartLiftDomain p hp e j)).preimage (prodModelEquiv N n).symm.continuous

omit [IsComplexManifold n X] in
theorem conormalDomain_subset_target (i : Fin (N + 1)) (e : ComplexChart n X) (j : Fin (N + 1)) :
    conormalDomain p e j ⊆ (prodChart (affineChart i) e.val).target := by
  intro w hw
  rw [prodChart_target]
  exact ⟨by simp, hw.2.1⟩

omit [IsComplexManifold n X] in
theorem prodChart_mem_conormalDomain_iff {i j : Fin (N + 1)} {e : ComplexChart n X}
    {q : HyperplaneSpace N × X} (hq : q.2 ∈ e.val.source) :
    prodChart (affineChart i) e.val q ∈ conormalDomain p e j ↔ p q.2 ∈ (affineChart j).source := by
  simp only [conormalDomain, mem_preimage, prodChart_apply, ContinuousLinearEquiv.symm_apply_apply,
    mem_prod, mem_univ, true_and]
  exact mem_chartLiftDomain_iff p hq

/-- A pairing of the affine lift of the first coordinate with a holomorphic vector of the second
is holomorphic on `ℂᴺ × S`. -/
theorem differentiableOn_pairing_affineLift_comp (i : Fin (N + 1))
    {R : ComplexModel n → Fin (N + 1) → ℂ} {S : Set (ComplexModel n)}
    (hR : ∀ m, DifferentiableOn ℂ (fun z => R z m) S) :
    DifferentiableOn ℂ (fun w => pairing (affineLift i ((prodModelEquiv N n).symm w).1)
      (R ((prodModelEquiv N n).symm w).2)) ((prodModelEquiv N n).symm ⁻¹' (univ ×ˢ S)) := by
  intro w hw
  simp only [pairing]
  refine DifferentiableWithinAt.fun_sum fun m _ => DifferentiableWithinAt.mul ?_ ?_
  · have h1 : Differentiable ℂ (fun w : ComplexModel (N + n) => ((prodModelEquiv N n).symm w).1) :=
      differentiable_fst.comp (prodModelEquiv N n).symm.differentiable
    exact ((differentiable_affineLift_apply i m).comp h1).differentiableAt.differentiableWithinAt
  · have h2 : Differentiable ℂ (fun w : ComplexModel (N + n) => ((prodModelEquiv N n).symm w).2) :=
      differentiable_snd.comp (prodModelEquiv N n).symm.differentiable
    exact DifferentiableWithinAt.comp (g := fun z => R z m) w (hR m _ hw.2)
      (h2 w).differentiableWithinAt (fun w' hw' => hw'.2)

theorem differentiableOn_conormalGenerator
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (i : Fin (N + 1))
    (e : ComplexChart n X) (j : Fin (N + 1)) (k : Fin (n + 1)) :
    DifferentiableOn ℂ (conormalGenerator p i e j k) (conormalDomain p e j) := by
  refine Fin.cases ?_ (fun m => ?_) k
  · simp only [conormalGenerator, Fin.cons_zero]
    exact differentiableOn_pairing_affineLift_comp i (differentiableOn_chartLift_apply p hp e j)
  · simp only [conormalGenerator, Fin.cons_succ]
    exact differentiableOn_pairing_affineLift_comp i
      (differentiableOn_chartLiftDeriv_apply p hp e j (EuclideanSpace.single m 1))

/-- **The zero locus of the generators** is the conormal set, in the product chart `U_i × e`
with `p(x) ∈ U_j`. -/
theorem conormalGenerator_prodChart_iff
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) {i j : Fin (N + 1)}
    {e : ComplexChart n X} {q : HyperplaneSpace N × X} (hq1 : q.1 ∈ (affineChart i).source)
    (hq2 : q.2 ∈ e.val.source) (hqj : p q.2 ∈ (affineChart j).source) :
    (∀ k, conormalGenerator p i e j k (prodChart (affineChart i) e.val q) = 0) ↔
      IsSingularPointOfMember n p q.1 q.2 := by
  have hL : (prodModelEquiv N n).symm (prodChart (affineChart i) e.val q) =
      (affineChart i q.1, e.val q.2) := by
    simp [prodChart_apply]
  set ζ := affineChart i q.1 with hζ
  set c := q.1.rep i with hcdef
  have hc : c ≠ 0 := (mem_affineChart_source_iff i q.1).mp hq1
  have hrep : q.1.rep = c • affineLift i ζ := rep_eq_smul_affineLift i hq1
  have hz : e.val q.2 ∈ chartLiftDomain p e j := (mem_chartLiftDomain_iff p hq2).mpr hqj
  have h0 : memberEquation p q.1 j q.2 =
      c * pairing (affineLift i ζ) (chartLift p e j (e.val q.2)) := by
    rw [chartLift_chart p hq2]
    simp only [memberEquation, hyperplaneEquation, hrep, pairing_smul_left]
  have hd : ∀ v, chartDeriv e v (memberEquation p q.1 j) q.2 =
      c * pairing (affineLift i ζ) (chartLiftDeriv p e j (e.val q.2) v) := by
    intro v
    rw [chartDeriv, memberEquation_comp_symm, fderiv_pairing_chartLift_apply p hp hz, hrep,
      pairing_smul_left]
  have hgen0 : conormalGenerator p i e j 0 (prodChart (affineChart i) e.val q) =
      pairing (affineLift i ζ) (chartLift p e j (e.val q.2)) := by
    simp only [conormalGenerator, Fin.cons_zero, hL]
  have hgen : ∀ m : Fin n, conormalGenerator p i e j m.succ (prodChart (affineChart i) e.val q) =
      pairing (affineLift i ζ) (chartLiftDeriv p e j (e.val q.2) (EuclideanSpace.single m 1)) := by
    intro m
    simp only [conormalGenerator, Fin.cons_succ, hL]
  rw [Fin.forall_fin_succ, hgen0]
  simp only [hgen]
  have hmem : q.2 ∈ member p q.1 ↔ pairing (affineLift i ζ) (chartLift p e j (e.val q.2)) = 0 := by
    rw [mem_member_iff_memberEquation p q.1 j hqj, h0]
    exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hc, fun h => by rw [h, mul_zero]⟩
  constructor
  · rintro ⟨hm0, hm⟩
    have hx : q.2 ∈ member p q.1 := hmem.mpr hm0
    refine ⟨hx, fun v => ?_⟩
    refine chartDeriv_memberEquation_eq_zero p hp q.1 hx hqj (mem_affineChart_chartIndex (p q.2))
      hq2 (mem_complexChartAt_source q.2) (fun v => ?_) v
    rw [hd, chartLiftDeriv_eq_sum, pairing_sum_smul_right]
    simp [hm]
  · rintro ⟨hx, hsing⟩
    refine ⟨hmem.mp hx, fun m => ?_⟩
    have h1 := chartDeriv_memberEquation_eq_zero p hp q.1 hx (mem_affineChart_chartIndex (p q.2))
      hqj (mem_complexChartAt_source q.2) hq2 hsing (EuclideanSpace.single m 1)
    rw [hd] at h1
    exact (mul_eq_zero.mp h1).resolve_left hc

omit [IsComplexManifold n X] in
/-- The first generator vanishes exactly on the incidence variety `{(ℓ, x) : x ∈ p⁻¹(H_ℓ)}`. -/
theorem conormalGenerator_zero_prodChart_eq_zero_iff {i j : Fin (N + 1)} {e : ComplexChart n X}
    {q : HyperplaneSpace N × X} (hq1 : q.1 ∈ (affineChart i).source) (hq2 : q.2 ∈ e.val.source)
    (hqj : p q.2 ∈ (affineChart j).source) :
    conormalGenerator p i e j 0 (prodChart (affineChart i) e.val q) = 0 ↔ q.2 ∈ member p q.1 := by
  have hL : (prodModelEquiv N n).symm (prodChart (affineChart i) e.val q) =
      (affineChart i q.1, e.val q.2) := by
    simp [prodChart_apply]
  have hc : q.1.rep i ≠ 0 := (mem_affineChart_source_iff i q.1).mp hq1
  have hrep : q.1.rep = q.1.rep i • affineLift i (affineChart i q.1) := rep_eq_smul_affineLift i hq1
  have h0 : memberEquation p q.1 j q.2 =
      q.1.rep i * pairing (affineLift i (affineChart i q.1)) (chartLift p e j (e.val q.2)) := by
    rw [chartLift_chart p hq2]
    conv_lhs => rw [memberEquation, hyperplaneEquation, hrep, pairing_smul_left]
  rw [mem_member_iff_memberEquation p q.1 j hqj, h0]
  simp only [conormalGenerator, Fin.cons_zero, hL]
  exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_eq_zero.mp h).resolve_left hc⟩

omit [IsComplexManifold n X] in
/-- The preferred chart of `Λ × X` at `y` is the product of the affine chart `U_{chartIndex y.1}`
and the preferred chart of `X` at `y.2`. -/
theorem complexChartAt_prod_val (y : HyperplaneSpace N × X) :
    (complexChartAt (n := N + n) y).val =
      prodChart (affineChart (chartIndex y.1)) (complexChartAt (n := n) y.2).val := rfl

/-- **The conormal set is analytic** (blueprint `claude-bertini:conormal-analytic`): near
`(ℓ₀, x₀)` it is the common zero set of the local equation of the incidence variety and its `n`
partial derivatives in the `X`-coordinates. -/
theorem isComplexAnalyticSubset_conormalSet
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) :
    IsComplexAnalyticSubset (n := N + n) (conormalSet n p) := by
  intro y₀
  set i := chartIndex y₀.1 with hi
  set e := complexChartAt (n := n) y₀.2 with he
  set j := chartIndex (p y₀.2) with hj
  have hE := complexChartAt_prod_val (n := n) y₀
  have hy₀ : y₀.2 ∈ e.val.source := mem_complexChartAt_source y₀.2
  refine ⟨{
    generatorCount := n + 1
    generator := conormalGenerator p i e j
    coordinateNeighborhood := conormalDomain p e j
    isOpen_coordinateNeighborhood := isOpen_conormalDomain p hp e j
    center_mem_coordinateNeighborhood := by
      rw [hE]
      exact (prodChart_mem_conormalDomain_iff p hy₀).mpr (mem_affineChart_chartIndex (p y₀.2))
    coordinateNeighborhood_subset_target := by
      rw [hE]
      exact conormalDomain_subset_target p i e j
    generator_holomorphic := differentiableOn_conormalGenerator p hp i e j
    zeroLocus := ?_ }⟩
  intro y hy hyV
  rw [hE] at hy hyV ⊢
  rw [prodChart_source] at hy
  have hyj := (prodChart_mem_conormalDomain_iff p hy.2).mp hyV
  exact (conormalGenerator_prodChart_iff p hp hy.1 hy.2 hyj).symm

end Conormal

/-! ### The rank bound -/

section Rank

open scoped ProductComplexManifold
open ProductComplexManifold DerivativeIdeal RankDegeneracy Module

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N)

theorem complexChartAt_projective_val (l : ComplexProjectiveSpace N) :
    (complexChartAt (n := N) l).val = affineChart (chartIndex l) := rfl

omit [IsComplexManifold n X] in
/-- The first projection read in the preferred charts is the linear projection `(ζ, z) ↦ ζ`. -/
theorem chartDeriv_fst_eq (y : HyperplaneSpace N × X) :
    RankDegeneracy.chartDeriv (complexChartAt (n := N + n) y) (complexChartAt (n := N) y.1)
        Prod.fst y =
      (ContinuousLinearMap.fst ℂ (ComplexModel N) (ComplexModel n)).comp
        ((prodModelEquiv N n).symm : ComplexModel (N + n) →L[ℂ] ComplexModel N × ComplexModel n) := by
  have hfun : (fun w => (complexChartAt (n := N) y.1).val
      (Prod.fst ((complexChartAt (n := N + n) y).val.symm w))) =
      ⇑((ContinuousLinearMap.fst ℂ (ComplexModel N) (ComplexModel n)).comp
        ((prodModelEquiv N n).symm : ComplexModel (N + n) →L[ℂ] ComplexModel N × ComplexModel n)) := by
    funext w
    rw [complexChartAt_prod_val, prodChart_symm_apply, complexChartAt_projective_val]
    simp
  rw [RankDegeneracy.chartDeriv, hfun, ContinuousLinearMap.fderiv]

/-- The linear form `ζ' ↦ ∑ₖ cₖ ζ'ₖ` on `ℂᴺ`. -/
def linearForm (c : Fin N → ℂ) : ComplexModel N →L[ℂ] ℂ :=
  ∑ k : Fin N, c k • (EuclideanSpace.proj k : ComplexModel N →L[ℂ] ℂ)

theorem linearForm_apply (c : Fin N → ℂ) (v : ComplexModel N) :
    linearForm c v = ∑ k : Fin N, c k * v k := by
  simp [linearForm]

/-- The kernel of a nonzero linear form on `ℂᴺ` has dimension `N - 1`. -/
theorem finrank_ker_linearForm_le {c : Fin N → ℂ} {k : Fin N} (hk : c k ≠ 0) :
    finrank ℂ (LinearMap.ker (linearForm c : ComplexModel N →ₗ[ℂ] ℂ)) ≤ N - 1 := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (linearForm c : ComplexModel N →ₗ[ℂ] ℂ)
  rw [finrank_euclideanSpace_fin] at hsum
  have hne : LinearMap.range (linearForm c : ComplexModel N →ₗ[ℂ] ℂ) ≠ ⊥ := by
    rw [Ne, LinearMap.range_eq_bot]
    intro h
    have h1 := LinearMap.congr_fun h (EuclideanSpace.single k 1)
    simp only [ContinuousLinearMap.coe_coe, LinearMap.zero_apply, linearForm_apply,
      PiLp.single_apply] at h1
    simp [hk] at h1
  have hpos : 0 < finrank ℂ (LinearMap.range (linearForm c : ComplexModel N →ₗ[ℂ] ℂ)) :=
    Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
  omega

/-- **The derivative of the local equation of the incidence variety at a point of the conormal
set**: the equation `⟨insertNth i 1 ζ, chartLift z⟩` is affine in `ζ`, and its `z`-derivative
vanishes at the point, so its differential is `λ ∘ pr₁` with `λ(ζ') = ∑ₖ chartLift_{i.succAbove k} ζ'ₖ`. -/
theorem hasFDerivAt_conormalGenerator_zero
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) {i j : Fin (N + 1)}
    {e : ComplexChart n X} {w₀ : ComplexModel (N + n)}
    (hw₀ : ((prodModelEquiv N n).symm w₀).2 ∈ chartLiftDomain p e j)
    (hzero : ∀ v, fderiv ℂ (fun z => pairing (affineLift i ((prodModelEquiv N n).symm w₀).1)
      (chartLift p e j z)) ((prodModelEquiv N n).symm w₀).2 v = 0) :
    HasFDerivAt (conormalGenerator p i e j 0)
      ((linearForm fun k => chartLift p e j ((prodModelEquiv N n).symm w₀).2 (i.succAbove k)).comp
        ((ContinuousLinearMap.fst ℂ (ComplexModel N) (ComplexModel n)).comp
          ((prodModelEquiv N n).symm :
            ComplexModel (N + n) →L[ℂ] ComplexModel N × ComplexModel n))) w₀ := by
  set L := prodModelEquiv N n with hL
  set π₁ : ComplexModel (N + n) →L[ℂ] ComplexModel N :=
    (ContinuousLinearMap.fst ℂ (ComplexModel N) (ComplexModel n)).comp
      (L.symm : ComplexModel (N + n) →L[ℂ] ComplexModel N × ComplexModel n) with hπ₁
  set π₂ : ComplexModel (N + n) →L[ℂ] ComplexModel n :=
    (ContinuousLinearMap.snd ℂ (ComplexModel N) (ComplexModel n)).comp
      (L.symm : ComplexModel (N + n) →L[ℂ] ComplexModel N × ComplexModel n) with hπ₂
  set ζ₀ := (L.symm w₀).1 with hζ₀
  set z₀ := (L.symm w₀).2 with hz₀
  set Ψ : ComplexModel n → ℂ := fun z => pairing (affineLift i ζ₀) (chartLift p e j z) with hΨ
  have hΨd : HasFDerivAt Ψ (0 : ComplexModel n →L[ℂ] ℂ) z₀ := by
    have h := (hasFDerivAt_pairing_chartLift p hp hw₀ (affineLift i ζ₀))
    have h0 : fderiv ℂ Ψ z₀ = 0 := by
      ext v
      simpa using hzero v
    rw [← h0]
    exact h.differentiableAt.hasFDerivAt
  have hfun : conormalGenerator p i e j 0 = fun w => Ψ (π₂ w) +
      ∑ k : Fin N, chartLift p e j (π₂ w) (i.succAbove k) * (π₁ w k - ζ₀ k) := by
    funext w
    simp only [conormalGenerator, Fin.cons_zero, hΨ, pairing_affineLift_left, hπ₁, hπ₂,
      ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hπ₂w : π₂ w₀ = z₀ := rfl
  have hπ₁w : π₁ w₀ = ζ₀ := rfl
  have hA : HasFDerivAt (fun w => Ψ (π₂ w)) ((0 : ComplexModel n →L[ℂ] ℂ).comp π₂) w₀ := by
    exact hΨd.comp w₀ (π₂.hasFDerivAt (x := w₀))
  have hB : ∀ k : Fin N, HasFDerivAt
      (fun w => chartLift p e j (π₂ w) (i.succAbove k) * (π₁ w k - ζ₀ k))
      (chartLift p e j z₀ (i.succAbove k) •
        ((EuclideanSpace.proj k : ComplexModel N →L[ℂ] ℂ).comp π₁)) w₀ := by
    intro k
    have hf : HasFDerivAt (fun w => chartLift p e j (π₂ w) (i.succAbove k))
        ((fderiv ℂ (fun z => chartLift p e j z (i.succAbove k)) z₀).comp π₂) w₀ := by
      exact (differentiableAt_chartLift_apply p hp hw₀ (i.succAbove k)).hasFDerivAt.comp w₀
        (π₂.hasFDerivAt (x := w₀))
    have hg : HasFDerivAt (fun w => π₁ w k - ζ₀ k)
        ((EuclideanSpace.proj k : ComplexModel N →L[ℂ] ℂ).comp π₁) w₀ :=
      (((EuclideanSpace.proj k : ComplexModel N →L[ℂ] ℂ).comp π₁).hasFDerivAt).sub_const _
    refine (hf.mul hg).congr_fderiv ?_
    ext v
    simp [hπ₁w, hπ₂w]
  rw [hfun]
  refine ((hA.add (HasFDerivAt.fun_sum fun k _ => hB k))).congr_fderiv ?_
  ext v
  simp [linearForm, hπ₁]

/-- **The conormal rank bound** (blueprint `claude-bertini:conormal-rank`): at every point `y` of
a subset `A` of the conormal set, the image of the tangent space of `A` (read in the preferred
chart: the common kernel of the differentials of the germs vanishing on `A`) under the
differential of `pr₁ : Λ × X → Λ` has dimension at most `N - 1`. -/
theorem rankAt_fst_le (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    {A : Set (HyperplaneSpace N × X)} (hA : A ⊆ conormalSet n p) {y : HyperplaneSpace N × X}
    (hy : y ∈ A) : rankAt (n := N + n) (n' := N) Prod.fst A y ≤ N - 1 := by
  set i := chartIndex y.1 with hi
  set e := complexChartAt (n := n) y.2 with he
  set j := chartIndex (p y.2) with hj
  set E := complexChartAt (n := N + n) y with hEdef
  have hE : E.val = prodChart (affineChart i) e.val := rfl
  set w₀ := E.val y with hw₀def
  have hw₀ : (prodModelEquiv N n).symm w₀ = (affineChart i y.1, e.val y.2) := by
    simp [w₀, hE, prodChart_apply]
  have hy1 : y.1 ∈ (affineChart i).source := mem_affineChart_chartIndex _
  have hy2 : y.2 ∈ e.val.source := mem_complexChartAt_source y.2
  have hyj : p y.2 ∈ (affineChart j).source := mem_affineChart_chartIndex _
  have hz₀ : e.val y.2 ∈ chartLiftDomain p e j := (mem_chartLiftDomain_iff p hy2).mpr hyj
  have hgen := (conormalGenerator_prodChart_iff p hp hy1 hy2 hyj).mpr (hA hy)
  have hgen' : ∀ k, conormalGenerator p i e j k w₀ = 0 := hgen
  have hgen0 : pairing (affineLift i (affineChart i y.1)) (chartLift p e j (e.val y.2)) = 0 := by
    have := hgen' 0
    simpa only [conormalGenerator, Fin.cons_zero, hw₀] using this
  have hzero : ∀ v, fderiv ℂ (fun z => pairing (affineLift i ((prodModelEquiv N n).symm w₀).1)
      (chartLift p e j z)) ((prodModelEquiv N n).symm w₀).2 v = 0 := by
    intro v
    rw [hw₀]
    rw [fderiv_pairing_chartLift_apply p hp hz₀, chartLiftDeriv_eq_sum, pairing_sum_smul_right]
    refine Finset.sum_eq_zero fun m _ => ?_
    have := hgen' m.succ
    simp only [conormalGenerator, Fin.cons_succ, hw₀] at this
    rw [this, mul_zero]
  have hD := hasFDerivAt_conormalGenerator_zero p hp (hw₀ ▸ hz₀) hzero
  rw [hw₀] at hD
  set c : Fin N → ℂ := fun k => chartLift p e j (e.val y.2) (i.succAbove k) with hc
  -- `g = g₀ ∘ E` lies in the vanishing ideal of `A` at `y`
  set g₀ := conormalGenerator p i e j 0 with hg₀
  set g : HyperplaneSpace N × X → ℂ := fun q => g₀ (E.val q) with hgdef
  have hVo := isOpen_conormalDomain p hp e j
  have hw₀V : w₀ ∈ conormalDomain p e j := (prodChart_mem_conormalDomain_iff p hy2).mpr hyj
  have hyE : y ∈ E.val.source := mem_complexChartAt_source y
  have hg : (vanishingIdeal (n := N + n) A).mem y g := by
    refine ⟨holomorphicAt_comp_chart E hyE ?_, ?_⟩
    · filter_upwards [hVo.mem_nhds hw₀V] with w hw
      exact (differentiableOn_conormalGenerator p hp i e j 0 w hw).differentiableAt
        (hVo.mem_nhds hw)
    · have hU : IsOpen (E.val.source ∩ E.val ⁻¹' conormalDomain p e j) :=
        E.val.isOpen_inter_preimage hVo
      filter_upwards [hU.mem_nhds ⟨hyE, hw₀V⟩] with q hq hqA
      have hq1 : q ∈ (prodChart (affineChart i) e.val).source := hE ▸ hq.1
      rw [prodChart_source] at hq1
      have hq2 : prodChart (affineChart i) e.val q ∈ conormalDomain p e j := hE ▸ hq.2
      have hqj := (prodChart_mem_conormalDomain_iff p hq1.2).mp hq2
      exact (conormalGenerator_prodChart_iff p hp hq1.1 hq1.2 hqj).mpr (hA hqA) 0
  -- the tangent space lies in `ker (λ ∘ pr₁)`
  have hT : ∀ v ∈ tangentSpaceIn E A y, linearForm c ((prodModelEquiv N n).symm v).1 = 0 := by
    intro v hv
    have h1 := (mem_tangentSpaceIn.mp hv) g hg
    have heq : (fun w => g (E.val.symm w)) =ᶠ[𝓝 (E.val y)] g₀ := by
      filter_upwards [E.val.open_target.mem_nhds (E.val.map_source hyE)] with w hw
      simp only [g, E.val.right_inv hw]
    rw [heq.fderiv_eq, hD.fderiv] at h1
    simpa using h1
  have hle : (tangentSpaceIn E A y).map
      ((RankDegeneracy.chartDeriv E (complexChartAt (n := N) y.1) Prod.fst y :
        ComplexModel (N + n) →L[ℂ] ComplexModel N) : ComplexModel (N + n) →ₗ[ℂ] ComplexModel N) ≤
      LinearMap.ker (linearForm c : ComplexModel N →ₗ[ℂ] ℂ) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [LinearMap.mem_ker]
    rw [chartDeriv_fst_eq]
    exact hT v hv
  obtain ⟨k, hk⟩ := exists_succAbove_ne_zero_of_pairing_eq_zero (affineLift_ne_zero j _) hgen0
  have hck : c k ≠ 0 := hk
  calc rankAt (n := N + n) (n' := N) Prod.fst A y
      ≤ finrank ℂ (LinearMap.ker (linearForm c : ComplexModel N →ₗ[ℂ] ℂ)) :=
        Submodule.finrank_mono hle
    _ ≤ N - 1 := finrank_ker_linearForm_le hck

end Rank

end SGPT.Trace.Bertini
