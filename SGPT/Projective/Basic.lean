import SGPT.Toric.MonomialProjectiveCompactness
import SGPT.Toric.MonomialVertexCoordinates
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Complex projective space `ℙᴺ` as a compact complex manifold

The book uses `ℙᴺ` (and in examples `ℙ¹`, `ℙ²`) as a compact Kähler manifold in the setting
`ChartedSpace (ComplexModel N)` / `IsComplexManifold N` of `SGPT.Foundations.Analysis`.  This file
constructs it.

* `SGPT.Projective.ComplexProjectiveSpace N` is the projectivization
  `ℙᴺ = (ℂ^{N+1} ∖ 0)/ℂ^*` with its quotient topology (a type synonym of Mathlib's
  `Projectivization ℂ (Fin (N + 1) → ℂ)`, so that its atlas does not interfere with the
  separately constructed native `ℙ¹` of `SGPT.Toric`).  It is compact and Hausdorff
  (`SGPT.Toric.monomialProjectiveCompactSpace`, `monomialProjectiveT2Space`).
* `affineChart i` is the standard affine chart `U_i = {Z_i ≠ 0} → ℂᴺ`,
  `[Z] ↦ (Z_{i.succAbove k} / Z_i)_k`, with inverse `z ↦ [insertNth i 1 z]`
  (`affinePoint`) and target all of `ℂᴺ`.
* The atlas consists exactly of the `N + 1` affine charts; the transition maps are the
  rational maps `z ↦ (w_{j.succAbove k}/w_j)_k`, `w = insertNth i 1 z`, which are holomorphic
  on their domain `{w_j ≠ 0}`.  Hence `ℙᴺ` is a compact connected complex manifold
  (`IsComplexManifold N`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff

namespace SGPT.Projective

/-- Complex projective space `ℙᴺ = (ℂ^{N+1} ∖ 0)/ℂ^*`. -/
def ComplexProjectiveSpace (N : ℕ) : Type := Projectivization ℂ (Fin (N + 1) → ℂ)

namespace ComplexProjectiveSpace

variable {N : ℕ}

/-- The quotient topology of `ℙᴺ`. -/
instance : TopologicalSpace (ComplexProjectiveSpace N) :=
  SGPT.Toric.monomialProjectiveTopology (Fin (N + 1))

instance : CompactSpace (ComplexProjectiveSpace N) :=
  SGPT.Toric.monomialProjectiveCompactSpace (I := Fin (N + 1))

instance : T2Space (ComplexProjectiveSpace N) :=
  SGPT.Toric.monomialProjectiveT2Space (I := Fin (N + 1))

/-- The Borel σ-algebra of `ℙᴺ`. -/
instance : MeasurableSpace (ComplexProjectiveSpace N) := borel _

instance : BorelSpace (ComplexProjectiveSpace N) := ⟨rfl⟩

/-! ### Homogeneous coordinates -/

/-- The point `[v] ∈ ℙᴺ` with homogeneous coordinates `v ≠ 0`. -/
def mk (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) : ComplexProjectiveSpace N :=
  Projectivization.mk ℂ v hv

/-- A (chosen) homogeneous representative of a point. -/
def rep (p : ComplexProjectiveSpace N) : Fin (N + 1) → ℂ := Projectivization.rep p

theorem rep_ne_zero (p : ComplexProjectiveSpace N) : p.rep ≠ 0 :=
  Projectivization.rep_nonzero p

@[simp] theorem mk_rep (p : ComplexProjectiveSpace N) : mk p.rep p.rep_ne_zero = p :=
  Projectivization.mk_rep p

theorem mk_eq_mk_iff {v w : Fin (N + 1) → ℂ} (hv : v ≠ 0) (hw : w ≠ 0) :
    mk v hv = mk w hw ↔ ∃ c : ℂ, c • w = v :=
  Projectivization.mk_eq_mk_iff' ℂ v w hv hw

theorem exists_eq_smul_of_mk_eq {v w : Fin (N + 1) → ℂ} {hv : v ≠ 0} {hw : w ≠ 0}
    (h : mk v hv = mk w hw) : ∃ c : ℂ, c ≠ 0 ∧ w = c • v := by
  obtain ⟨c, hc⟩ := (mk_eq_mk_iff hw hv).mp h.symm
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  exact hw (by simpa using hc.symm)

theorem mk_smul {v : Fin (N + 1) → ℂ} (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    mk (c • v) (smul_ne_zero hc hv) = mk v hv :=
  (mk_eq_mk_iff _ _).mpr ⟨c, rfl⟩

/-- Every point is `[v]` for some `v ≠ 0`. -/
theorem ind {P : ComplexProjectiveSpace N → Prop} (h : ∀ v hv, P (mk v hv)) :
    ∀ p, P p :=
  Projectivization.ind h

theorem rep_smul (p : ComplexProjectiveSpace N) {v : Fin (N + 1) → ℂ} (hv : v ≠ 0)
    (hp : p = mk v hv) : ∃ c : ℂ, c ≠ 0 ∧ p.rep = c • v := by
  have h : mk v hv = mk p.rep p.rep_ne_zero := by rw [mk_rep, hp]
  exact exists_eq_smul_of_mk_eq h

/-- The quotient map `ℂ^{N+1} ∖ 0 → ℙᴺ` is continuous. -/
theorem continuous_mk_subtype :
    Continuous (fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => mk v.1 v.2) :=
  continuous_quotient_mk'

/-- A map into `ℙᴺ` given by a continuous nonvanishing homogeneous lift is continuous. -/
theorem continuous_mk_comp {X : Type*} [TopologicalSpace X] {F : X → Fin (N + 1) → ℂ}
    (hF : Continuous F) (hF0 : ∀ x, F x ≠ 0) :
    Continuous (fun x => mk (F x) (hF0 x)) :=
  continuous_mk_subtype.comp (hF.subtype_mk hF0)

/-! ### The affine charts -/

/-- The homogeneous lift `insertNth i 1 z` of an affine point `z` of the chart `U_i`. -/
def affineLift (i : Fin (N + 1)) (z : ComplexModel N) : Fin (N + 1) → ℂ :=
  Fin.insertNth i 1 (WithLp.ofLp z)

@[simp] theorem affineLift_same (i : Fin (N + 1)) (z : ComplexModel N) :
    affineLift i z i = 1 := by
  simp [affineLift]

@[simp] theorem affineLift_succAbove (i : Fin (N + 1)) (z : ComplexModel N) (k : Fin N) :
    affineLift i z (i.succAbove k) = z k := by
  simp [affineLift]

theorem affineLift_ne_zero (i : Fin (N + 1)) (z : ComplexModel N) : affineLift i z ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

/-- Each homogeneous coordinate of the affine lift is an affine function of `z`. -/
theorem differentiable_affineLift_apply (i m : Fin (N + 1)) :
    Differentiable ℂ (fun z : ComplexModel N => affineLift i z m) := by
  refine Fin.succAboveCases i ?_ (fun k => ?_) m
  · simp only [affineLift_same]
    exact differentiable_const 1
  · simp only [affineLift_succAbove]
    exact (EuclideanSpace.proj k : ComplexModel N →L[ℂ] ℂ).differentiable

theorem differentiable_affineLift (i : Fin (N + 1)) :
    Differentiable ℂ (affineLift (N := N) i) :=
  differentiable_pi.mpr (differentiable_affineLift_apply i)

theorem continuous_affineLift (i : Fin (N + 1)) : Continuous (affineLift (N := N) i) :=
  (differentiable_affineLift i).continuous

/-- The point `[insertNth i 1 z]` of the affine chart `U_i`. -/
def affinePoint (i : Fin (N + 1)) (z : ComplexModel N) : ComplexProjectiveSpace N :=
  mk (affineLift i z) (affineLift_ne_zero i z)

theorem affinePoint_eq_ratioPoint (i : Fin (N + 1)) (z : ComplexModel N) :
    affinePoint i z = SGPT.Toric.monomialProjectiveRatioPoint N i (WithLp.ofLp z) :=
  (SGPT.Toric.monomialProjectiveRatioPoint_eq_mk N i (WithLp.ofLp z)).symm

theorem isOpenEmbedding_affinePoint (i : Fin (N + 1)) :
    IsOpenEmbedding (affinePoint (N := N) i) := by
  have hfun : affinePoint (N := N) i =
      SGPT.Toric.monomialProjectiveRatioPoint N i ∘ (EuclideanSpace.equiv (Fin N) ℂ) := by
    funext z
    exact affinePoint_eq_ratioPoint i z
  let : TopologicalSpace (Projectivization ℂ (Fin (N + 1) → ℂ)) :=
    SGPT.Toric.monomialProjectiveTopology (Fin (N + 1))
  rw [hfun]
  exact (SGPT.Toric.isOpenEmbedding_monomialProjectiveRatioPoint N i).comp
    (EuclideanSpace.equiv (Fin N) ℂ).toHomeomorph.isOpenEmbedding

/-- The affine coordinates `(v_{i.succAbove k} / v_i)_k` of a homogeneous vector. -/
def affineRatio (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) : ComplexModel N :=
  WithLp.toLp 2 (fun k => v (i.succAbove k) / v i)

@[simp] theorem affineRatio_apply (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (k : Fin N) :
    affineRatio i v k = v (i.succAbove k) / v i := rfl

theorem affineRatio_affineLift (i : Fin (N + 1)) (z : ComplexModel N) :
    affineRatio i (affineLift i z) = z := by
  ext k
  simp

theorem affineLift_affineRatio (i : Fin (N + 1)) {v : Fin (N + 1) → ℂ} (hvi : v i ≠ 0) :
    affineLift i (affineRatio i v) = (v i)⁻¹ • v := by
  funext m
  refine Fin.succAboveCases i ?_ (fun k => ?_) m
  · simp [inv_mul_cancel₀ hvi]
  · simp [div_eq_inv_mul]

/-- On `U_i`, `[v] = [insertNth i 1 (v/v_i)]`. -/
theorem mk_eq_affinePoint (i : Fin (N + 1)) {v : Fin (N + 1) → ℂ} (hv : v ≠ 0)
    (hvi : v i ≠ 0) : mk v hv = affinePoint i (affineRatio i v) := by
  unfold affinePoint
  simp only [affineLift_affineRatio i hvi]
  exact (mk_smul hv (inv_ne_zero hvi)).symm

/-- The standard affine chart `U_i = {Z_i ≠ 0} → ℂᴺ`. -/
def affineChart (i : Fin (N + 1)) : OpenPartialHomeomorph (ComplexProjectiveSpace N) (ComplexModel N) :=
  ((isOpenEmbedding_affinePoint i).toOpenPartialHomeomorph (affinePoint i)).symm

@[simp] theorem affineChart_target (i : Fin (N + 1)) :
    (affineChart (N := N) i).target = univ := rfl

theorem affineChart_source (i : Fin (N + 1)) :
    (affineChart (N := N) i).source = range (affinePoint i) := by
  rw [affineChart, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]

@[simp] theorem affineChart_symm_apply (i : Fin (N + 1)) (z : ComplexModel N) :
    (affineChart i).symm z = affinePoint i z := rfl

@[simp] theorem affineChart_affinePoint (i : Fin (N + 1)) (z : ComplexModel N) :
    affineChart i (affinePoint i z) = z :=
  (isOpenEmbedding_affinePoint i).toOpenPartialHomeomorph_left_inv (affinePoint i)

theorem affinePoint_mem_source (i : Fin (N + 1)) (z : ComplexModel N) :
    affinePoint i z ∈ (affineChart i).source := by
  rw [affineChart_source]
  exact mem_range_self z

/-- `[v] ∈ U_i` iff `v_i ≠ 0`. -/
theorem mk_mem_affineChart_source_iff (i : Fin (N + 1)) {v : Fin (N + 1) → ℂ} (hv : v ≠ 0) :
    mk v hv ∈ (affineChart i).source ↔ v i ≠ 0 := by
  rw [affineChart_source]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨c, hc0, hc⟩ := exists_eq_smul_of_mk_eq hz
    intro hvi
    have := congrFun hc i
    simp [hvi] at this
    exact hc0 this.symm
  · intro hvi
    exact ⟨_, (mk_eq_affinePoint i hv hvi).symm⟩

theorem mem_affineChart_source_iff (i : Fin (N + 1)) (p : ComplexProjectiveSpace N) :
    p ∈ (affineChart i).source ↔ p.rep i ≠ 0 := by
  conv_lhs => rw [← mk_rep p]
  exact mk_mem_affineChart_source_iff i p.rep_ne_zero

/-- In the chart `U_i`, `[v] ↦ (v_{i.succAbove k} / v_i)_k`. -/
theorem affineChart_mk (i : Fin (N + 1)) {v : Fin (N + 1) → ℂ} (hv : v ≠ 0) (hvi : v i ≠ 0) :
    affineChart i (mk v hv) = affineRatio i v := by
  rw [mk_eq_affinePoint i hv hvi, affineChart_affinePoint]

theorem exists_rep_ne_zero (p : ComplexProjectiveSpace N) : ∃ i, p.rep i ≠ 0 := by
  by_contra h
  push Not at h
  exact p.rep_ne_zero (funext h)

theorem exists_mem_affineChart_source (p : ComplexProjectiveSpace N) :
    ∃ i, p ∈ (affineChart i).source := by
  obtain ⟨i, hi⟩ := exists_rep_ne_zero p
  exact ⟨i, (mem_affineChart_source_iff i p).mpr hi⟩

/-- The index of a chart containing `p`. -/
def chartIndex (p : ComplexProjectiveSpace N) : Fin (N + 1) :=
  Classical.choose (exists_mem_affineChart_source p)

theorem mem_affineChart_chartIndex (p : ComplexProjectiveSpace N) :
    p ∈ (affineChart (chartIndex p)).source :=
  Classical.choose_spec (exists_mem_affineChart_source p)

/-- The atlas of `ℙᴺ`: the `N + 1` standard affine charts. -/
instance : ChartedSpace (ComplexModel N) (ComplexProjectiveSpace N) where
  atlas := range affineChart
  chartAt p := affineChart (chartIndex p)
  mem_chart_source p := mem_affineChart_chartIndex p
  chart_mem_atlas p := ⟨chartIndex p, rfl⟩

theorem mem_atlas_iff (e : OpenPartialHomeomorph (ComplexProjectiveSpace N) (ComplexModel N)) :
    e ∈ atlas (ComplexModel N) (ComplexProjectiveSpace N) ↔ ∃ i, e = affineChart i := by
  change e ∈ range affineChart ↔ _
  simp only [mem_range, eq_comm]

theorem affineChart_mem_atlas (i : Fin (N + 1)) :
    affineChart i ∈ atlas (ComplexModel N) (ComplexProjectiveSpace N) := ⟨i, rfl⟩

/-! ### Transition maps -/

theorem mem_transition_source_iff (i j : Fin (N + 1)) (z : ComplexModel N) :
    z ∈ ((affineChart i).symm.trans (affineChart j)).source ↔ affineLift i z j ≠ 0 := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, affineChart_target]
  simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, affineChart_symm_apply]
  exact mk_mem_affineChart_source_iff j (affineLift_ne_zero i z)

/-- The transition map `U_i → U_j`: `z ↦ (w_{j.succAbove k} / w_j)_k`, `w = insertNth i 1 z`. -/
theorem transition_apply (i j : Fin (N + 1)) {z : ComplexModel N} (hz : affineLift i z j ≠ 0) :
    ((affineChart i).symm.trans (affineChart j)) z = affineRatio j (affineLift i z) := by
  change affineChart j (affinePoint i z) = _
  exact affineChart_mk j _ hz

/-- The affine-ratio map is holomorphic where the denominator does not vanish. -/
theorem differentiableAt_affineRatio (j : Fin (N + 1)) {v : Fin (N + 1) → ℂ} (hvj : v j ≠ 0) :
    DifferentiableAt ℂ (affineRatio j) v := by
  have h : DifferentiableAt ℂ (fun w : Fin (N + 1) → ℂ => fun k : Fin N =>
      w (j.succAbove k) / w j) v := by
    refine differentiableAt_pi.mpr fun k => ?_
    simp only [div_eq_mul_inv]
    exact (differentiableAt_apply (𝕜 := ℂ) (j.succAbove k) v).mul
      ((differentiableAt_apply (𝕜 := ℂ) j v).inv hvj)
  exact (EuclideanSpace.equiv (Fin N) ℂ).symm.differentiableAt.comp v h

theorem contDiffAt_affineRatio (j : Fin (N + 1)) {v : Fin (N + 1) → ℂ} (hvj : v j ≠ 0) :
    ContDiffAt ℂ ∞ (affineRatio j) v := by
  have hopen : IsOpen {w : Fin (N + 1) → ℂ | w j ≠ 0} :=
    isOpen_ne.preimage (continuous_apply j)
  have hd : DifferentiableOn ℂ (affineRatio j) {w : Fin (N + 1) → ℂ | w j ≠ 0} :=
    fun w hw => (differentiableAt_affineRatio j hw).differentiableWithinAt
  exact (contDiffOn_of_differentiableOn_complex hd hopen).contDiffAt (hopen.mem_nhds hvj)

theorem differentiableOn_transition (i j : Fin (N + 1)) :
    DifferentiableOn ℂ ((affineChart (N := N) i).symm.trans (affineChart j))
      ((affineChart (N := N) i).symm.trans (affineChart j)).source := by
  intro z hz
  have hz' := (mem_transition_source_iff i j z).mp hz
  have hd : DifferentiableAt ℂ (fun y => affineRatio j (affineLift i y)) z :=
    (differentiableAt_affineRatio j hz').comp z (differentiable_affineLift i z)
  refine hd.differentiableWithinAt.congr (fun y hy => ?_) ?_
  · exact transition_apply i j ((mem_transition_source_iff i j y).mp hy)
  · exact transition_apply i j hz'

/-- Holomorphic transition maps: `ℙᴺ` is a complex manifold. -/
theorem isManifold : IsManifold 𝓘(ℂ, ComplexModel N) ∞ (ComplexProjectiveSpace N) := by
  apply isManifold_of_contDiffOn 𝓘(ℂ, ComplexModel N) ∞ (ComplexProjectiveSpace N)
  intro e f he hf
  obtain ⟨i, rfl⟩ := (mem_atlas_iff e).mp he
  obtain ⟨j, rfl⟩ := (mem_atlas_iff f).mp hf
  simpa using contDiffOn_of_differentiableOn_complex (differentiableOn_transition i j)
    ((affineChart i).symm.trans (affineChart j)).open_source

instance : SecondCountableTopology (ComplexProjectiveSpace N) :=
  ChartedSpace.secondCountable_of_sigmaCompact (ComplexModel N) (ComplexProjectiveSpace N)

/-- `ℙᴺ` is a (compact, Hausdorff, second-countable) complex manifold of dimension `N`. -/
instance : IsComplexManifold N (ComplexProjectiveSpace N) where
  toIsManifold := isManifold

instance : Nonempty (ComplexProjectiveSpace N) := ⟨affinePoint 0 0⟩

/-- The point `[1 : ⋯ : 1]`, which lies in every affine chart. -/
theorem mk_one_mem_affineChart_source (i : Fin (N + 1)) :
    mk (fun _ => (1 : ℂ)) (fun h => one_ne_zero (congrFun h 0)) ∈ (affineChart i).source :=
  (mk_mem_affineChart_source_iff i _).mpr one_ne_zero

/-- `ℙᴺ` is connected: it is the union of the connected affine charts `U_i ≅ ℂᴺ`, which all
contain `[1 : ⋯ : 1]`. -/
instance : ConnectedSpace (ComplexProjectiveSpace N) := by
  rw [connectedSpace_iff_univ]
  have hU : (⋃ i : Fin (N + 1), range (affinePoint (N := N) i)) = univ := by
    apply eq_univ_of_forall
    intro p
    obtain ⟨i, hi⟩ := exists_mem_affineChart_source p
    rw [affineChart_source] at hi
    exact mem_iUnion.mpr ⟨i, hi⟩
  rw [← hU]
  have hone : ∀ i : Fin (N + 1), mk (fun _ => (1 : ℂ)) (fun h => one_ne_zero (congrFun h 0)) ∈
      range (affinePoint (N := N) i) := by
    intro i
    rw [← affineChart_source]
    exact mk_one_mem_affineChart_source i
  refine ⟨⟨_, mem_iUnion.mpr ⟨0, hone 0⟩⟩, ?_⟩
  apply isPreconnected_iUnion ⟨_, mem_iInter.mpr hone⟩
  intro i
  exact isPreconnected_range (isOpenEmbedding_affinePoint i).continuous

theorem isOpen_affineChart_source (i : Fin (N + 1)) :
    IsOpen (affineChart (N := N) i).source := (affineChart i).open_source

theorem continuous_affinePoint (i : Fin (N + 1)) : Continuous (affinePoint (N := N) i) :=
  (isOpenEmbedding_affinePoint i).continuous

end ComplexProjectiveSpace

end SGPT.Projective
