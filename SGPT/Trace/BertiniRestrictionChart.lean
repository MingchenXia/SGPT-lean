import SGPT.Trace.BertiniSmoothConormal
import SGPT.PSH.CountablePluripolar
import SGPT.Foundations.Analysis.FirstPass.LocalHolomorphicInverse
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback

/-!
# Slice charts of the incidence variety

Source: `chapter_trace.tex`, Section "Analytic Bertini theorems", `cor:qpshgeneralres` (for
`φ ∈ QPSH(X)` and quasi-every member `H` of a base-point-free linear system, `φ|_H ≢ -∞`).
Blueprint: `claude-bertini:product-chart`, `claude-bertini:product-slice`
(`blueprint/src/claude-bertini.tex`) and `blueprint/src/claude-bertini-bc.tex`.

Let `p : X → ℙᴺ` be holomorphic and `(ℓ₀, x₀)` a point of the incidence variety
`U = {(ℓ, x) : x ∈ p⁻¹(H_ℓ)} ⊆ Λ × X` at which the member `p⁻¹(H_{ℓ₀})` is smooth. In the product
chart `U_i × e` of `Λ × X` the incidence variety is the zero set of the function
`G(ζ, z) = ⟨insertNth i 1 ζ, chartLift z⟩`, whose partial derivative in some coordinate `z_m` of `X`
does not vanish. The **flattening** `Ψ(w) = w + (G(w) - z_m) e_m` (`flatMap`) keeps the
`Λ`-coordinate `ζ`, has injective derivative (`injective_flatMap_deriv`), hence is a local
biholomorphism (`FirstPass.exists_localHolomorphicEquivAt`), and sends `U` to the coordinate
hyperplane `{z_m = 0}`. A **slice chart** (`SliceChart`) bundles such a flattening with a
product of balls `D × Ω` in the flat coordinates and a local decomposition `φ = ψ + h` (`ψ` psh,
`h` smooth) of a quasi-psh `φ`; the map `(ζ, b) ↦ point ζ b` parametrizes, for each fixed `ζ ∈ D`,
an open piece of the member `p⁻¹(H_{[insertNth i 1 ζ]})` (`SliceChart.point_mem_member`).

* `exists_sliceChart`: slice charts exist at every smooth point of the incidence variety.
* `SliceChart.locallyPluripolar_image_badSet` (the **product-slice lemma**, blueprint
  `claude-bertini:product-slice`): the set of `ζ` for which `φ ≡ -∞` on the slice piece indexed by
  an open `B ⊆ Ω` is pluripolar. For one `b* ∈ B` the function `ζ ↦ ψ(slice ζ b*)` is psh on `D`
  (`HolomorphicPullback.plurisubharmonicOn_comp_holomorphic`) and not identically `-∞`: the
  projection of `U` to `X` is open (the equation `G` is affine in `ζ` with a nonzero coefficient,
  so it can be solved for `ζ_k`), and `φ` is not `-∞` on any open subset of `X`.
* `SliceChart.exists_mem_image_badSet`: if `(ℓ, x)` lies in the domain of the chart and `φ ≡ -∞`
  on a neighbourhood of `x` in `p⁻¹(H_ℓ)`, then `ℓ` lies in one of these countably many sets.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.Bertini

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

open scoped ProductComplexManifold
open ProductComplexManifold

/-! ### Flat coordinates -/

section Flat

variable {N n : ℕ}

/-- The direction `e_m` of the `m`-th coordinate of `X` in `ℂ^{N+n} = ℂᴺ × ℂⁿ`. -/
def slDir (m : Fin n) : ComplexModel (N + n) :=
  prodModelEquiv N n (0, EuclideanSpace.single m 1)

/-- The `m`-th coordinate `w ↦ z_m` of `X` on `ℂ^{N+n} = ℂᴺ × ℂⁿ`. -/
def slCoord (m : Fin n) : ComplexModel (N + n) →L[ℂ] ℂ :=
  (EuclideanSpace.proj m : ComplexModel n →L[ℂ] ℂ).comp
    ((ContinuousLinearMap.snd ℂ (ComplexModel N) (ComplexModel n)).comp
      ((prodModelEquiv N n).symm : ComplexModel (N + n) →L[ℂ] ComplexModel N × ComplexModel n))

theorem slCoord_apply (m : Fin n) (w : ComplexModel (N + n)) :
    slCoord (N := N) m w = ((prodModelEquiv N n).symm w).2 m := rfl

theorem symm_slDir (m : Fin n) :
    (prodModelEquiv N n).symm (slDir m) = (0, EuclideanSpace.single m 1) := by
  simp [slDir]

theorem slCoord_slDir (m : Fin n) : slCoord (N := N) m (slDir m) = 1 := by
  simp [slCoord_apply, symm_slDir]

/-- The projection `w ↦ w - z_m e_m` onto the flat hyperplane `{z_m = 0}`. -/
def flatProj (m : Fin n) : ComplexModel (N + n) →L[ℂ] ComplexModel (N + n) :=
  ContinuousLinearMap.id ℂ _ - (slCoord m).smulRight (slDir m)

theorem flatProj_apply (m : Fin n) (w : ComplexModel (N + n)) :
    flatProj m w = w - slCoord m w • slDir m := rfl

theorem slCoord_flatProj (m : Fin n) (w : ComplexModel (N + n)) :
    slCoord m (flatProj m w) = 0 := by
  simp [flatProj_apply, slCoord_slDir]

theorem fst_symm_flatProj (m : Fin n) (w : ComplexModel (N + n)) :
    ((prodModelEquiv N n).symm (flatProj m w)).1 = ((prodModelEquiv N n).symm w).1 := by
  simp [flatProj_apply, symm_slDir]

/-- The `X`-coordinates of a flat point only see `b` up to its `m`-th coordinate. -/
theorem flatProj_prod_update (m : Fin n) (ζ : ComplexModel N) (z : ComplexModel n) (c : ℂ) :
    flatProj m (prodModelEquiv N n (ζ, z + c • EuclideanSpace.single m 1)) =
      flatProj m (prodModelEquiv N n (ζ, z)) := by
  have h : prodModelEquiv N n (ζ, z + c • EuclideanSpace.single m 1) =
      prodModelEquiv N n (ζ, z) + c • slDir m := by
    rw [slDir, ← map_smul, ← map_add]
    simp
  rw [h, map_add, map_smul]
  simp [flatProj_apply, slCoord_slDir]

theorem snd_symm_flatProj (m : Fin n) (w : ComplexModel (N + n)) :
    ((prodModelEquiv N n).symm (flatProj m w)).2 =
      ((prodModelEquiv N n).symm w).2 - slCoord m w • EuclideanSpace.single m 1 := by
  simp [flatProj_apply, symm_slDir]

/-- Moving `ζ` along `e_k` changes the affine equation by the `k`-th coefficient. -/
theorem pairing_affineLift_sub_smul_single (i : Fin (N + 1)) (ζ : ComplexModel N) (k : Fin N)
    (t : ℂ) (v : Fin (N + 1) → ℂ) :
    pairing (affineLift i (ζ - t • EuclideanSpace.single k 1)) v =
      pairing (affineLift i ζ) v - v (i.succAbove k) * t := by
  rw [pairing_affineLift_left, pairing_affineLift_left]
  have h : ∀ k' : Fin N, v (i.succAbove k') *
      (ζ - t • EuclideanSpace.single k (1 : ℂ) : ComplexModel N) k' =
      v (i.succAbove k') * ζ k' - if k' = k then v (i.succAbove k) * t else 0 := by
    intro k'
    by_cases hk : k' = k
    · subst hk
      simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, if_true, smul_eq_mul,
        mul_one, mul_sub]
    · simp [hk]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end Flat

/-! ### The flattening of the incidence variety -/

section Flattening

variable {N n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N)

/-- The flattening `Ψ(w) = w + (G(w) - z_m) e_m` of the incidence variety in the product chart
`U_i × e` (`G` the local equation `conormalGenerator p i e j 0`). -/
def flatMap (i : Fin (N + 1)) (e : ComplexChart n X) (j : Fin (N + 1)) (m : Fin n)
    (w : ComplexModel (N + n)) : ComplexModel (N + n) :=
  w + (conormalGenerator p i e j 0 w - slCoord m w) • slDir m

omit [IsComplexManifold n X] in
theorem slCoord_flatMap (i : Fin (N + 1)) (e : ComplexChart n X) (j : Fin (N + 1)) (m : Fin n)
    (w : ComplexModel (N + n)) :
    slCoord m (flatMap p i e j m w) = conormalGenerator p i e j 0 w := by
  simp [flatMap, slCoord_slDir]

omit [IsComplexManifold n X] in
theorem fst_symm_flatMap (i : Fin (N + 1)) (e : ComplexChart n X) (j : Fin (N + 1)) (m : Fin n)
    (w : ComplexModel (N + n)) :
    ((prodModelEquiv N n).symm (flatMap p i e j m w)).1 = ((prodModelEquiv N n).symm w).1 := by
  simp [flatMap, symm_slDir]

omit [IsComplexManifold n X] in
theorem flatMap_eq_flatProj {i : Fin (N + 1)} {e : ComplexChart n X} {j : Fin (N + 1)}
    {m : Fin n} {w : ComplexModel (N + n)} (h : conormalGenerator p i e j 0 w = 0) :
    flatMap p i e j m w = flatProj m w := by
  simp only [flatMap, flatProj_apply, h, zero_sub, neg_smul]
  abel

omit [IsComplexManifold n X] in
theorem hasFDerivAt_flatMap {i : Fin (N + 1)} {e : ComplexChart n X} {j : Fin (N + 1)}
    (m : Fin n) {w : ComplexModel (N + n)} {G' : ComplexModel (N + n) →L[ℂ] ℂ}
    (hG : HasFDerivAt (conormalGenerator p i e j 0) G' w) :
    HasFDerivAt (flatMap p i e j m)
      (ContinuousLinearMap.id ℂ _ + (G' - slCoord m).smulRight (slDir m)) w :=
  (hasFDerivAt_id w).add ((hG.sub (slCoord m).hasFDerivAt).smul_const (slDir m))

/-- The derivative of the flattening is injective when `∂G/∂z_m ≠ 0`. -/
theorem injective_flatMap_deriv {m : Fin n} {G' : ComplexModel (N + n) →L[ℂ] ℂ}
    (h : G' (slDir (N := N) m) ≠ 0) :
    Function.Injective (ContinuousLinearMap.id ℂ (ComplexModel (N + n)) +
      (G' - slCoord (N := N) m).smulRight (slDir (N := N) m)) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  have h1 : v + (G' v - slCoord (N := N) m v) • slDir (N := N) m = 0 := by simpa using hv
  have h2 : G' v = 0 := by
    have := congrArg (slCoord (N := N) m) h1
    simp only [map_add, map_smul, slCoord_slDir, smul_eq_mul, mul_one, map_zero] at this
    linear_combination this
  have h3 : v = slCoord (N := N) m v • slDir (N := N) m := by
    rw [h2, zero_sub, neg_smul] at h1
    exact eq_of_add_neg_eq_zero h1
  have h4 : slCoord (N := N) m v = 0 := by
    have := congrArg G' h3
    rw [map_smul, smul_eq_mul, h2] at this
    exact (mul_eq_zero.mp this.symm).resolve_right h
  rw [h3, h4, zero_smul]

theorem differentiableOn_flatMap
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) (i : Fin (N + 1))
    (e : ComplexChart n X) (j : Fin (N + 1)) (m : Fin n) :
    DifferentiableOn ℂ (flatMap p i e j m) (conormalDomain p e j) := by
  intro w hw
  have hG := (differentiableOn_conormalGenerator p hp i e j 0 w hw).differentiableAt
    ((isOpen_conormalDomain p hp e j).mem_nhds hw)
  exact (hasFDerivAt_flatMap p m hG.hasFDerivAt).differentiableAt.differentiableWithinAt

/-- `∂G/∂z_m` is the `m`-th derivative generator. -/
theorem fderiv_conormalGenerator_zero_slDir
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p) {i : Fin (N + 1)}
    {e : ComplexChart n X} {j : Fin (N + 1)} {w : ComplexModel (N + n)}
    (hw : w ∈ conormalDomain p e j) (m : Fin n) :
    fderiv ℂ (conormalGenerator p i e j 0) w (slDir m) = conormalGenerator p i e j m.succ w := by
  set L := prodModelEquiv N n with hL
  set ζ := (L.symm w).1 with hζ
  set z := (L.symm w).2 with hz
  have hGd : DifferentiableAt ℂ (conormalGenerator p i e j 0) w :=
    (differentiableOn_conormalGenerator p hp i e j 0 w hw).differentiableAt
      ((isOpen_conormalDomain p hp e j).mem_nhds hw)
  have hι : HasFDerivAt (fun z' : ComplexModel n => L (ζ, z'))
      ((L : ComplexModel N × ComplexModel n →L[ℂ] ComplexModel (N + n)).comp
        ((0 : ComplexModel n →L[ℂ] ComplexModel N).prod (ContinuousLinearMap.id ℂ _))) z :=
    (L : ComplexModel N × ComplexModel n →L[ℂ] ComplexModel (N + n)).hasFDerivAt.comp z
      ((hasFDerivAt_const ζ z).prodMk (hasFDerivAt_id z))
  have hιz : L (ζ, z) = w := by simp [hζ, hz]
  have hGd' : HasFDerivAt (conormalGenerator p i e j 0)
      (fderiv ℂ (conormalGenerator p i e j 0) w) (L (ζ, z)) := by
    rw [hιz]
    exact hGd.hasFDerivAt
  have hcomp := hGd'.comp z hι
  have hfun : (conormalGenerator p i e j 0 ∘ fun z' => L (ζ, z')) =
      fun z' => pairing (affineLift i ζ) (chartLift p e j z') := by
    funext z'
    simp [conormalGenerator, hL]
  rw [hfun] at hcomp
  have hzd : z ∈ chartLiftDomain p e j := hw.2
  have h1 := hcomp.fderiv
  have h2 : fderiv ℂ (fun z' => pairing (affineLift i ζ) (chartLift p e j z')) z
      (EuclideanSpace.single m 1) = fderiv ℂ (conormalGenerator p i e j 0) w (slDir m) := by
    rw [h1]
    simp [slDir]
    rfl
  rw [← h2, fderiv_pairing_chartLift_apply p hp hzd]
  simp [conormalGenerator, hL, hζ, hz]

omit [IsComplexManifold n X] in
/-- A point of `conormalDomain` on which `G` vanishes is a point of the incidence variety. -/
theorem symm_snd_mem_member {i : Fin (N + 1)} {e : ComplexChart n X} {j : Fin (N + 1)}
    {w : ComplexModel (N + n)} (hw : w ∈ conormalDomain p e j)
    (hG : conormalGenerator p i e j 0 w = 0) :
    e.val.symm ((prodModelEquiv N n).symm w).2 ∈
      member p (affinePoint i ((prodModelEquiv N n).symm w).1) := by
  set q : HyperplaneSpace N × X :=
    (affinePoint i ((prodModelEquiv N n).symm w).1, e.val.symm ((prodModelEquiv N n).symm w).2)
  have hz : ((prodModelEquiv N n).symm w).2 ∈ chartLiftDomain p e j := hw.2
  have hq1 : q.1 ∈ (affineChart i).source := affinePoint_mem_source i _
  have hq2 : q.2 ∈ e.val.source := e.val.map_target hz.1
  have hqj : p q.2 ∈ (affineChart j).source := hz.2
  have hqw : prodChart (affineChart i) e.val q = w := by
    rw [prodChart_apply]
    simp only [q, affineChart_affinePoint, e.val.right_inv hz.1]
    simp
  have := (conormalGenerator_zero_prodChart_eq_zero_iff p hq1 hq2 hqj).mp (by rw [hqw]; exact hG)
  exact this

end Flattening

/-! ### Slice charts -/

section SliceChart

variable {N n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N) (φ : X → EReal)

/-- A **slice chart** of the incidence variety `{(ℓ, x) : x ∈ p⁻¹(H_ℓ)}` adapted to `φ`: a local
biholomorphism `Φ` of `ℂ^{N+n}` defined on the product chart `U_i × e` of `Λ × X`, equal there to
the flattening `flatMap p i e j m`, balls `D = B(ζ₀, r) ⊆ ℂᴺ` and `Ω = B(z₀, r) ⊆ ℂⁿ` of flat
coordinates mapped into the target of `Φ`, and a decomposition `φ ∘ e⁻¹ = ψ + h` with `ψ` psh and
`h` real on an open set `V` containing the `X`-coordinates of `Φ⁻¹(D × Ω)`. -/
structure SliceChart (n : ℕ) {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (p : X → ComplexProjectiveSpace N) (φ : X → EReal) where
  /-- the chart `U_i` of `Λ` -/
  i : Fin (N + 1)
  /-- the chart of `X` -/
  e : ComplexChart n X
  /-- the chart `U_j` of `ℙᴺ` -/
  j : Fin (N + 1)
  /-- the coordinate of `X` in which the local equation has nonzero derivative -/
  m : Fin n
  /-- the centre, in product coordinates -/
  w₀ : ComplexModel (N + n)
  /-- the local biholomorphism -/
  Φ : LocalHolomorphicEquivAt (n := N + n) w₀
  source_subset : Φ.source ⊆ conormalDomain p e j
  toFun_eq : Φ.toFun = flatMap p i e j m
  /-- the `Λ`-coordinate of the centre -/
  ζ₀ : ComplexModel N
  /-- the `X`-coordinate of the centre -/
  z₀ : ComplexModel n
  w₀_eq : w₀ = prodModelEquiv N n (ζ₀, z₀)
  /-- the radius of the balls `D` and `Ω` -/
  r : ℝ
  r_pos : 0 < r
  /-- the domain of the local decomposition of `φ` -/
  V : Set (ComplexModel n)
  isOpen_V : IsOpen V
  V_subset : V ⊆ e.val.target
  /-- the psh part -/
  ψ : ComplexModel n → EReal
  /-- the smooth part -/
  h : ComplexModel n → ℝ
  psh : PlurisubharmonicOn ψ V
  eq_add : ∀ y ∈ V, φ (e.val.symm y) = ψ y + (h y : EReal)
  mapsTo_target : ∀ ζ ∈ ball ζ₀ r, ∀ b ∈ ball z₀ r,
    flatProj m (prodModelEquiv N n (ζ, b)) ∈ Φ.target
  mapsTo_V : ∀ ζ ∈ ball ζ₀ r, ∀ b ∈ ball z₀ r,
    ((prodModelEquiv N n).symm (Φ.invFun (flatProj m (prodModelEquiv N n (ζ, b))))).2 ∈ V

namespace SliceChart

variable {p φ} (c : SliceChart n p φ)

/-- The `X`-coordinates of the point of the incidence variety with flat coordinates `(ζ, b)`. -/
def slice (ζ : ComplexModel N) (b : ComplexModel n) : ComplexModel n :=
  ((prodModelEquiv N n).symm (c.Φ.invFun (flatProj c.m (prodModelEquiv N n (ζ, b))))).2

/-- The point of `X` with flat coordinates `(ζ, b)`; it lies on `p⁻¹(H_{[insertNth i 1 ζ]})`. -/
def point (ζ : ComplexModel N) (b : ComplexModel n) : X := c.e.val.symm (c.slice ζ b)

/-- The domain of the chart in `Λ × X`. -/
def domain : Set (HyperplaneSpace N × X) :=
  {q | q.1 ∈ (affineChart c.i).source ∧ q.2 ∈ c.e.val.source ∧
    prodChart (affineChart c.i) c.e.val q ∈ c.Φ.source ∧
    affineChart c.i q.1 ∈ ball c.ζ₀ (c.r / 2) ∧ c.e.val q.2 ∈ ball c.z₀ c.r}

theorem isOpen_domain : IsOpen c.domain := by
  have h : c.domain = (prodChart (affineChart c.i) c.e.val).source ∩
      prodChart (affineChart c.i) c.e.val ⁻¹' (c.Φ.source ∩
        (prodModelEquiv N n).symm ⁻¹' (ball c.ζ₀ (c.r / 2) ×ˢ ball c.z₀ c.r)) := by
    ext q
    simp only [domain, prodChart_source, mem_prod, mem_inter_iff, mem_preimage, mem_ofPred_eq,
      prodChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    tauto
  rw [h]
  exact (prodChart (affineChart c.i) c.e.val).isOpen_inter_preimage
    (c.Φ.isOpen_source.inter ((isOpen_ball.prod isOpen_ball).preimage
      (prodModelEquiv N n).symm.continuous))

/-- The `Λ`-coordinate is preserved by the flattening. -/
theorem fst_invFun {t : ComplexModel (N + n)} (ht : t ∈ c.Φ.target) :
    ((prodModelEquiv N n).symm (c.Φ.invFun t)).1 = ((prodModelEquiv N n).symm t).1 := by
  have h := fst_symm_flatMap p c.i c.e c.j c.m (c.Φ.invFun t)
  rw [← c.toFun_eq, c.Φ.right_inv t ht] at h
  exact h.symm

/-- Points with flat coordinates lie on the incidence variety. -/
theorem generator_invFun_flatProj {ζ : ComplexModel N} {b : ComplexModel n}
    (ht : flatProj c.m (prodModelEquiv N n (ζ, b)) ∈ c.Φ.target) :
    conormalGenerator p c.i c.e c.j 0
      (c.Φ.invFun (flatProj c.m (prodModelEquiv N n (ζ, b)))) = 0 := by
  have h := slCoord_flatMap p c.i c.e c.j c.m
    (c.Φ.invFun (flatProj c.m (prodModelEquiv N n (ζ, b))))
  rw [← c.toFun_eq, c.Φ.right_inv _ ht, slCoord_flatProj] at h
  exact h.symm

/-- `point ζ b` lies on the member `p⁻¹(H_{[insertNth i 1 ζ]})`. -/
theorem point_mem_member {ζ : ComplexModel N} {b : ComplexModel n} (hζ : ζ ∈ ball c.ζ₀ c.r)
    (hb : b ∈ ball c.z₀ c.r) : c.point ζ b ∈ member p (affinePoint c.i ζ) := by
  have ht := c.mapsTo_target ζ hζ b hb
  have hs : c.Φ.invFun (flatProj c.m (prodModelEquiv N n (ζ, b))) ∈ conormalDomain p c.e c.j :=
    c.source_subset (c.Φ.mapsTo_invFun ht)
  have h := symm_snd_mem_member p hs (c.generator_invFun_flatProj ht)
  rwa [c.fst_invFun ht, fst_symm_flatProj, ContinuousLinearEquiv.symm_apply_apply] at h

end SliceChart

/-- **Existence of slice charts** (blueprint `claude-bertini:product-chart`) at every point
`(ℓ₀, x₀)` of the incidence variety at which the member `p⁻¹(H_{ℓ₀})` is smooth. -/
theorem exists_sliceChart (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {q₀ : HyperplaneSpace N × X}
    (hmem : q₀.2 ∈ member p q₀.1) (hsm : ¬ IsSingularPointOfMember n p q₀.1 q₀.2) :
    ∃ c : SliceChart n p φ, q₀ ∈ c.domain := by
  set i := chartIndex q₀.1 with hi
  set e := complexChartAt (n := n) q₀.2 with he
  set j := chartIndex (p q₀.2) with hj
  have hq1 : q₀.1 ∈ (affineChart i).source := mem_affineChart_chartIndex _
  have hq2 : q₀.2 ∈ e.val.source := mem_complexChartAt_source _
  have hqj : p q₀.2 ∈ (affineChart j).source := mem_affineChart_chartIndex _
  set L := prodModelEquiv N n with hL
  set w₀ := prodChart (affineChart i) e.val q₀ with hw₀
  have hw₀V : w₀ ∈ conormalDomain p e j := (prodChart_mem_conormalDomain_iff p hq2).mpr hqj
  have hgen0 : conormalGenerator p i e j 0 w₀ = 0 :=
    (conormalGenerator_zero_prodChart_eq_zero_iff p hq1 hq2 hqj).mpr hmem
  obtain ⟨m, hm⟩ : ∃ m : Fin n, conormalGenerator p i e j m.succ w₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hsm ((conormalGenerator_prodChart_iff p hp hq1 hq2 hqj).mp fun k => ?_)
    refine Fin.cases ?_ (fun m => ?_) k
    · exact hgen0
    · exact hcon m
  have hGd : DifferentiableAt ℂ (conormalGenerator p i e j 0) w₀ :=
    (differentiableOn_conormalGenerator p hp i e j 0 w₀ hw₀V).differentiableAt
      ((isOpen_conormalDomain p hp e j).mem_nhds hw₀V)
  have hderiv : fderiv ℂ (conormalGenerator p i e j 0) w₀ (slDir (N := N) m) ≠ 0 := by
    rw [fderiv_conormalGenerator_zero_slDir p hp hw₀V m]
    exact hm
  have hΨ := hasFDerivAt_flatMap p m hGd.hasFDerivAt
  have hinj : Function.Injective (fderiv ℂ (flatMap p i e j m) w₀) := by
    rw [hΨ.fderiv]
    exact injective_flatMap_deriv hderiv
  obtain ⟨Φ, hΦs, hΦf, -⟩ := exists_localHolomorphicEquivAt (isOpen_conormalDomain p hp e j)
    hw₀V (differentiableOn_flatMap p hp i e j m) hinj
  set ζ₀ := affineChart i q₀.1 with hζ₀
  set z₀ := e.val q₀.2 with hz₀
  have hw₀eq : w₀ = L (ζ₀, z₀) := rfl
  -- the local decomposition of `φ` at `x₀`
  obtain ⟨ψ, h, ⟨U, hUo, hzU, hUpsh⟩, -, heq⟩ := hφ e z₀ (e.val.map_source hq2)
  obtain ⟨V₁, hV₁, hV₁o, hzV₁⟩ := _root_.eventually_nhds_iff.mp heq
  set V := U ∩ V₁ ∩ e.val.target with hVdef
  have hVo : IsOpen V := (hUo.inter hV₁o).inter e.val.open_target
  have hzV : z₀ ∈ V := ⟨⟨hzU, hzV₁⟩, e.val.map_source hq2⟩
  have hpsh : PlurisubharmonicOn ψ V := fun y hy => (hUpsh.plurisubharmonicOn hUo) y hy.1.1
  have heqV : ∀ y ∈ V, φ (e.val.symm y) = ψ y + (h y : EReal) := fun y hy => hV₁ y hy.1.2
  -- the target region
  set R := Φ.target ∩ Φ.invFun ⁻¹' (L.symm ⁻¹' (univ ×ˢ V)) with hR
  have hRo : IsOpen R := Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage Φ.isOpen_target
    ((isOpen_univ.prod hVo).preimage L.symm.continuous)
  have ht₀ : flatProj m w₀ = Φ.toFun w₀ := by rw [hΦf, flatMap_eq_flatProj p hgen0]
  have ht₀R : flatProj m (L (ζ₀, z₀)) ∈ R := by
    rw [← hw₀eq, ht₀]
    refine ⟨Φ.mapsTo_toFun Φ.center_mem_source, ?_⟩
    simp only [mem_preimage, Φ.left_inv w₀ Φ.center_mem_source, mem_prod, mem_univ, true_and]
    rw [hw₀eq, ContinuousLinearEquiv.symm_apply_apply]
    exact hzV
  set κ : ComplexModel N × ComplexModel n → ComplexModel (N + n) :=
    fun q => flatProj m (L q) with hκ
  have hκc : Continuous κ := (flatProj m).continuous.comp L.continuous
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hRo.preimage hκc) (ζ₀, z₀) ht₀R
  have hmaps : ∀ ζ ∈ ball ζ₀ r, ∀ b ∈ ball z₀ r, flatProj m (L (ζ, b)) ∈ R := by
    intro ζ hζ b hb
    have : (ζ, b) ∈ ball (ζ₀, z₀) r := by
      rw [← ball_prod_same]
      exact ⟨hζ, hb⟩
    exact hball this
  refine ⟨⟨i, e, j, m, w₀, Φ, hΦs, hΦf, ζ₀, z₀, hw₀eq, r, hr, V, hVo, fun y hy => hy.2, ψ, h,
    hpsh, heqV, fun ζ hζ b hb => (hmaps ζ hζ b hb).1,
    fun ζ hζ b hb => ((hmaps ζ hζ b hb).2).2⟩, ?_⟩
  refine ⟨hq1, hq2, Φ.center_mem_source, mem_ball_self (half_pos hr), mem_ball_self hr⟩

namespace SliceChart

variable {p φ} (c : SliceChart n p φ)

/-- The `ζ` of the closed ball `K = closedBall ζ₀ (r/2)` for which `φ ≡ -∞` on the slice piece
`{point ζ b : b ∈ B ∩ Ω}` of the member `p⁻¹(H_{[insertNth i 1 ζ]})`. -/
def badSet (B : Set (ComplexModel n)) : Set (ComplexModel N) :=
  {ζ | ζ ∈ closedBall c.ζ₀ (c.r / 2) ∧ (B ∩ ball c.z₀ c.r).Nonempty ∧
    ∀ b ∈ B ∩ ball c.z₀ c.r, φ (c.point ζ b) = ⊥}

theorem flatProj_mem_target {ζ : ComplexModel N} {b : ComplexModel n} (hζ : ζ ∈ ball c.ζ₀ c.r)
    (hb : b ∈ ball c.z₀ c.r) : flatProj c.m (prodModelEquiv N n (ζ, b)) ∈ c.Φ.target :=
  c.mapsTo_target ζ hζ b hb

/-- For fixed `b ∈ Ω`, the slice `ζ ↦ slice ζ b` is holomorphic on `D`. -/
theorem differentiableOn_slice {b : ComplexModel n} (hb : b ∈ ball c.z₀ c.r) :
    DifferentiableOn ℂ (fun ζ => c.slice ζ b) (ball c.ζ₀ c.r) := by
  have hκ : Differentiable ℂ (fun ζ : ComplexModel N => flatProj c.m (prodModelEquiv N n (ζ, b))) :=
    (flatProj c.m).differentiable.comp
      ((prodModelEquiv N n).differentiable.comp (differentiable_id.prodMk (differentiable_const b)))
  have h1 : DifferentiableOn ℂ
      (fun ζ : ComplexModel N => c.Φ.invFun (flatProj c.m (prodModelEquiv N n (ζ, b))))
      (ball c.ζ₀ c.r) :=
    c.Φ.invFun_holomorphic.comp hκ.differentiableOn fun ζ hζ => c.flatProj_mem_target hζ hb
  exact (differentiable_snd.comp (prodModelEquiv N n).symm.differentiable).comp_differentiableOn h1

/-- For fixed `ζ ∈ D`, the slice point `b ↦ point ζ b` is continuous on `Ω`. -/
theorem continuousOn_point {ζ : ComplexModel N} (hζ : ζ ∈ ball c.ζ₀ c.r) :
    ContinuousOn (fun b => c.point ζ b) (ball c.z₀ c.r) := by
  have hκ : Continuous (fun b : ComplexModel n => flatProj c.m (prodModelEquiv N n (ζ, b))) :=
    (flatProj c.m).continuous.comp ((prodModelEquiv N n).continuous.comp
      (continuous_const.prodMk continuous_id))
  have h1 : ContinuousOn (fun b => c.slice ζ b) (ball c.z₀ c.r) := by
    have h2 : ContinuousOn
        (fun b : ComplexModel n => c.Φ.invFun (flatProj c.m (prodModelEquiv N n (ζ, b))))
        (ball c.z₀ c.r) :=
      c.Φ.invFun_holomorphic.continuousOn.comp hκ.continuousOn
        fun b hb => c.flatProj_mem_target hζ hb
    exact (continuous_snd.comp (prodModelEquiv N n).symm.continuous).comp_continuousOn h2
  exact c.e.val.continuousOn_symm.comp h1 fun b hb => c.V_subset (c.mapsTo_V ζ hζ b hb)

/-- **Nondegeneracy on slices**: if `φ` is not `-∞` on any open set, then for every nonempty open
`B ∩ Ω` there are `b ∈ B ∩ Ω` and `a ∈ D` with `ψ(slice a b) ≠ -∞`. The projection of the
incidence variety to `X` is open: near a point, the equation `G(ζ, z) = 0`, affine in `ζ` with a
nonzero coefficient of `ζ_k`, is solved by moving `ζ` along `e_k`. -/
theorem exists_psh_ne_bot (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hnd : LocallyNondegenerate φ) {B : Set (ComplexModel n)} (hB : IsOpen B)
    {b₁ : ComplexModel n} (hb₁ : b₁ ∈ B ∩ ball c.z₀ c.r) :
    ∃ b ∈ B ∩ ball c.z₀ c.r, ∃ a ∈ ball c.ζ₀ c.r, c.ψ (c.slice a b) ≠ ⊥ := by
  have hζ₀D : c.ζ₀ ∈ ball c.ζ₀ c.r := mem_ball_self c.r_pos
  set t₁ := flatProj c.m ((prodModelEquiv N n) (c.ζ₀, b₁)) with ht₁def
  have ht₁ : t₁ ∈ c.Φ.target := c.flatProj_mem_target hζ₀D hb₁.2
  set w₁ := c.Φ.invFun t₁ with hw₁def
  have hw₁s : w₁ ∈ c.Φ.source := c.Φ.mapsTo_invFun ht₁
  have hw₁V : w₁ ∈ conormalDomain p c.e c.j := c.source_subset hw₁s
  have hG₁ : conormalGenerator p c.i c.e c.j 0 w₁ = 0 := c.generator_invFun_flatProj ht₁
  have hfst₁ : ((prodModelEquiv N n).symm w₁).1 = c.ζ₀ := by
    rw [c.fst_invFun ht₁, fst_symm_flatProj, ContinuousLinearEquiv.symm_apply_apply]
  set z₁ := ((prodModelEquiv N n).symm w₁).2 with hz₁def
  have hw₁eq : w₁ = (prodModelEquiv N n) (c.ζ₀, z₁) := by
    rw [← hfst₁, hz₁def]
    simp
  have hz₁dom : z₁ ∈ chartLiftDomain p c.e c.j := hw₁V.2
  -- the flat coordinates of `w₁`
  have hflat₁ : flatProj c.m ((prodModelEquiv N n) (c.ζ₀, z₁)) = t₁ := by
    rw [← hw₁eq, ← flatMap_eq_flatProj p hG₁, ← c.toFun_eq, c.Φ.right_inv t₁ ht₁]
  have hb₁z₁ : z₁ + (b₁ c.m - z₁ c.m) • EuclideanSpace.single c.m 1 = b₁ := by
    have h := congrArg (fun w => (((prodModelEquiv N n).symm w).2)) hflat₁
    simp only [ht₁def, snd_symm_flatProj, slCoord_apply, ContinuousLinearEquiv.symm_apply_apply] at h
    calc z₁ + (b₁ c.m - z₁ c.m) • EuclideanSpace.single c.m (1 : ℂ)
        = (z₁ - z₁ c.m • EuclideanSpace.single c.m (1 : ℂ)) +
            b₁ c.m • EuclideanSpace.single c.m (1 : ℂ) := by rw [sub_smul]; abel
      _ = (b₁ - b₁ c.m • EuclideanSpace.single c.m (1 : ℂ)) +
            b₁ c.m • EuclideanSpace.single c.m (1 : ℂ) := by rw [h]
      _ = b₁ := by abel
  -- the local equation
  set g : ComplexModel n → ℂ := fun z => pairing (affineLift c.i c.ζ₀) (chartLift p c.e c.j z)
    with hgdef
  have hg₁ : g z₁ = 0 := by
    have := hG₁
    simp only [conormalGenerator, Fin.cons_zero, hfst₁] at this
    exact this
  obtain ⟨k, hk⟩ := exists_succAbove_ne_zero_of_pairing_eq_zero (affineLift_ne_zero c.j _) hg₁
  set cz : ComplexModel n → ℂ := fun z => chartLift p c.e c.j z (c.i.succAbove k) with hczdef
  set a : ComplexModel n → ComplexModel N :=
    fun z => c.ζ₀ - (g z / cz z) • EuclideanSpace.single k 1 with hadef
  set bb : ComplexModel n → ComplexModel n :=
    fun z => z + (b₁ c.m - z c.m) • EuclideanSpace.single c.m 1 with hbbdef
  have hgc : ContinuousAt g z₁ :=
    (hasFDerivAt_pairing_chartLift p hp hz₁dom _).differentiableAt.continuousAt
  have hczc : ContinuousAt cz z₁ := (differentiableAt_chartLift_apply p hp hz₁dom _).continuousAt
  have hac : ContinuousAt a z₁ :=
    continuousAt_const.sub ((hgc.div hczc hk).smul continuousAt_const)
  have hbbc : Continuous bb :=
    continuous_id.add ((continuous_const.sub
      ((EuclideanSpace.proj c.m : ComplexModel n →L[ℂ] ℂ).continuous)).smul continuous_const)
  have ha₁ : a z₁ = c.ζ₀ := by simp [hadef, hg₁]
  have hbb₁ : bb z₁ = b₁ := hb₁z₁
  have hLc : ContinuousAt (fun z => (prodModelEquiv N n) (a z, z)) z₁ :=
    (prodModelEquiv N n).continuous.continuousAt.comp (hac.prodMk continuousAt_id)
  have e1 : ∀ᶠ z in 𝓝 z₁, z ∈ chartLiftDomain p c.e c.j :=
    (isOpen_chartLiftDomain p hp c.e c.j).mem_nhds hz₁dom
  have e2 : ∀ᶠ z in 𝓝 z₁, cz z ≠ 0 := hczc.eventually_ne hk
  have e3 : ∀ᶠ z in 𝓝 z₁, a z ∈ ball c.ζ₀ c.r :=
    hac.eventually (isOpen_ball.mem_nhds (ha₁ ▸ hζ₀D))
  have e4 : ∀ᶠ z in 𝓝 z₁, bb z ∈ B ∩ ball c.z₀ c.r :=
    hbbc.continuousAt.eventually ((hB.inter isOpen_ball).mem_nhds (hbb₁ ▸ hb₁))
  have e5 : ∀ᶠ z in 𝓝 z₁, (prodModelEquiv N n) (a z, z) ∈ c.Φ.source := by
    refine hLc.eventually (c.Φ.isOpen_source.mem_nhds ?_)
    change (prodModelEquiv N n) (a z₁, z₁) ∈ c.Φ.source
    rw [ha₁, ← hw₁eq]
    exact hw₁s
  have hev : ∀ᶠ z in 𝓝 z₁, z ∈ chartLiftDomain p c.e c.j ∧ cz z ≠ 0 ∧ a z ∈ ball c.ζ₀ c.r ∧
      bb z ∈ B ∩ ball c.z₀ c.r ∧ (prodModelEquiv N n) (a z, z) ∈ c.Φ.source :=
    e1.and (e2.and (e3.and (e4.and e5)))
  obtain ⟨O, hO, hOo, hz₁O⟩ := _root_.eventually_nhds_iff.mp hev
  -- a point of `X` near `x₁ = e⁻¹ z₁` where `φ ≠ -∞`
  have hz₁t : z₁ ∈ c.e.val.target := hz₁dom.1
  obtain ⟨y, hy, hφy⟩ := hnd (c.e.val.symm z₁) (c.e.val.source ∩ c.e.val ⁻¹' O)
    (c.e.val.isOpen_inter_preimage hOo)
    ⟨c.e.val.map_target hz₁t, by
      simp only [mem_preimage, c.e.val.right_inv hz₁t]
      exact hz₁O⟩
  set z := c.e.val y with hzdef
  obtain ⟨hzdom, hcz, haD, hbbB, hLs⟩ := hO z hy.2
  -- `(a z, z)` lies on the incidence variety and has flat coordinates `(a z, bb z)`
  have hGz : conormalGenerator p c.i c.e c.j 0 ((prodModelEquiv N n) (a z, z)) = 0 := by
    simp only [conormalGenerator, Fin.cons_zero, ContinuousLinearEquiv.symm_apply_apply, hadef]
    rw [pairing_affineLift_sub_smul_single]
    change g z - cz z * (g z / cz z) = 0
    field_simp
    ring
  have hflat : flatProj c.m ((prodModelEquiv N n) (a z, bb z)) = c.Φ.toFun ((prodModelEquiv N n) (a z, z)) := by
    rw [c.toFun_eq, flatMap_eq_flatProj p hGz, hbbdef]
    exact flatProj_prod_update c.m (a z) z _
  have hslice : c.slice (a z) (bb z) = z := by
    simp only [slice, hflat, c.Φ.left_inv _ hLs, ContinuousLinearEquiv.symm_apply_apply]
  have hzV : z ∈ c.V := hslice ▸ c.mapsTo_V (a z) haD (bb z) hbbB.2
  refine ⟨bb z, hbbB, a z, haD, ?_⟩
  rw [hslice]
  intro hψ
  apply hφy
  have := c.eq_add z hzV
  rw [hzdef, c.e.val.left_inv hy.1] at this
  rw [this, hψ, EReal.bot_add]

/-- **The product-slice lemma** (blueprint `claude-bertini:product-slice`): if `φ` is not `-∞` on
any open subset of `X` and `B` is open, the set of hyperplanes `[insertNth i 1 ζ]`, `ζ ∈ badSet B`,
is pluripolar in `Λ`. -/
theorem locallyPluripolar_image_badSet
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hnd : LocallyNondegenerate φ) {B : Set (ComplexModel n)} (hB : IsOpen B) :
    (SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar
      ((affineChart c.i).symm '' c.badSet B) := by
  apply SGPT.PSH.VariableComplexAtlas.locallyPluripolar_of_in_chart
    (A := SGPT.PSH.VariableComplexAtlas.ofFixedModel N (HyperplaneSpace N))
  intro e'
  by_cases hne : (B ∩ ball c.z₀ c.r).Nonempty
  · obtain ⟨b, hbB, a, ha, hψa⟩ := c.exists_psh_ne_bot hp hnd hB hne.some_mem
    set v : ComplexModel N → EReal := fun ζ => c.ψ (c.slice ζ b) with hv
    have hvpsh : PlurisubharmonicOn v (ball c.ζ₀ c.r) :=
      HolomorphicPullback.plurisubharmonicOn_comp_holomorphic isOpen_ball
        (c.differentiableOn_slice hbB.2) (fun ζ hζ => c.mapsTo_V ζ hζ b hbB.2) c.psh
    have hpoles := hvpsh.locallyPluripolarOn_poles isOpen_ball (convex_ball _ _).isPreconnected
      ⟨a, ha, hψa⟩
    have hKD : closedBall c.ζ₀ (c.r / 2) ⊆ ball c.ζ₀ c.r :=
      closedBall_subset_ball (half_lt_self c.r_pos)
    have himg := SGPT.PSH.manifoldLocallyPluripolar_chartImage (affineComplexChart c.i)
      (isCompact_closedBall c.ζ₀ (c.r / 2)) (by simp [affineComplexChart])
      (fun z hz => hpoles z (hKD hz))
    refine (himg.mono ?_) e'
    rintro _ ⟨ζ, hζ, rfl⟩
    refine ⟨ζ, ⟨?_, hζ.1⟩, rfl⟩
    have h1 := hζ.2.2 b hbB
    have hsV := c.mapsTo_V ζ (hKD hζ.1) b hbB.2
    change c.ψ (c.slice ζ b) = ⊥
    have h2 := c.eq_add (c.slice ζ b) hsV
    rw [show c.e.val.symm (c.slice ζ b) = c.point ζ b from rfl, h1] at h2
    rcases EReal.add_eq_bot_iff.mp h2.symm with h | h
    · exact h
    · exact absurd h (EReal.coe_ne_bot _)
  · have hempty : (affineChart c.i).symm '' c.badSet B = ∅ := by
      rw [image_eq_empty]
      ext ζ
      simp only [badSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun _ h => absurd h hne
    rw [hempty]
    exact manifoldLocallyPluripolar_empty (n := N) e'

/-- **Covering by the slice sets**: if `(ℓ, x)` lies in the domain of the chart, `x ∈ p⁻¹(H_ℓ)`
and `φ ≡ -∞` on `W ∩ p⁻¹(H_ℓ)` for an open `W ∋ x`, then `ℓ` lies in the image of `badSet B` for
some `B` of the countable basis of `ℂⁿ`. -/
theorem exists_mem_image_badSet {q : HyperplaneSpace N × X} (hq : q ∈ c.domain) (hmem : q.2 ∈ member p q.1) {W : Set X}
    (hW : IsOpen W) (hqW : q.2 ∈ W) (hpole : ∀ y ∈ W ∩ member p q.1, φ y = ⊥) :
    ∃ B ∈ TopologicalSpace.countableBasis (ComplexModel n),
      q.1 ∈ (affineChart c.i).symm '' c.badSet B := by
  obtain ⟨hq1, hq2, hqΦ, hζ, hz⟩ := hq
  set ζ := affineChart c.i q.1 with hζdef
  set z := c.e.val q.2 with hzdef
  have hw : prodChart (affineChart c.i) c.e.val q = (prodModelEquiv N n) (ζ, z) := rfl
  have hwV := c.source_subset hqΦ
  have hqj : p q.2 ∈ (affineChart c.j).source := (prodChart_mem_conormalDomain_iff p hq2).mp hwV
  have hG : conormalGenerator p c.i c.e c.j 0 ((prodModelEquiv N n) (ζ, z)) = 0 := by
    rw [← hw]
    exact (conormalGenerator_zero_prodChart_eq_zero_iff p hq1 hq2 hqj).mpr hmem
  have hζD : ζ ∈ ball c.ζ₀ c.r := ball_subset_ball (half_le_self c.r_pos.le) hζ
  have hpt : c.point ζ z = q.2 := by
    have h1 : flatProj c.m ((prodModelEquiv N n) (ζ, z)) = c.Φ.toFun ((prodModelEquiv N n) (ζ, z)) := by
      rw [c.toFun_eq, flatMap_eq_flatProj p hG]
    simp only [point, slice, h1, c.Φ.left_inv _ (hw ▸ hqΦ), ContinuousLinearEquiv.symm_apply_apply]
    exact c.e.val.left_inv hq2
  set B' := ball c.z₀ c.r ∩ (fun b => c.point ζ b) ⁻¹' W with hB'
  have hB'o : IsOpen B' := (c.continuousOn_point hζD).isOpen_inter_preimage isOpen_ball hW
  have hzB' : z ∈ B' := ⟨hz, by simp only [mem_preimage, hpt]; exact hqW⟩
  obtain ⟨B, hB, hzB, hBB'⟩ :=
    (TopologicalSpace.isBasis_countableBasis (ComplexModel n)).exists_subset_of_mem_open hzB' hB'o
  refine ⟨B, hB, ζ, ⟨ball_subset_closedBall hζ, ⟨z, hzB, hz⟩, fun b hb => ?_⟩, ?_⟩
  · have hbW : c.point ζ b ∈ W := (hBB' hb.1).2
    have hbM := c.point_mem_member hζD hb.2
    have hℓ : affinePoint c.i ζ = q.1 := (affineChart c.i).left_inv hq1
    rw [hℓ] at hbM
    exact hpole _ ⟨hbW, hbM⟩
  · exact (affineChart c.i).left_inv hq1

end SliceChart

end SliceChart

end SGPT.Trace.Bertini
