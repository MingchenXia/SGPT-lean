import SGPT.Unibranch.FNAInterface
import SGPT.Foundations.Analysis.Pending.HironakaDimensionGlobalComponents
import SGPT.Foundations.Analysis.Pending.HironakaG8MemberLoci

/-!
# Reduction of the local Fornæss--Narasimhan theorem to pure-dimensional sets

Source: [FN80] Theorem 5.3.1 (Fornæss--Narasimhan, *The Levi problem on complex spaces with
singularities*, Math. Ann. 248 (1980)), used for SGPT `thm:FN` (`appendix_unibranch.tex`).
[FN80, Lemma 5.2] and the Runge half of Theorem 5.3.1 need a *pure-dimensional* set (a branched
covering); [FN80] treat the pure-dimensional pieces `S_j` of `X` separately and glue them by the
theorem that a space is Stein iff its normalization is. We avoid that gluing by a **suspension**:
for `X` analytic in an open set `Ω ⊆ ℂⁿ` with dimension parts `X⁽ᵏ⁾` (SGPT.Foundations.Analysis
`dimensionPart`, analytic, pure `k`-dimensional, `X = ⋃ₖ X⁽ᵏ⁾`) put

  `X̃ = ⋃ₖ X⁽ᵏ⁾ × Lₖ ⊆ ℂⁿ × ℂⁿ`,  `Lₖ = ℂ^{n-k} × 0` (`complexCoordinatePlane n (n - k)`).

Then `X̃` is pure `n`-dimensional (`isPureDim_suspension`): near a `k`-regular point `z` of `X`
off the other parts, `X̃` is the product of a `k`-dimensional manifold with `Lₖ`, and such points
are dense in `X⁽ᵏ⁾`. The first projection maps `X̃` onto `X`, `x ↦ (x, 0)` is a section, so for
`φ ∈ WP(X)` the function `φ ∘ pr₁` lies in `WP(X̃)`, and an ambient extension `ψ̃` of `φ ∘ pr₁`
near `(a, 0)` gives the ambient extension `ψ = ψ̃(·, 0)` of `φ` near `a`.

Main results:

* `LocalFNExtensionPure`: the local [FN80] theorem for pure-dimensional `X` (SGPT.Foundations.Analysis
  `AnalyticDimensionBasics.IsPureDim`: every regular point of `X` has dimension `d`).
* `extension_of_pure`: `LocalFNExtensionPure` gives the local extension for every analytic subset
  of an open set of `ℂⁿ` (intersected with a polydisc in it).
* `localFNExtension_of_pure : LocalFNExtensionPure → LocalFNExtension`.
* Auxiliary: `regularAtDim_prod` (products with coordinate planes), `isPureDim_suspension`,
  `hasLocalEquationsOn_iUnion`, `HasLocalEquationsOn.inter`, `HasLocalEquationsOn.preimage`,
  `isComplexAnalyticSubset_of_hasLocalEquationsOn`, `FNL.IsWeaklyPSHOn` along linear maps.
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology Manifold

noncomputable section

namespace SGPT.Unibranch.FNA

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

-- `Fin.natAdd n i = i.addNat n` (for `i : Fin n`) would hide `Fin.append_right`.
attribute [-simp] Fin.natAdd_eq_addNat

/-! ### Two blocks of coordinates `ℂⁿ × ℂⁿ = ℂ^{n+n}` -/

section Blocks

variable {n : ℕ}

/-- The first block of coordinates of `ℂ^{n+n}`. -/
def blk1 : ComplexModel (n + n) →L[ℂ] ComplexModel n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun i => w (Fin.castAdd n i))
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp }

/-- The second block of coordinates of `ℂ^{n+n}`. -/
def blk2 : ComplexModel (n + n) →L[ℂ] ComplexModel n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2 (fun i => w (Fin.natAdd n i))
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun _ _ => by ext; simp }

/-- `x ↦ (x, 0)`. -/
def inl : ComplexModel n →L[ℂ] ComplexModel (n + n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (Fin.append (fun i => x i) (fun _ => 0))
      map_add' := fun x y => by
        ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
      map_smul' := fun c x => by
        ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp }

/-- `t ↦ (0, t)`. -/
def inr : ComplexModel n →L[ℂ] ComplexModel (n + n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t => WithLp.toLp 2 (Fin.append (fun _ => 0) (fun i => t i))
      map_add' := fun x y => by
        ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
      map_smul' := fun c x => by
        ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp }

/-- The point `(x, t)` of `ℂ^{n+n}`. -/
def glue (x t : ComplexModel n) : ComplexModel (n + n) := inl x + inr t

@[simp] theorem blk1_apply (w : ComplexModel (n + n)) (i : Fin n) :
    blk1 w i = w (Fin.castAdd n i) := rfl

@[simp] theorem blk2_apply (w : ComplexModel (n + n)) (i : Fin n) :
    blk2 w i = w (Fin.natAdd n i) := rfl

@[simp] theorem inl_castAdd (x : ComplexModel n) (i : Fin n) : inl x (Fin.castAdd n i) = x i := by
  simp [inl]

@[simp] theorem inl_natAdd (x : ComplexModel n) (i : Fin n) : inl x (Fin.natAdd n i) = 0 := by
  simp [inl]

@[simp] theorem inr_castAdd (t : ComplexModel n) (i : Fin n) : inr t (Fin.castAdd n i) = 0 := by
  simp [inr]

@[simp] theorem inr_natAdd (t : ComplexModel n) (i : Fin n) : inr t (Fin.natAdd n i) = t i := by
  simp [inr]

@[simp] theorem glue_castAdd (x t : ComplexModel n) (i : Fin n) :
    glue x t (Fin.castAdd n i) = x i := by
  simp [glue]

@[simp] theorem glue_natAdd (x t : ComplexModel n) (i : Fin n) :
    glue x t (Fin.natAdd n i) = t i := by
  simp [glue]

@[simp] theorem blk1_glue (x t : ComplexModel n) : blk1 (glue x t) = x := by
  ext i
  simp

@[simp] theorem blk2_glue (x t : ComplexModel n) : blk2 (glue x t) = t := by
  ext i
  simp

@[simp] theorem glue_blk (w : ComplexModel (n + n)) : glue (blk1 w) (blk2 w) = w := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

theorem inl_eq_glue (x : ComplexModel n) : inl x = glue x 0 := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

@[simp] theorem blk1_inl (x : ComplexModel n) : blk1 (inl x) = x := by
  rw [inl_eq_glue, blk1_glue]

@[simp] theorem blk2_inl (x : ComplexModel n) : blk2 (inl x) = 0 := by
  rw [inl_eq_glue, blk2_glue]

@[simp] theorem glue_zero : glue (0 : ComplexModel n) 0 = 0 := by
  simp [glue]

theorem continuous_glue_left (t : ComplexModel n) : Continuous fun x : ComplexModel n => glue x t :=
  inl.continuous.add continuous_const

end Blocks

/-! ### Products with coordinate planes are regular -/

section Regular

variable {n : ℕ}

open AnalyticDimensionBasics RegularPointDimension NormalCrossings

/-- The local biholomorphism `(x, s) ↦ (Φ x, s - t)` of `ℂ^{n+n}`. -/
def prodEquiv {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p) (t : ComplexModel n)
    (q : ComplexModel (n + n)) (hq : blk1 q = p) : LocalHolomorphicEquivAt (n := n + n) q where
  source := blk1 ⁻¹' Φ.source
  target := blk1 ⁻¹' Φ.target
  isOpen_source := Φ.isOpen_source.preimage blk1.continuous
  isOpen_target := Φ.isOpen_target.preimage blk1.continuous
  center_mem_source := by
    rw [mem_preimage, hq]
    exact Φ.center_mem_source
  toFun w := glue (Φ.toFun (blk1 w)) (blk2 w - t)
  invFun w := glue (Φ.invFun (blk1 w)) (blk2 w + t)
  toFun_holomorphic := by
    have h1 : DifferentiableOn ℂ (fun w => Φ.toFun (blk1 w)) (blk1 ⁻¹' Φ.source) :=
      Φ.toFun_holomorphic.comp blk1.differentiable.differentiableOn (fun _ hw => hw)
    exact (inl.differentiable.comp_differentiableOn h1).add
      (inr.differentiable.comp_differentiableOn
        ((blk2.differentiable.sub_const t).differentiableOn))
  invFun_holomorphic := by
    have h1 : DifferentiableOn ℂ (fun w => Φ.invFun (blk1 w)) (blk1 ⁻¹' Φ.target) :=
      Φ.invFun_holomorphic.comp blk1.differentiable.differentiableOn (fun _ hw => hw)
    exact (inl.differentiable.comp_differentiableOn h1).add
      (inr.differentiable.comp_differentiableOn
        ((blk2.differentiable.add_const t).differentiableOn))
  mapsTo_toFun w hw := by
    simp only [mem_preimage, blk1_glue]
    exact Φ.mapsTo_toFun hw
  mapsTo_invFun w hw := by
    simp only [mem_preimage, blk1_glue]
    exact Φ.mapsTo_invFun hw
  left_inv w hw := by
    simp only [blk1_glue, blk2_glue, sub_add_cancel]
    rw [Φ.left_inv _ hw, glue_blk]
  right_inv w hw := by
    simp only [blk1_glue, blk2_glue, add_sub_cancel_right]
    rw [Φ.right_inv _ hw, glue_blk]

theorem complexChartAt_model_apply {m : ℕ} (x y : ComplexModel m) :
    (complexChartAt (n := m) x).val y = y := by
  simp [complexChartAt, chartAt_self_eq]

theorem complexChartAt_model_source {m : ℕ} (x : ComplexModel m) :
    (complexChartAt (n := m) x).val.source = univ := by
  simp [complexChartAt, chartAt_self_eq]

theorem complexChartAt_model_target {m : ℕ} (x : ComplexModel m) :
    (complexChartAt (n := m) x).val.target = univ := by
  simp [complexChartAt, chartAt_self_eq]

theorem card_filter_le_val (n m : ℕ) :
    (Finset.univ.filter (fun i : Fin n => m ≤ i.val)).card = n - m := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i : Fin n => (i : ℕ) < m)
  have h1 : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < m)).card = min n m :=
    Fin.card_filter_val_lt
  simp only [Finset.card_univ, Fintype.card_fin, not_lt] at h
  omega

/-- **Products with coordinate planes.** If `A ⊆ ℂⁿ` is regular of dimension `k` at `z`, then
`A × (ℂ^{n-k} × 0) ⊆ ℂ^{n+n}` is regular of dimension `n` at every point `(z, t)`. -/
theorem regularAtDim_prod {A : Set (ComplexModel n)} {z : ComplexModel n} {k : ℕ}
    (hz : RegularAtDim (n := n) (M := ComplexModel n) A z k) {t : ComplexModel n}
    (ht : t ∈ complexCoordinatePlane n (n - k)) :
    RegularAtDim (n := n + n) (M := ComplexModel (n + n))
      {w | blk1 w ∈ A ∧ blk2 w ∈ complexCoordinatePlane n (n - k)} (glue z t) n := by
  classical
  obtain ⟨hkn, -, Φ, -, hΦ0, hflat⟩ := hz
  have hcz : (complexChartAt (n := n) z).val z = z := complexChartAt_model_apply z z
  set q := (complexChartAt (n := n + n) (glue z t)).val (glue z t) with hqdef
  have hq : q = glue z t := complexChartAt_model_apply _ _
  have hq1 : blk1 q = (complexChartAt (n := n) z).val z := by rw [hq, blk1_glue, hcz]
  set T : Finset (Fin (n + n)) :=
    (Finset.univ.filter (fun i : Fin n => k ≤ i.val)).map (Fin.castAddEmb n) ∪
      (Finset.univ.filter (fun i : Fin n => n - k ≤ i.val)).map (Fin.natAddEmb n) with hT
  have hdisj : Disjoint ((Finset.univ.filter (fun i : Fin n => k ≤ i.val)).map (Fin.castAddEmb n))
      ((Finset.univ.filter (fun i : Fin n => n - k ≤ i.val)).map (Fin.natAddEmb n)) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
    obtain ⟨i₁, -, rfl⟩ := hj1
    obtain ⟨i₂, -, h⟩ := hj2
    have h' := congrArg Fin.val h
    simp only [Fin.natAddEmb_apply, Fin.val_natAdd, Fin.castAddEmb_apply, Fin.val_castAdd] at h'
    omega
  have hTcard : T.card = n := by
    rw [hT, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
      card_filter_le_val, card_filter_le_val]
    omega
  have hmemT : ∀ v : ComplexModel (n + n), v ∈ coordSubspace T ↔
      (∀ i : Fin n, k ≤ i.val → v (Fin.castAdd n i) = 0) ∧
        (∀ i : Fin n, n - k ≤ i.val → v (Fin.natAdd n i) = 0) := by
    intro v
    simp only [coordSubspace, mem_ofPred_eq, hT, Finset.mem_union, Finset.mem_map,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨fun i hi => h _ (Or.inl ⟨i, hi, rfl⟩), fun i hi => h _ (Or.inr ⟨i, hi, rfl⟩)⟩
    · rintro ⟨h1, h2⟩ j (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact h1 i hi
      · exact h2 i hi
  have hres := HironakaG8MemberLoci.regularAtDim_of_flat_coordSubspace
    (M := ComplexModel (n + n))
    (B := {w | blk1 w ∈ A ∧ blk2 w ∈ complexCoordinatePlane n (n - k)}) (x := glue z t) (T := T)
    (prodEquiv Φ t q hq1) (by rw [complexChartAt_model_target]; exact subset_univ _) ?_ ?_
  · rwa [hTcard, Nat.add_sub_cancel] at hres
  · change glue (Φ.toFun (blk1 q)) (blk2 q - t) = 0
    rw [hq1, hΦ0, hq, blk2_glue, sub_self, glue_zero]
  · intro y _ hyΦ
    change blk1 ((complexChartAt (n := n + n) (glue z t)).val y) ∈ Φ.source at hyΦ
    rw [complexChartAt_model_apply (glue z t) y] at hyΦ
    change (y ∈ {w | blk1 w ∈ A ∧ blk2 w ∈ complexCoordinatePlane n (n - k)}) ↔
      glue (Φ.toFun (blk1 ((complexChartAt (n := n + n) (glue z t)).val y)))
        (blk2 ((complexChartAt (n := n + n) (glue z t)).val y) - t) ∈ coordSubspace T
    rw [complexChartAt_model_apply (glue z t) y]
    have hA := hflat (y := blk1 y) (by rw [complexChartAt_model_source]; exact mem_univ _)
      (by rw [complexChartAt_model_apply z (blk1 y)]; exact hyΦ)
    rw [complexChartAt_model_apply z (blk1 y)] at hA
    change (blk1 y ∈ A ∧ blk2 y ∈ complexCoordinatePlane n (n - k)) ↔ _
    rw [hmemT, hA]
    simp only [glue_castAdd, glue_natAdd, complexCoordinatePlane, mem_ofPred_eq]
    have htz : ∀ i : Fin n, n - k ≤ i.val → t i = 0 := fun i hi => ht i hi
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun i hi => ?_⟩
      rw [PiLp.sub_apply, h2 i hi, htz i hi, sub_zero]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun i hi => ?_⟩
      have := h2 i hi
      rw [PiLp.sub_apply, htz i hi, sub_zero] at this
      exact this

end Regular

/-! ### The suspension is pure-dimensional -/

section Suspension

variable {n : ℕ}

open AnalyticDimensionBasics RegularPointDimension

/-- The suspension `⋃ₖ Sₖ × (ℂ^{n-k} × 0) ⊆ ℂ^{n+n}` of a family of pieces `Sₖ ⊆ ℂⁿ`. -/
def suspension (S : Fin (n + 1) → Set (ComplexModel n)) : Set (ComplexModel (n + n)) :=
  {w | ∃ k : Fin (n + 1), blk1 w ∈ S k ∧ blk2 w ∈ complexCoordinatePlane n (n - k)}

theorem blk1_mem_of_mem_suspension {S : Fin (n + 1) → Set (ComplexModel n)}
    {w : ComplexModel (n + n)} (hw : w ∈ suspension S) : blk1 w ∈ ⋃ k, S k := by
  obtain ⟨k, hk, -⟩ := hw
  exact mem_iUnion.mpr ⟨k, hk⟩

theorem inl_mem_suspension {S : Fin (n + 1) → Set (ComplexModel n)} {x : ComplexModel n}
    (hx : x ∈ ⋃ k, S k) : inl x ∈ suspension S := by
  obtain ⟨k, hk⟩ := mem_iUnion.mp hx
  refine ⟨k, by rwa [blk1_inl], ?_⟩
  rw [blk2_inl]
  intro i _
  rfl

/-- **The suspension is pure `n`-dimensional**, provided every piece `Sₖ` is the closure of
points at which `⋃ S` is regular of dimension `k` and which have a neighbourhood meeting no other
piece. -/
theorem isPureDim_suspension (S : Fin (n + 1) → Set (ComplexModel n))
    (hS : ∀ (k : Fin (n + 1)) (y : ComplexModel n), y ∈ S k → ∀ U ∈ 𝓝 y, ∃ z ∈ U, z ∈ S k ∧
      RegularAtDim (n := n) (M := ComplexModel n) (⋃ k, S k) z k ∧
      ∀ᶠ z' in 𝓝 z, ∀ k', z' ∈ S k' → k' = k) :
    IsPureDim (n := n + n) (M := ComplexModel (n + n)) (suspension S) n := by
  intro p j hp
  obtain ⟨k, hpk, hpt⟩ := hp.2.1
  have hev := RegularPatchNeighborhood.eventually_regularAtDim hp
  have hU : (fun x : ComplexModel n => glue x (blk2 p)) ⁻¹'
      {q | q ∈ suspension S → RegularAtDim (n := n + n) (suspension S) q j} ∈ 𝓝 (blk1 p) := by
    apply (continuous_glue_left (blk2 p)).continuousAt.preimage_mem_nhds
    rw [glue_blk]
    exact hev
  obtain ⟨z, hzU, hzS, hzreg, hznbhd⟩ := hS k (blk1 p) hpk _ hU
  have hq : glue z (blk2 p) ∈ suspension S := ⟨k, by rwa [blk1_glue], by rwa [blk2_glue]⟩
  have hqj : RegularAtDim (n := n + n) (suspension S) (glue z (blk2 p)) j := hzU hq
  -- near `glue z t` the suspension is `(⋃ S) × L_k`
  obtain ⟨V, hVsub, hVo, hzV⟩ := _root_.mem_nhds_iff.mp hznbhd
  have hW : IsOpen (blk1 ⁻¹' V) := hVo.preimage blk1.continuous
  have hqW : glue z (blk2 p) ∈ blk1 ⁻¹' V := by
    rw [mem_preimage, blk1_glue]
    exact hzV
  have hqn : RegularAtDim (n := n + n) (suspension S) (glue z (blk2 p)) n := by
    refine regularAtDim_of_inter_eq hW hqW ?_ (regularAtDim_prod hzreg hpt)
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, suspension]
    constructor
    · rintro ⟨⟨hw1, hw2⟩, hwV⟩
      obtain ⟨k', hk'⟩ := mem_iUnion.mp hw1
      have := hVsub hwV k' hk'
      subst this
      exact ⟨⟨k', hk', hw2⟩, hwV⟩
    · rintro ⟨⟨k', hk', hw2⟩, hwV⟩
      have := hVsub hwV k' hk'
      subst this
      exact ⟨⟨mem_iUnion.mpr ⟨k', hk'⟩, hw2⟩, hwV⟩
  exact eq_of_regularAtDim hqj hqn

end Suspension

/-! ### Local equations -/

section Equations

variable {n m : ℕ}

theorem hasLocalEquationsOn_inter_sets {X Y Ω : Set (ComplexModel n)} (hX : FNR.HasLocalEquationsOn X Ω)
    (hY : FNR.HasLocalEquationsOn Y Ω) : FNR.HasLocalEquationsOn (X ∩ Y) Ω := by
  intro x hx
  obtain ⟨W₁, hW₁, hxW₁, N₁, g₁, hg₁, h₁⟩ := hX x hx
  obtain ⟨W₂, hW₂, hxW₂, N₂, g₂, hg₂, h₂⟩ := hY x hx
  refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hxW₁, hxW₂⟩, N₁ + N₂,
    fun i => Fin.append g₁ g₂ i, fun i => ?_, fun y hy => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using (hg₁ i).mono inter_subset_left
    · simpa using (hg₂ i).mono inter_subset_right
  · rw [mem_inter_iff, h₁ y hy.1, h₂ y hy.2]
    constructor
    · rintro ⟨ha, hb⟩ i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using ha i
      · simpa using hb i
    · intro h
      exact ⟨fun i => by simpa using h (Fin.castAdd N₂ i),
        fun i => by simpa using h (Fin.natAdd N₁ i)⟩

theorem hasLocalEquationsOn_preimage {X Ω : Set (ComplexModel n)}
    (hX : FNR.HasLocalEquationsOn X Ω) (L : ComplexModel m →L[ℂ] ComplexModel n) :
    FNR.HasLocalEquationsOn (L ⁻¹' X) (L ⁻¹' Ω) := by
  intro x hx
  obtain ⟨W, hW, hxW, N, g, hg, h⟩ := hX (L x) hx
  refine ⟨L ⁻¹' W, hW.preimage L.continuous, hxW, N, fun i y => g i (L y), fun i => ?_,
    fun y hy => h (L y) hy⟩
  exact (hg i).comp L.differentiable.differentiableOn (fun _ hy => hy)

theorem hasLocalEquationsOn_of_global {Ω : Set (ComplexModel n)} {N : ℕ}
    {g : Fin N → ComplexModel n → ℂ} (hg : ∀ i, Differentiable ℂ (g i)) :
    FNR.HasLocalEquationsOn {y | ∀ i, g i y = 0} Ω :=
  fun _ _ => ⟨univ, isOpen_univ, mem_univ _, N, g, fun i => (hg i).differentiableOn,
    fun _ _ => Iff.rfl⟩

/-- Finite unions of sets with local equations have local equations (products of equations). -/
theorem hasLocalEquationsOn_iUnion {ι : Type*} [Fintype ι] {X : ι → Set (ComplexModel n)}
    {Ω : Set (ComplexModel n)} (hX : ∀ i, FNR.HasLocalEquationsOn (X i) Ω) :
    FNR.HasLocalEquationsOn (⋃ i, X i) Ω := by
  classical
  intro x hx
  choose W hW hxW N g hg h using fun i => hX i x hx
  let σT := (i : ι) → Fin (N i)
  let e := Fintype.equivFin σT
  refine ⟨⋂ i, W i, isOpen_iInter_of_finite hW, mem_iInter.mpr hxW, Fintype.card σT,
    fun l y => ∏ i, g i (e.symm l i) y, fun l => ?_, fun y hy => ?_⟩
  · show DifferentiableOn ℂ (fun y => ∏ i, g i (e.symm l i) y) _
    refine PureDimension.differentiableOn_finset_prod Finset.univ
      (fun i => g i (e.symm l i)) _ fun i _ => ?_
    exact (hg i _).mono (iInter_subset _ i)
  · have hyW : ∀ i, y ∈ W i := mem_iInter.mp hy
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩ l
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact (h i y (hyW i)).mp hi _
    · intro hall
      by_contra hne
      push Not at hne
      have hne' : ∀ i, ∃ j, g i j y ≠ 0 := by
        intro i
        by_contra hc
        push Not at hc
        exact hne i ((h i y (hyW i)).mpr hc)
      choose σ hσ using hne'
      have := hall (e σ)
      rw [Equiv.symm_apply_apply] at this
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hσ i) this

theorem hasLocalEquationsOn_mono_set {X Ω Ω' : Set (ComplexModel n)}
    (hX : FNR.HasLocalEquationsOn X Ω) (hΩ : Ω' ⊆ Ω) : FNR.HasLocalEquationsOn X Ω' :=
  hX.mono hΩ

/-- A set with local equations on an open polydisc (or any open `Ω`), viewed inside the manifold
`Ω`, is an analytic subset. -/
theorem isComplexAnalyticSubset_of_hasLocalEquationsOn {Ω : Opens (ComplexModel n)}
    {X : Set (ComplexModel n)} (hX : FNR.HasLocalEquationsOn X Ω) :
    IsComplexAnalyticSubset (n := n) ((Subtype.val : Ω → ComplexModel n) ⁻¹' X) := by
  intro x
  obtain ⟨W, hW, hxW, N, g, hg, h⟩ := hX x.val x.property
  have happly : ∀ y : Ω, (complexChartAt (n := n) x).val y = y.val := fun y => by
    change chartAt (ComplexModel n) (x : ComplexModel n) y = y.val
    simp [chartAt_self_eq]
  refine ⟨{ generatorCount := N
            generator := g
            coordinateNeighborhood := W ∩ (complexChartAt (n := n) x).val.target
            isOpen_coordinateNeighborhood := hW.inter (complexChartAt (n := n) x).val.open_target
            center_mem_coordinateNeighborhood := ⟨by rw [happly]; exact hxW,
              (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)⟩
            coordinateNeighborhood_subset_target := inter_subset_right
            generator_holomorphic := fun i => (hg i).mono inter_subset_left
            zeroLocus := ?_ }⟩
  intro y _ hy
  rw [happly] at hy ⊢
  exact h y.val hy.1

end Equations

/-! ### Weak plurisubharmonicity along linear maps -/

theorem isWeaklyPSHOn_comp {n m : ℕ} {X : Set (ComplexModel n)} {φ : ComplexModel n → EReal}
    (hφ : FNL.IsWeaklyPSHOn X φ) (L : ComplexModel m →L[ℂ] ComplexModel n)
    {Y : Set (ComplexModel m)} (hY : MapsTo L Y X) :
    FNL.IsWeaklyPSHOn Y (fun y => φ (L y)) :=
  ⟨fun _ hy => hφ.ne_top _ (hY hy), hφ.upperSemicontinuousOn.comp L.continuous.continuousOn hY,
    fun f hf hfY => hφ.disc (fun t => L (f t)) (L.differentiable.comp_differentiableOn hf)
      (fun _ ht => hY (hfY ht))⟩

/-! ### The reduction -/

/-- **`[FN80]` Theorem 5.3.1, local form, for pure-dimensional sets.** As `LocalFNExtension`,
with the additional hypothesis that `X` is pure-dimensional (every regular point of `X` has the
same dimension `d`, SGPT.Foundations.Analysis `AnalyticDimensionBasics.IsPureDim`). -/
def LocalFNExtensionPure : Prop :=
  ∀ (n : ℕ) (X : Set (ComplexModel n)) (a : ComplexModel n) (r : Fin n → ℝ) (d : ℕ)
    (φ : ComplexModel n → EReal),
    (∀ i, 0 < r i) → X ⊆ polydisc a r → FNR.HasLocalEquationsOn X (polydisc a r) →
    AnalyticDimensionBasics.IsPureDim (n := n) (M := ComplexModel n) X d → a ∈ X →
    FNL.IsWeaklyPSHOn X φ →
    ∃ W : Set (ComplexModel n), IsOpen W ∧ a ∈ W ∧ ∃ ψ : ComplexModel n → EReal,
      SGPT.Foundations.Analysis.DiscPshOn ψ W ∧ ∀ x ∈ X ∩ W, ψ x = φ x

/-- **`[FN80]` Theorem 5.3.1, local form, for pure-dimensional sets with global equations**: as
`LocalFNExtensionOfEquations`, with the additional hypothesis that the zero set is
pure-dimensional. -/
def LocalFNExtensionPureOfEquations : Prop :=
  ∀ (n : ℕ) (a : ComplexModel n) (r : Fin n → ℝ) (V : Set (ComplexModel n)) (m : ℕ)
    (h : Fin m → ComplexModel n → ℂ) (d : ℕ) (φ : ComplexModel n → EReal),
    (∀ i, 0 < r i) → IsOpen V → closedPolydisc a r ⊆ V → (∀ l, DifferentiableOn ℂ (h l) V) →
    (∀ l, h l a = 0) →
    AnalyticDimensionBasics.IsPureDim (n := n) (M := ComplexModel n)
      {z | z ∈ polydisc a r ∧ ∀ l, h l z = 0} d →
    FNL.IsWeaklyPSHOn {z | z ∈ polydisc a r ∧ ∀ l, h l z = 0} φ →
    ∃ W : Set (ComplexModel n), IsOpen W ∧ a ∈ W ∧ ∃ ψ : ComplexModel n → EReal,
      SGPT.Foundations.Analysis.DiscPshOn ψ W ∧
        ∀ x ∈ W, x ∈ polydisc a r → (∀ l, h l x = 0) → ψ x = φ x

section Reduction

variable {n : ℕ}

open AnalyticDimensionBasics RegularPointDimension HironakaEmbeddedDimensionParts

/-- The dimension parts of an analytic subset of an open set `Ω ⊆ ℂⁿ`, as subsets of `ℂⁿ`. -/
def dimPieces {Ω : Opens (ComplexModel n)} (C : Set Ω) (k : Fin (n + 1)) : Set (ComplexModel n) :=
  Subtype.val '' dimensionPart (n := n) (M := Ω) C k

theorem iUnion_dimPieces {Ω : Opens (ComplexModel n)} {C : Set Ω}
    (hC : IsComplexAnalyticSubset (n := n) C) : (⋃ k, dimPieces C k) = Subtype.val '' C := by
  conv_rhs => rw [eq_iUnion_dimensionPart hC]
  rw [image_iUnion]
  rfl

theorem dimPieces_hS {Ω : Opens (ComplexModel n)} {C : Set Ω}
    (hC : IsComplexAnalyticSubset (n := n) C) (k : Fin (n + 1)) (y : ComplexModel n)
    (hy : y ∈ dimPieces C k) (U : Set (ComplexModel n)) (hU : U ∈ 𝓝 y) :
    ∃ z ∈ U, z ∈ dimPieces C k ∧
      RegularAtDim (n := n) (M := ComplexModel n) (⋃ k, dimPieces C k) z k ∧
      ∀ᶠ z' in 𝓝 z, ∀ k', z' ∈ dimPieces C k' → k' = k := by
  obtain ⟨y', hy', rfl⟩ := hy
  have hU' : (Subtype.val : Ω → ComplexModel n) ⁻¹' U ∈ 𝓝 y' :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hU
  obtain ⟨z', hz'U, hz'reg⟩ := mem_closure_iff_nhds.mp hy' _ hU'
  have hz'reg : RegularAtDim (n := n) C z' k := hz'reg
  refine ⟨z'.val, hz'U, ⟨z', subset_closure hz'reg, rfl⟩, ?_, ?_⟩
  · rw [iUnion_dimPieces hC]
    exact AnalyticSubsetOpens.regularAtDim_image_val_iff.mpr hz'reg
  · have hev := RegularPatchNeighborhood.eventually_regularAtDim hz'reg
    obtain ⟨G, hGsub, hGo, hz'G⟩ := _root_.mem_nhds_iff.mp hev
    have hGo' : IsOpen ((Subtype.val : Ω → ComplexModel n) '' G) :=
      Ω.isOpen.isOpenMap_subtype_val G hGo
    filter_upwards [hGo'.mem_nhds ⟨z', hz'G, rfl⟩] with w hw k' hwk'
    obtain ⟨v, hvG, rfl⟩ := hw
    obtain ⟨v', hv', hv'v⟩ := hwk'
    have hv'eq : v' = v := Subtype.val_injective hv'v
    subst hv'eq
    obtain ⟨u, huG, hureg⟩ := mem_closure_iff_nhds.mp hv' G (hGo.mem_nhds hvG)
    have hureg' : RegularAtDim (n := n) C u k' := hureg
    have huk : RegularAtDim (n := n) C u k := hGsub huG hureg'.2.1
    exact Fin.ext (eq_of_regularAtDim hureg' huk)

theorem isComplexAnalyticSubset_dimPieces_hasLocalEquationsOn {Ω : Opens (ComplexModel n)}
    {C : Set Ω} (hC : IsComplexAnalyticSubset (n := n) C) (k : Fin (n + 1)) :
    FNR.HasLocalEquationsOn (dimPieces C k) (Ω : Set (ComplexModel n)) :=
  FNR.hasLocalEquationsOn_of_isComplexAnalyticSubset (isComplexAnalyticSubset_dimensionPart hC k)

theorem hasLocalEquationsOn_suspension {Ω : Opens (ComplexModel n)} {C : Set Ω}
    (hC : IsComplexAnalyticSubset (n := n) C) :
    FNR.HasLocalEquationsOn (suspension (dimPieces C)) (blk1 ⁻¹' (Ω : Set (ComplexModel n))) := by
  have heq : suspension (dimPieces C) = ⋃ k : Fin (n + 1),
      (blk1 ⁻¹' dimPieces C k ∩ blk2 ⁻¹' complexCoordinatePlane n (n - k)) := by
    ext w
    simp [suspension]
  rw [heq]
  refine hasLocalEquationsOn_iUnion fun k => hasLocalEquationsOn_inter_sets
    (hasLocalEquationsOn_preimage (isComplexAnalyticSubset_dimPieces_hasLocalEquationsOn hC k)
      blk1) ?_
  have hplane : blk2 ⁻¹' complexCoordinatePlane n (n - k) =
      {w : ComplexModel (n + n) | ∀ i : Fin n,
        (fun i w => if n - (k : ℕ) ≤ i.val then blk2 w i else 0) i w = 0} := by
    ext w
    simp only [mem_preimage, complexCoordinatePlane, mem_ofPred_eq]
    constructor
    · intro h i
      split_ifs with hi
      · exact h i hi
      · rfl
    · intro h i hi
      have := h i
      rwa [if_pos hi] at this
  rw [hplane]
  apply hasLocalEquationsOn_of_global
  intro i
  by_cases hi : n - (k : ℕ) ≤ i.val
  · simp only [if_pos hi]
    exact ((EuclideanSpace.proj (𝕜 := ℂ) i).comp blk2).differentiable
  · simp only [if_neg hi]
    exact differentiable_const 0

/-- **Reduction to pure dimension.** Given the local [FN80] theorem for pure-dimensional sets,
for every analytic subset `C` of an open set `Ω ⊆ ℂⁿ`, every polydisc `Δ(a, r) ⊆ Ω` centred at
`a ∈ C` and every `φ ∈ WP(C ∩ Δ(a, r))`, near `a` the function `φ` is the restriction to `C` of an
ambient function satisfying the disc criterion. -/
theorem extension_of_pure (hP : LocalFNExtensionPure) {Ω : Opens (ComplexModel n)} {C : Set Ω}
    (hC : IsComplexAnalyticSubset (n := n) C) {a : ComplexModel n} {r : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hΔΩ : polydisc a r ⊆ Ω) (ha : a ∈ Subtype.val '' C)
    {φ : ComplexModel n → EReal}
    (hφ : FNL.IsWeaklyPSHOn (Subtype.val '' C ∩ polydisc a r) φ) :
    ∃ W : Set (ComplexModel n), IsOpen W ∧ a ∈ W ∧ ∃ ψ : ComplexModel n → EReal,
      SGPT.Foundations.Analysis.DiscPshOn ψ W ∧
        ∀ x ∈ (Subtype.val '' C ∩ polydisc a r) ∩ W, ψ x = φ x := by
  set S := dimPieces C
  have hU : (⋃ k, S k) = Subtype.val '' C := iUnion_dimPieces hC
  set r' : Fin (n + n) → ℝ := Fin.append r (fun _ => 1) with hr'def
  set a' : ComplexModel (n + n) := inl a
  set Δ' := polydisc a' r'
  have hr' : ∀ i, 0 < r' i := fun i =>
    Fin.addCases (fun i => by simpa [hr'def] using hr i) (fun i => by simp [hr'def]) i
  have hmemΔ' : ∀ w, w ∈ Δ' ↔ blk1 w ∈ polydisc a r ∧ ∀ i : Fin n, ‖blk2 w i‖ < 1 := by
    intro w
    simp only [Δ', polydisc, mem_ofPred_eq, a', blk1_apply, blk2_apply]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa [hr'def] using h (Fin.castAdd n i)
      · simpa [hr'def] using h (Fin.natAdd n i)
    · rintro ⟨h1, h2⟩ j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa [hr'def] using h1 i
      · simpa [hr'def] using h2 i
  have hΔ'Ω : Δ' ⊆ blk1 ⁻¹' (Ω : Set (ComplexModel n)) := fun w hw =>
    hΔΩ ((hmemΔ' w).mp hw).1
  set X' := suspension S ∩ Δ'
  have hX'eq : FNR.HasLocalEquationsOn X' Δ' :=
    hasLocalEquationsOn_inter_sets ((hasLocalEquationsOn_suspension hC).mono hΔ'Ω)
      (fun x hx => ⟨Δ', isOpen_polydisc a' r', hx, 0, Fin.elim0, fun i => i.elim0,
        fun y hy => by simp [hy]⟩)
  have hX'pure : IsPureDim (n := n + n) (M := ComplexModel (n + n)) X' n := by
    intro p j hp
    have hpΔ : p ∈ Δ' := hp.2.1.2
    have hp' : RegularAtDim (n := n + n) (suspension S) p j := by
      refine regularAtDim_of_inter_eq (isOpen_polydisc a' r') hpΔ ?_ hp
      ext w
      simp only [X', mem_inter_iff]
      tauto
    exact isPureDim_suspension S (fun k y hy U hUy => dimPieces_hS hC k y hy U hUy) p j hp'
  have hmapX' : MapsTo blk1 X' (Subtype.val '' C ∩ polydisc a r) := by
    intro w hw
    refine ⟨?_, ((hmemΔ' w).mp hw.2).1⟩
    rw [← hU]
    exact blk1_mem_of_mem_suspension hw.1
  have hinl : ∀ x ∈ Subtype.val '' C ∩ polydisc a r, inl x ∈ X' := by
    rintro x ⟨hxC, hxΔ⟩
    refine ⟨inl_mem_suspension (by rwa [hU]), (hmemΔ' _).mpr ⟨by rwa [blk1_inl], fun i => ?_⟩⟩
    simp
  have haΔ : a ∈ polydisc a r := fun i => by simpa using hr i
  obtain ⟨W', hW', haW', ψ', hψ', hψ'φ⟩ := hP (n + n) X' a' r' n (fun w => φ (blk1 w)) hr'
    inter_subset_right hX'eq hX'pure (hinl a ⟨ha, haΔ⟩) (isWeaklyPSHOn_comp hφ blk1 hmapX')
  refine ⟨inl ⁻¹' W', hW'.preimage inl.continuous, haW', fun x => ψ' (inl x),
    hψ'.comp_continuousLinearMap inl, ?_⟩
  rintro x ⟨hx, hxW⟩
  show ψ' (inl x) = φ x
  rw [hψ'φ (inl x) ⟨hinl x hx, hxW⟩, blk1_inl]

/-- **The local [FN80] theorem for pure-dimensional sets implies it for all analytic sets.** -/
theorem localFNExtension_of_pure (hP : LocalFNExtensionPure) : LocalFNExtension := by
  intro n X a r φ hr hXΔ hloc haX hφ
  let Ω : Opens (ComplexModel n) := ⟨polydisc a r, isOpen_polydisc a r⟩
  have hC : IsComplexAnalyticSubset (n := n) ((Subtype.val : Ω → ComplexModel n) ⁻¹' X) :=
    isComplexAnalyticSubset_of_hasLocalEquationsOn (Ω := Ω) hloc
  have himage : Subtype.val '' ((Subtype.val : Ω → ComplexModel n) ⁻¹' X) = X := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact hy'
    · intro hy
      exact ⟨⟨y, hXΔ hy⟩, hy, rfl⟩
  have hXX : Subtype.val '' ((Subtype.val : Ω → ComplexModel n) ⁻¹' X) ∩ polydisc a r = X := by
    rw [himage]
    exact inter_eq_left.mpr hXΔ
  obtain ⟨W, hW, haW, ψ, hψ, hψφ⟩ := extension_of_pure hP hC hr subset_rfl
    (by rw [himage]; exact haX) (by rw [hXX]; exact hφ)
  refine ⟨W, hW, haW, ψ, hψ, ?_⟩
  rw [← hXX]
  exact hψφ

/-- The global-equations form of the pure-dimensional local [FN80] theorem implies the form with
local equations (Cartan's Theorem A on a closed polydisc of half the radii; pure dimension passes
to open subsets). -/
theorem localFNExtensionPure_of_equations (H : LocalFNExtensionPureOfEquations) :
    LocalFNExtensionPure := by
  intro n X a r d φ hr hXΔ hloc hpure haX hWP
  obtain ⟨V, hV, hCV, m, h, hh, hmemX⟩ := exists_equations_half hr hloc
  have hr' := half_radii_pos hr
  have hsub : polydisc a (fun i => r i / 2) ⊆ V :=
    (polydisc_subset_closedPolydisc a _).trans hCV
  have haV : a ∈ V := hsub (center_mem_polydisc a hr')
  have hX'eq : {z | z ∈ polydisc a (fun i => r i / 2) ∧ ∀ l, h l z = 0} =
      X ∩ polydisc a (fun i => r i / 2) := by
    ext z
    constructor
    · rintro ⟨hz, hz0⟩
      exact ⟨(hmemX z (hsub hz)).mpr hz0, hz⟩
    · rintro ⟨hzX, hz⟩
      exact ⟨hz, (hmemX z (hsub hz)).mp hzX⟩
  have hpure' : IsPureDim (n := n) (M := ComplexModel n)
      {z | z ∈ polydisc a (fun i => r i / 2) ∧ ∀ l, h l z = 0} d := by
    rw [hX'eq]
    intro p j hp
    refine hpure p j (regularAtDim_of_inter_eq (isOpen_polydisc _ _) hp.2.1.2 ?_ hp)
    rw [inter_assoc, inter_self]
  obtain ⟨W, hW, haW, ψ, hψ, hψφ⟩ := H n a (fun i => r i / 2) V m h d φ hr' hV hCV hh
    ((hmemX a haV).mp haX) hpure' (by rw [hX'eq]; exact hWP.mono inter_subset_left)
  refine ⟨W ∩ polydisc a (fun i => r i / 2), hW.inter (isOpen_polydisc _ _),
    ⟨haW, center_mem_polydisc a hr'⟩, ψ, hψ.mono inter_subset_left, ?_⟩
  rintro x ⟨hxX, hxW, hxΔ⟩
  exact hψφ x hxW hxΔ ((hmemX x (hsub hxΔ)).mp hxX)

end Reduction

end SGPT.Unibranch.FNA
