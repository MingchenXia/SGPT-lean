import SGPT.GAGA.SerreM5Gen

/-!
# Serre's theorems on `ℙᴺ`: linear changes of coordinates

Towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145), milestone M4.2.

The hyperplane step of Theorem A treats the points of `L_d ∩ {z_d = 0} = L_{d-1}`. A linear
automorphism `T` of `ℂ^{N+1}` with `T(L_d) ⊆ L_d` transports the class `𝒮_d` (`InS.pushLin`:
`a ∈ (T_*M)_y` iff `a ∘ T ∈ M_{T⁻¹y}`, coherence by `CoherentAt.comapHomeomorph`) and generation
(`GenOn.of_pushLin`), so pointwise generation at `T x` gives it at `x` (`ptGen_of_map`). The
elementary shears `z ↦ z + t z_j e_k` (`shearEquiv`) move every point of `L_d ∖ 0` into
`L_{d-1}` (`ptGen_of_planeL`).

Blueprint: `claude-serre-m5.tex`, node `claude-serre-m5:shear`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Transport along a linear automorphism -/

section Transport

variable (T : ConeSpace N ≃L[ℂ] ConeSpace N)

theorem clEquiv_ne_zero {z : ConeSpace N} (hz : z ≠ 0) : T z ≠ 0 := fun h =>
  hz (by simpa using congrArg T.symm h)

/-- The push-forward `T_* M`: `a ∈ (T_*M)_y` iff `a ∘ T ∈ M_{T⁻¹ y}`. -/
def pushLin (M : GermModule (ConeSpace N) ι) : GermModule (ConeSpace N) ι :=
  M.comapHomeomorph T.symm.toHomeomorph

theorem mem_pushLin {M : GermModule (ConeSpace N) ι} {y : ConeSpace N}
    {a : ι → ConeSpace N → ℂ} :
    (pushLin T M).mem y a ↔ M.mem (T.symm y) (fun j z => a j (T z)) :=
  Iff.rfl

/-- `I_{L_d} 𝒪^ι` is transported by maps preserving `L_d`. -/
theorem Idm_mem_comp {d : ℕ} (hT : ∀ z ∈ planeL d, T z ∈ planeL d) {y : ConeSpace N}
    {a : ι → ConeSpace N → ℂ} (ha : (Idm d ι).mem (T y) a) :
    (Idm d ι).mem y (fun j z => a j (T z)) := by
  rw [mem_Idm_iff] at ha ⊢
  refine ⟨fun j => (ha.1 j).comp T.continuous fun _ =>
    (T : ConeSpace N →L[ℂ] ConeSpace N).differentiableAt, ?_⟩
  filter_upwards [T.continuous.continuousAt.eventually ha.2] with z hz hzL j
  exact hz (hT z hzL) j

/-- The class `𝒮_d` is transported by linear automorphisms preserving `L_d`. -/
theorem InS.pushLin {d : ℕ} (hT : ∀ z ∈ planeL d, T z ∈ planeL d)
    {M : GermModule (ConeSpace N) ι} (hS : InS d M) : InS d (pushLin T M) where
  coh y hy := GermModule.CoherentAt.comapHomeomorph T.symm.toHomeomorph
    (fun _ => (T.symm : ConeSpace N →L[ℂ] ConeSpace N).differentiableAt)
    (fun _ => (T : ConeSpace N →L[ℂ] ConeSpace N).differentiableAt)
    (hS.coh _ (clEquiv_ne_zero T.symm hy))
  inv := by
    intro y hy c hc a
    have key := hS.inv (T.symm y) (clEquiv_ne_zero T.symm hy) c hc (fun j z => a j (T z))
    have e1 : T.symm (c • y) = c • T.symm y := map_smul _ _ _
    have e2 : (fun j z => a j (c⁻¹ • T z)) =
        (fun j z => (fun j z => a j (T z)) j (c⁻¹ • z)) := by
      funext j z
      simp only [map_smul]
    show _ ↔ M.mem (T.symm (c • y)) (fun j z => a j (c⁻¹ • T z))
    rw [e1, e2]
    exact key
  le y hy a ha := by
    rw [mem_pushLin]
    refine hS.le _ (clEquiv_ne_zero T.symm hy) _ (Idm_mem_comp T hT ?_)
    rwa [T.apply_symm_apply]

/-- Generation is transported by linear automorphisms preserving `L_d`. -/
theorem GenOn.of_pushLin {d : ℕ} (hT : ∀ z ∈ planeL d, T z ∈ planeL d)
    {M : GermModule (ConeSpace N) ι} {x : ConeSpace N} {m : ℤ}
    (h : GenOn (pushLin T M) (Idm d ι) m {T x}) : GenOn M (Idm d ι) m {x} := by
  obtain ⟨μ, _, σ, ⟨hσh, hσM⟩, hgen⟩ := h
  refine ⟨μ, inferInstance, fun k j z => σ k j (T z), ⟨fun k => ?_, fun k y hy => ?_⟩,
    fun y hy => ?_⟩
  · refine ⟨isOpen_ne, isCone_ne_zero, fun _ h => h, fun j => ?_, fun z hz c hc j => ?_⟩
    · exact ((hσh k).diff j).comp (T : ConeSpace N →L[ℂ] ConeSpace N).differentiableOn
        fun z hz => clEquiv_ne_zero T hz
    · simp only [map_smul]
      exact (hσh k).hom (T z) (clEquiv_ne_zero T hz) c hc j
  · have := hσM k (T y) (clEquiv_ne_zero T hy)
    rw [mem_pushLin, T.symm_apply_apply] at this
    exact this
  · rw [Set.mem_singleton_iff.1 hy]
    intro a ha
    have ha' : (pushLin T M).mem (T x) (fun j z => a j (T.symm z)) := by
      rw [mem_pushLin, T.symm_apply_apply]
      simpa only [T.symm_apply_apply] using ha
    obtain ⟨c, hc, hca⟩ := hgen (T x) rfl _ ha'
    refine ⟨fun k z => c k (T z), fun k => (hc k).comp T.continuous fun _ =>
      (T : ConeSpace N →L[ℂ] ConeSpace N).differentiableAt, ?_⟩
    have := Idm_mem_comp T hT hca
    simpa only [T.symm_apply_apply] using this

/-- **Pointwise generation is transported** by linear automorphisms preserving `L_d`. -/
theorem ptGen_of_map {d : ℕ} (hT : ∀ z ∈ planeL d, T z ∈ planeL d) {x : ConeSpace N}
    (h : PtGen N d (T x)) : PtGen N d x := by
  intro ι _ _ M hS
  obtain ⟨m₀, hm₀⟩ := h ι (pushLin T M) (hS.pushLin T hT)
  exact ⟨m₀, hm₀.of_pushLin T hT⟩

end Transport

/-! ### Elementary shears -/

/-- The shear `z ↦ z + t z_j e_k`. -/
def shear (j k : Fin (N + 1)) (t : ℂ) : ConeSpace N →L[ℂ] ConeSpace N :=
  ContinuousLinearMap.id ℂ (ConeSpace N) +
    (t • EuclideanSpace.proj j).smulRight (EuclideanSpace.single k (1 : ℂ))

theorem shear_apply_coord (j k : Fin (N + 1)) (t : ℂ) (z : ConeSpace N) (l : Fin (N + 1)) :
    shear j k t z l = z l + if l = k then t * z j else 0 := by
  by_cases h : l = k
  · subst h
    simp [shear]
  · simp [shear, h]

theorem shear_neg_shear {j k : Fin (N + 1)} (hjk : j ≠ k) (t : ℂ) (z : ConeSpace N) :
    shear j k (-t) (shear j k t z) = z := by
  ext l
  simp only [shear_apply_coord, if_neg hjk, add_zero]
  split_ifs <;> ring

/-- The shear as a linear automorphism (`j ≠ k`). -/
def shearEquiv {j k : Fin (N + 1)} (hjk : j ≠ k) (t : ℂ) : ConeSpace N ≃L[ℂ] ConeSpace N :=
  ContinuousLinearEquiv.equivOfInverse (shear j k t) (shear j k (-t))
    (fun z => shear_neg_shear hjk t z)
    (fun z => by simpa using shear_neg_shear hjk (-t) z)

theorem shearEquiv_apply_coord {j k : Fin (N + 1)} (hjk : j ≠ k) (t : ℂ) (z : ConeSpace N)
    (l : Fin (N + 1)) : shearEquiv hjk t z l = z l + if l = k then t * z j else 0 :=
  shear_apply_coord j k t z l

/-- Shears into a coordinate `k ≤ d` preserve `L_d`. -/
theorem shearEquiv_planeL {j k : Fin (N + 1)} (hjk : j ≠ k) (t : ℂ) {d : ℕ} (hk : k.1 ≤ d) :
    ∀ z ∈ planeL d, shearEquiv hjk t z ∈ planeL d := by
  intro z hz l hl
  have hlk : l ≠ k := fun h => by rw [h] at hl; omega
  rw [shearEquiv_apply_coord, if_neg hlk, add_zero]
  exact hz l hl

/-- **Moving points of `L_d` into `L_{d-1}`.** If every member of `𝒮_d` is generated at every
point of `L_{d-1} ∖ 0`, then also at every point of `L_d ∖ 0` (`1 ≤ d ≤ N`). -/
theorem ptGen_of_planeL {d : ℕ} (hd : d < N + 1) (hd1 : 1 ≤ d)
    (h : ∀ y : ConeSpace N, y ∈ planeL (d - 1) → y ≠ 0 → PtGen N d y) {x : ConeSpace N}
    (hx : x ∈ planeL d) (hx0 : x ≠ 0) : PtGen N d x := by
  set e : Fin (N + 1) := ⟨d, hd⟩ with he
  -- points with `x_d = 0` lie in `L_{d-1}`
  have hA : ∀ y : ConeSpace N, y ∈ planeL d → y ≠ 0 → y e = 0 → PtGen N d y := by
    intro y hy hy0 hye
    refine h y (fun l hl => ?_) hy0
    by_cases hld : l.1 = d
    · have : l = e := Fin.ext hld
      rw [this]
      exact hye
    · exact hy l (by omega)
  -- points with a non-zero coordinate `x_j`, `j < d`
  have hB : ∀ y : ConeSpace N, y ∈ planeL d → y ≠ 0 → ∀ j : Fin (N + 1), j.1 < d → y j ≠ 0 →
      PtGen N d y := by
    intro y hy hy0 j hj hyj
    have hje : j ≠ e := fun h' => by
      have := congrArg Fin.val h'
      simp [he] at this
      omega
    let T := shearEquiv hje (-(y e / y j))
    have hT : ∀ z ∈ planeL d, T z ∈ planeL d := shearEquiv_planeL hje _ (le_refl d)
    refine ptGen_of_map T hT (hA (T y) (hT y hy) (clEquiv_ne_zero T hy0) ?_)
    show shearEquiv hje (-(y e / y j)) y e = 0
    rw [shearEquiv_apply_coord, if_pos rfl]
    field_simp
    ring
  by_cases hxe : x e = 0
  · exact hA x hx hx0 hxe
  by_cases hj : ∃ j : Fin (N + 1), j.1 < d ∧ x j ≠ 0
  · obtain ⟨j, hj, hxj⟩ := hj
    exact hB x hx hx0 j hj hxj
  push Not at hj
  set o : Fin (N + 1) := ⟨0, by omega⟩ with ho
  have heo : e ≠ o := fun h' => by
    have := congrArg Fin.val h'
    simp [he, ho] at this
    omega
  let T := shearEquiv heo 1
  have hT : ∀ z ∈ planeL d, T z ∈ planeL d := shearEquiv_planeL heo _ (Nat.zero_le d)
  refine ptGen_of_map T hT (hB (T x) (hT x hx) (clEquiv_ne_zero T hx0) o (by simp [ho]; omega) ?_)
  show shearEquiv heo 1 x o ≠ 0
  rw [shearEquiv_apply_coord, if_pos rfl, hj o (by simp [ho]; omega), one_mul, zero_add]
  exact hxe

end SGPT.GAGA.PN
