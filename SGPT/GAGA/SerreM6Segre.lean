import SGPT.GAGA.SerreM5Main

/-!
# Serre's GAGA: the Segre cone and its local equations

Towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145), step G1.

`ℙᴷ × ℙ¹` embeds in `ℙ^{2K+1}` by Segre's map; on cones, `ℂ^{K+1} × ℂ → ℂ^{2K+2}`,
`segre (z, t) = (z, t z)` (the affine part `t = s₁/s₀` of `(z, s) ↦ z ⊗ s`), and the points
at `t = ∞` are `(0, y)`, the images of `segre` under the exchange `swapE` of the two blocks
of coordinates. The cone over the Segre variety is cut out by the `2 × 2` minors
`segE i j = u_i v_j - u_j v_i`.

* `segre_piI`, `piI_segre`: on `{u_i ≠ 0}`, a point of the Segre cone is `segre (piI i w)`
  with `piI i (u, v) = (u, v_i / u_i)`.
* `swap_segre`: `swapE (segre (y, s)) = segre (s y, 1/s)` for `s ≠ 0` (the transition to the
  chart at infinity, `chi`).
* **`exists_segE_comb`** (the Segre cone is a submanifold, with the minors as local
  equations): a function `f` holomorphic near a point of the Segre cone with `u_i ≠ 0` is
  `f ∘ segre ∘ piI i + ∑_j C_j · segE i j` near that point. Proof: the coordinates
  `(u, t, r) ↦ (u, t u + r)` straighten the cone to `{r = 0}`; Hadamard's lemma for
  coordinate planes (TN `CoordinatePlaneDivision.exists_eq_sum_coord_mul`).

Blueprint: `claude-serre-m6.tex`, node `claude-serre-m6:segre`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.Foundations.Analysis.FirstPass
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

/-- Holomorphy along a map which is holomorphic near the point. -/
theorem HolAt.comp_of_eventually {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : F → ℂ} {φ : E → F} {y : E}
    (hf : HolAt f (φ y)) (hφ : ∀ᶠ x in 𝓝 y, DifferentiableAt ℂ φ x) :
    HolAt (fun x => f (φ x)) y := by
  have hc : ContinuousAt φ y := hφ.self_of_nhds.continuousAt
  filter_upwards [hc.eventually hf, hφ] with x h1 h2
  exact h1.comp x h2

theorem differentiable_coordE {n : ℕ} (k : Fin n) :
    Differentiable ℂ (fun x : EuclideanSpace ℂ (Fin n) => x k) :=
  (EuclideanSpace.proj (𝕜 := ℂ) k).differentiable

variable {K : ℕ}

/-! ### Coordinates on `ℂ^{2K+2}` -/

/-- `ℂ^{2K+2}`, the cone over `ℙ^{2K+1}`. -/
abbrev SegW (K : ℕ) := ConeSpace (K + 1 + K)

/-- The index of `u_l`. -/
def iu (l : Fin (K + 1)) : Fin (K + 1 + K + 1) := ⟨l.1, by omega⟩

/-- The index of `v_l`. -/
def iv (l : Fin (K + 1)) : Fin (K + 1 + K + 1) := ⟨K + 1 + l.1, by omega⟩

/-- The point `(u, v) = (a, b)`. -/
def mkW (a b : Fin (K + 1) → ℂ) : SegW K :=
  (EuclideanSpace.equiv (Fin (K + 1 + K + 1)) ℂ).symm
    (fun k => if h : k.1 < K + 1 then a ⟨k.1, h⟩ else b ⟨k.1 - (K + 1), by omega⟩)

theorem mkW_apply (a b : Fin (K + 1) → ℂ) (k : Fin (K + 1 + K + 1)) :
    mkW a b k = if h : k.1 < K + 1 then a ⟨k.1, h⟩ else b ⟨k.1 - (K + 1), by omega⟩ := rfl

/-- The coordinate `u_l`. -/
def uC (w : SegW K) (l : Fin (K + 1)) : ℂ := w (iu l)

/-- The coordinate `v_l`. -/
def vC (w : SegW K) (l : Fin (K + 1)) : ℂ := w (iv l)

@[simp] theorem uC_mkW (a b : Fin (K + 1) → ℂ) (l : Fin (K + 1)) : uC (mkW a b) l = a l := by
  rw [uC, mkW_apply, dif_pos (show (iu l).1 < K + 1 from l.2)]
  rfl

@[simp] theorem vC_mkW (a b : Fin (K + 1) → ℂ) (l : Fin (K + 1)) : vC (mkW a b) l = b l := by
  rw [vC, mkW_apply, dif_neg (show ¬ (iv l).1 < K + 1 by simp only [iv]; omega)]
  congr 1
  ext
  simp [iv]

theorem mkW_eta (w : SegW K) : mkW (uC w) (vC w) = w := by
  ext k
  rw [mkW_apply]
  split_ifs with h
  · rfl
  · show w (iv ⟨k.1 - (K + 1), _⟩) = w k
    rw [show (iv ⟨k.1 - (K + 1), by omega⟩ : Fin (K + 1 + K + 1)) = k from
      Fin.ext (by simp only [iv]; omega)]

theorem differentiable_uC (l : Fin (K + 1)) : Differentiable ℂ (fun w : SegW K => uC w l) :=
  differentiable_coord (iu l)

theorem differentiable_vC (l : Fin (K + 1)) : Differentiable ℂ (fun w : SegW K => vC w l) :=
  differentiable_coord (iv l)

theorem differentiableAt_mkW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x₀ : E}
    {a b : E → Fin (K + 1) → ℂ} (ha : ∀ l, DifferentiableAt ℂ (fun x => a x l) x₀)
    (hb : ∀ l, DifferentiableAt ℂ (fun x => b x l) x₀) :
    DifferentiableAt ℂ (fun x => mkW (a x) (b x)) x₀ := by
  have h : DifferentiableAt ℂ (fun x => fun k : Fin (K + 1 + K + 1) =>
      if h : k.1 < K + 1 then a x ⟨k.1, h⟩ else b x ⟨k.1 - (K + 1), by omega⟩) x₀ := by
    refine differentiableAt_pi.2 fun k => ?_
    by_cases hk : k.1 < K + 1
    · simp only [dif_pos hk]
      exact ha _
    · simp only [dif_neg hk]
      exact hb _
  exact ((EuclideanSpace.equiv (Fin (K + 1 + K + 1)) ℂ).symm.toContinuousLinearMap.differentiableAt
    (x := _)).comp x₀ h

/-! ### The Segre map -/

/-- `segre (z, t) = (z, t z)`. -/
def segre (q : ConeSpace K × ℂ) : SegW K := mkW (fun l => q.1 l) (fun l => q.2 * q.1 l)

@[simp] theorem uC_segre (q : ConeSpace K × ℂ) (l : Fin (K + 1)) : uC (segre q) l = q.1 l :=
  uC_mkW _ _ l

@[simp] theorem vC_segre (q : ConeSpace K × ℂ) (l : Fin (K + 1)) :
    vC (segre q) l = q.2 * q.1 l :=
  vC_mkW _ _ l

theorem differentiable_segre : Differentiable ℂ (segre (K := K)) := fun q =>
  differentiableAt_mkW (fun l => (differentiable_coord l).differentiableAt.comp q
      differentiableAt_fst)
    (fun l => differentiableAt_snd.mul
      ((differentiable_coord l).differentiableAt.comp q differentiableAt_fst))

/-- The `2 × 2` minors, equations of the Segre cone. -/
def segE (i j : Fin (K + 1)) (w : SegW K) : ℂ := uC w i * vC w j - uC w j * vC w i

theorem segE_segre (i j : Fin (K + 1)) (q : ConeSpace K × ℂ) : segE i j (segre q) = 0 := by
  simp only [segE, uC_segre, vC_segre]
  ring

theorem differentiable_segE (i j : Fin (K + 1)) : Differentiable ℂ (segE (K := K) i j) :=
  ((differentiable_uC i).mul (differentiable_vC j)).sub
    ((differentiable_uC j).mul (differentiable_vC i))

/-- The `u`-block as a point of `ℂ^{K+1}`. -/
def uPt (w : SegW K) : ConeSpace K := (EuclideanSpace.equiv (Fin (K + 1)) ℂ).symm (uC w)

theorem uPt_apply (w : SegW K) (l : Fin (K + 1)) : uPt w l = uC w l := rfl

/-- The chart `w ↦ (u, v_i / u_i)` of the Segre cone on `{u_i ≠ 0}`. -/
def piI (i : Fin (K + 1)) (w : SegW K) : ConeSpace K × ℂ := (uPt w, vC w i / uC w i)

theorem piI_segre {i : Fin (K + 1)} {q : ConeSpace K × ℂ} (hq : q.1 i ≠ 0) :
    piI i (segre q) = q := by
  refine Prod.ext ?_ ?_
  · ext l
    simp [piI, uPt_apply]
  · simp only [piI, uC_segre, vC_segre]
    field_simp

theorem segre_piI {i : Fin (K + 1)} {w : SegW K} (hw : uC w i ≠ 0) (hS : ∀ j, segE i j w = 0) :
    segre (piI i w) = w := by
  conv_rhs => rw [← mkW_eta w]
  unfold segre
  congr 1
  funext l
  have h := hS l
  simp only [segE] at h
  simp only [piI, uPt_apply]
  field_simp
  linear_combination -h

theorem differentiableAt_vu (i : Fin (K + 1)) {w : SegW K} (hw : uC w i ≠ 0) :
    DifferentiableAt ℂ (fun w : SegW K => vC w i / uC w i) w := by
  have hv : HolAt (fun w : SegW K => vC w i) w :=
    Eventually.of_forall fun _ => (differentiable_vC i).differentiableAt
  have hu : HolAt (fun w : SegW K => uC w i) w :=
    Eventually.of_forall fun _ => (differentiable_uC i).differentiableAt
  have e : (fun w : SegW K => vC w i / uC w i) = fun w => vC w i * (uC w i)⁻¹ :=
    funext fun _ => div_eq_mul_inv _ _
  rw [e]
  exact (hv.mul (hu.inv hw)).self_of_nhds

theorem differentiableAt_piI {i : Fin (K + 1)} {w : SegW K} (hw : uC w i ≠ 0) :
    DifferentiableAt ℂ (piI i) w := by
  refine DifferentiableAt.prodMk ?_ ?_
  · exact ((EuclideanSpace.equiv (Fin (K + 1)) ℂ).symm.toContinuousLinearMap.differentiableAt
      (x := _)).comp w (differentiableAt_pi.2 fun l => (differentiable_uC l).differentiableAt)
  · exact differentiableAt_vu i hw

theorem eventually_differentiableAt_piI {i : Fin (K + 1)} {w : SegW K} (hw : uC w i ≠ 0) :
    ∀ᶠ w' in 𝓝 w, DifferentiableAt ℂ (piI i) w' := by
  filter_upwards [(differentiable_uC i).continuous.continuousAt.eventually_ne hw] with w' hw'
  exact differentiableAt_piI hw'

/-! ### The exchange of the two blocks -/

/-- `(u, v) ↦ (v, u)`. -/
def swapFun (w : SegW K) : SegW K := mkW (vC w) (uC w)

@[simp] theorem uC_swapFun (w : SegW K) (l : Fin (K + 1)) : uC (swapFun w) l = vC w l :=
  uC_mkW _ _ l

@[simp] theorem vC_swapFun (w : SegW K) (l : Fin (K + 1)) : vC (swapFun w) l = uC w l :=
  vC_mkW _ _ l

theorem swapFun_swapFun (w : SegW K) : swapFun (swapFun w) = w := by
  conv_rhs => rw [← mkW_eta w]
  unfold swapFun
  congr 1 <;> funext l <;> simp

theorem uC_add (w w' : SegW K) (l : Fin (K + 1)) : uC (w + w') l = uC w l + uC w' l := rfl
theorem vC_add (w w' : SegW K) (l : Fin (K + 1)) : vC (w + w') l = vC w l + vC w' l := rfl
theorem uC_smul (c : ℂ) (w : SegW K) (l : Fin (K + 1)) : uC (c • w) l = c * uC w l := rfl
theorem vC_smul (c : ℂ) (w : SegW K) (l : Fin (K + 1)) : vC (c • w) l = c * vC w l := rfl

theorem mkW_add (a b a' b' : Fin (K + 1) → ℂ) :
    mkW a b + mkW a' b' = mkW (a + a') (b + b') := by
  conv_lhs => rw [← mkW_eta (mkW a b + mkW a' b')]
  congr 1 <;> funext l <;> simp [uC_add, vC_add]

theorem mkW_smul (c : ℂ) (a b : Fin (K + 1) → ℂ) : c • mkW a b = mkW (c • a) (c • b) := by
  conv_lhs => rw [← mkW_eta (c • mkW a b)]
  congr 1 <;> funext l <;> simp [uC_smul, vC_smul]

/-- The exchange as a linear map. -/
def swapLin : SegW K →ₗ[ℂ] SegW K where
  toFun := swapFun
  map_add' w w' := by
    simp only [swapFun, mkW_add]
    congr 1
  map_smul' c w := by
    simp only [swapFun, mkW_smul, RingHom.id_apply]
    congr 1

/-- The exchange of the two blocks of coordinates. -/
def swapE : SegW K ≃L[ℂ] SegW K :=
  ContinuousLinearEquiv.equivOfInverse (LinearMap.toContinuousLinearMap swapLin)
    (LinearMap.toContinuousLinearMap swapLin) (fun w => swapFun_swapFun w)
    (fun w => swapFun_swapFun w)

theorem swapE_apply (w : SegW K) : swapE w = swapFun w := rfl

theorem swapE_symm_apply (w : SegW K) : swapE.symm w = swapFun w := rfl

/-- The transition `(y, s) ↦ (s y, 1/s)` between the two charts of `ℙ¹`. -/
def chi (q : ConeSpace K × ℂ) : ConeSpace K × ℂ := (q.2 • q.1, q.2⁻¹)

theorem swap_segre {q : ConeSpace K × ℂ} (hq : q.2 ≠ 0) : swapFun (segre q) = segre (chi q) := by
  unfold swapFun
  conv_rhs => unfold segre
  congr 1 <;> funext l <;> simp [chi, hq]

theorem chi_chi {q : ConeSpace K × ℂ} (hq : q.2 ≠ 0) : chi (chi q) = q := by
  refine Prod.ext ?_ ?_
  · simp [chi, smul_smul, inv_mul_cancel₀ hq]
  · simp [chi]

theorem differentiableAt_chi {q : ConeSpace K × ℂ} (hq : q.2 ≠ 0) :
    DifferentiableAt ℂ (chi (K := K)) q :=
  DifferentiableAt.prodMk
    (DifferentiableAt.smul (c := fun x : ConeSpace K × ℂ => x.2) (f := fun x => x.1)
      differentiableAt_snd differentiableAt_fst)
    (differentiableAt_snd.inv hq)

theorem eventually_differentiableAt_chi {q : ConeSpace K × ℂ} (hq : q.2 ≠ 0) :
    ∀ᶠ q' in 𝓝 q, DifferentiableAt ℂ (chi (K := K)) q' := by
  filter_upwards [continuous_snd.continuousAt.eventually_ne hq] with q' hq'
  exact differentiableAt_chi hq'

/-! ### Straightening the Segre cone -/

/-- `ℂ^{K+2} × ℂ^{K+1}` with coordinates `(z, t, r)`. -/
abbrev SegO (K : ℕ) := EuclideanSpace ℂ (Fin (K + 2 + (K + 1)))

/-- The point `(z, t, r)`. -/
def mkO (a : Fin (K + 1) → ℂ) (t : ℂ) (r : Fin (K + 1) → ℂ) : SegO K :=
  (EuclideanSpace.equiv (Fin (K + 2 + (K + 1))) ℂ).symm
    (Fin.append (Fin.snoc (α := fun _ => ℂ) a t) r)

def zO (x : SegO K) (l : Fin (K + 1)) : ℂ := x (Fin.castAdd (K + 1) (Fin.castSucc l))
def tO (x : SegO K) : ℂ := x (Fin.castAdd (K + 1) (Fin.last (K + 1)))
def rO (x : SegO K) (j : Fin (K + 1)) : ℂ := x (Fin.natAdd (K + 2) j)

@[simp] theorem zO_mkO (a : Fin (K + 1) → ℂ) (t : ℂ) (r : Fin (K + 1) → ℂ) (l : Fin (K + 1)) :
    zO (mkO a t r) l = a l := by
  show Fin.append (Fin.snoc (α := fun _ => ℂ) a t) r _ = _
  rw [Fin.append_left, Fin.snoc_castSucc]

@[simp] theorem tO_mkO (a : Fin (K + 1) → ℂ) (t : ℂ) (r : Fin (K + 1) → ℂ) :
    tO (mkO a t r) = t := by
  show Fin.append (Fin.snoc (α := fun _ => ℂ) a t) r _ = _
  rw [Fin.append_left, Fin.snoc_last]

@[simp] theorem rO_mkO (a : Fin (K + 1) → ℂ) (t : ℂ) (r : Fin (K + 1) → ℂ) (j : Fin (K + 1)) :
    rO (mkO a t r) j = r j := by
  show Fin.append (Fin.snoc (α := fun _ => ℂ) a t) r _ = _
  rw [Fin.append_right]

theorem mkO_eta (x : SegO K) : mkO (zO x) (tO x) (rO x) = x := by
  ext k
  refine Fin.addCases (fun k₁ => ?_) (fun j => ?_) k
  · refine Fin.lastCases ?_ (fun l => ?_) k₁
    · exact tO_mkO _ _ _
    · exact zO_mkO _ _ _ l
  · exact rO_mkO _ _ _ j

theorem mkO_ext {a a' : Fin (K + 1) → ℂ} {t t' : ℂ} {r r' : Fin (K + 1) → ℂ} (ha : a = a')
    (ht : t = t') (hr : r = r') : mkO a t r = mkO a' t' r' := by
  rw [ha, ht, hr]

/-- `(z, t, r) ↦ (z, t z + r)`. -/
def omegaM (x : SegO K) : SegW K := mkW (zO x) (fun l => tO x * zO x l + rO x l)

/-- `(z, t, r) ↦ (z, t, 0)`. -/
def kappaM (x : SegO K) : SegO K := mkO (zO x) (tO x) 0

/-- The inverse chart on `{u_i ≠ 0}`: `(u, v) ↦ (u, v_i/u_i, v - (v_i/u_i) u)`. -/
def tauM (i : Fin (K + 1)) (w : SegW K) : SegO K :=
  mkO (uC w) (vC w i / uC w i) (fun j => vC w j - vC w i / uC w i * uC w j)

theorem omega_tau (i : Fin (K + 1)) (w : SegW K) : omegaM (tauM i w) = w := by
  conv_rhs => rw [← mkW_eta w]
  unfold omegaM tauM
  congr 1 <;> funext l <;> simp

theorem omega_kappa_tau (i : Fin (K + 1)) (w : SegW K) :
    omegaM (kappaM (tauM i w)) = segre (piI i w) := by
  unfold omegaM kappaM tauM segre piI
  congr 1 <;> funext l <;> simp [uPt_apply]

theorem kappa_of_plane {x : SegO K} (hx : x ∈ complexCoordinatePlane (K + 2 + (K + 1)) (K + 2)) :
    kappaM x = x := by
  conv_rhs => rw [← mkO_eta x]
  refine mkO_ext rfl rfl ?_
  funext j
  exact (hx (Fin.natAdd (K + 2) j) (by simp)).symm

theorem rO_tauM (i : Fin (K + 1)) (w : SegW K) (hw : uC w i ≠ 0) (j : Fin (K + 1)) :
    rO (tauM i w) j = segE i j w / uC w i := by
  simp only [tauM, rO_mkO, segE]
  field_simp

theorem tauM_mem_plane {i : Fin (K + 1)} {w : SegW K} (hw : uC w i ≠ 0)
    (hS : ∀ j, segE i j w = 0) :
    tauM i w ∈ complexCoordinatePlane (K + 2 + (K + 1)) (K + 2) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j : Fin (K + 1), Fin.natAdd (K + 2) j = k :=
    ⟨⟨k.1 - (K + 2), by omega⟩, Fin.ext (by simp; omega)⟩
  show rO (tauM i w) j = 0
  rw [rO_tauM i w hw, hS j, zero_div]

theorem differentiableAt_mkO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x₀ : E}
    {a r : E → Fin (K + 1) → ℂ} {t : E → ℂ} (ha : ∀ l, DifferentiableAt ℂ (fun x => a x l) x₀)
    (ht : DifferentiableAt ℂ t x₀) (hr : ∀ l, DifferentiableAt ℂ (fun x => r x l) x₀) :
    DifferentiableAt ℂ (fun x => mkO (a x) (t x) (r x)) x₀ := by
  have h : DifferentiableAt ℂ (fun x => Fin.append (Fin.snoc (α := fun _ => ℂ) (a x) (t x))
      (r x)) x₀ := by
    refine differentiableAt_pi.2 fun k => ?_
    refine Fin.addCases (fun k₁ => ?_) (fun j => ?_) k
    · simp only [Fin.append_left]
      refine Fin.lastCases ?_ (fun l => ?_) k₁
      · simp only [Fin.snoc_last]
        exact ht
      · simp only [Fin.snoc_castSucc]
        exact ha l
    · simp only [Fin.append_right]
      exact hr j
  exact ((EuclideanSpace.equiv (Fin (K + 2 + (K + 1))) ℂ).symm.toContinuousLinearMap.differentiableAt
    (x := _)).comp x₀ h

theorem differentiable_omegaM : Differentiable ℂ (omegaM (K := K)) := fun _ =>
  differentiableAt_mkW (fun _ => (differentiable_coordE _).differentiableAt)
    (fun _ => ((differentiable_coordE _).differentiableAt.mul
      (differentiable_coordE _).differentiableAt).add (differentiable_coordE _).differentiableAt)

theorem differentiable_kappaM : Differentiable ℂ (kappaM (K := K)) := fun _ =>
  differentiableAt_mkO (fun _ => (differentiable_coordE _).differentiableAt)
    (differentiable_coordE _).differentiableAt (fun _ => differentiableAt_const 0)

theorem differentiableAt_tauM {i : Fin (K + 1)} {w : SegW K} (hw : uC w i ≠ 0) :
    DifferentiableAt ℂ (tauM i) w := by
  have hq : DifferentiableAt ℂ (fun w : SegW K => vC w i / uC w i) w := differentiableAt_vu i hw
  exact differentiableAt_mkO (fun l => (differentiable_uC l).differentiableAt) hq
    (fun j => (differentiable_vC j).differentiableAt.sub
      (hq.mul (differentiable_uC j).differentiableAt))

/-- **The minors are local equations of the Segre cone.** -/
theorem exists_segE_comb {i : Fin (K + 1)} {w : SegW K} (hwi : uC w i ≠ 0)
    (hS : ∀ j, segE i j w = 0) {f : SegW K → ℂ} (hf : HolAt f w) :
    ∃ C : Fin (K + 1) → SegW K → ℂ, (∀ j, HolAt (C j) w) ∧
      ∀ᶠ w' in 𝓝 w, f w' = f (segre (piI i w')) + ∑ j, C j w' * segE i j w' := by
  have hq := tauM_mem_plane hwi hS
  have hwq : omegaM (tauM i w) = w := omega_tau i w
  have hRq : omegaM (kappaM (tauM i w)) = w := by rw [kappa_of_plane hq, hwq]
  have h1 : HolAt (fun x => f (omegaM x)) (tauM i w) :=
    HolAt.comp_of_eventually (by rw [hwq]; exact hf)
      (Eventually.of_forall fun x => differentiable_omegaM x)
  have h2 : HolAt (fun x => f (omegaM (kappaM x))) (tauM i w) :=
    HolAt.comp_of_eventually (φ := fun x => omegaM (kappaM x)) (by rw [hRq]; exact hf)
      (Eventually.of_forall fun x => (differentiable_omegaM _).comp x (differentiable_kappaM x))
  obtain ⟨H, hH0, hHd, hHF⟩ := CoordinatePlaneDivision.exists_eq_sum_coord_mul (K + 1) (K + 2)
    (by omega) (F := fun x => f (omegaM x) - f (omegaM (kappaM x))) hq (h1.sub h2)
    (Eventually.of_forall fun x hx => by
      show f (omegaM x) - f (omegaM (kappaM x)) = 0
      rw [kappa_of_plane hx, sub_self])
  have hu : HolAt (fun w' : SegW K => uC w' i) w :=
    Eventually.of_forall fun w' => (differentiable_uC i).differentiableAt
  have hτ : ∀ᶠ w' in 𝓝 w, DifferentiableAt ℂ (tauM i) w' := by
    filter_upwards [hu.continuousAt.eventually_ne hwi] with w' hw'
    exact differentiableAt_tauM hw'
  refine ⟨fun j w' => H (Fin.natAdd (K + 2) j) (tauM i w') * (uC w' i)⁻¹, fun j => ?_, ?_⟩
  · exact (HolAt.comp_of_eventually (φ := tauM i) (hHd _) hτ).mul (hu.inv hwi)
  · filter_upwards [(differentiableAt_tauM hwi).continuousAt.eventually hHF,
      hu.continuousAt.eventually_ne hwi] with w' hF hw'
    have e1 : f (omegaM (tauM i w')) - f (omegaM (kappaM (tauM i w'))) =
        f w' - f (segre (piI i w')) := by
      rw [omega_tau i w', omega_kappa_tau]
    have e2 : ∑ k, (tauM i w') k * H k (tauM i w') =
        ∑ j : Fin (K + 1), rO (tauM i w') j * H (Fin.natAdd (K + 2) j) (tauM i w') := by
      rw [Fin.sum_univ_add]
      have : ∑ a : Fin (K + 2), (tauM i w') (Fin.castAdd (K + 1) a) *
          H (Fin.castAdd (K + 1) a) (tauM i w') = 0 :=
        Finset.sum_eq_zero fun a _ => by rw [hH0 _ (by simp), Pi.zero_apply, mul_zero]
      rw [this, zero_add]
      rfl
    have hF' : f w' - f (segre (piI i w')) =
        ∑ j : Fin (K + 1), rO (tauM i w') j * H (Fin.natAdd (K + 2) j) (tauM i w') := by
      rw [← e1, ← e2]
      exact hF
    have e3 : ∑ j : Fin (K + 1), rO (tauM i w') j * H (Fin.natAdd (K + 2) j) (tauM i w') =
        ∑ j, H (Fin.natAdd (K + 2) j) (tauM i w') * (uC w' i)⁻¹ * segE i j w' :=
      Finset.sum_congr rfl fun j _ => by
        rw [rO_tauM i w' hw']
        field_simp
    rw [← e3, ← hF']
    ring

end SGPT.GAGA.PN
