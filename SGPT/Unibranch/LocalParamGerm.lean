import SGPT.Unibranch.LocalParamSlice
import SGPT.Foundations.Analysis.Pending.DimensionMonotone
import SGPT.Foundations.Analysis.Pending.FiniteFibrePiece

/-!
# Analytic sets of codimension at least two are locally covered by grids

This file supplies the local-parametrization half of the proof of the
Grauert--Remmert extension theorem across analytic sets of codimension at least
two (SGPT `thm:GRexten`, item (1)).

Let `S ⊆ ℂⁿ` be analytic near a point `p` (finitely many holomorphic equations)
and assume every regular point of `S` near `p` has dimension at most `n - 2`.
The germ of `S` at `p` is a finite irredundant union of irreducible germs
(`AnalyticGermDecomposition`).  Each irreducible germ `B` carries, after a linear
change of coordinates `L`, the data of the local parametrization theorem
(Demailly, *Complex analytic and differential geometry*, II.4.19; Grauert--Remmert,
*Coherent analytic sheaves*, §3.4): a base `ℂᵈ` of the finite branched covering and,
for every fibre coordinate `k ≥ d`, a Weierstrass polynomial `Q_k(z', z_k)` in
`z_k` over the base, vanishing on `B` (`ParametrizationData.e_eq_zero`).  The
dimension `d` of the covering is the dimension of the regular points of `B`
(`GermComponentDimension`), hence `d ≤ n - 2` (`dim_add_two_le`).  The two last
coordinates `n - 2, n - 1` are then fibre coordinates, and `Q_{n-2}`, `Q_{n-1}`
(in the coordinates `L`) form a two-sheet grid containing `B`
(`componentGrid`).  Hence `S` is covered near `p` by finitely many grids
(`exists_gridCover`), and `LocalParamSlice` gives the local upper bound of a
function plurisubharmonic off `S` (`exists_bound_of_codimTwo`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Unibranch.LocalParam

open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
open SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
open SGPT.Foundations.Analysis.Pending.PshCodimTwoExtension (unitVec unitVec_apply_ne)

variable {n : ℕ}

/-! ### The dimension of a local irreducible component -/

/-- **Local irreducible components have codimension at least two.**  If every regular point
of `S` in `Ω` has dimension at most `n - 2`, then every local irreducible component of the
germ of `S` at `p ∈ Ω` has a parametrization of dimension at most `n - 2`: inside an open set
meeting only that component, its regular points of the parametrization dimension are
regular points of `S`. -/
theorem dim_add_two_le {Ω S : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    (hcodim : ∀ y ∈ Ω, ∀ k : ℕ,
      RegularAtDim (n := n) (M := ComplexModel n) S y k → k + 2 ≤ n)
    {p : ComplexModel n} (hp : p ∈ Ω) {r : ℕ} {B : Fin r → Set (ComplexModel n)}
    (hB : ∀ i, IsIrreducibleGerm (B i))
    (hcover : {w : ComplexModel n | w + p ∈ S} =ᶠ[𝓝 0] (⋃ i, B i))
    (hpw : Pairwise fun i j => ¬ (B i ≤ᶠ[𝓝 0] B j)) (i : Fin r)
    {L : ComplexModel n ≃L[ℂ] ComplexModel n} (P : ParametrizationData (L ⁻¹' B i))
    (SD : SetsData P) : P.dim + 2 ≤ n := by
  obtain ⟨Ωp, hΩpo, hΩp0, hΩp⟩ := GermComponentDimension.exists_pure_nhds_dim (hB i)
    fun ε hε => GermComponentDimension.exists_regularAtDim_near_zero L SD hε
  obtain ⟨ρ₁, hρ₁, hρ₁s⟩ := Metric.eventually_nhds_iff_ball.1 (Filter.eventuallyEq_set.mp hcover)
  obtain ⟨ρ₂, hρ₂, hρ₂Ω⟩ := Metric.isOpen_iff.mp hΩ p hp
  have hρ : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
  obtain ⟨O', hO'o, hO'sub, hne, hdisj⟩ := GermComponentDimension.exists_isOpen_disjoint_others hB
    hpw i (isOpen_ball.inter hΩpo) ⟨mem_ball_self hρ, hΩp0⟩
  obtain ⟨z, hzO', hzA⟩ := hne
  obtain ⟨y, hyO', hyreg⟩ :=
    mem_closure_iff.mp ((hΩp O' hO'o (hO'sub.trans inter_subset_right)).2 ⟨hzA, hzO'⟩)
      O' hO'o hzO'
  have hmem : ∀ w ∈ O', w ∈ ball (0 : ComplexModel n) ρ₁ := fun w hw =>
    ball_subset_ball (min_le_left _ _) (hO'sub hw).1
  have hcg : {w : ComplexModel n | w + p ∈ S} ∩ O' = B i ∩ O' := by
    ext w
    constructor
    · rintro ⟨hw, hwO⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp ((hρ₁s w (hmem w hwO)).mp hw)
      by_cases hji : j = i
      · exact ⟨hji ▸ hj, hwO⟩
      · have : w ∈ O' ∩ B j := ⟨hwO, hj⟩
        rw [hdisj j hji] at this
        exact absurd this (notMem_empty w)
    · rintro ⟨hw, hwO⟩
      exact ⟨(hρ₁s w (hmem w hwO)).mpr (mem_iUnion.2 ⟨i, hw⟩), hwO⟩
  have hyreg' : RegularAtDim (n := n) (M := ComplexModel n)
      {w : ComplexModel n | w + p ∈ S} y P.dim :=
    RegularPointDimension.regularAtDim_of_inter_eq hO'o hyO'
      (by rw [hcg, inter_assoc, inter_self]) hyreg
  have hset : {w : ComplexModel n | w + p ∈ S} = {w : ComplexModel n | w - (-p) ∈ S} := by
    ext w
    simp only [mem_ofPred_eq, sub_neg_eq_add]
  rw [hset] at hyreg'
  have hyS := (AnalyticLocalStatement.regularAtDim_translate_iff (S := S) (-p) y).mp hyreg'
  rw [sub_neg_eq_add] at hyS
  refine hcodim (y + p) (hρ₂Ω ?_) _ hyS
  have hy : ‖y‖ < ρ₂ := by
    have := (hO'sub hyO').1
    rw [mem_ball_zero_iff] at this
    exact this.trans_le (min_le_right _ _)
  rwa [mem_ball, dist_eq_norm, add_sub_cancel_right]

/-! ### The grid of a component -/

/-- The projection to the first `d` coordinates kills a coordinate vector of index `≥ d`. -/
theorem coordinateProjection_unitVec {d : ℕ} {k : Fin n} (hk : d ≤ k.1) :
    coordinateProjection n d (unitVec k) = 0 := by
  ext a
  rw [coordinateProjection_apply]
  split_ifs with h
  · have hne : (⟨a.1, h⟩ : Fin n) ≠ k := fun heq => by
      have := congrArg Fin.val heq
      simp only at this
      omega
    rw [unitVec_apply_ne hne]
    rfl
  · rfl

section Component

variable {B : Set (ComplexModel n)} {L : ComplexModel n ≃L[ℂ] ComplexModel n}
  (P : ParametrizationData (L ⁻¹' B))

/-- The Weierstrass polynomial `Q_k(z', z_k)` of the fibre coordinate `k` over the base
`ℂᵈ` of the local parametrization. -/
def fibrePoly (k : Fin n) (w : ComplexModel n) : ℂ :=
  monicEval (P.s k) (P.e k) (coordinateProjection n P.dim w) (w k)

/-- `Q_k` does not depend on another fibre coordinate. -/
theorem fibrePoly_add_unitVec_of_ne {k j : Fin n} (hj : P.dim ≤ j.1) (hjk : j ≠ k)
    (w : ComplexModel n) (t : ℂ) :
    fibrePoly P k (w + t • unitVec j) = fibrePoly P k w := by
  have hproj : coordinateProjection n P.dim (w + t • unitVec j) =
      coordinateProjection n P.dim w := by
    rw [map_add, map_smul, coordinateProjection_unitVec hj, smul_zero, add_zero]
  have hk : (w + t • unitVec j) k = w k := by
    simp [unitVec_apply_ne hjk.symm]
  simp only [fibrePoly, hproj, hk]

/-- Along its own coordinate axis, `Q_k` is a monic polynomial. -/
theorem fibrePoly_add_unitVec_self {k : Fin n} (hk : P.dim ≤ k.1) (w : ComplexModel n)
    (t : ℂ) :
    fibrePoly P k (w + t • unitVec k) =
      monicEval (P.s k) (P.e k) (coordinateProjection n P.dim w) (w k + t) := by
  have hproj : coordinateProjection n P.dim (w + t • unitVec k) =
      coordinateProjection n P.dim w := by
    rw [map_add, map_smul, coordinateProjection_unitVec hk, smul_zero, add_zero]
  have hkk : (w + t • unitVec k) k = w k + t := by simp
  simp only [fibrePoly, hproj, hkk]

/-- `Q_k` is holomorphic on the ball of the parametrization. -/
theorem differentiableOn_fibrePoly (k : Fin n) :
    DifferentiableOn ℂ (fibrePoly P k) (ball 0 P.rad) := by
  have hcoord : Differentiable ℂ (fun w : ComplexModel n => w k) :=
    (EuclideanSpace.proj (𝕜 := ℂ) k).differentiable
  have hmaps : MapsTo (coordinateProjection n P.dim) (ball (0 : ComplexModel n) P.rad)
      (ball 0 P.rad) := fun w hw => by
    rw [mem_ball_zero_iff] at hw ⊢
    exact (FiniteFibrePiece.norm_coordinateProjection_le P.dim_le w).trans_lt hw
  have he : ∀ j, DifferentiableOn ℂ (fun w => P.e k j (coordinateProjection n P.dim w))
      (ball 0 P.rad) := fun j =>
    (P.differentiableOn_e k j).comp (coordinateProjection n P.dim).differentiable.differentiableOn
      hmaps
  unfold fibrePoly monicEval
  exact (hcoord.differentiableOn.fun_pow _).add
    (DifferentiableOn.fun_sum fun j _ => (he j).fun_mul (hcoord.differentiableOn.fun_pow _))

/-- The first of the two last coordinates. -/
def idxA (hdim : P.dim + 2 ≤ n) : Fin n := ⟨n - 2, by omega⟩

/-- The last coordinate. -/
def idxB (hdim : P.dim + 2 ≤ n) : Fin n := ⟨n - 1, by omega⟩

theorem idxA_ne_idxB (hdim : P.dim + 2 ≤ n) : idxA P hdim ≠ idxB P hdim := by
  intro h
  have := congrArg Fin.val h
  simp only [idxA, idxB] at this
  omega

theorem dim_le_idxA (hdim : P.dim + 2 ≤ n) : P.dim ≤ (idxA P hdim).1 := by
  simp only [idxA]
  omega

theorem dim_le_idxB (hdim : P.dim + 2 ≤ n) : P.dim ≤ (idxB P hdim).1 := by
  simp only [idxB]
  omega

theorem symm_sub_add_smul (p z v : ComplexModel n) (t : ℂ) :
    L.symm (z + t • L v - p) = L.symm (z - p) + t • v := by
  rw [add_sub_right_comm, map_add, map_smul, ContinuousLinearEquiv.symm_apply_apply]

theorem mapsTo_symm_sub {p : ComplexModel n} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * (‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n)‖ + 1) ≤ P.rad) :
    MapsTo (fun z => L.symm (z - p)) (ball p δ) (ball 0 P.rad) := by
  intro z hz
  rw [mem_ball, dist_eq_norm] at hz
  rw [mem_ball_zero_iff]
  have h1 : ‖L.symm (z - p)‖ ≤ ‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n)‖ * ‖z - p‖ :=
    (L.symm : ComplexModel n →L[ℂ] ComplexModel n).le_opNorm (z - p)
  have h2 : ‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n)‖ * ‖z - p‖ ≤
      ‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n)‖ * δ :=
    mul_le_mul_of_nonneg_left hz.le (norm_nonneg _)
  nlinarith

/-- **The grid of a local irreducible component** of dimension at most `n - 2`: in the
parametrizing coordinates `L` centred at `p`, the Weierstrass polynomials of the two last
fibre coordinates, sliced along the corresponding coordinate axes. -/
def componentGrid (p : ComplexModel n) (hdim : P.dim + 2 ≤ n) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * (‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n)‖ + 1) ≤ P.rad) :
    GridData (ball p δ) where
  fa z := fibrePoly P (idxA P hdim) (L.symm (z - p))
  fb z := fibrePoly P (idxB P hdim) (L.symm (z - p))
  va := L (unitVec (idxA P hdim))
  vb := L (unitVec (idxB P hdim))
  differentiableOn_fa := (differentiableOn_fibrePoly P _).comp
    ((L.symm : ComplexModel n →L[ℂ] ComplexModel n).differentiable.comp
      (differentiable_id.sub_const p)).differentiableOn (mapsTo_symm_sub P hδ0 hδ)
  differentiableOn_fb := (differentiableOn_fibrePoly P _).comp
    ((L.symm : ComplexModel n →L[ℂ] ComplexModel n).differentiable.comp
      (differentiable_id.sub_const p)).differentiableOn (mapsTo_symm_sub P hδ0 hδ)
  fa_add_vb z t := by
    rw [symm_sub_add_smul, fibrePoly_add_unitVec_of_ne P (dim_le_idxB P hdim)
      (idxA_ne_idxB P hdim).symm]
  fb_add_va z t := by
    rw [symm_sub_add_smul, fibrePoly_add_unitVec_of_ne P (dim_le_idxA P hdim)
      (idxA_ne_idxB P hdim)]
  finite_fa x _ := by
    refine ((FiniteFibrePiece.finite_setOf_monicEval_eq_zero (P.s (idxA P hdim))
      (P.e (idxA P hdim)) (coordinateProjection n P.dim (L.symm (x - p)))).preimage
      (add_right_injective (L.symm (x - p) (idxA P hdim))).injOn).subset fun t ht => ?_
    simp only [mem_ofPred_eq] at ht
    rw [symm_sub_add_smul, fibrePoly_add_unitVec_self P (dim_le_idxA P hdim)] at ht
    exact ht
  finite_fb x _ := by
    refine ((FiniteFibrePiece.finite_setOf_monicEval_eq_zero (P.s (idxB P hdim))
      (P.e (idxB P hdim)) (coordinateProjection n P.dim (L.symm (x - p)))).preimage
      (add_right_injective (L.symm (x - p) (idxB P hdim))).injOn).subset fun t ht => ?_
    simp only [mem_ofPred_eq] at ht
    rw [symm_sub_add_smul, fibrePoly_add_unitVec_self P (dim_le_idxB P hdim)] at ht
    exact ht

/-- The component lies in its grid. -/
theorem mem_componentGrid_carrier {p : ComplexModel n} (hdim : P.dim + 2 ≤ n) {δ : ℝ}
    (hδ0 : 0 < δ)
    (hδ : δ * (‖(L.symm : ComplexModel n →L[ℂ] ComplexModel n)‖ + 1) ≤ P.rad)
    {z : ComplexModel n} (hz : z ∈ ball p δ) (hzB : z - p ∈ B) :
    z ∈ (componentGrid P p hdim hδ0 hδ).carrier := by
  have hw : L.symm (z - p) ∈ L ⁻¹' B := by
    rw [mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
    exact hzB
  have hball := mapsTo_symm_sub P hδ0 hδ hz
  exact ⟨hz, P.e_eq_zero _ hw hball _ (dim_le_idxA P hdim),
    P.e_eq_zero _ hw hball _ (dim_le_idxB P hdim)⟩

end Component

/-- Finitely many positive numbers have a common positive lower bound. -/
theorem exists_pos_le_of_fin {r : ℕ} (f : Fin r → ℝ) (hf : ∀ i, 0 < f i) {c : ℝ}
    (hc : 0 < c) : ∃ δ > 0, δ ≤ c ∧ ∀ i, δ ≤ f i := by
  induction r with
  | zero => exact ⟨c, hc, le_rfl, fun i => i.elim0⟩
  | succ r ih =>
    obtain ⟨δ, hδ, hδc, hδf⟩ := ih (fun i => f i.succ) (fun i => hf _)
    refine ⟨min δ (f 0), lt_min hδ (hf 0), (min_le_left _ _).trans hδc, fun i => ?_⟩
    exact Fin.cases (min_le_right _ _) (fun j => (min_le_left _ _).trans (hδf j)) i

/-! ### Covering by grids -/

/-- **Local grid covering of an analytic set of codimension at least two.**  Let `S` be
analytic in the open set `Ω` (locally the common zero set of finitely many holomorphic
functions) and let every regular point of `S` in `Ω` have dimension at most `n - 2`.  Near
every point `p ∈ Ω`, `S` is covered by finitely many two-sheet grids. -/
theorem exists_gridCover {Ω S : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    (hS : ∀ z ∈ Ω, ∃ W : Set (ComplexModel n), IsOpen W ∧ z ∈ W ∧
      ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ), (∀ j, DifferentiableOn ℂ (g j) W) ∧
        ∀ y ∈ W, y ∈ S ↔ ∀ j, g j y = 0)
    (hcodim : ∀ y ∈ Ω, ∀ k : ℕ,
      RegularAtDim (n := n) (M := ComplexModel n) S y k → k + 2 ≤ n)
    {p : ComplexModel n} (hp : p ∈ Ω) :
    ∃ δ > 0, ball p δ ⊆ Ω ∧ ∃ (r : ℕ) (G : Fin r → GridData (ball p δ)),
      S ∩ ball p δ ⊆ ⋃ m, (G m).carrier := by
  obtain ⟨W, hW, hpW, N, g, hg, hgS⟩ := hS p hp
  have htrans : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w + p ∈ W := by
    have h := (continuous_add_const p).tendsto (0 : ComplexModel n)
    rw [zero_add] at h
    exact h (hW.mem_nhds hpW)
  have hgerm : IsAnalyticGerm {w : ComplexModel n | w + p ∈ S} := by
    refine ⟨N, fun j w => g j (w + p), fun j => ?_, ?_⟩
    · filter_upwards [(hW.preimage (continuous_add_const p)).mem_nhds
        (show (0 : ComplexModel n) + p ∈ W by rwa [zero_add])] with w hw
      exact ((hg j).differentiableAt (hW.mem_nhds hw)).comp w
        (differentiableAt_id.add_const p)
    · filter_upwards [htrans] with w hw
      exact hgS (w + p) hw
  obtain ⟨r, B, hB, -, hcover, hpw⟩ := exists_irreducible_decomposition_euclidean hgerm
  choose L P hSD using fun i => DimensionMonotone.exists_parametrization (hB i)
  have hdim : ∀ i, (P i).dim + 2 ≤ n := fun i =>
    dim_add_two_le hΩ hcodim hp hB hcover hpw i (P i) (hSD i).some
  obtain ⟨ρ₁, hρ₁, hρ₁s⟩ := Metric.eventually_nhds_iff_ball.1 (Filter.eventuallyEq_set.mp hcover)
  obtain ⟨ρ₂, hρ₂, hρ₂Ω⟩ := Metric.isOpen_iff.mp hΩ p hp
  obtain ⟨δ, hδ, hδc, hδf⟩ := exists_pos_le_of_fin
    (fun i => (P i).rad / (‖((L i).symm : ComplexModel n →L[ℂ] ComplexModel n)‖ + 1))
    (fun i => div_pos (P i).rad_pos (by positivity)) (lt_min hρ₁ hρ₂)
  have hδrad : ∀ i, δ * (‖((L i).symm : ComplexModel n →L[ℂ] ComplexModel n)‖ + 1) ≤
      (P i).rad := fun i => (le_div_iff₀ (by positivity)).mp (hδf i)
  refine ⟨δ, hδ, (ball_subset_ball (hδc.trans (min_le_right _ _))).trans hρ₂Ω, r,
    fun i => componentGrid (P i) p (hdim i) hδ (hδrad i), ?_⟩
  rintro z ⟨hzS, hz⟩
  have hz' : z - p ∈ ball (0 : ComplexModel n) ρ₁ := by
    rw [mem_ball_zero_iff, ← dist_eq_norm]
    exact (mem_ball.mp hz).trans_le (hδc.trans (min_le_left _ _))
  have hzS' : z - p ∈ {w : ComplexModel n | w + p ∈ S} := by
    simpa only [mem_ofPred_eq, sub_add_cancel] using hzS
  obtain ⟨i, hi⟩ := mem_iUnion.mp ((hρ₁s _ hz').mp hzS')
  exact mem_iUnion.mpr ⟨i, mem_componentGrid_carrier (P i) (hdim i) hδ (hδrad i) hz hi⟩

/-- **Local upper bound across an analytic set of codimension at least two** (the main step of
SGPT `thm:GRexten`, item (1)).  Let `S` be analytic in the open set `Ω ⊆ ℂⁿ` with every
regular point of `S` in `Ω` of dimension at most `n - 2`, and let `ψ` be plurisubharmonic on
`Ω \ S`.  Then `ψ` is bounded above near every point of `Ω`, off `S`. -/
theorem exists_bound_of_codimTwo {Ω S : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    (hS : ∀ z ∈ Ω, ∃ W : Set (ComplexModel n), IsOpen W ∧ z ∈ W ∧
      ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ), (∀ j, DifferentiableOn ℂ (g j) W) ∧
        ∀ y ∈ W, y ∈ S ↔ ∀ j, g j y = 0)
    (hcodim : ∀ y ∈ Ω, ∀ k : ℕ,
      RegularAtDim (n := n) (M := ComplexModel n) S y k → k + 2 ≤ n)
    {ψ : ComplexModel n → EReal} (hψ : PlurisubharmonicOn ψ (Ω \ S))
    {p : ComplexModel n} (hp : p ∈ Ω) :
    ∃ U ∈ 𝓝 p, ∃ C : ℝ, ∀ y ∈ U, y ∉ S → ψ y ≤ C := by
  obtain ⟨δ, hδ, hδΩ, r, G, hcov⟩ := exists_gridCover hΩ hS hcodim hp
  have hopen : IsOpen (ball p δ \ S) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyb, hyS⟩
    obtain ⟨W, hW, hyW, N, g, hg, hgS⟩ := hS y (hδΩ hyb)
    obtain ⟨j, hj⟩ : ∃ j, g j y ≠ 0 := by
      by_contra! h
      exact hyS ((hgS y hyW).mpr h)
    have hcont : ContinuousAt (g j) y := (hg j).continuousOn.continuousAt (hW.mem_nhds hyW)
    filter_upwards [isOpen_ball.mem_nhds hyb, hW.mem_nhds hyW, hcont.eventually_ne hj] with
      x hxb hxW hx
    exact ⟨hxb, fun hxS => hx ((hgS x hxW).mp hxS j)⟩
  exact exists_bound_of_gridCover hδ G hcov hopen
    (hψ.mono fun y hy => ⟨hδΩ hy.1, hy.2⟩)

end SGPT.Unibranch.LocalParam
