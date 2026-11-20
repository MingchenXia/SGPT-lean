import SGPT.Toric.ProjectiveProductNativeTangent

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BoundedGlobalProduct
open SGPT.Foundations.Analysis.Pending.RelativeEnergy
open scoped Topology ENNReal RealInnerProductSpace

private def nativeBinarySubsetEquiv (n : ℕ) : (Fin n → Fin 2) ≃ Finset (Fin n) where
  toFun a := Finset.univ.filter (fun i => a i ≠ 0)
  invFun S i := if i ∈ S then 1 else 0
  left_inv a := by
    funext i
    change (if i ∈ Finset.univ.filter (fun k => a k ≠ 0) then 1 else 0) = a i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h : a i = 0 ∨ a i = 1 := by omega
    rcases h with h | h <;> simp [h]
  right_inv S := by
    ext i
    by_cases hi : i ∈ S <;> simp [hi]

private theorem native_subset_weight {n : ℕ} (S : Finset (Fin n)) (t : ℝ) :
    (∏ i : Fin n, if (nativeBinarySubsetEquiv n).symm S i = 0 then 1 - t else t) =
      t ^ S.card * (1 - t) ^ (n - S.card) := by
  classical
  have hin : (Finset.univ.filter (fun i : Fin n => i ∈ S)) = S := by ext i; simp
  have hnot : (Finset.univ.filter (fun i : Fin n => i ∉ S)).card = n - S.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin n => i ∈ S)
    rw [hin, Finset.card_univ, Fintype.card_fin] at h
    omega
  calc
    _ = ∏ i : Fin n, if i ∈ S then t else 1 - t := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S <;> simp [nativeBinarySubsetEquiv, hi]
    _ = _ := by
      rw [Finset.prod_ite, hin, Finset.prod_const, Finset.prod_const, hnot]

private def nativePrefixChoice {n : ℕ} (j : ℕ) (i : Fin n) : Fin 2 :=
  if i.val < j then 1 else 0

private def nativePrefixMoment {n : ℕ} {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u) (j : ℕ) : ℝ :=
  ∫ p, (u p - φ p).toReal ∂projectiveProductBinaryNativeMeasure hφ hu (nativePrefixChoice j)

private theorem native_binary_psh {n : ℕ} {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (a : Fin n → Fin 2) (i : Fin n) :
    ThetaPlurisubharmonic (projectiveProductFSBackground n).form.val
      (projectiveProductBinaryNativeFamily φ u (a i)) := by
  by_cases hi : a i = 0 <;> simp only [projectiveProductBinaryNativeFamily, hi, ↓reduceIte]
  · exact hφ.1
  · exact hu.1

private theorem native_subset_measure_eq_prefix {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (S : Finset (Fin n)) :
    projectiveProductBinaryNativeMeasure hφ hu ((nativeBinarySubsetEquiv n).symm S) =
      projectiveProductBinaryNativeMeasure hφ hu (nativePrefixChoice S.card) := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter (fun i => i.val < S.card)
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hT : T.card = S.card := by
    simp only [T, Fin.card_filter_val_lt, min_eq_right hcard]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq T S hT
  have hmem (i : Fin n) : σ i ∈ S ↔ i.val < S.card := by
    have hm : σ i ∈ S ↔ i ∈ T := by
      constructor
      · intro hi
        have hi' : σ i ∈ T.map σ.toEmbedding := hσ.symm ▸ hi
        obtain ⟨k, hk, hki⟩ := Finset.mem_map.mp hi'
        have he : k = i := σ.injective hki
        simpa only [he] using hk
      · intro hi
        have hi' : σ i ∈ T.map σ.toEmbedding := Finset.mem_map.mpr ⟨i, hi, rfl⟩
        rwa [hσ] at hi'
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  have htuple : (fun i => projectiveProductBinaryNativeFamily φ u
      ((nativeBinarySubsetEquiv n).symm S (σ i))) =
        fun i => projectiveProductBinaryNativeFamily φ u (nativePrefixChoice S.card i) := by
    funext i
    by_cases hi : i.val < S.card <;>
      simp [nativeBinarySubsetEquiv, projectiveProductBinaryNativeFamily, nativePrefixChoice,
        hmem, hi]
  have he := GlobalSlotPerm.globalMixedMeasure_perm
    (native_binary_psh hφ hu ((nativeBinarySubsetEquiv n).symm S)) σ
  exact he.symm.trans (GlobalDiagonalScaling.globalMixedMeasure_congr rfl htuple _ _)

/-- Actual native slot symmetry and genuine binary cardinalities give the literal
Bernstein expansion with original native endpoint moments. -/
theorem projectiveProductNativeTangent_eq_bernsteinPrefix {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u) (t : ℝ) :
    projectiveProductNativeTangentPolynomial hφ hu t =
      ∑ j ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n j).eval t *
        ∫ p, (u p - φ p).toReal ∂projectiveProductBinaryNativeMeasure hφ hu
          (fun i => if i.val < j then 1 else 0) := by
  classical
  let J : ℕ → ℝ := nativePrefixMoment hφ hu
  have hsum : (∑ S : Finset (Fin n), t ^ S.card * (1 - t) ^ (n - S.card) * J S.card) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (t ^ j * (1 - t) ^ (n - j) * J j) := by
    have h := Finset.sum_powerset_apply_card (fun j => t ^ j * (1 - t) ^ (n - j) * J j)
      (x := (Finset.univ : Finset (Fin n)))
    have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by ext S; simp
    rw [hpow, Finset.card_univ, Fintype.card_fin] at h
    simpa only [nsmul_eq_mul] using h
  calc
    projectiveProductNativeTangentPolynomial hφ hu t =
        ∑ S : Finset (Fin n), t ^ S.card * (1 - t) ^ (n - S.card) * J S.card := by
      unfold projectiveProductNativeTangentPolynomial
      apply Fintype.sum_equiv (nativeBinarySubsetEquiv n)
      intro a
      have ha : a = (nativeBinarySubsetEquiv n).symm ((nativeBinarySubsetEquiv n) a) :=
        ((nativeBinarySubsetEquiv n).symm_apply_apply a).symm
      rw [ha, native_subset_weight, native_subset_measure_eq_prefix]
      simp only [Equiv.apply_symm_apply, J, nativePrefixMoment]
    _ = _ := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro j _
      change (n.choose j : ℝ) * (t ^ j * (1 - t) ^ (n - j) * J j) =
        (bernsteinPolynomial ℝ n j).eval t * J j
      simp [bernsteinPolynomial, mul_assoc]

private theorem native_prefix_measure_eq_endpoint {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u) (j : Fin (n + 1)) :
    projectiveProductBinaryNativeMeasure hφ hu (nativePrefixChoice j.val) =
      endpointMixedMeasure (projectiveProductFSBackground n).form φ u hφ hu j := by
  have htuple : (fun i => projectiveProductBinaryNativeFamily φ u (nativePrefixChoice j.val i)) =
      endpointMixedPotential j u φ := by
    funext i
    by_cases hi : i.val < j.val <;>
      simp [projectiveProductBinaryNativeFamily, nativePrefixChoice, endpointMixedPotential, hi]
  exact GlobalDiagonalScaling.globalMixedMeasure_congr rfl htuple _ _

private theorem native_prefix_moment_eq_energyTerm {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hub : IsBoundedPotential u) (j : Fin (n + 1)) :
    nativePrefixMoment hφ hu j.val =
      relativeEnergyTerm (projectiveProductFSBackground n).form φ u hφ hu j := by
  rw [nativePrefixMoment, native_prefix_measure_eq_endpoint, relativeEnergyTerm]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by
    simp only [canonicalERealDiffToReal, poleModifiedERealDiffToReal, hub.ne_bot p,
      false_and, if_false])

/-- True Bernstein integration gives exactly the original native finite-type
endpoint energy, with the literal coefficient 1/(n+1), including n=0. -/
theorem intervalIntegral_projectiveProductNativeTangent_eq_relativeEnergy {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hub : IsBoundedPotential u) :
    (∫ t in (0 : ℝ)..1, projectiveProductNativeTangentPolynomial hφ hu t) =
      relativeEnergyOfMinimalType (projectiveProductFSBackground n).form φ u hφ hu := by
  let J : ℕ → ℝ := nativePrefixMoment hφ hu
  have hpoly (t : ℝ) : projectiveProductNativeTangentPolynomial hφ hu t =
      ∑ j ∈ Finset.range (n + 1), (bernsteinPolynomial ℝ n j).eval t * J j :=
    projectiveProductNativeTangent_eq_bernsteinPrefix hφ hu t
  simp_rw [hpoly]
  rw [intervalIntegral.integral_finsetSum (fun j _ => by
    have hc : Continuous (fun t : ℝ => (bernsteinPolynomial ℝ n j).eval t) :=
      continuous_iff_continuousAt.mpr (fun t => (bernsteinPolynomial ℝ n j).hasDerivAt t |>.continuousAt)
    exact (hc.mul continuous_const).intervalIntegrable 0 1)]
  have hint (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      (∫ t in (0 : ℝ)..1, (bernsteinPolynomial ℝ n j).eval t * J j) =
        (1 / (n + 1 : ℝ)) * J j := by
    rw [show (fun t : ℝ => (bernsteinPolynomial ℝ n j).eval t * J j) =
        (fun t : ℝ => J j * (bernsteinPolynomial ℝ n j).eval t) from funext (fun _ => mul_comm _ _),
      intervalIntegral.integral_const_mul,
      integral_bernsteinPolynomial_eq n j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    exact mul_comm _ _
  rw [Finset.sum_congr rfl hint, ← Finset.mul_sum, ← Fin.sum_univ_eq_sum_range J]
  have hsum : (∑ j : Fin (n + 1), J j.val) =
      ∑ j : Fin (n + 1), relativeEnergyTerm (projectiveProductFSBackground n).form φ u hφ hu j :=
    Finset.sum_congr rfl (fun j _ => native_prefix_moment_eq_energyTerm hφ hu hub j)
  rw [hsum, relativeEnergyOfMinimalType]
  ring

/-- The literal original conjugate of the manufactured finite product profile. -/
def projectiveProductToricLegendre {n : ℕ} (u : projectiveProductSpace n → EReal)
    (m : EuclideanSpace ℝ (Fin n)) : EReal :=
  conjugate (innerₗ (EuclideanSpace ℝ (Fin n)))
    (fun x => (projectiveProductToricEuclideanProfile u x : EReal)) m

/-- Actual source bounded growth gives genuine finite conjugate values throughout
 the actual cube before any real readback is used. -/
theorem projectiveProductToricLegendre_finite_of_bounded {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hiu : ProjectiveProductCircleInvariant u) (hub : IsBoundedPotential u) :
    ∀ m ∈ euclideanUnitCube n,
      projectiveProductToricLegendre u m = ((projectiveProductToricLegendre u m).toReal : EReal) := by
  obtain ⟨a, b, hab⟩ := conjugate_bounds_of_mem_boundedGrowthClass
    (innerₗ (EuclideanSpace ℝ (Fin n))) (isCompact_euclideanUnitCube n)
    (convex_euclideanUnitCube n) (projectiveProductToricProfile_mem_boundedGrowthClass hu hiu hub)
  intro m hm
  exact (EReal.coe_toReal
    (ne_top_of_le_ne_top (EReal.coe_ne_top b) (hab m hm).2)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hab m hm).1)).symm

/-- Genuine original finite conjugate bounds supply actual real integrability on the cube. -/
theorem projectiveProductToricLegendre_integrable_of_bounded {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hiu : ProjectiveProductCircleInvariant u) (hub : IsBoundedPotential u) :
    Integrable (fun m => (projectiveProductToricLegendre u m).toReal)
      (volume.restrict (euclideanUnitCube n)) :=
  integrable_conjugateToReal_of_mem_boundedGrowthClass volume (isCompact_euclideanUnitCube n)
    (nonempty_euclideanUnitCube n) (convex_euclideanUnitCube n)
    (f := ⟨projectiveProductToricEuclideanProfile u, projectiveProductToricEuclideanProfile_convex hu hiu⟩)
    (projectiveProductToricProfile_mem_boundedGrowthClass hu hiu hub)

/-- The actual original bounded native energy equals the literal factorial
Legendre-gap integral on the actual unit cube. No energy or derivative identity is supplied. -/
theorem projectiveProduct_relativeEnergyOfMinimalType_eq_legendre {n : ℕ}
    {φ u : projectiveProductSpace n → EReal}
    (hφ : IsThetaPshPotential (projectiveProductFSBackground n).form.val φ)
    (hiφ : ProjectiveProductCircleInvariant φ) (hφb : IsBoundedPotential φ)
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hiu : ProjectiveProductCircleInvariant u) (hub : IsBoundedPotential u) :
    relativeEnergyOfMinimalType (projectiveProductFSBackground n).form φ u hφ hu =
      (n.factorial : ℝ) * ∫ m in euclideanUnitCube n,
        ((projectiveProductToricLegendre φ m).toReal - (projectiveProductToricLegendre u m).toReal) := by
  let f : RealConvexFunction (EuclideanSpace ℝ (Fin n)) :=
    ⟨projectiveProductToricEuclideanProfile φ, projectiveProductToricEuclideanProfile_convex hφ hiφ⟩
  let g : RealConvexFunction (EuclideanSpace ℝ (Fin n)) :=
    ⟨projectiveProductToricEuclideanProfile u, projectiveProductToricEuclideanProfile_convex hu hiu⟩
  have he := integral_conjugate_difference_eq_affinePathEnergy volume
    (EuclideanSpace.basisFun (Fin n) ℝ) (isCompact_euclideanUnitCube n)
    (nonempty_euclideanUnitCube n) (convex_euclideanUnitCube n) (f := f) (g := g)
    (projectiveProductToricProfile_mem_boundedGrowthClass hφ hiφ hφb)
    (projectiveProductToricProfile_mem_boundedGrowthClass hu hiu hub)
  have hi : (∫ t in (0 : ℝ)..1, projectiveProductNativeTangentPolynomial hφ hu t) =
      ∫ t in (0 : ℝ)..1, affineTangentPolynomial volume (EuclideanSpace.basisFun (Fin n) ℝ) f g t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (1 : ℝ)] with t ht1
    intro ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    exact projectiveProductNativeTangent_eq_tropical hφ hu hiφ hiu hφb hub
      ⟨ht'.1, lt_of_le_of_ne ht'.2 ht1⟩
  rw [← intervalIntegral_projectiveProductNativeTangent_eq_relativeEnergy hφ hu hub, hi]
  exact he.symm

/-- The printed reference-zero source formula, with the actual product factorial normalization. -/
theorem projectiveProduct_relativeEnergyOfMinimalType_zero_eq_legendre {n : ℕ}
    {u : projectiveProductSpace n → EReal}
    (hu : IsThetaPshPotential (projectiveProductFSBackground n).form.val u)
    (hiu : ProjectiveProductCircleInvariant u) (hub : IsBoundedPotential u) :
    relativeEnergyOfMinimalType (projectiveProductFSBackground n).form
      (fun _ : projectiveProductSpace n => (0 : EReal)) u
      (isThetaPshPotential_projectiveProductZero n) hu =
      (n.factorial : ℝ) * ∫ m in euclideanUnitCube n,
        ((projectiveProductToricLegendre (fun _ : projectiveProductSpace n => (0 : EReal)) m).toReal -
          (projectiveProductToricLegendre u m).toReal) :=
  projectiveProduct_relativeEnergyOfMinimalType_eq_legendre
    (isThetaPshPotential_projectiveProductZero n) (fun _ _ _ => rfl) ⟨0, 0, fun _ => by simp⟩
    hu hiu hub

end SGPT.Toric
