import SGPT.Foundations.Analysis.Pending.NaturalHermitianSmoothFormMetric
import SGPT.Foundations.Analysis.Pending.CanonicalSmoothCurrentDensity

/-! # Actual perfect complementary wedge duality of original continuous form coefficients -/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalOriginalComplementaryWedgeDuality

open FirstPass FirstPass.MongeAmpere NaturalHermitianOriginalFormMetric
  NaturalHermitianSmoothFormMetric CanonicalCurrentFrame CanonicalSmoothCurrentDensity
  ConstantFormProducts StronglyPositiveForms
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {n k q : ℕ}

local instance formNormedAddCommGroup (j : ℕ) : NormedAddCommGroup (FormCoefficients n j) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (j : ℕ) : NormedSpace ℝ (FormCoefficients n j) :=
  ContinuousAlternatingMap.instNormedSpace

local instance formDualNormedAddCommGroup (j : ℕ) :
    NormedAddCommGroup (FormCoefficients n j →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formDualNormedSpace (j : ℕ) : NormedSpace ℝ (FormCoefficients n j →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Literal right volume contraction, upgraded in the unchanged original finite-dimensional norm. -/
def rightVolumeContraction (vol : (ComplexModel n) [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ)
    (w : Fin q → ComplexModel n) : FormCoefficients n k :=
  algebraicContinuousEquiv k
    ((formEvaluationCLM w).toLinearMap.compAlternatingMap (volumeContraction vol))

/-- Full original tuple readback of the actual right contraction. -/
theorem rightVolumeContraction_apply
    (vol : (ComplexModel n) [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ)
    (w : Fin q → ComplexModel n) (v : Fin k → ComplexModel n) :
    rightVolumeContraction vol w v = vol (Sum.elim v w) := by
  rw [rightVolumeContraction, algebraicContinuousEquiv_apply]
  rfl

/-- Exact value identity between the two genuine block contractions. -/
theorem rightVolumeContraction_eq_contractVolume
    (vol : (ComplexModel n) [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ)
    (w : Fin q → ComplexModel n) (v : Fin k → ComplexModel n) :
    rightVolumeContraction vol w v = contractVolume vol v w := by
  rw [rightVolumeContraction_apply, contractVolume_apply]

/-- Actual alternating dependence of right contraction on its original inserted tuple. -/
def rightVolumeContractionAlternating
    (vol : (ComplexModel n) [⋀^(Fin k ⊕ Fin q)]→L[ℝ] ℝ) :
    (ComplexModel n) [⋀^Fin q]→ₗ[ℝ] (FormCoefficients n k) where
  toFun := rightVolumeContraction vol
  map_update_add' w i a b := by
    ext v
    simp only [rightVolumeContraction_apply, ContinuousAlternatingMap.add_apply,
      Sum.elim_update_right]
    exact vol.map_update_add (Sum.elim v w) (Sum.inr i) a b
  map_update_smul' w i r a := by
    ext v
    simp only [rightVolumeContraction_apply, ContinuousAlternatingMap.smul_apply,
      Sum.elim_update_right]
    exact vol.map_update_smul (Sum.elim v w) (Sum.inr i) r a
  map_eq_zero_of_eq' w i j hw hij := by
    ext v
    rw [rightVolumeContraction_apply]
    exact vol.map_eq_zero_of_eq (Sum.elim v w) (i := Sum.inr i) (j := Sum.inr j)
      hw (Sum.inr_injective.ne hij)

/-- The actual finite normalized scalar shuffle pairing in the original two form norms. -/
def scalarShufflePairingCLM (v : Fin k ⊕ Fin q → ComplexModel n) :
    FormCoefficients n q →L[ℝ] FormCoefficients n k →L[ℝ] ℝ :=
  ∑ s : Equiv.Perm.ModSumCongr (Fin k) (Fin q),
    Equiv.Perm.sign s.out •
      (formEvaluationCLM (fun j => v (s.out (Sum.inr j)))).smulRight
        (formEvaluationCLM (fun i => v (s.out (Sum.inl i))))

/-- Literal normalized pairing, with the left form first in the actual exterior product. -/
theorem scalarShufflePairingCLM_apply (v : Fin k ⊕ Fin q → ComplexModel n)
    (η : FormCoefficients n q) (ξ : FormCoefficients n k) :
    scalarShufflePairingCLM v η ξ =
      ∑ s : Equiv.Perm.ModSumCongr (Fin k) (Fin q),
        Equiv.Perm.sign s.out •
          (ξ (fun i => v (s.out (Sum.inl i))) * η (fun j => v (s.out (Sum.inr j)))) := by
  simp [scalarShufflePairingCLM, sum_apply, mul_comm]

private lemma modSumCongr_crosses_relative
    (σ : Equiv.Perm (Fin k ⊕ Fin q)) (s : Equiv.Perm.ModSumCongr (Fin k) (Fin q))
    (hs : s ≠ QuotientGroup.mk σ) : ∃ j i, s.out (Sum.inr j) = σ (Sum.inl i) := by
  by_contra h
  push Not at h
  let δ : Equiv.Perm (Fin k ⊕ Fin q) := σ⁻¹ * s.out
  have hr : Set.MapsTo δ (Set.range (@Sum.inr (Fin k) (Fin q)))
      (Set.range (@Sum.inr (Fin k) (Fin q))) := by
    rintro _ ⟨j, rfl⟩
    rcases heq : δ (Sum.inr j) with i | j'
    · have : s.out (Sum.inr j) = σ (Sum.inl i) := by
        have := congrArg σ heq
        simpa [δ] using this
      exact (h j i this).elim
    · exact ⟨j', rfl⟩
  have hl : Set.MapsTo δ (Set.range (@Sum.inl (Fin k) (Fin q)))
      (Set.range (@Sum.inl (Fin k) (Fin q))) :=
    (Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr δ).2 hr
  have hδ : δ ∈ (Equiv.Perm.sumCongrHom (Fin k) (Fin q)).range :=
    Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hl
  have hm : QuotientGroup.mk σ = QuotientGroup.mk s.out := Quotient.sound' (by
    rw [QuotientGroup.leftRel_apply]
    exact hδ)
  exact hs (hm.trans (Quotient.out_eq' s)).symm

private lemma modSumCongr_crosses_left_relative
    (σ : Equiv.Perm (Fin k ⊕ Fin q)) (s : Equiv.Perm.ModSumCongr (Fin k) (Fin q))
    (hs : s ≠ QuotientGroup.mk σ) : ∃ i j, s.out (Sum.inl i) = σ (Sum.inr j) := by
  by_contra h
  push Not at h
  let δ : Equiv.Perm (Fin k ⊕ Fin q) := σ⁻¹ * s.out
  have hl : Set.MapsTo δ (Set.range (@Sum.inl (Fin k) (Fin q)))
      (Set.range (@Sum.inl (Fin k) (Fin q))) := by
    rintro _ ⟨i, rfl⟩
    rcases heq : δ (Sum.inl i) with i' | j
    · exact ⟨i', rfl⟩
    · have : s.out (Sum.inl i) = σ (Sum.inr j) := by
        have := congrArg σ heq
        simpa [δ] using this
      exact (h i j this).elim
  have hδ : δ ∈ (Equiv.Perm.sumCongrHom (Fin k) (Fin q)).range :=
    Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hl
  have hm : QuotientGroup.mk σ = QuotientGroup.mk s.out := Quotient.sound' (by
    rw [QuotientGroup.leftRel_apply]
    exact hδ)
  exact hs (hm.trans (Quotient.out_eq' s)).symm

private lemma scalarWedgeTerm_eq_summand (v : Fin k ⊕ Fin q → ComplexModel n)
    (a : (ComplexModel n) [⋀^Fin k]→ₗ[ℝ] ℝ)
    (c : (ComplexModel n) [⋀^Fin q]→ₗ[ℝ] ℝ)
    (s : Equiv.Perm.ModSumCongr (Fin k) (Fin q)) :
    Equiv.Perm.sign s.out •
      (a (fun i => v (s.out (Sum.inl i))) * c (fun j => v (s.out (Sum.inr j)))) =
      (TensorProduct.lid ℝ ℝ) (AlternatingMap.domCoprod.summand a c s v) := by
  conv_rhs => rw [← Quotient.out_eq s, AlternatingMap.domCoprod.summand_mk'']
  change (Equiv.Perm.sign s.out : ℤ) •
    (a (fun i => v (s.out (Sum.inl i))) * c (fun j => v (s.out (Sum.inr j)))) =
    (TensorProduct.lid ℝ ℝ) ((Equiv.Perm.sign s.out : ℤ) •
      (a (fun i => v (s.out (Sum.inl i))) ⊗ₜ[ℝ]
        c (fun j => v (s.out (Sum.inr j)))))
  rw [map_zsmul, TensorProduct.lid_tmul, smul_eq_mul]

/-- Full right-form reconstruction by genuine normalized signed left volume contractions. -/
theorem right_shuffle_reconstruction (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n))
    (η : FormCoefficients n q) :
    (∑ s : Equiv.Perm.ModSumCongr (Fin k) (Fin q), Equiv.Perm.sign s.out •
      (η (fun j => b (s.out (Sum.inr j))) •
        contractVolume (basisVolume b) (fun i => b (s.out (Sum.inl i))))) = η := by
  classical
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating b
  intro a ha
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (@Sum.inr (Fin k) (Fin q)) a Sum.inr_injective ha
  let s₀ : Equiv.Perm.ModSumCongr (Fin k) (Fin q) := QuotientGroup.mk σ
  change (∑ s : Equiv.Perm.ModSumCongr (Fin k) (Fin q), Equiv.Perm.sign s.out •
    (η (fun j => b (s.out (Sum.inr j))) •
      contractVolume (basisVolume b) (fun i => b (s.out (Sum.inl i)))))
    (fun j => b (a j)) = η (fun j => b (a j))
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single s₀]
  · rw [← rightVolumeContraction_eq_contractVolume]
    change Equiv.Perm.sign s₀.out •
      (η (fun j => b (s₀.out (Sum.inr j))) *
        rightVolumeContraction (basisVolume b) (fun j => b (a j))
          (fun i => b (s₀.out (Sum.inl i)))) = η (fun j => b (a j))
    have hterm := scalarWedgeTerm_eq_summand b
      (rightVolumeContraction (basisVolume b) (fun j => b (a j))).toAlternatingMap
      η.toAlternatingMap s₀
    simp only [ContinuousAlternatingMap.coe_toAlternatingMap] at hterm
    rw [mul_comm, hterm]
    dsimp only [s₀]
    rw [AlternatingMap.domCoprod.summand_mk'']
    simp only [smul_apply, MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply]
    rw [Units.smul_def, map_zsmul, TensorProduct.lid_tmul, smul_eq_mul]
    change Equiv.Perm.sign σ •
      (rightVolumeContraction (basisVolume b) (fun j => b (a j))
        (fun i => b (σ (Sum.inl i))) *
        η (fun j => b (σ (Sum.inr j)))) = η (fun j => b (a j))
    rw [rightVolumeContraction_eq_contractVolume]
    have hvol : contractVolume (basisVolume b) (fun i => b (σ (Sum.inl i)))
        (fun j => b (a j)) = Equiv.Perm.sign σ • (1 : ℝ) := by
      change basisVolume b (Sum.elim (fun i => b (σ (Sum.inl i))) (fun j => b (a j))) = _
      have hf : Sum.elim (fun i => b (σ (Sum.inl i))) (fun j => b (a j)) = b ∘ σ := by
        funext x
        rcases x with i | j
        · rfl
        · exact congrArg b (hσ j).symm
      rw [hf]
      exact ((basisVolume b).toAlternatingMap.map_perm b σ).trans
        (congrArg (fun r : ℝ => Equiv.Perm.sign σ • r) (basisVolume_self b))
    rw [hvol]
    simp only [hσ]
    simp [smul_smul]
  · intro s _ hs
    obtain ⟨i, j, hcross⟩ := modSumCongr_crosses_left_relative σ s hs
    have hvol : contractVolume (basisVolume b) (fun i => b (s.out (Sum.inl i)))
        (fun j => b (a j)) = 0 := by
      change basisVolume b (Sum.elim (fun i => b (s.out (Sum.inl i))) (fun j => b (a j))) = 0
      apply (basisVolume b).map_eq_zero_of_eq _ (i := Sum.inl i) (j := Sum.inr j)
      · change b (s.out (Sum.inl i)) = b (a j)
        rw [hcross, hσ]
      · exact Sum.inl_ne_inr
    change Equiv.Perm.sign s.out •
      (η (fun j => b (s.out (Sum.inr j))) *
        contractVolume (basisVolume b) (fun i => b (s.out (Sum.inl i)))
          (fun j => b (a j))) = 0
    rw [hvol]
    simp
  · simp

/-- Full left-form reconstruction by genuine normalized signed right volume contractions. -/
theorem left_shuffle_reconstruction (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n))
    (ξ : FormCoefficients n k) :
    (∑ s : Equiv.Perm.ModSumCongr (Fin k) (Fin q), Equiv.Perm.sign s.out •
      (ξ (fun i => b (s.out (Sum.inl i))) •
        rightVolumeContraction (basisVolume b) (fun j => b (s.out (Sum.inr j))))) = ξ := by
  classical
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating b
  intro a ha
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (@Sum.inl (Fin k) (Fin q)) a Sum.inl_injective ha
  let s₀ : Equiv.Perm.ModSumCongr (Fin k) (Fin q) := QuotientGroup.mk σ
  change (∑ s : Equiv.Perm.ModSumCongr (Fin k) (Fin q), Equiv.Perm.sign s.out •
    (ξ (fun i => b (s.out (Sum.inl i))) •
      rightVolumeContraction (basisVolume b) (fun j => b (s.out (Sum.inr j)))))
    (fun i => b (a i)) = ξ (fun i => b (a i))
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single s₀]
  · rw [rightVolumeContraction_eq_contractVolume]
    change Equiv.Perm.sign s₀.out •
      (ξ (fun i => b (s₀.out (Sum.inl i))) *
        contractVolume (basisVolume b) (fun i => b (a i))
          (fun j => b (s₀.out (Sum.inr j)))) = ξ (fun i => b (a i))
    have hterm := scalarWedgeTerm_eq_summand b ξ.toAlternatingMap
      (contractVolume (basisVolume b) (fun i => b (a i))).toAlternatingMap s₀
    simp only [ContinuousAlternatingMap.coe_toAlternatingMap] at hterm
    rw [hterm]
    dsimp only [s₀]
    rw [AlternatingMap.domCoprod.summand_mk'']
    simp only [smul_apply, MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply]
    rw [Units.smul_def, map_zsmul, TensorProduct.lid_tmul, smul_eq_mul]
    change Equiv.Perm.sign σ •
      (ξ (fun i => b (σ (Sum.inl i))) *
        contractVolume (basisVolume b) (fun i => b (a i))
          (fun j => b (σ (Sum.inr j)))) = ξ (fun i => b (a i))
    have hvol : contractVolume (basisVolume b) (fun i => b (a i))
        (fun j => b (σ (Sum.inr j))) = Equiv.Perm.sign σ • (1 : ℝ) := by
      change basisVolume b (Sum.elim (fun i => b (a i)) (fun j => b (σ (Sum.inr j)))) = _
      have hf : Sum.elim (fun i => b (a i)) (fun j => b (σ (Sum.inr j))) = b ∘ σ := by
        funext x
        rcases x with i | j
        · exact congrArg b (hσ i).symm
        · rfl
      rw [hf]
      exact ((basisVolume b).toAlternatingMap.map_perm b σ).trans
        (congrArg (fun r : ℝ => Equiv.Perm.sign σ • r) (basisVolume_self b))
    rw [hvol]
    simp only [hσ]
    simp [smul_smul]
  · intro s _ hs
    obtain ⟨j, i, hcross⟩ := modSumCongr_crosses_relative σ s hs
    have hvol : rightVolumeContraction (basisVolume b) (fun j => b (s.out (Sum.inr j)))
        (fun i => b (a i)) = 0 := by
      rw [rightVolumeContraction_apply]
      apply (basisVolume b).map_eq_zero_of_eq _ (i := Sum.inl i) (j := Sum.inr j)
      · change b (a i) = b (s.out (Sum.inr j))
        rw [hcross, hσ]
      · exact Sum.inl_ne_inr
    change Equiv.Perm.sign s.out •
      (ξ (fun i => b (s.out (Sum.inl i))) *
        rightVolumeContraction (basisVolume b) (fun j => b (s.out (Sum.inr j)))
          (fun i => b (a i))) = 0
    rw [hvol]
    simp
  · simp

/-- Actual algebraic inverse, applying the original functional to genuine right volume contraction. -/
def scalarWedgeInverseLinear (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n)) :
    (FormCoefficients n k →L[ℝ] ℝ) →ₗ[ℝ] FormCoefficients n q where
  toFun L := algebraicContinuousEquiv q
    (L.toLinearMap.compAlternatingMap (rightVolumeContractionAlternating (basisVolume b)))
  map_add' L K := by
    ext w
    simp only [ContinuousAlternatingMap.add_apply, algebraicContinuousEquiv_apply,
      LinearMap.compAlternatingMap_apply, ContinuousLinearMap.coe_coe, add_apply]
  map_smul' r L := by
    ext w
    simp only [ContinuousAlternatingMap.smul_apply, algebraicContinuousEquiv_apply,
      LinearMap.compAlternatingMap_apply, ContinuousLinearMap.coe_coe, smul_apply, RingHom.id_apply]

/-- Actual continuity of the whole inverse in the original finite-dimensional dual and form norms. -/
def scalarWedgeInverseCLM (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n)) :
    (FormCoefficients n k →L[ℝ] ℝ) →L[ℝ] FormCoefficients n q :=
  (scalarWedgeInverseLinear b).toContinuousLinearMap

/-- Full arbitrary original tuple readback of the actual continuous inverse. -/
theorem scalarWedgeInverseCLM_apply (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n))
    (L : FormCoefficients n k →L[ℝ] ℝ) (w : Fin q → ComplexModel n) :
    scalarWedgeInverseCLM b L w = L (rightVolumeContraction (basisVolume b) w) := by
  change algebraicContinuousEquiv q
    (L.toLinearMap.compAlternatingMap (rightVolumeContractionAlternating (basisVolume b))) w = _
  rw [algebraicContinuousEquiv_apply]
  rfl

/-- The actual inverse of the scalar wedge pairing recovers every whole original right form. -/
theorem scalarWedgeInverse_pairing (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n))
    (η : FormCoefficients n q) :
    scalarWedgeInverseCLM b (scalarShufflePairingCLM b η) = η := by
  ext w
  rw [scalarWedgeInverseCLM_apply, scalarShufflePairingCLM_apply]
  have h := congrArg (fun F : FormCoefficients n q => F w) (right_shuffle_reconstruction b η)
  simpa only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, contractVolume_apply, rightVolumeContraction_apply, mul_comm] using h

/-- The scalar wedge pairing of its actual inverse recovers every entire original functional. -/
theorem scalarPairing_wedgeInverse (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n))
    (L : FormCoefficients n k →L[ℝ] ℝ) :
    scalarShufflePairingCLM b (scalarWedgeInverseCLM b L) = L := by
  ext ξ
  rw [scalarShufflePairingCLM_apply]
  simp only [scalarWedgeInverseCLM_apply]
  have h := congrArg L (left_shuffle_reconstruction b ξ)
  simpa only [map_sum, Units.smul_def, map_zsmul, map_smul, smul_eq_mul] using h

/-- Genuine perfect complementary wedge equivalence in the original coefficient and dual norms. -/
def complementaryWedgeEquiv (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n)) :
    FormCoefficients n q ≃L[ℝ] (FormCoefficients n k →L[ℝ] ℝ) where
  toLinearEquiv :=
    { (scalarShufflePairingCLM b).toLinearMap with
      invFun := scalarWedgeInverseCLM b
      left_inv := scalarWedgeInverse_pairing b
      right_inv := scalarPairing_wedgeInverse b }
  continuous_toFun := (scalarShufflePairingCLM b).continuous
  continuous_invFun := (scalarWedgeInverseCLM b).continuous

/-- Entire normalized geometric exterior-product calibration of the actual scalar pairing. -/
theorem scalarShufflePairingCLM_eq_coordinateWedge (v : Fin k ⊕ Fin q → ComplexModel n)
    (η : FormCoefficients n q) (ξ : FormCoefficients n k) :
    scalarShufflePairingCLM v η ξ =
      coordinateWedge ξ η (fun i => v (finSumFinEquiv.symm i)) := by
  rw [coordinateWedge_apply]
  have hv : (fun i => v (finSumFinEquiv.symm i)) ∘ finSumFinEquiv = v := by
    funext i
    simp
  rw [hv]
  change scalarShufflePairingCLM v η ξ = (coordinateWedgeSum ξ η).toAlternatingMap v
  rw [coordinateWedgeSum_toAlternatingMap, LinearMap.compAlternatingMap_apply,
    scalarShufflePairingCLM_apply, AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  have h := scalarWedgeTerm_eq_summand v ξ.toAlternatingMap η.toAlternatingMap s
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap, LinearEquiv.coe_coe] using h

/-- Actual canonical complex-positive complementary wedge equivalence, including both endpoint degrees. -/
def canonicalComplementaryWedgeEquiv (j : CurrentDegree n) :
    FormCoefficients n (Module.finrank ℝ (ComplexModel n) - j.val) ≃L[ℝ]
      (FormCoefficients n j.val →L[ℝ] ℝ) :=
  complementaryWedgeEquiv (currentPairingBasis (canonicalBasis n) j)

/-- Literal full canonical density readback, with the actual original orientation and normalization. -/
theorem canonicalComplementaryWedgeEquiv_apply (j : CurrentDegree n)
    (η : FormCoefficients n (Module.finrank ℝ (ComplexModel n) - j.val))
    (ξ : FormCoefficients n j.val) :
    canonicalComplementaryWedgeEquiv j η ξ = TopDegreeDensity.topDensity
      (wedgeTo (by have hj := j.is_lt; rw [← complexModel_real_finrank n]; omega)
        ξ η) := by
  change scalarShufflePairingCLM (currentPairingBasis (canonicalBasis n) j) η ξ = _
  rw [scalarShufflePairingCLM_apply]
  simpa only [Units.smul_def, zsmul_eq_mul] using shuffleDensity_eq_topDensity ξ η

/-- Every entire original continuous form in excessive degree actually vanishes. -/
theorem originalForm_above_dimension (j : ℕ) (hj : n * 2 < j) (η : FormCoefficients n j) : η = 0 := by
  let : IsEmpty (FormIndex n j) := ⟨fun s => by
    have hle : s.val.card ≤ n * 2 := by simpa using Finset.card_le_univ s.val
    have hcard : s.val.card = j := s.property
    omega⟩
  have h := (originalFormBasis j).sum_repr η
  simpa using h.symm

end SGPT.Foundations.Analysis.Pending.NaturalOriginalComplementaryWedgeDuality
