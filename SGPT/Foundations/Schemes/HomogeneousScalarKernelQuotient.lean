import SGPT.Foundations.Schemes.HomogeneousSyzygyResolution
import SGPT.Foundations.Schemes.FiniteGradedPolynomialDegreePieces
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Genuine homogeneous scalar kernels and quotients

The actual projections commute with scalar multiplication with its true degree
shift. This produces the native annihilator and image gradings.
-/

universe u

open DirectSum

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section ScalarProjection

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M]
  (𝒜 : ℤ → Submodule K R) (ℳ : ℤ → Submodule K M)
  [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

/-- A genuine homogeneous scalar commutes with true projections with its actual degree shift. -/
theorem homogeneousScalar_decompose {a : ℤ} {x : R} (hx : x ∈ 𝒜 a)
    (m : ℤ) (v : M) :
    (DirectSum.decompose ℳ (x • v) (a + m) : M) =
      x • (DirectSum.decompose ℳ v m : M) := by
  classical
  refine DirectSum.Decomposition.inductionOn ℳ
    (motive := fun v => (DirectSum.decompose ℳ (x • v) (a + m) : M) =
      x • (DirectSum.decompose ℳ v m : M)) ?_ ?_ ?_ v
  · simp
  · intro j w
    have hw : x • (w : M) ∈ ℳ (a + j) :=
      SetLike.GradedSMul.smul_mem hx w.property
    by_cases hj : j = m
    · subst j
      rw [DirectSum.decompose_of_mem_same ℳ hw,
        DirectSum.decompose_of_mem_same ℳ w.property]
    · rw [DirectSum.decompose_of_mem_ne ℳ hw (by omega),
        DirectSum.decompose_of_mem_ne ℳ w.property hj, smul_zero]
  · intro v w hv hw
    simpa only [smul_add, DirectSum.decompose_add, DirectSum.add_apply,
      Submodule.coe_add] using congrArg₂ (· + ·) hv hw

/-- The native annihilator of an actual homogeneous scalar is genuinely homogeneous. -/
theorem homogeneousScalar_kernel_isHomogeneous {a : ℤ} {x : R} (hx : x ∈ 𝒜 a) :
    (LinearMap.ker (LinearMap.lsmul R M x)).IsHomogeneous ℳ := by
  intro m v hv
  change x • (DirectSum.decompose ℳ v m : M) = 0
  rw [← homogeneousScalar_decompose 𝒜 ℳ hx]
  change (DirectSum.decompose ℳ ((LinearMap.lsmul R M x) v) (a + m) : M) = 0
  rw [LinearMap.mem_ker.mp hv, DirectSum.decompose_zero]
  rfl

/-- The native image of an actual homogeneous scalar is genuinely homogeneous. -/
theorem homogeneousScalar_range_isHomogeneous {a : ℤ} {x : R} (hx : x ∈ 𝒜 a) :
    (LinearMap.range (LinearMap.lsmul R M x)).IsHomogeneous ℳ := by
  intro m v hv
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
  refine LinearMap.mem_range.mpr ⟨(DirectSum.decompose ℳ w (m - a) : M), ?_⟩
  change x • (DirectSum.decompose ℳ w (m - a) : M) =
    (DirectSum.decompose ℳ (x • w) m : M)
  have h := homogeneousScalar_decompose 𝒜 ℳ hx (m - a) w
  have he : a + (m - a) = m := by omega
  rw [he] at h
  exact h.symm

end ScalarProjection

section NativeQuotient

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  (ℳ : ℤ → Submodule K M) (p : Submodule R M)

/-- The literal degree piece in the native ring-module quotient. -/
def homogeneousRingQuotientPiece (m : ℤ) : Submodule K (M ⧸ p) :=
  (ℳ m).map (p.mkQ.restrictScalars K)

/-- The native quotient map restricted to the true homogeneous degree. -/
def homogeneousRingQuotientDegreeMap (m : ℤ) :
    ℳ m →ₗ[K] homogeneousRingQuotientPiece ℳ p m :=
  ((p.mkQ.restrictScalars K).comp (ℳ m).subtype).codRestrict _
    (fun v => Submodule.mem_map.mpr ⟨v, v.property, rfl⟩)

/-- Every element of an actual quotient degree piece has a genuine homogeneous representative. -/
theorem homogeneousRingQuotientDegreeMap_surjective (m : ℤ) :
    Function.Surjective (homogeneousRingQuotientDegreeMap ℳ p m) := by
  intro v
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp v.property
  exact ⟨⟨w, hw⟩, Subtype.ext hwv⟩

/-- The native ring quotient has a genuine internal grading induced by homogeneous relations. -/
@[instance_reducible]
def homogeneousRingQuotientDecomposition [DirectSum.Decomposition ℳ]
    (hp : p.IsHomogeneous ℳ) : DirectSum.Decomposition (homogeneousRingQuotientPiece ℳ p) := by
  exact homogeneousQuotientDecomposition ℳ (p.restrictScalars K) hp

variable (𝒜 : ℤ → Submodule K R) [SetLike.GradedSMul 𝒜 ℳ]

/-- Actual homogeneous scalar multiplication descends to actual native quotient degrees. -/
instance homogeneousRingQuotientGradedSMul :
    SetLike.GradedSMul 𝒜 (homogeneousRingQuotientPiece ℳ p) where
  smul_mem := by
    intro a m x v hx hv
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨x • w, SetLike.GradedSMul.smul_mem hx hw, ?_⟩
    change p.mkQ (x • w) = x • v
    change p.mkQ w = v at hwv
    rw [map_smul, hwv]

end NativeQuotient

section ScalarKernelQuotient

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  (𝒜 : ℤ → Submodule K R) (ℳ : ℤ → Submodule K M)
  [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

/-- The true scalar annihilator carries the actual induced internal grading. -/
@[instance_reducible]
def homogeneousScalarKernelDecomposition {a : ℤ} {x : R} (hx : x ∈ 𝒜 a) :
    DirectSum.Decomposition
      (homogeneousSubmodulePiece ℳ (LinearMap.ker (LinearMap.lsmul R M x))) :=
  homogeneousSubmoduleDecomposition ℳ _ (homogeneousScalar_kernel_isHomogeneous 𝒜 ℳ hx)

/-- The true quotient by homogeneous scalar multiplication carries its actual internal grading. -/
@[instance_reducible]
def homogeneousScalarQuotientDecomposition {a : ℤ} {x : R} (hx : x ∈ 𝒜 a) :
    DirectSum.Decomposition
      (homogeneousRingQuotientPiece ℳ (LinearMap.range (LinearMap.lsmul R M x))) :=
  homogeneousRingQuotientDecomposition ℳ _ (homogeneousScalar_range_isHomogeneous 𝒜 ℳ hx)

end ScalarKernelQuotient

section ScalarAnnihilation

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (x : R)

/-- The actual scalar annihilator is killed by the actual scalar. -/
theorem scalarKernel_smul_eq_zero (u : LinearMap.ker (LinearMap.lsmul R M x)) :
    x • u = 0 := Subtype.ext u.property

/-- The actual quotient by the scalar image is killed by the actual scalar. -/
theorem scalarQuotient_smul_eq_zero (v : M ⧸ LinearMap.range (LinearMap.lsmul R M x)) :
    x • v = 0 := by
  refine Submodule.Quotient.induction_on _ v ?_
  intro w
  change Submodule.Quotient.mk (x • w) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact LinearMap.mem_range.mpr ⟨w, rfl⟩

/-- Noetherianness makes the true scalar annihilator an actual finite module. -/
theorem scalarKernel_finite [IsNoetherianRing R] [Module.Finite R M] :
    Module.Finite R (LinearMap.ker (LinearMap.lsmul R M x)) := by infer_instance

/-- The true quotient of a finite module is an actual finite module. -/
theorem scalarQuotient_finite [Module.Finite R M] :
    Module.Finite R (M ⧸ LinearMap.range (LinearMap.lsmul R M x)) := by infer_instance

end ScalarAnnihilation

section ScalarDegreeExactness

variable {K R M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  (𝒜 : ℤ → Submodule K R) (ℳ : ℤ → Submodule K M)
  [SetLike.GradedSMul 𝒜 ℳ]
  {a : ℤ} {x : R} (hx : x ∈ 𝒜 a)

/-- Literal scalar multiplication on the actual source and shifted target degrees. -/
def homogeneousScalarDegreeMap (m : ℤ) : ℳ m →ₗ[K] ℳ (a + m) :=
  (((LinearMap.lsmul R M x).restrictScalars K).comp (ℳ m).subtype).codRestrict _
    (fun v => SetLike.GradedSMul.smul_mem hx v.property)

/-- The native kernel of the actual degree map is the genuine annihilator degree piece. -/
def homogeneousScalarDegreeKernelEquiv (m : ℤ) :
    LinearMap.ker (homogeneousScalarDegreeMap 𝒜 ℳ hx m) ≃ₗ[K]
      homogeneousSubmodulePiece ℳ (LinearMap.ker (LinearMap.lsmul R M x)) m where
  toFun v := ⟨⟨v.val.val, congrArg Subtype.val v.property⟩, v.val.property⟩
  invFun u := ⟨⟨u.val.val, u.property⟩, Subtype.ext u.val.property⟩
  left_inv _v := rfl
  right_inv _u := rfl
  map_add' _v _w := rfl
  map_smul' _c _v := rfl

/-- The native restricted image equals the native restricted quotient kernel. -/
theorem homogeneousScalarDegreeMap_range_eq_quotient_ker [DirectSum.Decomposition ℳ]
    (m : ℤ) :
    LinearMap.range (homogeneousScalarDegreeMap 𝒜 ℳ hx m) =
      LinearMap.ker (homogeneousRingQuotientDegreeMap ℳ
        (LinearMap.range (LinearMap.lsmul R M x)) (a + m)) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
    apply Subtype.ext
    change (LinearMap.range (LinearMap.lsmul R M x)).mkQ (x • (w : M)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact LinearMap.mem_range.mpr ⟨(w : M), rfl⟩
  · intro v hv
    have hz := congrArg Subtype.val hv
    change (LinearMap.range (LinearMap.lsmul R M x)).mkQ (v : M) = 0 at hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp hz)
    refine LinearMap.mem_range.mpr ⟨DirectSum.decompose ℳ w m, ?_⟩
    apply Subtype.ext
    change x • (DirectSum.decompose ℳ w m : M) = (v : M)
    rw [← homogeneousScalar_decompose 𝒜 ℳ hx]
    change (DirectSum.decompose ℳ ((LinearMap.lsmul R M x) w) (a + m) : M) = (v : M)
    rw [hw, DirectSum.decompose_of_mem_same ℳ v.property]

end ScalarDegreeExactness

section ScalarDegreeDimensions

variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  (𝒜 : ℤ → Submodule K R) (ℳ : ℤ → Submodule K M)
  [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  {a : ℤ} {x : R} (hx : x ∈ 𝒜 a) (m : ℤ)
  [Module.Finite K (ℳ m)] [Module.Finite K (ℳ (a + m))]

include hx in
/-- Actual native degreewise rank-nullity gives the genuine scalar dimension recurrence. -/
theorem homogeneousScalarDegree_finrank_recurrence :
    Module.finrank K (ℳ (a + m)) +
      Module.finrank K (homogeneousSubmodulePiece ℳ
        (LinearMap.ker (LinearMap.lsmul R M x)) m) =
    Module.finrank K (ℳ m) +
      Module.finrank K (homogeneousRingQuotientPiece ℳ
        (LinearMap.range (LinearMap.lsmul R M x)) (a + m)) := by
  let f := homogeneousScalarDegreeMap 𝒜 ℳ hx m
  let g := homogeneousRingQuotientDegreeMap ℳ
    (LinearMap.range (LinearMap.lsmul R M x)) (a + m)
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hgr : LinearMap.range g = ⊤ := LinearMap.range_eq_top.mpr
    (homogeneousRingQuotientDegreeMap_surjective ℳ _ (a + m))
  rw [hgr, finrank_top] at hg
  have hu := (homogeneousScalarDegreeKernelEquiv 𝒜 ℳ hx m).finrank_eq
  change Module.finrank K (LinearMap.ker f) = _ at hu
  rw [hu] at hf
  have hr := congrArg (fun p : Submodule K (ℳ (a + m)) => Module.finrank K p)
    (homogeneousScalarDegreeMap_range_eq_quotient_ker 𝒜 ℳ hx m)
  change Module.finrank K (LinearMap.range f) = Module.finrank K (LinearMap.ker g) at hr
  omega

end ScalarDegreeDimensions

section PolynomialCoordinateDimensions

variable {K I M : Type u} [Field K] [hI : Fintype I]
  [AddCommGroup M] [Module K M] [Module (MvPolynomial I K) M]
  [hTower : IsScalarTower K (MvPolynomial I K) M]
  (ℳ : ℤ → Submodule K M) [hDecomp : DirectSum.Decomposition ℳ]
  [hGraded : SetLike.GradedSMul (polynomialIntegralGrading (K := K) (I := I)) ℳ]
  [hFinite : Module.Finite (MvPolynomial I K) M]

include hI hTower hDecomp hGraded hFinite

/-- Every actual finite graded polynomial module has the genuine coordinate dimension recurrence. -/
theorem finiteGradedPolynomialCoordinate_finrank_recurrence (i : I) (m : ℤ) :
    Module.finrank K (ℳ (1 + m)) +
      Module.finrank K (homogeneousSubmodulePiece ℳ
        (LinearMap.ker (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i))) m) =
    Module.finrank K (ℳ m) +
      Module.finrank K (homogeneousRingQuotientPiece ℳ
        (LinearMap.range (LinearMap.lsmul (MvPolynomial I K) M (MvPolynomial.X i))) (1 + m)) := by
  let := finiteGradedPolynomialPiece_finite (K := K) (I := I) ℳ m
  let := finiteGradedPolynomialPiece_finite (K := K) (I := I) ℳ (1 + m)
  exact homogeneousScalarDegree_finrank_recurrence
    (polynomialIntegralGrading (K := K) (I := I)) ℳ
    (MvPolynomial.isWeightedHomogeneous_X K (fun _ : I => (1 : ℤ)) i) m

end PolynomialCoordinateDimensions

end

end SGPT.Foundations.Schemes
