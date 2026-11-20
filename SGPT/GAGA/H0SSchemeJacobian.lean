import SGPT.GAGA.H0SSchemeEquations
import Mathlib.Algebra.DualNumber

/-!
# The Jacobian criterion for `X(ℂ) ⊆ ℙᴺ`


Let `p ∈ Uᵢ(ℂ)` with affine coordinates `y₀ ∈ ℂᴺ`, and `w ∈ ℂᴺ` killed by the differentials at
`y₀` of the equations of `X ∩ D₊(xᵢ)`.  Then `w` is tangent to `X(ℂ)`: it is the image of a
tangent vector `v` of the chart of `X(ℂ)` at `p` (`exists_fderiv_eq_of_jacobian`).

Proof (dual numbers).  `P ↦ P(y₀ + w ε)` is a ring map `ℂ[t] → ℂ[ε]` (`ε² = 0`) killing the
equations, hence the ideal `Iᵢ`, so it factors through `Γ(X, Uᵢ)` and extends to the local ring
`𝒪_{X,x}` (its values at elements not vanishing at `p` are units).  The map
`a ↦ a(p) + D_v(a^an) ε` (`dualGerm`, `D_v` the derivative along `v` of the analytic germ) is
another such ring map.  Choosing `v` as the `ε`-parts of the free generators of the standard
smooth chart at `p`, the two maps agree on that chart's ring, since the difference of their
`ε`-parts is a derivation vanishing on the free generators, which span its Kähler differentials
(`Algebra.SubmersivePresentation.basisKaehler`; `eq_of_freeGenerator`).  The chart ring's
localization is the local ring, so the two maps agree; evaluating at the ratios `x_k/x_i` gives
`w = Dφ(v)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.H0S

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaHolomorphicJetMonomialSpan HolomorphicGermCoordinateDerivation
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open scoped Topology Manifold

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Dual-number evaluation of polynomials -/

/-- `P(y + w ε) = P(y) + DP(y)·w ε`. -/
theorem aeval_dual {N : ℕ} (y w : ComplexModel N) (P : MvPolynomial (Fin N) ℂ) :
    (MvPolynomial.aeval (fun a => (TrivSqZeroExt.inl (y a) + TrivSqZeroExt.inr (w a) :
      DualNumber ℂ)) P).fst = MvPolynomial.eval (fun a => y a) P ∧
    (MvPolynomial.aeval (fun a => (TrivSqZeroExt.inl (y a) + TrivSqZeroExt.inr (w a) :
      DualNumber ℂ)) P).snd = fderiv ℂ (fun z : ComplexModel N => MvPolynomial.eval (fun a => z a) P) y w := by
  induction P using MvPolynomial.induction_on with
  | C b =>
    refine ⟨by simp [TrivSqZeroExt.algebraMap_eq_inl], ?_⟩
    simp only [MvPolynomial.aeval_C, MvPolynomial.eval_C, TrivSqZeroExt.algebraMap_eq_inl,
      TrivSqZeroExt.snd_inl]
    rw [fderiv_const_apply]
    rfl
  | add P Q hP hQ =>
    simp only [map_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, hP.1, hQ.1, hP.2, hQ.2,
      true_and]
    rw [fderiv_fun_add (differentiable_eval_mvPolynomial P y) (differentiable_eval_mvPolynomial Q y)]
    rfl
  | mul_X P a hP =>
    have hd : HasFDerivAt (fun z : ComplexModel N => z a)
        (EuclideanSpace.proj (𝕜 := ℂ) a : ComplexModel N →L[ℂ] ℂ) y :=
      (EuclideanSpace.proj (𝕜 := ℂ) a).hasFDerivAt
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, add_zero, zero_add,
      hP.1, hP.2, true_and, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    rw [fderiv_fun_mul (differentiable_eval_mvPolynomial P y) hd.differentiableAt, hd.fderiv]
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    change _ = MvPolynomial.eval (fun b => y b) P * w a + y a * _
    ring

/-! ### Derivations of the standard smooth chart ring -/

section ChartRing

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (p : SchemeComplexPoint f)

local instance h0sJacChartAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- **Two dual-number points of the standard smooth chart ring with the same values agree if
they agree on the free generators.** -/
theorem eq_of_freeGenerator (Θ₁ Θ₂ : SchemeCoordinateAffineRing f n p →+* DualNumber ℂ)
    (hfst : ∀ a, (Θ₁ a).fst = (Θ₂ a).fst)
    (hc₁ : ∀ c : ℂ, Θ₁ (algebraMap ℂ _ c) = TrivSqZeroExt.inl c)
    (hc₂ : ∀ c : ℂ, Θ₂ (algebraMap ℂ _ c) = TrivSqZeroExt.inl c)
    (hgen : ∀ k, Θ₁ (standardSmoothComplexChartFreeGenerator f n p k) =
      Θ₂ (standardSmoothComplexChartFreeGenerator f n p k)) : Θ₁ = Θ₂ := by
  set χ : SchemeCoordinateAffineRing f n p →+* ℂ :=
    (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp Θ₁ with hχdef
  have hχ : ∀ a, χ a = (Θ₁ a).fst := fun a => rfl
  have hχc : ∀ c : ℂ, χ (algebraMap ℂ (SchemeCoordinateAffineRing f n p) c) = c := fun c => by
    rw [hχ, hc₁, TrivSqZeroExt.fst_inl]
  let : Module (SchemeCoordinateAffineRing f n p) ℂ := Module.compHom ℂ χ
  have hsmul : ∀ (a : SchemeCoordinateAffineRing f n p) (m : ℂ), a • m = χ a * m := fun _ _ => rfl
  have : IsScalarTower ℂ (SchemeCoordinateAffineRing f n p) ℂ := ⟨fun c a m => by
    show χ (c • a) * m = c * (χ a * m)
    rw [Algebra.smul_def, map_mul, hχc, mul_assoc]⟩
  -- the difference of the `ε`-parts is a derivation
  have hsnd_mul : ∀ (Θ : SchemeCoordinateAffineRing f n p →+* DualNumber ℂ)
      (a b : SchemeCoordinateAffineRing f n p),
      (Θ (a * b)).snd = (Θ a).fst * (Θ b).snd + (Θ b).fst * (Θ a).snd := by
    intro Θ a b
    rw [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring
  have hsnd_smul : ∀ (Θ : SchemeCoordinateAffineRing f n p →+* DualNumber ℂ),
      (∀ c : ℂ, Θ (algebraMap ℂ (SchemeCoordinateAffineRing f n p) c) = TrivSqZeroExt.inl c) →
      ∀ (c : ℂ) (a : SchemeCoordinateAffineRing f n p), (Θ (c • a)).snd = c * (Θ a).snd := by
    intro Θ hΘ c a
    rw [Algebra.smul_def, hsnd_mul, hΘ, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl, mul_zero,
      add_zero]
  let Dl : SchemeCoordinateAffineRing f n p →ₗ[ℂ] ℂ :=
    { toFun := fun a => (Θ₁ a).snd - (Θ₂ a).snd
      map_add' := fun a b => by simp only [map_add, TrivSqZeroExt.snd_add]; ring
      map_smul' := fun c a => by
        simp only [hsnd_smul Θ₁ hc₁, hsnd_smul Θ₂ hc₂, RingHom.id_apply, smul_eq_mul]; ring }
  let D : Derivation ℂ (SchemeCoordinateAffineRing f n p) ℂ := Derivation.mk' Dl fun a b => by
    change (Θ₁ (a * b)).snd - (Θ₂ (a * b)).snd = χ a * ((Θ₁ b).snd - (Θ₂ b).snd) +
      χ b * ((Θ₁ a).snd - (Θ₂ a).snd)
    rw [hsnd_mul, hsnd_mul, hχ, hχ, ← hfst a, ← hfst b]
    ring
  have hD : ∀ a, D a = (Θ₁ a).snd - (Θ₂ a).snd := fun _ => rfl
  -- it vanishes on the Kähler basis
  set P := (standardSmoothComplexChartPresentation f n p).2
  have hlift : D.liftKaehlerDifferential = 0 := by
    refine P.basisKaehler.ext fun k => ?_
    rw [Algebra.SubmersivePresentation.basisKaehler_apply,
      Derivation.liftKaehlerDifferential_comp_D, LinearMap.zero_apply, hD]
    have hk : standardSmoothComplexChartFreeGenerator f n p
        (standardSmoothComplexChartFreeIndexEquiv f n p k) = P.val k := by
      unfold standardSmoothComplexChartFreeGenerator
      rw [Equiv.symm_apply_apply]
    rw [← hk, hgen, sub_self]
  refine RingHom.ext fun a => TrivSqZeroExt.ext (hfst a) ?_
  have h := D.liftKaehlerDifferential_comp_D a
  rw [hlift, LinearMap.zero_apply, hD] at h
  exact (sub_eq_zero.mp h.symm)

end ChartRing

/-! ### The Jacobian criterion -/

section Main

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance h0sJacTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0sJacCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance h0sJacManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n
local instance h0sJacAffineAlgebra (p : SchemeComplexPoint f) :
    Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

theorem holGermEval_stalkToModel (p : SchemeComplexPoint f)
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    HolGerm.eval (stalkToModel f n p a) = pointEval f n p a :=
  NativeHolGerm.eval_chartEquiv _

/-- The dual-number point `a ↦ a(p) + D_v(a^an) ε` of the local ring at `p`. -/
def dualGerm (p : SchemeComplexPoint f) (v : ComplexModel n) :
    X.presheaf.stalk (schemeComplexPointImage f p) →+* DualNumber ℂ where
  toFun a := TrivSqZeroExt.inl (pointEval f n p a) +
    TrivSqZeroExt.inr (germDeriv v (stalkToModel f n p a))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [germDeriv_one]
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_mul, germDeriv_mul, holGermEval_stalkToModel, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, zero_add, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [germDeriv_zero]
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [germDeriv_add]

theorem dualGerm_fst (p : SchemeComplexPoint f) (v : ComplexModel n)
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    (dualGerm f n p v a).fst = pointEval f n p a := by
  simp [dualGerm]

theorem dualGerm_snd (p : SchemeComplexPoint f) (v : ComplexModel n)
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    (dualGerm f n p v a).snd = germDeriv v (stalkToModel f n p a) := by
  simp [dualGerm]

theorem mem_basicOpen_iff_notMem_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    {x : X} (hx : x ∈ U) : x ∈ X.basicOpen r ↔ r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have e1 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r ↔ x ∈ X.basicOpen r := by
    change hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen r ↔ _
    rw [hU.fromSpec_primeIdealOf ⟨x, hx⟩]
  rw [← e1, hU.fromSpec_preimage_basicOpen r]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- **The Jacobian criterion.**  At `p ∈ Uᵢ(ℂ)` with affine coordinates `y₀`, a vector `w`
killed by the differentials at `y₀` of the equations of `X ∩ D₊(xᵢ)` is the derivative of the
affine coordinates of `X(ℂ)` (in the preferred chart at `p`) along some `v`. -/
theorem exists_fderiv_eq_of_jacobian (p₀ : SchemeComplexPoint f)
    (i : Fin (E.ambientDimension + 1)) (hp₀ : schemeComplexPointImage f p₀ ∈ coordOpen E i)
    (w : ComplexModel E.ambientDimension)
    (hw : ∀ j, fderiv ℂ (fun y : ComplexModel E.ambientDimension =>
      MvPolynomial.eval (fun k => y k) (chartEquations f E i j)) (affineCoords f E n i p₀) w = 0) :
    ∃ v, fderiv ℂ (affineCoordMap f E n i (complexChartAt (n := n) p₀))
      ((complexChartAt (n := n) p₀).val p₀) v = w := by
  set y₀ := affineCoords f E n i p₀ with hy₀def
  set π := affinePresentation f E i
  have hsurj := affinePresentation_surjective f E i
  set δ : MvPolynomial (Fin E.ambientDimension) ℂ →+* DualNumber ℂ :=
    (MvPolynomial.aeval (fun a => (TrivSqZeroExt.inl (y₀ a) + TrivSqZeroExt.inr (w a) :
      DualNumber ℂ))).toRingHom with hδdef
  have hδ : ∀ P, (δ P).fst = MvPolynomial.eval (fun a => y₀ a) P ∧
      (δ P).snd = fderiv ℂ (fun z : ComplexModel E.ambientDimension =>
        MvPolynomial.eval (fun a => z a) P) y₀ w := fun P => aeval_dual y₀ w P
  -- `P ↦ P(y₀ + wε)` kills the ideal of `X ∩ D₊(xᵢ)`
  have hker : RingHom.ker π ≤ RingHom.ker δ := ker_le_of_chartEquations f E i fun j => by
    rw [RingHom.mem_ker]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [(hδ _).1, TrivSqZeroExt.fst_zero]
      exact eval_eq_zero_of_mem_ker f E n i (chartEquations_mem f E i j) hp₀
    · rw [(hδ _).2, TrivSqZeroExt.snd_zero]
      exact hw j
  set Φw := RingHom.liftOfSurjective π hsurj ⟨δ, hker⟩
  have hΦw : ∀ P, Φw (π P) = δ P := fun P => RingHom.liftOfSurjective_comp_apply π hsurj _ P
  have hΦfst : ∀ r, (Φw r).fst = schemeOpenRegularFunction f n E (coordOpen E i) r p₀ := by
    intro r
    obtain ⟨P, rfl⟩ := hsurj r
    rw [hΦw, (hδ P).1, schemeOpenRegularFunction_affinePresentation f E n i P p₀ hp₀]
  -- extension to the local ring
  set x₀ := schemeComplexPointImage f p₀
  have hU := isAffineOpen_coordOpen E i
  let : Algebra Γ(X, coordOpen E i) (X.presheaf.stalk x₀) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x₀, hp₀⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x₀) (hU.primeIdealOf ⟨x₀, hp₀⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x₀, hp₀⟩
  have halg : ∀ r, algebraMap Γ(X, coordOpen E i) (X.presheaf.stalk x₀) r =
      X.presheaf.germ (coordOpen E i) x₀ hp₀ r := fun _ => rfl
  have hunit : ∀ s : (hU.primeIdealOf ⟨x₀, hp₀⟩).asIdeal.primeCompl, IsUnit (Φw s) := by
    intro s
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hΦfst, isUnit_iff_ne_zero,
      schemeOpenRegularFunction_ne_zero_iff f E n _ _ p₀ hp₀,
      mem_basicOpen_iff_notMem_primeIdealOf hU _ hp₀]
    exact s.2
  set Ψ : X.presheaf.stalk x₀ →+* DualNumber ℂ :=
    IsLocalization.lift (M := (hU.primeIdealOf ⟨x₀, hp₀⟩).asIdeal.primeCompl) hunit
  have hΨ : ∀ r, Ψ (X.presheaf.germ (coordOpen E i) x₀ hp₀ r) = Φw r := fun r =>
    IsLocalization.lift_eq hunit r
  have hΨfst : ∀ a, (Ψ a).fst = pointEval f n p₀ a := by
    have h : ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp Ψ) = pointEval f n p₀ := by
      refine IsLocalization.ringHom_ext (hU.primeIdealOf ⟨x₀, hp₀⟩).asIdeal.primeCompl
        (RingHom.ext fun r => ?_)
      change (Ψ (algebraMap _ _ r)).fst = pointEval f n p₀ (algebraMap _ _ r)
      rw [halg, hΨ, hΦfst, schemeOpenRegularFunction_apply f n E _ r p₀ hp₀]
      rfl
    exact fun a => congrArg (fun φ : X.presheaf.stalk x₀ →+* ℂ => φ a) h
  -- the comparison on the standard smooth chart ring
  set κ : SchemeCoordinateAffineRing f n p₀ →+* X.presheaf.stalk x₀ :=
    (schemeCoordinateStalkEquiv f n p₀).toRingHom.comp
      (algebraMap (SchemeCoordinateAffineRing f n p₀) (SchemeCoordinateLocalRing f n p₀))
  set v : ComplexModel n := WithLp.toLp 2 fun k =>
    (Ψ (κ (standardSmoothComplexChartFreeGenerator f n p₀ k))).snd
  have hconstκ : ∀ c : ℂ, κ (algebraMap ℂ _ c) =
      X.presheaf.germ ⊤ x₀ trivial (schemeGlobalConstants f c) := by
    intro c
    rw [← schemeCoordinateStalkEquiv_global f n p₀, schemeCoordinateGlobalCoefficient_const]
    rfl
  have hΨconst : ∀ c : ℂ, Ψ (X.presheaf.germ ⊤ x₀ trivial (schemeGlobalConstants f c)) =
      TrivSqZeroExt.inl c := by
    intro c
    have hg : X.presheaf.germ ⊤ x₀ trivial (schemeGlobalConstants f c) =
        X.presheaf.germ (coordOpen E i) x₀ hp₀ (π (MvPolynomial.C c)) := by
      rw [affinePresentation_C]
      exact (X.presheaf.germ_res_apply (homOfLE (le_top : coordOpen E i ≤ ⊤)) x₀ hp₀ _).symm
    rw [hg, hΨ, hΦw]
    simp [hδdef, TrivSqZeroExt.algebraMap_eq_inl]
  have hdualconst : ∀ c : ℂ, dualGerm f n p₀ v (X.presheaf.germ ⊤ x₀ trivial
      (schemeGlobalConstants f c)) = TrivSqZeroExt.inl c := by
    intro c
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [dualGerm_fst, pointEval_germ_const, TrivSqZeroExt.fst_inl]
    · rw [dualGerm_snd, stalkToModel_constants, germDeriv_algebraMap, TrivSqZeroExt.snd_inl]
  have hgen : ∀ k, Ψ (κ (standardSmoothComplexChartFreeGenerator f n p₀ k)) =
      dualGerm f n p₀ v (κ (standardSmoothComplexChartFreeGenerator f n p₀ k)) := by
    intro k
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [hΨfst, dualGerm_fst]
    · rw [dualGerm_snd]
      change _ = germDeriv v (stalkToModel f n p₀ (schemeCoordinateStalkEquiv f n p₀
        (algebraMap _ (SchemeCoordinateLocalRing f n p₀)
          (standardSmoothComplexChartFreeGenerator f n p₀ k))))
      rw [stalkToModel_regular, schemeCoordinateModelRegularAlgHom_freeGenerator, germDeriv_add,
        germDeriv_coordinateGerm]
      have hc : germDeriv v (HolGerm.constHom (standardSmoothComplexAlgebraPoint f n p₀
          (standardSmoothComplexChartFreeGenerator f n p₀ k)) : HolGerm (ComplexModel n)) = 0 :=
        germDeriv_algebraMap v _
      rw [hc, add_zero]
  have hR := eq_of_freeGenerator f n p₀ (Ψ.comp κ) ((dualGerm f n p₀ v).comp κ)
    (fun a => by simp only [RingHom.comp_apply]; rw [hΨfst, dualGerm_fst])
    (fun c => by simp only [RingHom.comp_apply]; rw [hconstκ, hΨconst])
    (fun c => by simp only [RingHom.comp_apply]; rw [hconstκ, hdualconst])
    (fun k => by simp only [RingHom.comp_apply]; exact hgen k)
  -- hence on the whole local ring
  have hall : Ψ = dualGerm f n p₀ v := by
    have h2 : Ψ.comp (schemeCoordinateStalkEquiv f n p₀).toRingHom =
        (dualGerm f n p₀ v).comp (schemeCoordinateStalkEquiv f n p₀).toRingHom :=
      IsLocalization.ringHom_ext (schemeCoordinatePointIdeal f n p₀).primeCompl hR
    refine RingHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := (schemeCoordinateStalkEquiv f n p₀).surjective a
    exact congrArg (fun φ : SchemeCoordinateLocalRing f n p₀ →+* DualNumber ℂ => φ b) h2
  -- evaluation at the ratios
  refine ⟨v, ?_⟩
  set e := complexChartAt (n := n) p₀
  have hp : p₀ ∈ e.val.source := mem_complexChartAt_source p₀
  have hdom : e.val p₀ ∈ coordChartDomain f E n i e :=
    ⟨e.val.map_source hp, by
      show schemeComplexPointImage f (e.val.symm (e.val p₀)) ∈ coordOpen E i
      rw [e.val.left_inv hp]; exact hp₀⟩
  have hT : DifferentiableAt ℂ (affineCoordMap f E n i e) (e.val p₀) :=
    differentiableAt_affineCoordMap f E n i e hdom
  ext a
  have h1 : (δ (MvPolynomial.X a)).snd = w a := by
    simp [hδdef]
  have h2 : δ (MvPolynomial.X a) = dualGerm f n p₀ v
      (X.presheaf.germ (coordOpen E i) x₀ hp₀ (ratio E i (i.succAbove a))) := by
    rw [← hall, hΨ, ← affinePresentation_X, hΦw]
  rw [h2, dualGerm_snd, germDeriv_stalkToModel_germ f E n] at h1
  rw [← h1]
  have hproj : (fun z => schemeOpenRegularFunction f n E (coordOpen E i)
      (ratio E i (i.succAbove a)) (e.val.symm z)) =
      (EuclideanSpace.proj a : ComplexModel E.ambientDimension →L[ℂ] ℂ) ∘
        affineCoordMap f E n i e := by
    funext z
    rfl
  rw [hproj, fderiv_comp _ (EuclideanSpace.proj a).differentiableAt hT,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  rfl

end Main

end SGPT.GAGA.H0S
