import SGPT.PSH.ValMultLocal
import SGPT.Okounkov.OkoTowerDescent

/-!
# The finite log-resolution test of `thm:valuativemulti`

Source: `chapter_pshfunctions.tex`, `thm:valuativemulti`, final clause, in the revised form of the
current source (erratum E07: the test runs over ALL components of the resolved polar divisor that
meet `π⁻¹(x)`, strict transforms of polar divisors on `X` included):

> If `φ` has analytic singularities and `π : Y → X` is a log resolution of `φ` (`def:logres`), let
> `{E_i}` be the components of its resolved polar divisor that meet `π⁻¹(x)`.  Then (2) can be
> replaced by the finite set of inequalities `ord_{E_i}(f) > ν(φ, E_i) - A_X(E_i)` for all `i`.

Here the log resolution is `π : Y → X` with `φ ∘ π` having log singularities along the simple
normal crossing effective `ℚ`-divisor `D` (its resolved polar divisor); the components `E_i` are
the prime carriers `P` of `D` with positive coefficient.  Every component is a smooth connected
hypersurface of `Y` (`component_isClosedConnectedSubmanifold`), hence a prime divisor over `X`
(`componentPresentation`), with the book's readers: `ν(φ, E) = presentationReader` (generic Lelong
number of `π^*φ` along `E`, squared-log normalisation), `ord_E(f) = stalkOrdE` (order of vanishing of
`π^* f` along `E` at the points of `E` over `x`) and `A_X(E) = presentationLogDiscrepancy`
(`1 + ord_E(K_{Y/X})`).  The test `ord_E(f) > ν(φ, E) - A_X(E)` is written
`ν(φ, E) < ord_E(f) + A_X(E)` in `ℝ≥0∞` (`FiniteLogResolutionTest`); `ν(φ, E)` is finite
(`presentationReader_component_ne_top`) and `ord_E(f)` is finite for `f ≠ 0`.

* `mem_multiplierIdeal_iff_finiteLogResolutionTest`: for `φ` quasi-psh, `x ∈ X` and `f ∈ 𝒪_{X,x}`
  (also `f = 0`), `f ∈ 𝓘(φ)_x` iff the finite test holds.  The modification is any proper
  bimeromorphic holomorphic map (in particular every modification of `def:logres`).
* `isSourceLogResolution_finiteTest`: the same for a log resolution in the sense of `def:logres`
  (`IsSourceLogResolution`), for its resolved polar divisor.

Proof.  `(1) ⇒` test: the valuative criterion (1) ⇒ (2) (`mem_multiplierIdeal_iff_bookPrimeBound`)
gives `(1 + ε) ν ≤ ord + A`, and `ν` is finite, `A ≥ 1`.  Test `⇒ (1)`: by the change of variables
formula along `π` (`multiplierIntegrableAt_iff_fiber_jacobian_germs`), `f ∈ 𝓘(φ)_x` iff
`(f ∘ π) · Jac(π) ∈ 𝓘(π^*φ)_y` for every `y ∈ π⁻¹(x)`.  In simple normal crossing coordinates `ζ`
at `y`: `π^*φ ≥ Σ_k c_k log |ζ_k|² - C` (`exists_weight_lower_bound`), where `c_k = coeff_D(E)`
for the component `E = {ζ_k = 0}` through `y`, and `(f ∘ π) · Jac(π) = H · ∏ ζ_k^{b_k + d_k}` with
`b_k = ord_{E,y}(f ∘ π) ≥ ord_E(f)` and `d_k = ord_E(K_{Y/X}) = A_X(E) - 1`.  Since
`coeff_D(E) ≤ ν(φ, E)` (`coefficient_le_squaredLogLelongNumber`), the test gives
`c_k < b_k + d_k + 1`, and the monomial integrability `∫ ∏ |ζ_k|^{2(b_k + d_k - c_k)} < ∞`
(`multiplierIntegrableAt_of_coordinate_factorization`) concludes.

Blueprint: `claude-valmult.tex`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace SGPT.PSH.ValMultFinite

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  FirstPass.HolomorphicIdealSheaves FirstPass.HolomorphicMaps FirstPass.BlowupSequences
  BlowupFlatCoordinates NormalCrossings DivisorialChangeOfVariables
  AnalyticModificationLocalDiscrepancy DemaillyApproximantDivisorialLelong
  CompactPrimeOver CompactPrimeLogDiscrepancy ActualGermValuative RIsoAGermOrder
  HironakaSmoothCentreRealDomainActualSheafStalk ValMultLocal

universe u

/-! ### Components of a simple normal crossing divisor are smooth -/

section Smooth

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]

omit [ChartedSpace (ComplexModel (m + 1)) M] in
private theorem coordSubspace_singleton (j : Fin (m + 1)) (z : ComplexModel (m + 1)) :
    z ∈ coordSubspace ({j} : Finset (Fin (m + 1))) ↔ z j = 0 := by
  simp [coordSubspace]

/-- A set which, in holomorphic coordinates centred at `x`, is the coordinate hyperplane
`ζ_j = 0` near `x`, is regular of dimension `m` at `x`. -/
theorem regularAtDim_of_flat {E : Set M} {x : M}
    (Φ : LocalHolomorphicEquivAt (n := m + 1) ((chartAt (ComplexModel (m + 1)) x) x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (m + 1)) x).target)
    (h0 : Φ.toFun ((chartAt (ComplexModel (m + 1)) x) x) = 0) (j : Fin (m + 1)) (hx : x ∈ E)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (m + 1)) x).source →
      (chartAt (ComplexModel (m + 1)) x) y ∈ Φ.source →
        (y ∈ E ↔ Φ.toFun ((chartAt (ComplexModel (m + 1)) x) y) j = 0)) :
    RegularAtDim (n := m + 1) E x m := by
  classical
  let e : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
  let L : ComplexModel (m + 1) ≃L[ℂ] ComplexModel (m + 1) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toContinuousLinearEquiv
  have hlast (z : ComplexModel (m + 1)) : (L z) (Fin.last m) = z j := by
    change z (e.symm (Fin.last m)) = z j
    simp [e]
  have hplane (z : ComplexModel (m + 1)) :
      z j = 0 ↔ L z ∈ complexCoordinatePlane (m + 1) m := by
    rw [← coordSubspace_singleton]
    constructor
    · intro hz k hk
      have hk' : k = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [hk', hlast]
      exact hz j (Finset.mem_singleton_self j)
    · intro hz k hk
      rw [Finset.mem_singleton.mp hk]
      rw [← hlast]
      exact hz (Fin.last m) le_rfl
  let Θ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) x).val x) := {
    source := Φ.source
    target := L.symm ⁻¹' Φ.target
    isOpen_source := Φ.isOpen_source
    isOpen_target := Φ.isOpen_target.preimage L.symm.continuous
    center_mem_source := Φ.center_mem_source
    toFun := fun z => L (Φ.toFun z)
    invFun := fun z => Φ.invFun (L.symm z)
    toFun_holomorphic := L.differentiable.comp_differentiableOn Φ.toFun_holomorphic
    invFun_holomorphic := Φ.invFun_holomorphic.comp L.symm.differentiable.differentiableOn
      (fun _ hz => hz)
    mapsTo_toFun := by
      intro z hz
      change L.symm (L (Φ.toFun z)) ∈ Φ.target
      rw [L.symm_apply_apply]
      exact Φ.mapsTo_toFun hz
    mapsTo_invFun := fun _ hz => Φ.mapsTo_invFun hz
    left_inv := by
      intro z hz
      rw [L.symm_apply_apply]
      exact Φ.left_inv z hz
    right_inv := by
      intro z hz
      rw [Φ.right_inv _ hz, L.apply_symm_apply] }
  refine ⟨Nat.le_succ m, hx, Θ, hsrc, ?_, ?_⟩
  · change L (Φ.toFun ((complexChartAt (n := m + 1) x).val x)) = 0
    rw [show Φ.toFun ((complexChartAt (n := m + 1) x).val x) = 0 from h0, L.map_zero]
  · intro y hy hyΦ
    exact (hflat hy hyΦ).trans (hplane (Φ.toFun ((complexChartAt (n := m + 1) x).val y)))

variable [IsComplexManifold (m + 1) M]

/-- **Every component of a simple normal crossing divisor is a smooth connected closed
hypersurface.** -/
theorem component_isClosedConnectedSubmanifold {D : EffectiveGeometricQDivisor (m + 1) M}
    (hD : D.IsSNC) (P : GeometricPrimeCarrier (m + 1) M) (hP : 0 < D.coefficient P) :
    IsClosedConnectedSubmanifold (m + 1) P.val m := by
  have hD' := (EffectiveGeometricQDivisor.isSNC_iff_isSNCComponentwise D).mp hD
  refine ⟨P.isClosed, ⟨P.nonempty, ?_⟩, fun y hy => ?_⟩
  · have h := P.subvariety.irreducible_carrier
    rw [P.subvariety_carrier] at h
    exact CodimOneSupport.isPreconnected_of_isComplexAnalyticallyIrreducible h
  · obtain ⟨Φ, j, hsrc, h0, hflat, -⟩ := exists_adapted_coordinates hD' y
    exact regularAtDim_of_flat Φ hsrc h0 (j ⟨P, hP⟩) hy (hflat ⟨P, hP⟩ hy)

end Smooth

/-! ### Components as prime divisors over `X` -/

section Presentation

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- A component `P` of the resolved polar divisor `D` on `π : Y → X`, as a prime divisor over `X`
(`def:primdiv`): the smooth connected hypersurface `P ⊆ Y` of the modification `π`. -/
def componentPresentation {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    {D : EffectiveGeometricQDivisor (m + 1) Y} (hD : D.IsSNC) (P : GeometricPrimeCarrier (m + 1) Y)
    (hP : 0 < D.coefficient P) : PrimePresentation (m + 1) X where
  model := BlowupTowers.CMfd.of (n := m + 1) Y
  projection := π
  modification := hπ
  divisor := P.val
  divisorDimension := m
  smooth := component_isClosedConnectedSubmanifold hD P hP
  codimension_one := rfl

/-- The log discrepancy of a component is `1 + ord_E(K_{Y/X})`. -/
theorem presentationLogDiscrepancy_component {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {D : EffectiveGeometricQDivisor (m + 1) Y}
    (hD : D.IsSNC) (P : GeometricPrimeCarrier (m + 1) Y) (hP : 0 < D.coefficient P) :
    presentationLogDiscrepancy (componentPresentation hπ hD P hP) =
      ConnectedJacobianCoefficient.actualRelativeJacobianCoefficient hπ
        (component_isClosedConnectedSubmanifold hD P hP) + 1 := rfl

/-- **`ν(φ, E)` is finite** on the components of the resolved polar divisor. -/
theorem presentationReader_component_ne_top {φ : X → EReal} {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {D : EffectiveGeometricQDivisor (m + 1) Y}
    (hD : D.IsSNC) (hlog : NativeHasLogSingularitiesAlong D (φ ∘ π))
    (P : GeometricPrimeCarrier (m + 1) Y) (hP : 0 < D.coefficient P) {y : Y} (hy : y ∈ P.val) :
    presentationReader φ (componentPresentation hπ hD P hP) ≠ ⊤ := by
  rw [presentationReader_eq_iInf_squaredLog]
  refine ne_top_of_le_ne_top ?_ (iInf₂_le (f := fun z (_ : z ∈ P.val) =>
    SquaredLogLelongSourceNormalization.squaredLogLelongNumber (n := m + 1) (φ ∘ π) z) y hy)
  have hq := SGPT.Trace.Bertini.IsQPSH.manifoldQuasiPlurisubharmonic' hlog.1
  have hnd := SGPT.PSH.VariableComplexAtlas.IsQPSH.locallyNondegenerate hlog.1
  have h := LelongNumberFiniteness.lelongNumber_ne_top_of_quasiPsh (Nat.succ_pos m) hq hnd y
  rw [SquaredLogLelongSourceNormalization.lelongNumber_eq_two_mul_squaredLog
    (Nat.succ_ne_zero m)] at h
  intro htop
  exact h (by rw [htop]; simp)

/-- **`coeff_D(E) ≤ ν(φ, E)`** on the components of the resolved polar divisor. -/
theorem coefficient_le_presentationReader_component {φ : X → EReal} {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {D : EffectiveGeometricQDivisor (m + 1) Y}
    (hD : D.IsSNC) (hlog : NativeHasLogSingularitiesAlong D (φ ∘ π))
    (P : GeometricPrimeCarrier (m + 1) Y) (hP : 0 < D.coefficient P) :
    ENNReal.ofReal (D.coefficient P : ℝ) ≤
      presentationReader φ (componentPresentation hπ hD P hP) := by
  have hD' := (EffectiveGeometricQDivisor.isSNC_iff_isSNCComponentwise D).mp hD
  rw [presentationReader_eq_iInf_squaredLog]
  exact le_iInf₂ fun z hz => coefficient_le_squaredLogLelongNumber hlog hD' ⟨P, hP⟩ hz

end Presentation

/-! ### Integrability at the points of the fibre -/

section Fibre

/-- Change of adapted coordinates in a Jacobian-weighted multiplier germ (the argument of
`OriginalTruncationDescent`, for an arbitrary holomorphic map `g`). -/
theorem jacobian_integral_of_adapted {n : ℕ} {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt p) (g : ComplexModel n → ComplexModel n)
    (hg : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ g z)
    (w : ComplexModel n → EReal) (hw : QuasiPlurisubharmonicAt w p)
    (f : ComplexModel n → ℂ) (c : ℝ)
    (hint : MultiplierIntegrableAt (fun z => w (Φ.invFun z)) c
      (fun z => f (Φ.invFun z) * complexJacobian (g ∘ Φ.invFun) z) (Φ.toFun p) volume) :
    MultiplierIntegrableAt w c (fun z => f z * complexJacobian g z) p volume := by
  have hq : Φ.toFun p ∈ Φ.target := Φ.mapsTo_toFun Φ.center_mem_source
  have ht : Tendsto Φ.invFun (𝓝 (Φ.toFun p)) (𝓝 p) := by
    have h := (Φ.invFun_holomorphic.differentiableAt
      (Φ.isOpen_target.mem_nhds hq)).continuousAt.tendsto
    simpa only [Φ.left_inv p Φ.center_mem_source] using h
  obtain ⟨_hJto, hJinv, _hJto0, hJinv0⟩ :=
    LocalHolomorphicMultiplierGermCovariance.jacobian_units_of_local_holomorphic_equiv Φ
  have hchain : complexJacobian (g ∘ Φ.invFun) =ᶠ[𝓝 (Φ.toFun p)]
      (fun z => complexJacobian g (Φ.invFun z) * complexJacobian Φ.invFun z) := by
    filter_upwards [ht.eventually hg, Φ.isOpen_target.mem_nhds hq] with z hgz hz
    have hIz := Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hz)
    simp only [complexJacobian]
    rw [fderiv_comp z hgz hIz, ContinuousLinearMap.det]
    change LinearMap.det ((fderiv ℂ g (Φ.invFun z)).toLinearMap.comp
      (fderiv ℂ Φ.invFun z).toLinearMap) = _
    exact LinearMap.det_comp _ _
  have htest : (fun z => f (Φ.invFun z) * complexJacobian (g ∘ Φ.invFun) z)
      =ᶠ[𝓝 (Φ.toFun p)] (fun z => complexJacobian Φ.invFun z *
        (f (Φ.invFun z) * complexJacobian g (Φ.invFun z))) := by
    filter_upwards [hchain] with z hz
    rw [hz]
    ring
  have hplain : MultiplierIntegrableAt (fun z => w (Φ.invFun z)) c
      (fun z => f (Φ.invFun z) * complexJacobian g (Φ.invFun z)) (Φ.toFun p) volume :=
    (ComplexMonomialMultiplierUnit.multiplierIntegrableAt_mul_unit_iff
      (φ := fun z => w (Φ.invFun z)) (c := c)
      (f := fun z => f (Φ.invFun z) * complexJacobian g (Φ.invFun z)) hJinv hJinv0).mp
        (hint.congr EventuallyEq.rfl htest)
  exact (LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
    Φ (f := fun z => f z * complexJacobian g z) hw).mp hplain

/-- The finite cast of a finite order. -/
theorem extendedOrderValue_le_natCast {B : ℕ∞} {k : ℕ} (h : B ≤ k) :
    extendedOrderValue B ≤ (k : ℝ≥0∞) := by
  have hB : B ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hB
  have hb : b ≤ k := by exact_mod_cast h
  change ((b : NNReal) : ℝ≥0∞) ≤ (k : ℝ≥0∞)
  exact_mod_cast hb

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- **The local integrability at a point `y` of the fibre.**  If the finite test holds for the
components through `y`, then `(f ∘ π) · Jac(π)` lies in the multiplier ideal of `π^*φ` at `y`
(Jacobian-weighted chart form of `multiplierIntegrableAt_iff_fiber_jacobian_germs`). -/
theorem fibre_multiplierIntegrableAt {φ : X → EReal} {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {D : EffectiveGeometricQDivisor (m + 1) Y}
    (hD : D.IsSNC) (hlog : NativeHasLogSingularitiesAlong D (φ ∘ π))
    (F : X → ℂ) (y : Y) (hF : HolomorphicAt (m + 1) F (π y))
    (hFnon : ∃ᶠ z in 𝓝 (π y), F z ≠ 0)
    (htest : ∀ (P : GeometricPrimeCarrier (m + 1) Y) (hP : 0 < D.coefficient P), y ∈ P.val →
      presentationReader φ (componentPresentation hπ hD P hP) <
        extendedOrderValue (germOrdE (m + 1) π P.val (π y) F) +
          (presentationLogDiscrepancy (componentPresentation hπ hD P hP) : ℝ≥0∞)) :
    MultiplierIntegrableAt
      (fun z => chartFunction φ (complexChartAt (n := m + 1) (π y))
        (coordinateMap π (complexChartAt (n := m + 1) y) (complexChartAt (n := m + 1) (π y)) z)) 1
      (fun z => F ((complexChartAt (n := m + 1) (π y)).val.symm
          (coordinateMap π (complexChartAt (n := m + 1) y) (complexChartAt (n := m + 1) (π y)) z)) *
        complexJacobian (coordinateMap π (complexChartAt (n := m + 1) y)
          (complexChartAt (n := m + 1) (π y))) z)
      ((complexChartAt (n := m + 1) y).val y) volume := by
  classical
  have hD' := (EffectiveGeometricQDivisor.isSNC_iff_isSNCComponentwise D).mp hD
  set e := complexChartAt (n := m + 1) y with he
  set d := complexChartAt (n := m + 1) (π y) with hd
  set u : Y → EReal := φ ∘ π with hu
  have huq : ManifoldQuasiPlurisubharmonic (n := m + 1) u :=
    SGPT.Trace.Bertini.IsQPSH.manifoldQuasiPlurisubharmonic' hlog.1
  obtain ⟨Φ, j, hsrc, h0, hflat, hinj⟩ := exists_adapted_coordinates hD' y
  have hfinT : {P : {P : GeometricPrimeCarrier (m + 1) Y // 0 < D.coefficient P} |
      y ∈ P.val.val}.Finite := D.locallyFinite_positive.point_finite y
  set T := hfinT.toFinset with hTdef
  have hT : ∀ P, P ∈ T ↔ y ∈ P.val.val := fun P => hfinT.mem_toFinset
  have hinjT : InjOn j T := fun P hP Q hQ hPQ => hinj ((hT P).mp hP) ((hT Q).mp hQ) hPQ
  obtain ⟨C, hC⟩ := exists_weight_lower_bound hlog y Φ hsrc h0 j hflat T hT
  -- the chart at `π y` contains `π` of a neighbourhood of `y`
  have hπd : ∀ᶠ w in 𝓝 y, π w ∈ d.val.source :=
    hπ.1.continuous.continuousAt.preimage_mem_nhds
      (d.val.open_source.mem_nhds (mem_complexChartAt_source (π y)))
  have hes : Tendsto e.val.symm (𝓝 (e.val y)) (𝓝 y) := by
    have h := (e.val.continuousAt_symm (e.val.map_source (mem_complexChartAt_source y))).tendsto
    rwa [e.val.left_inv (mem_complexChartAt_source y)] at h
  -- change of the weight near `e y`
  have hwcongr : (chartFunction u e) =ᶠ[𝓝 (e.val y)]
      (fun z => chartFunction φ d (coordinateMap π e d z)) := by
    filter_upwards [hes.eventually hπd] with z hz
    simp only [chartFunction, coordinateMap, Function.comp_apply, hu]
    rw [d.val.left_inv hz]
  have hwq : QuasiPlurisubharmonicAt (chartFunction u e) (e.val y) :=
    huq e (e.val y) (e.val.map_source (mem_complexChartAt_source y))
  -- the coordinate expression of `π` is holomorphic near `e y`
  have hey : e.val y ∈ coordinateDomain π e d :=
    mem_coordinateDomain (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))
  have hgdiff : ∀ᶠ z in 𝓝 (e.val y), DifferentiableAt ℂ (coordinateMap π e d) z := by
    filter_upwards [(coordinateDomain_isOpen hπ.1 e d).mem_nhds hey] with z hz
    exact ((coordinateMap_contDiffOn hπ.1 e d).differentiableOn (by simp)).differentiableAt
      ((coordinateDomain_isOpen hπ.1 e d).mem_nhds hz)
  set f : ComplexModel (m + 1) → ℂ := fun z => F (d.val.symm (coordinateMap π e d z)) with hfdef
  refine (jacobian_integral_of_adapted Φ (coordinateMap π e d) hgdiff (chartFunction u e) hwq f 1
    ?_).congr hwcongr EventuallyEq.rfl
  rw [h0]
  -- the Jacobian of `π` in adapted coordinates
  set J : ComplexModel (m + 1) → ℂ := complexJacobian (coordinateMap π e d ∘ Φ.invFun) with hJdef
  have h0t := zero_mem_target y Φ h0
  have hinv0 : Φ.invFun 0 = e.val y := by
    rw [← show Φ.toFun (e.val y) = 0 from h0]
    exact Φ.left_inv _ Φ.center_mem_source
  have hJd : ∀ᶠ ζ in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ J ζ := by
    set W := Φ.target ∩ Φ.invFun ⁻¹' coordinateDomain π e d
    have hWo : IsOpen W := Φ.invFun_holomorphic.continuousOn.isOpen_inter_preimage
      Φ.isOpen_target (coordinateDomain_isOpen hπ.1 e d)
    have hGd : DifferentiableOn ℂ (coordinateMap π e d ∘ Φ.invFun) W :=
      ((coordinateMap_contDiffOn hπ.1 e d).differentiableOn (by simp)).comp
        (Φ.invFun_holomorphic.mono inter_subset_left) (fun ζ hζ => hζ.2)
    have hJW := SGPT.Okounkov.OkoTower.differentiableOn_complexJacobian hWo hGd
    have h0W : (0 : ComplexModel (m + 1)) ∈ W := ⟨h0t, by
      change Φ.invFun 0 ∈ coordinateDomain π e d
      rw [hinv0]
      exact hey⟩
    filter_upwards [hWo.mem_nhds h0W] with ζ hζ
    exact (hJW ζ hζ).differentiableAt (hWo.mem_nhds hζ)
  -- the pulled-back function in adapted coordinates
  have hfFp : ∀ᶠ ζ in 𝓝 (0 : ComplexModel (m + 1)),
      f (Φ.invFun ζ) = F (π (adaptedInv y Φ ζ)) := by
    filter_upwards [(tendsto_adaptedInv y Φ h0).eventually hπd] with ζ hζ
    simp only [hfdef, coordinateMap, Function.comp_apply]
    exact congrArg F (d.val.left_inv hζ)
  have hFπ : HolomorphicAt (m + 1) (F ∘ π) y :=
    hF.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt)
  have hFπnon : ∃ᶠ w in 𝓝 y, (F ∘ π) w ≠ 0 :=
    MultiplierPullbackNonzero.frequently_comp_ne_zero hπ y hF hFnon
  obtain ⟨hFTd, hFTnon⟩ :=
    ManifoldAdaptedMultiplierGermTransport.holomorphic_nonzero_comp_adapted y Φ h0 hFπ hFπnon
  obtain ⟨b, K, hK, -, hFfac, hnotK⟩ :=
    HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hFTd hFTnon
  by_cases hJnon : ∃ᶠ ζ in 𝓝 (0 : ComplexModel (m + 1)), J ζ ≠ 0
  swap
  · -- the Jacobian vanishes identically near `0`
    have hJ0 : ∀ᶠ ζ in 𝓝 (0 : ComplexModel (m + 1)), J ζ = 0 := by
      simpa only [Filter.Frequently, not_not, ne_eq] using hJnon
    refine (multiplierIntegrableAt_zero _ one_pos _ _).congr EventuallyEq.rfl ?_
    filter_upwards [hJ0] with ζ hζ
    rw [hζ, mul_zero]
  obtain ⟨dd, L, hL, -, hJfac, hnotL⟩ :=
    HolomorphicCoordinateOrders.exists_coordinate_factorization_of_nonzero_germ hJd hJnon
  -- the factorization of the test function
  have hQ : (fun ζ => f (Φ.invFun ζ) * J ζ) =ᶠ[𝓝 (0 : ComplexModel (m + 1))]
      fun ζ => (K ζ * L ζ) * ∏ k, ζ k ^ (b k + dd k) := by
    filter_upwards [hfFp, hFfac, hJfac] with ζ h1 h2 h3
    rw [h1, h3]
    change (F ∘ π) ((chartAt (ComplexModel (m + 1)) y).symm (Φ.invFun ζ)) * _ = _
    rw [h2]
    simp only [pow_add, Finset.prod_mul_distrib]
    ring
  -- the thresholds
  have hthr : ∀ k, 1 * coordinateCoefficient j T k < ((b k + dd k : ℕ) : ℝ) + 1 := by
    intro k
    rw [one_mul]
    by_cases hk : ∃ P ∈ T, j P = k
    swap
    · push Not at hk
      rw [coordinateCoefficient_eq_zero hk]
      positivity
    obtain ⟨P, hPT, rfl⟩ := hk
    have hyP : y ∈ P.val.val := (hT P).mp hPT
    rw [coordinateCoefficient_eq hinjT hPT]
    have hPsub := component_isClosedConnectedSubmanifold hD P.val P.property
    have hflatP : ∀ᶠ w in 𝓝 y, w ∈ P.val.val ↔
        Φ.toFun ((chartAt (ComplexModel (m + 1)) y) w) (j P) = 0 := by
      filter_upwards [(chartAt (ComplexModel (m + 1)) y).open_source.mem_nhds
          (mem_chart_source _ y),
        ((chartAt (ComplexModel (m + 1)) y).continuousAt (mem_chart_source _ y)).preimage_mem_nhds
          (Φ.isOpen_source.mem_nhds Φ.center_mem_source)] with w hw hwΦ
      exact hflat P hyP hw hwΦ
    obtain ⟨Ψ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hPsub.2.2 y hyP)
    -- the order of `f ∘ π` along `P` at `y` is `b_{j(P)}`
    have hb : vanishingOrderAlong (m + 1) P.val.val y (F ∘ π) = b (j P) := by
      rw [vanishingOrderAlong_eq_functionNormalOrder Ψ (F ∘ π) hFπ,
        SameCoordinateOrder.functionNormalOrder_eq_coordinate_of_eventually Ψ Φ hsrc h0 (j P)
          hflatP (F ∘ π) hFπ]
      refine SameCoordinateOrder.emultiplicity_coordinate_factorization (j P) _ b K hK ?_
        (hnotK (j P))
      rw [SameCoordinateOrder.adaptedGerm, HolGerm.coe_mk]
      exact Filter.Germ.coe_eq.mpr hFfac
    -- the order of the Jacobian along `P` is `A_X(P) - 1 = d_{j(P)}`
    have hdd : (ConnectedJacobianCoefficient.actualRelativeJacobianCoefficient hπ hPsub : ℕ∞) =
        dd (j P) := by
      rw [← SameCoordinateOrder.emultiplicity_adapted_jacobian_eq_actualCoefficient hπ hPsub hyP Φ
        hsrc h0 (j P) hflatP (HolGerm.mk J hJd) (by rw [HolGerm.coe_mk])]
      refine SameCoordinateOrder.emultiplicity_coordinate_factorization (j P) _ dd L hL ?_
        (hnotL (j P))
      rw [HolGerm.coe_mk]
      exact Filter.Germ.coe_eq.mpr hJfac
    have hdd' : ConnectedJacobianCoefficient.actualRelativeJacobianCoefficient hπ hPsub =
        dd (j P) := by exact_mod_cast hdd
    have hord : germOrdE (m + 1) π P.val.val (π y) F ≤ (b (j P) : ℕ∞) := by
      rw [← hb]
      exact iInf_le (fun w : {w : Y // w ∈ P.val.val ∧ π w = π y} =>
        vanishingOrderAlong (m + 1) P.val.val w.val (F ∘ π)) ⟨y, hyP, rfl⟩
    have hν := coefficient_le_presentationReader_component hπ hD hlog P.val P.property
    have ht := htest P.val P.property hyP
    rw [presentationLogDiscrepancy_component, hdd'] at ht
    have hlt : ENNReal.ofReal (D.coefficient P.val : ℝ) <
        ENNReal.ofReal (((b (j P) + dd (j P) : ℕ) : ℝ) + 1) := by
      calc ENNReal.ofReal (D.coefficient P.val : ℝ) ≤ _ := hν
        _ < _ := ht
        _ ≤ (b (j P) : ℝ≥0∞) + ((dd (j P) + 1 : ℕ) : ℝ≥0∞) :=
          add_le_add (extendedOrderValue_le_natCast hord) le_rfl
        _ = ENNReal.ofReal (((b (j P) + dd (j P) : ℕ) : ℝ) + 1) := by
          rw [show (((b (j P) + dd (j P) : ℕ) : ℝ) + 1) = ((b (j P) + (dd (j P) + 1) : ℕ) : ℝ) by
            push_cast; ring, ENNReal.ofReal_natCast]
          push_cast
          ring
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hlt
  have hmon := HolomorphicCoordinateOrders.multiplierIntegrableAt_of_coordinate_factorization
    (fun k => b k + dd k) (coordinateCoefficient j T) one_pos
    (hK.and hL |>.mono fun _ h => h.1.mul h.2) hQ (ρ := fun _ => 0)
    (Eventually.of_forall fun _ => continuousAt_const) hthr
  -- comparison of the weights
  obtain ⟨U, hUsub, hUo, h0U⟩ := _root_.mem_nhds_iff.mp (hC.and (Φ.isOpen_target.mem_nhds h0t))
  refine multiplierIntegrableAt_of_weight_le_aemeasurable one_pos hUo h0U ?_
    (A := ENNReal.ofReal (Real.exp C)) ENNReal.ofReal_ne_top ?_ hmon
  · apply aemeasurable_restrict_of_upperSemicontinuousOn hUo
    intro ζ hζ
    apply UpperSemicontinuousAt.upperSemicontinuousWithinAt
    have hζT : ζ ∈ Φ.target := (hUsub hζ).2
    have husc := (huq e (Φ.invFun ζ) (hsrc (Φ.mapsTo_invFun hζT))).upperSemicontinuousAt
    have hcont : ContinuousAt Φ.invFun ζ :=
      (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hζT)).continuousAt
    intro a ha
    exact hcont.eventually (husc a ha)
  · intro ζ hζ
    have hCζ := (hUsub hζ).1
    calc multiplierWeight 1 (chartFunction u e (Φ.invFun ζ))
        ≤ multiplierWeight 1 ((∑ k, ((2 * coordinateCoefficient j T k : ℝ) : EReal) *
            ENNReal.log (ENNReal.ofReal ‖ζ k‖)) + ((-C : ℝ) : EReal)) :=
          multiplierWeight_antitone zero_le_one hCζ
      _ = ENNReal.ofReal (Real.exp C) * multiplierWeight 1
            ((∑ k, ((2 * coordinateCoefficient j T k : ℝ) : EReal) *
              ENNReal.log (ENNReal.ofReal ‖ζ k‖)) + (((fun _ => (0 : ℝ)) ζ : ℝ) : EReal)) := by
          rw [multiplierWeight_one_add_coe, EReal.coe_zero, add_zero]

end Fibre

/-! ### The finite test -/

section Test

variable {m : ℕ} {X Y : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]

/-- **The finite test of `thm:valuativemulti`** (revised source, erratum E07): for every component
`E` of the resolved polar divisor `D` that meets `π⁻¹(x)`,
`ord_E(f) > ν(φ, E) - A_X(E)`, i.e. `ν(φ, E) < ord_E(f) + A_X(E)`. -/
def FiniteLogResolutionTest (φ : X → EReal) {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {D : EffectiveGeometricQDivisor (m + 1) Y}
    (hD : D.IsSNC) (x : X) (g : actualComplexStructureStalk (n := m + 1) x) : Prop :=
  ∀ (P : GeometricPrimeCarrier (m + 1) Y) (hP : 0 < D.coefficient P), (∃ y ∈ P.val, π y = x) →
    presentationReader φ (componentPresentation hπ hD P hP) <
      extendedOrderValue (stalkOrdE (componentPresentation hπ hD P hP) x g) +
        (presentationLogDiscrepancy (componentPresentation hπ hD P hP) : ℝ≥0∞)

/-- `(1) ⇒` finite test. -/
theorem finiteLogResolutionTest_of_mem {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ) {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {D : EffectiveGeometricQDivisor (m + 1) Y}
    (hD : D.IsSNC) (hlog : NativeHasLogSingularitiesAlong D (φ ∘ π)) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x)
    (hg : g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x) :
    FiniteLogResolutionTest φ hπ hD x g := by
  obtain ⟨ε, hε, hbound⟩ := (mem_multiplierIdeal_iff_bookPrimeBound hφ x g).mp hg
  rintro P hP ⟨y, hyP, hyx⟩
  have hx : x ∈ presentationCenter (componentPresentation hπ hD P hP) := ⟨y, hyP, hyx⟩
  have h := hbound _ hx
  have hfin := presentationReader_component_ne_top hπ hD hlog P hP hyP
  have hA : (0 : ℝ≥0∞) < (presentationLogDiscrepancy (componentPresentation hπ hD P hP) : ℝ≥0∞) := by
    exact_mod_cast presentationLogDiscrepancy_pos _
  by_cases hν0 : presentationReader φ (componentPresentation hπ hD P hP) = 0
  · rw [hν0]
    exact lt_of_lt_of_le hA le_add_self
  · have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + ε) := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    calc presentationReader φ (componentPresentation hπ hD P hP)
        = 1 * presentationReader φ (componentPresentation hπ hD P hP) := (one_mul _).symm
      _ < ENNReal.ofReal (1 + ε) * presentationReader φ (componentPresentation hπ hD P hP) :=
          ENNReal.mul_lt_mul_left hν0 hfin h1
      _ ≤ _ := h

/-- Finite test `⇒ (1)`. -/
theorem mem_of_finiteLogResolutionTest {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ) {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {D : EffectiveGeometricQDivisor (m + 1) Y}
    (hD : D.IsSNC) (hlog : NativeHasLogSingularitiesAlong D (φ ∘ π)) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x)
    (htest : FiniteLogResolutionTest φ hπ hD x g) :
    g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x := by
  classical
  obtain ⟨F, hF, hFg⟩ := exists_original_representative x g
  suffices hmem : (multiplierIdeal (n := m + 1) 1 φ).mem x F from
    Ideal.subset_span ⟨F, hF, hmem, hFg.symm⟩
  by_cases hFnon : ∃ᶠ z in 𝓝 x, F z ≠ 0
  swap
  · have hFzero : F =ᶠ[𝓝 x] (fun _ : X => (0 : ℂ)) := by
      have h : ∀ᶠ z in 𝓝 x, F z = 0 := by
        simpa only [Filter.Frequently, not_not, ne_eq] using hFnon
      exact h
    have hzeroMem : (multiplierIdeal (n := m + 1) 1 φ).mem x (fun _ : X => (0 : ℂ)) :=
      ⟨holomorphicAt_const (n := m + 1) 0,
        multiplierIntegrableAt_zero (chartFunction φ (complexChartAt (n := m + 1) x))
          zero_lt_one ((complexChartAt (n := m + 1) x).val x) volume⟩
    exact MultiplierIdealProductComparison.mem_multiplierIdeal_congr hzeroMem hFzero.symm
  refine ⟨hF, ?_⟩
  have hw : QuasiPlurisubharmonicAt (chartFunction φ (complexChartAt (n := m + 1) x))
      ((complexChartAt (n := m + 1) x).val x) :=
    hφ _ _ ((complexChartAt (n := m + 1) x).val.map_source (mem_complexChartAt_source x))
  have hgd : ∀ᶠ z in 𝓝 ((complexChartAt (n := m + 1) x).val x),
      DifferentiableAt ℂ (fun z => F ((complexChartAt (n := m + 1) x).val.symm z)) z :=
    MultiplierIdealBergmanNadelManifold.eventually_differentiableAt_comp_chart_symm
      (mem_complexChartAt_source x) hF
  apply (AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs
    hπ x one_pos hw hgd).mpr
  intro y hy
  subst hy
  apply fibre_multiplierIntegrableAt hπ hD hlog F y hF hFnon
  intro P hP hyP
  have h := htest P hP ⟨y, hyP, rfl⟩
  rwa [(stalkOrdE_eq (componentPresentation hπ hD P hP) (π y) g F hF hFg).1] at h

/-- **Source `thm:valuativemulti`, finite log-resolution test** (revised source, erratum E07).
Let `φ` be quasi-psh on `X`, `π : Y → X` a proper bimeromorphic holomorphic map such that `π^*φ`
has log singularities along the simple normal crossing effective `ℚ`-divisor `D` (its resolved
polar divisor).  For `x ∈ X` and `f ∈ 𝒪_{X,x}`: `f ∈ 𝓘(φ)_x` iff
`ord_E(f) > ν(φ, E) - A_X(E)` for every component `E` of `D` that meets `π⁻¹(x)`. -/
theorem mem_multiplierIdeal_iff_finiteLogResolutionTest {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ) {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {D : EffectiveGeometricQDivisor (m + 1) Y}
    (hD : D.IsSNC) (hlog : NativeHasLogSingularitiesAlong D (φ ∘ π)) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x) :
    g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x ↔
      FiniteLogResolutionTest φ hπ hD x g :=
  ⟨finiteLogResolutionTest_of_mem hφ hπ hD hlog x g, mem_of_finiteLogResolutionTest hφ hπ hD hlog x g⟩

/-- **Source `thm:valuativemulti`, final clause, for a log resolution in the sense of
`def:logres`** (`IsSourceLogResolution`: a modification `π` such that `π^*φ` has log singularities
along a simple normal crossing effective `ℚ`-divisor): for its resolved polar divisor `D`, the
finite test characterises `𝓘(φ)_x` for every `x ∈ X` and every `f ∈ 𝒪_{X,x}`. -/
theorem isSourceLogResolution_finiteTest {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := m + 1) φ) {π : Y → X}
    (hres : IsSourceLogResolution (m + 1) φ π) :
    ∃ (hπ : IsAnalyticModification (n := m + 1) π) (D : EffectiveGeometricQDivisor (m + 1) Y)
      (hD : D.IsSNC), NativeHasLogSingularitiesAlongAnyDimension D (φ ∘ π) ∧
        ∀ (x : X) (g : actualComplexStructureStalk (n := m + 1) x),
          g ∈ actualWholeSheafStalkIdeal (multiplierIdeal (n := m + 1) 1 φ) x ↔
            FiniteLogResolutionTest φ hπ hD x g := by
  obtain ⟨hmod, D, hD, hlog⟩ := hres
  have hπ : IsAnalyticModification (n := m + 1) π := hmod.isConventionModification.1
  exact ⟨hπ, D, hD, hlog, fun x g =>
    mem_multiplierIdeal_iff_finiteLogResolutionTest hφ hπ hD hlog x g⟩

/-- **The finite test in the book's real form** `ord_E(f) > ν(φ, E) - A_X(E)` for a nonzero germ
`f` (then `ord_E(f)` and `ν(φ, E)` are finite). -/
theorem finiteLogResolutionTest_iff_real {φ : X → EReal} {π : Y → X}
    (hπ : IsAnalyticModification (n := m + 1) π) {D : EffectiveGeometricQDivisor (m + 1) Y}
    (hD : D.IsSNC) (hlog : NativeHasLogSingularitiesAlong D (φ ∘ π)) (x : X)
    (g : actualComplexStructureStalk (n := m + 1) x) (hg : g ≠ 0) :
    FiniteLogResolutionTest φ hπ hD x g ↔
      ∀ (P : GeometricPrimeCarrier (m + 1) Y) (hP : 0 < D.coefficient P), (∃ y ∈ P.val, π y = x) →
        (presentationReader φ (componentPresentation hπ hD P hP)).toReal -
            (presentationLogDiscrepancy (componentPresentation hπ hD P hP) : ℝ) <
          ((stalkOrdE (componentPresentation hπ hD P hP) x g).toNat : ℝ) := by
  refine forall₂_congr fun P hP => imp_congr_right fun hmeet => ?_
  obtain ⟨y, hyP, hyx⟩ := hmeet
  have hν := presentationReader_component_ne_top hπ hD hlog P hP hyP
  obtain ⟨F, hF, hFg⟩ := exists_original_representative x g
  have hord : stalkOrdE (componentPresentation hπ hD P hP) x g ≠ ⊤ := by
    rw [(stalkOrdE_eq (componentPresentation hπ hD P hP) x g F hF hFg).2]
    exact actualGermFibreOrder_ne_top hπ P.val (component_isClosedConnectedSubmanifold hD P hP) x
      ⟨y, hyP, hyx⟩ g hg
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hord
  rw [← hk, ENat.toNat_natCast]
  have hext : extendedOrderValue (k : ℕ∞) = (k : ℝ≥0∞) := rfl
  set A := presentationLogDiscrepancy (componentPresentation hπ hD P hP)
  have hfinR : (k : ℝ≥0∞) + (A : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top k, ENNReal.natCast_ne_top A⟩
  rw [hext, ← ENNReal.toReal_lt_toReal hν hfinR,
    ENNReal.toReal_add (ENNReal.natCast_ne_top k) (ENNReal.natCast_ne_top A),
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  constructor <;> intro h <;> linarith

end Test

end SGPT.PSH.ValMultFinite
