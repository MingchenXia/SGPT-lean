import SGPT.GAGA.H0SSchemeGAGA

/-!
# Regular functions on the complex points of a smooth complex scheme


`X` is smooth of relative dimension `n` over `ℂ` with a closed projective embedding `E`; its
complex points `X(ℂ)` carry the analytic topology, and a regular function `r ∈ Γ(X, U)` has the
analytic function `p ↦ r(p)` on `U(ℂ)` (`SGPT.Okounkov.schemeOpenRegularFunction`).

* `exists_specializes_schemeComplexPoint`: every point of an open `W ⊆ X` specializes to a
  complex point of `W` (Nullstellensatz); hence `le_of_forall_schemeComplexPoint`: an open
  inclusion can be checked on complex points.
* `eq_zero_of_schemeOpenRegularFunction_eq_zero`: a regular function vanishing at all complex
  points of `U` is zero (faithful flatness of `𝒪_{X,x} → 𝒪^an_{X,x}`).
* `IsRegularOn U φ`: a function `φ : X(ℂ) → ℂ` agrees on `U(ℂ)` with the analytic function of a
  regular function on `U`.  This class is closed under the ring operations, restriction and
  inversion on basic opens, and it is **local** (`isRegularOn_of_local`, by the two facts above
  and the sheaf property).
* **`exists_isRegularOn_pow_mul`** (the extension lemma, Hartshorne II.5.14 for a basic open of
  an affine open): if `φ` is regular on `D(h) ⊆ V`, `V` affine, then `h^{r+1} φ` is regular on
  `V` for some `r` (`Γ(D(h), 𝒪_X) = Γ(V, 𝒪_X)_h`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.H0L

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.GAGA.H0S
open scoped Topology Manifold

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))

/-! ### Closed points are complex points -/

section Points

variable [LocallyOfFiniteType f]

/-- **Every point of an open `W` specializes to a complex point of `W`**: in an affine open
neighbourhood the prime of the point lies in a maximal ideal, whose point is complex by the
Nullstellensatz. -/
theorem exists_specializes_schemeComplexPoint {W : X.Opens} {y : X} (hy : y ∈ W) :
    ∃ p : SchemeComplexPoint f,
      schemeComplexPointImage f p ∈ W ∧ y ⤳ schemeComplexPointImage f p := by
  obtain ⟨V, hV, hyV, hVW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hy
  have hVa : IsAffineOpen V := hV
  set P := hVa.primeIdealOf ⟨y, hyV⟩
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
  obtain ⟨p, hp⟩ := SGPT.NAPotential.Berkovich.exists_schemeComplexPoint_fromSpec f hVa M hM
  refine ⟨p, hVW ?_, ?_⟩
  · rw [hp]
    exact SGPT.NAPotential.Berkovich.fromSpec_mem hVa _
  · rw [hp]
    have hsp : P ⤳ (⟨M, hM.isPrime⟩ : PrimeSpectrum Γ(X, V)) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hPM
    have h := hsp.map hVa.fromSpec.continuous
    rwa [show hVa.fromSpec P = y from hVa.fromSpec_primeIdealOf ⟨y, hyV⟩] at h

/-- **Inclusions of opens are detected on complex points.** -/
theorem le_of_forall_schemeComplexPoint {W W' : X.Opens}
    (h : ∀ p : SchemeComplexPoint f,
      schemeComplexPointImage f p ∈ W → schemeComplexPointImage f p ∈ W') : W ≤ W' := by
  intro y hy
  obtain ⟨p, hpW, hyp⟩ := exists_specializes_schemeComplexPoint f hy
  exact hyp.mem_open W'.isOpen (h p hpW)

end Points

/-! ### Regular functions as functions on complex points -/

variable (E : ClosedProjectiveEmbedding f) (n : ℕ) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f]

local instance h0lRegTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0lRegCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance h0lRegManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

theorem schemeOpenRegularFunction_sub' (U : X.Opens) (r s : Γ(X, U)) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ U) :
    schemeOpenRegularFunction f n E U (r - s) p =
      schemeOpenRegularFunction f n E U r p - schemeOpenRegularFunction f n E U s p := by
  simp only [schemeOpenRegularFunction, dif_pos hp, map_sub]

theorem schemeOpenRegularFunction_pow' (U : X.Opens) (r : Γ(X, U)) (k : ℕ)
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) :
    schemeOpenRegularFunction f n E U (r ^ k) p = schemeOpenRegularFunction f n E U r p ^ k := by
  simp only [schemeOpenRegularFunction, dif_pos hp, map_pow]

theorem schemeOpenRegularFunction_mul' (U : X.Opens) (r s : Γ(X, U)) {p : SchemeComplexPoint f}
    (hp : schemeComplexPointImage f p ∈ U) :
    schemeOpenRegularFunction f n E U (r * s) p =
      schemeOpenRegularFunction f n E U r p * schemeOpenRegularFunction f n E U s p :=
  schemeOpenRegularFunction_mul f n E U r s hp

theorem schemeOpenRegularFunction_eq_zero_of_not_mem_basicOpen (U : X.Opens) (r : Γ(X, U))
    {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U)
    (hD : schemeComplexPointImage f p ∉ X.basicOpen r) :
    schemeOpenRegularFunction f n E U r p = 0 := by
  by_contra h
  exact hD ((schemeOpenRegularFunction_ne_zero_iff f E n U r p hp).mp h)

/-- **A regular function vanishing at all complex points is zero.** The germ at a complex point
maps to the zero analytic germ, hence is zero (the analytification map of stalks is faithfully
flat, hence injective); every point specializes to a complex point. -/
theorem eq_zero_of_schemeOpenRegularFunction_eq_zero {U : X.Opens} (r : Γ(X, U))
    (h : ∀ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ U →
      schemeOpenRegularFunction f n E U r p = 0) : r = 0 := by
  let := E.locallyOfFiniteType
  apply TopCat.Presheaf.section_ext X.sheaf U r 0
  intro y hy
  obtain ⟨p, hpU, hyp⟩ := exists_specializes_schemeComplexPoint f hy
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' (U : Set X)) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  have hgerm : X.presheaf.germ U (schemeComplexPointImage f p) hpU r = 0 := by
    apply (schemeNativeStalkGerm_faithfullyFlat f n p).injective
    rw [map_zero, ← schemeOpenRegularFunction_germ f n E U r p hpU]
    have hz : NativeHolGerm.mk (schemeOpenRegularFunction f n E U r)
        (schemeOpenRegularFunction_holomorphicAt f n E U r p hpU) =
          NativeHolGerm.mk (n := n) (fun _ => (0 : ℂ)) (holomorphicAt_const 0) :=
      NativeHolGerm.mk_eq_mk_iff.mpr (by
        filter_upwards [hO.mem_nhds hpU] with q hq
        exact h q hq)
    rw [hz]
    rfl
  change X.presheaf.germ U y hy r = X.presheaf.germ U y hy 0
  rw [map_zero, ← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hpU hyp r, hgerm,
    map_zero]

/-- Two regular functions with the same values at all complex points are equal. -/
theorem eq_of_schemeOpenRegularFunction_eq {U : X.Opens} (r s : Γ(X, U))
    (h : ∀ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ U →
      schemeOpenRegularFunction f n E U r p = schemeOpenRegularFunction f n E U s p) : r = s := by
  rw [← sub_eq_zero]
  refine eq_zero_of_schemeOpenRegularFunction_eq_zero f E n (r - s) fun p hp => ?_
  rw [schemeOpenRegularFunction_sub' f E n U r s hp, h p hp, sub_self]

/-- **`φ` is regular on `U`**: it agrees on the complex points of `U` with the analytic function
of a regular function on `U`. -/
def IsRegularOn (U : X.Opens) (φ : SchemeComplexPoint f → ℂ) : Prop :=
  ∃ r : Γ(X, U), ∀ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ U →
    φ p = schemeOpenRegularFunction f n E U r p

variable {f E n}

theorem isRegularOn_schemeOpenRegularFunction (U : X.Opens) (r : Γ(X, U)) :
    IsRegularOn f E n U (schemeOpenRegularFunction f n E U r) :=
  ⟨r, fun _ _ => rfl⟩

theorem IsRegularOn.congr {U : X.Opens} {φ ψ : SchemeComplexPoint f → ℂ}
    (h : IsRegularOn f E n U φ)
    (heq : ∀ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ U → φ p = ψ p) :
    IsRegularOn f E n U ψ := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, fun p hp => (heq p hp).symm.trans (hr p hp)⟩

theorem IsRegularOn.mono {U V : X.Opens} {φ : SchemeComplexPoint f → ℂ}
    (h : IsRegularOn f E n U φ) (hVU : V ≤ U) : IsRegularOn f E n V φ := by
  obtain ⟨r, hr⟩ := h
  exact ⟨X.presheaf.map (homOfLE hVU).op r, fun p hp =>
    (hr p (hVU hp)).trans (schemeOpenRegularFunction_restrict f n E V U hVU r hp).symm⟩

theorem isRegularOn_one (U : X.Opens) : IsRegularOn f E n U (fun _ => 1) :=
  ⟨1, fun _ hp => (schemeOpenRegularFunction_one f n E U hp).symm⟩

theorem IsRegularOn.mul {U : X.Opens} {φ ψ : SchemeComplexPoint f → ℂ}
    (hφ : IsRegularOn f E n U φ) (hψ : IsRegularOn f E n U ψ) :
    IsRegularOn f E n U (fun p => φ p * ψ p) := by
  obtain ⟨r, hr⟩ := hφ
  obtain ⟨s, hs⟩ := hψ
  exact ⟨r * s, fun p hp => by
    beta_reduce
    rw [schemeOpenRegularFunction_mul' f E n U r s hp, hr p hp, hs p hp]⟩

theorem IsRegularOn.pow {U : X.Opens} {φ : SchemeComplexPoint f → ℂ}
    (hφ : IsRegularOn f E n U φ) (k : ℕ) : IsRegularOn f E n U (fun p => φ p ^ k) := by
  obtain ⟨r, hr⟩ := hφ
  exact ⟨r ^ k, fun p hp => by
    beta_reduce
    rw [schemeOpenRegularFunction_pow' f E n U r k hp, hr p hp]⟩

/-- **Inversion**: if `φ` is represented by `r` on `U`, then `φ⁻¹` is regular on `D(r)`. -/
theorem IsRegularOn.inv {U : X.Opens} {φ : SchemeComplexPoint f → ℂ} {r : Γ(X, U)}
    (hr : ∀ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ U →
      φ p = schemeOpenRegularFunction f n E U r p) :
    IsRegularOn f E n (X.basicOpen r) (fun p => (φ p)⁻¹) := by
  obtain ⟨u, hu⟩ : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le r)).op r) :=
    X.toRingedSpace.isUnit_res_basicOpen r
  refine ⟨(u⁻¹ : (Γ(X, X.basicOpen r))ˣ), fun p hp => ?_⟩
  have hpU : schemeComplexPointImage f p ∈ U := X.basicOpen_le r hp
  have h1 := schemeOpenRegularFunction_mul' f E n (X.basicOpen r) (u : Γ(X, X.basicOpen r))
    (u⁻¹ : (Γ(X, X.basicOpen r))ˣ) hp
  rw [Units.mul_inv, schemeOpenRegularFunction_one f n E _ hp] at h1
  have h2 : schemeOpenRegularFunction f n E (X.basicOpen r) (u : Γ(X, X.basicOpen r)) p = φ p := by
    rw [hu, hr p hpU]
    exact schemeOpenRegularFunction_restrict f n E (X.basicOpen r) U (X.basicOpen_le r) r hp
  rw [h2] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm).symm

/-- **Regularity is local** on the complex points: if every complex point of `U` has an open
neighbourhood in `U` on which `φ` is regular, then `φ` is regular on `U`. -/
theorem isRegularOn_of_local {U : X.Opens} {φ : SchemeComplexPoint f → ℂ}
    (h : ∀ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ U →
      ∃ V : X.Opens, V ≤ U ∧ schemeComplexPointImage f p ∈ V ∧ IsRegularOn f E n V φ) :
    IsRegularOn f E n U φ := by
  let := E.locallyOfFiniteType
  let ι := {V : X.Opens // V ≤ U ∧ IsRegularOn f E n V φ}
  choose r hr using fun V : ι => V.2.2
  have hcover : U ≤ iSup (fun V : ι => V.1) := by
    apply le_of_forall_schemeComplexPoint f
    intro p hp
    obtain ⟨V, hVU, hpV, hV⟩ := h p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVU, hV⟩, hpV⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj (fun V : ι => V.1) r := by
    intro V W
    change X.presheaf.map (homOfLE inf_le_left).op (r V) =
      X.presheaf.map (homOfLE inf_le_right).op (r W)
    refine eq_of_schemeOpenRegularFunction_eq f E n _ _ fun p hp => ?_
    rw [schemeOpenRegularFunction_restrict f n E _ _ inf_le_left _ hp,
      schemeOpenRegularFunction_restrict f n E _ _ inf_le_right _ hp, ← hr V p hp.1,
      ← hr W p hp.2]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun V : ι => V.1) U
    (fun V => homOfLE V.2.1) hcover r hcompat
  refine ⟨s, fun p hp => ?_⟩
  obtain ⟨V, hVU, hpV, hV⟩ := h p hp
  have hsV : X.presheaf.map (homOfLE hVU).op s = r ⟨V, hVU, hV⟩ := hs ⟨V, hVU, hV⟩
  rw [hr ⟨V, hVU, hV⟩ p hpV, ← hsV]
  exact schemeOpenRegularFunction_restrict f n E V U hVU s hpV

/-- **Extension over a basic open of an affine open** (Hartshorne II.5.14): if `φ` is regular
on `D(h) ⊆ V` with `V` affine, then `h^{r+1} φ` is regular on `V` for some `r`. -/
theorem exists_isRegularOn_pow_mul {V : X.Opens} (hV : IsAffineOpen V) (h : Γ(X, V))
    {φ : SchemeComplexPoint f → ℂ} (hφ : IsRegularOn f E n (X.basicOpen h) φ) :
    ∃ r : ℕ, IsRegularOn f E n V
      (fun p => schemeOpenRegularFunction f n E V h p ^ (r + 1) * φ p) := by
  obtain ⟨t, ht⟩ := hφ
  have := hV.isLocalization_basicOpen h
  obtain ⟨⟨R, d⟩, hRd⟩ := IsLocalization.surj (Submonoid.powers h) t
  obtain ⟨r, hr⟩ := Submonoid.mem_powers_iff _ _ |>.mp d.2
  refine ⟨r, h * R, fun p hp => ?_⟩
  beta_reduce
  rw [schemeOpenRegularFunction_mul' f E n V h R hp]
  by_cases hpD : schemeComplexPointImage f p ∈ X.basicOpen h
  · have e := congrArg (fun z => schemeOpenRegularFunction f n E (X.basicOpen h) z p) hRd
    simp only at e
    rw [schemeOpenRegularFunction_mul' f E n _ _ _ hpD] at e
    change _ * schemeOpenRegularFunction f n E (X.basicOpen h)
        (X.presheaf.map (homOfLE (X.basicOpen_le h)).op (d : Γ(X, V))) p =
      schemeOpenRegularFunction f n E (X.basicOpen h)
        (X.presheaf.map (homOfLE (X.basicOpen_le h)).op R) p at e
    rw [schemeOpenRegularFunction_restrict f n E _ V (X.basicOpen_le h) _ hpD,
      schemeOpenRegularFunction_restrict f n E _ V (X.basicOpen_le h) _ hpD, ← hr,
      schemeOpenRegularFunction_pow' f E n V h r hp, ← ht p hpD] at e
    rw [← e]
    ring
  · rw [schemeOpenRegularFunction_eq_zero_of_not_mem_basicOpen f E n V h hp hpD]
    ring

end SGPT.GAGA.H0L
