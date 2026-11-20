import SGPT.Okounkov.OF13Principalize
import SGPT.Okounkov.OF13CoordinatePrime
import SGPT.Foundations.Analysis.Pending.SNCSupportedDivisorFixedChartNormalForm
import SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRelativeIdeal
import SGPT.Foundations.Analysis.Pending.BlowupFlatCoordinates
import SGPT.Foundations.Analysis.Pending.HironakaG11BennettHolGerm
import SGPT.Foundations.Analysis.Pending.HolomorphicCoordinateFactorization
import SGPT.Foundations.Analysis.Pending.HironakaDivisorResidualUnit
import SGPT.Foundations.Analysis.Pending.ActualHolomorphicGermFactoriality
import SGPT.Foundations.Analysis.Pending.HolomorphicCoordinatePrime

/-!
# Simple normal crossings charts in germ language

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` (existence part of
[CFKLRS17, Thm 2.9]): reading the output of the principalization at a point.

Let `Y` be a complex manifold with a simple normal crossings divisor `E` (TN's `IsSNCDivisor`:
at every point, adapted holomorphic coordinates `Φ ∘ chart` in which the members through the point
are coordinate hyperplanes).

* `flatGermEquiv Φ h0 : 𝒪_{Y,y} ≃ 𝒪_{ℂⁿ,0}`: the germ ring isomorphism of adapted coordinates
  (`g ↦ g ∘ chart⁻¹ ∘ Φ⁻¹`); it sends the flat coordinate germs `ℓⱼ = (Φ ∘ chart)ⱼ` to the
  coordinate germs (`flatGermEquiv_flatCoord`), so the `ℓⱼ` generate the maximal ideal
  (`span_flatCoord_eq_maximalIdeal`);
* `isComplexAnalyticSubset_of_isSNCDivisor`: the members of `E` are analytic subsets;
* `flatCoord_generates_vanishingIdeal`: if a member is `{ℓⱼ = 0}` near `y`, the germ of `ℓⱼ`
  generates its ideal at `y`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF13

open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.NormalCrossings
open HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
open HironakaSmoothCentreRelativeIdeal BlowupFlatCoordinates
open HironakaActualAnalyticBlockGraphTranslation HironakaActualInheritedNextBlockGraph
open SGPT.Okounkov
open scoped Topology Manifold

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-! ### The germ ring of adapted coordinates -/

section Flat

variable {y : Y} (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
  (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0)

/-- The germ ring isomorphism `𝒪_{Y,y} ≃ 𝒪_{ℂⁿ,0}` of the adapted coordinates `Φ ∘ chart`:
`g ↦ g ∘ chart⁻¹ ∘ Φ⁻¹`. -/
def flatGermEquiv : NativeHolGerm n Y y ≃+* HolGerm (ComplexModel n) :=
  (NativeHolGerm.chartEquiv y).trans
    (localGermAlgEquiv (recenteredEquiv _ Φ) (recenteredEquiv_zero _ Φ h0)).symm.toRingEquiv

theorem coe_flatGermEquiv_mk (f : Y → ℂ) (hf : HolomorphicAt n f y) :
    ((flatGermEquiv Φ h0 (NativeHolGerm.mk f hf) : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) =
      ((fun z => f ((complexChartAt (n := n) y).val.symm (Φ.invFun z)) : ComplexModel n → ℂ) :
        Germ (𝓝 (0 : ComplexModel n)) ℂ) := by
  change ((fun z => f ((complexChartAt (n := n) y).val.symm
    ((Φ.invFun z - (complexChartAt (n := n) y).val y) + (complexChartAt (n := n) y).val y)) :
      ComplexModel n → ℂ) : Germ (𝓝 (0 : ComplexModel n)) ℂ) = _
  simp only [sub_add_cancel]

omit [IsComplexManifold n Y] in
include h0 in
theorem zero_mem_target : (0 : ComplexModel n) ∈ Φ.target := by
  rw [← h0]
  exact Φ.mapsTo_toFun Φ.center_mem_source

variable (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)

include hsrc in
/-- The flat coordinate germs go to the coordinate germs. -/
theorem flatGermEquiv_flatCoord (j : Fin n) :
    flatGermEquiv Φ h0 (NativeHolGerm.mk (flatCoord Φ j)
      (holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ))) = coordinateGerm j := by
  apply Subtype.ext
  rw [coe_flatGermEquiv_mk]
  unfold coordinateGerm
  rw [HolGerm.coe_mk]
  apply Germ.coe_eq.mpr
  filter_upwards [Φ.isOpen_target.mem_nhds (zero_mem_target Φ h0)] with z hz
  exact congrFun (congrArg (fun w : ComplexModel n => (w : Fin n → ℂ))
    (flatInverse_mem Φ hz hsrc).2) j

include h0 hsrc in
/-- The flat coordinates generate the maximal ideal of `𝒪_{Y,y}`. -/
theorem span_flatCoord_eq_maximalIdeal :
    Ideal.span (Set.range fun j => NativeHolGerm.mk (flatCoord Φ j)
      (holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ))) =
      IsLocalRing.maximalIdeal (NativeHolGerm n Y y) := by
  have h := congrArg (Ideal.map (flatGermEquiv Φ h0).symm)
    (HironakaG11BennettHolGerm.maximalIdeal_eq_span_coordinateGerm n).symm
  rw [IsLocalRing.map_ringEquiv_maximalIdeal, Ideal.map_span, ← Set.range_comp] at h
  rw [← h]
  congr 2
  funext j
  change _ = (flatGermEquiv Φ h0).symm (coordinateGerm j)
  rw [← flatGermEquiv_flatCoord Φ h0 hsrc j, RingEquiv.symm_apply_apply]

end Flat

/-! ### Members of a normal crossings divisor -/

/-- The members of a simple normal crossings divisor are analytic subsets. -/
theorem isComplexAnalyticSubset_of_isSNCDivisor {E : List (Set Y)} (hE : IsSNCDivisor n E)
    (i : Fin E.length) : IsComplexAnalyticSubset (n := n) (E.get i) := by
  intro x
  by_cases hx : x ∈ E.get i
  · obtain ⟨S, ⟨Φ, hsrc, h0, hflat⟩, hcard, -⟩ := hE.2 x
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (hcard i hx)
    refine ⟨{ generatorCount := 1
              generator := fun _ w => Φ.toFun w j
              coordinateNeighborhood := Φ.source
              isOpen_coordinateNeighborhood := Φ.isOpen_source
              center_mem_coordinateNeighborhood := Φ.center_mem_source
              coordinateNeighborhood_subset_target := hsrc
              generator_holomorphic := fun _ => ?_
              zeroLocus := fun {z} hz hzN => ?_ }⟩
    · intro w hw
      exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n => ℂ) j).differentiableAt.comp w
        (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hw))).differentiableWithinAt
    · rw [hflat i hx hz hzN, hj]
      simp [coordSubspace]
  · exact ⟨SGPT.GAGA.ChowBl.complementPresentation (hE.1 _ (List.get_mem _ _)) hx⟩

/-! ### Local equations of members -/

section LocalEquation

variable {y : Y} (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
  (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0)
  (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)

include h0 hsrc in
/-- If the set `H` is `{(Φ ∘ chart)ⱼ = 0}` near `y`, the germ of the flat coordinate `ℓⱼ` generates
the ideal of `H` at `y`. -/
theorem flatCoord_generates_vanishingIdeal {H : Set Y} {j : Fin n}
    (hflat : ∀ {z : Y}, z ∈ (complexChartAt (n := n) y).val.source →
      (complexChartAt (n := n) y).val z ∈ Φ.source →
        (z ∈ H ↔ Φ.toFun ((complexChartAt (n := n) y).val z) ∈ coordSubspace {j}))
    (g : Y → ℂ) (hg : HolomorphicAt n g y) (hgH : (vanishingIdeal (n := n) H).mem y g) :
    NativeHolGerm.mk g hg ∈ Ideal.span {NativeHolGerm.mk (flatCoord Φ j)
      (holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ))} := by
  classical
  obtain ⟨F, hF, hFeq⟩ := HolGerm.exists_eq_mk (flatGermEquiv Φ h0 (NativeHolGerm.mk g hg))
  have hFG : F =ᶠ[𝓝 0] fun z => g ((complexChartAt (n := n) y).val.symm (Φ.invFun z)) := by
    have h1 := congrArg (fun G : HolGerm (ComplexModel n) => (G : Germ (𝓝 (0 : ComplexModel n)) ℂ))
      hFeq
    simp only [coe_flatGermEquiv_mk, HolGerm.coe_mk] at h1
    exact (Germ.coe_eq.mp h1).symm
  -- `F` vanishes on the coordinate hyperplane `{zⱼ = 0}` near `0`
  have hT : Tendsto (fun u => (complexChartAt (n := n) y).val.symm (Φ.invFun u)) (𝓝 0) (𝓝 y) := by
    have h := tendsto_flatInverse Φ (mem_flatDomain_self Φ)
    rwa [show Φ.toFun ((chartAt (ComplexModel n) y) y) = 0 from h0] at h
  have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z j = 0 → F z = 0 := by
    obtain ⟨-, hgv⟩ := hgH
    filter_upwards [hFG, Φ.isOpen_target.mem_nhds (zero_mem_target Φ h0), hT.eventually hgv]
      with z hz hzT hzg hzj
    rw [hz]
    obtain ⟨hdom, hback⟩ := flatInverse_mem Φ hzT hsrc
    apply hzg
    refine (hflat hdom.1 hdom.2).mpr ?_
    intro i hi
    have hb := congrArg (fun w : ComplexModel n => w i) hback
    simp only at hb
    erw [hb]
    rw [Finset.mem_singleton.mp hi]
    exact hzj
  -- hence `F` lies in the coordinate ideal `(wⱼ)`
  have hblock : flatGermEquiv Φ h0 (NativeHolGerm.mk g hg) ∈
      actualAnalyticCoordinateBlockIdeal ({j} : Set (Fin n)) := by
    rw [mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero, hFeq]
    unfold actualBlockProjectionGermHom
    rw [compAlgHom_mk]
    rw [← HolGerm.mk_zero]
    apply HolGerm.mk_eq_mk_iff.mpr
    have hP : Tendsto (actualBlockCoordinateProjection ({j}ᶜ : Set (Fin n))) (𝓝 0) (𝓝 0) := by
      simpa using (actualBlockCoordinateProjection ({j}ᶜ : Set (Fin n))).continuous.tendsto 0
    filter_upwards [hP.eventually hvan] with z hz
    apply hz
    rw [actualBlockCoordinateProjection_apply]
    simp
  have hspan : actualAnalyticCoordinateBlockIdeal ({j} : Set (Fin n)) =
      Ideal.span {coordinateGerm j} := by
    rw [actualAnalyticCoordinateBlockIdeal, Set.image_singleton]
  rw [hspan, Ideal.mem_span_singleton'] at hblock
  obtain ⟨c, hc⟩ := hblock
  rw [Ideal.mem_span_singleton']
  refine ⟨(flatGermEquiv Φ h0).symm c, ?_⟩
  apply (flatGermEquiv Φ h0).injective
  rw [map_mul, RingEquiv.apply_symm_apply, flatGermEquiv_flatCoord Φ h0 hsrc, hc]

end LocalEquation

/-! ### The monomial chart of a principalized divisor -/

section Monomial

theorem coe_holGerm_unit_monomial (H : ComplexModel n → ℂ)
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z) (a : Fin n → ℕ) :
    ((HolGerm.mk H hH * ∏ j, coordinateGerm j ^ a j : HolGerm (ComplexModel n)) :
      Germ (𝓝 (0 : ComplexModel n)) ℂ) =
      ((fun z => H z * ∏ j : Fin n, z j ^ a j : ComplexModel n → ℂ) :
        Germ (𝓝 (0 : ComplexModel n)) ℂ) := by
  have hfun : (fun z => H z * ∏ j : Fin n, z j ^ a j : ComplexModel n → ℂ) =
      H * ∏ j, (fun z : ComplexModel n => (z j : ℂ)) ^ a j := by
    funext z
    simp [Finset.prod_apply]
  rw [hfun, Germ.coe_mul, ← Germ.coe_coeRingHom, map_prod]
  simp only [Germ.coe_coeRingHom, Germ.coe_pow]
  rw [Subring.coe_mul, SubmonoidClass.coe_finsetProd]
  simp only [SubmonoidClass.coe_pow]
  rfl

/-- **The monomial chart of a principalized divisor.** Let `D` be an effective divisor on `Y`
whose support lies in a simple normal crossings divisor `E`. At every `y ∈ Y` there are flat
coordinates `ℓ₁, …, ℓₙ` (their germs generate the maximal ideal), a set `M` of indices whose
coordinates are local equations at `y` of members `Hⱼ` of `E` (analytic subsets), and a local
generator `g` of `D` at `y` such that every divisor of the germ of `g` is a unit times a monomial
`∏_{j ∈ M} ℓⱼ^{αⱼ}`. -/
theorem exists_sncChart_monomial (D : EffectiveDivisor n Y) {E : List (Set Y)}
    (hE : IsSNCDivisor n E) (hsupp : D.support ⊆ ⋃ H ∈ E, H) (y : Y) :
    ∃ (ℓ : Fin n → Y → ℂ) (hℓ : ∀ j, HolomorphicAt n (ℓ j) y),
      Ideal.span (Set.range fun j => NativeHolGerm.mk (ℓ j) (hℓ j)) =
        IsLocalRing.maximalIdeal (NativeHolGerm n Y y) ∧
      ∃ (M : Finset (Fin n)) (H : Fin n → Set Y),
        (∀ j ∈ M, IsComplexAnalyticSubset (n := n) (H j)) ∧
        (∀ j ∈ M, (vanishingIdeal (n := n) (H j)).mem y (ℓ j)) ∧
        (∀ j ∈ M, ∀ (h : Y → ℂ) (hh : HolomorphicAt n h y),
          (vanishingIdeal (n := n) (H j)).mem y h →
            NativeHolGerm.mk h hh ∈ Ideal.span {NativeHolGerm.mk (ℓ j) (hℓ j)}) ∧
        ∃ (g : Y → ℂ) (hg : HolomorphicAt n g y),
          (∀ f, D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = g) y f) ∧
          ∀ c : NativeHolGerm n Y y, c ∣ NativeHolGerm.mk g hg →
            ∃ (η : (NativeHolGerm n Y y)ˣ) (α : Fin n → ℕ), (∀ j ∉ M, α j = 0) ∧
              c = η * ∏ j, (NativeHolGerm.mk (ℓ j) (hℓ j)) ^ (α j) := by
  classical
  obtain ⟨S, ⟨Φ, hsrc, h0, hflat⟩, hcard, -⟩ := hE.2 y
  obtain ⟨U, hU, hyU, g, hgd, -, hgen, -, -, -, a, H₀, hH₀, hH₀0, hfac⟩ :=
    SNCSupportedDivisorFixedChartNormalForm.exists_unit_monomial_generator_in_adapted_coordinates
      D E hE hsupp y S Φ hsrc h0 hcard hflat
  let ℓ : Fin n → Y → ℂ := flatCoord Φ
  have hℓ : ∀ j, HolomorphicAt n (ℓ j) y := fun j =>
    holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ)
  let M : Finset (Fin n) := Finset.univ.filter fun j => ∃ i, y ∈ E.get i ∧ S i = {j}
  let H : Fin n → Set Y := fun j =>
    if h : ∃ i, y ∈ E.get i ∧ S i = {j} then E.get h.choose else ∅
  have hHM : ∀ j ∈ M, ∃ i, y ∈ E.get i ∧ S i = {j} ∧ H j = E.get i := fun j hj => by
    have h : ∃ i, y ∈ E.get i ∧ S i = {j} := (Finset.mem_filter.mp hj).2
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, by simp only [H, dif_pos h]⟩
  have hg : HolomorphicAt n g y :=
    SGPT.PSH.IdealRestriction.holomorphicAt_of_mdifferentiableOn hU hgd hyU
  -- the generator in adapted coordinates
  have hθg : flatGermEquiv Φ h0 (NativeHolGerm.mk g hg) =
      HolGerm.mk H₀ hH₀ * ∏ j, coordinateGerm j ^ a j := by
    apply Subtype.ext
    rw [coe_flatGermEquiv_mk, coe_holGerm_unit_monomial]
    exact Germ.coe_eq.mpr hfac
  -- exponents vanish off the members through `y`
  have hT : Tendsto (fun u => (complexChartAt (n := n) y).val.symm (Φ.invFun u)) (𝓝 0) (𝓝 y) := by
    have h := tendsto_flatInverse Φ (mem_flatDomain_self Φ)
    rwa [show Φ.toFun ((chartAt (ComplexModel n) y) y) = 0 from h0] at h
  have havoid : ∀ᶠ y' in 𝓝 y, ∀ i : Fin E.length, y ∉ E.get i → y' ∉ E.get i := by
    apply eventually_all.mpr
    intro i
    by_cases hyi : y ∈ E.get i
    · exact Eventually.of_forall fun _ h => (h hyi).elim
    · have hi : ∀ᶠ y' in 𝓝 y, y' ∉ E.get i :=
        (hE.1 _ (List.get_mem _ _)).isOpen_compl.mem_nhds hyi
      exact hi.mono fun _ hy _ => hy
  have hzeroM : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      H₀ z * ∏ j : Fin n, z j ^ a j = 0 → ∃ j ∈ M, z j = 0 := by
    filter_upwards [hfac, Φ.isOpen_target.mem_nhds (zero_mem_target Φ h0),
      hT.eventually (hU.mem_nhds hyU), hT.eventually havoid] with z hz hzT hzU hzav hz0
    rw [← hz] at hz0
    obtain ⟨hdom, hback⟩ := flatInverse_mem Φ hzT hsrc
    set y' := (complexChartAt (n := n) y).val.symm (Φ.invFun z)
    have hsup : y' ∈ D.support :=
      (SNCDivisorLocalGenerator.mem_support_iff_generator_eq_zero D
        (SGPT.PSH.IdealRestriction.holomorphicAt_of_mdifferentiableOn hU hgd hzU)
        (hgen y' hzU)).mpr hz0
    obtain ⟨F, hF⟩ := mem_iUnion.mp (hsupp hsup)
    obtain ⟨hFE, hyF⟩ := mem_iUnion.mp hF
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hFE
    have hyi : y ∈ E.get i := by
      by_contra h
      exact hzav i h hyF
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (hcard i hyi)
    have hsub := (hflat i hyi hdom.1 hdom.2).mp hyF
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, i, hyi, hj⟩, ?_⟩
    have hb := congrArg (fun w : ComplexModel n => w j) hback
    simp only at hb
    have h1 := hsub j (by rw [hj]; exact Finset.mem_singleton_self j)
    erw [hb] at h1
    exact h1
  have haM : ∀ j ∉ M, a j = 0 := by
    intro j hj
    by_contra hne
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hzeroM
    obtain ⟨z, hz, hzj, hzi⟩ := HironakaDivisorResidualUnit.exists_coordinate_unit_point j hε
    obtain ⟨j', hj'M, hj'⟩ := hball z hz (by
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hzj]; exact zero_pow hne), mul_zero])
    by_cases hjj : j' = j
    · exact hj (hjj ▸ hj'M)
    · exact hzi j' hjj hj'
  refine ⟨ℓ, hℓ, span_flatCoord_eq_maximalIdeal Φ h0 hsrc, M, H, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, g, hg, hgen y hyU, fun c hc => ?_⟩
  · obtain ⟨i, -, -, hHi⟩ := hHM j hj
    rw [hHi]
    exact isComplexAnalyticSubset_of_isSNCDivisor hE i
  · obtain ⟨i, hyi, hSi, hHi⟩ := hHM j hj
    rw [hHi]
    refine ⟨hℓ j, ?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y' hy' hy'E
    have hsub := (hflat i hyi hy'.1 hy'.2).mp hy'E
    rw [hSi] at hsub
    exact hsub j (Finset.mem_singleton_self j)
  · obtain ⟨i, hyi, hSi, hHi⟩ := hHM j hj
    rw [hHi]
    intro h hh hhv
    refine flatCoord_generates_vanishingIdeal Φ h0 hsrc (fun hz hzN => ?_) h hh hhv
    rw [← hSi]
    exact hflat i hyi hz hzN
  · -- divisors of the generator
    let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
      ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
    have hunit : IsUnit (HolGerm.mk H₀ hH₀) :=
      (HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa [HolGerm.eval_mk] using hH₀0)
    have hdvd : flatGermEquiv Φ h0 c ∣ ∏ j, coordinateGerm j ^ a j := by
      have h1 := map_dvd (flatGermEquiv Φ h0) hc
      rw [hθg] at h1
      exact (hunit.dvd_mul_left).mp h1
    obtain ⟨α, hαa, hassoc⟩ :=
      HolomorphicCoordinateFactorization.exists_associated_prod_pow_of_dvd_prod_pow
        (fun j => coordinateGerm j) a
        (fun j => HolomorphicCoordinatePrime.prime_coordinate_germ j) hdvd
    obtain ⟨v, hv⟩ := hassoc.symm
    refine ⟨(Units.map (flatGermEquiv Φ h0).symm.toMonoidHom v), α,
      fun j hj => Nat.eq_zero_of_le_zero ((hαa j).trans (haM j hj).le), ?_⟩
    apply (flatGermEquiv Φ h0).injective
    rw [map_mul, map_prod, ← hv]
    have h1 : (flatGermEquiv Φ h0) ((Units.map (flatGermEquiv Φ h0).symm.toMonoidHom v :
        (NativeHolGerm n Y y)ˣ) : NativeHolGerm n Y y) = v := by simp
    rw [h1, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow]
    exact congrArg (· ^ α j) (flatGermEquiv_flatCoord Φ h0 hsrc j).symm

end Monomial

end SGPT.Okounkov.OF13
