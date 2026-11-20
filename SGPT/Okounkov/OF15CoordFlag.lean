import SGPT.Okounkov.OF15SncTower
import SGPT.Okounkov.OF6PrefixCentres
import SGPT.Okounkov.FlagValuationPrefixIdeals
import SGPT.Okounkov.OF9ModelFlagUniqueness
import SGPT.Foundations.Analysis.Pending.BoundaryCount
import SGPT.Foundations.Analysis.Pending.HironakaEmbeddedResolution
import SGPT.Foundations.Analysis.Pending.HironakaG8MemberLoci
import SGPT.Foundations.Analysis.Pending.CodimOneSupport

/-!
# Smooth flags cut out by the members of a normal crossings divisor

Source: chapter *The theory of Okounkov bodies*, `rmk:valcurr` (a resolution `π : Y → X` with a
**smooth flag** `Y•` — `def:Okounkov:L170`: connected closed submanifolds `Yᵢ` of dimension
`n - i` — such that `ν = ν_{Y•} g`).

Let `E` be a simple normal crossings divisor on a connected complex manifold `Y` of dimension `n`,
`y ∈ Y`, `Φ` an adapted chart of `E` at `y` with flat coordinates `ℓ₁, …, ℓₙ` such that each
coordinate hyperplane `{ℓⱼ = 0}` is the member `E (idx j)` near `y`, and `σ` a permutation.

* `sncFlag E idx σ y`: `Y_k` = the connected component through `y` of
  `E (idx σ(0)) ∩ ⋯ ∩ E (idx σ(k-1))`;
* `isSmoothFlag_sncFlag`: it is a smooth flag (every intersection of members of `E` is a closed
  submanifold, of codimension the number of members at each of its points);
* `flatCoord_mem_vanishingIdeal_sncFlag_iff`: `ℓ_{σ(i)}` vanishes on `Y_k` near `y` iff `i < k`;
* **`isUnitUpperTriangular_sncFlag_matrix`**: the matrix of the flag valuations
  `ν_{Y•}(ℓ_{σ(i)})` is unit upper triangular. Proof: the prefix criterion
  (`originalFlagGermVector_prefix_pos_iff`) gives an upper triangular matrix with positive diagonal;
  on the Noetherian germ ring the coordinate ideals form a chain of local equations, and the flag
  valuation is surjective on meromorphic germs, which forces a unit diagonal
  (lane OF6, `LocalEquationChain.diag_eq_one_of_surjective`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF15

open Set Filter Metric IsLocalRing
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.NormalCrossings SGPT.Foundations.Analysis.Pending.BoundaryCount
open HironakaHolomorphicJetMonomialSpan HolomorphicGermCoordinateDerivation BlowupFlatCoordinates
open SGPT.Okounkov SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr SGPT.Okounkov.OF13
open SGPT.NAPotential.FSPos (germDeriv germDeriv_zero germDeriv_add germDeriv_mul)
open scoped Topology Manifold

variable {n : ℕ}

/-! ### Coordinate germs -/

section Germs

/-- In a holomorphic coordinate system of `𝒪_{ℂⁿ,0}`, `tⱼ ∉ (t_s)` for `j ∉ s`. -/
theorem notMem_span_image_of_coordinates (t : Fin n → HolGerm (ComplexModel n))
    (ht : Ideal.span (Set.range t) = maximalIdeal (HolGerm (ComplexModel n))) (s : Set (Fin n))
    {j : Fin n} (hj : j ∉ s) : t j ∉ Ideal.span (t '' s) := by
  classical
  obtain ⟨v, hv⟩ := dualVectors_of_span_eq t ht
  have hres : ∀ k, HolGerm.eval (t k) = 0 := fun k => by
    rw [← HolGerm.mem_maximalIdeal_iff, ← ht]
    exact Ideal.subset_span ⟨k, rfl⟩
  intro hmem
  have key : ∀ a ∈ Ideal.span (t '' s), HolGerm.eval a = 0 ∧ germDeriv (v j) a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨k, hk, rfl⟩ := ha
        refine ⟨hres k, ?_⟩
        rw [hv j k, if_neg]
        rintro rfl
        exact hj hk
    | zero => simp [germDeriv_zero]
    | add a b _ _ ha hb => simp [map_add, germDeriv_add, ha.1, hb.1, ha.2, hb.2]
    | smul r a _ ha =>
        rw [smul_eq_mul, map_mul, germDeriv_mul, ha.1, ha.2]
        simp
  have h := (key _ hmem).2
  rw [hv j j, if_pos rfl] at h
  exact one_ne_zero h

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {y : Y}
  (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y))
  (hsrc : Φ.source ⊆ (complexChartAt (n := n) y).val.target)
  (h0 : Φ.toFun ((complexChartAt (n := n) y).val y) = 0)

include hsrc h0 in
/-- The flat coordinate germs, read in the preferred chart, generate the maximal ideal. -/
theorem span_chartEquiv_flatGerm :
    Ideal.span (Set.range fun j => NativeHolGerm.chartEquiv y (flatGerm Φ j)) =
      maximalIdeal (HolGerm (ComplexModel n)) := by
  have h := congrArg (Ideal.map (NativeHolGerm.chartEquiv (n := n) y))
    (span_flatCoord_eq_maximalIdeal Φ h0 hsrc)
  rw [Ideal.map_span, IsLocalRing.map_ringEquiv_maximalIdeal, ← Set.range_comp] at h
  exact h

theorem map_chartEquiv_span_flatGerm (s : Set (Fin n)) :
    Ideal.map (NativeHolGerm.chartEquiv (n := n) y) (Ideal.span (flatGerm Φ '' s)) =
      Ideal.span ((fun j => NativeHolGerm.chartEquiv y (flatGerm Φ j)) '' s) := by
  rw [Ideal.map_span, ← Set.image_comp]
  rfl

include hsrc h0 in
/-- `ℓⱼ ∉ (ℓ_s)` for `j ∉ s`. -/
theorem flatGerm_notMem_span (s : Set (Fin n)) {j : Fin n} (hj : j ∉ s) :
    flatGerm Φ j ∉ Ideal.span (flatGerm Φ '' s) := by
  intro h
  have h1 := Ideal.mem_map_of_mem (NativeHolGerm.chartEquiv (n := n) y) h
  rw [map_chartEquiv_span_flatGerm] at h1
  exact notMem_span_image_of_coordinates _ (span_chartEquiv_flatGerm Φ hsrc h0) s hj h1

include hsrc h0 in
theorem flatGerm_ne_zero (j : Fin n) : flatGerm Φ j ≠ 0 := by
  intro h
  apply flatGerm_notMem_span Φ hsrc h0 ∅ (Set.notMem_empty j)
  rw [h]
  exact Ideal.zero_mem _

include hsrc h0 in
/-- The coordinate ideals `(ℓ_s)` are prime. -/
theorem isPrime_span_flatGerm (s : Set (Fin n)) : (Ideal.span (flatGerm Φ '' s)).IsPrime := by
  have hp := isPrime_span_image_of_span_eq_maximalIdeal _ (span_chartEquiv_flatGerm Φ hsrc h0) s
  have h := Ideal.map_isPrime_of_equiv (NativeHolGerm.chartEquiv (n := n) y).symm
    (I := Ideal.span ((fun j => NativeHolGerm.chartEquiv y (flatGerm Φ j)) '' s))
  rw [← map_chartEquiv_span_flatGerm] at h
  have hback :
      Ideal.map (NativeHolGerm.chartEquiv (n := n) y).symm.toRingHom
        (Ideal.map (NativeHolGerm.chartEquiv (n := n) y).toRingHom
          (Ideal.span (flatGerm Φ '' s))) = Ideal.span (flatGerm Φ '' s) := by
    simpa only [RingEquiv.toRingHom_eq_coe] using
      (Ideal.map_of_equiv (I := Ideal.span (flatGerm Φ '' s))
        (NativeHolGerm.chartEquiv (n := n) y))
  exact hback ▸ h

end Germs

/-! ### Connected components of closed sets -/

theorem isClosed_connectedComponentIn {α : Type*} [TopologicalSpace α] {F : Set α}
    (hF : IsClosed F) (x : α) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · refine closure_subset_iff_isClosed.mp ?_
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (hF.closure_subset_iff.mpr (connectedComponentIn_subset F x))
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-! ### The flag -/

section Flag

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **The flag of members**: `Y_k` is the connected component through `y` of the intersection of
the members `E (idx σ(0)), …, E (idx σ(k-1))`. -/
def sncFlag (E : List (Set Y)) (idx : Fin n → Fin E.length) (σ : Equiv.Perm (Fin n)) (y : Y) :
    Fin (n + 1) → Set Y :=
  fun k => connectedComponentIn (memberInter E ((OF11.prefixSet σ k).image idx)) y

theorem memberInter_anti (E : List (Set Y)) {S S' : Finset (Fin E.length)} (h : S ⊆ S') :
    memberInter E S' ⊆ memberInter E S :=
  fun _ hw i hi => hw i (h hi)

theorem memberInter_empty (E : List (Set Y)) : memberInter E ∅ = univ := by
  ext w
  simp [memberInter]

open Classical in
/-- **An intersection of members is regular of the expected dimension** at each of its points:
codimension = number of members (the members through a point are distinct coordinate hyperplanes
of one coordinate system). -/
theorem regularAtDim_memberInter {E : List (Set Y)} (hE : IsSNCDivisor n E)
    (T : Finset (Fin E.length)) {x : Y} (hx : x ∈ memberInter E T) :
    RegularAtDim (n := n) (memberInter E T) x (n - T.card) := by
  obtain ⟨S, ⟨Ψ, hΨt, hΨ0, hΨA⟩, hcard, hinj⟩ := hE.2 x
  have hflat : ∀ {w : Y}, w ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val w ∈ Ψ.source →
        (w ∈ memberInter E T ↔
          Ψ.toFun ((complexChartAt (n := n) x).val w) ∈ coordSubspace (T.biUnion S)) := by
    intro w hw hwΨ
    change (∀ i ∈ T, w ∈ E.get i) ↔ _
    rw [mem_coordSubspace_biUnion]
    exact forall₂_congr fun i hi => hΨA i (hx i hi) hw hwΨ
  have hc : (T.biUnion S).card = T.card := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl fun i hi => hcard i (hx i hi)]
      simp
    · intro i hi i' hi' hii'
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hcard i (hx i hi))
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (hcard i' (hx i' hi'))
      change Disjoint (S i) (S i')
      rw [ha, hb, Finset.disjoint_singleton]
      intro hab
      apply hii'
      apply hinj (hx i hi) (hx i' hi')
      rw [ha, hb, hab]
  have h := HironakaG8MemberLoci.regularAtDim_of_flat_coordSubspace Ψ hΨt hΨ0 hflat
  rwa [hc] at h

variable (E : List (Set Y)) (idx : Fin n → Fin E.length) (σ : Equiv.Perm (Fin n)) (y : Y)

theorem card_image_prefixSet (hidx : Function.Injective idx) (k : ℕ) :
    ((OF11.prefixSet σ k).image idx).card = min n k := by
  rw [Finset.card_image_of_injective _ hidx, OF11.card_prefixSet]

theorem mem_memberInter_of_forall (hy : ∀ j, y ∈ E.get (idx j)) (T : Finset (Fin n)) :
    y ∈ memberInter E (T.image idx) := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
  exact hy j

/-- **The flag of members is a smooth flag** (`def:Okounkov:L170`). -/
theorem isSmoothFlag_sncFlag [ConnectedSpace Y] (hn : 0 < n) (hE : IsSNCDivisor n E)
    (hidx : Function.Injective idx) (hy : ∀ j, y ∈ E.get (idx j)) :
    IsSmoothFlag (sncFlag E idx σ y) := by
  refine ⟨?_, ?_, fun k => ⟨?_, ?_, fun x hx => ?_⟩⟩
  · change connectedComponentIn (memberInter E ((OF11.prefixSet σ 0).image idx)) y = univ
    rw [OF11.prefixSet_zero, Finset.image_empty, memberInter_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
  · intro a b hab
    exact connectedComponentIn_mono y (memberInter_anti E (Finset.image_subset_image
      (OF11.prefixSet_mono σ (show (a : ℕ) ≤ b from hab))))
  · exact isClosed_connectedComponentIn (isClosed_memberInter hE.1 _) y
  · exact isConnected_connectedComponentIn_iff.mpr (mem_memberInter_of_forall E idx y hy _)
  · have hxM := connectedComponentIn_subset _ y hx
    have hreg := regularAtDim_memberInter hE _ hxM
    rw [card_image_prefixSet E idx σ hidx, min_eq_right (Nat.lt_succ_iff.mp k.2)] at hreg
    exact CodimOneSupport.regularAtDim_of_eventually_mem_iff
      ((HironakaEmbeddedResolution.eventually_mem_connectedComponentIn_iff
        (isClosedSubmanifold_memberInter hn hE _) hx).mono fun _ h => h.symm) hreg

/-- Near `y`, the flag member `Y_k` is the intersection of its members. -/
theorem eventually_mem_sncFlag_iff (hn : 0 < n) (hE : IsSNCDivisor n E)
    (hy : ∀ j, y ∈ E.get (idx j)) (k : Fin (n + 1)) :
    ∀ᶠ w in 𝓝 y, w ∈ sncFlag E idx σ y k ↔
      w ∈ memberInter E ((OF11.prefixSet σ k).image idx) :=
  HironakaEmbeddedResolution.eventually_mem_connectedComponentIn_iff
    (isClosedSubmanifold_memberInter hn hE _)
    (mem_connectedComponentIn (mem_memberInter_of_forall E idx y hy _))

variable {E idx y}

/-- In the flat coordinates of an adapted chart whose coordinate hyperplanes are the members
`E (idx j)`, an intersection of members is a coordinate subspace. -/
theorem mem_memberInter_image_iff {S : Fin E.length → Finset (Fin n)}
    {Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)}
    (hΦ : IsAdaptedChart y S Φ) (hidx : ∀ j, y ∈ E.get (idx j) ∧ S (idx j) = {j})
    (J : Finset (Fin n)) {w : Y} (hw : w ∈ flatDomain Φ) :
    w ∈ memberInter E (J.image idx) ↔
      Φ.toFun ((complexChartAt (n := n) y).val w) ∈ coordSubspace J := by
  classical
  change (∀ i ∈ J.image idx, w ∈ E.get i) ↔ _
  simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h j hj
    have h1 := (hΦ.2.2.1 (idx j) (hidx j).1 hw.1 hw.2).mp (h j hj)
    rw [(hidx j).2] at h1
    exact h1 j (Finset.mem_singleton_self j)
  · intro h j hj
    refine (hΦ.2.2.1 (idx j) (hidx j).1 hw.1 hw.2).mpr ?_
    rw [(hidx j).2]
    intro l hl
    rw [Finset.mem_singleton.mp hl]
    exact h j hj

/-- **`ℓ_{σ(i)}` vanishes on `Y_k` near `y` iff `i < k`.** -/
theorem flatCoord_mem_vanishingIdeal_sncFlag_iff (hn : 0 < n) (hE : IsSNCDivisor n E)
    {S : Fin E.length → Finset (Fin n)}
    {Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)}
    (hΦ : IsAdaptedChart y S Φ) (hidx : ∀ j, y ∈ E.get (idx j) ∧ S (idx j) = {j})
    (k : Fin (n + 1)) (i : Fin n) :
    (vanishingIdeal (n := n) (sncFlag E idx σ y k)).mem y (flatCoord Φ (σ i)) ↔
      (i : ℕ) < k := by
  have hy : ∀ j, y ∈ E.get (idx j) := fun j => (hidx j).1
  have hev := eventually_mem_sncFlag_iff E idx σ y hn hE hy k
  constructor
  · rintro ⟨-, hvan⟩
    by_contra hik
    have hnot : σ i ∉ OF11.prefixSet σ k := by
      rw [OF11.mem_prefixSet, σ.symm_apply_apply]
      exact hik
    -- the curve `t ↦ (Φ ∘ chart)⁻¹ (t eᵢ)`
    let e : ComplexModel n := EuclideanSpace.single (σ i) (1 : ℂ)
    let γ : ℂ → Y := fun t => (complexChartAt (n := n) y).val.symm (Φ.invFun (t • e))
    have hcont : Tendsto (fun t : ℂ => t • e) (𝓝 0) (𝓝 0) := by
      have he : Continuous (fun t : ℂ => t • e) := continuous_id.smul continuous_const
      simpa only [zero_smul] using he.tendsto 0
    have hT : Tendsto γ (𝓝 0) (𝓝 y) := by
      have h := tendsto_flatInverse Φ (mem_flatDomain_self Φ)
      rw [show Φ.toFun ((chartAt (ComplexModel n) y) y) = 0 from hΦ.2.1] at h
      exact h.comp hcont
    have htarget : ∀ᶠ t in 𝓝 (0 : ℂ), t • e ∈ Φ.target :=
      hcont.eventually (Φ.isOpen_target.mem_nhds (zero_mem_target Φ hΦ.2.1))
    have hcoord : ∀ t : ℂ, (t • e) (σ i) = t := fun t => by
      simp [e]
    have hzero : ∀ᶠ t in 𝓝 (0 : ℂ), t = 0 := by
      filter_upwards [htarget, hT.eventually hev, hT.eventually hvan] with t ht hevt hvant
      obtain ⟨hdom, hback⟩ := flatInverse_mem Φ ht hΦ.1
      have hmem : γ t ∈ memberInter E ((OF11.prefixSet σ k).image idx) := by
        refine (mem_memberInter_image_iff hΦ hidx _ hdom).mpr ?_
        erw [hback]
        intro l hl
        have hl' : l ≠ σ i := fun h => hnot (h ▸ hl)
        simp [e, hl']
      have h1 := hvant (hevt.mpr hmem)
      change Φ.toFun ((chartAt (ComplexModel n) y) (γ t)) (σ i) = 0 at h1
      erw [hback] at h1
      rwa [hcoord] at h1
    obtain ⟨t, ht0, htne⟩ := ((hzero.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {t : ℂ | t ≠ 0} ∈ 𝓝[≠] (0 : ℂ))).exists
    exact htne ht0
  · intro hik
    refine ⟨holomorphicAt_flatCoord Φ (σ i) (mem_flatDomain_self Φ), ?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ), hev] with w hw hwF
      hwk
    have h1 := (mem_memberInter_image_iff hΦ hidx _ hw).mp (hwF.mp hwk)
    apply h1 (σ i)
    rw [OF11.mem_prefixSet, σ.symm_apply_apply]
    exact hik

end Flag

/-! ### The matrix of the flag valuations of the coordinates -/

section Matrix

variable {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] [CompactSpace Y] [ConnectedSpace Y]
  {E : List (Set Y)} {idx : Fin n → Fin E.length} {y : Y}
  {S : Fin E.length → Finset (Fin n)}
  {Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) y).val y)}

/-- The chain of coordinate ideals `(ℓ_{σ(0)}, …, ℓ_{σ(i-1)})` with local equations `ℓ_{σ(i)}` in
the germ ring at `y`. -/
def flatChain (hΦ : IsAdaptedChart y S Φ) (σ : Equiv.Perm (Fin n)) :
    LocalEquationChain (NativeHolGerm n Y y) n where
  P i := Ideal.span (flatGerm Φ '' ↑(OF11.prefixSet σ i))
  T i := if h : i < n then flatGerm Φ (σ ⟨i, h⟩) else 0
  isPrime i := isPrime_span_flatGerm Φ hΦ.1 hΦ.2.1 _
  succ_eq i hi := by
    simp only [dif_pos hi]
    rw [OF11.prefixSet_succ σ hi, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert,
      sup_comm]
  T_notMem i hi := by
    simp only [dif_pos hi]
    refine flatGerm_notMem_span Φ hΦ.1 hΦ.2.1 _ ?_
    rw [Finset.mem_coe, OF11.mem_prefixSet, σ.symm_apply_apply]
    exact lt_irrefl i

/-- **The flag valuations of the coordinates form a unit upper triangular matrix.** For the flag
of members `Y•` of `E` through `y` in the order `σ` (any Kähler background `ω`), the vectors
`ν_{Y•}(ℓ_{σ(i)})` of the flat coordinates are the rows of a unit upper triangular matrix. -/
theorem isUnitUpperTriangular_sncFlag_matrix (ω : KahlerBackground n Y) (hn : 0 < n)
    (hE : IsSNCDivisor n E) (hΦ : IsAdaptedChart y S Φ)
    (hidx : ∀ j, y ∈ E.get (idx j) ∧ S (idx j) = {j}) (σ : Equiv.Perm (Fin n))
    (hsm : IsSmoothFlag (sncFlag E idx σ y)) (hyL : y ∈ sncFlag E idx σ y (Fin.last n)) :
    IsUnitUpperTriangular (fun i j => (originalFlagGermVector
      (OriginalFlagGeometry.ofOriginal ω (sncFlag E idx σ y) hsm) ⟨y, hyL⟩
      (flatGerm Φ (σ i)) (flatGerm_ne_zero Φ hΦ.1 hΦ.2.1 (σ i)) j : ℤ)) := by
  classical
  set F := OriginalFlagGeometry.ofOriginal ω (sncFlag E idx σ y) hsm
  let x : OriginalFlagGermPoint F := ⟨y, hyL⟩
  let R := NativeHolGerm n Y y
  let K := FractionRing R
  have : IsNoetherianRing R := by
    change IsNoetherianRing (NativeHolGerm n Y y)
    infer_instance
  let C := flatChain hΦ σ
  let vec : Fin n → Fin n → ℕ := fun i => originalFlagGermVector F x (flatGerm Φ (σ i))
    (flatGerm_ne_zero Φ hΦ.1 hΦ.2.1 (σ i))
  let G : Matrix (Fin n) (Fin n) ℤ := fun i j => (vec i j : ℤ)
  let v := originalFlagGermFractionValuation F x
  -- the prefix criterion
  have hpre : ∀ (k : ℕ) (hk : k ≤ n) (i : Fin n),
      (∃ l : Fin k, 0 < vec i (Fin.castLE hk l)) ↔ (i : ℕ) < k := by
    intro k hk i
    have h := originalFlagGermVector_prefix_pos_iff F x k hk (flatCoord Φ (σ i))
      (holomorphicAt_flatCoord Φ (σ i) (mem_flatDomain_self Φ))
      (flatGerm_ne_zero Φ hΦ.1 hΦ.2.1 (σ i))
    exact h.trans (flatCoord_mem_vanishingIdeal_sncFlag_iff σ hn hE hΦ hidx
      ⟨k, Nat.lt_succ_of_le hk⟩ i)
  have hlow : ∀ i j : Fin n, j < i → vec i j = 0 := by
    intro i j hji
    by_contra hne
    have h := (hpre i i.2.le i).mp ⟨⟨j, hji⟩, Nat.pos_of_ne_zero hne⟩
    exact lt_irrefl _ h
  have hdiag : ∀ i : Fin n, 0 < vec i i := by
    intro i
    obtain ⟨l, hl⟩ := (hpre (i + 1) i.2 i).mpr (Nat.lt_succ_self i)
    have hli : Fin.castLE i.2 l = i := by
      apply Fin.ext
      by_contra hne
      have hlt : (l : ℕ) < i := by have := l.2; simp only [Fin.val_castLE] at hne; omega
      rw [hlow i (Fin.castLE i.2 l) hlt] at hl
      exact lt_irrefl _ hl
    rwa [hli] at hl
  have hG : IsPosUpperTriangular G :=
    ⟨fun i => by
      change (0 : ℤ) < (vec i i : ℤ)
      exact_mod_cast hdiag i,
    fun i j hji => by
      change ((vec i j : ℕ) : ℤ) = 0
      rw [hlow i j hji, Nat.cast_zero]⟩
  -- the hypotheses of the diagonal criterion
  have h0 : C.P 0 = ⊥ := by
    change Ideal.span (flatGerm Φ '' ↑(OF11.prefixSet σ 0)) = ⊥
    rw [OF11.prefixSet_zero, Finset.coe_empty, Set.image_empty, Ideal.span_empty]
  have hv : Function.Surjective v := by
    intro b
    induction b using WithTop.recTopCoe with
    | top => exact ⟨0, v.map_zero⟩
    | coe b =>
      obtain ⟨q, -, hq⟩ := originalFlagGermFractionValuation_integer_surjective F x b
      exact ⟨q, hq⟩
  have hnonneg : ∀ a : R, 0 ≤ v (algebraMap R K a) := fun a => by
    calc
      0 ≤ originalFlagGermValuation F x a := originalFlagGermValuation_nonneg F x a
      _ = v (algebraMap R K a) := (originalFlagGermFractionValuation_algebraMap F x a).symm
  have hT : ∀ (i : ℕ) (hi : i < n),
      v (algebraMap R K (C.T i)) = vecValue (G ⟨i, hi⟩) := by
    intro i hi
    let a := flatGerm Φ (σ ⟨i, hi⟩)
    have hTa : C.T i = a := dif_pos hi
    have ha : a ≠ 0 := flatGerm_ne_zero Φ hΦ.1 hΦ.2.1 _
    calc
      v (algebraMap R K (C.T i)) = v (algebraMap R K a) :=
        congrArg (fun t : R => v (algebraMap R K t)) hTa
      _ = originalFlagGermValuation F x a := originalFlagGermFractionValuation_algebraMap F x a
      _ = vecValue (G ⟨i, hi⟩) := originalFlagGermValuation_apply_of_ne_zero F x a ha
  have hunit : ∀ a : R, a ∉ C.P n → v (algebraMap R K a) = 0 := by
    intro a ha
    have hPn : C.P n = maximalIdeal R := by
      change Ideal.span (flatGerm Φ '' ↑(OF11.prefixSet σ n)) = _
      rw [OF11.prefixSet_of_le σ le_rfl, Finset.coe_univ, Set.image_univ]
      exact span_flatCoord_eq_maximalIdeal Φ hΦ.2.1 hΦ.1
    rw [hPn] at ha
    have hu : IsUnit a := by
      by_contra hu
      exact ha ((mem_maximalIdeal a).mpr hu)
    exact (originalFlagGermFractionValuation_algebraMap F x a).trans
      (OF9.originalFlagGermValuation_eq_zero_of_isUnit F x hu)
  have hone : ∀ i, G i i = 1 := fun i =>
    LocalEquationChain.diag_eq_one_of_surjective C K h0 v hv hG hnonneg hT hunit i
  exact ⟨hone, hG.2⟩

end Matrix

end SGPT.Okounkov.OF15
