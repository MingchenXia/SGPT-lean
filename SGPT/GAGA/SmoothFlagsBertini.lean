import SGPT.GAGA.SmoothFlagsSubmanifold
import SGPT.Trace.BertiniSmooth

/-!
# Smooth flags on compact complex manifolds embedded in projective space


Let `M` be a compact connected complex manifold of dimension `n` and `p : M → ℙᴺ` an injective
holomorphic map. The smooth flag `M = Y₀ ⊋ Y₁ ⊋ ⋯ ⊋ Yₙ = {pt}` of `def:Okounkov:L170`
(`SGPT.Okounkov.IsSmoothFlag`) is built by repeated hyperplane sections (Bertini):

* `eq_of_member_eq_empty`: if `p(M)` misses a hyperplane `H`, then `p` is constant (the
  degree-zero ratios `Zₘ/ℓ(Z)` are holomorphic functions on the compact connected `M`), adapting
  the `member_nonempty` to maps that are not assumed nondegenerate;
* **`exists_isClosedConnectedSubmanifold_pred`** (`k ≥ 1`): by the analytic generic
  smoothness (`SGPT.Trace.Bertini.interior_singularMemberSet`: the hyperplanes with a singular
  member form a set with empty interior) some member `p⁻¹(H)` is a smooth hypersurface; it is
  nonempty because `p` is injective and `M` has two points; a connected component of it is a
  closed connected submanifold of dimension `k - 1`;
* `exists_subset_isClosedConnectedSubmanifold`: the same inside a closed connected submanifold
  `W ⊆ M` of dimension `k ≥ 1` (Bertini on the manifold `↥W` with the map `p ∘ val`, then
  `SGPT.GAGA.SmoothFlags.isClosedConnectedSubmanifold_image_val`);
* `exists_partialFlag_extend`: a partial flag `Y₀ = M ⊇ ⋯ ⊇ Yᵢ` extends to a longer one;
* **`exists_isSmoothFlag_of_injective`**: `M` carries a smooth flag;
* `exists_isSmoothFlag_one_eq`: every closed connected submanifold of dimension `n - 1` is the
  first member `Y₁` of a smooth flag.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.SmoothFlags

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini

/-- `ℙ⁰` is a point. -/
theorem subsingleton_complexProjectiveSpace_zero : Subsingleton (ComplexProjectiveSpace 0) := by
  refine ⟨fun z w => ?_⟩
  have hsrc : ∀ u : ComplexProjectiveSpace 0, u ∈ (affineChart 0).source := fun u => by
    have h := mem_affineChart_chartIndex u
    have h0 : chartIndex u = 0 := Fin.ext (Nat.lt_one_iff.mp (chartIndex u).isLt)
    rwa [h0] at h
  refine (affineChart 0).injOn (hsrc z) (hsrc w) ?_
  ext i
  exact i.elim0

section Member

variable {N k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M] (p : M → ComplexProjectiveSpace N)

/-- If `p(M)` misses the hyperplane `H_ℓ` (`p⁻¹(H_ℓ) = ∅`), `M` compact connected, then `p` is
constant: the degree-zero ratios `Zₘ(p x)/⟨ℓ, Z(p x)⟩` are holomorphic, hence constant. -/
theorem eq_of_member_eq_empty [CompactSpace M] [ConnectedSpace M]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ p) {l : HyperplaneSpace N}
    (hl : member p l = ∅) (x y : M) : p y = p x := by
  have hoff : ∀ x, p x ∉ hyperplane l := fun x hx => by
    have : x ∈ member p l := hx
    rw [hl] at this
    exact this
  have hpair : ∀ y, pairing l.rep (p y).rep ≠ 0 := fun y h => by
    apply hoff y
    have := mem_hyperplane_mk_iff l (p y).rep_ne_zero
    rw [mk_rep] at this
    exact this.mpr h
  have hconst : ∀ y m, (p y).rep m / pairing l.rep (p y).rep =
      (p x).rep m / pairing l.rep (p x).rep := fun y m =>
    MDifferentiable.apply_eq_of_compactSpace (mdifferentiable_rep_div_pairing p hp hoff m) y x
  have hy : (p y).rep = (pairing l.rep (p y).rep / pairing l.rep (p x).rep) • (p x).rep := by
    funext m
    have := hconst y m
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hpair y, hpair x] at this ⊢
    linear_combination this
  have hc : pairing l.rep (p y).rep / pairing l.rep (p x).rep ≠ 0 :=
    div_ne_zero (hpair y) (hpair x)
  rw [← mk_rep (p y), ← mk_rep (p x)]
  exact (mk_eq_mk_iff _ _).mpr ⟨_, hy.symm⟩

/-- **One Bertini step.** On a compact connected complex manifold `M` of dimension `k ≥ 1` with an
injective holomorphic map `p : M → ℙᴺ`, some connected component of a smooth member `p⁻¹(H)` is a
closed connected submanifold of dimension `k - 1`. -/
theorem exists_isClosedConnectedSubmanifold_pred [CompactSpace M] [ConnectedSpace M] (hk : 1 ≤ k)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hinj : Function.Injective p) : ∃ C : Set M, IsClosedConnectedSubmanifold k C (k - 1) := by
  obtain ⟨a, b, hab⟩ := exists_ne_of_one_le hk (W := M)
  have hN : 1 ≤ N := by
    by_contra h
    obtain rfl : N = 0 := by omega
    exact hab (hinj (subsingleton_complexProjectiveSpace_zero.elim _ _))
  have hex : ∃ l, IsSmoothHypersurfaceMember k p l := by
    by_contra h
    push Not at h
    have huniv : singularMemberSet k p = univ := eq_univ_of_forall h
    have hint := interior_singularMemberSet p hp hN
    rw [huniv, interior_univ] at hint
    exact univ_nonempty.ne_empty hint
  obtain ⟨l, hl⟩ := hex
  have hne : (member p l).Nonempty := by
    by_contra hne
    exact hab (hinj (eq_of_member_eq_empty p hp (not_nonempty_iff_eq_empty.mp hne) b a))
  obtain ⟨x, hx⟩ := hne
  exact ⟨_, isClosedConnectedSubmanifold_connectedComponentIn
    (isClosed_member p hp.continuous l) (fun y hy => regularAtDim_member p hp hl hy) hx⟩

end Member

section Flag

variable {N n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] (p : M → ComplexProjectiveSpace N)

/-- **One Bertini step inside a submanifold.** If `W ⊆ M` is a closed connected submanifold of
dimension `k ≥ 1` and `p` is an injective holomorphic map to `ℙᴺ`, then `W` contains a closed
connected submanifold of `M` of dimension `k - 1`. -/
theorem exists_subset_isClosedConnectedSubmanifold
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hinj : Function.Injective p) {W : Set M} {k : ℕ} (hW : IsClosedConnectedSubmanifold n W k)
    (hk : 1 ≤ k) : ∃ C ⊆ W, IsClosedConnectedSubmanifold n C (k - 1) := by
  have hkn := SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW
  let := SubmanifoldChartedSpace.chartedSpace hkn hW.2.2
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hkn hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have hq : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel N) ∞ (p ∘ Subtype.val : W → _) :=
    hp.comp (SubmanifoldChartedSpace.contMDiff_val hkn hW.2.2)
  obtain ⟨C, hC⟩ := exists_isClosedConnectedSubmanifold_pred (p ∘ Subtype.val) hk hq
    (hinj.comp Subtype.val_injective)
  exact ⟨Subtype.val '' C, Subtype.coe_image_subset W C,
    isClosedConnectedSubmanifold_image_val hkn hW.1 hW.2.2 hC⟩

omit [IsComplexManifold n M] [CompactSpace M] in
/-- `M` itself is a closed connected submanifold of dimension `n`. -/
theorem isClosedConnectedSubmanifold_univ [ConnectedSpace M] :
    IsClosedConnectedSubmanifold n (univ : Set M) n :=
  ⟨isClosed_univ, isConnected_univ, fun x _ => AnalyticIrreducibleComponents.regularAtDim_univ x⟩

/-- **Extension of a partial flag.** A chain `Y₀ = M ⊇ Y₁ ⊇ ⋯` whose first `i + 1` levels are
closed connected submanifolds of dimensions `n, n - 1, …, n - i` extends (keeping these levels) to
one whose first `i + r + 1` levels are, for `i + r ≤ n`. -/
theorem exists_partialFlag_extend
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hinj : Function.Injective p) {i : ℕ} {Y : ℕ → Set M} (hY0 : Y 0 = univ)
    (hYanti : Antitone Y) (hY : ∀ j ≤ i, IsClosedConnectedSubmanifold n (Y j) (n - j)) :
    ∀ r, i + r ≤ n → ∃ Y' : ℕ → Set M, Y' 0 = univ ∧ Antitone Y' ∧
      (∀ j ≤ i + r, IsClosedConnectedSubmanifold n (Y' j) (n - j)) ∧ ∀ j ≤ i, Y' j = Y j := by
  intro r
  induction r with
  | zero => exact fun _ => ⟨Y, hY0, hYanti, hY, fun _ _ => rfl⟩
  | succ r ih =>
    intro hir
    obtain ⟨Y', h0, hanti, hY', hagree⟩ := ih (by omega)
    obtain ⟨C, hCY, hC⟩ :=
      exists_subset_isClosedConnectedSubmanifold p hp hinj (hY' (i + r) le_rfl) (by omega)
    classical
    refine ⟨fun j => if j ≤ i + r then Y' j else C, by simp [h0], ?_, fun j hj => ?_,
      fun j hj => ?_⟩
    · intro a b hab
      dsimp only
      by_cases hb : b ≤ i + r
      · rw [if_pos hb, if_pos (hab.trans hb)]
        exact hanti hab
      · rw [if_neg hb]
        by_cases ha : a ≤ i + r
        · rw [if_pos ha]
          exact hCY.trans (hanti ha)
        · rw [if_neg ha]
    · dsimp only
      by_cases hji : j ≤ i + r
      · rw [if_pos hji]
        exact hY' j hji
      · rw [if_neg hji]
        obtain rfl : j = i + r + 1 := by omega
        have h : n - (i + r) - 1 = n - (i + r + 1) := by omega
        rw [← h]
        exact hC
    · dsimp only
      rw [if_pos (by omega)]
      exact hagree j hj

/-- **Smooth flags exist on a compact connected complex manifold with an injective holomorphic
map to projective space** (`def:Okounkov:L170`): there is `M = Y₀ ⊇ Y₁ ⊇ ⋯ ⊇ Yₙ` with `Yᵢ` a closed
connected complex submanifold of dimension `n - i` (`SGPT.Okounkov.IsSmoothFlag`). -/
theorem exists_isSmoothFlag_of_injective [ConnectedSpace M]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hinj : Function.Injective p) : ∃ Y : Fin (n + 1) → Set M, SGPT.Okounkov.IsSmoothFlag Y := by
  obtain ⟨Y, hY0, hYanti, hY, -⟩ := exists_partialFlag_extend p hp hinj (i := 0)
    (Y := fun _ => univ) rfl (fun _ _ _ => le_rfl) (fun j hj => by
      obtain rfl : j = 0 := by omega
      simpa using isClosedConnectedSubmanifold_univ (M := M)) n (by omega)
  exact ⟨fun j => Y j, hY0, fun a b hab => hYanti hab, fun j => hY j (by omega)⟩

/-- **A smooth connected hypersurface is the first member of a smooth flag** (the step "we can
always find a flag with `E` being the first component" of the proof of `cor:numin`, for `E` a
closed connected submanifold of dimension `n - 1`). -/
theorem exists_isSmoothFlag_one_eq [ConnectedSpace M]
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hinj : Function.Injective p) (hn : 1 ≤ n) {W : Set M}
    (hW : IsClosedConnectedSubmanifold n W (n - 1)) :
    ∃ Y : Fin (n + 1) → Set M, SGPT.Okounkov.IsSmoothFlag Y ∧ Y ⟨1, by omega⟩ = W := by
  classical
  obtain ⟨Y, hY0, hYanti, hY, hagree⟩ := exists_partialFlag_extend p hp hinj (i := 1)
    (Y := fun j => if j = 0 then univ else W) (by simp) (fun a b hab => by
      dsimp only
      by_cases ha : a = 0
      · rw [if_pos ha]
        exact subset_univ _
      · rw [if_neg ha, if_neg (by omega)]) (fun j hj => by
      by_cases hj0 : j = 0
      · rw [if_pos hj0, hj0]
        simpa using isClosedConnectedSubmanifold_univ (M := M)
      · rw [if_neg hj0]
        obtain rfl : j = 1 := by omega
        exact hW) (n - 1) (by omega)
  refine ⟨fun j => Y j, ⟨hY0, fun a b hab => hYanti hab, fun j => hY j (by omega)⟩, ?_⟩
  show Y 1 = W
  rw [hagree 1 le_rfl]
  simp

end Flag

end SGPT.GAGA.SmoothFlags
