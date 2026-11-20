import SGPT.Toric.Toric3Flag
import SGPT.Toric.BigToric2Sections

/-!
# The flag valuation of the sections of `O(D)` along a toric flag

Source `chapter_toric_big.tex`, `prop:toricusualOko` and its proof.  Let `σ = σ_v` be a maximal
cone with the ordering `ρ_{l+1} = u_{e(l)}(v)` of its rays, `Y•` the toric flag
(`toricFlag`), and

`Φ : M → ℤ^n,  m ↦ (⟨m - m_σ, u_{ρ_1}⟩, …, ⟨m - m_σ, u_{ρ_n}⟩)`

(`eq:isoMZncanonical`).  A section `s ∈ H⁰(X, O(D))` is `s = f_v e_v` on `U_v` (frame
`e_v = χ^{m_v} s_D`, see `toricSections`); its valuation `ν_{Y•}(s)` is the flag valuation
(`originalFlagGermValuation`, source `subsec:flagvalalgebraic`: successive orders of vanishing
along `Y_i ⊆ Y_{i-1}` and restrictions) of the germ of its coefficient `f_v` at the point
`Y_n = {x_v}`; `e_v` is a local trivialization of `O(D)` near `Y_n`, as in the source.

## Main results

* `toricSectionValuation_latticeCharacter`: `ν_{Y•}(χ^m) = Φ(m)` for `m ∈ M ∩ P_D` (the
  zero divisor of `χ^m` on `U_σ` is `∑_i ⟨m - m_σ, u_{ρ_i}⟩ D_{ρ_i}`);
* `exists_toricSectionValuation_eq`: for a nonzero section `s = ∑_m c_m χ^m`,
  `ν_{Y•}(s) = Φ(m)` for some `m` with `c_m ≠ 0` (the lexicographically first exponent);
* `toricSectionValues_eq`: `ν_{Y•}(H⁰(X, O(D)) ∖ 0) = Φ(M ∩ P_D)`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Okounkov
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology BigOperators Manifold ContDiff

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-! ### Coefficients of sections -/

/-- The coefficient `f_v` of a section `g = s / s_D` of `O(D)` in the frame `e_v` of `U_v`
(`g = f_v(z_v) χ^{m_v}`); `0` if `g` is not a section. -/
def toricSectionCoeff (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ)
    (g : (Fin n → ℂˣ) → ℂ) : ComplexModel n → ℂ :=
  open Classical in if h : g ∈ toricSections D then (h v).choose else 0

theorem differentiable_toricSectionCoeff (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ)
    (g : (Fin n → ℂˣ) → ℂ) : Differentiable ℂ (toricSectionCoeff D v g) := by
  classical
  unfold toricSectionCoeff
  split_ifs with h
  · exact (h v).choose_spec.1
  · exact differentiable_const 0

theorem toricSectionCoeff_spec {D : ToricDivisor γ hs} {g : (Fin n → ℂˣ) → ℂ}
    (hg : g ∈ toricSections D) (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ) :
    g a = toricSectionCoeff D v g (originalPolytopeNativeModelChart γ hs v
      (polytopeToricEmbedding γ hs a)) * latticeCharacter (toricCartierDatum D v) a := by
  classical
  unfold toricSectionCoeff
  rw [dif_pos hg]
  exact (hg v).choose_spec.2 a

/-- The Laurent coefficients `c_m` of a section `g = ∑_m c_m χ^m`. -/
def toricSectionLaurentCoeff (g : (Fin n → ℂˣ) → ℂ) (m : Fin n → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (fun t => g (compactTorusPoint t)) m

/-- `f_v = ∑_{m ∈ M ∩ P_D} c_m z^{⟨m - m_v, u(v)⟩}`. -/
theorem toricSectionCoeff_eq_sum {D : ToricDivisor γ hs} {g : (Fin n → ℂˣ) → ℂ}
    (hg : g ∈ toricSections D) (v : latticePolytopeVertices γ) :
    toricSectionCoeff D v g = fun z => ∑ m ∈ (finite_toricLatticePoints D).toFinset,
      toricSectionLaurentCoeff g m * toricMonomial D v m z := by
  apply toricSectionCoeff_unique D v (differentiable_toricSectionCoeff D v g).continuous
    (continuous_finsetSum _ fun m _ =>
      continuous_const.mul (differentiable_toricMonomial D v m).continuous)
    (toricSectionCoeff_spec hg v)
  intro a
  rw [eq_sum_of_mem_toricSections hg a, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Set.Finite.mem_toFinset] at hm
  rw [latticeCharacter_eq_toricMonomial D hm v a]
  simp only [Pi.mul_apply, toricSectionLaurentCoeff]
  ring

theorem toricSectionLaurentCoeff_eq_zero_of_not_mem {D : ToricDivisor γ hs}
    {g : (Fin n → ℂˣ) → ℂ} (hg : g ∈ toricSections D) {m : Fin n → ℤ}
    (hm : m ∉ toricLatticePoints D) : toricSectionLaurentCoeff g m = 0 :=
  laurentCoeff_eq_zero_of_mem_toricSections hg hm

/-! ### The germ of a section at the flag point -/

/-- The germ at `x_v` of the coefficient `f_v ∘ z_v` of a section in the frame `e_v`. -/
def toricSectionGerm (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ)
    (g : (Fin n → ℂˣ) → ℂ) : NativeHolGerm n (PolytopeToricVariety γ hs) (vertexPoint hs v 0) :=
  NativeHolGerm.mk (fun p => toricSectionCoeff D v g (originalPolytopeNativeModelChart γ hs v p))
    (holomorphicAt_comp_vertexChart v (vertexPoint_mem_source v 0)
      (Eventually.of_forall fun _ => (differentiable_toricSectionCoeff D v g).differentiableAt))

variable (hs) in
/-- Source `prop:toricusualOko`: the flag valuation `ν_{Y•}(s)` of a section `s` of `O(D)` along
the toric flag of `(σ_v, e)`, computed in the local trivialization `e_v` near `Y_n`. -/
def toricSectionValuation (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (D : ToricDivisor γ hs) (g : (Fin n → ℂˣ) → ℂ) : WithTop (Lex (Fin n → ℤ)) :=
  originalFlagGermValuation (toricFlagGeometry (hs := hs) v e) (toricFlagPoint (hs := hs) v e)
    (toricSectionGerm D v g)

variable (hs) in
/-- Source `eq:isoMZncanonical`: `Φ(m) = (⟨m - m_σ, u_{ρ_1}⟩, …, ⟨m - m_σ, u_{ρ_n}⟩)`. -/
def toricFlagLatticeMap (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (D : ToricDivisor γ hs) (m : Fin n → ℤ) : Fin n → ℤ :=
  fun l => intPairing (m - toricCartierDatum D v) (polytopeToricRayGenerator γ hs v (e l))

theorem toricFlagLatticeMap_injective (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (D : ToricDivisor γ hs) : Function.Injective (toricFlagLatticeMap hs v e D) := by
  intro m m' h
  have h' : m - toricCartierDatum D v = m' - toricCartierDatum D v := by
    apply eq_of_intPairing_rayGenerator_eq v
    intro j
    have := congrFun h (e.symm j)
    simpa [toricFlagLatticeMap] using this
  simpa using h'

/-! ### Products of germs -/

theorem nativeHolGerm_mk_prod_pow {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] {x : M} (G : Fin n → M → ℂ)
    (hG : ∀ l, HolomorphicAt n (G l) x) (b : Fin n → ℕ)
    (h : HolomorphicAt n (fun p => ∏ l, G l p ^ b l) x) :
    NativeHolGerm.mk (fun p => ∏ l, G l p ^ b l) h = ∏ l, NativeHolGerm.mk (G l) (hG l) ^ b l := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_finsetProd]
  simp only [SubmonoidClass.coe_pow]
  change ((fun p => ∏ l, G l p ^ b l : M → ℂ) : Germ (𝓝 x) ℂ) = ∏ l, ((G l : M → ℂ) : Germ (𝓝 x) ℂ) ^ b l
  have : (fun p => ∏ l, G l p ^ b l : M → ℂ) = ∏ l, G l ^ b l := by
    funext p; simp [Finset.prod_apply]
  rw [this]
  exact map_prod (Germ.coeRingHom (𝓝 x)) (fun l => G l ^ b l) Finset.univ |>.trans
    (Finset.prod_congr rfl fun l _ => map_pow (Germ.coeRingHom (𝓝 x)) (G l) (b l))

/-! ### Valuations of characters -/

variable (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) (D : ToricDivisor γ hs)

theorem holomorphicAt_toricMonomial_comp (m : Fin n → ℤ) :
    HolomorphicAt n
      (fun p : PolytopeToricVariety γ hs => toricMonomial D v m (originalPolytopeNativeModelChart γ hs v p))
      (vertexPoint hs v 0) :=
  holomorphicAt_comp_vertexChart v (vertexPoint_mem_source v 0)
    (Eventually.of_forall fun _ => (differentiable_toricMonomial D v m).differentiableAt)

/-- The flag vector of the monomial `z^{⟨m - m_v, u(v)⟩}`: `Φ(m)`. -/
theorem originalFlagGermValuation_toricMonomial {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints D) :
    originalFlagGermValuation (toricFlagGeometry (hs := hs) v e) (toricFlagPoint (hs := hs) v e)
      (NativeHolGerm.mk (fun p => toricMonomial D v m (originalPolytopeNativeModelChart γ hs v p))
        (holomorphicAt_toricMonomial_comp v D m)) =
      ((toLex (toricFlagLatticeMap hs v e D m) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
  set F := toricFlagGeometry (hs := hs) v e
  set x := toricFlagPoint (hs := hs) v e
  set G : Fin n → F.carrier → ℂ := fun k p => originalPolytopeNativeModelChart γ hs v p (e k)
  have hG := isAdaptedFlagCoordinates_toricFlag (hs := hs) v e
  set β : Fin n → ℕ := fun l => (intPairing m (polytopeToricRayGenerator γ hs v (e l)) -
    intPairing (toricCartierDatum D v) (polytopeToricRayGenerator γ hs v (e l))).toNat
  obtain ⟨hne, hvec⟩ := originalFlagGermVector_monomial F x G hG β
  set f : F.carrier → ℂ := fun p => toricMonomial D v m (originalPolytopeNativeModelChart γ hs v p)
  have hmono : HolomorphicAt n f x.1 := holomorphicAt_toricMonomial_comp v D m
  have hfun : ∀ p : F.carrier, f p = ∏ l, G l p ^ β l := by
    intro p
    simp only [f, toricMonomial]
    exact (Fintype.prod_equiv e _ _ fun l => rfl).symm
  have hgerm : NativeHolGerm.mk f hmono = ∏ j, NativeHolGerm.mk (G j) (hG.holo j) ^ β j :=
    (NativeHolGerm.mk_eq_mk_iff.mpr (Eventually.of_forall hfun)).trans
      (nativeHolGerm_mk_prod_pow (x := x.1) G hG.holo β (hmono.congr (Eventually.of_forall hfun)))
  change originalFlagGermValuation F x (NativeHolGerm.mk f hmono) = _
  rw [hgerm, originalFlagGermValuation_apply_of_ne_zero F x _ hne]
  congr 1
  change (toLex fun i => (originalFlagGermVector F x _ hne i : ℤ)) = toLex _
  congr 1
  funext l
  rw [hvec]
  have hpos := (mem_toricLatticePoints_iff D m).mp hm v (e l)
  simp only [β, toricFlagLatticeMap, intPairing_sub]
  omega

theorem toricSectionCoeff_latticeCharacter {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints D) :
    toricSectionCoeff D v (fun a => (latticeCharacter m a : ℂ)) = toricMonomial D v m :=
  toricSectionCoeff_unique D v (differentiable_toricSectionCoeff D v _).continuous
    (differentiable_toricMonomial D v m).continuous
    (toricSectionCoeff_spec (latticeCharacter_mem_toricSections D hm) v)
    (latticeCharacter_eq_toricMonomial D hm v)

/-- Source `prop:toricusualOko` (proof): `ν_{Y•}(χ^m) = Φ(m)` for `m ∈ M ∩ P_D`. -/
theorem toricSectionValuation_latticeCharacter {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints D) :
    toricSectionValuation hs v e D (fun a => (latticeCharacter m a : ℂ)) =
      ((toLex (toricFlagLatticeMap hs v e D m) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
  have hg : toricSectionGerm D v (fun a => (latticeCharacter m a : ℂ)) =
      NativeHolGerm.mk (fun p : PolytopeToricVariety γ hs =>
        toricMonomial D v m (originalPolytopeNativeModelChart γ hs v p))
        (holomorphicAt_toricMonomial_comp v D m) := by
    apply NativeHolGerm.mk_eq_mk_iff.mpr
    refine Eventually.of_forall fun p => ?_
    rw [toricSectionCoeff_latticeCharacter v D hm]
  unfold toricSectionValuation
  rw [hg]
  exact originalFlagGermValuation_toricMonomial v e D hm

theorem nativeHolGerm_mk_sum {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] {x : M} {ι : Type*} (S : Finset ι) (G : ι → M → ℂ)
    (hG : ∀ l, HolomorphicAt n (G l) x) (h : HolomorphicAt n (fun p => ∑ l ∈ S, G l p) x) :
    NativeHolGerm.mk (fun p => ∑ l ∈ S, G l p) h = ∑ l ∈ S, NativeHolGerm.mk (G l) (hG l) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  change ((fun p => ∑ l ∈ S, G l p : M → ℂ) : Germ (𝓝 x) ℂ) = ∑ l ∈ S, ((G l : M → ℂ) : Germ (𝓝 x) ℂ)
  have : (fun p => ∑ l ∈ S, G l p : M → ℂ) = ∑ l ∈ S, G l := by
    funext p; simp [Finset.sum_apply]
  rw [this]
  exact map_sum (Germ.coeRingHom (𝓝 x)) G S

/-- Units (nonzero constants) have flag valuation `0`. -/
theorem originalFlagGermValuation_of_isUnit {F : OriginalFlagGeometry n}
    (x : OriginalFlagGermPoint F) (w : NativeHolGerm n F.carrier x.1) (hw : IsUnit w) :
    originalFlagGermValuation F x w = 0 := by
  rw [originalFlagGermValuation_apply_of_ne_zero F x w hw.ne_zero]
  change (((toLex fun i => (originalFlagGermVector F x w hw.ne_zero i : ℤ)) : Lex (Fin n → ℤ)) :
    WithTop (Lex (Fin n → ℤ))) = 0
  rw [originalFlagGermVector_of_isUnit F x w hw]
  rfl

/-- Source `prop:toricusualOko` (proof): the valuation of a nonzero section `s = ∑_m c_m χ^m`
is `Φ(m)` for the exponent `m` with `c_m ≠ 0` which is lexicographically first. -/
theorem exists_toricSectionValuation_eq {g : (Fin n → ℂˣ) → ℂ} (hg : g ∈ toricSections D)
    (hg0 : g ≠ 0) : ∃ m ∈ toricLatticePoints D, toricSectionLaurentCoeff g m ≠ 0 ∧
      toricSectionValuation hs v e D g =
        ((toLex (toricFlagLatticeMap hs v e D m) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
  classical
  set F := toricFlagGeometry (hs := hs) v e
  set x := toricFlagPoint (hs := hs) v e
  set Λ := (finite_toricLatticePoints D).toFinset
  set c := toricSectionLaurentCoeff g
  set Φ := toricFlagLatticeMap hs v e D
  set T := Λ.filter fun m => c m ≠ 0
  have hT : T.Nonempty := by
    by_contra hT
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    apply hg0
    funext a
    rw [eq_sum_of_mem_toricSections hg a]
    refine Finset.sum_eq_zero fun m hm => ?_
    have : c m = 0 := by
      by_contra hc
      have : m ∈ T := Finset.mem_filter.mpr ⟨hm, hc⟩
      rw [hT] at this
      exact Finset.notMem_empty m this
    change c m * _ = 0
    rw [this, zero_mul]
  obtain ⟨m0, hm0T, hmin⟩ := T.exists_min_image (fun m => toLex (Φ m)) hT
  have hm0 := Finset.mem_filter.mp hm0T
  have hm0Λ : m0 ∈ toricLatticePoints D := (Set.Finite.mem_toFinset _).mp hm0.1
  refine ⟨m0, hm0Λ, hm0.2, ?_⟩
  -- the germ as a combination of monomial germs (germs on `X` at `x_v`)
  let X := PolytopeToricVariety γ hs
  let ν : AddValuation (NativeHolGerm n X (vertexPoint hs v 0)) (WithTop (Lex (Fin n → ℤ))) :=
    originalFlagGermValuation F x
  let Mg : (Fin n → ℤ) → NativeHolGerm n X (vertexPoint hs v 0) := fun m =>
    NativeHolGerm.mk (fun p : X => toricMonomial D v m (originalPolytopeNativeModelChart γ hs v p))
      (holomorphicAt_toricMonomial_comp v D m)
  let term : (Fin n → ℤ) → NativeHolGerm n X (vertexPoint hs v 0) := fun m =>
    NativeHolGerm.constHom (c m) * Mg m
  have hsumholo : HolomorphicAt n (fun p : X =>
      ∑ m ∈ Λ, c m * toricMonomial D v m (originalPolytopeNativeModelChart γ hs v p))
      (vertexPoint hs v 0) :=
    HolomorphicAt.sum Λ fun m _ => (holomorphicAt_const (c m)).mul
      (holomorphicAt_toricMonomial_comp v D m)
  have hgerm : toricSectionGerm D v g = ∑ m ∈ Λ, term m := by
    have h1 : toricSectionGerm D v g = NativeHolGerm.mk (fun p : X =>
        ∑ m ∈ Λ, c m * toricMonomial D v m (originalPolytopeNativeModelChart γ hs v p)) hsumholo := by
      apply NativeHolGerm.mk_eq_mk_iff.mpr
      refine Eventually.of_forall fun p => ?_
      change toricSectionCoeff D v g (originalPolytopeNativeModelChart γ hs v p) = _
      rw [toricSectionCoeff_eq_sum hg v]
    rw [h1]
    exact nativeHolGerm_mk_sum Λ (fun m (p : X) =>
      c m * toricMonomial D v m (originalPolytopeNativeModelChart γ hs v p))
      (fun m => (holomorphicAt_const (c m)).mul (holomorphicAt_toricMonomial_comp v D m)) hsumholo
  have hval : ∀ m ∈ T, ν (term m) =
      ((toLex (Φ m) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
    intro m hm
    have hmT := Finset.mem_filter.mp hm
    have hmΛ : m ∈ toricLatticePoints D := (Set.Finite.mem_toFinset _).mp hmT.1
    have hunit : IsUnit (NativeHolGerm.constHom (c m) : NativeHolGerm n X (vertexPoint hs v 0)) := by
      rw [NativeHolGerm.isUnit_iff_eval_ne_zero]
      exact hmT.2
    have h0 : ν (NativeHolGerm.constHom (c m)) = 0 := originalFlagGermValuation_of_isUnit x _ hunit
    change ν (NativeHolGerm.constHom (c m) * Mg m) = _
    rw [ν.map_mul, h0, zero_add]
    exact originalFlagGermValuation_toricMonomial v e D hmΛ
  have hsumT : ∑ m ∈ Λ, term m = ∑ m ∈ T, term m := by
    rw [Finset.sum_filter_of_ne]
    intro m _ hm
    by_contra hc
    apply hm
    change NativeHolGerm.constHom (c m) * Mg m = 0
    rw [hc, map_zero, zero_mul]
  change ν (toricSectionGerm D v g) = _
  rw [hgerm, hsumT, ← Finset.add_sum_erase T term hm0T]
  rw [AddValuation.map_add_eq_of_lt_left _ ?_, hval m0 hm0T]
  rw [hval m0 hm0T]
  apply AddValuation.map_lt_sum' _ (WithTop.coe_lt_top _)
  intro m hm
  have hmT := (Finset.mem_erase.mp hm)
  rw [hval m hmT.2]
  apply WithTop.coe_lt_coe.mpr
  apply lt_of_le_of_ne (hmin m hmT.2)
  intro h
  exact hmT.1 (toricFlagLatticeMap_injective v e D (toLex.injective h).symm)

/-- `ν_{Y•}(H⁰(X, O(D)) ∖ 0)`, the valuations of the nonzero sections. -/
def toricSectionValues : Set (Fin n → ℤ) :=
  {w | ∃ g ∈ toricSections D, g ≠ 0 ∧
    toricSectionValuation hs v e D g = ((toLex w : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))}

/-- Source `prop:toricusualOko` (proof): `ν_{Y•}(H⁰(X, O(D)) ∖ 0) = Φ(M ∩ P_D)`. -/
theorem toricSectionValues_eq :
    toricSectionValues v e D = toricFlagLatticeMap hs v e D '' toricLatticePoints D := by
  ext w
  constructor
  · rintro ⟨g, hg, hg0, hw⟩
    obtain ⟨m, hm, -, hv⟩ := exists_toricSectionValuation_eq v e D hg hg0
    refine ⟨m, hm, ?_⟩
    rw [hw] at hv
    exact (toLex.injective (WithTop.coe_injective hv)).symm
  · rintro ⟨m, hm, rfl⟩
    refine ⟨fun a => (latticeCharacter m a : ℂ), latticeCharacter_mem_toricSections D hm, ?_,
      toricSectionValuation_latticeCharacter v e D hm⟩
    intro h0
    have := congrFun h0 1
    simp at this

end SGPT.Toric
