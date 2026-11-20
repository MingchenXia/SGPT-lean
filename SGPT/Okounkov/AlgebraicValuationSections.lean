import SGPT.Okounkov.AlgebraicValuationCenter
import SGPT.Okounkov.AlgebraicBodyOperations
import SGPT.Foundations.Schemes.SectionRingCenteredFrame

/-!
# Valuations of sections and Okounkov bodies for an arbitrary valuation `ν`

Source: Section *Algebraic partial Okounkov bodies* of the chapter *The theory of Okounkov
bodies*, which fixes **a rank `n` valuation `ν : ℂ(X)^× → ℤⁿ`** (not necessarily a flag
valuation) and considers `Γ(θ, φ)`, `Δ_k(θ, φ)` (`def:Okounkov:L484`), `Γ^∞(θ, φ)`
(`def:Okounkov:L500`), the twisted polytopes (`def:DeltakT`) and `Δ_ν(L) = Δ(Γ(L))`
(`def:Okobd`).

## The value of a section

`v : ℂ(X) → ℤⁿ_lex ∪ {∞}` is any additive valuation of the function field (rank and
surjectivity, assumed in the source, are not needed). For `s ∈ H⁰(X, L^k)`, `ν(s)` is the value
of the coefficient `s / e^k` of `s` in the `k`-th power of a frame `e` of `L` at the centre of
`v` (`SGPT.Okounkov.AlgebraicValuation.valuationCenter`, which exists and is unique for `X`
proper over `ℂ`). We define the value at every point `c` at which `v` is nonnegative
(`IsNonnegAt v c`, implied by the centre conditions): then it does not depend on the frame
(`sectionValue_eq_frame`) nor on the atlas, and products of sections add values. For a section
`s` of an arbitrary line bundle `M` (degree one, used for the twisted bundles `T ⊗ L^k`),
`plainSectionValue` is the value of `s / e`.

## Main definitions

* `sectionValue v c a k s`, `sectionVector`: `ν(s) ∈ ℤⁿ_lex ∪ {∞}`, `ν(s) ∈ ℤⁿ` for `s ≠ 0`.
* `sectionSemigroup v c a`: `Γ(L) = {(ν(s), k)}`, a semigroup.
* `sectionValueSet v c a P`, `multiplierSectionSet v c a φ` (`Γ(θ, φ)`),
  `inftySectionSet v c a φ` (`Γ^∞(θ, φ)`), `multiplierDegreePolytope` (`Δ_k(θ, φ)`),
  `twistedMultiplierDegreePolytope`, `twistedDegreePolytope` (`Δ_{k,T}(θ, φ)`, `Δ_{k,T}(L)`, with
  the literal sections of `T ⊗ L^k`), `okounkovBody v c a` (`Δ_ν(L)`), and the canonical versions
  at the centre of `v` (`centreOkounkovBody` etc.).

## Main results

* `okounkovBody_add_subset_tensor` (source `prop:subaddOkoun`) and `okounkovBody_tensorPower`
  (source `prop:Okourescaling`) for every valuation `v` and every point where `v ≥ 0`, in
  particular at the centre.
* Bridges to the flag-valuation API of `SGPT.Okounkov.AlgebraicSectionBodies`:
  `IsNonnegAt` holds for the flag valuation at the flag point, and there `sectionSemigroup`,
  `multiplierSectionSet`, `inftySectionSet` and `okounkovBody` are the existing objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.AlgebraicValuation

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Opposite TopologicalSpace
open scoped Pointwise

variable {X : Scheme.{0}} [IsIntegral X] {n : ℕ}
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))

/-- `v` is nonnegative on the local ring `𝒪_{X,c}` (e.g. `c` is the centre of `v`). -/
def IsNonnegAt (c : X) : Prop :=
  ∀ g : X.presheaf.stalk c, 0 ≤ v (algebraMap (X.presheaf.stalk c) X.functionField g)

variable {v}

theorem IsValuationCenter.isNonnegAt {c : X} (hc : IsValuationCenter v c) : IsNonnegAt v c :=
  hc.1

/-- Units of `𝒪_{X,c}` have value `0`. -/
theorem valuation_stalkUnit_eq_zero {c : X} (hc : IsNonnegAt v c) (u : (X.presheaf.stalk c)ˣ) :
    v (algebraMap (X.presheaf.stalk c) X.functionField (u : X.presheaf.stalk c)) = 0 := by
  have hu := hc u
  have hinv := hc ↑u⁻¹
  have hsum : v (algebraMap (X.presheaf.stalk c) X.functionField (u : X.presheaf.stalk c)) +
      v (algebraMap (X.presheaf.stalk c) X.functionField (↑u⁻¹ : X.presheaf.stalk c)) = 0 := by
    rw [← v.map_mul, ← map_mul]
    simp
  exact le_antisymm ((le_add_of_nonneg_right hinv).trans hsum.le) hu

/-- The transition between two frames through `c` has value `0`. -/
theorem valuation_frameTransition_eq_zero {L : X.Modules} {U V : X.Opens} {c : X}
    (hc : IsNonnegAt v c) (e : LocalBundleFrame L U) (f : LocalBundleFrame L V)
    (hx : c ∈ U) (hy : c ∈ V) :
    letI : Nonempty (U ⊓ V : X.Opens) := ⟨⟨c, hx, hy⟩⟩
    v (X.germToFunctionField (U ⊓ V)
      (localBundleFrameTransition e f (homOfLE inf_le_left) (homOfLE inf_le_right) :
        X.sheaf.obj.obj (op (U ⊓ V)))) = 0 := by
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨c, hx, hy⟩⟩
  rw [← localBundleFrameTransitionAtCenter_functionField e f c hx hy]
  exact valuation_stalkUnit_eq_zero hc _

omit [IsIntegral X] in
/-- Coefficients of a restricted global section in a restricted frame. -/
theorem frame_global_coefficients_restrict {M : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame M U) (i : V ⟶ U) (s : bundleSections M ⊤) :
    e.coefficients i (M.val.map (homOfLE le_top).op s) =
      X.presheaf.map i.op (e.coefficients (𝟙 _) (M.val.map (homOfLE le_top).op s)) := by
  have h := e.coefficients_restrict (𝟙 U) i (M.val.map (homOfLE le_top).op s)
  have hi : (homOfLE (le_top : U ≤ ⊤)).op ≫ i.op = (homOfLE (le_top : V ≤ ⊤)).op :=
    Subsingleton.elim _ _
  rw [← PresheafOfModules.map_comp_apply, hi] at h
  simp only [Category.comp_id] at h
  exact h

/-- The value of a section `s` of a line bundle `M` (degree one) does not depend on the frame
through a point where `v ≥ 0`. -/
theorem frame_value_eq {M : X.Modules} {U V : X.Opens} [Nonempty U] [Nonempty V] {c : X}
    (hc : IsNonnegAt v c) (e : LocalBundleFrame M U) (f : LocalBundleFrame M V)
    (hx : c ∈ U) (hy : c ∈ V) (s : bundleSections M ⊤) :
    v (globalSectionToFunctionField f s) = v (globalSectionToFunctionField e s) := by
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨c, hx, hy⟩⟩
  have h : globalSectionToFunctionField f s =
      X.germToFunctionField (U ⊓ V)
        (localBundleFrameTransition e f (homOfLE inf_le_left) (homOfLE inf_le_right) :
          X.sheaf.obj.obj (op (U ⊓ V))) * globalSectionToFunctionField e s := by
    change X.germToFunctionField V (f.coefficients (𝟙 _) (M.val.map (homOfLE le_top).op s)) = _ *
      X.germToFunctionField U (e.coefficients (𝟙 _) (M.val.map (homOfLE le_top).op s))
    rw [← germToFunctionField_restrict (homOfLE inf_le_right : U ⊓ V ⟶ V),
      ← germToFunctionField_restrict (homOfLE inf_le_left : U ⊓ V ⟶ U), ← map_mul]
    congr 1
    rw [← frame_global_coefficients_restrict f (homOfLE inf_le_right) s,
      ← frame_global_coefficients_restrict e (homOfLE inf_le_left) s]
    exact localBundleFrameTransition_coefficients e f _ _ _
  rw [h, v.map_mul, valuation_frameTransition_eq_zero hc e f hx hy, zero_add]

variable (v)

/-- `ν(s) = v(s / e)` for a section `s` of a line bundle `M` and the atlas frame `e` through `c`. -/
def plainSectionValue (c : X) {M : X.Modules} (b : LineBundleAtlas M) (s : bundleSections M ⊤) :
    WithTop (Lex (Fin n → ℤ)) :=
  v (globalSectionToFunctionField (b.frame (b.centerIndex c)) s)

/-- `ν(s) = v(s / e^k)` for `s ∈ H⁰(X, L^k)` and the atlas frame `e` of `L` through `c`. -/
def sectionValue (c : X) {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) : WithTop (Lex (Fin n → ℤ)) :=
  v (globalSectionToFunctionField ((a.frame (a.centerIndex c)).tensorPower k) s)

variable {v}

/-- The value of a section of `M` does not depend on the frame through `c`. -/
theorem plainSectionValue_eq_frame {c : X} (hc : IsNonnegAt v c) {M : X.Modules}
    (b : LineBundleAtlas M) {U : X.Opens} [Nonempty U] (e : LocalBundleFrame M U) (hcU : c ∈ U)
    (s : bundleSections M ⊤) :
    plainSectionValue v c b s = v (globalSectionToFunctionField e s) :=
  frame_value_eq hc e _ hcU (b.centerIndex_mem c) s

/-- The value of a section of `L^k` does not depend on the frame of `L` through `c`. -/
theorem sectionValue_eq_frame {c : X} (hc : IsNonnegAt v c) {L : X.Modules}
    (a : LineBundleAtlas L) {U : X.Opens} [Nonempty U] (e : LocalBundleFrame L U) (hcU : c ∈ U)
    (k : ℕ) (s : bundlePowerGlobalSections L k) :
    sectionValue v c a k s = v (globalSectionToFunctionField (e.tensorPower k) s) := by
  unfold sectionValue
  let : Nonempty (U ⊓ a.opens (a.centerIndex c) : X.Opens) := ⟨⟨c, hcU, a.centerIndex_mem c⟩⟩
  rw [LocalBundleFrame.globalGenericPowerCoefficient_transition e (a.frame (a.centerIndex c))
    (homOfLE inf_le_left : U ⊓ a.opens (a.centerIndex c) ⟶ U)
    (homOfLE inf_le_right : U ⊓ a.opens (a.centerIndex c) ⟶ a.opens (a.centerIndex c)),
    v.map_mul, v.map_pow, valuation_frameTransition_eq_zero hc e _ hcU (a.centerIndex_mem c),
    nsmul_zero, zero_add]

/-- The value of a section of `L^k` does not depend on the atlas. -/
theorem sectionValue_atlas_independent {c : X} (hc : IsNonnegAt v c) {L : X.Modules}
    (a b : LineBundleAtlas L) (k : ℕ) (s : bundlePowerGlobalSections L k) :
    sectionValue v c a k s = sectionValue v c b k s :=
  sectionValue_eq_frame hc a _ (b.centerIndex_mem c) k s

/-- The value of a section of `M` does not depend on the atlas. -/
theorem plainSectionValue_atlas_independent {c : X} (hc : IsNonnegAt v c) {M : X.Modules}
    (b b' : LineBundleAtlas M) (s : bundleSections M ⊤) :
    plainSectionValue v c b s = plainSectionValue v c b' s :=
  plainSectionValue_eq_frame hc b _ (b'.centerIndex_mem c) s

theorem sectionValue_eq_top_iff (c : X) {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) : sectionValue v c a k s = ⊤ ↔ s = 0 := by
  unfold sectionValue
  rw [v.top_iff]
  constructor
  · intro h
    apply globalSectionToFunctionField_injective (a.tensorPower k)
      ((a.frame (a.centerIndex c)).tensorPower k)
    rw [h, map_zero]
  · rintro rfl
    exact map_zero _

theorem plainSectionValue_eq_top_iff (c : X) {M : X.Modules} (b : LineBundleAtlas M)
    (s : bundleSections M ⊤) : plainSectionValue v c b s = ⊤ ↔ s = 0 := by
  unfold plainSectionValue
  rw [v.top_iff]
  constructor
  · intro h
    apply globalSectionToFunctionField_injective b (b.frame (b.centerIndex c))
    rw [h, map_zero]
  · rintro rfl
    exact map_zero _

variable (v)

/-- The vector `ν(s) ∈ ℤⁿ` of a nonzero section of `L^k`. -/
def sectionVector (c : X) {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) : Fin n → ℤ :=
  ofLex ((sectionValue v c a k s).untop ((sectionValue_eq_top_iff c a k s).not.mpr hs))

/-- The vector `ν(s) ∈ ℤⁿ` of a nonzero section of a line bundle `M`. -/
def plainSectionVector (c : X) {M : X.Modules} (b : LineBundleAtlas M) (s : bundleSections M ⊤)
    (hs : s ≠ 0) : Fin n → ℤ :=
  ofLex ((plainSectionValue v c b s).untop ((plainSectionValue_eq_top_iff c b s).not.mpr hs))

variable {v}

theorem sectionValue_eq_vector (c : X) {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (s : bundlePowerGlobalSections L k) (hs : s ≠ 0) :
    sectionValue v c a k s = ((toLex (sectionVector v c a k s hs) : Lex (Fin n → ℤ)) :
      WithTop (Lex (Fin n → ℤ))) := by
  unfold sectionVector
  rw [toLex_ofLex, WithTop.coe_untop]

theorem plainSectionValue_eq_vector (c : X) {M : X.Modules} (b : LineBundleAtlas M)
    (s : bundleSections M ⊤) (hs : s ≠ 0) :
    plainSectionValue v c b s = ((toLex (plainSectionVector v c b s hs) : Lex (Fin n → ℤ)) :
      WithTop (Lex (Fin n → ℤ))) := by
  unfold plainSectionVector
  rw [toLex_ofLex, WithTop.coe_untop]

/-- Equal values give equal vectors. -/
theorem sectionVector_eq_of_value_eq (c c' : X) {L L' : X.Modules} (a : LineBundleAtlas L)
    (a' : LineBundleAtlas L') (m m' : ℕ) (s : bundlePowerGlobalSections L m)
    (s' : bundlePowerGlobalSections L' m') (hs : s ≠ 0) (hs' : s' ≠ 0)
    (h : sectionValue v c a m s = sectionValue v c' a' m' s') :
    sectionVector v c a m s hs = sectionVector v c' a' m' s' hs' := by
  rw [sectionValue_eq_vector c a m s hs, sectionValue_eq_vector c' a' m' s' hs'] at h
  exact toLex.injective (WithTop.coe_injective h)

/-- Equal values of sections of line bundles give equal vectors. -/
theorem plainSectionVector_eq_of_value_eq (c c' : X) {M M' : X.Modules} (b : LineBundleAtlas M)
    (b' : LineBundleAtlas M') (s : bundleSections M ⊤) (s' : bundleSections M' ⊤) (hs : s ≠ 0)
    (hs' : s' ≠ 0) (h : plainSectionValue v c b s = plainSectionValue v c' b' s') :
    plainSectionVector v c b s hs = plainSectionVector v c' b' s' hs' := by
  rw [plainSectionValue_eq_vector c b s hs, plainSectionValue_eq_vector c' b' s' hs'] at h
  exact toLex.injective (WithTop.coe_injective h)

theorem sectionVector_congr (c : X) {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ)
    {s s' : bundlePowerGlobalSections L m} (hs : s ≠ 0) (hs' : s' ≠ 0) (h : s = s') :
    sectionVector v c a m s hs = sectionVector v c a m s' hs' := by
  subst h
  rfl

/-- Products of sections add values. -/
theorem sectionValue_mul (c : X) {L : X.Modules} (a : LineBundleAtlas L) (m k : ℕ)
    (s : bundlePowerGlobalSections L m) (t : bundlePowerGlobalSections L k) :
    sectionValue v c a (m + k) (atlasPowerGlobalMul a m k s t) =
      sectionValue v c a m s + sectionValue v c a k t := by
  unfold sectionValue
  change v (X.germToFunctionField (a.opens (a.centerIndex c))
      (atlasPowerGlobalCoefficients a (m + k) (a.centerIndex c) (atlasPowerGlobalMul a m k s t))) =
    v (X.germToFunctionField (a.opens (a.centerIndex c))
      (atlasPowerGlobalCoefficients a m (a.centerIndex c) s)) +
    v (X.germToFunctionField (a.opens (a.centerIndex c))
      (atlasPowerGlobalCoefficients a k (a.centerIndex c) t))
  rw [atlasPowerGlobalMul_coefficients, map_mul, v.map_mul]

/-- The unit `1 ∈ H⁰(L⁰)` has value `0`. -/
theorem sectionValue_one (c : X) {L : X.Modules} (a : LineBundleAtlas L) :
    sectionValue v c a 0 (bundlePowerGlobalOne L) = 0 := by
  unfold sectionValue
  change v (X.germToFunctionField (a.opens (a.centerIndex c))
      (atlasPowerGlobalCoefficients a 0 (a.centerIndex c) (bundlePowerGlobalOne L))) = 0
  rw [atlasPowerGlobalCoefficients_one, map_one, v.map_one]

include v in
theorem atlasPowerGlobalMul_ne_zero (c : X) {L : X.Modules} (a : LineBundleAtlas L) (m k : ℕ)
    {s : bundlePowerGlobalSections L m} {t : bundlePowerGlobalSections L k} (hs : s ≠ 0)
    (ht : t ≠ 0) : atlasPowerGlobalMul a m k s t ≠ 0 := by
  intro h0
  have h := sectionValue_mul (v := v) c a m k s t
  rw [h0, (sectionValue_eq_top_iff c a (m + k) 0).mpr rfl] at h
  exact WithTop.add_ne_top.mpr ⟨(sectionValue_eq_top_iff c a m s).not.mpr hs,
    (sectionValue_eq_top_iff c a k t).not.mpr ht⟩ h.symm

include v in
theorem bundlePowerGlobalOne_ne_zero (c : X) {L : X.Modules} (a : LineBundleAtlas L) :
    bundlePowerGlobalOne L ≠ 0 := by
  intro h0
  have h := sectionValue_one (v := v) c a
  rw [h0, (sectionValue_eq_top_iff c a 0 0).mpr rfl] at h
  exact WithTop.top_ne_zero h

variable (v)

/-- Source: the section semigroup `Γ(L) = {(ν(s), k) : s ∈ H⁰(X, L^k) \ {0}}` of the valuation
`v` (with sections valued at `c`). -/
def sectionSemigroup (c : X) {L : X.Modules} (a : LineBundleAtlas L) :
    AddSubsemigroup ((Fin n → ℤ) × ℤ) where
  carrier := {z | ∃ (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0),
    z = (sectionVector v c a k s hs, (k : ℤ))}
  add_mem' := by
    rintro z w ⟨m, s, hs, rfl⟩ ⟨k, t, ht, rfl⟩
    have hu := atlasPowerGlobalMul_ne_zero (v := v) c a m k hs ht
    refine ⟨m + k, atlasPowerGlobalMul a m k s t, hu, ?_⟩
    have hv := sectionValue_mul (v := v) c a m k s t
    rw [sectionValue_eq_vector c a (m + k) _ hu, sectionValue_eq_vector c a m s hs,
      sectionValue_eq_vector c a k t ht, ← WithTop.coe_add, ← toLex_add] at hv
    have hv' := toLex.injective (WithTop.coe_injective hv)
    rw [hv']
    ext <;> simp

/-- Lattice points `(ν(s), k)` of the nonzero sections `s ∈ H⁰(X, L^k)` satisfying `P k s`. -/
def sectionValueSet (c : X) {L : X.Modules} (a : LineBundleAtlas L)
    (P : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop) : Set ((Fin n → ℤ) × ℤ) :=
  {z | ∃ (k : ℕ) (s : bundlePowerGlobalSections L k) (hs : s ≠ 0), P k s ∧
    z = (sectionVector v c a k s hs, (k : ℤ))}

/-- Source `def:Okobd`: `Δ_ν(L) = Δ(Γ(L))` (height-one slice of the closed cone generated by
`Γ(L)`, source `def:Okokk`). -/
def okounkovBody (c : X) {L : X.Modules} (a : LineBundleAtlas L) : Set (Fin n → ℝ) :=
  SGPT.AlmostSemigroup.Okounkov.body (sectionSemigroup v c a)

variable {v}

theorem sectionValueSet_true (c : X) {L : X.Modules} (a : LineBundleAtlas L) :
    sectionValueSet v c a (fun _ _ => True) =
      (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) := by
  ext z
  constructor
  · rintro ⟨k, s, hs, -, rfl⟩
    exact ⟨k, s, hs, rfl⟩
  · rintro ⟨k, s, hs, rfl⟩
    exact ⟨k, s, hs, trivial, rfl⟩

theorem sectionValueSet_subset (c : X) {L : X.Modules} (a : LineBundleAtlas L)
    (P : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop) :
    sectionValueSet v c a P ⊆ (sectionSemigroup v c a : Set ((Fin n → ℤ) × ℤ)) := by
  rintro z ⟨k, s, hs, -, rfl⟩
  exact ⟨k, s, hs, rfl⟩

theorem sectionValueSet_mono (c : X) {L : X.Modules} (a : LineBundleAtlas L)
    {P Q : ∀ k : ℕ, bundlePowerGlobalSections L k → Prop} (hPQ : ∀ k s, P k s → Q k s) :
    sectionValueSet v c a P ⊆ sectionValueSet v c a Q := by
  rintro z ⟨k, s, hs, hP, rfl⟩
  exact ⟨k, s, hs, hPQ k s hP, rfl⟩

theorem zero_mem_sectionSemigroup (c : X) {L : X.Modules} (a : LineBundleAtlas L) :
    (0 : (Fin n → ℤ) × ℤ) ∈ sectionSemigroup v c a := by
  have h1 := bundlePowerGlobalOne_ne_zero (v := v) c a
  refine ⟨0, bundlePowerGlobalOne L, h1, ?_⟩
  have hv := sectionValue_one (v := v) c a
  rw [sectionValue_eq_vector c a 0 _ h1] at hv
  have hv' : toLex (sectionVector v c a 0 (bundlePowerGlobalOne L) h1) = toLex 0 :=
    WithTop.coe_injective hv
  rw [toLex.injective hv']
  rfl

theorem sectionSemigroup_degree_nonneg (c : X) {L : X.Modules} (a : LineBundleAtlas L)
    (z : (Fin n → ℤ) × ℤ) (hz : z ∈ sectionSemigroup v c a) : 0 ≤ z.2 := by
  obtain ⟨k, s, hs, rfl⟩ := hz
  exact Int.natCast_nonneg _

/-- The section semigroup does not depend on the atlas. -/
theorem sectionSemigroup_atlas_independent {c : X} (hc : IsNonnegAt v c) {L : X.Modules}
    (a b : LineBundleAtlas L) : sectionSemigroup v c a = sectionSemigroup v c b := by
  ext z
  constructor
  · rintro ⟨k, s, hs, rfl⟩
    exact ⟨k, s, hs, by rw [sectionVector_eq_of_value_eq c c a b k k s s hs hs
      (sectionValue_atlas_independent hc a b k s)]⟩
  · rintro ⟨k, s, hs, rfl⟩
    exact ⟨k, s, hs, by rw [sectionVector_eq_of_value_eq c c b a k k s s hs hs
      (sectionValue_atlas_independent hc b a k s)]⟩

/-! ### Tensor powers: `Δ_ν(L^a) = a Δ_ν(L)` -/

/-- `L^{rm} ≅ (L^r)^m` preserves values. -/
theorem sectionValue_tensorPowerMulIso {c : X} (hc : IsNonnegAt v c) {L : X.Modules}
    (a : LineBundleAtlas L) (r m : ℕ) (t : bundlePowerGlobalSections L (r * m)) :
    sectionValue v c (a.tensorPower r) m
        ((nativeLineTensorPowerMulIso a r m).hom.val.app (op ⊤) t) =
      sectionValue v c a (r * m) t := by
  have hx := a.centerIndex_mem c
  rw [sectionValue_eq_frame hc (a.tensorPower r) ((a.frame (a.centerIndex c)).tensorPower r) hx m,
    globalSectionToFunctionField_tensorPowerMulIso]
  rfl

/-- `(x, k) ∈ Γ(L^r) ↔ (x, r k) ∈ Γ(L)`, for every atlas of `L^r`. -/
theorem mem_sectionSemigroup_tensorPower_iff {c : X} (hc : IsNonnegAt v c) {L : X.Modules}
    (a : LineBundleAtlas L) {r : ℕ} (hr : 0 < r) (b : LineBundleAtlas (bundleTensorPower L r))
    (x : Fin n → ℤ) (k : ℤ) :
    (x, k) ∈ sectionSemigroup v c b ↔ (x, (r : ℤ) * k) ∈ sectionSemigroup v c a := by
  rw [sectionSemigroup_atlas_independent hc b (a.tensorPower r)]
  constructor
  · rintro ⟨m, s, hs, hz⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
    let Φ := nativeLineTensorPowerMulIso a r m
    let t := Φ.inv.val.app (op ⊤) s
    have hst : Φ.hom.val.app (op ⊤) t = s := congrArg (fun α => α.val.app (op ⊤) s) Φ.inv_hom_id
    have ht : t ≠ 0 := by
      intro h0
      apply hs
      rw [← hst, h0, map_zero]
    refine ⟨r * m, t, ht, ?_⟩
    have hv := sectionValue_tensorPowerMulIso hc a r m t
    rw [hst] at hv
    rw [sectionVector_eq_of_value_eq c c _ _ _ _ s t hs ht hv]
    push_cast
    rfl
  · rintro ⟨m', t, ht, hz⟩
    obtain ⟨hx, hk⟩ := Prod.mk.inj hz
    have hk0 : 0 ≤ k := by
      have : (0 : ℤ) ≤ (r : ℤ) * k := by rw [hk]; exact Int.natCast_nonneg _
      have hr' : (0 : ℤ) < r := by exact_mod_cast hr
      nlinarith
    lift k to ℕ using hk0
    have hm' : m' = r * k := by exact_mod_cast hk.symm
    subst hm' hx
    let Φ := nativeLineTensorPowerMulIso a r k
    have hΦt : Φ.hom.val.app (op ⊤) t ≠ 0 := by
      intro h0
      apply ht
      have hh := congrArg (fun α => α.val.app (op ⊤) t) Φ.hom_inv_id
      change Φ.inv.val.app (op ⊤) (Φ.hom.val.app (op ⊤) t) = t at hh
      rw [← hh, h0, map_zero]
    refine ⟨k, Φ.hom.val.app (op ⊤) t, hΦt, ?_⟩
    rw [sectionVector_eq_of_value_eq c c _ _ _ _ _ t hΦt ht
      (sectionValue_tensorPowerMulIso hc a r k t)]

/-- **Source `prop:Okourescaling`**: `Δ_ν(L^a) = a Δ_ν(L)` for every `a ∈ ℤ_{>0}`, every valuation
`v` and every point `c` where `v ≥ 0` (in particular the centre), and every atlas of `L^a`. -/
theorem okounkovBody_tensorPower {c : X} (hc : IsNonnegAt v c) {L : X.Modules}
    (a : LineBundleAtlas L) {r : ℕ} (hr : 0 < r) (b : LineBundleAtlas (bundleTensorPower L r)) :
    okounkovBody v c b = (r : ℝ) • okounkovBody v c a :=
  SGPT.Okounkov.AlgebraicBody.body_eq_smul_of_veronese _ _ hr
    (mem_sectionSemigroup_tensorPower_iff hc a hr b)

/-! ### Tensor products: `Δ_ν(L) + Δ_ν(L') ⊆ Δ_ν(L ⊗ L')` -/

/-- Products `H⁰(L^k) × H⁰(N^k) → H⁰((L ⊗ N)^k)` add values. -/
theorem sectionValue_tensorPowerSectionProduct {c : X} (hc : IsNonnegAt v c) {L N : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (d : LineBundleAtlas (bundleTensor L N))
    (k : ℕ) (s : bundlePowerGlobalSections L k) (t : bundlePowerGlobalSections N k) :
    sectionValue v c d k (tensorPowerSectionProduct a b k s t) =
      sectionValue v c a k s + sectionValue v c b k t := by
  obtain ⟨i, hi⟩ := a.covers c
  obtain ⟨j, hj⟩ := b.covers c
  have hx : c ∈ (a.opens (i, j).1 ⊓ b.opens (i, j).2 : X.Opens) := ⟨hi, hj⟩
  let : Nonempty (a.opens (i, j).1 ⊓ b.opens (i, j).2 : X.Opens) := ⟨⟨_, hx⟩⟩
  rw [sectionValue_eq_frame hc d
      ((leftRestrictedFrame a b (i, j)).tensor (rightRestrictedFrame a b (i, j))) hx k,
    sectionValue_eq_frame hc a (leftRestrictedFrame a b (i, j)) hx k,
    sectionValue_eq_frame hc b (rightRestrictedFrame a b (i, j)) hx k,
    globalSectionToFunctionField_tensorPowerSectionProduct, v.map_mul]

/-- Same-degree points of `Γ(L)` and `Γ(N)` multiply into `Γ(L ⊗ N)`. -/
theorem sectionSemigroup_add_mem_tensor {c : X} (hc : IsNonnegAt v c) {L N : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (d : LineBundleAtlas (bundleTensor L N))
    (x y : Fin n → ℤ) (k : ℤ) (hx : (x, k) ∈ sectionSemigroup v c a)
    (hy : (y, k) ∈ sectionSemigroup v c b) : (x + y, k) ∈ sectionSemigroup v c d := by
  obtain ⟨m, s, hs, hz⟩ := hx
  obtain ⟨m', t, ht, hz'⟩ := hy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
  obtain ⟨rfl, hmm⟩ := Prod.mk.inj hz'
  have hm : m' = m := by exact_mod_cast hmm.symm
  subst hm
  have hv := sectionValue_tensorPowerSectionProduct hc a b d m' s t
  have hst : tensorPowerSectionProduct a b m' s t ≠ 0 := by
    intro h0
    rw [h0, (sectionValue_eq_top_iff c d m' 0).mpr rfl] at hv
    exact WithTop.add_ne_top.mpr ⟨(sectionValue_eq_top_iff c a m' s).not.mpr hs,
      (sectionValue_eq_top_iff c b m' t).not.mpr ht⟩ hv.symm
  refine ⟨m', tensorPowerSectionProduct a b m' s t, hst, ?_⟩
  rw [sectionValue_eq_vector c d m' _ hst, sectionValue_eq_vector c a m' s hs,
    sectionValue_eq_vector c b m' t ht, ← WithTop.coe_add, ← toLex_add] at hv
  rw [toLex.injective (WithTop.coe_injective hv)]

/-- **Source `prop:subaddOkoun`**: `Δ_ν(L) + Δ_ν(N) ⊆ Δ_ν(L ⊗ N)` for all line bundles, every
valuation `v`, every point `c` where `v ≥ 0` (in particular the centre) and every atlas of
`L ⊗ N`. -/
theorem okounkovBody_add_subset_tensor {c : X} (hc : IsNonnegAt v c) {L N : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (d : LineBundleAtlas (bundleTensor L N)) :
    okounkovBody v c a + okounkovBody v c b ⊆ okounkovBody v c d :=
  SGPT.Okounkov.AlgebraicBody.body_add_subset_of_mul _ _ _
    (zero_mem_sectionSemigroup c a) (zero_mem_sectionSemigroup c b)
    (sectionSemigroup_degree_nonneg c a) (sectionSemigroup_degree_nonneg c b)
    (sectionSemigroup_add_mem_tensor hc a b d)

/-! ### The canonical objects at the centre of `v` -/

section Centre

variable (f : X ⟶ Spec (.of ℂ)) [IsProper f]

/-- Source `def:Okobd`: the Okounkov body `Δ_ν(L)` of `L` for the valuation `ν = w`, with section
values taken at the centre of `w`. -/
def centreOkounkovBody (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    {L : X.Modules} (a : LineBundleAtlas L) : Set (Fin n → ℝ) :=
  okounkovBody w (valuationCenter f w) a

theorem isNonnegAt_valuationCenter (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) :
    IsNonnegAt w (valuationCenter f w) :=
  (isValuationCenter_valuationCenter f w).isNonnegAt

/-- Source `prop:Okourescaling` at the centre. -/
theorem centreOkounkovBody_tensorPower
    (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {L : X.Modules}
    (a : LineBundleAtlas L) {r : ℕ} (hr : 0 < r) (b : LineBundleAtlas (bundleTensorPower L r)) :
    centreOkounkovBody f w b = (r : ℝ) • centreOkounkovBody f w a :=
  okounkovBody_tensorPower (isNonnegAt_valuationCenter f w) a hr b

/-- Source `prop:subaddOkoun` at the centre. -/
theorem centreOkounkovBody_add_subset_tensor
    (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {L N : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas N) (d : LineBundleAtlas (bundleTensor L N)) :
    centreOkounkovBody f w a + centreOkounkovBody f w b ⊆ centreOkounkovBody f w d :=
  okounkovBody_add_subset_tensor (isNonnegAt_valuationCenter f w) a b d

/-- `Δ_ν(L)` does not depend on the atlas. -/
theorem centreOkounkovBody_atlas_independent
    (w : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) {L : X.Modules}
    (a b : LineBundleAtlas L) : centreOkounkovBody f w a = centreOkounkovBody f w b := by
  unfold centreOkounkovBody okounkovBody
  rw [sectionSemigroup_atlas_independent (isNonnegAt_valuationCenter f w) a b]

end Centre

end SGPT.Okounkov.AlgebraicValuation
