import SGPT.BDivisor.BlowupModelModifiedNef
import SGPT.BDivisor.PseudoeffectivePushforward

/-!
# Comparison of the b-divisors over the book's models with those over all modifications

The b-divisor files of lanes S4–S36 (`SGPT.BDivisor.WeilBDivisor`) index b-divisors by all proper
holomorphic bimeromorphic maps `π : Y → X` from complex manifolds; the book (`def:modif`) indexes
them by the finite compositions of blow-ups with smooth centres (`ModelSystem.blowup`, with the
b-divisors `BlowupWeilBDivisor`). This file compares the two conventions, for an arbitrary model
system `S` of the compact connected manifold `X`.

**Unconditional comparisons** (no Chow lemma):

* `WeilBDivisorOn.restrict S` — the linear restriction map from all-model b-divisors to `S`; it
  preserves classes, roots, the order and pseudo-effectivity, and maps the Cartier b-divisor
  realized by `(π, α)` with `π ∈ S` to the `S`-Cartier b-divisor realized by `(π, α)`
  (`restrict_cartierOf`);
* every `S`-Cartier (resp. nef Cartier) b-divisor is the restriction of the all-model Cartier
  (resp. nef Cartier) b-divisor with the same realization (`exists_cartier_restrict_eq`,
  `exists_nefCartier_restrict_eq`): Cartier b-divisors are determined on a model of `S`;
* `vol_le_vol_restrict` — the volume over all models is at most the volume over `S`.

**Comparisons that need cofinality of `S`** (`ModelSystem.IsCofinal`: every modification is
dominated by a model of `S`; for the book's system this is Hironaka's Chow lemma,
`ModelSystem.blowup_isCofinal_of_chow`, not proved):

* `restrictEquiv` — restriction is a linear isomorphism, with inverse `extend`
  (`𝔻_π = g_* 𝔻_σ` for any `σ ∈ S` dominating `π`);
* `le_iff_restrict`, `isPseudoeffective_iff_restrict`, `isCartier_iff_restrict`,
  `isNefCartier_iff_restrict` and `isNef_iff_restrict` (the latter two for systems of Kähler
  models, such as the blow-up models of a compact Kähler manifold);
* `vol_restrict_eq` — the two volumes agree **provided** the class volume does not decrease under
  push-forward along all dominations of arbitrary models (`WeilBDivisor.PushforwardVolumeMonotone`);
  that monotonicity is known only on Kähler models (`prop:cones_modif2`), and modifications of a
  Kähler manifold need not be Kähler, so this hypothesis stays explicit even granted the Chow
  lemma. Over the book's models no such hypothesis is needed (`tendsto_vol_blowup`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.BDivisor

open Set Filter
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending

namespace WeilBDivisorOn

section General

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] {S : ModelSystem n X} {hn : 0 < n}

variable (S) in
/-- The **restriction** of a b-divisor over all modifications to the models of `S`. -/
def restrict : WeilBDivisor n X hn →ₗ[ℝ] WeilBDivisorOn S hn where
  toFun D := ⟨fun π => D.onModel π.1, fun π π' h => D.pushforward_onModel (show π.1 ≤ π'.1 from h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrict_onModel (D : WeilBDivisor n X hn) (π : S.Model) :
    (restrict S D).onModel π = D.onModel π.1 := rfl

@[simp] theorem root_restrict (D : WeilBDivisor n X hn) : (restrict S D).root = D.root := rfl

theorem restrict_le {D D' : WeilBDivisor n X hn} (h : D.LE D') :
    (restrict S D).LE (restrict S D') := fun π => h π.1

theorem restrict_isPseudoeffective {D : WeilBDivisor n X hn} (h : D.IsPseudoeffective) :
    (restrict S D).IsPseudoeffective := fun π => h π.1

/-- A realization on a model of `S` restricts to a realization. -/
theorem restrict_isRealization {D : WeilBDivisor n X hn} {π : S.Model}
    {α : RealBottChern n π.1.carrier} (h : D.IsRealization π.1 α) :
    (restrict S D).IsRealization π α :=
  fun π' h' => h π'.1 h'


section Cofinal

/-! ### Under cofinality -/

variable (hS : S.IsCofinal)
include hS

/-- The class on an arbitrary model `π` of the extension of `E`: `g_* E_σ` for a model `σ ∈ S`
dominating `π`. -/
def extendClass (E : WeilBDivisorOn S hn) (π : Modification n X) : RealBottChern n π.carrier :=
  Modification.classPushforwardOfLE hn (hS π).choose_spec (E.onModel (hS π).choose)

theorem extendClass_eq (E : WeilBDivisorOn S hn) {π : Modification n X} {σ : S.Model}
    (h : π ≤ σ.1) : extendClass hS E π = Modification.classPushforwardOfLE hn h (E.onModel σ) := by
  obtain ⟨ρ, h₀, h₁⟩ := ModelSystem.Model.exists_le_le (hS π).choose σ
  rw [extendClass, ← E.pushforward_onModel h₀, ← E.pushforward_onModel h₁,
    ← Modification.classPushforwardOfLE_trans, ← Modification.classPushforwardOfLE_trans]

/-- The extension of a b-divisor over a cofinal system to all modifications. -/
def extend (E : WeilBDivisorOn S hn) : WeilBDivisor n X hn :=
  ⟨extendClass hS E, by
    intro π π' h
    obtain ⟨σ, hσ⟩ := hS π'
    rw [extendClass_eq hS E hσ, extendClass_eq hS E (h.trans hσ)]
    exact (Modification.classPushforwardOfLE_trans hn h hσ _).symm⟩

theorem extend_onModel (E : WeilBDivisorOn S hn) {π : Modification n X} {σ : S.Model}
    (h : π ≤ σ.1) :
    (extend hS E).onModel π = Modification.classPushforwardOfLE hn h (E.onModel σ) :=
  extendClass_eq hS E h

theorem restrict_extend (E : WeilBDivisorOn S hn) : restrict S (extend hS E) = E := by
  ext σ
  rw [restrict_onModel, extend_onModel hS E (le_refl σ.1), Modification.classPushforwardOfLE_refl]

theorem extend_restrict (D : WeilBDivisor n X hn) : extend hS (restrict S D) = D := by
  apply Subtype.ext
  funext π
  obtain ⟨σ, hσ⟩ := hS π
  change (extend hS (restrict S D)).onModel π = D.onModel π
  rw [extend_onModel hS _ hσ, restrict_onModel, D.pushforward_onModel]

/-- **Under cofinality, restriction is a linear isomorphism** between b-divisors over all
modifications and b-divisors over `S`. -/
def restrictEquiv : WeilBDivisor n X hn ≃ₗ[ℝ] WeilBDivisorOn S hn :=
  { restrict S with
    invFun := extend hS
    left_inv := extend_restrict hS
    right_inv := restrict_extend hS }

theorem restrict_injective : Function.Injective (restrict S (hn := hn)) :=
  (restrictEquiv hS).injective

theorem isCartier_iff_restrict (D : WeilBDivisor n X hn) :
    D.IsCartier ↔ (restrict S D).IsCartier := by
  constructor
  · rintro ⟨π, α, hr⟩
    obtain ⟨σ, hσ⟩ := hS π
    refine ⟨σ, Modification.classPullbackOfLE hσ α, fun σ' h' => ?_⟩
    rw [restrict_onModel, hr σ'.1 (hσ.trans h')]
    exact Modification.classPullbackOfLE_trans hσ h' α
  · rintro ⟨σ, α, hr⟩
    refine ⟨σ.1, α, fun π' h' => ?_⟩
    obtain ⟨τ, hτ⟩ := hS π'
    have hστ : σ ≤ τ := show σ.1 ≤ τ.1 from h'.trans hτ
    rw [← D.pushforward_onModel hτ, ← restrict_onModel (S := S) D τ, hr τ hστ]
    change Modification.classPushforwardOfLE hn hτ
      (Modification.classPullbackOfLE (h'.trans hτ) α) = _
    rw [Modification.classPullbackOfLE_trans h' hτ,
      Modification.classPushforwardOfLE_classPullbackOfLE]

/-- A nef Cartier b-divisor over `S` comes from an all-model nef Cartier b-divisor; with Kähler
models in `S`, conversely. -/
theorem isNefCartier_iff_restrict
    (hK : ∀ σ : S.Model, Nonempty (KahlerBackground n σ.1.carrier)) (D : WeilBDivisor n X hn) :
    D.IsNefCartier ↔ (restrict S D).IsNefCartier := by
  constructor
  · rintro ⟨π, α, hr, κ, hα⟩
    obtain ⟨σ, hσ⟩ := hS π
    obtain ⟨κσ⟩ := hK σ
    refine ⟨σ, Modification.classPullbackOfLE hσ α, fun σ' h' => ?_, κσ,
      classNef_classPullback (Modification.contMDiff_homOfLE hσ) κ κσ hα⟩
    rw [restrict_onModel, hr σ'.1 (hσ.trans h')]
    exact Modification.classPullbackOfLE_trans hσ h' α
  · rintro ⟨σ, α, hr, κ, hα⟩
    refine ⟨σ.1, α, fun π' h' => ?_, κ, hα⟩
    obtain ⟨τ, hτ⟩ := hS π'
    have hστ : σ ≤ τ := show σ.1 ≤ τ.1 from h'.trans hτ
    rw [← D.pushforward_onModel hτ, ← restrict_onModel (S := S) D τ, hr τ hστ]
    change Modification.classPushforwardOfLE hn hτ
      (Modification.classPullbackOfLE (h'.trans hτ) α) = _
    rw [Modification.classPullbackOfLE_trans h' hτ,
      Modification.classPushforwardOfLE_classPullbackOfLE]

/-- **Nefness is the same in both conventions** (cofinal system of Kähler models). -/
theorem isNef_iff_restrict (hK : ∀ σ : S.Model, Nonempty (KahlerBackground n σ.1.carrier))
    (𝔻 : WeilBDivisor n X hn) : 𝔻.IsNef ↔ (restrict S 𝔻).IsNef := by
  constructor
  · rintro ⟨ι, i1, i2, i3, D, hD, hconv⟩
    exact ⟨ι, i1, i2, i3, fun i => restrict S (D i),
      fun i => (isNefCartier_iff_restrict hS hK (D i)).mp (hD i), fun σ => hconv σ.1⟩
  · rintro ⟨ι, i1, i2, i3, E, hE, hconv⟩
    refine ⟨ι, i1, i2, i3, fun i => extend hS (E i), fun i => ?_, fun π => ?_⟩
    · rw [isNefCartier_iff_restrict hS hK, restrict_extend]
      exact hE i
    · obtain ⟨σ, hσ⟩ := hS π
      have h := tendsto_euclideanTopology_map (Modification.classPushforwardOfLE hn hσ) (hconv σ)
      have e₁ : ∀ i, (extend hS (E i)).onModel π =
          Modification.classPushforwardOfLE hn hσ ((E i).onModel σ) :=
        fun i => extend_onModel hS (E i) hσ
      have e₂ : 𝔻.onModel π =
          Modification.classPushforwardOfLE hn hσ ((restrict S 𝔻).onModel σ) := by
        rw [restrict_onModel, 𝔻.pushforward_onModel]
      simp only [e₁, e₂]
      exact h

end Cofinal

end General

section Connected

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [ConnectedSpace X] {S : ModelSystem n X} {hn : 0 < n}

/-- The restriction of the all-model Cartier b-divisor realized by `(π, α)`, `π ∈ S`, is the
`S`-Cartier b-divisor realized by `(π, α)`. -/
theorem restrict_cartierOf (π : S.Model) (α : RealBottChern n π.1.carrier) :
    restrict S (WeilBDivisor.cartierOf hn π.1 α) = cartierOf hn π α :=
  (restrict_isRealization (WeilBDivisor.isRealization_cartierOf π.1 α)).eq_cartierOf

/-- **Cartier b-divisors over `S` are determined on a model**: every `S`-Cartier b-divisor is the
restriction of an all-model Cartier b-divisor with the same realization. -/
theorem exists_cartier_restrict_eq {E : WeilBDivisorOn S hn} (hE : E.IsCartier) :
    ∃ D : WeilBDivisor n X hn, D.IsCartier ∧ restrict S D = E := by
  obtain ⟨π, α, hr⟩ := hE
  exact ⟨WeilBDivisor.cartierOf hn π.1 α, WeilBDivisor.isCartier_cartierOf π.1 α,
    (restrict_cartierOf π α).trans hr.eq_cartierOf.symm⟩

/-- Every nef Cartier b-divisor over `S` is the restriction of an all-model nef Cartier
b-divisor (with the same realization). -/
theorem exists_nefCartier_restrict_eq {E : WeilBDivisorOn S hn} (hE : E.IsNefCartier) :
    ∃ D : WeilBDivisor n X hn, D.IsNefCartier ∧ restrict S D = E := by
  obtain ⟨π, α, hr, κ, hα⟩ := hE
  exact ⟨WeilBDivisor.cartierOf hn π.1 α, WeilBDivisor.isNefCartier_cartierOf π.1 α κ hα,
    (restrict_cartierOf π α).trans hr.eq_cartierOf.symm⟩

/-- The volume over all modifications is at most the volume over the models of `S`. -/
theorem vol_le_vol_restrict (D : WeilBDivisor n X hn) : D.vol ≤ (restrict S D).vol := by
  by_cases h : D.IsPseudoeffective
  · rw [WeilBDivisor.vol_of_isPseudoeffective h,
      vol_of_isPseudoeffective (restrict_isPseudoeffective h)]
    exact le_iInf fun π => iInf_le (fun π : Modification n X =>
      Modification.classVolume π (D.onModel π)) π.1
  · rw [WeilBDivisor.vol_of_not_isPseudoeffective h]
    exact zero_le

end Connected

section Positive

variable {m : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [ConnectedSpace X]
  {S : ModelSystem (m + 1) X} {hn : 0 < m + 1} (hS : S.IsCofinal)
include hS

omit [ConnectedSpace X] in
theorem isPseudoeffective_iff_restrict (D : WeilBDivisor (m + 1) X hn) :
    D.IsPseudoeffective ↔ (restrict S D).IsPseudoeffective := by
  refine ⟨fun h => restrict_isPseudoeffective h, fun h => ?_⟩
  rw [WeilBDivisor.isPseudoeffective_iff]
  intro π
  obtain ⟨σ, hσ⟩ := hS π
  rw [← D.pushforward_onModel hσ]
  exact classPseudoeffective_classPushforward (Modification.contMDiff_homOfLE hσ) hn
    (((isPseudoeffective_iff _).mp h) σ)

omit [ConnectedSpace X] in
/-- **The order is the same in both conventions** (cofinal system). -/
theorem le_iff_restrict (D D' : WeilBDivisor (m + 1) X hn) :
    D.LE D' ↔ (restrict S D).LE (restrict S D') := by
  rw [WeilBDivisor.le_iff_isPseudoeffective_sub, le_iff_isPseudoeffective_sub, ← map_sub]
  exact isPseudoeffective_iff_restrict hS (D' - D)

/-- **Volumes in both conventions agree** for a cofinal system, provided the class volume does
not decrease under push-forward along the dominations of arbitrary modifications
(`WeilBDivisor.PushforwardVolumeMonotone`; known along Kähler models, `prop:cones_modif2`). -/
theorem vol_restrict_eq (hmono : WeilBDivisor.PushforwardVolumeMonotone (m + 1) X hn)
    (D : WeilBDivisor (m + 1) X hn) : (restrict S D).vol = D.vol := by
  refine le_antisymm ?_ (vol_le_vol_restrict D)
  by_cases h : D.IsPseudoeffective
  · rw [WeilBDivisor.vol_of_isPseudoeffective h,
      vol_of_isPseudoeffective (restrict_isPseudoeffective h)]
    refine le_iInf fun π => ?_
    obtain ⟨σ, hσ⟩ := hS π
    calc ⨅ σ' : S.Model, Modification.classVolume σ'.1 ((restrict S D).onModel σ')
        ≤ Modification.classVolume σ.1 (D.onModel σ.1) := iInf_le
          (fun σ' : S.Model => Modification.classVolume σ'.1 ((restrict S D).onModel σ')) σ
      _ ≤ Modification.classVolume π
            (Modification.classPushforwardOfLE hn hσ (D.onModel σ.1)) :=
          hmono π σ.1 hσ _ (((WeilBDivisor.isPseudoeffective_iff D).mp h) σ.1)
      _ = Modification.classVolume π (D.onModel π) := by rw [D.pushforward_onModel]
  · have h' : ¬ (restrict S D).IsPseudoeffective := fun h' =>
      h ((isPseudoeffective_iff_restrict hS D).mpr h')
    rw [vol_of_not_isPseudoeffective h']
    exact zero_le

end Positive

end WeilBDivisorOn

end SGPT.BDivisor
