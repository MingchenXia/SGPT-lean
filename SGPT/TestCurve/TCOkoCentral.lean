import SGPT.TestCurve.TCLinUnique
import SGPT.TestCurve.TCLinMain
import SGPT.TestCurve.TestConfigJumpMeasure

/-!
# Weights of the reduction modulo `t` and jumping numbers (the [BHJ17] dictionary)

Source: `rmk:NApotential:L862` (chapter *Non-Archimedean pluripotential theory*): *"our
Duistermaat–Heckman measure coincides with the more traditional definition of [BHJ17, §3.2]"*.
The traditional definition takes the weights of the `ℂ^*`-action on `H⁰(𝓧₀, k𝓛₀)`; the formal
statements of lanes NA-NS/TC-ENC/TC-LIN use the jumping measures `ν_k` of the induced filtration
`𝓕`, which [BHJ17, §2.5] identifies with those weights. Lane TC-OKO, blueprint `claude-tc-oko`.

For a test configuration `(𝓧, 𝓛)` with a `𝔾_m`-linearization (lane TC-LIN's
`SectionLinearization`: `H⁰(𝓧, m𝓛) = ⊕_λ V_{m,λ}`, `V_{m,λ}` the sections restricting to
`t^{-λ} q^* s`), multiplication by `t` maps `V_{m,λ+1}` to `V_{m,λ}`, so the `ℂ^*`-representation
descends to the reduction modulo `t`,

`H⁰(𝓧, m𝓛) / t H⁰(𝓧, m𝓛) = ⊕_λ (V_{m,λ} / t V_{m,λ+1})`,

and this file proves the dictionary of [BHJ17, §2.5] for it:

* `centralWeight_isInternal`: the weight decomposition of `H⁰(𝓧, m𝓛) / t H⁰(𝓧, m𝓛)`;
* `finrank_centralWeight_add`: `dim (weight-λ part) = dim 𝓕^λ_m - dim 𝓕^{λ+1}_m`, i.e. the
  weight-`λ` part is `gr^λ_𝓕 H⁰(X, L^m)`;
* `centralWeightMeasure_Ici`, **`centralWeightMeasure_eq_jumpMeasure`**: the weight measure
  `∑_λ dim(weight-λ part) δ_{λ/m}` of the reduction modulo `t` is the jumping measure `ν_m` of
  the induced filtration (`m > 0`, finitely generated filtration);
* `linearized_centralWeight_tendsto`: for ample linearized test configurations, the rescaled
  weight measures of the reduction modulo `t` converge weakly to the book's `DH(Γ^𝓕)`
  (`rmk:NApotential:L862` stated with `ℂ^*`-weights; TC-LIN's convergence).

Not formalized: the identification `H⁰(𝓧₀, m𝓛₀) = H⁰(𝓧, m𝓛) / t H⁰(𝓧, m𝓛)` for `m ≫ 0`
(cohomology and base change along `0 ∈ 𝔸¹` with relative Serre vanishing of `H¹(𝓧, m𝓛)`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCOko

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Opposite MeasureTheory Set
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin SGPT.TestCurve.FGRel
open scoped ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

/-! ### Multiplication by `t` -/

/-- Multiplication by `t ∘ π` on `H⁰(𝓧, 𝓛^m)`. -/
def tMul (m : ℕ) :
    SectionSpace T.structureMap T.line m →ₗ[ℂ] SectionSpace T.structureMap T.line m where
  toFun σ := (show SectionSpace T.structureMap T.line m from
    (tFun T.toLine) • (show bundlePowerGlobalSections T.line m from σ))
  map_add' σ σ' := by
    change (tFun T.toLine) • ((show bundlePowerGlobalSections T.line m from σ) +
        (show bundlePowerGlobalSections T.line m from σ')) =
      (tFun T.toLine) • (show bundlePowerGlobalSections T.line m from σ) +
        (tFun T.toLine) • (show bundlePowerGlobalSections T.line m from σ')
    exact smul_add _ _ _
  map_smul' c σ := by
    change (tFun T.toLine) • (schemeGlobalConstants T.structureMap c •
        (show bundlePowerGlobalSections T.line m from σ)) =
      schemeGlobalConstants T.structureMap c •
        ((tFun T.toLine) • (show bundlePowerGlobalSections T.line m from σ))
    rw [smul_smul, smul_smul, mul_comm]

theorem tMul_apply (m : ℕ) (σ : SectionSpace T.structureMap T.line m) :
    tMul T m σ = (show SectionSpace T.structureMap T.line m from
      (tFun T.toLine) • (show bundlePowerGlobalSections T.line m from σ)) := rfl

variable {T}

/-- If `σ` extends `t^{-λ} s̄`, then `t σ` extends `t^{-(λ-1)} s̄`. -/
theorem extends_tMul {lam : ℤ} {m : ℕ} {s : SectionSpace f L m}
    {σ : SectionSpace T.structureMap T.line m} (h : T.Extends lam m s σ) :
    T.Extends (lam - 1) m s (tMul T m σ) := by
  have h1 := T.extends_tpow h 1
  rw [pow_one, Nat.cast_one] at h1
  exact h1

/-- The coefficients of `t σ` are those of `σ` times `t` (a unit on `q⁻¹(V_j)`). -/
theorem epsCoeff_tMul (m : ℕ) (j : a.I) (σ : SectionSpace T.structureMap T.line m) :
    T.epsCoeff m j (tMul T m σ) = (T.tUnit j).val * T.epsCoeff m j σ := by
  simp only [TestConfiguration.epsCoeff]
  rw [tMul_apply, atlasPowerGlobalCoefficients_smul]
  rfl

/-- **Division by `t` off the central fibre**: if `t σ` extends `t^{-λ} s̄`, then `σ` extends
`t^{-(λ+1)} s̄` (`t` is a unit on `𝓧 ∖ 𝓧₀`). -/
theorem extends_of_extends_tMul {lam : ℤ} {m : ℕ} {s : SectionSpace f L m}
    {σ : SectionSpace T.structureMap T.line m} (h : T.Extends lam m s (tMul T m σ)) :
    T.Extends (lam + 1) m s σ := by
  intro j
  have e1 := h j
  rw [epsCoeff_tMul] at e1
  have key : T.epsCoeff m j σ =
      (T.tUnit j)⁻¹.val * ((T.tUnit j).val * T.epsCoeff m j σ) := by
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [key, e1, ← mul_assoc, ← Units.val_mul]
  congr 2
  rw [← zpow_neg_one, ← zpow_add]
  congr 1
  ring

/-! ### The reduction modulo `t` and its weights -/

variable (T)

/-- `H⁰(𝓧, 𝓛^m) / t H⁰(𝓧, 𝓛^m)`, the reduction modulo `t` of the sections (the sections of the
central fibre `H⁰(𝓧₀, 𝓛₀^m)` for `m ≫ 0`, [BHJ17, §2.5]). -/
abbrev CentralQuotient (m : ℕ) : Type :=
  SectionSpace T.structureMap T.line m ⧸ LinearMap.range (tMul T m)

/-- The weight-`λ` part of `H⁰(𝓧, 𝓛^m) / t H⁰(𝓧, 𝓛^m)`: the image of `V_{m,λ}`. -/
def centralWeight (m : ℕ) (lam : ℤ) : Submodule ℂ (CentralQuotient T m) :=
  (weightSpace T m lam).map (LinearMap.range (tMul T m)).mkQ

variable [IsIntegral X] (E : ClosedProjectiveEmbedding f)

include E in
/-- A section extends at most one... and `t^{-λ} s̄` extends in at most one way (`𝓧` integral). -/
theorem extends_eq {lam : ℤ} {m : ℕ} {s : SectionSpace f L m}
    {σ σ' : SectionSpace T.structureMap T.line m} (h : T.Extends lam m s σ)
    (h' : T.Extends lam m s σ') : σ = σ' := by
  have := T.isIntegral_space_of_embedding E
  exact T.eq_of_epsCoeff_eq fun j => by rw [h j, h' j]

/-- The extension `σ` of `t^{-λ} s̄`, for `s ∈ 𝓕^λ_m`, as a linear map `𝓕^λ_m → H⁰(𝓧, 𝓛^m)`. -/
def extendMap (lam : ℤ) (m : ℕ) :
    T.piece lam m →ₗ[ℂ] SectionSpace T.structureMap T.line m where
  toFun s := Classical.choose s.2
  map_add' s s' := by
    refine (extends_eq T E (Classical.choose_spec (s + s').2) ?_)
    exact TestConfiguration'.extends_add T (Classical.choose_spec s.2) (Classical.choose_spec s'.2)
  map_smul' c s := by
    refine (extends_eq T E (Classical.choose_spec (c • s).2) ?_)
    exact TestConfiguration'.extends_smul T (Classical.choose_spec s.2) c

theorem extendMap_extends (lam : ℤ) (m : ℕ) (s : T.piece lam m) :
    T.Extends lam m s (extendMap T E lam m s) :=
  Classical.choose_spec s.2

/-- `𝓕^λ_m → H⁰(𝓧, 𝓛^m) / t H⁰(𝓧, 𝓛^m)`, `s ↦ [σ]`, `σ` extending `t^{-λ} s̄`. -/
def centralMap (lam : ℤ) (m : ℕ) : T.piece lam m →ₗ[ℂ] CentralQuotient T m :=
  (LinearMap.range (tMul T m)).mkQ ∘ₗ extendMap T E lam m

theorem range_centralMap (lam : ℤ) (m : ℕ) :
    LinearMap.range (centralMap T E lam m) = centralWeight T m lam := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, ⟨s, extendMap_extends T E lam m s⟩, rfl⟩
  · rintro ⟨σ, ⟨s, hs⟩, rfl⟩
    refine ⟨⟨s, σ, hs⟩, ?_⟩
    change (LinearMap.range (tMul T m)).mkQ (extendMap T E lam m ⟨s, σ, hs⟩) = _
    rw [extends_eq T E (extendMap_extends T E lam m ⟨s, σ, hs⟩) hs]

/-- **The kernel of `𝓕^λ_m → (H⁰(𝓧, 𝓛^m) / t)_λ` is `𝓕^{λ+1}_m`.** -/
theorem mem_ker_centralMap (lam : ℤ) (m : ℕ) (s : T.piece lam m) :
    s ∈ LinearMap.ker (centralMap T E lam m) ↔ (s : SectionSpace f L m) ∈ T.piece (lam + 1) m := by
  rw [LinearMap.mem_ker]
  change (LinearMap.range (tMul T m)).mkQ (extendMap T E lam m s) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y, hy⟩
    have h := extendMap_extends T E lam m s
    rw [← hy] at h
    exact ⟨y, extends_of_extends_tMul h⟩
  · rintro ⟨σ', hσ'⟩
    refine ⟨σ', ?_⟩
    have h := extends_tMul hσ'
    rw [add_sub_cancel_right] at h
    exact extends_eq T E h (extendMap_extends T E lam m s)

include E in
/-- **The weight-`λ` part of `H⁰(𝓧, 𝓛^m) / t H⁰(𝓧, 𝓛^m)` is `gr^λ_𝓕 H⁰(X, L^m)`**:
`dim (H⁰(𝓧, 𝓛^m) / t)_λ + dim 𝓕^{λ+1}_m = dim 𝓕^λ_m`. -/
theorem finrank_centralWeight_add (lam : ℤ) (m : ℕ) :
    Module.finrank ℂ (centralWeight T m lam) + Module.finrank ℂ (T.piece (lam + 1) m) =
      Module.finrank ℂ (T.piece lam m) := by
  have := SectionSpace.finiteDimensional f E a m
  have hrn := LinearMap.finrank_range_add_finrank_ker (centralMap T E lam m)
  rw [range_centralMap] at hrn
  have hker : LinearMap.ker (centralMap T E lam m) =
      Submodule.comap (T.piece lam m).subtype (T.piece (lam + 1) m) := by
    ext s
    rw [mem_ker_centralMap]
    rfl
  rw [hker, (Submodule.comapSubtypeEquivOfLe (T.piece_anti (by omega) m)).finrank_eq] at hrn
  exact hrn

include E in
/-- **The weight decomposition of the reduction modulo `t`**: for a `𝔾_m`-linearized `𝓛`,
`H⁰(𝓧, 𝓛^m) / t H⁰(𝓧, 𝓛^m) = ⊕_λ (V_{m,λ} mod t)`. -/
theorem centralWeight_isInternal (P : SectionLinearization T) (m : ℕ) :
    DirectSum.IsInternal (centralWeight T m) := by
  classical
  have hint : DirectSum.IsInternal (weightSpace T m) := by
    have h := P.isInternal m
    rwa [show P.weight m = weightSpace T m from funext (P.weight_eq E m)] at h
  have hind := hint.submodule_iSupIndep
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    rintro x ⟨v, hv, rfl⟩ hx
    have hx' : (LinearMap.range (tMul T m)).mkQ v ∈
        (⨆ (j : ℤ) (_ : j ≠ i), weightSpace T m j).map (LinearMap.range (tMul T m)).mkQ := by
      rw [Submodule.map_iSup]
      simp_rw [Submodule.map_iSup]
      exact hx
    obtain ⟨w, hw, hvw⟩ := hx'
    have hdiff : v - w ∈ LinearMap.range (tMul T m) := by
      rw [← Submodule.Quotient.eq]
      exact hvw.symm
    obtain ⟨y, hy⟩ := hdiff
    have hymem : y ∈ ⨆ μ, weightSpace T m μ := by
      rw [hint.submodule_iSup_eq_top]
      trivial
    obtain ⟨c, hc, hcy⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hymem
    have htc : ∀ μ, tMul T m (c μ) ∈ weightSpace T m (μ - 1) := fun μ => by
      obtain ⟨s, hs⟩ := hc μ
      exact ⟨s, extends_tMul hs⟩
    set u := tMul T m (c (i + 1)) with hu
    have hu_mem : u ∈ weightSpace T m i := by
      have := htc (i + 1)
      rwa [add_sub_cancel_right] at this
    -- `t y - u` lies in `⨆_{j ≠ i} V_j`
    have hrest : tMul T m y - u ∈ ⨆ (j : ℤ) (_ : j ≠ i), weightSpace T m j := by
      have hsum : tMul T m y = ∑ μ ∈ c.support, tMul T m (c μ) := by
        rw [← hcy, Finsupp.sum, map_sum]
      have hsplit : ∑ μ ∈ c.support, tMul T m (c μ) =
          (∑ μ ∈ c.support.filter (fun μ => μ = i + 1), tMul T m (c μ)) +
            ∑ μ ∈ c.support.filter (fun μ => ¬ μ = i + 1), tMul T m (c μ) :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have hfirst : ∑ μ ∈ c.support.filter (fun μ => μ = i + 1), tMul T m (c μ) = u := by
        rw [Finset.sum_filter, Finset.sum_ite_eq']
        split_ifs with hmem
        · rfl
        · rw [hu, Finsupp.notMem_support_iff.mp hmem, map_zero]
      rw [hsum, hsplit, hfirst, add_sub_cancel_left]
      refine Submodule.sum_mem _ fun μ hμ => ?_
      have hμ' : μ - 1 ≠ i := by
        have := (Finset.mem_filter.mp hμ).2
        omega
      exact Submodule.mem_iSup_of_mem (μ - 1) (Submodule.mem_iSup_of_mem hμ' (htc μ))
    -- hence `v - u ∈ V_i ∩ ⨆_{j ≠ i} V_j = 0`
    have hvu : v - u = w + (tMul T m y - u) := by
      rw [hy]
      abel
    have hzero : v - u = 0 := by
      have hd := (iSupIndep_def.mp hind) i
      rw [Submodule.disjoint_def] at hd
      refine hd (v - u) (Submodule.sub_mem _ hv hu_mem) ?_
      rw [hvu]
      exact Submodule.add_mem _ hw hrest
    have hvu' : v = u := sub_eq_zero.mp hzero
    rw [hvu', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨c (i + 1), rfl⟩
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (tMul T m)) x
    have hv : v ∈ ⨆ μ, weightSpace T m μ := by
      rw [hint.submodule_iSup_eq_top]
      trivial
    have : (LinearMap.range (tMul T m)).mkQ v ∈
        (⨆ μ, weightSpace T m μ).map (LinearMap.range (tMul T m)).mkQ := ⟨v, hv, rfl⟩
    rwa [Submodule.map_iSup] at this

/-! ### The weight measure of the reduction modulo `t` -/

/-- **Telescoping**: if `d l + a (l + 1) = a l` and `a l = 0` for `l ≥ B`, then
`∑_{l ≥ L} d l = a L`. -/
theorem tsum_ite_le_eq {d c : ℤ → ℕ} (hdc : ∀ l, d l + c (l + 1) = c l) {B : ℤ}
    (hB : ∀ l, B ≤ l → c l = 0) (L : ℤ) :
    ∑' l : ℤ, (if L ≤ l then (d l : ℝ≥0∞) else 0) = c L := by
  classical
  have htel : ∀ n : ℕ, (∑ i ∈ Finset.range n, d (L + i)) + c (L + n) = c L := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := hdc (L + n)
      push_cast
      rw [add_assoc] at h
      omega
  set n := (B - L).toNat with hn
  have hLn : B ≤ L + n := by omega
  have hsum : ∑ i ∈ Finset.range n, d (L + i) = c L := by
    have := htel n
    rw [hB _ hLn, add_zero] at this
    exact this
  have hd0 : ∀ l, B ≤ l → d l = 0 := fun l hl => by
    have := hdc l
    rw [hB l hl, hB (l + 1) (by omega)] at this
    omega
  let g : ℕ → ℤ := fun i => L + i
  have hg : Function.Injective g := fun i j h => by
    simp only [g] at h
    exact_mod_cast add_left_cancel h
  rw [tsum_eq_sum (s := (Finset.range n).image g)]
  · rw [Finset.sum_image fun i _ j _ h => hg h]
    rw [← hsum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos (by simp [g])]
  · intro l hl
    split_ifs with hLl
    · have hBl : B ≤ l := by
        by_contra hlt
        apply hl
        refine Finset.mem_image.mpr ⟨(l - L).toNat, Finset.mem_range.mpr (by omega), ?_⟩
        simp only [g]
        omega
      rw [hd0 l hBl, Nat.cast_zero]
    · rfl

/-- **The weight measure** `∑_λ dim (H⁰(𝓧, 𝓛^m) / t)_λ · δ_{λ/m}` of the `ℂ^*`-representation on
the reduction modulo `t` (the measure of [BHJ17, §3.2] before normalization, for the reduction
modulo `t` in place of `H⁰(𝓧₀, m𝓛₀)`). -/
def centralWeightMeasure (m : ℕ) : Measure ℝ :=
  Measure.sum fun lam : ℤ =>
    (Module.finrank ℂ (centralWeight T m lam) : ℝ≥0∞) • Measure.dirac ((lam : ℝ) / m)

include E in
/-- **Tails of the weight measure**: `w_m [τ, ∞) = dim 𝓕^{⌈mτ⌉}_m` (`m > 0`). -/
theorem centralWeightMeasure_Ici {m : ℕ} (hm : 0 < m) (τ : ℝ) :
    centralWeightMeasure T m (Ici τ) = Module.finrank ℂ (T.piece ⌈(m : ℝ) * τ⌉ m) := by
  classical
  have := SectionSpace.finiteDimensional f E a m
  have := T.isIntegral_space_of_embedding E
  obtain ⟨B, hB⟩ := T.exists_piece_eq_bot m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [centralWeightMeasure, Measure.sum_apply _ measurableSet_Ici]
  have hterm : ∀ lam : ℤ, ((Module.finrank ℂ (centralWeight T m lam) : ℝ≥0∞) •
      Measure.dirac ((lam : ℝ) / m)) (Ici τ) =
      if ⌈(m : ℝ) * τ⌉ ≤ lam then (Module.finrank ℂ (centralWeight T m lam) : ℝ≥0∞) else 0 := by
    intro lam
    rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ici, smul_eq_mul]
    have hiff : (lam : ℝ) / m ∈ Ici τ ↔ ⌈(m : ℝ) * τ⌉ ≤ lam := by
      rw [Set.mem_Ici, le_div_iff₀ hmR, Int.ceil_le, mul_comm]
    by_cases h : ⌈(m : ℝ) * τ⌉ ≤ lam
    · rw [Set.indicator_of_mem (hiff.mpr h), if_pos h, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
  simp_rw [hterm]
  refine tsum_ite_le_eq (d := fun l => Module.finrank ℂ (centralWeight T m l))
    (c := fun l => Module.finrank ℂ (T.piece l m)) (fun l => finrank_centralWeight_add T E l m)
    (B := B) (fun l hl => ?_) _
  rw [eq_bot_iff.mpr ((T.piece_anti hl m).trans (le_of_eq hB)), finrank_bot]

include E in
/-- **The [BHJ17, §2.5] dictionary for the reduction modulo `t`**: for a test configuration with
finitely generated induced filtration `𝓕` and `m > 0`, the weight measure
`∑_λ dim (H⁰(𝓧, 𝓛^m) / t H⁰(𝓧, 𝓛^m))_λ δ_{λ/m}` of the `ℂ^*`-representation on the reduction
modulo `t` is the jumping measure `ν_m = ∑_j δ_{λ^{(m)}_j / m}` of `𝓕`: the weights, with
multiplicities, are the jumping numbers of `𝓕` (successive minima). -/
theorem centralWeightMeasure_eq_jumpMeasure (hfg : T.FiltrationFinitelyGenerated E) {m : ℕ}
    (hm : 0 < m) :
    centralWeightMeasure T m = (T.inducedFiltration E hfg).jumpMeasure m := by
  have := SectionSpace.finiteDimensional f E a m
  have hfin : IsFiniteMeasure ((T.inducedFiltration E hfg).jumpMeasure m) :=
    ⟨by rw [SectionFiltration.jumpMeasure_univ]; exact ENNReal.natCast_lt_top _⟩
  refine (Measure.ext_of_Ici _ _ fun τ => ?_).symm
  rw [SectionFiltration.jumpMeasure_Ici _ hm, centralWeightMeasure_Ici T E hm]
  rfl

/-- **The dictionary for ample linearized test configurations** ([BHJ17, Def. 2.1–2.3]): the
weight decomposition of `H⁰(𝓧, 𝓛^m) / t H⁰(𝓧, 𝓛^m)` induced by the linearization, and for
`m > 0` its weight measure is the jumping measure of the induced filtration. -/
theorem linearized_centralWeight (T : LinearizedTestConfiguration f a) (hA : T.IsAmple) (m : ℕ) :
    DirectSum.IsInternal (centralWeight T.toTestConfiguration m) ∧
      (0 < m → centralWeightMeasure T.toTestConfiguration m =
        (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)).jumpMeasure m) :=
  ⟨centralWeight_isInternal T.toTestConfiguration E T.linearization m,
    fun hm => centralWeightMeasure_eq_jumpMeasure T.toTestConfiguration E _ hm⟩

/-! ### The [BHJ17, §3.2] Duistermaat–Heckman measure from the weights modulo `t` -/

section DH

open Filter Topology SGPT.Okounkov SGPT.NAPotential.NANS.TestConfig
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f}

local instance tcOkoDHTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance tcOkoDHCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance tcOkoDHManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance tcOkoDHMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance tcOkoDHBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L}
  (H : SchemeLineBundleMetric f (m + 1) E L)
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **`rmk:NApotential:L862` in terms of `ℂ^*`-weights**: for an ample test configuration with a
`𝔾_m`-linearized `𝓛`, `θ = c₁(L, h)` Kähler and `X` with a smooth flag, the rescaled weight
measures `(n!/kⁿ) ∑_λ dim (H⁰(𝓧, k𝓛)/t)_λ δ_{λ/k}` of the `ℂ^*`-representation on the reduction
modulo `t` (`k = j + 1`) are the measures `rescaledFiniteMeasure` of the induced filtration, and
they converge weakly to the book's `DH(Γ^𝓕)`. -/
theorem linearized_centralWeight_tendsto (T : LinearizedTestConfiguration f a) (hA : T.IsAmple)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    (∀ j : ℕ, ((rescaledFiniteMeasure (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA))
        (m + 1) j : FiniteMeasure ℝ) : Measure ℝ) =
        (((m + 1).factorial : ℝ≥0∞) / ((j + 1 : ℕ) : ℝ≥0∞) ^ (m + 1)) •
          centralWeightMeasure T.toTestConfiguration (j + 1)) ∧
    Tendsto (fun j : ℕ => rescaledFiniteMeasure
        (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) (m + 1) j) atTop
      (𝓝 (filtrationDHFinite (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA))
        H Y hY hbig)) := by
  refine ⟨fun j => ?_, linearized_rescaledJumpMeasure_tendsto H Y hY T hA hK hbig⟩
  rw [centralWeightMeasure_eq_jumpMeasure T.toTestConfiguration E _ (Nat.succ_pos j)]
  rfl

end DH

end SGPT.TestCurve.TCOko
