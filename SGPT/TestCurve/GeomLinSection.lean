import SGPT.TestCurve.GeomLinPoint
import SGPT.TestCurve.TCLinUnique

/-!
# A geometric linearization induces the `𝔾_m`-representation on sections

Let `(𝓧, 𝓛)` be a test configuration of an integral projective `(X, L)` with a
geometric `𝔾_m`-linearization `Φ : σ^* 𝓛 ≅ pr₂^* 𝓛` (`GeomLinearization`, [BHJ17, Def. 2.2]).
Then `H⁰(𝓧, 𝓛^m)` is the direct sum of the weight spaces

`weightSpace T m λ = {σ : σ|_{𝓧 ∖ 𝓧₀} = t^{-λ} q^* s for some s ∈ H⁰(X, L^m)}`,

i.e. `Φ` induces the `SectionLinearization`
(`GeomLinearization.toSectionLinearization`), and a test configuration with a geometric
linearization is a `TCLin.LinearizedTestConfiguration`
(`GeomLinearizedTestConfiguration.toLinearized`).

## Proof

* (Künneth, `exists_section_expansion`) `σ|_{𝓧 ∖ 𝓧₀} = Σ_{λ ∈ S} t^{-λ} q^* s_λ`, a finite sum.
* (Action of the points, `GeomLinearization.actSection`) for `c ∈ ℂ^*`, `ρ_c(σ) = Φ_c^m(σ_c^* σ)`
  is a global section of `𝓛^m` with `ρ_c(σ)|_{𝓧 ∖ 𝓧₀} = Σ_λ c^{-λ} t^{-λ} q^* s_λ`
  (`epsCoeff_actSection_expansion`): on `𝓧 ∖ 𝓧₀` the linearization is the canonical one,
  `σ_c^* t = c t` and `σ_c^* q^* = q^*`.
* (Interpolation, the `exists_interpolation`) choose `c_1, …, c_r ∈ ℂ^*` and
  `β_1, …, β_r` with `Σ_l β_l c_l^{-λ} = δ_{λμ}` for `λ ∈ S`; then `ξ_μ = Σ_l β_l ρ_{c_l}(σ)`
  is a global section restricting to `t^{-μ} q^* s_μ`, so `ξ_μ ∈ weightSpace T m μ`, and
  `σ = Σ_μ ξ_μ` (sections are determined on `𝓧 ∖ 𝓧₀`, `𝓧` integral).
* The weight spaces are independent (TC-LIN's `sum_mono_eq_zero`).

Only the action of the closed points of `𝔾_m` is used: the cocycle condition (which makes
`c ↦ ρ_c` a representation) is part of the definition but not needed for the weight
decomposition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.GeomLin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite SGPT.TestCurve.TestConfig SGPT.TestCurve.TestConfig.LaurentSecRing
open SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  {T : TestConfiguration f a}

/-- The constants `ℂ → Γ(𝓧, q⁻¹(V_k))`. -/
def chartConst (T : TestConfiguration f a) (k : a.I) :
    ℂ →+* Γ(T.space, overOpen T.coord (a.opens k)) :=
  (T.space.presheaf.map (homOfLE le_top).op).hom.comp (schemeGlobalConstants T.structureMap)

/-- The chart coefficient of a finite sum. -/
theorem epsCoeff_sum (T : TestConfiguration f a) (m : ℕ) (k : a.I) {ι : Type*} (t : Finset ι)
    (v : ι → SectionSpace T.structureMap T.line m) :
    T.epsCoeff m k (∑ i ∈ t, v i) = ∑ i ∈ t, T.epsCoeff m k (v i) :=
  map_sum (coeffHom T.extAtlas m (.inr k)) v t

/-- The chart coefficient of a complex multiple. -/
theorem epsCoeff_smul (T : TestConfiguration f a) (m : ℕ) (k : a.I) (β : ℂ)
    (v : SectionSpace T.structureMap T.line m) :
    T.epsCoeff m k (β • v) = chartConst T k β * T.epsCoeff m k v :=
  SectionSpace.atlasPowerGlobalCoefficients_smul_const T.structureMap T.extAtlas m (.inr k) β v

namespace GeomLinearization

variable (Λ : GeomLinearization T)

/-- `σ_c^♯ (t^n) = c^n t^n`. -/
theorem actAt_tUnit_zpow (c : ℂˣ) (k : a.I) (n : ℤ) :
    (Λ.action.actAt c).appLE (overOpen T.coord (a.opens k)) (overOpen T.coord (a.opens k))
        (Λ.action.le_actAt_overOpen c _) ((T.tUnit k ^ n).val) =
      chartConst T k ((c ^ n : ℂˣ) : ℂ) * (T.tUnit k ^ n).val := by
  let φ := ((Λ.action.actAt c).appLE (overOpen T.coord (a.opens k))
    (overOpen T.coord (a.opens k)) (Λ.action.le_actAt_overOpen c _)).hom
  have hu : Units.map φ.toMonoidHom (T.tUnit k) =
      Units.map (chartConst T k).toMonoidHom c * T.tUnit k := by
    ext
    exact Λ.action.actAt_tResOn c (a.opens k)
  have h := congrArg Units.val (congrArg (· ^ n) hu)
  simp only [← map_zpow, mul_zpow, Units.val_mul] at h
  exact h

/-- **The action of `c ∈ ℂ^*` on a Laurent expansion**: if `σ|_{𝓧 ∖ 𝓧₀} = Σ t^{-λ} q^* s_λ`,
then `ρ_c(σ)|_{𝓧 ∖ 𝓧₀} = Σ c^{-λ} t^{-λ} q^* s_λ`. -/
theorem epsCoeff_actSection_expansion (c : ℂˣ) (m : ℕ) (σ : SectionSpace T.structureMap T.line m)
    (S : Finset ℤ) (s : ℤ → SectionSpace f L m) (k : a.I)
    (hσ : T.epsCoeff m k σ = ∑ lam ∈ S, (T.tUnit k ^ (-lam)).val *
      pullFun T.coord (a.opens k) (atlasPowerGlobalCoefficients a m k (s lam))) :
    T.epsCoeff m k (Λ.actSection c m σ) = ∑ lam ∈ S, chartConst T k ((c ^ (-lam) : ℂˣ) : ℂ) *
      ((T.tUnit k ^ (-lam)).val *
        pullFun T.coord (a.opens k) (atlasPowerGlobalCoefficients a m k (s lam))) := by
  rw [Λ.epsCoeff_actSection, hσ, map_sum]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [map_mul, Λ.actAt_tUnit_zpow, Λ.action.actAt_pullFun, mul_assoc]

include Λ in
/-- **Every section is a sum of weight vectors** (for a geometric linearization). -/
theorem mem_iSup_weightSpace [IsIntegral X] (E : ClosedProjectiveEmbedding f) (m : ℕ)
    (σ : SectionSpace T.structureMap T.line m) : σ ∈ ⨆ lam, weightSpace T m lam := by
  classical
  have : IsIntegral T.space := T.isIntegral_space_of_embedding E
  obtain ⟨S, s, hexp⟩ := exists_section_expansion T m σ
  -- the weight components
  have key : ∀ μ ∈ S, ∃ ξ : SectionSpace T.structureMap T.line m, T.Extends μ m (s μ) ξ := by
    intro μ hμ
    obtain ⟨C, β, hβ⟩ := exists_interpolation (S.map (Equiv.neg ℤ).toEmbedding) (-μ)
    refine ⟨∑ c ∈ C, β c • Λ.actSection c m σ, fun k => ?_⟩
    rw [epsCoeff_sum]
    simp_rw [epsCoeff_smul, Λ.epsCoeff_actSection_expansion _ m σ S s k (hexp k),
      Finset.mul_sum]
    rw [Finset.sum_comm]
    have hδ : ∀ lam ∈ S, ∑ c ∈ C, chartConst T k (β c) *
        (chartConst T k ((c ^ (-lam) : ℂˣ) : ℂ) * ((T.tUnit k ^ (-lam)).val *
          pullFun T.coord (a.opens k) (atlasPowerGlobalCoefficients a m k (s lam)))) =
        if lam = μ then (T.tUnit k ^ (-lam)).val *
          pullFun T.coord (a.opens k) (atlasPowerGlobalCoefficients a m k (s lam)) else 0 := by
      intro lam hlam
      simp_rw [← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum]
      rw [hβ (-lam) (Finset.mem_map_of_mem _ hlam)]
      by_cases h : lam = μ
      · rw [if_pos (congrArg Neg.neg h), if_pos h, map_one, one_mul]
      · rw [if_neg (fun h' => h (neg_inj.mp h')), if_neg h, map_zero, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl hδ, Finset.sum_ite_eq' S μ, if_pos hμ]
  choose ξ hξ using key
  -- `σ` is the sum of its weight components
  have hσ : σ = ∑ μ ∈ S.attach, ξ μ.1 μ.2 := by
    apply T.eq_of_epsCoeff_eq
    intro k
    rw [epsCoeff_sum, hexp k]
    rw [← Finset.sum_attach S]
    exact Finset.sum_congr rfl fun μ _ => (hξ μ.1 μ.2 k).symm
  rw [hσ]
  exact Submodule.sum_mem _ fun μ _ =>
    Submodule.mem_iSup_of_mem μ.1 ⟨s μ.1, hξ μ.1 μ.2⟩

end GeomLinearization

/-- **The weight spaces are independent** (`X` integral projective): weight vectors of distinct
weights summing to zero vanish. -/
theorem iSupIndep_weightSpace [IsIntegral X] (E : ClosedProjectiveEmbedding f)
    (T : TestConfiguration f a) (m : ℕ) : iSupIndep (weightSpace T m) := by
  classical
  have : IsIntegral T.space := T.isIntegral_space_of_embedding E
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro S v hv hsum i hi
  choose u hu using hv
  let u' : ℤ → SectionSpace f L m := fun j => if hj : j ∈ S then u j hj else 0
  have hu' : ∀ j ∈ S, T.Extends (id j) m (u' j) (v j) := by
    intro j hj
    simp only [u', id, dif_pos hj]
    exact hu j hj
  have hmono := sum_mono_eq_zero T S id m u' v hu' hsum
  have hc := congrArg (coeffAt (-i) m) hmono
  rw [map_sum, Finset.sum_eq_single i] at hc
  · rw [id, coeffAt_mono_same, map_zero] at hc
    have hext := hu' i hi
    rw [hc] at hext
    exact eq_zero_of_extends_zero hext
  · intro j _ hji
    rw [coeffAt_mono, dif_neg (fun h => hji (neg_inj.mp h.1))]
  · intro h
    exact absurd hi h

namespace GeomLinearization

/-- **A geometric `𝔾_m`-linearization induces the `𝔾_m`-representation on the sections**
(the `SectionLinearization`): for `X` integral projective, `H⁰(𝓧, 𝓛^m)` is the
direct sum of the weight spaces `weightSpace T m λ`. -/
def toSectionLinearization [IsIntegral X] (E : ClosedProjectiveEmbedding f)
    (Λ : GeomLinearization T) : SectionLinearization T where
  weight := weightSpace T
  isInternal m := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_weightSpace E T m) (eq_top_iff.mpr fun σ _ => Λ.mem_iSup_weightSpace E m σ)
  compat _ _ := le_rfl

theorem toSectionLinearization_weight [IsIntegral X] (E : ClosedProjectiveEmbedding f)
    (Λ : GeomLinearization T) (m : ℕ) (lam : ℤ) :
    (Λ.toSectionLinearization E).weight m lam = weightSpace T m lam :=
  rfl

end GeomLinearization

/-- **A test configuration with a geometric linearization** ([BHJ17, Def. 2.1–2.3]) is a
linearized test configuration in the sense of lane TC-LIN (`X` integral projective). -/
def GeomLinearizedTestConfiguration.toLinearized [IsIntegral X] (E : ClosedProjectiveEmbedding f)
    (T : GeomLinearizedTestConfiguration f a) : LinearizedTestConfiguration f a where
  toTestConfiguration := T.toTestConfiguration
  isGmEquivariant := T.isGmEquivariant
  linearization := T.linearization.toSectionLinearization E

end SGPT.TestCurve.GeomLin
