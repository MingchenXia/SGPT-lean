import SGPT.TestCurve.TCEncZFiltration
import SGPT.TestCurve.FGRelAssembly
import SGPT.TestCurve.FGRelDivision

/-!
# The saturation condition for the filtration of a test configuration

See [BHJ17, Prop. 2.15]. Let `(𝓧, 𝓛)` be a test configuration of `(X, L)` and let
`ξ_i ∈ H⁰(𝓧, 𝓛^r)` be sections without common zeros which are weight vectors: `ξ_i` extends
`t^{-w_i} q^* y_i` (`TestConfiguration.Extends (w i) r (y i) (ξ i)`); for an ample test
configuration embedded equivariantly in `ℙᴺ × 𝔸¹` by `𝓛^r` these are the coordinate sections.
Then the induced filtration satisfies the saturation condition of
`FGRel.mono_mem_polAlg_of_large` (`saturation_of_weightSections`): if
`x_i^D · t^j s ∈ ℂ[t, x]` for every `i`, then `t^j s̄` extends to `𝓧`. Indeed the extensions
`Σ_i` of `x_i^D t^j s̄` satisfy `Σ_i ξ_{i'}^D = Σ_{i'} ξ_i^D`, so `Σ_i / ξ_i^D` glue
(`FGRel.exists_section_mul_eq`) to a section extending `t^j s̄`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.FGRel

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Opposite
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TestConfig.LaurentSecRing SGPT.TestCurve.TCEnc

/-! ### Powers of sections -/

section Pow

variable {Z : Scheme} {g : Z ⟶ Spec (.of ℂ)} {M : Z.Modules} (b : LineBundleAtlas M)

/-- The power `σ^D ∈ H⁰(Z, M^{rD})` of `σ ∈ H⁰(Z, M^r)`. -/
def secPow {r : ℕ} (σ : SectionSpace g M r) : (D : ℕ) → SectionSpace g M (r * D)
  | 0 => secOne g M
  | D + 1 => SectionSpace.mul g b (r * D) r (secPow σ D) σ

theorem coeff_secPow {r : ℕ} (σ : SectionSpace g M r) (D : ℕ) (c : b.I) :
    atlasPowerGlobalCoefficients b (r * D) c (secPow b σ D) =
      atlasPowerGlobalCoefficients b r c σ ^ D := by
  induction D with
  | zero =>
    change atlasPowerGlobalCoefficients b 0 c (bundlePowerGlobalOne M) = _
    rw [pow_zero]
    exact atlasPowerGlobalCoefficients_one b c
  | succ D ih =>
    change atlasPowerGlobalCoefficients b (r * D + r) c
      (SectionSpace.mul g b (r * D) r (secPow b σ D) σ) = _
    rw [SectionSpace.coefficients_mul, ih, pow_succ]

end Pow

section Rees

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}

theorem coordElt_pow {N r : ℕ} (w : Fin (N + 1) → ℤ) (y : Fin (N + 1) → SectionSpace f L r)
    (i : Fin (N + 1)) (D : ℕ) :
    coordElt a w y i ^ D = mono (-((D : ℤ) * w i)) (r * D) (secPow a (y i) D) := by
  induction D with
  | zero =>
    rw [pow_zero, one_eq_mono]
    congr 1
    simp
  | succ D ih =>
    rw [pow_succ, ih, coordElt, mono_mul_mono]
    congr 1
    push_cast
    ring

/-- The bihomogeneous coefficients of an element of the Rees algebra lie in the filtration. -/
theorem coeffAt_mem_piece_of_mem_rees (F : SectionZFiltration f a) (h0 : F.piece 0 0 = ⊤)
    {z : LaurentSecRing f a} (hz : z ∈ F.rees) (j : ℤ) (m : ℕ) :
    coeffAt j m z ∈ F.piece (-j) m := by
  obtain ⟨S, hS, hzS⟩ := F.exists_finset_of_mem_rees hz
  have hle : Submodule.span ℂ (S : Set (LaurentSecRing f a)) ≤
      monoSpan (a := a) (fun j m => F.piece (-j) m) := by
    rw [Submodule.span_le]
    intro x hx
    rcases hS hx with ⟨μ, m', s, hs, rfl⟩ | hx1
    · exact mono_mem_monoSpan _ (by rwa [neg_neg])
    · rw [Set.mem_singleton_iff.mp hx1, one_eq_mono]
      exact mono_mem_monoSpan _ (by rw [neg_zero, h0]; exact Submodule.mem_top)
  exact coeffAt_mem_of_mem_monoSpan _ (hle hzS) j m

end Rees

/-! ### Extensions -/

namespace TestConfiguration'

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

theorem pullFun_one (V : X.Opens) : pullFun T.coord V 1 = 1 := map_one _

theorem extends_mul {lam lam' : ℤ} {m m' : ℕ} {s : SectionSpace f L m} {s' : SectionSpace f L m'}
    {σ : SectionSpace T.structureMap T.line m} {σ' : SectionSpace T.structureMap T.line m'}
    (h : T.Extends lam m s σ) (h' : T.Extends lam' m' s' σ') :
    T.Extends (lam + lam') (m + m') (SectionSpace.mul f a m m' s s')
      (SectionSpace.mul T.structureMap T.extAtlas m m' σ σ') := by
  intro j
  have e1 := h j
  have e2 := h' j
  simp only [TestConfiguration.epsCoeff] at e1 e2 ⊢
  rw [SectionSpace.coefficients_mul, SectionSpace.coefficients_mul, e1, e2, map_mul,
    neg_add, zpow_add, Units.val_mul]
  ring

theorem extends_one :
    T.Extends 0 0 (secOne f L) (secOne T.structureMap T.line) := by
  intro j
  simp only [TestConfiguration.epsCoeff, neg_zero, zpow_zero, Units.val_one, one_mul]
  simp only [secOne]
  erw [atlasPowerGlobalCoefficients_one, atlasPowerGlobalCoefficients_one, map_one]

theorem extends_secPow {lam : ℤ} {r : ℕ} {s : SectionSpace f L r}
    {σ : SectionSpace T.structureMap T.line r} (h : T.Extends lam r s σ) (D : ℕ) :
    T.Extends ((D : ℤ) * lam) (r * D) (secPow a s D) (secPow T.extAtlas σ D) := by
  induction D with
  | zero =>
    rw [Nat.cast_zero, zero_mul]
    exact extends_one T
  | succ D ih =>
    have := extends_mul T ih h
    have e : (D : ℤ) * lam + lam = ((D + 1 : ℕ) : ℤ) * lam := by push_cast; ring
    rw [e] at this
    exact this

end TestConfiguration'

/-! ### The saturation condition -/

open TestConfiguration' in
/-- **Saturation for test configurations.** If the weight sections `ξ_i` (extending
`t^{-w_i} q^* y_i`) have no common zeros, then every `t^j s` with `x_i^D t^j s ∈ ℂ[t, x]` for
all `i` lies in the Rees algebra of the induced filtration: `t^j s̄` extends to `𝓧`. -/
theorem saturation_of_weightSections {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
    {a : LineBundleAtlas L} [IsIntegral X] (E : ClosedProjectiveEmbedding f)
    (T : TestConfiguration f a) {N r : ℕ} (w : Fin (N + 1) → ℤ)
    (y : Fin (N + 1) → SectionSpace f L r) (ξ : Fin (N + 1) → SectionSpace T.structureMap T.line r)
    (hext : ∀ i, T.Extends (w i) r (y i) (ξ i))
    (hcov : ∀ c : T.extAtlas.I, T.extAtlas.opens c ≤
      ⨆ i, T.space.basicOpen (atlasPowerGlobalCoefficients T.extAtlas r c (ξ i)))
    (k : ℕ) (j : ℤ) (s : SectionSpace f L (r * k))
    (h : ∀ i, ∃ D : ℕ, coordElt a w y i ^ D * mono j (r * k) s ∈ polAlg a w y) :
    s ∈ T.piece (-j) (r * k) := by
  classical
  have hXi : IsIntegral T.space := T.isIntegral_space_of_embedding E
  have hpol : polAlg a w y ≤ (T.zFiltration E).rees := by
    apply Algebra.adjoin_le
    rintro z (rfl | ⟨i, rfl⟩)
    · exact SectionZFiltration'.tElt_mem_rees _ (T.zFiltration_piece_zero_zero E)
    · exact (T.zFiltration E).mono_mem_rees (T.mem_piece.mpr ⟨ξ i, hext i⟩)
  choose D hD using h
  set D0 := ∑ i, D i with hD0def
  have hD0 : ∀ i, coordElt a w y i ^ D0 * mono j (r * k) s ∈ polAlg a w y := by
    intro i
    have hle : D i ≤ D0 := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [show D0 = (D0 - D i) + D i by omega, pow_add, mul_assoc]
    exact mul_mem (pow_mem (coordElt_mem_polAlg a w y i) _) (hD i)
  -- the extensions `Σ_i` of `x_i^{D₀} t^j s̄`
  have hSg : ∀ i, ∃ Sg : SectionSpace T.structureMap T.line (r * D0 + r * k),
      T.Extends ((D0 : ℤ) * w i - j) (r * D0 + r * k)
        (SectionSpace.mul f a (r * D0) (r * k) (secPow a (y i) D0) s) Sg := by
    intro i
    have hm := hpol (hD0 i)
    rw [coordElt_pow, mono_mul_mono] at hm
    have := coeffAt_mem_piece_of_mem_rees (T.zFiltration E) (T.zFiltration_piece_zero_zero E) hm
      (-((D0 : ℤ) * w i) + j) (r * D0 + r * k)
    rw [coeffAt_mono_same, show -(-((D0 : ℤ) * w i) + j) = (D0 : ℤ) * w i - j by ring] at this
    exact this
  choose Sg hSgext using hSg
  let Ξ : Fin (N + 1) → SectionSpace T.structureMap T.line (r * D0) :=
    fun i => secPow T.extAtlas (ξ i) D0
  have hΞext : ∀ i, T.Extends ((D0 : ℤ) * w i) (r * D0) (secPow a (y i) D0) (Ξ i) :=
    fun i => extends_secPow T (hext i) D0
  -- no common zeros of the `Ξ_i`
  have hcovΞ : ∀ c : T.extAtlas.I, T.extAtlas.opens c ≤
      ⨆ i, T.space.basicOpen (atlasPowerGlobalCoefficients T.extAtlas (r * D0) c (Ξ i)) := by
    intro c
    refine (hcov c).trans (iSup_mono fun i => ?_)
    rw [show atlasPowerGlobalCoefficients T.extAtlas (r * D0) c (Ξ i) =
      atlasPowerGlobalCoefficients T.extAtlas r c (ξ i) ^ D0 from coeff_secPow _ _ _ _]
    rcases Nat.eq_zero_or_pos D0 with h0 | h0
    · rw [h0, pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]
      exact Scheme.basicOpen_le _ _
    · rw [Scheme.basicOpen_pow _ _ h0]
  -- the `t`-power bookkeeping
  have htu : ∀ (j' : a.I) (p q p' q' : ℤ), p + q = p' + q' →
      ((T.tUnit j' ^ p).val * (T.tUnit j' ^ q).val : Γ(T.space, _)) =
        (T.tUnit j' ^ p').val * (T.tUnit j' ^ q').val := by
    intro j' p q p' q' hpq
    rw [← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add, hpq]
  -- compatibility `Σ_i Ξ_{i'} = Σ_{i'} Ξ_i`
  have hprod : ∀ i i', SectionSpace.mul T.structureMap T.extAtlas _ _ (Sg i) (Ξ i') =
      SectionSpace.mul T.structureMap T.extAtlas _ _ (Sg i') (Ξ i) := by
    intro i i'
    have := Nonempty.intro (Classical.arbitrary X)
    apply T.eq_of_epsCoeff_eq
    intro j'
    have e1 := extends_mul T (hSgext i) (hΞext i') j'
    have e2 := extends_mul T (hSgext i') (hΞext i) j'
    rw [e1, e2]
    simp only [SectionSpace.coefficients_mul, coeff_secPow, map_mul]
    rw [show -((D0 : ℤ) * w i - j + (D0 : ℤ) * w i') = -((D0 : ℤ) * w i' - j + (D0 : ℤ) * w i)
      by ring]
    ring
  obtain ⟨σ, hσ⟩ := exists_section_mul_eq T.extAtlas (r * k) (r * D0)
    (fun i => (Ξ i : bundlePowerGlobalSections T.line (r * D0)))
    (fun i => (Sg i : bundlePowerGlobalSections T.line (r * D0 + r * k))) hcovΞ
    (fun c i i' => by
      have := congrArg (atlasPowerGlobalCoefficients T.extAtlas (r * D0 + r * k + r * D0) c)
        (hprod i i')
      simpa only [SectionSpace.coefficients_mul] using this)
  refine ⟨σ, fun j' => ?_⟩
  -- `σ` extends `t^j s̄`: check after multiplication by the `Ξ_i`, whose nonvanishing loci
  -- cover the chart
  rw [← sub_eq_zero]
  apply eq_zero_of_mul_eq_zero_cover _
    (fun i => atlasPowerGlobalCoefficients T.extAtlas (r * D0) (Sum.inr j') (Ξ i)) (hcovΞ _)
  intro i
  have h1 := hσ (Sum.inr j') i
  have h2 := hSgext i j'
  have h3 := hΞext i j'
  simp only [TestConfiguration.epsCoeff] at h2 h3
  rw [sub_mul]
  change atlasPowerGlobalCoefficients T.extAtlas (r * k) (Sum.inr j') σ *
      atlasPowerGlobalCoefficients T.extAtlas (r * D0) (Sum.inr j') (Ξ i) - _ = 0
  rw [h1, h2, h3, SectionSpace.coefficients_mul, map_mul, coeff_secPow]
  rw [sub_eq_zero]
  have := htu j' (-((D0 : ℤ) * w i - j)) 0 (-(-j)) (-((D0 : ℤ) * w i)) (by ring)
  rw [zpow_zero, Units.val_one, mul_one] at this
  rw [this]
  ring

end SGPT.TestCurve.FGRel
