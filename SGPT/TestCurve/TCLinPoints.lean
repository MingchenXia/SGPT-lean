import SGPT.TestCurve.TCLinDef
import SGPT.TestCurve.TCLinVandermonde

/-!
# Weight vectors of distinct weights are independent

Let `(𝓧, 𝓛)` be a test configuration of `(X, L)` (the encoding), with
`q : 𝓧 ∖ 𝓧₀ ⟶ X` and `(q, π) : 𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m`. On the chart `q⁻¹(V)` the functions
`t^λ q^♯(b)` with distinct `λ` are linearly independent over `q^♯ Γ(X, V)`:

*if `Σ_{λ ∈ S} t^λ q^♯(b_λ) = 0` on `q⁻¹(V)`, then all `b_λ` vanish*
(`TestConfiguration.eq_zero_of_sum_tpow_mul`).

Proof: for every `c ∈ ℂ^*` the identification gives a section `e_c : X ⟶ 𝓧 ∖ 𝓧₀` of `q` with
`t ∘ e_c = c` (the point `x ↦ (x, c)` of `X × 𝔾_m`, `sectionAt`); pulling back along `e_c`
gives `Σ_λ c^λ b_λ = 0` for all `c ∈ ℂ^*`, and the characters `c ↦ c^λ` are linearly
independent (`TCLin.eq_zero_of_forall_sum_zpow_mul`).

This is the algebraic content of "a section of `𝓛^m` over `𝓧 ∖ 𝓧₀` has a unique weight
decomposition" used for the `𝔾_m`-linearization (`TCLinGraph`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCLin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite SGPT.TestCurve.TCEnc

/-! ### Points of `𝔾_m` -/

/-- The point `c` of `𝔸¹ = Spec ℂ[t]`. -/
def linePoint (c : ℂ) : Spec (.of ℂ) ⟶ AffineLine :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c))

theorem linePoint_comp_toBase (c : ℂ) : linePoint c ≫ affineLineToBase = 𝟙 _ := by
  rw [linePoint, affineLineToBase, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

theorem linePoint_appTop_coordT (c : ℂ) :
    (linePoint c).appTop coordT = (Scheme.ΓSpecIso (.of ℂ)).inv c := by
  rw [coordT_eq, linePoint, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  simp

theorem linePoint_range (c : ℂˣ) :
    Set.range (linePoint (c : ℂ)) ⊆ Set.range gmOpen.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι, SetLike.mem_coe, mem_gmOpen]
  intro hX
  have hc : (Polynomial.evalRingHom (c : ℂ)) Polynomial.X ∈
      (show PrimeSpectrum ℂ from x).asIdeal := hX
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_X] at hc
  exact (show PrimeSpectrum ℂ from x).isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hc c.isUnit)

/-- The point `c ∈ ℂ^*` of `𝔾_m`. -/
def gmLinePoint (c : ℂˣ) : Spec (.of ℂ) ⟶ gmOpen.toScheme :=
  IsOpenImmersion.lift gmOpen.ι (linePoint (c : ℂ)) (linePoint_range c)

@[simp] theorem gmLinePoint_ι (c : ℂˣ) : gmLinePoint c ≫ gmOpen.ι = linePoint (c : ℂ) :=
  IsOpenImmersion.lift_fac _ _ _

/-- A morphism equal to the identity acts trivially on sections. -/
theorem appLE_of_eq_id {Z : Scheme.{0}} {g : Z ⟶ Z} (hg : g = 𝟙 Z) (V : Z.Opens)
    (e : V ≤ g ⁻¹ᵁ V) : g.appLE V V e = 𝟙 _ := by
  subst hg
  simp [Scheme.Hom.appLE]
  exact Z.presheaf.map_id _

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

/-- The isomorphism `(q, π) : 𝓧 ∖ 𝓧₀ ⟶ X ×_ℂ 𝔾_m` of the identification. -/
abbrev coordLift : (offCentral T.toLine).toScheme ⟶ pullback f gmToBase :=
  pullback.lift (f := f) (g := gmToBase) T.coord (toGm T.toLine)
    (by rw [T.coord_over, ← Category.assoc, ← toGm_comp_ι, Category.assoc])

instance coordLift_isIso : IsIso (coordLift T) := T.coord_isIso

/-- **The section `x ↦ (x, c)` of `q`**, for `c ∈ ℂ^*`. -/
def sectionAt (c : ℂˣ) : X ⟶ (offCentral T.toLine).toScheme :=
  pullback.lift (f := f) (g := gmToBase) (𝟙 X) (f ≫ gmLinePoint c)
      (by rw [Category.id_comp, Category.assoc, ← Category.assoc (gmLinePoint c),
        gmLinePoint_ι, linePoint_comp_toBase, Category.comp_id]) ≫
    inv (coordLift T)

theorem sectionAt_coord (c : ℂˣ) : (sectionAt T) c ≫ T.coord = 𝟙 X := by
  have h : inv (coordLift T) ≫ T.coord = pullback.fst f gmToBase := by
    rw [IsIso.inv_comp_eq, pullback.lift_fst]
  rw [sectionAt, Category.assoc, h, pullback.lift_fst]

theorem sectionAt_toGm (c : ℂˣ) : (sectionAt T) c ≫ toGm T.toLine = f ≫ gmLinePoint c := by
  have h : inv (coordLift T) ≫ toGm T.toLine = pullback.snd f gmToBase := by
    rw [IsIso.inv_comp_eq, pullback.lift_snd]
  rw [sectionAt, Category.assoc, h, pullback.lift_snd]

theorem sectionAt_toLine (c : ℂˣ) :
    (sectionAt T) c ≫ (offCentral T.toLine).ι ≫ T.toLine = f ≫ linePoint (c : ℂ) := by
  rw [← toGm_comp_ι, ← Category.assoc, sectionAt_toGm, Category.assoc, gmLinePoint_ι]

theorem le_sectionAt_preimage (c : ℂˣ) (V : X.Opens) :
    V ≤ (sectionAt T) c ⁻¹ᵁ (T.coord ⁻¹ᵁ V) := by
  intro x hx
  change T.coord ((sectionAt T) c x) ∈ V
  rw [← Scheme.Hom.comp_apply, sectionAt_coord]
  exact hx

/-- **Evaluation at `t = c`**: the pull-back along `e_c` of functions on `q⁻¹(V) ⊆ 𝓧`. -/
def evalAt (c : ℂˣ) (V : X.Opens) : Γ(T.space, overOpen T.coord V) ⟶ Γ(X, V) :=
  ((offCentral T.toLine).ι.appIso (T.coord ⁻¹ᵁ V)).hom ≫
    ((sectionAt T) c).appLE (T.coord ⁻¹ᵁ V) V ((le_sectionAt_preimage T) c V)

theorem evalAt_pullFun (c : ℂˣ) (V : X.Opens) (b : Γ(X, V)) :
    (evalAt T) c V (pullFun T.coord V b) = b := by
  rw [evalAt, TCEnc.pullFun, ← CommRingCat.comp_apply, Category.assoc, Iso.inv_hom_id_assoc,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_of_eq_id ((sectionAt_coord T) c)]
  rfl

theorem evalAt_tFun (c : ℂˣ) (V : X.Opens) :
    evalAt T c V (T.space.presheaf.map (homOfLE le_top).op (tFun T.toLine)) =
      X.presheaf.map (homOfLE le_top).op (schemeGlobalConstants f (c : ℂ)) := by
  have hcomp : (sectionAt T c ≫ (offCentral T.toLine).ι ≫ T.toLine).appTop coordT =
      f.appTop ((linePoint (c : ℂ)).appTop coordT) := by
    rw [sectionAt_toLine]
    rfl
  rw [linePoint_appTop_coordT] at hcomp
  rw [evalAt, ← CommRingCat.comp_apply, Scheme.Hom.appIso_hom',
    Scheme.Hom.map_appLE_assoc, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE,
    CommRingCat.comp_apply]
  congr 1

/-- **Independence of the powers of `t` over `q^♯`**: if `Σ_{λ ∈ S} t^λ q^♯(b_λ) = 0` on the chart
`q⁻¹(V_j)`, then every `b_λ`, `λ ∈ S`, vanishes. -/
theorem eq_zero_of_sum_tpow_mul (j : a.I) (S : Finset ℤ) (b : ℤ → Γ(X, a.opens j))
    (h : ∑ lam ∈ S, (T.tUnit j ^ lam).val * pullFun T.coord (a.opens j) (b lam) = 0) :
    ∀ lam ∈ S, b lam = 0 := by
  let κ : ℂ →+* Γ(X, a.opens j) :=
    (X.presheaf.map (homOfLE le_top : a.opens j ⟶ ⊤).op).hom.comp (schemeGlobalConstants f)
  refine eq_zero_of_forall_sum_zpow_mul κ S b fun c => ?_
  let ev : Γ(T.space, overOpen T.coord (a.opens j)) →+* Γ(X, a.opens j) :=
    ((evalAt T) c (a.opens j)).hom
  have hu : Units.map ev.toMonoidHom (T.tUnit j) = Units.map κ.toMonoidHom c := by
    ext
    change ev (T.tRes j) = κ c
    exact (evalAt_tFun T) c (a.opens j)
  have h1 := congrArg ev h
  rw [map_sum, map_zero] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [map_mul]
  have e1 : ev (pullFun T.coord (a.opens j) (b lam)) = b lam := (evalAt_pullFun T) c _ _
  have e2 : ev ((T.tUnit j ^ lam).val) = κ ((c ^ lam : ℂˣ) : ℂ) := by
    have := congrArg Units.val (congrArg (· ^ lam) hu)
    simp only [← map_zpow] at this
    exact this
  rw [e1, e2]

end SGPT.TestCurve.TCLin
