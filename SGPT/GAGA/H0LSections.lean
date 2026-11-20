import SGPT.GAGA.H0LCone

/-!
# GAGA for the sections of an arbitrary line bundle


`X` is smooth projective over `ℂ` (closed projective embedding `E`, `𝒪_X(1)` with the frames
`x_l` on `U_l = X ∩ D₊(x_l)`), `L` is an algebraic line bundle with a rank-one atlas `a`
(frames `αᵢ` on `Vᵢ`) and an arbitrary smooth metric `H`, and `s` is a holomorphic section of
`((L, H)^an)^{⊗ k}` with coefficients `cᵢ = lcoef s i` in the frames `αᵢ^k`
(`c_l = g_{il}^k cᵢ`, `lcoef_transition`).

The classical proof of GAGA for `H⁰` twists by `𝒪(m)`: for a complex point `x ∈ Vᵢ`, choose a
basic open `x ∈ D(g) ⊆ Vᵢ ∩ U_{l₀}` (`g` regular on the affine `U_{l₀}`).  The local section
`g^R x_{l₀}^m αᵢ^{-k}` of `L^{-k}(m)` on `D(g)`, extended by zero, is algebraic on all of `X` for
`R, m ≫ 0` (Serre's twisting argument, Hartshorne II.5.14): on a finite cover of `X(ℂ)` by
affine basic opens `V ⊆ U_{l_V} ∩ V_{i_V}` its coefficient is regular
(`isRegularOn_twist`, two applications of the extension lemma
`SGPT.GAGA.H0L.exists_isRegularOn_pow_mul`).  Hence the coefficients
`h_l = (x_{l₀}/x_l)^m g^R cᵢ` (extended by zero) of `s ⊗ (g^R x_{l₀}^m αᵢ^{-k})` form a section
family of degree `m` (`SGPT.GAGA.H0L.IsSectionFamily`), which is polynomial for `m ≫ 0`:
`h_{l₀} = P(x/x_{l₀})`, so `cᵢ = P(x/x_{l₀}) / g^R` is regular on `D(g)`
(`isRegularOn_lcoef`).  Regularity being local, `cᵢ` is regular on `Vᵢ`; the regular
coefficients glue (`exists_isAnalytificationOf`) to an algebraic section `σ` with `σ^an = s`.

* **`schemeSectionsAlgebraic`**: GAGA for the sections of `L^{⊗ k}` (lane GAGAMULT2's
  `SchemeSectionsAlgebraic`) for every line bundle `L`, every atlas and smooth metric, and every
  `k` (not only `k ≫ 0`);
* `eq_of_isAnalytificationOf`: the algebraic section is unique.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.H0L

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.NAPotential.GAGAMult SGPT.GAGA.H0S
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open scoped Topology Manifold

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f} {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance h0lSecTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0lSecCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance h0lSecManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- A regular function is holomorphic on its domain. -/
theorem IsRegularOn.holomorphicAt {U : X.Opens} {φ : SchemeComplexPoint f → ℂ}
    (h : IsRegularOn f E n U φ) {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ U) :
    HolomorphicAt n φ p := by
  obtain ⟨r, hr⟩ := h
  have hO : IsOpen (schemeComplexPointImage f ⁻¹' (U : Set X)) :=
    U.isOpen.preimage (schemeComplexPointImage_continuous f)
  refine (schemeOpenRegularFunction_holomorphicAt f n E U r p hp).congr ?_
  filter_upwards [hO.mem_nhds hp] with q hq
  exact (hr q hq).symm

/-- The analytic frame transitions are regular on the overlaps. -/
theorem isRegularOn_schemeFrameTransition {L : X.Modules} {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) :
    IsRegularOn f E n (U ⊓ V) (schemeFrameTransition f n E α β) :=
  isRegularOn_schemeOpenRegularFunction _ _

/-! ### Coefficients of holomorphic sections of `((L, H)^an)^{⊗ k}` -/

section Coefficients

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) {k : ℕ}

/-- The analytic transition of `(L, H)^an` between two algebraic frames. -/
theorem coordChangeL_schemeHermitianAtlasFrame' {U V : X.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V)
    {p : SchemeComplexPoint f} (hpU : schemeComplexPointImage f p ∈ U)
    (hpV : schemeComplexPointImage f p ∈ V) :
    ((schemeHermitianAtlasFrame f n E a H α).val.coordChangeL ℂ
      (schemeHermitianAtlasFrame f n E a H β).val p) 1 =
        schemeFrameTransition f n E α β p := by
  rw [Trivialization.coordChangeL_apply _ _ ⟨hpU, hpV⟩]
  change frameCoef f n E a H β p *
      (show ℂ from (schemeHermitianTrivialization f n E a H α).symm p 1) = _
  rw [schemeHermitianTrivialization_symm f n E a H α hpU,
    frameCoef_transition f n E a H α β hpU hpV, mul_one, mul_assoc,
    mul_inv_cancel₀ (frameCoef_ne_zero f n E a H α hpU), mul_one]

/-- The coefficient of a holomorphic section `s` of `((L, H)^an)^{⊗ k}` in the frame `αᵢ^k`. -/
def lcoef (s : twistedSections (schemeHermitianLineBundle f n E a H) unit k) (i : a.I)
    (p : SchemeComplexPoint f) : ℂ :=
  (twistedFrame f n E a H (a.frame i) k).val.continuousLinearMapAt ℂ p (s p)

/-- **Transition of the coefficients**: `c_l = g_{il}^k cᵢ` on `Vᵢ ∩ V_l`. -/
theorem lcoef_transition (s : twistedSections (schemeHermitianLineBundle f n E a H) unit k)
    (i l : a.I) {p : SchemeComplexPoint f} (hpi : schemeComplexPointImage f p ∈ a.opens i)
    (hpl : schemeComplexPointImage f p ∈ a.opens l) :
    lcoef a H s l p = schemeFrameTransition f n E (a.frame i) (a.frame l) p ^ k * lcoef a H s i p := by
  set e := twistedFrame f n E a H (a.frame i) k
  set e' := twistedFrame f n E a H (a.frame l) k
  have he : p ∈ e.val.baseSet := mem_twistedFrame_baseSet f n E a H _ k hpi
  have he' : p ∈ e'.val.baseSet := mem_twistedFrame_baseSet f n E a H _ k hpl
  have htr := twistedPower_frame_transition
    (schemeHermitianAtlasFrame f n E a H (a.frame i))
    (schemeHermitianAtlasFrame f n E a H (a.frame l))
    (unitAtlasFrame (n := n) (M := SchemeComplexPoint f)) unitAtlasFrame
    (x := p) hpi hpl (Set.mem_univ p) (Set.mem_univ p) k
  have hu : ((unitAtlasFrame (n := n) (M := SchemeComplexPoint f)).val.coordChangeL ℂ
      unitAtlasFrame.val p) 1 = 1 := by
    change ((Bundle.Trivial.trivialization (SchemeComplexPoint f) ℂ).coordChangeL ℂ
      (Bundle.Trivial.trivialization (SchemeComplexPoint f) ℂ) p) 1 = 1
    rw [Bundle.Trivial.trivialization.coordChangeL]
    rfl
  rw [hu, mul_one, coordChangeL_schemeHermitianAtlasFrame' a H _ _ hpi hpl] at htr
  unfold lcoef
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e'.val he',
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val he]
  have hs : s p = e.val.symm p ((e.val ⟨p, s p⟩).2) := (e.val.symm_apply_apply_mk he (s p)).symm
  conv_lhs => rw [hs]
  rw [← Trivialization.coordChangeL_apply (R := ℂ) e.val e'.val ⟨he, he'⟩]
  have hlin : (e.val.coordChangeL ℂ e'.val p) ((e.val ⟨p, s p⟩).2) =
      (e.val ⟨p, s p⟩).2 * (e.val.coordChangeL ℂ e'.val p) 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [hlin]
  change _ * ((twistedPowerAtlasFrame _ _ k).val.coordChangeL ℂ
    (twistedPowerAtlasFrame _ _ k).val p) 1 = _
  rw [htr, mul_comm]

/-- The coefficients are holomorphic on `Vᵢ(ℂ)`. -/
theorem holomorphicAt_lcoef (s : twistedSections (schemeHermitianLineBundle f n E a H) unit k)
    (i : a.I) {p : SchemeComplexPoint f} (hp : schemeComplexPointImage f p ∈ a.opens i) :
    HolomorphicAt n (lcoef a H s i) p :=
  holomorphicAt_coef_of_contMDiff (twistedFrame f n E a H (a.frame i) k).val
    s.contMDiff (mem_twistedFrame_baseSet f n E a H _ k hp)

end Coefficients

/-! ### The twist `g^R x_{l₀}^m α^{-k}` is algebraic -/

section Twist

open scoped Classical

variable {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)

/-- **The twisting section is regular on an affine piece.**  Let `D(g) ⊆ Vᵢ` with `g` regular
on `U_{l₀}`, and let `V ⊆ U_{l_V} ∩ V_{i_V}` be affine.  The coefficient of
`g^R x_{l₀}^m αᵢ^{-k}` (extended by zero off `D(g)`) in the frame `x_{l_V}^m α_{i_V}^{-k}`,
`(x_{l₀}/x_{l_V})^m g^R g_{i_V i}^k`, is regular on `V` for all `R > R₀` and `m ≥ (e + 2) R`. -/
theorem isRegularOn_twist {V : X.Opens} (hV : IsAffineOpen V) {lV l₀ : Fin (E.ambientDimension + 1)}
    {iV i : a.I} (hVl : V ≤ coordOpen E lV) (hVi : V ≤ a.opens iV) (g : Γ(X, coordOpen E l₀))
    (hg : X.basicOpen g ≤ a.opens i) :
    ∃ e R₀ : ℕ, ∀ R, R₀ + 1 ≤ R → ∀ m, (e + 2) * R ≤ m → IsRegularOn f E n V (fun p =>
      if schemeComplexPointImage f p ∈ X.basicOpen g then
        homCoords f E n lV p l₀ ^ m * schemeOpenRegularFunction f n E (coordOpen E l₀) g p ^ R *
          schemeFrameTransition f n E (a.frame iV) (a.frame i) p ^ k
      else 0) := by
  let := E.locallyOfFiniteType
  set gf := schemeOpenRegularFunction f n E (coordOpen E l₀) g with hgf
  set ρ : Γ(X, V) := X.presheaf.map (homOfLE hVl).op (ratio E lV l₀) with hρ
  have hρv : ∀ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ V →
      schemeOpenRegularFunction f n E V ρ p = homCoords f E n lV p l₀ := fun p hp =>
    schemeOpenRegularFunction_restrict f n E V (coordOpen E lV) hVl _ hp
  -- first extension: `ρ^{e+1} g` is regular on `V`
  have hDρ : X.basicOpen ρ ≤ coordOpen E l₀ := by
    rw [hρ, Scheme.basicOpen_res, basicOpen_ratio f E]
    exact inf_le_right.trans inf_le_right
  obtain ⟨e, G, hG⟩ := exists_isRegularOn_pow_mul hV ρ
    ((isRegularOn_schemeOpenRegularFunction (f := f) (E := E) (n := n) (coordOpen E l₀) g).mono hDρ)
  -- the values of `h' = G ρ = ρ^{e+2} g`
  have hh' : ∀ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ V →
      schemeOpenRegularFunction f n E V (G * ρ) p = homCoords f E n lV p l₀ ^ (e + 2) * gf p := by
    intro p hp
    have hGp := hG p hp
    simp only at hGp
    rw [schemeOpenRegularFunction_mul' f E n V G ρ hp, ← hGp, hρv p hp]
    ring
  -- `h'` vanishes off `D(g)`
  have hh'0 : ∀ p : SchemeComplexPoint f, schemeComplexPointImage f p ∈ V →
      schemeComplexPointImage f p ∉ X.basicOpen g →
        schemeOpenRegularFunction f n E V (G * ρ) p = 0 := by
    intro p hp hpg
    rw [hh' p hp]
    by_cases hρ0 : homCoords f E n lV p l₀ = 0
    · rw [hρ0, zero_pow (by omega), zero_mul]
    · have hpl₀ : schemeComplexPointImage f p ∈ coordOpen E l₀ :=
        (mem_coordOpen_iff_ratio_ne_zero f E n lV l₀ p (hVl hp)).mpr hρ0
      rw [hgf, schemeOpenRegularFunction_eq_zero_of_not_mem_basicOpen f E n _ g hpl₀ hpg,
        mul_zero]
  -- second extension: `h'^{R₀+1} g_{i_V i}^k` is regular on `V`
  have hD' : X.basicOpen (G * ρ) ≤ a.opens iV ⊓ a.opens i := by
    apply le_of_forall_schemeComplexPoint f
    intro p hp
    have hpV : schemeComplexPointImage f p ∈ V := X.basicOpen_le _ hp
    refine ⟨hVi hpV, hg ?_⟩
    by_contra hpg
    exact (schemeOpenRegularFunction_ne_zero_iff f E n V _ p hpV).mpr hp (hh'0 p hpV hpg)
  obtain ⟨R₀, hR₀⟩ := exists_isRegularOn_pow_mul hV (G * ρ)
    (((isRegularOn_schemeFrameTransition (f := f) (E := E) (n := n) (a.frame iV)
      (a.frame i)).pow k).mono hD')
  refine ⟨e, R₀, fun R hR m hm => ?_⟩
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hR
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hreg := (((isRegularOn_schemeOpenRegularFunction (f := f) (E := E) (n := n) V ρ).pow c).mul
    ((isRegularOn_schemeOpenRegularFunction (f := f) (E := E) (n := n) V (G * ρ)).pow b)).mul hR₀
  refine hreg.congr fun p hp => ?_
  split_ifs with hpg
  · rw [hρv p hp, hh' p hp]
    ring
  · rw [hh'0 p hp hpg]
    ring

end Twist

/-! ### The coefficients are regular -/

section Local

open scoped Classical

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L) {k : ℕ}
  [CompactSpace (SchemeComplexPoint f)]

/-- **The coefficients of a holomorphic section of `((L, H)^an)^{⊗ k}` are regular**: `cᵢ` is
regular on `Vᵢ`. -/
theorem isRegularOn_lcoef (s : twistedSections (schemeHermitianLineBundle f n E a H) unit k)
    (i : a.I) : IsRegularOn f E n (a.opens i) (lcoef a H s i) := by
  let := E.locallyOfFiniteType
  obtain ⟨k₀, hk₀⟩ := exists_polynomial_of_isSectionFamily f E n
  -- an affine cover of `X(ℂ)` adapted to both atlases
  choose iq hiq using fun q : SchemeComplexPoint f => a.covers (schemeComplexPointImage f q)
  have hbas : ∀ q : SchemeComplexPoint f, ∃ hq : Γ(X, coordOpen E (frameIndex f E q)),
      X.basicOpen hq ≤ a.opens (iq q) ⊓ coordOpen E (frameIndex f E q) ∧
        schemeComplexPointImage f q ∈ X.basicOpen hq := fun q =>
    (isAffineOpen_coordOpen E (frameIndex f E q)).exists_basicOpen_le
      (V := a.opens (iq q) ⊓ coordOpen E (frameIndex f E q))
      ⟨schemeComplexPointImage f q, ⟨hiq q, mem_coordOpen_frameIndex f E q⟩⟩
      (mem_coordOpen_frameIndex f E q)
  choose hq hqV hqmem using hbas
  obtain ⟨B, -, hB⟩ := (isCompact_univ : IsCompact (Set.univ : Set (SchemeComplexPoint f))).elim_nhds_subcover
    (fun q => schemeComplexPointImage f ⁻¹' (X.basicOpen (hq q) : Set X))
    (fun q _ => ((X.basicOpen (hq q)).isOpen.preimage
      (schemeComplexPointImage_continuous f)).mem_nhds (hqmem q))
  apply isRegularOn_of_local
  intro x hx
  set l₀ := frameIndex f E x
  have hx₀ := mem_coordOpen_frameIndex f E x
  obtain ⟨g, hgV, hxg⟩ := (isAffineOpen_coordOpen E l₀).exists_basicOpen_le
    (V := a.opens i ⊓ coordOpen E l₀) ⟨_, ⟨hx, hx₀⟩⟩ hx₀
  have hgi : X.basicOpen g ≤ a.opens i := hgV.trans inf_le_left
  set gf := schemeOpenRegularFunction f n E (coordOpen E l₀) g with hgf
  -- the twists on the pieces of the cover
  have htw := fun q : SchemeComplexPoint f => isRegularOn_twist (f := f) (E := E) (n := n) a k
    ((isAffineOpen_coordOpen E (frameIndex f E q)).basicOpen (hq q)) (l₀ := l₀) (i := i)
    ((hqV q).trans inf_le_right) ((hqV q).trans inf_le_left) g hgi
  choose e R₀ hR₀ using htw
  set R := B.sup R₀ + 1 with hRdef
  set m := max k₀ ((B.sup e + 2) * R) with hmdef
  have hRq : ∀ q ∈ B, R₀ q + 1 ≤ R := fun q hq => Nat.succ_le_succ (Finset.le_sup hq)
  have hmq : ∀ q ∈ B, (e q + 2) * R ≤ m := fun q hq =>
    le_trans (Nat.mul_le_mul_right R (Nat.add_le_add_right (Finset.le_sup hq) 2)) (le_max_right _ _)
  have hR : 0 < R := Nat.succ_pos _
  -- the coefficients of `s ⊗ g^R x_{l₀}^m αᵢ^{-k}`
  set hfam : Fin (E.ambientDimension + 1) → SchemeComplexPoint f → ℂ := fun l p =>
    if schemeComplexPointImage f p ∈ X.basicOpen g then
      homCoords f E n l p l₀ ^ m * gf p ^ R * lcoef a H s i p
    else 0 with hfamdef
  -- on a piece of the cover, `h_l = (x_{l_q}/x_l)^m τ_q c_{i_q}`
  have hpiece : ∀ q ∈ B, ∀ (l : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f),
      schemeComplexPointImage f p ∈ X.basicOpen (hq q) →
        schemeComplexPointImage f p ∈ coordOpen E l →
          hfam l p = homCoords f E n l p (frameIndex f E q) ^ m *
            (if schemeComplexPointImage f p ∈ X.basicOpen g then
              homCoords f E n (frameIndex f E q) p l₀ ^ m * gf p ^ R *
                schemeFrameTransition f n E (a.frame (iq q)) (a.frame i) p ^ k
            else 0) * lcoef a H s (iq q) p := by
    intro q _ l p hpq hpl
    have hpV := hqV q hpq
    simp only [hfamdef]
    split_ifs with hpg
    · rw [homCoords_trans f E n (frameIndex f E q) l l₀ hpV.2 hpl,
        lcoef_transition a H s (iq q) i hpV.1 (hgi hpg)]
      ring
    · ring
  have hfamily : IsSectionFamily f E n m hfam := by
    refine ⟨fun l p hpl => ?_, fun i' l p hpi' hpl => ?_⟩
    · obtain ⟨q, hqB, hpq⟩ : ∃ q ∈ B, schemeComplexPointImage f p ∈ X.basicOpen (hq q) := by
        have := hB (Set.mem_univ p)
        simp only [Set.mem_iUnion] at this
        obtain ⟨q, hqB, hpq⟩ := this
        exact ⟨q, hqB, hpq⟩
      have hτ := hR₀ q R (hRq q hqB) m (hmq q hqB)
      have hreg := (((isRegularOn_schemeOpenRegularFunction (f := f) (E := E) (n := n)
        (coordOpen E l) (ratio E l (frameIndex f E q))).pow m).mono
          (inf_le_right : X.basicOpen (hq q) ⊓ coordOpen E l ≤ coordOpen E l)).mul
        (hτ.mono (inf_le_left : X.basicOpen (hq q) ⊓ coordOpen E l ≤ X.basicOpen (hq q)))
      have hO : IsOpen (schemeComplexPointImage f ⁻¹'
          ((X.basicOpen (hq q) ⊓ coordOpen E l : X.Opens) : Set X)) :=
        (X.basicOpen (hq q) ⊓ coordOpen E l).isOpen.preimage (schemeComplexPointImage_continuous f)
      refine ((hreg.holomorphicAt ⟨hpq, hpl⟩).mul
        (holomorphicAt_lcoef a H s (iq q) ((hqV q hpq).1))).congr ?_
      filter_upwards [hO.mem_nhds ⟨hpq, hpl⟩] with p' hp'
      exact (hpiece q hqB l p' hp'.1 hp'.2).symm
    · simp only [hfamdef]
      split_ifs with hpg
      · rw [homCoords_trans f E n i' l l₀ hpi' hpl]
        ring
      · ring
  obtain ⟨P, -, hP⟩ := hk₀ m (le_max_left _ _) hfam hfamily
  refine ⟨X.basicOpen g, hgi, hxg, ?_⟩
  have h1 := (isRegularOn_schemeOpenRegularFunction (f := f) (E := E) (n := n) (coordOpen E l₀)
    (polyCoef E l₀ P)).mono (X.basicOpen_le g)
  have h2 : IsRegularOn f E n (X.basicOpen (g ^ R)) (fun p => (gf p ^ R)⁻¹) :=
    IsRegularOn.inv fun p hp => (schemeOpenRegularFunction_pow' f E n _ g R hp).symm
  rw [Scheme.basicOpen_pow X g hR] at h2
  refine (h1.mul h2).congr fun p hp => ?_
  have hpl₀ : schemeComplexPointImage f p ∈ coordOpen E l₀ := X.basicOpen_le g hp
  have hgp : gf p ≠ 0 := (schemeOpenRegularFunction_ne_zero_iff f E n _ g p hpl₀).mpr hp
  have hPp := hP l₀ p hpl₀
  simp only [hfamdef, if_pos hp, homCoords_self f E n l₀ hpl₀, one_pow, one_mul] at hPp
  rw [schemeOpenRegularFunction_polyCoef f n E l₀ P p hpl₀]
  change MvPolynomial.eval (homCoords f E n l₀ p) P * _ = _
  rw [← hPp]
  field_simp

/-! ### Gluing: GAGA for the sections of `L^{⊗ k}` -/

/-- **Every holomorphic section of `((L, H)^an)^{⊗ k}` is the analytification of an algebraic
section of `L^{⊗ k}`.** -/
theorem exists_isAnalytificationOf
    (s : twistedSections (schemeHermitianLineBundle f n E a H) unit k) :
    ∃ σ : bundlePowerGlobalSections L k, IsAnalytificationOf f n E a H s σ := by
  choose r hr using fun i => isRegularOn_lcoef a H s i
  let loc : ∀ i : a.I, bundleSections (bundleTensorPower L k) (a.opens i) := fun i =>
    (((a.frame i).tensorPower k).coefficients (𝟙 _)).symm (r i)
  have hloc : ∀ (i : a.I) {W : X.Opens} (h : W ⟶ a.opens i),
      ((a.frame i).tensorPower k).coefficients h
        ((bundleTensorPower L k).val.map h.op (loc i)) = X.presheaf.map h.op (r i) := by
    intro i W h
    have h' := ((a.frame i).tensorPower k).coefficients_restrict (𝟙 _) h (loc i)
    simp only [Category.comp_id, loc, LinearEquiv.apply_symm_apply] at h'
    exact h'
  have hcompat : TopCat.Presheaf.IsCompatible (bundleTensorPower L k).val.presheaf a.opens loc := by
    intro i l
    let lft : a.opens i ⊓ a.opens l ⟶ a.opens i := homOfLE inf_le_left
    let rgt : a.opens i ⊓ a.opens l ⟶ a.opens l := homOfLE inf_le_right
    apply (((a.frame l).tensorPower k).coefficients rgt).injective
    change ((a.frame l).tensorPower k).coefficients rgt
        ((bundleTensorPower L k).val.map lft.op (loc i)) =
      ((a.frame l).tensorPower k).coefficients rgt ((bundleTensorPower L k).val.map rgt.op (loc l))
    rw [LocalBundleFrame.tensorPower_coefficients_transition (a.frame i) (a.frame l) lft rgt k,
      hloc i lft, hloc l rgt]
    refine eq_of_schemeOpenRegularFunction_eq f E n _ _ fun p hp => ?_
    rw [schemeOpenRegularFunction_mul' f E n _ _ _ hp, schemeOpenRegularFunction_pow' f E n _ _ _ hp,
      schemeOpenRegularFunction_restrict f n E _ _ inf_le_left _ hp,
      schemeOpenRegularFunction_restrict f n E _ _ inf_le_right _ hp, ← hr i p hp.1,
      ← hr l p hp.2, lcoef_transition a H s i l hp.1 hp.2]
    rfl
  have hcover : (⊤ : X.Opens) ≤ iSup a.opens := by
    intro x _
    obtain ⟨i, hi⟩ := a.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let S : TopCat.Sheaf AddCommGrpCat X :=
    ⟨(bundleTensorPower L k).val.presheaf, (bundleTensorPower L k).isSheaf⟩
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' S a.opens ⊤
    (fun _ => homOfLE le_top) hcover loc hcompat
  refine ⟨σ, fun i p hp => ?_⟩
  have hc : algCoef (a.frame i) k σ = r i := by
    unfold algCoef
    have hσi : (bundleTensorPower L k).val.map (homOfLE le_top).op σ = loc i := hσ i
    rw [hσi]
    simp only [loc, LinearEquiv.apply_symm_apply]
  rw [hc]
  exact hr i p hp

/-- **GAGA for the sections of `L^{⊗ k}`** (the `SchemeSectionsAlgebraic`) for every
algebraic line bundle `L` on the smooth projective complex scheme `X`, every atlas `a`, every
smooth metric `H` and every `k`. -/
theorem schemeSectionsAlgebraic (j : ℕ) : SchemeSectionsAlgebraic f n E a H j :=
  fun s => exists_isAnalytificationOf a H s

end Local

/-- **The algebraic section of a holomorphic section is unique**: two algebraic sections of
`L^{⊗ k}` with the same analytification are equal. -/
theorem eq_of_isAnalytificationOf {L : X.Modules} {a : LineBundleAtlas L}
    {H : SchemeLineBundleMetric f n E L} {k : ℕ}
    {s : twistedSections (schemeHermitianLineBundle f n E a H) unit k}
    {σ σ' : bundlePowerGlobalSections L k} (h : IsAnalytificationOf f n E a H s σ)
    (h' : IsAnalytificationOf f n E a H s σ') : σ = σ' := by
  apply atlasPowerGlobalCoefficients_ext a k
  intro i
  refine eq_of_schemeOpenRegularFunction_eq f E n _ _ fun p hp => ?_
  exact (h i p hp).symm.trans (h' i p hp)

end SGPT.GAGA.H0L
