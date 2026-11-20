import SGPT.GAGA.H0LSections

/-!
# GAGA for coefficient families with regular transitions


Let `X` be smooth projective over `ℂ` (closed projective embedding `E`), `L` an algebraic line
bundle with a rank-one atlas `a` (frames `αᵢ` on `Vᵢ`) and `k ∈ ℕ`. A *holomorphic coefficient
family of degree `k`* is a family of functions `cᵢ` on the complex points of `X` such that `cᵢ` is
holomorphic on `Vᵢ(ℂ)` and `c_l = g_{il}^k cᵢ` on `(Vᵢ ∩ V_l)(ℂ)`, where `g_{il}` is the
(algebraic) transition of the frames (`IsHolomorphicCoefficientFamily`). These are exactly the
coefficients of a holomorphic section of the analytification of `L^{⊗ k}`, written in the
algebraic frames `αᵢ^k`, but no analytic bundle is needed to state the condition.

Lane H0-GAGA3 proved that the coefficients of the holomorphic sections of `((L, H)^an)^{⊗ k}`
are regular and glue to an algebraic section (`SGPT.GAGA.H0L.isRegularOn_lcoef`,
`SGPT.GAGA.H0L.exists_isAnalytificationOf`). Its proof only uses the holomorphy of the
coefficients and their transition law; this file records the abstract version:

* `isRegularOn_of_isHolomorphicCoefficientFamily`: every `cᵢ` is regular on `Vᵢ`
  (Serre's twisting argument, verbatim from H0-GAGA3);
* `exists_section_of_isHolomorphicCoefficientFamily`: the `cᵢ` are the analytic coefficients
  of an algebraic section `σ ∈ H⁰(X, L^{⊗ k})`;
* `eq_of_algCoef_eq`: such a `σ` is unique.

It is applied to the twisted bundles `T ⊗ L^k` (with `k = 1` and the pairwise tensor atlas) in
`SGPT.GAGA.OkoCloseTwisted`, and with `k = 0` (holomorphic functions) in
`SGPT.GAGA.OkoCloseConnected`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.GAGA.OkoClose

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.NAPotential.GAGAMult SGPT.GAGA.H0S SGPT.GAGA.H0L
open scoped Topology Manifold

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f} {n : ℕ}
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance okoFamTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance okoFamCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance okoFamManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (f E n) in
/-- **A holomorphic coefficient family of degree `k`** for the atlas `a` of `L`: `cᵢ` is
holomorphic on `Vᵢ(ℂ)` and `c_l = g_{il}^k cᵢ` on `(Vᵢ ∩ V_l)(ℂ)`. -/
structure IsHolomorphicCoefficientFamily {L : X.Modules} (a : LineBundleAtlas L) (k : ℕ)
    (c : a.I → SchemeComplexPoint f → ℂ) : Prop where
  holomorphicAt : ∀ (i : a.I) (p : SchemeComplexPoint f),
    schemeComplexPointImage f p ∈ a.opens i → HolomorphicAt n (c i) p
  transition : ∀ (i l : a.I) (p : SchemeComplexPoint f),
    schemeComplexPointImage f p ∈ a.opens i → schemeComplexPointImage f p ∈ a.opens l →
      c l p = schemeFrameTransition f n E (a.frame i) (a.frame l) p ^ k * c i p

section Local

open scoped Classical

variable {L : X.Modules} {a : LineBundleAtlas L} {k : ℕ} {c : a.I → SchemeComplexPoint f → ℂ}
  [CompactSpace (SchemeComplexPoint f)]

/-- **The functions of a holomorphic coefficient family are regular**: `cᵢ` is regular on `Vᵢ`.
(The proof of `SGPT.GAGA.H0L.isRegularOn_lcoef`, which only uses the two properties of the
family.) -/
theorem isRegularOn_of_isHolomorphicCoefficientFamily
    (hc : IsHolomorphicCoefficientFamily f E n a k c) (i : a.I) :
    IsRegularOn f E n (a.opens i) (c i) := by
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
  obtain ⟨B, -, hB⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (SchemeComplexPoint f))).elim_nhds_subcover
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
    le_trans (Nat.mul_le_mul_right R (Nat.add_le_add_right (Finset.le_sup hq) 2))
      (le_max_right _ _)
  have hR : 0 < R := Nat.succ_pos _
  -- the coefficients of `s ⊗ g^R x_{l₀}^m αᵢ^{-k}`
  set hfam : Fin (E.ambientDimension + 1) → SchemeComplexPoint f → ℂ := fun l p =>
    if schemeComplexPointImage f p ∈ X.basicOpen g then
      homCoords f E n l p l₀ ^ m * gf p ^ R * c i p
    else 0 with hfamdef
  -- on a piece of the cover, `h_l = (x_{l_q}/x_l)^m τ_q c_{i_q}`
  have hpiece : ∀ q ∈ B, ∀ (l : Fin (E.ambientDimension + 1)) (p : SchemeComplexPoint f),
      schemeComplexPointImage f p ∈ X.basicOpen (hq q) →
        schemeComplexPointImage f p ∈ coordOpen E l →
          hfam l p = homCoords f E n l p (frameIndex f E q) ^ m *
            (if schemeComplexPointImage f p ∈ X.basicOpen g then
              homCoords f E n (frameIndex f E q) p l₀ ^ m * gf p ^ R *
                schemeFrameTransition f n E (a.frame (iq q)) (a.frame i) p ^ k
            else 0) * c (iq q) p := by
    intro q _ l p hpq hpl
    have hpV := hqV q hpq
    simp only [hfamdef]
    split_ifs with hpg
    · rw [homCoords_trans f E n (frameIndex f E q) l l₀ hpV.2 hpl,
        hc.transition (iq q) i p hpV.1 (hgi hpg)]
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
        (X.basicOpen (hq q) ⊓ coordOpen E l).isOpen.preimage
          (schemeComplexPointImage_continuous f)
      refine ((hreg.holomorphicAt ⟨hpq, hpl⟩).mul
        (hc.holomorphicAt (iq q) p ((hqV q hpq).1))).congr ?_
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

/-- **Gluing: a holomorphic coefficient family is the family of analytic coefficients of an
algebraic section** `σ ∈ H⁰(X, L^{⊗ k})`. (The proof of
`SGPT.GAGA.H0L.exists_isAnalytificationOf`.) -/
theorem exists_section_of_isHolomorphicCoefficientFamily
    (hc : IsHolomorphicCoefficientFamily f E n a k c) :
    ∃ σ : bundlePowerGlobalSections L k, ∀ (i : a.I) (p : SchemeComplexPoint f),
      schemeComplexPointImage f p ∈ a.opens i →
        schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) k σ) p = c i p := by
  choose r hr using fun i => isRegularOn_of_isHolomorphicCoefficientFamily hc i
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
      ((a.frame l).tensorPower k).coefficients rgt
        ((bundleTensorPower L k).val.map rgt.op (loc l))
    rw [LocalBundleFrame.tensorPower_coefficients_transition (a.frame i) (a.frame l) lft rgt k,
      hloc i lft, hloc l rgt]
    refine eq_of_schemeOpenRegularFunction_eq f E n _ _ fun p hp => ?_
    rw [schemeOpenRegularFunction_mul' f E n _ _ _ hp,
      schemeOpenRegularFunction_pow' f E n _ _ _ hp,
      schemeOpenRegularFunction_restrict f n E _ _ inf_le_left _ hp,
      schemeOpenRegularFunction_restrict f n E _ _ inf_le_right _ hp, ← hr i p hp.1,
      ← hr l p hp.2, hc.transition i l p hp.1 hp.2]
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
  have hc' : algCoef (a.frame i) k σ = r i := by
    unfold algCoef
    have hσi : (bundleTensorPower L k).val.map (homOfLE le_top).op σ = loc i := hσ i
    rw [hσi]
    simp only [loc, LinearEquiv.apply_symm_apply]
  rw [hc']
  exact (hr i p hp).symm

end Local

/-- **Uniqueness**: two algebraic sections of `L^{⊗ k}` with the same analytic coefficients in
the frames of an atlas are equal. -/
theorem eq_of_algCoef_eq {L : X.Modules} (a : LineBundleAtlas L) {k : ℕ}
    {σ σ' : bundlePowerGlobalSections L k}
    (h : ∀ (i : a.I) (p : SchemeComplexPoint f), schemeComplexPointImage f p ∈ a.opens i →
      schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) k σ) p =
        schemeOpenRegularFunction f n E (a.opens i) (algCoef (a.frame i) k σ') p) :
    σ = σ' := by
  apply atlasPowerGlobalCoefficients_ext a k
  intro i
  exact eq_of_schemeOpenRegularFunction_eq f E n _ _ fun p hp => h i p hp

end SGPT.GAGA.OkoClose
