import SGPT.Okounkov.ValGen2Dual
import SGPT.GAGA.OkoCloseDXMain
import SGPT.Okounkov.ValGenCont

/-!
# `prop:Deltaconvtwisted` for an arbitrary valuation and every twist `T`

Lane POB-VALGEN2, blueprint `claude-val-gen2.tex`. Source: chapter *The theory of Okounkov
bodies*, Section *Algebraic Okounkov bodies*, `prop:Deltaconvtwisted`: for every holomorphic line
bundle `T`, `Δ_{k,T}(L) → Δ_ν(L)` in the Hausdorff metric.

Setting of `SGPT.Okounkov.ValGen`: `X` integral smooth projective of dimension `n = m + 1`
carrying a smooth flag (used only through the valuation-free twisted `thm:DXmain1`), an arbitrary
valuation `ν = v` (section values at a point `c` with `v ≥ 0` there, e.g. the centre), and the
explicit hypothesis `Γ(L) ∈ 𝒮'(C)` for `v` (the conclusion of source `prop:Okounbiglbdl`).

## Proof (the source's)

`L` is big (from `Γ(L) ∈ 𝒮'(C)`), so by the twisted `thm:DXmain1`
(`SGPT.GAGA.OkoClose.dxMain1TwistedHolds`) there are `k₀, k₁` and nonzero sections
`s₀ ∈ H⁰(X, T⁻¹ ⊗ L^{k₀})`, `s₁ ∈ H⁰(X, T ⊗ L^{k₁})` (`exists_twisted_section_ne_zero`; `T⁻¹` is the
dual `bundleDual T` with its dual atlas). Multiplication by them
(`SGPT.Okounkov.ValGen2.lowerProduct`, `upperProduct`) gives
`Γ(L)_j + ν(s₁) ⊆ ν(H⁰(T ⊗ L^{j+k₁})^×)` and `ν(H⁰(T ⊗ L^k)^×) + ν(s₀) ⊆ Γ(L)_{k+k₀}`, and the
sandwich criterion `SGPT.Okounkov.ValGen2.tendsto_hausdorffDist_poly_of_sandwich` with
`Δ_k(L) → Δ_ν(L)` (`SGPT.Okounkov.ValGen.tendsto_hausdorffDist_lineBundleDegreePolytope`)
concludes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.ValGen2

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric Opposite
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Okounkov
open scoped Topology

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance valGen2TwTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance valGen2TwCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance valGen2TwManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} (a : LineBundleAtlas L)

include E Y hY a in
/-- **Twisted sections of a big line bundle**: if `L` is big (`vol L > 0`), then for every line
bundle `T'` (with an atlas) `H⁰(X, T' ⊗ L^k) ≠ 0` for all large `k` (twisted `thm:DXmain1`). -/
theorem exists_twisted_section_ne_zero [Nonempty (SchemeComplexPoint f)]
    (hbig : SGPT.LineBundle.IsBig f L (m + 1)) (hvol : 0 < SGPT.LineBundle.volume f L (m + 1))
    {T' : X.Modules} (aT' : LineBundleAtlas T') :
    ∀ᶠ k in atTop, ∃ s : bundleSections (bundleTensor T' (bundleTensorPower L k)) ⊤, s ≠ 0 := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let H : SchemeLineBundleMetric f (m + 1) E L := schemeLineBundleMetric f (m + 1) E a
  have hV := SGPT.Okounkov.AlgPOB.isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hbig
  have hlim := SGPT.GAGA.OkoClose.dxMain1TwistedHolds a H Y hY aT' hV
  have hle := SGPT.IGood.DXMain.volume_le_iVolume_thetaPshSupremum f E a H Y hY hV
  have hpos := lt_of_lt_of_le hvol hle
  filter_upwards [hlim.eventually (lt_mem_nhds hpos)] with k hk
  have hne : SGPT.IGood.DXMain.twistedMultiplierH0 f (m + 1) E hV.1.quasiPlurisubharmonic T' L k ≠
      0 := by
    intro h0
    unfold SGPT.IGood.DXMain.normalizedTwistedH0 at hk
    rw [h0] at hk
    simp at hk
  have := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hne)
  obtain ⟨x, hx⟩ := exists_ne (0 : SGPT.IGood.DXMain.twistedMultiplierSubmodule f (m + 1) E
    hV.1.quasiPlurisubharmonic T' L k)
  refine ⟨(bundleTensorLeftUnitIso _).hom.val.app (op ⊤) x.val, fun h0 => hx ?_⟩
  have hh := congrArg (fun α => α.val.app (op ⊤) x.val)
    (bundleTensorLeftUnitIso (bundleTensor T' (bundleTensorPower L k))).hom_inv_id
  change (bundleTensorLeftUnitIso _).inv.val.app (op ⊤)
    ((bundleTensorLeftUnitIso _).hom.val.app (op ⊤) x.val) = x.val at hh
  rw [h0, map_zero] at hh
  exact Subtype.ext hh.symm

variable (c : X) (v : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))

include E Y hY in
/-- **Source `prop:Deltaconvtwisted` for an arbitrary valuation `ν = v` and every twist `T`**:
under `Γ(L) ∈ 𝒮'(C)` for `v` (source `prop:Okounbiglbdl`, an explicit hypothesis), for every line
bundle `T` (with an atlas) and all atlases `b k` of `T ⊗ L^k`,
`Δ_{k,T}(L) = Conv{k⁻¹ ν(s) : s ∈ H⁰(X, T ⊗ L^k)^×} → Δ_ν(L)` in the Hausdorff metric (Euclidean
copies). -/
theorem tendsto_hausdorffDist_twistedDegreePolytope [Nonempty (SchemeComplexPoint f)]
    (hc : IsNonnegAt v c) {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {T : X.Modules} (aT : LineBundleAtlas T)
    (b : ∀ k : ℕ, LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    Tendsto (fun k => hausdorffDist
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' AlgebraicValuation.twistedDegreePolytope v c k (b k))
        ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' okounkovBody v c a)) atTop (𝓝 0) := by
  set Γ := sectionSemigroup v c a with hΓ
  -- `L` is big
  have hlim := SGPT.Okounkov.ValGen.tendsto_normalized_h0_okounkovBody f E Y hY a c v hS hG
  have hVpos : 0 < volume.real (okounkovBody v c a) :=
    BodyGeometry.volume_real_body_pos C _ hS hG
  have hbig : SGPT.LineBundle.IsBig f L (m + 1) := by
    refine ⟨volume.real (okounkovBody v c a) / 2, half_pos hVpos, ?_⟩
    filter_upwards [hlim.eventually (lt_mem_nhds (half_lt_self hVpos)), eventually_ge_atTop 1]
      with k hk hk1
    have hkpos : (0 : ℝ) < (k : ℝ) ^ (m + 1) := by
      have : (0 : ℝ) < k := by exact_mod_cast hk1
      positivity
    rw [inv_pow, ← div_eq_inv_mul, lt_div_iff₀ hkpos] at hk
    exact hk.le
  have hvol : 0 < SGPT.LineBundle.volume f L (m + 1) := by
    rw [SGPT.Okounkov.ValGen.volume_eq_factorial_mul_okounkovBody f E Y hY a c v hS hG]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  -- the two fixed sections
  obtain ⟨k₁, s₁, hs₁⟩ := (exists_twisted_section_ne_zero f E Y hY a hbig hvol aT).exists
  obtain ⟨k₀, s₀, hs₀⟩ :=
    (exists_twisted_section_ne_zero f E Y hY a hbig hvol (dualAtlas aT)).exists
  set bD := pairwiseTensorAtlas (dualAtlas aT) (a.tensorPower k₀)
  set w₁ := plainSectionVector v c (b k₁) s₁ hs₁
  set w₀ := plainSectionVector v c bD s₀ hs₀
  -- the lattice families
  set P : ℕ → Set (Fin (m + 1) → ℤ) := fun j => slice (Γ : Set ((Fin (m + 1) → ℤ) × ℤ)) (j : ℤ)
  set Q : ℕ → Set (Fin (m + 1) → ℤ) := fun k => AlgebraicValuation.twistedValues v c k (b k)
  have hpolyP : ∀ j, poly P j =
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' AlgebraicValuation.lineBundleDegreePolytope v c a j := fun j =>
    (image_convexHull_eq_poly P j).symm
  have hpolyQ : ∀ k, poly Q k =
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' AlgebraicValuation.twistedDegreePolytope v c k (b k) := fun k =>
    (image_convexHull_eq_poly Q k).symm
  -- the body
  have hne : (Γ : Set ((Fin (m + 1) → ℤ) × ℤ)).Nonempty := nonempty_of_generatedGroup_eq_top Γ hG
  have hKc : IsCompact ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' okounkovBody v c a) :=
    (isCompact_body C Γ hS hne).image (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous
  have hKv : Convex ℝ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' okounkovBody v c a) :=
    (convex_body Γ).linear_image (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toLinearMap
  have hKne : ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' okounkovBody v c a).Nonempty :=
    BodyGeometry.euclideanBody_nonempty C Γ hS hG
  have hP : Tendsto (fun j => hausdorffDist (poly P j)
      ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm '' okounkovBody v c a)) atTop (𝓝 0) := by
    simp only [hpolyP]
    exact SGPT.Okounkov.ValGen.tendsto_hausdorffDist_lineBundleDegreePolytope a c v hS hG
  have hPfin : ∀ j, (P j).Finite := fun j =>
    ConeSubset.finite_slice (sourceSubset C Γ hS) j
  have hPne : ∀ᶠ j in atTop, (P j).Nonempty := by
    filter_upwards [BodyGeometry.eventually_euclideanDegreeBody_nonempty C Γ hS hG] with j hj
    rw [← SGPT.Okounkov.ValGen.image_degreePolytope] at hj
    have hj' : (poly P j).Nonempty := by
      rw [hpolyP]
      exact hj
    exact (convexHull_nonempty_iff.mp hj').of_image
  -- the sandwich
  have hlow : ∀ j, ∀ x ∈ P j, x + w₁ ∈ Q (j + k₁) := by
    intro j x hx
    obtain ⟨j', t, ht, hz⟩ := hx
    obtain ⟨rfl, hjj⟩ := Prod.mk.inj hz
    have hj : j = j' := by exact_mod_cast hjj
    subst hj
    obtain ⟨hts, h⟩ := lowerProduct_vector a aT v hc j k₁ (b k₁) (b (j + k₁)) ht hs₁
    exact ⟨_, hts, h.symm⟩
  have hup : ∀ k, ∀ y ∈ Q k, y + w₀ ∈ P (k + k₀) := by
    rintro k y ⟨s, hs, rfl⟩
    obtain ⟨hst, h⟩ := upperProduct_vector a aT v hc k k₀ (b k) bD hs hs₀
    refine ⟨k + k₀, _, hst, ?_⟩
    rw [h]
  have h := tendsto_hausdorffDist_poly_of_sandwich hKc hKv hKne P Q hPfin hP hPne k₀ k₁ w₀ w₁
    hlow hup
  simp only [hpolyQ] at h
  exact h

include E Y hY in
/-- The twisted polytopes `Δ_{k,T}(L)` are nonempty for all large `k` (so that the convergence of
`prop:Deltaconvtwisted` is about genuinely defined polytopes): under `Γ(L) ∈ 𝒮'(C)` for `v`,
`H⁰(X, T ⊗ L^k) ≠ 0` for `k ≫ 0`. -/
theorem eventually_twistedDegreePolytope_nonempty [Nonempty (SchemeComplexPoint f)]
    {C : AdmissibleCone (m + 1)}
    (hS : sectionSemigroup v c a ≤ latticePoints C.cone)
    (hG : LatticeSlices.generatedGroup (sectionSemigroup v c a) = ⊤)
    {T : X.Modules} (aT : LineBundleAtlas T)
    (b : ∀ k : ℕ, LineBundleAtlas (bundleTensor T (bundleTensorPower L k))) :
    ∀ᶠ k in atTop, (AlgebraicValuation.twistedDegreePolytope v c k (b k)).Nonempty := by
  have hlim := SGPT.Okounkov.ValGen.tendsto_normalized_h0_okounkovBody f E Y hY a c v hS hG
  have hVpos : 0 < volume.real (okounkovBody v c a) :=
    BodyGeometry.volume_real_body_pos C _ hS hG
  have hbig : SGPT.LineBundle.IsBig f L (m + 1) := by
    refine ⟨volume.real (okounkovBody v c a) / 2, half_pos hVpos, ?_⟩
    filter_upwards [hlim.eventually (lt_mem_nhds (half_lt_self hVpos)), eventually_ge_atTop 1]
      with k hk hk1
    have hkpos : (0 : ℝ) < (k : ℝ) ^ (m + 1) := by
      have : (0 : ℝ) < k := by exact_mod_cast hk1
      positivity
    rw [inv_pow, ← div_eq_inv_mul, lt_div_iff₀ hkpos] at hk
    exact hk.le
  have hvol : 0 < SGPT.LineBundle.volume f L (m + 1) := by
    rw [SGPT.Okounkov.ValGen.volume_eq_factorial_mul_okounkovBody f E Y hY a c v hS hG]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  filter_upwards [exists_twisted_section_ne_zero f E Y hY a hbig hvol aT] with k ⟨s, hs⟩
  have hQ : (AlgebraicValuation.twistedValues v c k (b k)).Nonempty := ⟨_, s, hs, rfl⟩
  exact convexHull_nonempty_iff.mpr (hQ.image _)

end SGPT.Okounkov.ValGen2
