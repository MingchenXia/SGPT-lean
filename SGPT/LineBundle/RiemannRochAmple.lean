import SGPT.LineBundle.BigLineBundle
import SGPT.LineBundle.RiemannRochQuasiPolynomial
import SGPT.Foundations.Schemes.NativePolarizedResidueHilbert
import SGPT.Foundations.Schemes.OriginalPowerCommonDegreeGenerators
import SGPT.Foundations.Schemes.AffineBasicOpenSpanning
import SGPT.Foundations.Schemes.ProjectiveSectionExtension

/-!
# Asymptotic Riemann–Roch for ample line bundles on projective schemes

Algebraic infrastructure towards the asymptotic Riemann–Roch formula `thm:DXmain1`
(chapter *I-good singularities*) and the volume `vol L = lim n! h⁰(X, L^k) / k^n` of
`cor:volbigL`, in the scheme-side setting of the workspace (`SGPT.Foundations.Schemes`): `X` is a scheme
over `ℂ` with structure morphism `f`, `L : X.Modules` is a line bundle (with a rank-one atlas),
`L^k = bundleTensorPower L k` and `h⁰(X, L^k) = SGPT.LineBundle.h0 f L k`.

## Ampleness

`AmplePolarization f L` records that a positive power `L^q` is very ample: a closed immersion
`ι : X → ℙ^N_ℂ` over `ℂ` together with an isomorphism `L^q ≅ ι^* 𝒪(1)`. `IsAmple f L` is the
existence of such data. For a proper `X` over `ℂ` this is the usual definition of ampleness
(Hartshorne II.7.6: `L` is ample iff some power is very ample; immersions of proper schemes are
closed), and `IsVeryAmple f L` is the case `q = 1`.

## Main results

* `AmplePolarization.exists_h0_residuePolynomial`: Serre's theorem — on every residue class
  `k = q m + r` the dimension `h⁰(X, L^k)` is eventually a polynomial in `m` of degree `≤ N`
  (from the workspace's twisted Hilbert polynomials of coherent sheaves on `ℙ^N`).
* `AmplePolarization.exists_ne_zero_of_residue`, `AmplePolarization.eventually_exists_ne_zero`:
  Serre's theorem A — `L^k` has nonzero global sections for all large `k` (`X ≠ ∅`).
* `h0_le_h0_add_of_ne_zero`: on an integral projective scheme a nonzero section of `L^d`
  gives `h⁰(L^k) ≤ h⁰(L^{k+d})`.
* `AmplePolarization.exists_growthDegree`: there is a degree `e ≤ N` (the degree of the Hilbert
  quasi-polynomial) and `c > 0` with `h⁰(X, L^k) / k^e → c`.
* `AmplePolarization.tendsto_volume`: for every `n`, `n! h⁰(X, L^k) / k^n` converges in
  `[0, ∞]`, so the volume `SGPT.LineBundle.volume f L n` of an ample line bundle is a limit.
* `AmplePolarization.growthDegree_spec`: the growth degree `e` is characterised by
  `0 < vol_e(L) < ∞`, `vol_n(L) = ∞` for `n < e`, `vol_n(L) = 0` for `n > e`, and
  `IsBig f L n ↔ n ≤ e`.
* `AmplePolarization.h0_sub_isBigO` (**asymptotic Riemann–Roch**, error term): if
  `vol_n(L) < ∞` (`n ≥ 1`), then `h⁰(X, L^k) = (vol_n(L) / n!) k^n + O(k^{n-1})`.
* `AmplePolarization.volume_tensorPower`: `vol_n(L^r) = r^n vol_n(L)`.
* `projectiveSpacePolarization`, `isVeryAmple_projectiveSpace`: `𝒪(1)` on `ℙ^N_ℂ` is very ample
  (the hypotheses are satisfiable).

For `X` smooth of relative dimension `n`, the finiteness hypothesis `vol_n(L) < ∞` is discharged
and the leading coefficient is identified with the self-intersection number `(L^n)` in
`SGPT.LineBundle.IntersectionAmple`.

## Not formalized here

Mixed intersection numbers and the extension to nef line bundles.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.LineBundle

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Opposite TopologicalSpace
open Polynomial Asymptotics
open scoped ENNReal Nat Topology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (L : X.Modules)

/-- An ample polarization of `L`: a positive power `L^q` is very ample, i.e. isomorphic to the
pullback of `𝒪(1)` under a closed immersion `ι : X → ℙ^N_ℂ` over `ℂ`. -/
structure AmplePolarization where
  /-- The power `q` of `L` which is very ample. -/
  power : ℕ
  /-- The power is positive. -/
  power_pos : 0 < power
  /-- The dimension `N` of the ambient projective space. -/
  ambientDimension : ℕ
  /-- The closed immersion `ι : X → ℙ^N_ℂ`. -/
  map : X ⟶ polynomialProj ℂ ambientDimension
  /-- `ι` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion map
  /-- `ι` is a morphism over `ℂ`. -/
  over_base : map ≫ polynomialProjStructureMap ℂ ambientDimension = f
  /-- The isomorphism `L^q ≅ ι^* 𝒪(1)`. -/
  iso : bundleTensorPower L power ≅
    (Scheme.Modules.pullback map).obj (polynomialProjTwistingLine ℂ ambientDimension).sheaf

attribute [instance] AmplePolarization.isClosedImmersion

/-- `L` is ample: some positive power of `L` is very ample. -/
def IsAmple : Prop := Nonempty (AmplePolarization f L)

/-- `L` is very ample: `L ≅ ι^* 𝒪(1)` for a closed immersion `ι : X → ℙ^N_ℂ` over `ℂ`. -/
def IsVeryAmple : Prop := ∃ P : AmplePolarization f L, P.power = 1

variable {f L}

theorem IsVeryAmple.isAmple (h : IsVeryAmple f L) : IsAmple f L := ⟨h.choose⟩

/-- `𝒪(1)` on `ℙ^N_ℂ` is very ample, with the identity embedding (so the hypotheses of this file
are satisfiable). -/
def projectiveSpacePolarization (N : ℕ) :
    AmplePolarization (polynomialProjStructureMap ℂ N) (polynomialProjTwistingLine ℂ N).sheaf where
  power := 1
  power_pos := one_pos
  ambientDimension := N
  map := 𝟙 _
  isClosedImmersion := inferInstance
  over_base := Category.id_comp _
  iso := bundleTensorLeftUnitIso _ ≪≫ ((Scheme.Modules.pullbackId _).app _).symm

/-- `𝒪(1)` on `ℙ^N_ℂ` is very ample. -/
theorem isVeryAmple_projectiveSpace (N : ℕ) :
    IsVeryAmple (polynomialProjStructureMap ℂ N) (polynomialProjTwistingLine ℂ N).sheaf :=
  ⟨projectiveSpacePolarization N, rfl⟩

namespace AmplePolarization

/-- The underlying closed projective embedding of `X`. -/
def toClosedProjectiveEmbedding (P : AmplePolarization f L) : ClosedProjectiveEmbedding f where
  ambientDimension := P.ambientDimension
  map := P.map
  closedImmersion := P.isClosedImmersion
  over_base := P.over_base

/-- **Serre's theorem (Hilbert quasi-polynomial).** On every residue class `k = q m + r` the
dimension `h⁰(X, L^k)` is eventually a polynomial in `m`, of degree at most `N`. -/
theorem exists_h0_residuePolynomial (P : AmplePolarization f L) (a : LineBundleAtlas L)
    (r : ℕ) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ P.ambientDimension ∧ ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      (h0 f L (P.power * m + r) : ℚ) = Q.eval (m : ℚ) := by
  obtain ⟨Q, hQ, b, hb⟩ := nativePolarizedResidueSectionDimension_eventualPolynomial_over
    (⟨L, a⟩ : IntrinsicLineBundle X) P.ambientDimension P.map P.power P.iso f P.over_base r
  exact ⟨Q, hQ, b, fun m hm => hb m hm⟩

/-- The residue polynomials of `h⁰(X, L^k)`, as real polynomials with one common bound. -/
theorem exists_h0_uniformResiduePolynomial (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    ∃ Q : Fin P.power → Polynomial ℝ, (∀ r, (Q r).natDegree ≤ P.ambientDimension) ∧
      ∃ b : ℕ, ∀ (r : Fin P.power) (m : ℕ), b ≤ m →
        (h0 f L (P.power * m + r.val) : ℝ) = (Q r).eval (m : ℝ) := by
  classical
  choose Q hQ b hb using fun r : Fin P.power => P.exists_h0_residuePolynomial a r.val
  refine ⟨fun r => (Q r).map (algebraMap ℚ ℝ), fun r => ?_, Finset.univ.sup b, fun r m hm => ?_⟩
  · simpa only [natDegree_map] using hQ r
  · have hm' : b r ≤ m := (Finset.le_sup (f := b) (Finset.mem_univ r)).trans hm
    have he : ((Q r).map (algebraMap ℚ ℝ)).eval (m : ℝ) = algebraMap ℚ ℝ ((Q r).eval (m : ℚ)) := by
      simpa only [map_natCast] using (Polynomial.eval_map_apply (algebraMap ℚ ℝ) (p := Q r) (m : ℚ))
    rw [he, ← hb r m hm']
    simp

/-- The frame coefficients of a local frame identify sections with functions, so the sections of
a line bundle over a nonempty open contained in a frame domain form a nontrivial module. -/
private theorem sections_nontrivial_of_frame {M : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame M U) (i : V ⟶ U) (hV : (V : Set X).Nonempty) :
    ∃ y : bundleSections M V, y ≠ 0 := by
  obtain ⟨x, hx⟩ := hV
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  refine ⟨(e.coefficients i).symm 1, fun h => ?_⟩
  have h1 : (1 : Γ(X, V)) = 0 := by
    have := congrArg (e.coefficients i) h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  exact one_ne_zero h1

/-- **Serre's theorem A (nonvanishing).** For every residue `r`, the bundle `L^{q D + r}` has a
nonzero global section for all large `D` (if `X ≠ ∅`). -/
theorem exists_ne_zero_of_residue [Nonempty X] (P : AmplePolarization f L)
    (a : LineBundleAtlas L) (r : ℕ) :
    ∃ B : ℕ, ∀ D : ℕ, B ≤ D → ∃ s : SectionSpace f L (P.power * D + r), s ≠ 0 := by
  obtain ⟨m, B, h⟩ := nativePositiveProjective_exists_commonDegree_originalPower_chart_generators
    ℂ P.ambientDimension P.map (⟨L, a⟩ : IntrinsicLineBundle X) P.power P.iso r
  refine ⟨B, fun D hD => ?_⟩
  obtain ⟨s, hs⟩ := h D hD
  by_contra hall
  push Not at hall
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hx : x ∈ iSup (actualPolynomialProjectivePullbackCoordinateOpens P.map) := by
    rw [actualPolynomialProjectivePullbackCoordinateOpens_covers]
    trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  let V := P.map ⁻¹ᵁ polynomialProjCoordinateOpen ℂ P.ambientDimension i
  have hxV : x ∈ V := hxi
  have hV : IsAffineOpen V :=
    (polynomialProjCoordinateOpen_isAffine ℂ P.ambientDimension i).preimage P.map
  let M := bundleTensorPower L (P.power * D + r)
  let a' := a.tensorPower (P.power * D + r)
  have : M.IsQuasicoherent := a'.isQuasicoherent
  obtain ⟨k, hxk⟩ := a'.covers x
  obtain ⟨g, hgk, hxg⟩ := hV.exists_basicOpen_le (show a'.opens k from ⟨x, hxk⟩) hxV
  have hspan := affineBasicOpen_restricted_sections_span M hV
    (fun b => M.val.map V.leTop.op (s b)) (hs i) g
  have hzero : ∀ b, M.val.map (homOfLE (X.basicOpen_le g)).op (M.val.map V.leTop.op (s b)) = 0 := by
    intro b
    have hsb : s b = 0 := hall (s b)
    rw [hsb, map_zero, map_zero]
  have hbot : Submodule.span Γ(X, X.basicOpen g)
      (Set.range fun b => M.val.map (homOfLE (X.basicOpen_le g)).op
        (M.val.map V.leTop.op (s b))) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨b, rfl⟩
    exact hzero b
  obtain ⟨y, hy⟩ := sections_nontrivial_of_frame (a'.frame k) (homOfLE hgk) ⟨x, hxg⟩
  have hy' : y ∈ (⊥ : Submodule Γ(X, X.basicOpen g) (bundleSections M (X.basicOpen g))) := by
    rw [← hbot, hspan]
    trivial
  exact hy ((Submodule.mem_bot _).mp hy')

/-- **Serre's theorem A (nonvanishing), all degrees.** `L^k` has a nonzero global section for all
large `k` (if `X ≠ ∅`). -/
theorem eventually_exists_ne_zero [Nonempty X] (P : AmplePolarization f L)
    (a : LineBundleAtlas L) : ∀ᶠ k : ℕ in atTop, ∃ s : SectionSpace f L k, s ≠ 0 := by
  classical
  choose B hB using fun r : Fin P.power => P.exists_ne_zero_of_residue a r.val
  filter_upwards [eventually_ge_atTop (P.power * Finset.univ.sup B)] with k hk
  let r : Fin P.power := ⟨k % P.power, Nat.mod_lt _ P.power_pos⟩
  have hD : B r ≤ k / P.power :=
    (Finset.le_sup (f := B) (Finset.mem_univ r)).trans
      ((Nat.le_div_iff_mul_le P.power_pos).mpr (by rw [Nat.mul_comm]; exact hk))
  obtain ⟨s, hs⟩ := hB r (k / P.power) hD
  have hk' : P.power * (k / P.power) + r.val = k := Nat.div_add_mod k P.power
  exact hk' ▸ ⟨s, hs⟩

end AmplePolarization

/-- On an integral projective scheme, multiplication by a nonzero section of `L^d` embeds
`H⁰(X, L^k)` into `H⁰(X, L^{k+d})`. -/
theorem h0_le_h0_add_of_ne_zero [IsIntegral X] (E : ClosedProjectiveEmbedding f)
    (a : LineBundleAtlas L) {d : ℕ} {u : SectionSpace f L d} (hu : u ≠ 0) (k : ℕ) :
    h0 f L k ≤ h0 f L (k + d) := by
  have := SectionSpace.finiteDimensional f E a (d + k)
  have hinj : Function.Injective (SectionSpace.mul f a d k u) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    by_contra htne
    exact SectionSpace.mul_ne_zero f a hu htne ht
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Nat.add_comm d k] at hle
  exact hle

namespace AmplePolarization

/-- Nonzero sections in two consecutive degrees give the shift inequalities used to compare the
residue polynomials of `h⁰(X, L^k)`. -/
theorem exists_consecutive_shifts [IsIntegral X] (P : AmplePolarization f L)
    (a : LineBundleAtlas L) :
    ∃ d : ℕ, (∀ k, (h0 f L k : ℝ) ≤ h0 f L (k + d)) ∧
      ∀ k, (h0 f L k : ℝ) ≤ h0 f L (k + (d + 1)) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (P.eventually_exists_ne_zero a)
  obtain ⟨u, hu⟩ := hK K le_rfl
  obtain ⟨v, hv⟩ := hK (K + 1) (Nat.le_succ K)
  refine ⟨K, fun k => ?_, fun k => ?_⟩
  · exact_mod_cast h0_le_h0_add_of_ne_zero P.toClosedProjectiveEmbedding a hu k
  · exact_mod_cast h0_le_h0_add_of_ne_zero P.toClosedProjectiveEmbedding a hv k

/-- `h⁰(X, L^k) > 0` for all large `k` (ample `L` on a nonempty `X`). -/
theorem eventually_h0_pos [IsIntegral X] (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    ∀ᶠ k : ℕ in atTop, 0 < h0 f L k := by
  have := P.toClosedProjectiveEmbedding
  filter_upwards [P.eventually_exists_ne_zero a] with k hk
  obtain ⟨s, hs⟩ := hk
  have := SectionSpace.finiteDimensional f P.toClosedProjectiveEmbedding a k
  have : Nontrivial (SectionSpace f L k) := ⟨⟨s, 0, hs⟩⟩
  exact Module.finrank_pos

/-- **Hilbert asymptotics of an ample line bundle.** There is a degree `e ≤ N` (the growth
degree, i.e. the degree of the Hilbert quasi-polynomial) and `c > 0` with
`h⁰(X, L^k) / k^e → c`. -/
theorem exists_growthDegree [IsIntegral X] (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    ∃ e ≤ P.ambientDimension, ∃ c : ℝ, 0 < c ∧
      Tendsto (fun k : ℕ => (h0 f L k : ℝ) / (k : ℝ) ^ e) atTop (𝓝 c) := by
  obtain ⟨Q, hQdeg, b, hQ⟩ := P.exists_h0_uniformResiduePolynomial a
  refine QuasiPolynomial.exists_growthDegree (fun k => (h0 f L k : ℝ)) P.power_pos
    P.ambientDimension b Q hQdeg hQ (fun k => Nat.cast_nonneg _) ?_
    (P.exists_consecutive_shifts a)
  filter_upwards [P.eventually_h0_pos a] with k hk
  exact_mod_cast hk

/-- The limit of `n! h⁰(X, L^k) / k^n` in `[0, ∞]` exists in every normalising degree `n`, in
terms of the growth degree `e` and the limit `c` of `h⁰(X, L^k) / k^e`. -/
theorem tendsto_ratio_of_growthDegree {e : ℕ} {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun k : ℕ => (h0 f L k : ℝ) / (k : ℝ) ^ e) atTop (𝓝 c)) (n : ℕ) :
    Tendsto (fun k : ℕ => ((n ! : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ n) atTop
      (𝓝 (if n < e then ∞ else if n = e then ENNReal.ofReal ((n ! : ℝ) * c) else 0)) := by
  rcases lt_trichotomy n e with hne | rfl | hen
  · rw [if_pos hne]
    exact QuasiPolynomial.tendsto_ennreal_ratio_of_tendsto_atTop (h0 f L) n
      (QuasiPolynomial.tendsto_div_pow_atTop_of_gt _ hc0 hne hc)
  · rw [if_neg (lt_irrefl _), if_pos rfl]
    exact QuasiPolynomial.tendsto_ennreal_ratio_of_tendsto (h0 f L) n hc
  · rw [if_neg (by omega), if_neg (by omega)]
    have h := QuasiPolynomial.tendsto_ennreal_ratio_of_tendsto (h0 f L) n
      (QuasiPolynomial.tendsto_div_pow_of_lt _ hen hc)
    simpa using h

/-- **The volume of an ample line bundle is a limit.** For every `n`,
`n! h⁰(X, L^k) / k^n → vol_n(L)` in `[0, ∞]` (`vol_n = SGPT.LineBundle.volume f L n`, defined as
the `limsup`). -/
theorem tendsto_volume [IsIntegral X] (P : AmplePolarization f L) (a : LineBundleAtlas L)
    (n : ℕ) :
    Tendsto (fun k : ℕ => ((n ! : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ n) atTop
      (𝓝 (volume f L n)) := by
  obtain ⟨e, -, c, hc0, hc⟩ := P.exists_growthDegree a
  have h := tendsto_ratio_of_growthDegree hc0 hc n
  have hv : volume f L n = _ := h.limsup_eq
  rw [hv]
  exact h

/-- **Growth degree of an ample line bundle.** There is `e ≤ N` such that `0 < vol_e(L) < ∞`,
`vol_n(L) = ∞` for `n < e`, `vol_n(L) = 0` for `n > e`, and `L` is big in the section-growth
sense of dimension `n` (`IsBig f L n`) exactly for `n ≤ e`. (For `X` of dimension `n` one has
`e = n`; this is not formalized.) -/
theorem growthDegree_spec [IsIntegral X] (P : AmplePolarization f L) (a : LineBundleAtlas L) :
    ∃ e ≤ P.ambientDimension, (0 < volume f L e ∧ volume f L e ≠ ∞) ∧
      (∀ n, n < e → volume f L n = ∞) ∧ (∀ n, e < n → volume f L n = 0) ∧
      ∀ n, IsBig f L n ↔ n ≤ e := by
  obtain ⟨e, he, c, hc0, hc⟩ := P.exists_growthDegree a
  have hvol (n : ℕ) : volume f L n =
      if n < e then ∞ else if n = e then ENNReal.ofReal ((n ! : ℝ) * c) else 0 :=
    (tendsto_ratio_of_growthDegree hc0 hc n).limsup_eq
  refine ⟨e, he, ⟨?_, ?_⟩, fun n hn => ?_, fun n hn => ?_, fun n => ⟨fun hbig => ?_, fun hn => ?_⟩⟩
  · rw [hvol, if_neg (lt_irrefl _), if_pos rfl]
    exact ENNReal.ofReal_pos.mpr (mul_pos (by exact_mod_cast Nat.factorial_pos e) hc0)
  · rw [hvol, if_neg (lt_irrefl _), if_pos rfl]
    exact ENNReal.ofReal_ne_top
  · rw [hvol, if_pos hn]
  · rw [hvol, if_neg (by omega), if_neg (by omega)]
  · by_contra hlt
    push Not at hlt
    obtain ⟨c', hc', hev⟩ := hbig
    have h0lim := QuasiPolynomial.tendsto_div_pow_of_lt (fun k => (h0 f L k : ℝ)) hlt hc
    have hge : ∀ᶠ k : ℕ in atTop, c' ≤ (h0 f L k : ℝ) / (k : ℝ) ^ n := by
      filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
      have hkpos : (0 : ℝ) < (k : ℝ) ^ n := pow_pos (by exact_mod_cast hk1) n
      rw [le_div_iff₀ hkpos]
      exact hk
    have := ge_of_tendsto h0lim hge
    linarith
  · refine ⟨c / 2, by linarith, ?_⟩
    have hev : ∀ᶠ k : ℕ in atTop, c / 2 < (h0 f L k : ℝ) / (k : ℝ) ^ e :=
      hc.eventually (lt_mem_nhds (by linarith))
    filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkpos : (0 : ℝ) < (k : ℝ) ^ e := pow_pos (by linarith) e
    rw [lt_div_iff₀ hkpos] at hk
    have hpow : (k : ℝ) ^ n ≤ (k : ℝ) ^ e := pow_le_pow_right₀ hk1' hn
    nlinarith

/-- `L` ample on an integral `X` is big in its growth degree; in particular `IsBig f L n` holds
whenever `vol_n(L) < ∞` and `vol_n(L) > 0`. -/
theorem isBig_of_volume_pos [IsIntegral X] (P : AmplePolarization f L) (a : LineBundleAtlas L)
    {n : ℕ} (hpos : 0 < volume f L n) : IsBig f L n := by
  obtain ⟨e, -, -, -, hgt, hbig⟩ := P.growthDegree_spec a
  refine (hbig n).mpr ?_
  by_contra h
  push Not at h
  exact (ne_of_gt hpos) (hgt n h)

/-- **Asymptotic Riemann–Roch for ample line bundles.** If `vol_n(L) < ∞` (`n ≥ 1`; for `X` of
dimension `n` this is the growth bound `h⁰(X, L^k) = O(k^n)`), then
`h⁰(X, L^k) = (vol_n(L) / n!) k^n + O(k^{n-1})`. -/
theorem h0_sub_isBigO [IsIntegral X] (P : AmplePolarization f L) (a : LineBundleAtlas L)
    {n : ℕ} (hn : 1 ≤ n) (hfin : volume f L n ≠ ∞) :
    (fun k : ℕ => (h0 f L k : ℝ) - ((volume f L n).toReal / (n ! : ℝ)) * (k : ℝ) ^ n)
      =O[atTop] (fun k : ℕ => (k : ℝ) ^ (n - 1)) := by
  obtain ⟨Q, -, b, hQ⟩ := P.exists_h0_uniformResiduePolynomial a
  -- `vol_n(L) < ∞` forces all residue polynomials to have degree `≤ n`
  have hnot : ¬ Tendsto (fun k : ℕ => (h0 f L k : ℝ) / (k : ℝ) ^ n) atTop atTop := fun ht =>
    hfin (QuasiPolynomial.tendsto_ennreal_ratio_of_tendsto_atTop (h0 f L) n ht).limsup_eq
  have hpos : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < h0 f L k := by
    filter_upwards [P.eventually_h0_pos a] with k hk
    exact_mod_cast hk
  have hdeg := QuasiPolynomial.natDegree_le_of_not_tendsto_atTop (fun k => (h0 f L k : ℝ))
    P.power_pos b Q hQ (fun k => Nat.cast_nonneg _) hpos (P.exists_consecutive_shifts a) hnot
  have hcoef := QuasiPolynomial.coeff_eq_of_shifts (fun k => (h0 f L k : ℝ)) P.power_pos n b Q
    hdeg hQ (P.exists_consecutive_shifts a)
  set β := (Q ⟨0, P.power_pos⟩).coeff n with hβ
  have hcommon : ∀ r, (Q r).coeff n = β := fun r => hcoef r _
  have htend := QuasiPolynomial.tendsto_div_pow_of_common_coeff (fun k => (h0 f L k : ℝ))
    P.power_pos n b Q β hdeg hcommon hQ
  have hlimnn : 0 ≤ β / (P.power : ℝ) ^ n :=
    ge_of_tendsto' htend fun k => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hvol : volume f L n = ENNReal.ofReal ((n ! : ℝ) * (β / (P.power : ℝ) ^ n)) :=
    (QuasiPolynomial.tendsto_ennreal_ratio_of_tendsto (h0 f L) n htend).limsup_eq
  have hcoeffval : (volume f L n).toReal / (n ! : ℝ) = β / (P.power : ℝ) ^ n := by
    rw [hvol, ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hlimnn)]
    have : (n ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    field_simp
  rw [hcoeffval]
  exact SGPT.Foundations.Schemes.residuePolynomial_full_isBigO_of_common_coeff (fun k => (h0 f L k : ℝ))
    P.power P.power_pos n hn b Q β hdeg hcommon hQ

/-- **Asymptotic Riemann–Roch, limit form.** If `vol_n(L) < ∞`, then
`n! h⁰(X, L^k) / k^n → vol_n(L)` as real numbers. -/
theorem tendsto_real_volume [IsIntegral X] (P : AmplePolarization f L) (a : LineBundleAtlas L)
    {n : ℕ} (hfin : volume f L n ≠ ∞) :
    Tendsto (fun k : ℕ => (n ! : ℝ) * (h0 f L k : ℝ) / (k : ℝ) ^ n) atTop
      (𝓝 (volume f L n).toReal) := by
  have h := (ENNReal.tendsto_toReal hfin).comp (P.tendsto_volume a n)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  simp only [Function.comp_apply]
  rw [QuasiPolynomial.ennreal_ratio_eq_ofReal (h0 f L) n k hk,
    ENNReal.toReal_ofReal (by positivity)]
  ring

end AmplePolarization

/-- Isomorphic tensor powers have the same `h⁰` (the global sections of an isomorphism of
sheaves of modules are linear over the constants of `f`). -/
theorem h0_eq_of_iso {M N : X.Modules} {k l : ℕ}
    (E : bundleTensorPower M k ≅ bundleTensorPower N l) : h0 f M k = h0 f N l :=
  (nativeModuleIsoBaseGlobalSections E (schemeGlobalConstants f)).toLinearEquiv.finrank_eq

/-- `h⁰(X, (L^r)^m) = h⁰(X, L^{rm})`. -/
theorem h0_tensorPower (a : LineBundleAtlas L) (r m : ℕ) :
    h0 f (bundleTensorPower L r) m = h0 f L (r * m) :=
  h0_eq_of_iso (nativeLineTensorPowerMulIso a r m).symm

namespace AmplePolarization

/-- **Homogeneity of the volume of an ample line bundle:** `vol_n(L^r) = r^n vol_n(L)` for
`r > 0`. -/
theorem volume_tensorPower [IsIntegral X] (P : AmplePolarization f L) (a : LineBundleAtlas L)
    (n : ℕ) {r : ℕ} (hr : 0 < r) :
    volume f (bundleTensorPower L r) n = (r : ℝ≥0∞) ^ n * volume f L n := by
  have hlim := P.tendsto_volume a n
  have hsub : Tendsto (fun m : ℕ => r * m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hr) tendsto_id
  have hcomp := ENNReal.Tendsto.const_mul (hlim.comp hsub)
    (Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)) : volume f L n ≠ 0 ∨
      (r : ℝ≥0∞) ^ n ≠ ∞)
  have hG : Tendsto (fun m : ℕ => ((n ! : ℝ≥0∞) * (h0 f (bundleTensorPower L r) m : ℝ≥0∞)) /
      (m : ℝ≥0∞) ^ n) atTop (𝓝 ((r : ℝ≥0∞) ^ n * volume f L n)) := by
    refine hcomp.congr' (Eventually.of_forall fun m => ?_)
    simp only [Function.comp_apply]
    rw [h0_tensorPower a r m, Nat.cast_mul, mul_pow, ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ (pow_ne_zero n (by exact_mod_cast hr.ne'))
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r))]
  exact hG.limsup_eq

end AmplePolarization

end SGPT.LineBundle
