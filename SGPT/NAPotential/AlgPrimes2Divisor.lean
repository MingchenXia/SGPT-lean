import SGPT.NAPotential.AlgPrimes2Order
import SGPT.NAPotential.AlgPrimesHypersurface
import SGPT.Foundations.Analysis.Pending.LocalGiraudTransform
import SGPT.Foundations.Analysis.Pending.BlowupSNCTransform
import SGPT.Foundations.Analysis.Pending.IdealPowerNormalOrder
import SGPT.Okounkov.SchemeNativeAnalyticSubset

/-!
# Algebraic prime divisors centred on a divisor of `X` are realized


Let `X` be a smooth projective integral complex scheme of dimension `m + 1` and `D` an algebraic
prime divisor over `X` (`SGPT.NAPotential.Berkovich.PrimeDivisorOver`) whose valuation `ord_D`
has a centre `z` of codimension one in `X`, i.e. `ord_D` is the order of vanishing along the
prime divisor `{z}‾` of `X` itself.  Then `D` is realized by an analytic presentation
(`exists_isRealizedBy_of_coheight_center_eq_one`): the clause of
`SGPT.NAPotential.Berkovich.AlgebraicPrimesRealized` for these `D`, with the identity
modification.  This is step (d) of the plan of `claude-alg-primes:remaining` (the order
comparison at a smooth point of a prime divisor of a smooth model), carried out on `X`.

* `exists_divisorFlattening`: at the smooth point `y` of `exists_regular_point`, the analytic set
  `T = {z}‾(ℂ)` is a smooth hypersurface with a flattening whose equation is the analytic germ of
  the local equation `u` (TN's hypersurface coordinates from a nonzero derivative);
* `emultiplicity_map_of_faithfullyFlat` and the faithful flatness of
  `𝒪_{X,y} → 𝒪^an_{X,y}`: the analytic order along `T` at `y` of `g^an` is the multiplicity of
  `u` in `g`, which is `ord_D(g)` (`ord_eq_emultiplicity`);
* `exists_isRealizedBy_of_coheight_center_eq_one`: by
  `SGPT.NAPotential.AlgPrimes.exists_isRealizedBy_of_analyticSubset` with `ρ = id`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes2

open Set Filter
open scoped Topology Manifold ContDiff
open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.NAPotential.Berkovich SGPT.NAPotential.FSPos
open SGPT.GAGA.H0S SGPT.NAPotential.TowerAlg SGPT.NAPotential.AlgPrimes
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

/-- **Multiplicities are preserved by faithfully flat maps.** -/
theorem emultiplicity_map_of_faithfullyFlat {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.FaithfullyFlat) (a b : R) :
    emultiplicity (φ a) (φ b) = emultiplicity a b := by
  let := φ.toAlgebra
  let : Module.FaithfullyFlat R S := hφ
  refine emultiplicity_eq_emultiplicity_iff.mpr fun k => ?_
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton, ← map_pow]
  have hmap : Ideal.span {φ (a ^ k)} = (Ideal.span {a ^ k}).map φ := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hmap]
  have := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (Ideal.span {a ^ k})
  constructor
  · intro h
    rw [← this]
    exact h
  · intro h
    exact Ideal.mem_map_of_mem _ h

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [IsProper f]

local instance algPrimes2DivPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance algPrimes2DivPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance algPrimes2DivPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable [IsIntegral X]

omit [IsIntegral X] in
/-- The chart germ of the representative of an algebraic germ is its analytic germ in the
preferred chart. -/
theorem chartTranslatedGerm_stalkRep (y : SchemeComplexPoint f)
    (g : X.presheaf.stalk (schemeComplexPointImage f y)) :
    chartTranslatedGerm y y (mem_chart_source _ y) (stalkRep m y g) (stalkRep_holomorphicAt y g) =
      stalkToModel f (m + 1) y g := by
  change _ = NativeHolGerm.chartEquiv y (schemeNativeStalkGerm f (m + 1) y g)
  rw [schemeNativeStalkGerm_eq_mk_stalkRep]
  apply Subtype.ext
  rw [NativeHolGerm.chartEquiv_mk]
  rfl

omit [IsIntegral X] in
/-- **The flattening of a prime divisor at a smooth point by its local equation.**  In the
situation of `exists_regular_point`, the analytic set `T = {z}‾(ℂ)` is a smooth hypersurface at
`y`, with a flattening whose equation is the analytic germ of `u`. -/
theorem exists_divisorFlattening (E : ClosedProjectiveEmbedding f) {z : X} {V : X.Opens}
    (hV : IsAffineOpen V) (hzV : z ∈ V) {u s : Γ(X, V)}
    (hu : u ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal)
    (hsq : ∀ a ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal, s * a ∈ Ideal.span {u})
    {y : SchemeComplexPoint f} (hy : schemeComplexPointImage f y ∈ V)
    (hzy : z ⤳ schemeComplexPointImage f y)
    (hsy : s ∉ (hV.primeIdealOf ⟨schemeComplexPointImage f y, hy⟩).asIdeal)
    {v : ComplexModel (m + 1)}
    (hv : germDeriv v (stalkToModel f (m + 1) y
      (X.presheaf.germ V (schemeComplexPointImage f y) hy u)) ≠ 0) :
    ∃ Ψ : DivisorFlattening (m := m) (schemeNativeAlgebraicTrace f (closure {z})) y,
      divisorEquationGerm Ψ = stalkToModel f (m + 1) y
        (X.presheaf.germ V (schemeComplexPointImage f y) hy u) := by
  let := E.isSeparated
  let := E.quasiCompact
  set T := schemeNativeAlgebraicTrace f (closure {z}) with hTdef
  set F := schemeOpenRegularFunction f (m + 1) E V u with hFdef
  set O : Set (SchemeComplexPoint f) :=
    schemeComplexPointImage f ⁻¹' ((V : Set X) ∩ X.basicOpen s) with hOdef
  have hOopen : IsOpen O :=
    (V.isOpen.inter (X.basicOpen s).isOpen).preimage (schemeComplexPointImage_continuous f)
  have hyO : y ∈ O := ⟨hy, (mem_basicOpen_iff_notMem_primeIdealOf hV s hy).mpr hsy⟩
  have hFhol : ∀ p ∈ O, HolomorphicAt (m + 1) F p := fun p hp =>
    schemeOpenRegularFunction_holomorphicAt f (m + 1) E V u p hp.1
  -- `T = {F = 0}` on `O`
  have hT : ∀ p ∈ O, p ∈ T ↔ F p = 0 := by
    intro p ⟨hpV, hps⟩
    have hsp : s ∉ (hV.primeIdealOf ⟨_, hpV⟩).asIdeal :=
      (mem_basicOpen_iff_notMem_primeIdealOf hV s hpV).mp hps
    have hF0 : F p = 0 ↔ u ∈ (hV.primeIdealOf ⟨_, hpV⟩).asIdeal := by
      rw [← not_iff_not, ← ne_eq, hFdef, schemeOpenRegularFunction_ne_zero_iff f E (m + 1) V u p hpV,
        mem_basicOpen_iff_notMem_primeIdealOf hV u hpV]
    rw [hF0]
    change schemeComplexPointImage f p ∈ closure {z} ↔ _
    rw [← specializes_iff_mem_closure, specializes_iff_primeIdealOf_le hV hpV hzV]
    constructor
    · intro h
      exact h hu
    · intro h a ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hsq a ha)
      have hsa : s * a ∈ (hV.primeIdealOf ⟨_, hpV⟩).asIdeal := by
        rw [← hc]; exact Ideal.mul_mem_left _ _ h
      exact ((hV.primeIdealOf ⟨_, hpV⟩).isPrime.mem_or_mem hsa).resolve_left hsp
  have hyT : y ∈ T := subset_closure (Set.mem_singleton z) |> fun _ =>
    (specializes_iff_mem_closure.mp hzy)
  have hFy : F y = 0 := (hT y hyO).mp hyT
  -- the derivative of `F` at `y`
  set e := complexChartAt (n := m + 1) y with he
  have hd : DerivativeIdeal.chartDeriv e v F y ≠ 0 := by
    have h := germDeriv_stalkToModel_germ (f := f) (E := E) (n := m + 1) V u y hy v
    rw [h] at hv
    exact hv
  obtain ⟨hn, W, hWs, hWinj, hWu⟩ := LocalGiraudTransform.exists_hypersurface_coords
    (hFhol y hyO) (mem_complexChartAt_source y) hd
  have hO' : IsOpen (O ∩ (chartAt (ComplexModel (m + 1)) y).source) :=
    hOopen.inter (chartAt (ComplexModel (m + 1)) y).open_source
  obtain ⟨Θ, hΘt, hΘ0, hΘ⟩ := BlowupSNCTransform.exists_recentred_coords hO'
    (fun z' hz' => hWs z' hz'.2 (hFhol z' hz'.1)) ⟨hyO, mem_chart_source _ y⟩ hWinj
  have hlast : (⟨m + 1 - 1, Nat.sub_lt hn one_pos⟩ : Fin (m + 1)) = Fin.last m := by
    ext; simp
  have hΘlast : ∀ {y' : SchemeComplexPoint f}, y' ∈ (complexChartAt (n := m + 1) y).val.source →
      (complexChartAt (n := m + 1) y).val y' ∈ Θ.source →
        y' ∈ O ∧ Θ.toFun ((complexChartAt (n := m + 1) y).val y') (Fin.last m) = F y' := by
    intro y' hy' hy'Θ
    obtain ⟨hy'O, hΘy'⟩ := hΘ hy' hy'Θ
    refine ⟨hy'O.1, ?_⟩
    rw [hΘy', PiLp.sub_apply, ← hlast, hWu, hWu, hFy, sub_zero]
  let Ψ : DivisorFlattening (m := m) T y :=
    { Φ := Θ
      source_subset := hΘt
      map_center := hΘ0
      mem_iff := fun y' hy' hy'Θ => by
        obtain ⟨hy'O, hval⟩ := hΘlast hy' hy'Θ
        rw [hval]
        exact hT y' hy'O }
  refine ⟨Ψ, ?_⟩
  -- the equation germ is the germ of `F`
  have hgerm : stalkToModel f (m + 1) y (X.presheaf.germ V (schemeComplexPointImage f y) hy u) =
      NativeHolGerm.chartEquiv y (NativeHolGerm.mk F (hFhol y hyO)) := by
    change NativeHolGerm.chartEquiv y (schemeNativeStalkGerm f (m + 1) y _) = _
    rw [← schemeOpenRegularFunction_germ f (m + 1) E V u y hy]
  rw [hgerm]
  apply Subtype.ext
  rw [NativeHolGerm.chartEquiv_mk]
  unfold divisorEquationGerm
  rw [HolGerm.coe_mk]
  apply Filter.Germ.coe_eq.mpr
  have ht : Tendsto (fun w : ComplexModel (m + 1) => w + (complexChartAt (n := m + 1) y).val y)
      (𝓝 0) (𝓝 ((complexChartAt (n := m + 1) y).val y)) := by
    simpa only [zero_add] using
      (continuous_add_const ((complexChartAt (n := m + 1) y).val y)).tendsto 0
  filter_upwards [ht.eventually ((complexChartAt (n := m + 1) y).val.open_target.mem_nhds
      ((complexChartAt (n := m + 1) y).val.map_source (mem_complexChartAt_source y))),
    ht.eventually (Θ.isOpen_source.mem_nhds Θ.center_mem_source)] with w hwt hwΘ
  have hys : (complexChartAt (n := m + 1) y).val.symm (w + (complexChartAt (n := m + 1) y).val y) ∈
      (complexChartAt (n := m + 1) y).val.source :=
    (complexChartAt (n := m + 1) y).val.map_target hwt
  have hcc : (complexChartAt (n := m + 1) y).val ((complexChartAt (n := m + 1) y).val.symm
      (w + (complexChartAt (n := m + 1) y).val y)) = w + (complexChartAt (n := m + 1) y).val y :=
    (complexChartAt (n := m + 1) y).val.right_inv hwt
  have hmem : (complexChartAt (n := m + 1) y).val ((complexChartAt (n := m + 1) y).val.symm
      (w + (complexChartAt (n := m + 1) y).val y)) ∈ Θ.source := by rw [hcc]; exact hwΘ
  have h := (hΘlast hys hmem).2
  rw [hcc] at h
  exact h

omit [IsIntegral X] in
/-- `𝒪_{X,y} → 𝒪_{ℂⁿ,0}` (the analytic germ in the preferred chart) is faithfully flat. -/
theorem stalkToModel_faithfullyFlat (y : SchemeComplexPoint f) :
    (stalkToModel f (m + 1) y).FaithfullyFlat :=
  RingHom.FaithfullyFlat.stableUnderComposition _ _ (schemeNativeStalkGerm_faithfullyFlat f (m + 1) y)
    (RingHom.FaithfullyFlat.of_bijective (NativeHolGerm.chartEquiv (n := m + 1) y).bijective)

/-- **Algebraic prime divisors centred on a prime divisor of `X` are realized.**  Let `D` be an
algebraic prime divisor over the smooth projective integral complex scheme `X` whose valuation
`ord_D` has a centre of codimension one in `X` (equivalently, `ord_D` is the order of vanishing
along a prime divisor of `X`).  Then `D` is realized by an analytic presentation of a prime
divisor over `X(ℂ)`: the clause of `AlgebraicPrimesRealized` for `D`, with the identity
modification. -/
theorem exists_isRealizedBy_of_coheight_center_eq_one (E : ClosedProjectiveEmbedding f)
    (D : PrimeDivisorOver X) (hc : Order.coheight (D.ordVal f 1 one_pos).center = 1) :
    ∃ p : SGPT.PSH.CompactPrimeOver.PrimePresentation (m + 1) (SchemeComplexPoint f),
      D.IsRealizedBy m E p := by
  let := E.isSeparated
  let := E.quasiCompact
  have : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set z := (D.ordVal f 1 one_pos).center with hzdef
  have hcz : (D.ordVal f 1 one_pos).IsCenter z := (D.ordVal f 1 one_pos).isCenter_center
  have : IsDiscreteValuationRing (X.presheaf.stalk z) := isDiscreteValuationRing_stalk f (m + 1) hc
  obtain ⟨V, hV, hzV, u, s, hu, -, hsq, hirr, y, hy, hzy, hsy, v, hv⟩ :=
    exists_regular_point f (m + 1) hc
  obtain ⟨Ψ, hΨ⟩ := exists_divisorFlattening E hV hzV hu hsq hy hzy hsy hv
  have hTan : IsComplexAnalyticSubset (n := m + 1)
      (schemeNativeAlgebraicTrace f (closure {z})) :=
    schemeNativeAlgebraicTrace_isComplexAnalyticSubset f (m + 1) _ isClosed_closure
  have hreg := IdealPowerNormalOrder.regularAtDim_of_divisorFlattening Ψ
  refine exists_isRealizedBy_of_analyticSubset E D (ρ := id)
    HironakaChowLemma.isAnalyticModification_id hTan hreg Ψ fun g hg => ?_
  change (D.ord ((BerkovichPoint.specializationMap
    (ordVal_support_specializes f D (schemeComplexPointImage f y))).hom g) : ℤ) = _
  rw [PrimeDivisorOver'.ord_eq_emultiplicity D hcz hV hzV hu hsq hirr hy hzy hsy hg]
  congr 2
  change _ = normalOrder Ψ (chartTranslatedGerm y y (mem_chart_source _ y) (stalkRep m y g)
    (stalkRep_holomorphicAt y g))
  rw [chartTranslatedGerm_stalkRep, normalOrder, hΨ]
  exact (emultiplicity_map_of_faithfullyFlat _ (stalkToModel_faithfullyFlat y) _ _).symm

variable (m) in
/-- **`HypersurfaceRealizations` for the prime divisors over `X` centred in codimension at least
two**: the clause of `SGPT.NAPotential.AlgPrimes.HypersurfaceRealizations` for every algebraic
prime divisor `D` over `X` whose centre on `X` is not a prime divisor of `X`.  (A statement; not
proved here.) -/
def HypersurfaceRealizationsHighCodim : Prop :=
  ∀ D : PrimeDivisorOver X, Order.coheight (D.ordVal f 1 one_pos).center ≠ 1 →
    ∃ (W : BlowupTowers.CMfd.{0} (m + 1)) (ρ : W → SchemeComplexPoint f)
      (hρ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) ρ)
      (T : Set W) (_ : IsComplexAnalyticSubset (n := m + 1) T) (w₀ : W)
      (_ : RegularAtDim (n := m + 1) T w₀ m) (Ψ : DivisorFlattening (m := m) T w₀),
      ∀ g : X.presheaf.stalk (schemeComplexPointImage f (ρ w₀)), g ≠ 0 →
        (D.ord ((BerkovichPoint.specializationMap
          (ordVal_support_specializes f D (schemeComplexPointImage f (ρ w₀)))).hom g) : ℤ) =
          ((pullbackNormalOrder hρ Ψ (stalkRep m (ρ w₀) g)
            (stalkRep_holomorphicAt (ρ w₀) g)).toNat : ℤ)

/-- **`AlgebraicPrimesRealized` reduces to the prime divisors centred in codimension at least
two**: the prime divisors centred on a prime divisor of `X` are realized
(`exists_isRealizedBy_of_coheight_center_eq_one`), and for the others
`HypersurfaceRealizationsHighCodim` and `exists_isRealizedBy_of_analyticSubset` apply. -/
theorem algebraicPrimesRealized_of_hypersurfaceRealizationsHighCodim
    (E : ClosedProjectiveEmbedding f) (h : HypersurfaceRealizationsHighCodim (f := f) m) :
    AlgebraicPrimesRealized (f := f) m E := by
  intro D
  by_cases hc : Order.coheight (D.ordVal f 1 one_pos).center = 1
  · exact exists_isRealizedBy_of_coheight_center_eq_one E D hc
  · obtain ⟨W, ρ, hρ, T, hT, w₀, hreg, Ψ, hD⟩ := h D hc
    exact exists_isRealizedBy_of_analyticSubset E D hρ hT hreg Ψ hD

/-- `HypersurfaceRealizations` implies its restriction `HypersurfaceRealizationsHighCodim`. -/
theorem hypersurfaceRealizationsHighCodim_of_hypersurfaceRealizations
    (h : HypersurfaceRealizations (f := f) m) : HypersurfaceRealizationsHighCodim (f := f) m :=
  fun D _ => h D

end SGPT.NAPotential.AlgPrimes2

end
