import SGPT.NAPotential.AlgPrimes2Divisor
import SGPT.Foundations.Analysis.Pending.InvertibleIdealQuotient

/-!
# Actual analytic divisor coordinates without a properness hypothesis

Blueprint: `affine-divisor-flattening.tex`. The local holomorphic
representative of an original section is constructed by the existing smooth
affine germ API. No projective embedding or output flattening is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.AffineDivisorFlattening

open Set Filter
open scoped Topology Manifold ContDiff
open AlgebraicGeometry CategoryTheory IsLocalRing
open SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.NAPotential.FSPos SGPT.GAGA.H0S
open DemaillyApproximantDivisorialLelong FixedGermNormalOrder HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (m : ℕ)
  [SmoothOfRelativeDimension (m + 1) f] [IsSeparated f] [QuasiCompact f]

local instance pointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance pointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance pointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The derivative of an actual native germ is the derivative in the same preferred chart. -/
theorem germDeriv_chartEquiv_mk (y : SchemeComplexPoint f) (H : SchemeComplexPoint f → ℂ)
    (hH : HolomorphicAt (m + 1) H y) (v : ComplexModel (m + 1)) :
    germDeriv v (NativeHolGerm.chartEquiv y (NativeHolGerm.mk H hH)) =
      DerivativeIdeal.chartDeriv (complexChartAt (n := m + 1) y) v H y := by
  change _ = fderiv ℂ (fun z : ComplexModel (m + 1) =>
    H ((complexChartAt (n := m + 1) y).val.symm z))
      ((complexChartAt (n := m + 1) y).val y) v
  obtain ⟨g, hg, hgeq⟩ := HolGerm.exists_eq_mk
    (NativeHolGerm.chartEquiv y (NativeHolGerm.mk H hH))
  have hcoe := congrArg (fun q : HolGerm (ComplexModel (m + 1)) =>
    (q : Germ (𝓝 (0 : ComplexModel (m + 1))) ℂ)) hgeq
  simp only [NativeHolGerm.chartEquiv_mk, HolGerm.coe_mk] at hcoe
  have hev : (fun z : ComplexModel (m + 1) =>
      H ((complexChartAt (n := m + 1) y).val.symm
        (z + (complexChartAt (n := m + 1) y).val y))) =ᶠ[𝓝 0] g :=
    Germ.coe_eq.mp hcoe
  rw [hgeq, germDeriv_mk, ← hev.fderiv_eq,
    fderiv_comp_add_right (f := fun z : ComplexModel (m + 1) =>
      H ((complexChartAt (n := m + 1) y).val.symm z)), zero_add]

/-- An actual local divisor equation manufactures its flattening without projectivity. -/
theorem exists_divisorFlattening {z : X} {V : X.Opens}
    (hV : IsAffineOpen V) (hzV : z ∈ V) {u s : Γ(X, V)}
    (hu : u ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal)
    (hsq : ∀ a ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal, s * a ∈ Ideal.span {u})
    {y : SchemeComplexPoint f} (hy : schemeComplexPointImage f y ∈ V)
    (hzy : z ⤳ schemeComplexPointImage f y)
    (hsy : s ∉ (hV.primeIdealOf ⟨schemeComplexPointImage f y, hy⟩).asIdeal)
    {v : ComplexModel (m + 1)}
    (hv : germDeriv v (SGPT.NAPotential.FSPos.stalkToModel f (m + 1) y
      (X.presheaf.germ V (schemeComplexPointImage f y) hy u)) ≠ 0) :
    ∃ Ψ : DivisorFlattening (m := m) (schemeNativeAlgebraicTrace f (closure {z})) y,
      divisorEquationGerm Ψ = SGPT.NAPotential.FSPos.stalkToModel f (m + 1) y
        (X.presheaf.germ V (schemeComplexPointImage f y) hy u) := by
  obtain ⟨W, hW, hyW, hWV, H, hH, hread⟩ :=
    SmoothSchemeGerms.regularSection_locally_holomorphic f (m + 1) V u y hy
  have hHhol : ∀ q ∈ W, HolomorphicAt (m + 1) H q := fun q hq =>
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hW hH hq
  have hgerm : ∀ q (hq : q ∈ W),
      schemeNativeStalkGerm f (m + 1) q
        (X.presheaf.germ V (schemeComplexPointImage f q) (hWV hq) u) =
          NativeHolGerm.mk H (hHhol q hq) := by
    intro q hq
    apply Subtype.ext
    exact hread q hq (hWV hq)
  set T := schemeNativeAlgebraicTrace f (closure {z}) with hTdef
  set O : Set (SchemeComplexPoint f) := W ∩ schemeComplexPointImage f ⁻¹' X.basicOpen s with hOdef
  have hOopen : IsOpen O :=
    hW.inter ((X.basicOpen s).isOpen.preimage (schemeComplexPointImage_continuous f))
  have hyO : y ∈ O := ⟨hyW, (mem_basicOpen_iff_notMem_primeIdealOf hV s hy).mpr hsy⟩
  have hHholO : ∀ q ∈ O, HolomorphicAt (m + 1) H q := fun q hq => hHhol q hq.1
  have hT : ∀ q ∈ O, q ∈ T ↔ H q = 0 := by
    intro q hq
    have hqV : schemeComplexPointImage f q ∈ V := hWV hq.1
    have hsq' : s ∉ (hV.primeIdealOf ⟨_, hqV⟩).asIdeal :=
      (mem_basicOpen_iff_notMem_primeIdealOf hV s hqV).mp hq.2
    have heval : H q = SGPT.GAGA.H0S.pointEval f (m + 1) q
        (X.presheaf.germ V (schemeComplexPointImage f q) hqV u) := by
      change H q = NativeHolGerm.eval (schemeNativeStalkGerm f (m + 1) q _)
      rw [hgerm q hq.1, NativeHolGerm.eval_mk]
    have hH0 : H q = 0 ↔ u ∈ (hV.primeIdealOf ⟨_, hqV⟩).asIdeal := by
      rw [heval, SGPT.GAGA.H0S.pointEval_eq_zero_iff,
        ← Scheme.mem_basicOpen _ _ _ hqV, mem_basicOpen_iff_notMem_primeIdealOf hV u hqV,
        not_not]
    rw [hH0]
    change schemeComplexPointImage f q ∈ closure {z} ↔ _
    rw [← specializes_iff_mem_closure, AlgPrimes2.specializes_iff_primeIdealOf_le hV hqV hzV]
    constructor
    · intro h
      exact h hu
    · intro h a ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hsq a ha)
      have hsa : s * a ∈ (hV.primeIdealOf ⟨_, hqV⟩).asIdeal := by
        rw [← hc]
        exact Ideal.mul_mem_left _ _ h
      exact ((hV.primeIdealOf ⟨_, hqV⟩).isPrime.mem_or_mem hsa).resolve_left hsq'
  have hyT : y ∈ T := specializes_iff_mem_closure.mp hzy
  have hHy : H y = 0 := (hT y hyO).mp hyT
  have hd : DerivativeIdeal.chartDeriv (complexChartAt (n := m + 1) y) v H y ≠ 0 := by
    have hgy := hgerm y hyW
    change germDeriv v (NativeHolGerm.chartEquiv y (schemeNativeStalkGerm f (m + 1) y _)) ≠ 0 at hv
    rw [hgy, germDeriv_chartEquiv_mk] at hv
    exact hv
  obtain ⟨hn, Ω, hΩs, hΩinj, hΩu⟩ := LocalGiraudTransform.exists_hypersurface_coords
    (hHholO y hyO) (mem_complexChartAt_source y) hd
  have hO' : IsOpen (O ∩ (chartAt (ComplexModel (m + 1)) y).source) :=
    hOopen.inter (chartAt (ComplexModel (m + 1)) y).open_source
  obtain ⟨Θ, hΘt, hΘ0, hΘ⟩ := BlowupSNCTransform.exists_recentred_coords hO'
    (fun q hq => hΩs q hq.2 (hHholO q hq.1)) ⟨hyO, mem_chart_source _ y⟩ hΩinj
  have hlast : (⟨m + 1 - 1, Nat.sub_lt hn one_pos⟩ : Fin (m + 1)) = Fin.last m := by
    ext
    simp
  have hΘlast : ∀ {q : SchemeComplexPoint f},
      q ∈ (complexChartAt (n := m + 1) y).val.source →
      (complexChartAt (n := m + 1) y).val q ∈ Θ.source →
      q ∈ O ∧ Θ.toFun ((complexChartAt (n := m + 1) y).val q) (Fin.last m) = H q := by
    intro q hq hqΘ
    obtain ⟨hqO, hΘq⟩ := hΘ hq hqΘ
    refine ⟨hqO.1, ?_⟩
    rw [hΘq, PiLp.sub_apply, ← hlast, hΩu, hΩu, hHy, sub_zero]
  let Ψ : DivisorFlattening (m := m) T y :=
    { Φ := Θ
      source_subset := hΘt
      map_center := hΘ0
      mem_iff := fun q hq hqΘ => by
        obtain ⟨hqO, hqval⟩ := hΘlast hq hqΘ
        rw [hqval]
        exact hT q hqO }
  refine ⟨Ψ, ?_⟩
  change _ = NativeHolGerm.chartEquiv y (schemeNativeStalkGerm f (m + 1) y _)
  rw [hgerm y hyW]
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
  have hys : (complexChartAt (n := m + 1) y).val.symm
      (w + (complexChartAt (n := m + 1) y).val y) ∈ (complexChartAt (n := m + 1) y).val.source :=
    (complexChartAt (n := m + 1) y).val.map_target hwt
  have hcc : (complexChartAt (n := m + 1) y).val ((complexChartAt (n := m + 1) y).val.symm
      (w + (complexChartAt (n := m + 1) y).val y)) = w + (complexChartAt (n := m + 1) y).val y :=
    (complexChartAt (n := m + 1) y).val.right_inv hwt
  have hmem : (complexChartAt (n := m + 1) y).val ((complexChartAt (n := m + 1) y).val.symm
      (w + (complexChartAt (n := m + 1) y).val y)) ∈ Θ.source := by
    rw [hcc]
    exact hwΘ
  have h := (hΘlast hys hmem).2
  rw [hcc] at h
  exact h

/-- The actual algebraic stalk-to-preferred-chart map is faithfully flat on a smooth model. -/
theorem stalkToModel_faithfullyFlat (y : SchemeComplexPoint f) :
    (stalkToModel f (m + 1) y).FaithfullyFlat :=
  RingHom.FaithfullyFlat.stableUnderComposition _ _
    (schemeNativeStalkGerm_faithfullyFlat f (m + 1) y)
    (RingHom.FaithfullyFlat.of_bijective (NativeHolGerm.chartEquiv (n := m + 1) y).bijective)

/-- Every actual codimension-one point has analytic divisor coordinates, with all original
algebraic-germ multiplicities preserved. No properness, projectivity, flattening, or order
comparison is an input. -/
theorem exists_divisorFlattening_of_coheight_one [IsIntegral X] {z : X}
    (hz : Order.coheight z = 1) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (hzV : z ∈ V) (u s : Γ(X, V)),
      u ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal ∧
      s ∉ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal ∧
      (∀ a ∈ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal, s * a ∈ Ideal.span {u}) ∧
      Irreducible (X.presheaf.germ V z hzV u) ∧
      ∃ (y : SchemeComplexPoint f) (hy : schemeComplexPointImage f y ∈ V),
        z ⤳ schemeComplexPointImage f y ∧
        s ∉ (hV.primeIdealOf ⟨schemeComplexPointImage f y, hy⟩).asIdeal ∧
        ∃ Ψ : DivisorFlattening (m := m) (schemeNativeAlgebraicTrace f (closure {z})) y,
          divisorEquationGerm Ψ = stalkToModel f (m + 1) y
            (X.presheaf.germ V (schemeComplexPointImage f y) hy u) ∧
          ∀ g : X.presheaf.stalk (schemeComplexPointImage f y),
            normalOrder Ψ (stalkToModel f (m + 1) y g) =
              emultiplicity (X.presheaf.germ V (schemeComplexPointImage f y) hy u) g := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hV, hzV, u, s, hu, hs, hsq, hirr, y, hy, hzy, hsy, v, hv⟩ :=
    AlgPrimes2.exists_regular_point f (m + 1) hz
  obtain ⟨Ψ, hΨ⟩ := exists_divisorFlattening f m hV hzV hu hsq hy hzy hsy hv
  refine ⟨V, hV, hzV, u, s, hu, hs, hsq, hirr, y, hy, hzy, hsy, Ψ, hΨ, ?_⟩
  intro g
  unfold normalOrder
  rw [hΨ]
  exact AlgPrimes2.emultiplicity_map_of_faithfullyFlat _ (stalkToModel_faithfullyFlat f m y) _ _

/-- The same original algebraic divisorial order is the produced analytic normal order.
The centre is specified explicitly, so a proper base is unnecessary. -/
theorem exists_order_comparison_at_center [IsIntegral X]
    (D : SGPT.NAPotential.Berkovich.PrimeDivisorOver X) {z : X}
    (hc : (D.ordVal f 1 one_pos).IsCenter z) (hz : Order.coheight z = 1) :
    ∃ y : SchemeComplexPoint f, z ⤳ schemeComplexPointImage f y ∧
      ∃ Ψ : DivisorFlattening (m := m) (schemeNativeAlgebraicTrace f (closure {z})) y,
        ∀ g : X.presheaf.stalk (schemeComplexPointImage f y), g ≠ 0 →
          (D.ord ((Berkovich.BerkovichPoint.specializationMap
            (SGPT.NAPotential.AlgPrimes.ordVal_support_specializes f D
              (schemeComplexPointImage f y))).hom g) : ℤ) =
            ((normalOrder Ψ (stalkToModel f (m + 1) y g)).toNat : ℤ) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsDiscreteValuationRing (X.presheaf.stalk z) :=
    AlgPrimes2.isDiscreteValuationRing_stalk f (m + 1) hz
  obtain ⟨V, hV, hzV, u, s, hu, _, hsq, hirr, y, hy, hzy, hsy, Ψ, _, hord⟩ :=
    exists_divisorFlattening_of_coheight_one f m hz
  refine ⟨y, hzy, Ψ, ?_⟩
  intro g hg
  rw [hord g]
  exact AlgPrimes2.PrimeDivisorOver'.ord_eq_emultiplicity D hc hV hzV hu hsq hirr hy hzy hsy hg

end SGPT.NAPotential.AffineDivisorFlattening
