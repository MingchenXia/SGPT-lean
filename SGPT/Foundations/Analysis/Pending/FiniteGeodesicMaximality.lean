import SGPT.Foundations.Analysis.Pending.OpensRestriction
import SGPT.Foundations.Analysis.Pending.ScaledPolydiskBalayageMass
import SGPT.Foundations.Analysis.Pending.PolydiskPatchVanishing
import SGPT.Foundations.Analysis.Pending.BedfordTaylorCapacity
import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesics
import SGPT.Foundations.Analysis.FirstPass.PshSupremumRegularization
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationLocality
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Perron geodesic with bounded slices is maximal on the strip

Source: Xia, SGPT, proof of Proposition 4.3.3, Step 2 (`xia-sgpt:page-0172`).

Let `θ` be a smooth real `2`-form on a complex manifold `M` of dimension `n`, and let `U` be the
Perron finite geodesic between `u₀` and `u₁` (`FirstPass.finiteGeodesic`). Assume that `U` is a
subgeodesic from `u₀` to `u₁` and that its slices `U t`, `0 < t < 1`, are uniformly bounded.
In a chart `e` with a smooth local potential `ρ` of `θ` on `W`, the corrected complexification
`h (z, τ) = U (Re τ) (e⁻¹ z) + ρ z` is plurisubharmonic on `W × {0 < Re τ < 1}`. We prove that `h`
coincides with its balayage on every polydisk whose closure lies in `W × {0 < Re τ < 1}`
(`eqOn_scaledPolydiskBalayage_finiteGeodesic`), so that every Bedford--Taylor limit of
`(h, …, h)` (`n + 1` copies) on such a polydisk is zero
(`isBTLimit_eq_zero_finiteGeodesic`), hence every Bedford--Taylor limit of `(h, …, h)` on all of
`W × {0 < Re τ < 1}` is zero (`isBTLimit_modelStripOpens_eq_zero_finiteGeodesic`): the
complexified geodesic solves the homogeneous complex Monge--Ampère equation `(ddᶜ h)^{n+1} = 0`.

The two hypotheses on `U` hold when the endpoints have relative minimal singularities with respect
to a model potential (`Pending.FiniteGeodesicsFullMassGeneral.
finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity`), and the slices are then bounded as soon
as the model potential is.

## The argument (Xia's, with the polydisk balayage)

The balayage `h̃` of `h` on a polydisk `P` (`BedfordTaylor.scaledPolydiskBalayage`, Xia's
Proposition 1.2.9) is plurisubharmonic, equals `h` off `P` and is `≥ h` on `P`. Glue `h̃ - ρ` into
the complexification of `U` over `P`; the result `Ũ` depends on `Im τ`. Its symmetrization
`G (x, τ) = sup_s Ũ (x, τ + i s)`, regularized, depends only on `Re τ` and so defines a curve `V`.
The curve `V` is a subgeodesic from `u₀` to `u₁`: in every chart its corrected complexification is
the regularized supremum of a locally uniformly bounded family of plurisubharmonic functions
(transported between charts along the holomorphic transitions, `stripWitness_of_chart`),
and it coincides with `U` near `t = 0` and `t = 1`. Perron maximality gives `V ≤ U`, hence
`h̃ ≤ h` on `P`.

The strip `ℂⁿ × ℂ` is identified with `ℂⁿ⁺¹` by `stripModelEquiv`, the model on which the
polydisk balayage and Bedford--Taylor limits are stated.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

open FirstPass FirstPass.HolomorphicMaps FirstPass.MongeAmpere BedfordTaylor

noncomputable section

/-! ### The model `ℂⁿ⁺¹ ≃ ℂⁿ × ℂ` -/

section Model

variable {n : ℕ}

/-- The identification `ℂⁿ⁺¹ ≃ ℂⁿ × ℂ`: the first `n` coordinates and the last one. -/
def stripModelEquiv (n : ℕ) : ComplexModel (n + 1) ≃L[ℂ] ComplexModel n × ℂ :=
  (ProductComplexManifold.prodModelEquiv n 1).symm.trans
    ((ContinuousLinearEquiv.refl ℂ (ComplexModel n)).prodCongr
      (PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => ℂ)))

/-- Plurisubharmonicity on `ℂⁿ × ℂ` pulls back along the model identification. -/
theorem plurisubharmonicOn_comp_stripModelEquiv {Ψ : ComplexModel n × ℂ → EReal}
    {V : Set (ComplexModel n × ℂ)} (hΨ : PlurisubharmonicOn Ψ V) :
    PlurisubharmonicOn (fun q => Ψ (stripModelEquiv n q)) (stripModelEquiv n ⁻¹' V) :=
  hΨ.comp_continuousLinearMap (stripModelEquiv n : ComplexModel (n + 1) →L[ℂ] ComplexModel n × ℂ)

/-- Plurisubharmonicity on `ℂⁿ⁺¹` pushes forward along the model identification. -/
theorem plurisubharmonicOn_comp_stripModelEquiv_symm {Ψ : ComplexModel (n + 1) → EReal}
    {V : Set (ComplexModel (n + 1))} (hΨ : PlurisubharmonicOn Ψ V) :
    PlurisubharmonicOn (fun p => Ψ ((stripModelEquiv n).symm p)) ((stripModelEquiv n).symm ⁻¹' V) :=
  hΨ.comp_continuousLinearMap
    ((stripModelEquiv n).symm : ComplexModel n × ℂ →L[ℂ] ComplexModel (n + 1))

/-- **Holomorphic pullback on `ℂⁿ × ℂ`.** A plurisubharmonic function composed with a map that is
holomorphic on an open set is plurisubharmonic there. -/
theorem plurisubharmonicOn_comp_holomorphic_strip {F : ComplexModel n × ℂ → ComplexModel n × ℂ}
    {Ψ : ComplexModel n × ℂ → EReal} {U V : Set (ComplexModel n × ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hFV : MapsTo F U V) (hΨ : PlurisubharmonicOn Ψ V) :
    PlurisubharmonicOn (fun p => Ψ (F p)) U := by
  set L := stripModelEquiv n
  have h1 := plurisubharmonicOn_comp_stripModelEquiv hΨ
  let G : ComplexModel (n + 1) → ComplexModel (n + 1) := fun q => L.symm (F (L q))
  have hUL : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hG : DifferentiableOn ℂ G (L ⁻¹' U) :=
    L.symm.differentiable.comp_differentiableOn
      (hF.comp L.differentiable.differentiableOn fun q hq => hq)
  have hGV : MapsTo G (L ⁻¹' U) (L ⁻¹' V) := by
    intro q hq
    simp only [mem_preimage, G, ContinuousLinearEquiv.apply_symm_apply]
    exact hFV hq
  have h2 := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hUL hG hGV h1
  have h3 := plurisubharmonicOn_comp_stripModelEquiv_symm h2
  have e : (fun p => Ψ (F p)) = fun p => Ψ (L (G (L.symm p))) := by
    funext p
    simp [G]
  rw [e]
  refine h3.mono fun p hp => ?_
  show (stripModelEquiv n) ((stripModelEquiv n).symm p) ∈ U
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact hp

end Model

/-! ### Corrected complexifications in charts -/

section Strip

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The corrected complexification, in the chart `e` with the local potential `ρ`, of a function
`F` of `(x, τ) ∈ M × ℂ`: `(z, τ) ↦ F (e⁻¹ z) τ + ρ z`. For `F x τ = curve (Re τ) x` this is
`subgeodesicChartFunction curve e ρ`. -/
def stripChartFunction (F : M → ℂ → EReal) (e : ComplexChart n M) (ρ : ComplexModel n → ℝ) :
    ComplexModel n × ℂ → EReal :=
  fun p => F (e.val.symm p.1) p.2 + (ρ p.1 : EReal)

theorem subgeodesicChartFunction_eq_stripChartFunction (curve : ℝ → M → EReal)
    (e : ComplexChart n M) (ρ : ComplexModel n → ℝ) :
    subgeodesicChartFunction curve e ρ = stripChartFunction (fun x τ => curve τ.re x) e ρ :=
  rfl

/-- **A strip witness transports between charts.** If, in the chart `d`, `ρ'` is a smooth local
potential of `θ` on `W'` and the corrected complexification of `F` is plurisubharmonic on
`W' × strip`, then in the chart `e` the pulled-back potential `ρ' ∘ (d ∘ e⁻¹)` on the pulled-back
domain is a smooth local potential of `θ`, and the corrected complexification of `F` is
plurisubharmonic on that domain times the strip. The domain and the potential do not depend on
`F`. -/
theorem stripWitness_of_chart {θ : SmoothRealForm n M 2} {F : M → ℂ → EReal}
    (e d : ComplexChart n M) {W' : Set (ComplexModel n)} {ρ' : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ d W' ρ')
    (hp : PlurisubharmonicOn (stripChartFunction F d ρ') (geodesicChartDomain W')) :
    IsSmoothLocalPotential θ e (LocalPotentialPullback.potentialDomain id e d W')
        (ρ' ∘ coordinateMap id e d) ∧
      PlurisubharmonicOn (stripChartFunction F e (ρ' ∘ coordinateMap id e d))
        (geodesicChartDomain (LocalPotentialPullback.potentialDomain id e d W')) := by
  have hid : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : M → M) :=
    contMDiff_id
  set D := LocalPotentialPullback.potentialDomain id e d W' with hDdef
  have hD : IsOpen D := LocalPotentialPullback.potentialDomain_isOpen hid e d hρ.1
  refine ⟨((SmoothRealForm.pullback_id_geometricallyEq θ).localPotential_iff e _ _).mp
    (LocalPotentialPullback.isSmoothLocalPotential_pullback hid e hρ), ?_⟩
  let Φ : ComplexModel n × ℂ → ComplexModel n × ℂ := fun p => (coordinateMap id e d p.1, p.2)
  have hDopen : IsOpen (geodesicChartDomain D) := isOpen_geodesicChartDomain hD
  have hcd : DifferentiableOn ℂ (coordinateMap id e d) D :=
    ((coordinateMap_contDiffOn hid e d).mono inter_subset_left).differentiableOn (by simp)
  have hΦ : DifferentiableOn ℂ Φ (geodesicChartDomain D) :=
    (hcd.comp differentiableOn_fst fun p hp => hp.1).prodMk differentiableOn_snd
  have hmaps : MapsTo Φ (geodesicChartDomain D) (geodesicChartDomain W') := by
    intro p hp
    exact ⟨hp.1.2, hp.2⟩
  have hpull := plurisubharmonicOn_comp_holomorphic_strip hDopen hΦ hmaps hp
  intro p hp
  apply (hpull p hp).congr
  filter_upwards [hDopen.mem_nhds hp] with q hq
  change F (d.val.symm (d.val (id (e.val.symm q.1)))) q.2 +
      (ρ' (coordinateMap id e d q.1) : EReal) =
    F (e.val.symm q.1) q.2 + (ρ' (coordinateMap id e d q.1) : EReal)
  rw [d.val.left_inv hq.1.1.2]
  rfl

/-- At a point of a chart target, regularizing a function of `(x, τ)` after reading it in the chart
is the same as reading the regularized function in the chart. -/
theorem uscRegularization_stripChart_apply (G : M × ℂ → EReal) (e : ComplexChart n M)
    {y : ComplexModel n} (hy : y ∈ e.val.target) (τ : ℂ) :
    uscRegularization (fun q : ComplexModel n × ℂ => G (e.val.symm q.1, q.2)) (y, τ) =
      uscRegularization G (e.val.symm y, τ) := by
  let ψ : OpenPartialHomeomorph (ComplexModel n × ℂ) (M × ℂ) :=
    e.val.symm.prod (OpenPartialHomeomorph.refl ℂ)
  have hsrc : (y, τ) ∈ ψ.source := by
    simp only [ψ, OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.refl_source, mem_prod, mem_univ, and_true]
    exact hy
  have h := uscRegularization_comp_openPartialHomeomorph_apply G ψ hsrc
  simpa [ψ, Function.comp_def] using h

/-- **The complexification of a subgeodesic is upper semicontinuous at interior times**, in the
form: its regularization at `(x, t)`, `0 < t < 1`, is its value. -/
theorem uscRegularization_complexified_eq {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal}
    (h : IsSubgeodesicInterior θ curve) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    uscRegularization (fun p : M × ℂ => curve p.2.re p.1) (x, (t : ℂ)) = curve t x := by
  refine le_antisymm ?_ (by simpa using le_uscRegularization (fun p : M × ℂ => curve p.2.re p.1) (x, (t : ℂ)))
  set e : ComplexChart n M := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := h.complexified_psh e hz
  have hmem : (e.val x, (t : ℂ)) ∈ geodesicChartDomain W := by
    refine ⟨hzW, ?_⟩
    simpa using ht
  have husc : UpperSemicontinuousAt (subgeodesicChartFunction curve e ρ) (e.val x, (t : ℂ)) :=
    (hpsh _ hmem).upperSemicontinuousAt
  -- read everything in the chart
  have h1 := uscRegularization_stripChart_apply (fun p : M × ℂ => curve p.2.re p.1) e hz (t : ℂ)
  rw [e.val.left_inv hx] at h1
  rw [← h1]
  have hρ0 : ContinuousAt ρ (e.val x) := hρ.2.2.1.continuousOn.continuousAt (hρ.1.mem_nhds hzW)
  have hfst : ContinuousAt (fun q : ComplexModel n × ℂ => q.1) (e.val x, (t : ℂ)) :=
    continuous_fst.continuousAt
  have hρc : ContinuousAt (fun q : ComplexModel n × ℂ => -ρ q.1) (e.val x, (t : ℂ)) :=
    (ContinuousAt.comp (g := ρ) (f := fun q : ComplexModel n × ℂ => q.1) hρ0 hfst).neg
  have heq : (fun q : ComplexModel n × ℂ => curve q.2.re (e.val.symm q.1)) =
      fun q => subgeodesicChartFunction curve e ρ q + ((-ρ q.1 : ℝ) : EReal) := by
    funext q
    simp only [subgeodesicChartFunction, chartFunction]
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  rw [heq, uscRegularization_add_coe_continuousAt_apply _ hρc]
  have hreg : uscRegularization (subgeodesicChartFunction curve e ρ) (e.val x, (t : ℂ)) ≤
      subgeodesicChartFunction curve e ρ (e.val x, (t : ℂ)) :=
    uscRegularization_le_of_eventually_le husc (Eventually.of_forall fun _ => le_rfl)
  calc uscRegularization (subgeodesicChartFunction curve e ρ) (e.val x, (t : ℂ)) +
        ((-ρ (e.val x) : ℝ) : EReal)
      ≤ subgeodesicChartFunction curve e ρ (e.val x, (t : ℂ)) + ((-ρ (e.val x) : ℝ) : EReal) :=
        add_le_add hreg le_rfl
    _ = curve t x := by
        simp only [subgeodesicChartFunction_apply, chartFunction, Complex.ofReal_re,
          e.val.left_inv hx]
        rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

end Strip

/-! ### Imaginary-time symmetrization -/

section Symmetrization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The supremum over imaginary translations: `G (x, τ) = sup_s F x (τ + i s)`. -/
def stripSupremum (F : M → ℂ → EReal) : M × ℂ → EReal :=
  fun p => ⨆ s : ℝ, F p.1 (p.2 + (s : ℂ) * Complex.I)

/-- The curve of the regularized symmetrization, read at real times. -/
def symmetrizedCurve (F : M → ℂ → EReal) : ℝ → M → EReal :=
  fun t x => uscRegularization (stripSupremum F) (x, (t : ℂ))

theorem stripSupremum_add_mul_I (F : M → ℂ → EReal) (x : M) (τ : ℂ) (s : ℝ) :
    stripSupremum F (x, τ + (s : ℂ) * Complex.I) = stripSupremum F (x, τ) := by
  simp only [stripSupremum]
  refine (Equiv.addLeft s).iSup_congr fun s' => ?_
  simp only [Equiv.coe_addLeft]
  congr 1
  push_cast
  ring

/-- The regularized symmetrization only depends on the real part of the time. -/
theorem uscRegularization_stripSupremum_re (F : M → ℂ → EReal) (x : M) (τ : ℂ) :
    uscRegularization (stripSupremum F) (x, τ) =
      uscRegularization (stripSupremum F) (x, (τ.re : ℂ)) := by
  let T : M × ℂ ≃ₜ M × ℂ :=
    (Homeomorph.refl M).prodCongr (Homeomorph.addRight (((-τ.im : ℝ) : ℂ) * Complex.I))
  have hGT : stripSupremum F ∘ T = stripSupremum F := by
    funext p
    exact stripSupremum_add_mul_I F p.1 p.2 (-τ.im)
  have h := uscRegularization_comp_homeomorph_apply (stripSupremum F) T (x, τ)
  rw [hGT] at h
  rw [h]
  congr 1
  refine Prod.ext rfl ?_
  show τ + ((-τ.im : ℝ) : ℂ) * Complex.I = (τ.re : ℂ)
  apply Complex.ext <;> simp

theorem le_stripSupremum (F : M → ℂ → EReal) (x : M) (τ : ℂ) :
    F x τ ≤ stripSupremum F (x, τ) := by
  show F x τ ≤ ⨆ s : ℝ, F x (τ + (s : ℂ) * Complex.I)
  exact le_iSup_of_le 0 (by simp)

theorem le_symmetrizedCurve (F : M → ℂ → EReal) (x : M) (τ : ℂ) :
    F x τ ≤ symmetrizedCurve F τ.re x := by
  have h := (le_stripSupremum F x τ).trans (le_uscRegularization (stripSupremum F) (x, τ))
  rwa [uscRegularization_stripSupremum_re] at h

/-- On a witness domain, the corrected complexification of the symmetrized curve is the regularized
supremum of the corrected complexifications of the imaginary translates. -/
theorem subgeodesicChartFunction_symmetrizedCurve_eq (F : M → ℂ → EReal)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hW : IsOpen W) (hWt : W ⊆ e.val.target) (hρ : ContinuousOn ρ W)
    {p : ComplexModel n × ℂ} (hp : p.1 ∈ W) :
    subgeodesicChartFunction (symmetrizedCurve F) e ρ p =
      uscRegularization (sSup (range fun s : ℝ =>
        stripChartFunction (fun x τ => F x (τ + (s : ℂ) * Complex.I)) e ρ)) p := by
  have hsSup : sSup (range fun s : ℝ =>
      stripChartFunction (fun x τ => F x (τ + (s : ℂ) * Complex.I)) e ρ) =
      fun q => stripSupremum F (e.val.symm q.1, q.2) + (ρ q.1 : EReal) := by
    funext q
    rw [sSup_range, iSup_apply]
    simp only [stripChartFunction, stripSupremum]
    exact iSup_add_coe _ _
  rw [hsSup]
  have hρc : ContinuousAt (fun q : ComplexModel n × ℂ => ρ q.1) p :=
    ContinuousAt.comp (g := ρ) (f := fun q : ComplexModel n × ℂ => q.1)
      (hρ.continuousAt (hW.mem_nhds hp)) continuous_fst.continuousAt
  rw [uscRegularization_add_coe_continuousAt_apply _ hρc]
  obtain ⟨y, τ⟩ := p
  rw [uscRegularization_stripChart_apply (stripSupremum F) e (hWt hp) τ,
    uscRegularization_stripSupremum_re]
  rfl

/-- **The symmetrized modification of a subgeodesic is a subgeodesic.** Let `curve` be a
subgeodesic from `u₀` to `u₁`, and `F` a function of `(x, τ)` lying above its complexification,
equal to it when `Re τ ∉ [a, b] ⊂ (0, 1)`, bounded above over the strip, and whose imaginary translates have, in
every chart, plurisubharmonic corrected complexifications with one common witness. Then the curve
`t ↦ (sup_s F (·, · + i s))^*(·, t)` is a subgeodesic from `u₀` to `u₁`. -/
theorem isSubgeodesicFrom_symmetrizedCurve
    {θ : SmoothRealForm n M 2} {curve : ℝ → M → EReal} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ curve u₀ u₁) {F : M → ℂ → EReal}
    (hle : ∀ x τ, curve τ.re x ≤ F x τ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hout : ∀ x τ, (τ.re < a ∨ b < τ.re) → F x τ = curve τ.re x)
    (hwit : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ),
        z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
        ∀ s : ℝ, PlurisubharmonicOn
          (stripChartFunction (fun x τ => F x (τ + (s : ℂ) * Complex.I)) e ρ)
          (geodesicChartDomain W))
    {C : ℝ} (hC : ∀ x τ, τ.re ∈ Ioo (0 : ℝ) 1 → F x τ ≤ (C : EReal)) :
    IsSubgeodesicFrom θ (symmetrizedCurve F) u₀ u₁ := by
  -- plurisubharmonicity in every chart
  have hchart : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∃ (W : Set (ComplexModel n)) (ρ : ComplexModel n → ℝ),
        z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
        PlurisubharmonicOn (subgeodesicChartFunction (symmetrizedCurve F) e ρ)
          (geodesicChartDomain W) := by
    intro e z hz
    obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hwit e z hz
    refine ⟨W, ρ, hzW, hρ, ?_⟩
    have hΩ : IsOpen (geodesicChartDomain W) := isOpen_geodesicChartDomain hρ.1
    have hbound : LocallyUniformlyBoundedAbove (range fun s : ℝ =>
        stripChartFunction (fun x τ => F x (τ + (s : ℂ) * Complex.I)) e ρ)
        (geodesicChartDomain W) := by
      intro p hp
      have hρ0 : ContinuousAt ρ p.1 :=
        hρ.2.2.1.continuousOn.continuousAt (hρ.1.mem_nhds hp.1)
      have hρc : ContinuousAt (fun q : ComplexModel n × ℂ => ρ q.1) p :=
        ContinuousAt.comp (g := ρ) (f := fun q : ComplexModel n × ℂ => q.1) hρ0
          continuous_fst.continuousAt
      have hnhds : {q : ComplexModel n × ℂ | ρ q.1 < ρ p.1 + 1} ∈ 𝓝 p :=
        hρc.preimage_mem_nhds (Iio_mem_nhds (by linarith))
      refine ⟨_, mem_nhdsWithin_of_mem_nhds hnhds, C + (ρ p.1 + 1), ?_⟩
      rintro f ⟨s, rfl⟩ q ⟨hq1, hq2⟩
      simp only [stripChartFunction]
      have hre : (q.2 + (s : ℂ) * Complex.I).re ∈ Ioo (0 : ℝ) 1 := by
        simpa using hq2.2
      calc F (e.val.symm q.1) (q.2 + (s : ℂ) * Complex.I) + (ρ q.1 : EReal)
          ≤ (C : EReal) + (ρ q.1 : EReal) := add_le_add (hC _ _ hre) le_rfl
        _ ≤ ((C + (ρ p.1 + 1) : ℝ) : EReal) := by
            rw [← EReal.coe_add, EReal.coe_le_coe_iff]
            have : ρ q.1 < ρ p.1 + 1 := hq1
            linarith
    have hfam := plurisubharmonicOn_uscRegularization_sSup hΩ (range_nonempty _)
      (by rintro f ⟨s, rfl⟩; exact hpsh s) hbound
    intro p hp
    refine (hfam p hp).congr ?_
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact (subgeodesicChartFunction_symmetrizedCurve_eq F e hρ.1 hρ.2.1
      hρ.2.2.1.continuousOn hq.1).symm
  -- the slices
  have hslice : ∀ t ∈ Ioo (0 : ℝ) 1, IsThetaPshPotential θ (symmetrizedCurve F t) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · intro e z hz
      obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hchart e z hz
      refine ⟨W, ρ, hzW, hρ, ?_⟩
      have h := hpsh.comp_affine (ContinuousLinearMap.inl ℂ (ComplexModel n) ℂ)
        ((0 : ComplexModel n), (t : ℂ))
      have hfun : (fun y => subgeodesicChartFunction (symmetrizedCurve F) e ρ
          (((0 : ComplexModel n), (t : ℂ)) + ContinuousLinearMap.inl ℂ (ComplexModel n) ℂ y)) =
          fun y => chartFunction (symmetrizedCurve F t) e y + (ρ y : EReal) := by
        funext y
        simp [subgeodesicChartFunction]
      rw [hfun] at h
      refine h.mono fun y hy => ?_
      simp only [mem_preimage, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero]
      exact ⟨hy, by simpa using ht⟩
    · refine (hsub.2.2.1.1 t ht).2.mono fun x => ?_
      have h1 := hle x (t : ℂ)
      have h2 := le_symmetrizedCurve F x (t : ℂ)
      simp only [Complex.ofReal_re] at h1 h2
      exact h1.trans h2
  -- agreement with the curve near the ends
  have hnear : ∀ t ∈ Ioo (0 : ℝ) 1, (t < a ∨ b < t) → symmetrizedCurve F t = curve t := by
    intro t ht htab
    funext x
    have hopen : IsOpen {p : M × ℂ | p.2.re < a ∨ b < p.2.re} :=
      (isOpen_lt (Complex.continuous_re.comp continuous_snd) continuous_const).union
        (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd))
    have hev : stripSupremum F =ᶠ[𝓝 (x, (t : ℂ))] fun p : M × ℂ => curve p.2.re p.1 := by
      filter_upwards [hopen.mem_nhds (by simpa using htab)] with p hp
      have hs : ∀ s : ℝ, F p.1 (p.2 + (s : ℂ) * Complex.I) = curve p.2.re p.1 := by
        intro s
        have hre : (p.2 + (s : ℂ) * Complex.I).re = p.2.re := by simp
        rw [hout _ _ (by rw [hre]; exact hp), hre]
      simp only [stripSupremum, hs, ciSup_const]
    show uscRegularization (stripSupremum F) (x, (t : ℂ)) = curve t x
    rw [uscRegularization_congr_of_eventuallyEq hev,
      uscRegularization_complexified_eq hsub.2.2.1 ht x]
  have hend0 : ManifoldL1LocallyTendsto (n := n) (symmetrizedCurve F) (𝓝[>] (0 : ℝ)) u₀ := by
    refine hsub.2.2.2.1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT ha] with t ht
    exact (hnear t ⟨ht.1, ht.2.trans_le (hab.trans hb.le)⟩ (Or.inl ht.2)).symm
  have hend1 : ManifoldL1LocallyTendsto (n := n) (symmetrizedCurve F) (𝓝[<] (1 : ℝ)) u₁ := by
    refine hsub.2.2.2.2.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hb] with t ht
    exact (hnear t ⟨(ha.trans_le hab).trans ht.1, ht.2⟩ (Or.inr ht.1)).symm
  exact ⟨hsub.1, hsub.2.1, ⟨hslice, hchart⟩, hend0, hend1⟩

end Symmetrization

/-! ### The balayage of the complexified geodesic -/

section Balayage

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The real corrected complexification of a curve in the chart `e`, read on `ℂⁿ⁺¹`. -/
def modelChartFunction (curve : ℝ → M → EReal) (e : ComplexChart n M)
    (ρ : ComplexModel n → ℝ) : ComplexModel (n + 1) → ℝ :=
  fun q => (subgeodesicChartFunction curve e ρ (stripModelEquiv n q)).toReal

/-- The open subset of `ℂⁿ⁺¹` corresponding to `W × {0 < Re τ < 1}`. -/
def modelStripOpens (W : Set (ComplexModel n)) (hW : IsOpen W) : Opens (ComplexModel (n + 1)) :=
  ⟨stripModelEquiv n ⁻¹' geodesicChartDomain W,
    (isOpen_geodesicChartDomain hW).preimage (stripModelEquiv n).continuous⟩

theorem mem_modelStripOpens {W : Set (ComplexModel n)} {hW : IsOpen W}
    {q : ComplexModel (n + 1)} :
    q ∈ modelStripOpens W hW ↔ stripModelEquiv n q ∈ geodesicChartDomain W :=
  Iff.rfl

/-- Uniformly bounded slices are finite. -/
theorem exists_eq_coe_of_bounded {curve : ℝ → M → EReal} {A B : ℝ}
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ curve t x ∧ curve t x ≤ (B : EReal))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : M) :
    ∃ c : ℝ, curve t x = (c : EReal) ∧ A ≤ c ∧ c ≤ B := by
  obtain ⟨h1, h2⟩ := hbd t ht x
  have hbot : curve t x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot A) h1
  have htop : curve t x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top B) h2
  refine ⟨(curve t x).toReal, (EReal.coe_toReal htop hbot).symm, ?_, ?_⟩
  · rw [← EReal.coe_le_coe_iff, EReal.coe_toReal htop hbot]; exact h1
  · rw [← EReal.coe_le_coe_iff, EReal.coe_toReal htop hbot]; exact h2

/-- On the strip, the real corrected complexification is the extended-real one. -/
theorem coe_modelChartFunction {curve : ℝ → M → EReal} {A B : ℝ}
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ curve t x ∧ curve t x ≤ (B : EReal))
    (e : ComplexChart n M) (ρ : ComplexModel n → ℝ) {W : Set (ComplexModel n)}
    {q : ComplexModel (n + 1)} (hq : stripModelEquiv n q ∈ geodesicChartDomain W) :
    (modelChartFunction curve e ρ q : EReal) =
      subgeodesicChartFunction curve e ρ (stripModelEquiv n q) := by
  have ht : (stripModelEquiv n q).2.re ∈ Ioo (0 : ℝ) 1 := hq.2
  obtain ⟨c, hc, -, -⟩ := exists_eq_coe_of_bounded hbd ht (e.val.symm (stripModelEquiv n q).1)
  simp only [modelChartFunction, subgeodesicChartFunction, chartFunction, hc]
  rw [← EReal.coe_add, EReal.toReal_coe]

/-- The real corrected complexification of a geodesic with bounded slices is locally bounded and
plurisubharmonic on the strip. -/
theorem isLocallyBoundedPshOn_modelChartFunction {curve : ℝ → M → EReal} {A B : ℝ}
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ curve t x ∧ curve t x ≤ (B : EReal))
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ} (hW : IsOpen W)
    (hρ : ContinuousOn ρ W)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction curve e ρ) (geodesicChartDomain W)) :
    IsLocallyBoundedPshOn (modelStripOpens W hW) (modelChartFunction curve e ρ) := by
  constructor
  · have h := plurisubharmonicOn_comp_stripModelEquiv hpsh
    intro q hq
    refine (h q hq).congr ?_
    filter_upwards [(modelStripOpens W hW).isOpen.mem_nhds hq] with q' hq'
    exact (coe_modelChartFunction hbd e ρ hq').symm
  · intro q hq
    set y0 := (stripModelEquiv n q).1
    have hy0 : y0 ∈ W := hq.1
    have hρ0 : ContinuousAt ρ y0 := hρ.continuousAt (hW.mem_nhds hy0)
    have hnb : {y | |ρ y - ρ y0| < 1} ∈ 𝓝 y0 := by
      filter_upwards [hρ0 (Metric.ball_mem_nhds (ρ y0) one_pos)] with y hy
      simpa [Metric.mem_ball, Real.dist_eq] using hy
    obtain ⟨O, hOsub, hOopen, hy0O⟩ := mem_nhds_iff.mp hnb
    let V : Opens (ComplexModel (n + 1)) :=
      ⟨stripModelEquiv n ⁻¹' ((W ∩ O) ×ˢ complexTimeStrip),
        ((hW.inter hOopen).prod isOpen_complexTimeStrip).preimage (stripModelEquiv n).continuous⟩
    refine ⟨V, ⟨⟨hy0, hy0O⟩, hq.2⟩, fun q' hq' => ⟨hq'.1.1, hq'.2⟩,
      max |A| |B| + (|ρ y0| + 1), fun q' hq' => ?_⟩
    have ht : (stripModelEquiv n q').2.re ∈ Ioo (0 : ℝ) 1 := hq'.2
    obtain ⟨c, hc, hcA, hcB⟩ :=
      exists_eq_coe_of_bounded hbd ht (e.val.symm (stripModelEquiv n q').1)
    have hval : modelChartFunction curve e ρ q' = c + ρ (stripModelEquiv n q').1 := by
      simp only [modelChartFunction, subgeodesicChartFunction, chartFunction, hc]
      rw [← EReal.coe_add, EReal.toReal_coe]
    rw [hval]
    have hρq : |ρ (stripModelEquiv n q').1 - ρ y0| < 1 := hOsub hq'.1.2
    have hcabs : |c| ≤ max |A| |B| := by
      rcases le_total 0 c with h | h
      · rw [abs_of_nonneg h]; exact (le_abs_self B |>.trans' hcB).trans (le_max_right _ _)
      · rw [abs_of_nonpos h]
        exact (neg_le_neg hcA |>.trans (neg_le_abs A)).trans (le_max_left _ _)
    have hρabs : |ρ (stripModelEquiv n q').1| ≤ |ρ y0| + 1 := by
      have := abs_sub_abs_le_abs_sub (ρ (stripModelEquiv n q').1) (ρ y0)
      linarith
    calc |c + ρ (stripModelEquiv n q').1| ≤ |c| + |ρ (stripModelEquiv n q').1| := abs_add_le _ _
      _ ≤ max |A| |B| + (|ρ y0| + 1) := add_le_add hcabs hρabs

open Classical in
/-- The complexified curve with the balayage of its corrected complexification glued in over the
polydisk `c + rP` (read through the chart `e` and `ℂⁿ × ℂ ≃ ℂⁿ⁺¹`). -/
def balayageModification (curve : ℝ → M → EReal) (e : ComplexChart n M)
    (ρ : ComplexModel n → ℝ) (c : ComplexModel (n + 1)) (r : ℝ) : M → ℂ → EReal :=
  fun x τ =>
    if x ∈ e.val.source ∧ (stripModelEquiv n).symm (e.val x, τ) ∈ scaledPolydisk c r then
      ((scaledPolydiskBalayage c r (modelChartFunction curve e ρ)
          ((stripModelEquiv n).symm (e.val x, τ)) - ρ (e.val x) : ℝ) : EReal)
    else curve τ.re x

/-- **The complexified geodesic is its own balayage** (Xia, proof of Proposition 4.3.3, Step 2).
Let the Perron geodesic `U` from `u₀` to `u₁` be a subgeodesic from `u₀` to `u₁` with uniformly
bounded slices. In a chart `e` with a smooth local potential `ρ` of `θ` on `W` for which the
corrected complexification is plurisubharmonic on `W × strip`, the balayage of that function
(read on `ℂⁿ⁺¹`) on any polydisk whose closure lies in `W × strip` equals the function on the
polydisk. -/
theorem eqOn_scaledPolydiskBalayage_finiteGeodesic
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁) {A B : ℝ}
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ finiteGeodesic θ u₀ u₁ t x ∧
      finiteGeodesic θ u₀ u₁ t x ≤ (B : EReal))
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (geodesicChartDomain W))
    {c : ComplexModel (n + 1)} {r : ℝ} (hr : 0 < r)
    (hP : polydiskChart c r '' closedUnitPolydisk (n + 1) ⊆ modelStripOpens W hρ.1) :
    EqOn (scaledPolydiskBalayage c r (modelChartFunction (finiteGeodesic θ u₀ u₁) e ρ))
      (modelChartFunction (finiteGeodesic θ u₀ u₁) e ρ) (scaledPolydisk c r) := by
  classical
  set U := finiteGeodesic θ u₀ u₁ with hUdef
  set L := stripModelEquiv n with hLdef
  set hL := modelChartFunction U e ρ with hhLdef
  set bal := scaledPolydiskBalayage c r hL with hbaldef
  set Ω := modelStripOpens W hρ.1 with hΩdef
  have hr0 : r ≠ 0 := hr.ne'
  have hlb : IsLocallyBoundedPshOn Ω hL :=
    isLocallyBoundedPshOn_modelChartFunction hbd e hρ.1 hρ.2.2.1.continuousOn hpsh
  set Pbar := polydiskChart c r '' closedUnitPolydisk (n + 1) with hPbar
  have hPbarc : IsCompact Pbar :=
    isCompact_closedUnitPolydisk.image (continuous_polydiskChart c r)
  have hPsub : scaledPolydisk c r ⊆ Pbar :=
    image_mono unitPolydisk_subset_closedUnitPolydisk
  have hcP : c ∈ Pbar := ⟨0, fun i => by simp, by simp [polydiskChart]⟩
  -- (B1)-(B4): the balayage
  have hbalpsh : PlurisubharmonicOn (fun q => ((bal q : ℝ) : EReal)) (Ω : Set (ComplexModel (n + 1))) :=
    plurisubharmonicOn_scaledPolydiskBalayage (Nat.succ_pos n) hlb hr0 hP
  have hbal_off : ∀ q, q ∉ scaledPolydisk c r → bal q = hL q := fun q hq =>
    scaledPolydiskBalayage_eqOn_compl hr0 hL hq
  have hPΩ' : closedUnitPolydisk (n + 1) ⊆
      (Opens.comap ⟨polydiskChart c r, continuous_polydiskChart c r⟩ Ω :
        Set (ComplexModel (n + 1))) := fun w hw => hP ⟨w, hw, rfl⟩
  have hbal_ge : ∀ q ∈ scaledPolydisk c r, hL q ≤ bal q := by
    intro q hq
    have hq' := (mem_scaledPolydisk_iff hr0).mp hq
    rw [hbaldef, scaledPolydiskBalayage_of_mem hr0 hL hq]
    have h := le_perronEnvelope_of_isLocallyBoundedPshOn (Nat.succ_pos n)
      (isLocallyBoundedPshOn_comp_polydiskChart hlb c r) hPΩ' hq'
    simpa [polydiskChart_polydiskChartInv hr0] using h
  obtain ⟨Cb, -, hCb⟩ := hlb.exists_compact_abs_bound hPbarc hP
  have hbal_le : ∀ q ∈ scaledPolydisk c r, bal q ≤ Cb := by
    intro q hq
    have hq' := (mem_scaledPolydisk_iff hr0).mp hq
    rw [hbaldef, scaledPolydiskBalayage_of_mem hr0 hL hq]
    exact perronEnvelope_le_of_isLocallyBoundedPshOn (Nat.succ_pos n)
      (isLocallyBoundedPshOn_comp_polydiskChart hlb c r) hPΩ'
      (fun w hw => (le_abs_self _).trans (hCb _ ⟨w, hw, rfl⟩)) hq'
  -- (B5): the real parts over the closed polydisk
  have hfc : Continuous fun q : ComplexModel (n + 1) => (L q).2.re :=
    Complex.continuous_re.comp (continuous_snd.comp L.continuous)
  obtain ⟨qa, hqa, hqamin⟩ := hPbarc.exists_isMinOn ⟨c, hcP⟩ hfc.continuousOn
  obtain ⟨qb, hqb, hqbmax⟩ := hPbarc.exists_isMaxOn ⟨c, hcP⟩ hfc.continuousOn
  set a := (L qa).2.re
  set b := (L qb).2.re
  have ha : 0 < a := (hP hqa).2.1
  have hb : b < 1 := (hP hqb).2.2
  have hab : a ≤ b := (hqamin hqb).trans_eq rfl |>.trans (hqbmax hqb)
  have hPre : ∀ q ∈ Pbar, a ≤ (L q).2.re ∧ (L q).2.re ≤ b := fun q hq => ⟨hqamin hq, hqbmax hq⟩
  -- (B6): the spatial projection
  set Kx := (fun q : ComplexModel (n + 1) => (L q).1) '' Pbar with hKx
  have hKxc : IsCompact Kx := hPbarc.image (continuous_fst.comp L.continuous)
  have hKxW : Kx ⊆ W := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hP hq).1
  have hWt : W ⊆ e.val.target := hρ.2.1
  set KM := e.val.symm '' Kx with hKM
  have hKMc : IsCompact KM :=
    hKxc.image_of_continuousOn (e.val.continuousOn_symm.mono (hKxW.trans hWt))
  have hKMcl : IsClosed KM := hKMc.isClosed
  have hKMsrc : KM ⊆ e.val.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.val.map_target (hWt (hKxW hy))
  obtain ⟨ρmin, hρmin⟩ : ∃ m : ℝ, ∀ y ∈ Kx, m ≤ ρ y := by
    obtain ⟨y0, -, hy0⟩ := hKxc.exists_isMinOn ⟨_, ⟨c, hcP, rfl⟩⟩
      (hρ.2.2.1.continuousOn.mono hKxW)
    exact ⟨ρ y0, fun y hy => hy0 hy⟩
  -- (B7): the modified branch
  have hmod : ∀ x τ, x ∈ e.val.source → L.symm (e.val x, τ) ∈ scaledPolydisk c r →
      x ∈ KM ∧ e.val x ∈ Kx ∧ a ≤ τ.re ∧ τ.re ≤ b := by
    intro x τ hx hq
    have hqP : L.symm (e.val x, τ) ∈ Pbar := hPsub hq
    have hLq : L (L.symm (e.val x, τ)) = (e.val x, τ) := L.apply_symm_apply _
    have hex : e.val x ∈ Kx := ⟨_, hqP, by simp only [hLq]⟩
    refine ⟨⟨e.val x, hex, e.val.left_inv hx⟩, hex, ?_, ?_⟩
    · simpa [hLq] using (hPre _ hqP).1
    · simpa [hLq] using (hPre _ hqP).2
  set F := balayageModification U e ρ c r with hFdef
  -- values of the real chart function
  have hLval : ∀ q, L q ∈ geodesicChartDomain W → ∃ cU : ℝ,
      U (L q).2.re (e.val.symm (L q).1) = (cU : EReal) ∧ hL q = cU + ρ (L q).1 := by
    intro q hq
    obtain ⟨cU, hcU, -, -⟩ := exists_eq_coe_of_bounded hbd hq.2 (e.val.symm (L q).1)
    refine ⟨cU, hcU, ?_⟩
    simp only [hhLdef, modelChartFunction, subgeodesicChartFunction, chartFunction, ← hLdef, hcU]
    rw [← EReal.coe_add, EReal.toReal_coe]
  -- (F1)
  have hle : ∀ x τ, U τ.re x ≤ F x τ := by
    intro x τ
    by_cases h : x ∈ e.val.source ∧ L.symm (e.val x, τ) ∈ scaledPolydisk c r
    · have hFx : F x τ = ((bal (L.symm (e.val x, τ)) - ρ (e.val x) : ℝ) : EReal) := by
        simp only [hFdef, balayageModification, ← hLdef, if_pos h]
        rfl
      rw [hFx]
      have hLq : L (L.symm (e.val x, τ)) = (e.val x, τ) := L.apply_symm_apply _
      have hdom : L (L.symm (e.val x, τ)) ∈ geodesicChartDomain W := hP (hPsub h.2)
      obtain ⟨cU, hcU, hval⟩ := hLval _ hdom
      rw [hLq] at hcU hval
      simp only [e.val.left_inv h.1] at hcU
      rw [hcU, EReal.coe_le_coe_iff]
      have := hbal_ge _ h.2
      linarith
    · simp only [hFdef, balayageModification, ← hLdef, if_neg h, le_refl]
  -- (F2)
  have hout : ∀ x τ, (τ.re < a ∨ b < τ.re) → F x τ = U τ.re x := by
    intro x τ hτ
    have h : ¬ (x ∈ e.val.source ∧ L.symm (e.val x, τ) ∈ scaledPolydisk c r) := by
      rintro ⟨hx, hq⟩
      obtain ⟨-, -, h1, h2⟩ := hmod x τ hx hq
      rcases hτ with hτ | hτ <;> linarith
    simp only [hFdef, balayageModification, ← hLdef, if_neg h]
  -- (F4)
  have hC : ∀ x τ, τ.re ∈ Ioo (0 : ℝ) 1 → F x τ ≤ ((max B (Cb - ρmin) : ℝ) : EReal) := by
    intro x τ hτ
    by_cases h : x ∈ e.val.source ∧ L.symm (e.val x, τ) ∈ scaledPolydisk c r
    · simp only [hFdef, balayageModification, ← hLdef, if_pos h, EReal.coe_le_coe_iff]
      have h1 := hbal_le _ h.2
      have h2 := hρmin _ (hmod x τ h.1 h.2).2.1
      exact (by linarith : bal (L.symm (e.val x, τ)) - ρ (e.val x) ≤ Cb - ρmin).trans
        (le_max_right _ _)
    · simp only [hFdef, balayageModification, ← hLdef, if_neg h]
      exact (hbd _ hτ x).2.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  -- (F3)
  have hwit : ∀ (e' : ComplexChart n M) (z : ComplexModel n), z ∈ e'.val.target →
      ∃ (W' : Set (ComplexModel n)) (ρ' : ComplexModel n → ℝ),
        z ∈ W' ∧ IsSmoothLocalPotential θ e' W' ρ' ∧
        ∀ s : ℝ, PlurisubharmonicOn
          (stripChartFunction (fun x τ => F x (τ + (s : ℂ) * Complex.I)) e' ρ')
          (geodesicChartDomain W') := by
    intro e' z hz
    by_cases hzK : e'.val.symm z ∈ KM
    · -- the balayage chart
      have hchartE : ∀ s : ℝ, PlurisubharmonicOn
          (stripChartFunction (fun x τ => F x (τ + (s : ℂ) * Complex.I)) e ρ)
          (geodesicChartDomain W) := by
        intro s
        have hb1 := plurisubharmonicOn_comp_stripModelEquiv_symm hbalpsh
        have hb2 := hb1.comp_affine (ContinuousLinearMap.id ℂ (ComplexModel n × ℂ))
          ((0 : ComplexModel n), (s : ℂ) * Complex.I)
        intro p hp
        have hmem : p ∈ (fun y => ((0 : ComplexModel n), (s : ℂ) * Complex.I) +
            ContinuousLinearMap.id ℂ (ComplexModel n × ℂ) y) ⁻¹'
            ((stripModelEquiv n).symm ⁻¹' (Ω : Set (ComplexModel (n + 1)))) := by
          simp only [mem_preimage, ContinuousLinearMap.id_apply]
          show L (L.symm (((0 : ComplexModel n), (s : ℂ) * Complex.I) + p)) ∈
            geodesicChartDomain W
          rw [L.apply_symm_apply]
          refine ⟨by simpa only [Prod.fst_add, zero_add] using hp.1, ?_⟩
          have h2 := hp.2
          simp only [mem_complexTimeStrip] at h2 ⊢
          simpa only [Prod.snd_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
            zero_add] using h2
        refine (hb2 p hmem).congr ?_
        filter_upwards [(isOpen_geodesicChartDomain hρ.1).mem_nhds hp] with p' hp'
        have hx : e.val.symm p'.1 ∈ e.val.source := e.val.map_target (hWt hp'.1)
        have hex : e.val (e.val.symm p'.1) = p'.1 := e.val.right_inv (hWt hp'.1)
        have hadd : ((0 : ComplexModel n), (s : ℂ) * Complex.I) +
            ContinuousLinearMap.id ℂ (ComplexModel n × ℂ) p' =
            (p'.1, p'.2 + (s : ℂ) * Complex.I) :=
          Prod.ext (zero_add _) (add_comm _ _)
        simp only [hadd, stripChartFunction]
        by_cases hq : L.symm (p'.1, p'.2 + (s : ℂ) * Complex.I) ∈ scaledPolydisk c r
        · have h : e.val.symm p'.1 ∈ e.val.source ∧
              L.symm (e.val (e.val.symm p'.1), p'.2 + (s : ℂ) * Complex.I) ∈ scaledPolydisk c r :=
            ⟨hx, by rw [hex]; exact hq⟩
          simp only [hFdef, balayageModification, ← hLdef, hex]
          rw [if_pos ⟨hx, hq⟩, ← EReal.coe_add, sub_add_cancel]
        · have h : ¬ (e.val.symm p'.1 ∈ e.val.source ∧
              L.symm (e.val (e.val.symm p'.1), p'.2 + (s : ℂ) * Complex.I) ∈
                scaledPolydisk c r) := by
            rw [hex]; exact fun h' => hq h'.2
          simp only [hFdef, balayageModification, ← hLdef, if_neg h]
          rw [hbal_off _ hq]
          have hdom : L (L.symm (p'.1, p'.2 + (s : ℂ) * Complex.I)) ∈ geodesicChartDomain W := by
            rw [L.apply_symm_apply]
            refine ⟨hp'.1, ?_⟩
            simpa using hp'.2
          rw [coe_modelChartFunction hbd e ρ hdom, L.apply_symm_apply]
          rfl
      have hxe : e'.val.symm z ∈ e.val.source := hKMsrc hzK
      obtain ⟨y, hyK, hy⟩ := hzK
      have hcd : coordinateMap id e' e z ∈ W := by
        show e.val (id (e'.val.symm z)) ∈ W
        rw [id, ← hy, e.val.right_inv (hWt (hKxW hyK))]
        exact hKxW hyK
      refine ⟨LocalPotentialPullback.potentialDomain id e' e W, ρ ∘ coordinateMap id e' e,
        ⟨⟨hz, hxe⟩, hcd⟩, (stripWitness_of_chart e' e hρ (hchartE 0)).1,
        fun s => (stripWitness_of_chart e' e hρ (hchartE s)).2⟩
    · -- away from the modification
      obtain ⟨W1, ρ1, hzW1, hρ1, hpsh1⟩ := hsub.2.2.1.2 e' z hz
      set O := e'.val.target ∩ e'.val.symm ⁻¹' KMᶜ with hO
      have hOopen : IsOpen O :=
        e'.val.continuousOn_symm.isOpen_inter_preimage e'.val.open_target hKMcl.isOpen_compl
      have hW'' : IsOpen (W1 ∩ O) := hρ1.1.inter hOopen
      refine ⟨W1 ∩ O, ρ1, ⟨hzW1, hz, hzK⟩, hρ1.mono hW'' inter_subset_left, fun s => ?_⟩
      intro p hp
      refine ((hpsh1.mono (prod_mono inter_subset_left subset_rfl)) p hp).congr ?_
      filter_upwards [(isOpen_geodesicChartDomain hW'').mem_nhds hp] with p' hp'
      have hnot : ¬ (e'.val.symm p'.1 ∈ e.val.source ∧
          L.symm (e.val (e'.val.symm p'.1), p'.2 + (s : ℂ) * Complex.I) ∈ scaledPolydisk c r) :=
        fun h => hp'.1.2.2 (hmod _ _ h.1 h.2).1
      simp only [subgeodesicChartFunction, chartFunction, stripChartFunction, hFdef,
        balayageModification, ← hLdef, if_neg hnot]
      congr 2
      simp
  -- the symmetrized curve is a Perron competitor
  have hV := isSubgeodesicFrom_symmetrizedCurve hsub hle ha hab hb hout hwit hC
  intro q hq
  refine le_antisymm ?_ (hbal_ge q hq)
  set p := L q with hpdef
  have hdom : p ∈ geodesicChartDomain W := hP (hPsub hq)
  have hx : e.val.symm p.1 ∈ e.val.source := e.val.map_target (hWt hdom.1)
  have hex : e.val (e.val.symm p.1) = p.1 := e.val.right_inv (hWt hdom.1)
  have hqp : L.symm p = q := L.symm_apply_apply q
  have hmodq : e.val.symm p.1 ∈ e.val.source ∧
      L.symm (e.val (e.val.symm p.1), p.2) ∈ scaledPolydisk c r := by
    refine ⟨hx, ?_⟩
    rw [hex, Prod.mk.eta, hqp]
    exact hq
  have hFq : F (e.val.symm p.1) p.2 = ((bal q - ρ p.1 : ℝ) : EReal) := by
    simp only [hFdef, balayageModification, ← hLdef, hex, Prod.mk.eta, hqp]
    rw [if_pos ⟨hx, hq⟩]
  have h1 := le_symmetrizedCurve F (e.val.symm p.1) p.2
  have h2 := subgeodesic_slice_le_finiteGeodesic hV p.2.re (e.val.symm p.1)
  obtain ⟨cU, hcU, hval⟩ := hLval q hdom
  rw [hFq] at h1
  have h3 := h1.trans h2
  have hcU' : finiteGeodesic θ u₀ u₁ p.2.re (e.val.symm p.1) = (cU : EReal) := hcU
  have hval' : hL q = cU + ρ p.1 := hval
  rw [hcU', EReal.coe_le_coe_iff] at h3
  rw [hval']
  linarith

/-- **The complexified geodesic carries no Monge--Ampère mass on a polydisk** (Xia, proof of
Proposition 4.3.3, Step 2, `μ_U = 0`). Under the hypotheses of
`eqOn_scaledPolydiskBalayage_finiteGeodesic`, every Bedford--Taylor limit of `(h, …, h)`
(`n + 1` copies of the corrected complexification `h`) on the open polydisk is zero. -/
theorem isBTLimit_eq_zero_finiteGeodesic
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁) {A B : ℝ}
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ finiteGeodesic θ u₀ u₁ t x ∧
      finiteGeodesic θ u₀ u₁ t x ≤ (B : EReal))
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (geodesicChartDomain W))
    {c : ComplexModel (n + 1)} {r : ℝ} (hr : 0 < r)
    (hP : polydiskChart c r '' closedUnitPolydisk (n + 1) ⊆ modelStripOpens W hρ.1)
    {μ : MeasureTheory.Measure (ComplexModel (n + 1))}
    (hμ : IsBTLimit (scaledPolydiskOpens c r)
      (fun _ => modelChartFunction (finiteGeodesic θ u₀ u₁) e ρ) μ) :
    μ = 0 :=
  eq_zero_of_isBTLimit_of_eqOn_scaledPolydiskBalayage (Nat.succ_pos n)
    (isLocallyBoundedPshOn_modelChartFunction hbd e hρ.1 hρ.2.2.1.continuousOn hpsh) hr.ne' hP
    (eqOn_scaledPolydiskBalayage_finiteGeodesic hsub hbd e hρ hpsh hr hP).symm hμ

/-- **The complexified geodesic solves the homogeneous complex Monge--Ampère equation** on
`W × {0 < Re τ < 1}` (Xia, proof of Proposition 4.3.3, Step 2). Under the hypotheses of
`eqOn_scaledPolydiskBalayage_finiteGeodesic`, every Bedford--Taylor limit of `(h, …, h)`
(`n + 1` copies of the corrected complexification `h`, read on `ℂⁿ⁺¹`) on `W × strip` is zero:
it vanishes on a polydisk around every point (`isBTLimit_eq_zero_finiteGeodesic`). -/
theorem isBTLimit_modelStripOpens_eq_zero_finiteGeodesic
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁) {A B : ℝ}
    (hbd : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, (A : EReal) ≤ finiteGeodesic θ u₀ u₁ t x ∧
      finiteGeodesic θ u₀ u₁ t x ≤ (B : EReal))
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ)
    (hpsh : PlurisubharmonicOn (subgeodesicChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (geodesicChartDomain W))
    {μ : MeasureTheory.Measure (ComplexModel (n + 1))}
    (hμ : IsBTLimit (modelStripOpens W hρ.1)
      (fun _ => modelChartFunction (finiteGeodesic θ u₀ u₁) e ρ) μ) :
    μ = 0 := by
  set Ω := modelStripOpens W hρ.1 with hΩdef
  have hΩ : μ (Ω : Set (ComplexModel (n + 1))) = 0 := by
    refine MeasureTheory.measure_null_of_locally_null _ fun q hq => ?_
    obtain ⟨r, hr, hP⟩ := exists_pos_image_closedUnitPolydisk_subset hq
    have h0 := isBTLimit_eq_zero_finiteGeodesic hsub hbd e hρ hpsh hr hP
      (hμ.restrict_opens (scaledPolydiskOpens_le hr.ne' hP))
    have hqV : q ∈ (scaledPolydiskOpens q r : Set (ComplexModel (n + 1))) := by
      rw [coe_scaledPolydiskOpens hr.ne']
      exact mem_scaledPolydisk_center hr.ne'
    refine ⟨scaledPolydiskOpens q r,
      mem_nhdsWithin_of_mem_nhds ((scaledPolydiskOpens q r).isOpen.mem_nhds hqV), ?_⟩
    rw [← MeasureTheory.Measure.restrict_apply_self, h0]
    rfl
  have h := MeasureTheory.measure_union_le (μ := μ) (Ω : Set (ComplexModel (n + 1)))
    (Ω : Set (ComplexModel (n + 1)))ᶜ
  rw [union_compl_self, hΩ, hμ.1, add_zero] at h
  exact MeasureTheory.Measure.measure_univ_eq_zero.mp (nonpos_iff_eq_zero.mp h)

end Balayage

end

end SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
