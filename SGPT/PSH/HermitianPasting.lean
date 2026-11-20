import SGPT.PSH.HermitianEnvelopeStability
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshSmoothLocalization
import SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingPSH

/-!
# Maximum pasting for nonclosed Hermitian backgrounds

A local branch is supplied by an actual PSH correction and a pointwise
Hessian inequality. These ordinary local data transport through the
holomorphic atlas. Maximum pasting uses common frozen corrections and
recovers the exact original background by letting the error tend to zero.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.Hermitian

open Set Filter TopologicalSpace
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending
open ERealBoundaryMaxPastingTopology ERealBoundaryMaxPastingPSH

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- A smooth local function with nonnegative genuine complex Hessian is PSH. -/
theorem plurisubharmonicOn_coe_of_smoothDDC_nonneg
    {W : Set (ComplexModel (m + 1))} {h : ComplexModel (m + 1) → ℝ}
    (hW : IsOpen W) (hh : ContDiffOn ℝ ∞ h W)
    (hddc : ∀ z ∈ W, ∀ v : ComplexModel (m + 1),
      0 ≤ smoothDDC h z ![v, Complex.I • v]) :
    PlurisubharmonicOn (fun z => (h z : EReal)) W := by
  intro x hx
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hW hh hx
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp (heq.and (hW.mem_nhds hx))
  have hVddc : ∀ y ∈ V, ∀ v : ComplexModel (m + 1), 0 ≤ leviForm g y v := by
    intro y hy v
    have hloc : h =ᶠ[𝓝 y] g := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact (hVsub hz).1
    have hdiag := smoothDDC_complexDiagonal_eq_leviForm (z := y)
      ((hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt) v
    have hnonneg := hddc y (hVsub hy).2 v
    rw [smoothDDC_congr hloc, hdiag] at hnonneg
    have hmul := mul_nonneg hnonneg Real.pi_pos.le
    simpa only [div_mul_cancel₀ _ Real.pi_ne_zero] using hmul
  apply ((plurisubharmonicOn_of_levi_nonneg
    (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hV hVddc) x hxV).congr
  exact heq.mono fun y hy => congrArg (fun r : ℝ => (r : EReal)) hy.symm

/-- A genuine local PSH-plus-smooth decomposition with Hessian bounded by
its background. This is local input data, with no closedness condition. -/
def HasDominatedLocalPSHCorrections
    (θ : SmoothRealForm (m + 1) M 2) (v : M → EReal) (U : Set M) : Prop :=
  ∀ (e : ComplexChart (m + 1) M) z, z ∈ e.val.target → e.val.symm z ∈ U →
    ∃ (W : Opens (ComplexModel (m + 1))) (_hW : W ≤ chartTarget e)
      (q : ComplexModel (m + 1) → ℝ), z ∈ W ∧
      (∀ y ∈ W, e.val.symm y ∈ U) ∧ ContDiffOn ℝ ∞ q W ∧
      PlurisubharmonicOn (fun y => chartFunction v e y + (q y : EReal)) W ∧
      ∀ y ∈ W, ∀ a : ComplexModel (m + 1), smoothDDC q y ![a, Complex.I • a] ≤
        θ.coeff e y ![a, Complex.I • a]

/-- A common dominating correction turns the local branch into a genuine
PSH function on the whole intersection of its domain with the chart patch. -/
theorem HasDominatedLocalPSHCorrections.corrected_plurisubharmonicOn
    {θ : SmoothRealForm (m + 1) M 2} {v : M → EReal} {U : Set M}
    (hv : HasDominatedLocalPSHCorrections θ v U)
    (e : ComplexChart (m + 1) M) {W : Opens (ComplexModel (m + 1))}
    (hW : W ≤ chartTarget e) {q : ComplexModel (m + 1) → ℝ}
    (hq : ContDiffOn ℝ ∞ q W)
    (hdom : ∀ y ∈ W, ∀ a : ComplexModel (m + 1),
      θ.coeff e y ![a, Complex.I • a] ≤ smoothDDC q y ![a, Complex.I • a]) :
    PlurisubharmonicOn (fun y => chartFunction v e y + (q y : EReal))
      ((W : Set (ComplexModel (m + 1))) ∩ e.val.symm ⁻¹' U) := by
  intro z hz
  obtain ⟨V, _hV, p, hzV, _hVU, hp, hpsh, hpdom⟩ := hv e z (hW hz.1) hz.2
  let Q : Set (ComplexModel (m + 1)) := W ∩ V
  have hQ : IsOpen Q := W.isOpen.inter V.isOpen
  have hqp : ContDiffOn ℝ ∞ (fun y => q y - p y) Q :=
    (hq.mono inter_subset_left).sub (hp.mono inter_subset_right)
  have hgap : PlurisubharmonicOn (fun y => ((q y - p y : ℝ) : EReal)) Q := by
    apply plurisubharmonicOn_coe_of_smoothDDC_nonneg hQ hqp
    intro y hy a
    rw [PositiveClasses.smoothDDC_sub hQ (hq.mono inter_subset_left)
      (hp.mono inter_subset_right) hy]
    exact sub_nonneg.mpr ((hpdom y hy.2 a).trans (hdom y hy.1 a))
  apply (((hpsh.mono inter_subset_right).add hgap) z ⟨hz.1, hzV⟩).congr
  exact Eventually.of_forall fun y => corrected_add_sub (chartFunction v e y) (p y) (q y)

/-- A PSH correction and its genuine Hessian bound in one chart transport
internally to every holomorphic chart meeting the local domain. -/
theorem hasDominatedLocalPSHCorrections_of_chart
    (θ : SmoothRealForm (m + 1) M 2) (e : ComplexChart (m + 1) M)
    {U : Set M} (hU : IsOpen U) (hUs : U ⊆ e.val.source)
    {v : M → EReal} {q : ComplexModel (m + 1) → ℝ}
    (hq : ContDiffOn ℝ ∞ q (e.val.target ∩ e.val.symm ⁻¹' U))
    (hp : PlurisubharmonicOn (fun y => chartFunction v e y + (q y : EReal))
      (e.val.target ∩ e.val.symm ⁻¹' U))
    (hdom : ∀ y ∈ e.val.target ∩ e.val.symm ⁻¹' U,
      ∀ a : ComplexModel (m + 1), smoothDDC q y ![a, Complex.I • a] ≤
        θ.coeff e y ![a, Complex.I • a]) :
    HasDominatedLocalPSHCorrections θ v U := by
  intro f z hz hzU
  let D : Set (ComplexModel (m + 1)) := e.val.target ∩ e.val.symm ⁻¹' U
  let V : Opens (ComplexModel (m + 1)) :=
    ⟨f.val.target ∩ f.val.symm ⁻¹' U, f.val.isOpen_inter_preimage_symm hU⟩
  let F := coordinateMap (id : M → M) f e
  have hD : IsOpen D := e.val.isOpen_inter_preimage_symm hU
  have hVo : IsOpen (V : Set (ComplexModel (m + 1))) := V.isOpen
  have hVsub : (V : Set (ComplexModel (m + 1))) ⊆ coordinateDomain (id : M → M) f e :=
    fun y hy => ⟨hy.1, hUs hy.2⟩
  have hF : ContDiffOn ℂ ∞ F V :=
    (coordinateMap_contDiffOn contMDiff_id f e).mono hVsub
  have hFV : MapsTo F (V : Set (ComplexModel (m + 1))) D := by
    intro y hy
    refine ⟨e.val.map_source (hUs hy.2), ?_⟩
    change e.val.symm (e.val (f.val.symm y)) ∈ U
    rw [e.val.left_inv (hUs hy.2)]
    exact hy.2
  refine ⟨V, fun _ hy => hy.1, fun y => q (F y), ⟨hz, hzU⟩,
    fun _ hy => hy.2, hq.comp (hF.restrict_scalars ℝ) hFV, ?_, ?_⟩
  · intro y hy
    have hcomp := HolomorphicPullback.plurisubharmonicAt_comp_holomorphic hVo
      (hF.differentiableOn (by simp)) hy (hp (F y) (hFV hy))
    apply hcomp.congr
    filter_upwards [hVo.mem_nhds hy] with t ht
    change v (e.val.symm (e.val (f.val.symm t))) + (q (F t) : EReal) = _
    rw [e.val.left_inv (hUs ht.2)]
    rfl
  · intro y hy a
    rw [HolomorphicDDC.smoothDDC_comp hVo hD hF hq hFV hy,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hθ := θ.compatible f e y (hVsub hy) ![a, Complex.I • a]
    have hI := coordinateMap_fderiv_map_smul_complex contMDiff_id f e (hVsub hy)
      Complex.I a
    have hvec : (fun i : Fin 2 => fderiv ℝ F y (![a, Complex.I • a] i)) =
        ![fderiv ℝ F y a, Complex.I • fderiv ℝ F y a] := by
      funext i
      fin_cases i
      · rfl
      · change fderiv ℝ F y (Complex.I • a) = Complex.I • fderiv ℝ F y a
        exact hI
    change smoothDDC q (F y) (fun i => fderiv ℝ F y (![a, Complex.I • a] i)) ≤ _
    rw [hvec]
    change θ.coeff f y ![a, Complex.I • a] = _ at hθ
    rw [hθ]
    change _ ≤ θ.coeff e (F y) (fun i => fderiv ℝ F y (![a, Complex.I • a] i))
    rw [hvec]
    exact hdom (F y) (hFV hy) (fderiv ℝ F y a)

private theorem boundaryDominatedOn_comp_continuousOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {Ω : Set X} {U : Set Y} {F : X → Y} {v u : Y → EReal}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hF : ContinuousOn F Ω)
    (hb : BoundaryDominatedOn univ U v u) :
    BoundaryDominatedOn Ω (Ω ∩ F ⁻¹' U) (v ∘ F) (u ∘ F) := by
  intro z hz c hc
  have hFc : ContinuousAt F z := hF.continuousAt (hΩ.mem_nhds hz.1)
  have hxcl : F z ∈ closure U :=
    (closure_mono (image_subset_iff.mpr (fun _ hy => hy.2)))
      (mem_closure_image hFc hz.2.1)
  have hD : IsOpen (Ω ∩ F ⁻¹' U) := hF.isOpen_inter_preimage hΩ hU
  have hxnot : F z ∉ U := by
    intro hx
    exact hz.2.2 (by rw [hD.interior_eq]; exact ⟨hz.1, hx⟩)
  have hxfr : F z ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨hxcl, hxnot⟩
  have hnear : ∀ᶠ y in 𝓝 (F z), y ∈ U → v y < c :=
    eventually_nhdsWithin_iff.mp (hb (F z) ⟨mem_univ _, hxfr⟩ c hc)
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [hFc.tendsto.eventually hnear] with y hy hyD
  exact hy hyD.2

private theorem boundaryDominatedOn_add_continuous
    {X : Type*} [TopologicalSpace X] {Ω D : Set X}
    {v u : X → EReal} {q : X → ℝ}
    (hΩ : IsOpen Ω) (hq : ContinuousOn q Ω)
    (hb : BoundaryDominatedOn Ω D v u) :
    BoundaryDominatedOn Ω D (fun y => v y + (q y : EReal))
      (fun y => u y + (q y : EReal)) := by
  intro x hx c hc
  obtain ⟨r, hur, hrc⟩ := EReal.exists_between_coe_real hc
  obtain ⟨s, hrs, hsc⟩ := EReal.exists_between_coe_real hrc
  have hux : u x < ((r - q x : ℝ) : EReal) := by
    simpa only [← EReal.coe_sub] using
      (EReal.lt_sub_iff_add_lt (.inl (EReal.coe_ne_bot (q x)))
        (.inl (EReal.coe_ne_top (q x)))).mpr hur
  have hnear := hb x hx ((r - q x : ℝ) : EReal) hux
  have hrsR : r < s := EReal.coe_lt_coe_iff.mp hrs
  have hqnear : ∀ᶠ y in 𝓝 x, q y < q x + (s - r) :=
    (hq.continuousAt (hΩ.mem_nhds hx.1)).eventually
      (isOpen_Iio.mem_nhds (show q x < q x + (s - r) by linarith))
  filter_upwards [hnear, hqnear.filter_mono nhdsWithin_le_nhds] with y hvy hqy
  have hsum : v y + (q y : EReal) < ((r - q x + q y : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact EReal.add_lt_add_right_coe hvy (q y)
  exact hsum.trans ((EReal.coe_lt_coe_iff.mpr (show r - q x + q y < s by linarith)).trans hsc)

private theorem max_add_real (a b : EReal) (r : ℝ) :
    max a b + (r : EReal) = max (a + (r : EReal)) (b + (r : EReal)) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,
      max_eq_right ((EReal.addLECancellable_coe r).add_le_add_iff_right.mpr h)]
  · rw [max_eq_left h,
      max_eq_left ((EReal.addLECancellable_coe r).add_le_add_iff_right.mpr h)]

/-- Actual boundary upper-limit dominance pastes a local PSH-plus-smooth
branch into a global potential, preserving its exact nonclosed background. -/
theorem isFormPSH_gluedMax_of_boundary
    (θ : SmoothRealForm (m + 1) M 2) (hθ₁ : θ.IsTypeOneOne)
    {U : Set M} (hU : IsOpen U) {v u : M → EReal}
    (hv : HasDominatedLocalPSHCorrections θ v U) (hu : IsFormPSH θ u)
    (hb : BoundaryDominatedOn univ U v u) :
    IsFormPSH θ (gluedMax U v u) := by
  let w : M → EReal := gluedMax U v u
  have hlocal : ∀ (e : ComplexChart (m + 1) M) z, z ∈ e.val.target →
      ∀ ε : ℝ, 0 < ε → ∃ (W : Opens (ComplexModel (m + 1))) (_hW : W ≤ chartTarget e)
        (q : ComplexModel (m + 1) → ℝ), z ∈ W ∧ ContDiffOn ℝ ∞ q W ∧
        PlurisubharmonicOn (fun y => chartFunction w e y + (q y : EReal)) W ∧
        ∀ y ∈ W, ∀ a : ComplexModel (m + 1), smoothDDC q y ![a, Complex.I • a] ≤
          θ.coeff e y ![a, Complex.I • a] + ε * ‖a‖ ^ 2 := by
    intro e z hz ε hε
    obtain ⟨W₀, q, hzW, hWo, hWt, hq, hbounds⟩ :=
      HermitianFreezing.exists_local_approximate_potential e.val.open_target
        (θ.coeff e) (θ.smooth e) (hθ₁ e) hz hε
    let W : Opens (ComplexModel (m + 1)) := ⟨W₀, hWo⟩
    have hW : W ≤ chartTarget e := hWt
    have huP := chart_add_smooth_plurisubharmonicOn hθ₁ hu e hW hq
      (fun y hy a => (hbounds y hy a).1)
    have hvP := hv.corrected_plurisubharmonicOn e hW hq
      (fun y hy a => (hbounds y hy a).1)
    have hF : ContinuousOn e.val.symm (W : Set (ComplexModel (m + 1))) :=
      e.val.continuousOn_symm.mono hW
    have hD : IsOpen ((W : Set (ComplexModel (m + 1))) ∩ e.val.symm ⁻¹' U) :=
      hF.isOpen_inter_preimage W.isOpen hU
    have hb₀ := boundaryDominatedOn_comp_continuousOn W.isOpen hU hF hb
    have hbq := boundaryDominatedOn_add_continuous W.isOpen hq.continuousOn hb₀
    have hp := ERealBoundaryMaxPastingPSH.plurisubharmonicOn_gluedMax W.isOpen hD
      huP hvP hbq
    refine ⟨W, hW, q, hzW, hq, ?_, fun y hy a => (hbounds y hy a).2⟩
    intro y hy
    apply (hp y hy).congr
    filter_upwards [W.isOpen.mem_nhds hy] with t ht
    by_cases htU : e.val.symm t ∈ U
    · simp only [gluedMax, mem_inter_iff, mem_preimage, ht, htU, and_self, ↓reduceIte,
        chartFunction, w]
      exact (max_add_real (v (e.val.symm t)) (u (e.val.symm t)) (q t)).symm
    · simp only [gluedMax, mem_inter_iff, mem_preimage, ht, htU, and_false, ↓reduceIte,
        chartFunction, w]
  have hn : LocallyNondegenerate w := by
    intro x O hO hx
    obtain ⟨y, hy, huy⟩ := hu.quasiPshPotential.2 x O hO hx
    refine ⟨y, hy, ?_⟩
    have hle : u y ≤ w y := by
      by_cases hyU : y ∈ U
      · change u y ≤ gluedMax U v u y
        rw [gluedMax_eq_max hyU]
        exact le_max_right _ _
      · simp only [w, gluedMax, hyU, ↓reduceIte, le_refl]
    intro hbot
    exact huy (le_bot_iff.mp (hbot ▸ hle))
  have hwQ : IsGlobalQuasiPshPotential (n := m + 1) w := by
    refine ⟨?_, hn⟩
    intro e z hz
    obtain ⟨W, _hW, q, hzW, hq, hp, _⟩ := hlocal e z hz 1 zero_lt_one
    refine ⟨fun y => chartFunction w e y + (q y : EReal), fun y => -q y,
      hp z hzW, ?_, ?_⟩
    · filter_upwards [W.isOpen.mem_nhds hzW] with y hy
      exact ((hq.neg) y hy).contDiffAt (W.isOpen.mem_nhds hy)
    · exact Eventually.of_forall fun y => by
        dsimp only
        rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  exact isFormPSH_of_approximate_local_psh θ hθ₁ w hwQ hlocal

/-- The ordinary boundary-limsup formulation of nonclosed maximum pasting. -/
theorem isFormPSH_gluedMax_of_boundary_limsup
    (θ : SmoothRealForm (m + 1) M 2) (hθ₁ : θ.IsTypeOneOne)
    {U : Set M} (hU : IsOpen U) {v u : M → EReal}
    (hv : HasDominatedLocalPSHCorrections θ v U) (hu : IsFormPSH θ u)
    (hb : ∀ x ∈ frontier U, limsup v (𝓝[U] x) ≤ u x) :
    IsFormPSH θ (gluedMax U v u) :=
  isFormPSH_gluedMax_of_boundary θ hθ₁ hU hv hu
    (fun x hx c hc => eventually_lt_of_limsup_lt ((hb x hx.2).trans_lt hc))

/-- An explicit collar gives genuine boundary upper-limit control. -/
theorem isFormPSH_gluedMax_of_collar
    (θ : SmoothRealForm (m + 1) M 2) (hθ₁ : θ.IsTypeOneOne)
    {U U' : Set M} (hU : IsOpen U) (hclosure : closure U' ⊆ U)
    {v u : M → EReal} (hcollar : ∀ x ∈ U \ U', v x ≤ u x)
    (hv : HasDominatedLocalPSHCorrections θ v U) (hu : IsFormPSH θ u) :
    IsFormPSH θ (gluedMax U v u) := by
  apply isFormPSH_gluedMax_of_boundary θ hθ₁ hU hv hu
  intro x hx c hc
  have hxnot : x ∉ closure U' := by
    intro hxcl
    exact hx.2.2 (by rw [hU.interior_eq]; exact hclosure hxcl)
  have huusc := hu.quasiPshPotential.1.upperSemicontinuous x c hc
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxnot, huusc] with y hy huy hyU
  exact (hcollar y ⟨hyU, fun hyU' => hy (subset_closure hyU')⟩).trans_lt huy

/-- One actual chart correction and genuine boundary control produce a
member of the original global Hermitian class. All chart transport is internal. -/
theorem isHermitianPSH_gluedMax_of_chart_boundary_limsup
    (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    {U : Set M} (hU : IsOpen U) (hUs : U ⊆ e.val.source)
    {v u : M → EReal} {q : ComplexModel (m + 1) → ℝ}
    (hq : ContDiffOn ℝ ∞ q (e.val.target ∩ e.val.symm ⁻¹' U))
    (hp : PlurisubharmonicOn (fun y => chartFunction v e y + (q y : EReal))
      (e.val.target ∩ e.val.symm ⁻¹' U))
    (hdom : ∀ y ∈ e.val.target ∩ e.val.symm ⁻¹' U,
      ∀ a : ComplexModel (m + 1), smoothDDC q y ![a, Complex.I • a] ≤
        omega.form.coeff e y ![a, Complex.I • a])
    (hu : IsHermitianPSH omega u)
    (hb : ∀ x ∈ frontier U, limsup v (𝓝[U] x) ≤ u x) :
    IsHermitianPSH omega (gluedMax U v u) :=
  isFormPSH_gluedMax_of_boundary_limsup omega.form omega.isTypeOneOne hU
    (hasDominatedLocalPSHCorrections_of_chart omega.form e hU hUs hq hp hdom) hu hb

/-- The chart-domain collar form of genuine Hermitian maximum pasting. -/
theorem isHermitianPSH_gluedMax_of_chart_collar
    (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    {U U' : Set M} (hU : IsOpen U) (hUs : U ⊆ e.val.source)
    (hclosure : closure U' ⊆ U)
    {v u : M → EReal} {q : ComplexModel (m + 1) → ℝ}
    (hq : ContDiffOn ℝ ∞ q (e.val.target ∩ e.val.symm ⁻¹' U))
    (hp : PlurisubharmonicOn (fun y => chartFunction v e y + (q y : EReal))
      (e.val.target ∩ e.val.symm ⁻¹' U))
    (hdom : ∀ y ∈ e.val.target ∩ e.val.symm ⁻¹' U,
      ∀ a : ComplexModel (m + 1), smoothDDC q y ![a, Complex.I • a] ≤
        omega.form.coeff e y ![a, Complex.I • a])
    (hu : IsHermitianPSH omega u) (hcollar : ∀ x ∈ U \ U', v x ≤ u x) :
    IsHermitianPSH omega (gluedMax U v u) :=
  isFormPSH_gluedMax_of_collar omega.form omega.isTypeOneOne hU hclosure hcollar
    (hasDominatedLocalPSHCorrections_of_chart omega.form e hU hUs hq hp hdom) hu

end SGPT.PSH.Hermitian
