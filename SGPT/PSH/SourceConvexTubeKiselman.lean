import SGPT.PSH.BookDeep2Kiselman
import SGPT.Foundations.Analysis.FirstPass.PshClosedDiscMaximum
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening
import SGPT.Foundations.Analysis.Pending.KiselmanMinimumPrincipleProof
import SGPT.Foundations.Analysis.FirstPass.HarmonicCircleApproximation
import Mathlib.Analysis.Complex.Harmonic.Analytic
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal

/-! Entire current original convex-tube-slice prop:Kis (pinned lines495--505).
Actual chosen direct proof: whole-disc real selection and one joint slack,
joint parameter-holomorphic boundary approximation, initial-only norm-square
maximum, original exhaustion continuity, exact infimum submean and source
PSH-or-identically-bottom dichotomy. All dimensions and poles are retained.
The separately proved Oka3/7 support package is NOT load-bearing and its
Oka/distance/invariant-barrier declarations are not included here. -/

/-! Genuine original pseudoconvex exhaustion produces compact bounds for
actual holomorphic disc families, with no compact-interior/output premise. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.KiselmanNext
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

theorem plurisubharmonicOn_comp_entire_disc {N : ℕ}
    {Ω : Set (ComplexModel N)} (hΩ : IsOpen Ω) {u : ComplexModel N → EReal}
    (hu : PlurisubharmonicOn u Ω) {F : ℂ → ComplexModel N} (hF : Differentiable ℂ F) :
    PlurisubharmonicOn (u ∘ F) (F ⁻¹' Ω) := by
  let e : ComplexModel 1 ≃L[ℂ] ℂ := PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => ℂ)
  have hA : IsOpen ((F ∘ e) ⁻¹' Ω) := hΩ.preimage (hF.continuous.comp e.continuous)
  have hp := Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hA
    (hF.comp e.differentiable).differentiableOn (fun z hz => hz) hu
  have hback := hp.comp_continuousLinearMap (e.symm : ℂ →L[ℂ] ComplexModel 1)
  convert hback using 1
  · funext z
    change u (F z)=u (F (e (e.symm z)))
    rw [e.apply_symm_apply]
  · ext z
    change F z∈Ω ↔ F (e (e.symm z))∈Ω
    rw [e.apply_symm_apply]

theorem holomorphic_disc_continuity_principle {N : ℕ} {T : Type*}
    [TopologicalSpace T] [PreconnectedSpace T]
    {Ω : Set (ComplexModel N)} (hΩ : BookDeep2Kiselman.IsPseudoconvex Ω)
    (F : T → ℂ → ComplexModel N) (hF : Continuous (Function.uncurry F))
    (hhol : ∀ t,Differentiable ℂ (F t)) {c : ℂ} {R : ℝ} (hR : 0<R)
    {K : Set (ComplexModel N)} (hK : IsCompact K) (hKΩ : K⊆Ω)
    (hboundary : ∀ t z,z∈sphere c R → F t z∈K)
    (t0 : T) (hstart : MapsTo (F t0) (closedBall c R) Ω) :
    ∃ L : Set (ComplexModel N),IsCompact L ∧ L⊆Ω ∧
      ∀ t z,z∈closedBall c R → F t z∈L := by
  obtain ⟨hΩopen,ρ,hρcont,hρpsh,hρexh⟩ := hΩ
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (hρcont.mono hKΩ)
  let L : Set (ComplexModel N) := {p | p∈Ω ∧ ρ p≤M}
  have hLc : IsCompact L := hρexh M
  let S : Set T := {t | MapsTo (F t) (closedBall c R) Ω}
  have hbound : ∀ t∈S,MapsTo (F t) (closedBall c R) L := by
    intro t ht
    have hp : PlurisubharmonicOn (fun z => (ρ (F t z):EReal)) ((F t) ⁻¹' Ω) :=
      plurisubharmonicOn_comp_entire_disc hΩopen hρpsh (hhol t)
    have hmax := hp.le_const_on_closedBall_of_le_on_sphere hR ht
      (fun z hz => EReal.coe_le_coe_iff.mpr
        ((le_abs_self (ρ (F t z))).trans (by simpa only [Real.norm_eq_abs] using hM _ (hboundary t z hz))))
    intro z hz
    exact ⟨ht hz,EReal.coe_le_coe_iff.mp (hmax z hz)⟩
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hprod : ({t}:Set T) ×ˢ closedBall c R⊆(Function.uncurry F) ⁻¹' Ω := by
      rintro ⟨s,z⟩ ⟨hs,hz⟩
      have hst : s=t := mem_singleton_iff.mp hs
      subst s
      exact ht hz
    obtain ⟨V,W,hV,-,htV,hDW,hVW⟩ := generalized_tube_lemma isCompact_singleton
      (isCompact_closedBall c R) (hΩopen.preimage hF) hprod
    exact mem_of_superset (hV.mem_nhds (htV (mem_singleton t)))
      (fun s hs z hz => hVW (show (s,z)∈V ×ˢ W from ⟨hs,hDW hz⟩))
  have hSeq : S=⋂ z : ↥(closedBall c R),(fun t => F t z.val) ⁻¹' L := by
    ext t
    constructor
    · intro ht
      exact mem_iInter.mpr (fun z => hbound t ht z.property)
    · intro ht z hz
      exact (mem_iInter.mp ht ⟨z,hz⟩).1
  have hSclosed : IsClosed S := by
    rw [hSeq]
    exact isClosed_iInter (fun z => hLc.isClosed.preimage
      (hF.comp (continuous_id.prodMk continuous_const)))
  have hall : (univ:Set T)⊆S := isPreconnected_univ.subset_of_closure_inter_subset hSopen
    ⟨t0,mem_univ t0,hstart⟩ (fun t ht => hSclosed.closure_eq ▸ ht.1)
  exact ⟨L,hLc,fun p hp => hp.1,fun t z hz => hbound t (hall (mem_univ t)) hz⟩

end SGPT.PSH.KiselmanNext


set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.KiselmanNext
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

theorem pseudoconvex_preimage_linearEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F) {Ω : Set F} (hΩ : BookDeep2Kiselman.IsPseudoconvex Ω) :
    BookDeep2Kiselman.IsPseudoconvex (e ⁻¹' Ω) := by
  obtain ⟨ho,ρ,hc,hp,hk⟩ := hΩ
  refine ⟨ho.preimage e.continuous,ρ ∘ e,
    hc.comp e.continuous.continuousOn (fun p hp => hp),
    hp.comp_continuousLinearMap (e:E →L[ℂ] F),?_⟩
  intro C
  have heq : {p | p∈e ⁻¹' Ω ∧ (ρ ∘ e) p≤C}=e.symm '' {q | q∈Ω ∧ ρ q≤C} := by
    ext p
    constructor
    · intro hp
      exact ⟨e p,hp,e.symm_apply_apply p⟩
    · rintro ⟨q,hq,rfl⟩
      change e (e.symm q)∈Ω ∧ ρ (e (e.symm q))≤C
      rw [e.apply_symm_apply]
      exact hq
  rw [heq]
  exact (hk C).image e.symm.continuous

abbrev productCoordinate (m n : ℕ) :
    (ComplexModel m × ComplexModel n) ≃L[ℂ] ComplexModel (m+n) :=
  (EuclideanSpace.finAddEquivProd (𝕜:=ℂ) (n:=m) (m:=n)).symm


end SGPT.PSH.KiselmanNext


/-! Actual real-fibre projection and PSH norm square, with genuine original
product geometry and no product/Euclidean norm identification. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.KiselmanNext
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

def tubeRealProjection (m n : ℕ) :
    (ComplexModel m × ComplexModel n) →ₗ[ℝ] (ComplexModel m × ComplexModel n) where
  toFun p := (p.1,WithLp.toLp 2 (fun k : Fin n => ((p.2 k).re:ℂ)))
  map_add' p q := by
    apply Prod.ext
    · rfl
    · ext k
      change (((p.2 k+q.2 k).re:ℝ):ℂ)=((p.2 k).re:ℂ)+((q.2 k).re:ℂ)
      simp
  map_smul' t p := by
    apply Prod.ext
    · rfl
    · ext k
      change (((t • p.2 k).re:ℝ):ℂ)=t • ((p.2 k).re:ℂ)
      simp [Complex.mul_re]

theorem continuous_tubeRealProjection (m n : ℕ) : Continuous (tubeRealProjection m n) := by
  exact continuous_fst.prodMk ((PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
    (continuous_pi (fun k => Complex.continuous_ofReal.comp (Complex.continuous_re.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) k).comp continuous_snd)))))

def tubeRealNormSquare {m n : ℕ} (p : ComplexModel m × ComplexModel n) : ℝ :=
  ‖tubeRealProjection m n p‖^2

theorem continuous_tubeRealNormSquare (m n : ℕ) :
    Continuous (@tubeRealNormSquare m n) := (continuous_tubeRealProjection m n).norm.pow 2

theorem convexOn_tubeRealNormSquare (m n : ℕ) :
    ConvexOn ℝ univ (@tubeRealNormSquare m n) := by
  have hc : ConvexOn ℝ (univ:Set (ComplexModel m × ComplexModel n)) (fun p => ‖p‖^2) :=
    (convexOn_norm convex_univ).pow (fun p hp => norm_nonneg p) 2
  refine ⟨convex_univ,?_⟩
  intro p hp q hq a b ha hb hab
  change ‖tubeRealProjection m n (a • p+b • q)‖^2≤
    a • ‖tubeRealProjection m n p‖^2+b • ‖tubeRealProjection m n q‖^2
  rw [map_add,map_smul,map_smul]
  exact hc.2 (mem_univ _) (mem_univ _) ha hb hab

theorem plurisubharmonicOn_tubeRealNormSquare (m n : ℕ) :
    PlurisubharmonicOn (fun p : ComplexModel m × ComplexModel n => (tubeRealNormSquare p:EReal)) univ := by
  let e := productCoordinate m n
  have hc : ConvexOn ℝ univ (fun p : ComplexModel (m+n) => tubeRealNormSquare (e.symm p)) := by
    refine ⟨convex_univ,?_⟩
    intro p hp q hq a b ha hb hab
    have heq : e.symm (a • p+b • q)=a • e.symm p+b • e.symm q := by
      rw [e.symm.map_add]
      congr 1
    change tubeRealNormSquare (e.symm (a • p+b • q))≤
      a • tubeRealNormSquare (e.symm p)+b • tubeRealNormSquare (e.symm q)
    rw [heq]
    exact (convexOn_tubeRealNormSquare m n).2 (mem_univ _) (mem_univ _) ha hb hab
  have hcont := (continuous_tubeRealNormSquare m n).comp e.symm.continuous
  have hp := Pending.plurisubharmonicOn_of_convexOn isOpen_univ
    hc hcont.continuousOn
  have hback := hp.comp_continuousLinearMap
    (e:(ComplexModel m × ComplexModel n) →L[ℂ] ComplexModel (m+n))
  convert hback using 1
  · funext p
    change (tubeRealNormSquare p:EReal)=(tubeRealNormSquare (e.symm (e p)):EReal)
    rw [e.symm_apply_apply]
  · exact (preimage_univ).symm


end SGPT.PSH.KiselmanNext


/-! Genuine jointly continuous parameter family of entire holomorphic real
boundary approximations, from actual continuous data on a compact parameter
space times the circle. No harmonic/holomorphic output data is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.KiselmanNext
open Set Filter Metric InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

theorem exists_continuous_holomorphic_real_boundary_approx
    {T : Type*} [MetricSpace T] [CompactSpace T] [Nonempty T]
    {c : ℂ} {R : ℝ} (hR : 0<R)
    (g : T × ↥(sphere c R) → ℝ) (hg : Continuous g) {ε : ℝ} (hε : 0<ε) :
    ∃ H : T → ℂ → ℂ,Continuous (Function.uncurry H) ∧
      (∀ t,Differentiable ℂ (H t)) ∧
      ∀ (t : T) (z : ↥(sphere c R)),|(H t z.val).re-g (t,z)|<ε := by
  classical
  let S := ↥(sphere c R)
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere c R)
  have hex : ∀ t : T,∃ H : ℂ → ℂ,Differentiable ℂ H ∧
      ∀ z : S,|(H z.val).re-g (t,z)|<ε/2 := by
    intro t
    let f : ℂ → ℝ := fun z => if hz : z∈sphere c R then g (t,⟨z,hz⟩) else 0
    have hf : ContinuousOn f (sphere c R) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have heq : (fun z : S => f z.val)=(fun z : S => g (t,z)) := by
        funext z
        simp only [f,dif_pos z.property]
        exact congrArg (fun q : S => g (t,q)) (Subtype.ext (by rfl))
      change Continuous (fun z : S => f z.val)
      rw [heq]
      exact hg.comp (continuous_const.prodMk continuous_id)
    obtain ⟨h,hh,happ⟩ := exists_global_harmonic_uniformApproxOn_sphere c hR hf (ε:=ε/2)
      (div_pos hε (by norm_num))
    obtain ⟨H,hHa,hHr⟩ := hh.exists_analyticOnNhd_univ_re_eq
    refine ⟨H,(fun z => (hHa z (mem_univ z)).differentiableAt),?_⟩
    intro z
    have hreal : (H z.val).re=h z.val := congrFun hHr z.val
    simpa only [hreal,f,dif_pos z.property] using happ z.val z.property
  choose A hA hApprox using hex
  have hnear : ∀ s : T,∃ V : Set T,IsOpen V ∧ s∈V ∧
      ∀ t∈V,∀ z : S,|(A s z.val).re-g (t,z)|<ε := by
    intro s
    let O : Set (T × S) := {p | |(A s p.2.val).re-g p|<ε}
    have hO : IsOpen O := isOpen_lt
      (((Complex.continuous_re.comp ((hA s).continuous.comp
        (continuous_subtype_val.comp continuous_snd))).sub hg).abs) continuous_const
    have hprod : ({s}:Set T) ×ˢ (univ:Set S)⊆O := by
      rintro ⟨t,z⟩ ⟨ht,-⟩
      have hts : t=s := mem_singleton_iff.mp ht
      subst t
      exact (hApprox s z).trans (by linarith)
    obtain ⟨V,W,hV,-,hsV,hUW,hVW⟩ := generalized_tube_lemma isCompact_singleton
      isCompact_univ hO hprod
    exact ⟨V,hV,hsV (mem_singleton s),fun t ht z => hVW (show (t,z)∈V ×ˢ W from
      ⟨ht,hUW (mem_univ z)⟩)⟩
  choose V hVo hsV hGood using hnear
  have hcover : (univ:Set T)⊆⋃ s,V s := fun t _ => mem_iUnion.mpr ⟨t,hsV t⟩
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover V hVo hcover
  let d : T → T → ℝ := fun s t => if (V s)ᶜ.Nonempty then infDist t (V s)ᶜ else 1
  have hdcont : ∀ s,Continuous (d s) := by
    intro s
    by_cases hc : (V s)ᶜ.Nonempty
    · simpa only [d,if_pos hc] using continuous_infDist_pt (V s)ᶜ
    · simpa only [d,if_neg hc] using (continuous_const : Continuous (fun _ : T => (1:ℝ)))
  have hdnonneg : ∀ s t,0≤d s t := by
    intro s t
    by_cases hc : (V s)ᶜ.Nonempty
    · simp only [d,if_pos hc]
      exact infDist_nonneg
    · simp only [d,if_neg hc]
      norm_num
  have hdpos : ∀ s t,t∈V s ↔ 0<d s t := by
    intro s t
    by_cases hc : (V s)ᶜ.Nonempty
    · simp only [d,if_pos hc]
      have h := (hVo s).isClosed_compl.notMem_iff_infDist_pos (x:=t) hc
      simpa only [mem_compl_iff,not_not] using h
    · have ht : t∈V s := by
        by_contra ht
        exact hc ⟨t,ht⟩
      simp only [d,if_neg hc,ht,zero_lt_one]
  let D : T → ℝ := fun t => ∑ s∈I,d s t
  have hDcont : Continuous D := continuous_finsetSum I (fun s _ => hdcont s)
  have hDpos : ∀ t,0<D t := by
    intro t
    obtain ⟨s,hsI,hts⟩ := mem_iUnion₂.mp (hI (mem_univ t))
    exact Finset.sum_pos' (fun s _ => hdnonneg s t) ⟨s,hsI,(hdpos s t).mp hts⟩
  let α : T → T → ℝ := fun s t => d s t/D t
  have hαcont : ∀ s,Continuous (α s) := fun s =>
    (hdcont s).div hDcont (fun t => (hDpos t).ne')
  let H : T → ℂ → ℂ := fun t z => ∑ s∈I,(α s t:ℂ)*A s z
  have hHcont : Continuous (Function.uncurry H) := continuous_finsetSum I (fun s _ =>
    ((Complex.continuous_ofReal.comp ((hαcont s).comp continuous_fst)).mul
      ((hA s).continuous.comp continuous_snd)))
  have hHhol : ∀ t,Differentiable ℂ (H t) := fun t =>
    Differentiable.fun_sum (fun s hs => (hA s).const_mul (α s t:ℂ))
  refine ⟨H,hHcont,hHhol,?_⟩
  intro t z
  have hsupp : ∀ s∈I,α s t≠0 → 0<d s t := by
    intro s hs hn
    refine lt_of_le_of_ne (hdnonneg s t) (fun hz => hn ?_)
    simp only [α,← hz,zero_div]
  have hsum : ∑ s∈I.filter (fun s => 0<d s t),α s t=1 := by
    rw [Finset.sum_filter_of_ne hsupp]
    simp only [α,← Finset.sum_div,D,div_self (hDpos t).ne']
  have hvalues : ∀ s∈I.filter (fun s => 0<d s t),
      (A s z.val).re∈Ioo (g (t,z)-ε) (g (t,z)+ε) := by
    intro s hs
    have ht : t∈V s := (hdpos s t).mpr (Finset.mem_filter.mp hs).2
    have hb := abs_lt.mp (hGood s t ht z)
    constructor <;> linarith
  have hcomb := (convex_Ioo (g (t,z)-ε) (g (t,z)+ε)).sum_mem
    (fun s hs => div_nonneg (hdnonneg s t) (hDpos t).le) hsum hvalues
  have hreal : (H t z.val).re=
      ∑ s∈I.filter (fun s => 0<d s t),α s t • (A s z.val).re := by
    rw [Finset.sum_filter_of_ne]
    · simp only [H,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero,smul_eq_mul]
    · intro s hs hn
      exact hsupp s hs (fun hz => hn (by rw [hz,zero_smul]))
  rw [← hreal] at hcomb
  exact abs_lt.mpr ⟨by linarith [hcomb.1],by linarith [hcomb.2]⟩

end SGPT.PSH.KiselmanNext


/-! Actual whole-disc convex real-fibre selection with one common positive
slack for the entire original domain and the original boundary obstacle. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.KiselmanNext
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

theorem exists_whole_disc_convex_selector_with_uniform_slack
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : ℂ} {R : ℝ} (hR : 0<R) {V G : Set (ℂ × F)} (hVo : IsOpen V) (hGo : IsOpen G)
    (hGV : G⊆V)
    (hVne : ∀ z∈closedBall c R,∃ t : F,(z,t)∈V)
    (hGne : ∀ z∈sphere c R,∃ t : F,(z,t)∈G)
    (hVc : ∀ z∈closedBall c R,Convex ℝ {t : F | (z,t)∈V})
    (hGc : ∀ z∈sphere c R,Convex ℝ {t : F | (z,t)∈G}) :
    ∃ w : ℂ → F,ContinuousOn w (closedBall c R) ∧
      (∀ z∈closedBall c R,(z,w z)∈V) ∧ (∀ z∈sphere c R,(z,w z)∈G) ∧
      ∃ ε : ℝ,0<ε ∧
        (∀ z∈closedBall c R,∀ t : F,‖t-w z‖<ε → (z,t)∈V) ∧
        (∀ z∈sphere c R,∀ t : F,‖t-w z‖<ε → (z,t)∈G) := by
  classical
  let K := ↥(closedBall c R)
  have hex : ∀ z : K,∃ t : F,(z.val,t)∈V ∧ (z.val∈sphere c R → (z.val,t)∈G) := by
    intro z
    by_cases hz : z.val∈sphere c R
    · obtain ⟨t,ht⟩ := hGne z.val hz
      exact ⟨t,hGV ht,fun _ => ht⟩
    · obtain ⟨t,ht⟩ := hVne z.val z.property
      exact ⟨t,ht,fun h => (hz h).elim⟩
  choose b hbV hbG using hex
  let O : K → Set ℂ := fun i => ball c (R+1)∩
    if i.val∈sphere c R then {z | (z,b i)∈G}
    else {z | (z,b i)∈V}∩(sphere c R)ᶜ
  have hOo : ∀ i,IsOpen (O i) := by
    intro i
    by_cases hi : i.val∈sphere c R
    · dsimp only [O]
      rw [if_pos hi]
      change IsOpen (ball c (R+1)∩(fun z : ℂ => (z,b i)) ⁻¹' G)
      exact isOpen_ball.inter (hGo.preimage (continuous_id.prodMk continuous_const))
    · dsimp only [O]
      rw [if_neg hi]
      change IsOpen (ball c (R+1)∩((fun z : ℂ => (z,b i)) ⁻¹' V∩(sphere c R)ᶜ))
      exact isOpen_ball.inter ((hVo.preimage (continuous_id.prodMk continuous_const)).inter
        isClosed_sphere.isOpen_compl)
  have hself : ∀ i : K,i.val∈O i := by
    intro i
    have hb : i.val∈ball c (R+1) := (mem_closedBall.mp i.property).trans_lt (lt_add_one R)
    by_cases hi : i.val∈sphere c R
    · refine ⟨hb,?_⟩
      rw [if_pos hi]
      change (i.val,b i)∈G
      exact hbG i hi
    · refine ⟨hb,?_⟩
      rw [if_neg hi]
      change (i.val,b i)∈V ∧ i.val∉sphere c R
      exact ⟨hbV i,hi⟩
  have hcover : closedBall c R⊆⋃ i,O i := fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hself ⟨z,hz⟩⟩
  obtain ⟨I,hI⟩ := (isCompact_closedBall c R).elim_finite_subcover O hOo hcover
  let d : K → ℂ → ℝ := fun i z => infDist z (O i)ᶜ
  have hfar : ∀ i : K,c+((R+1:ℝ):ℂ)∈(O i)ᶜ := by
    intro i hi
    have h := hi.1
    rw [mem_ball,dist_self_add_left,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by linarith : (0:ℝ)<R+1)] at h
    exact lt_irrefl _ h
  have hdpos : ∀ i z,z∈O i ↔ 0<d i z := by
    intro i z
    have h := (hOo i).isClosed_compl.notMem_iff_infDist_pos (x:=z) ⟨_,hfar i⟩
    simpa only [mem_compl_iff,not_not] using h
  have hdnonneg : ∀ i z,0≤d i z := fun i z => infDist_nonneg
  have hdcont : ∀ i,Continuous (d i) := fun i => continuous_infDist_pt _
  let D : ℂ → ℝ := fun z => ∑ i∈I,d i z
  have hDcont : Continuous D := continuous_finsetSum I (fun i _ => hdcont i)
  have hDpos : ∀ z∈closedBall c R,0<D z := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hI hz)
    exact Finset.sum_pos' (fun i _ => hdnonneg i z) ⟨i,hi,(hdpos i z).mp hzi⟩
  let α : K → ℂ → ℝ := fun i z => d i z/D z
  have hα : ∀ i,ContinuousOn (α i) (closedBall c R) := fun i =>
    (hdcont i).continuousOn.div hDcont.continuousOn (fun z hz => (hDpos z hz).ne')
  let w : ℂ → F := fun z => ∑ i∈I,α i z • b i
  have hwcont : ContinuousOn w (closedBall c R) :=
    continuousOn_finsetSum I (fun i _ => (hα i).smul continuousOn_const)
  have hcombine : ∀ z∈closedBall c R,∀ A : Set F,Convex ℝ A →
      (∀ i∈I,z∈O i → b i∈A) → w z∈A := by
    intro z hz A hA hval
    have hsupp : ∀ i∈I,α i z≠0 → 0<d i z := by
      intro i hi hn
      refine lt_of_le_of_ne (hdnonneg i z) (fun h => hn ?_)
      simp only [α,← h,zero_div]
    have hsum : ∑ i∈I.filter (fun i => 0<d i z),α i z=1 := by
      rw [Finset.sum_filter_of_ne hsupp]
      simp only [α,← Finset.sum_div,D,div_self (hDpos z hz).ne']
    have heq : w z=∑ i∈I.filter (fun i => 0<d i z),α i z • b i := by
      rw [Finset.sum_filter_of_ne]
      intro i hi hn
      exact hsupp i hi (fun h => hn (by rw [h,zero_smul]))
    rw [heq]
    exact hA.sum_mem (fun i _ => div_nonneg (hdnonneg i z) (hDpos z hz).le) hsum
      (fun i hi => hval i (Finset.mem_filter.mp hi).1 ((hdpos i z).mpr (Finset.mem_filter.mp hi).2))
  have hwV : ∀ z∈closedBall c R,(z,w z)∈V := by
    intro z hz
    apply hcombine z hz {t : F | (z,t)∈V} (hVc z hz)
    intro i hi hzi
    have h : z∈if i.val∈sphere c R then {y | (y,b i)∈G}
        else {y | (y,b i)∈V}∩(sphere c R)ᶜ := hzi.2
    by_cases hs : i.val∈sphere c R
    · rw [if_pos hs] at h
      exact hGV h
    · rw [if_neg hs] at h
      exact h.1
  have hwG : ∀ z∈sphere c R,(z,w z)∈G := by
    intro z hz
    apply hcombine z (sphere_subset_closedBall hz) {t : F | (z,t)∈G} (hGc z hz)
    intro i hi hzi
    have h : z∈if i.val∈sphere c R then {y | (y,b i)∈G}
        else {y | (y,b i)∈V}∩(sphere c R)ᶜ := hzi.2
    by_cases hs : i.val∈sphere c R
    · rwa [if_pos hs] at h
    · rw [if_neg hs] at h
      exact (h.2 hz).elim
  let ΓV := (fun z => (z,w z)) '' closedBall c R
  let ΓG := (fun z => (z,w z)) '' sphere c R
  have hΓV : IsCompact ΓV := (isCompact_closedBall c R).image_of_continuousOn
    (continuousOn_id.prodMk hwcont)
  have hΓG : IsCompact ΓG := (isCompact_sphere c R).image_of_continuousOn
    (continuousOn_id.prodMk (hwcont.mono sphere_subset_closedBall))
  have hΓVV : ΓV⊆V := by rintro p ⟨z,hz,rfl⟩; exact hwV z hz
  have hΓGG : ΓG⊆G := by rintro p ⟨z,hz,rfl⟩; exact hwG z hz
  obtain ⟨δV,hδV,hthickV⟩ := hΓV.exists_thickening_subset_open hVo hΓVV
  obtain ⟨δG,hδG,hthickG⟩ := hΓG.exists_thickening_subset_open hGo hΓGG
  refine ⟨w,hwcont,hwV,hwG,min δV δG,lt_min hδV hδG,?_,?_⟩
  · intro z hz t ht
    apply hthickV
    rw [mem_thickening_iff]
    refine ⟨(z,w z),⟨z,hz,rfl⟩,?_⟩
    rw [Prod.dist_eq,dist_self,dist_eq_norm]
    exact max_lt hδV (ht.trans_le (min_le_left _ _))
  · intro z hz t ht
    apply hthickG
    rw [mem_thickening_iff]
    refine ⟨(z,w z),⟨z,hz,rfl⟩,?_⟩
    rw [Prod.dist_eq,dist_self,dist_eq_norm]
    exact max_lt hδG (ht.trans_le (min_le_right _ _))

end SGPT.PSH.KiselmanNext


/-! Actual vector-valued parameter-holomorphic boundary approximations,
including finite norm control and the whole initial-disc real-part bound. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.KiselmanNext
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

def fibreRealVector {n : ℕ} (w : ComplexModel n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => (w k).re)

theorem continuous_fibreRealVector (n : ℕ) : Continuous (@fibreRealVector n) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    (continuous_pi (fun k => Complex.continuous_re.comp (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) k)))

def realFibreEmbedding {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) : ComplexModel n :=
  WithLp.toLp 2 (fun k => (w k:ℂ))

theorem fibreRealVector_realFibreEmbedding {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    fibreRealVector (realFibreEmbedding w)=w := by ext k; rfl

theorem exists_continuous_holomorphic_real_vector_boundary_approx
    {T : Type*} [MetricSpace T] [CompactSpace T] [Nonempty T] {n : ℕ}
    {c : ℂ} {R : ℝ} (hR : 0<R)
    (g : T × ↥(sphere c R) → EuclideanSpace ℝ (Fin n)) (hg : Continuous g)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ H : T → ℂ → ComplexModel n,Continuous (Function.uncurry H) ∧
      (∀ t,Differentiable ℂ (H t)) ∧
      ∀ (t : T) (z : ↥(sphere c R)),‖fibreRealVector (H t z.val)-g (t,z)‖<δ := by
  let eR : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let C : ℝ := ‖eR.symm.toContinuousLinearMap‖
  have hC : 0≤C := norm_nonneg _
  let ε : ℝ := δ/(C+1)
  have hε : 0<ε := div_pos hδ (by linarith)
  have hεC : C*ε<δ := by
    dsimp only [ε]
    rw [← mul_div_assoc,div_lt_iff₀ (by linarith : (0:ℝ)<C+1)]
    nlinarith
  have hex : ∀ k : Fin n,∃ A : T → ℂ → ℂ,Continuous (Function.uncurry A) ∧
      (∀ t,Differentiable ℂ (A t)) ∧
      ∀ (t : T) (z : ↥(sphere c R)),|(A t z.val).re-(g (t,z)) k|<ε := by
    intro k
    exact exists_continuous_holomorphic_real_boundary_approx hR (fun p => g p k)
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) k).comp hg) hε
  choose A hAcont hAhol hApprox using hex
  let eC : ComplexModel n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let H : T → ℂ → ComplexModel n := fun t z => eC.symm (fun k => A k t z)
  have hHcont : Continuous (Function.uncurry H) := eC.symm.continuous.comp
    (continuous_pi (fun k => hAcont k))
  have hHhol : ∀ t,Differentiable ℂ (H t) := fun t => eC.symm.differentiable.comp
    (differentiable_pi.mpr (fun k => hAhol k t))
  refine ⟨H,hHcont,hHhol,?_⟩
  intro t z
  let err : Fin n → ℝ := fun k => (A k t z.val).re-(g (t,z)) k
  have herr : ‖err‖<ε := (pi_norm_lt_iff hε).mpr
    (fun k => by simpa only [Real.norm_eq_abs] using hApprox k t z)
  have heq : fibreRealVector (H t z.val)-g (t,z)=eR.symm err := by
    ext k
    rfl
  rw [heq]
  calc
    ‖eR.symm err‖≤C*‖err‖ := eR.symm.toContinuousLinearMap.le_opNorm err
    _≤C*ε := mul_le_mul_of_nonneg_left herr.le hC
    _<δ := hεC

theorem realFibreNormSquare_eq_tubeRealNormSquare {n : ℕ} (w : ComplexModel n)
    (a : EuclideanSpace ℝ (Fin n)) :
    ‖fibreRealVector w-a‖^2=tubeRealNormSquare ((0:ComplexModel 0),w-realFibreEmbedding a) := by
  change ‖fibreRealVector w-a‖^2=
    ‖((0:ComplexModel 0),WithLp.toLp 2 (fun k : Fin n => (((w k)-(a k:ℂ)).re:ℂ)))‖^2
  rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro k hk
  change ‖(w k).re-a k‖^2=‖((((w k)-(a k:ℂ)).re:ℝ):ℂ)‖^2
  rw [Complex.norm_real,Complex.sub_re,Complex.ofReal_re]

theorem plurisubharmonicOn_realFibreNormSquare {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) :
    PlurisubharmonicOn (fun w : ComplexModel n => ((‖fibreRealVector w-a‖^2:ℝ):EReal)) univ := by
  let L : ComplexModel n →L[ℂ] ComplexModel 0 × ComplexModel n := ContinuousLinearMap.inr ℂ _ _
  have hp := (plurisubharmonicOn_tubeRealNormSquare 0 n).comp_affine L
    ((0:ComplexModel 0),-realFibreEmbedding a)
  convert hp using 1
  · funext w
    change ((‖fibreRealVector w-a‖^2:ℝ):EReal)=
      (tubeRealNormSquare (((0:ComplexModel 0),-realFibreEmbedding a)+L w):EReal)
    have heq : ((0:ComplexModel 0),-realFibreEmbedding a)+L w=(0,w-realFibreEmbedding a) := by
      simp [L,sub_eq_add_neg,add_comm]
    rw [heq,← realFibreNormSquare_eq_tubeRealNormSquare]
  · exact (preimage_univ).symm

theorem holomorphic_real_boundary_norm_bound {n : ℕ}
    {H : ℂ → ComplexModel n} (hH : Differentiable ℂ H)
    (a : EuclideanSpace ℝ (Fin n)) {c : ℂ} {R M : ℝ} (hR : 0<R) (hM : 0≤M)
    (hbound : ∀ z∈sphere c R,‖fibreRealVector (H z)-a‖≤M) :
    ∀ z∈closedBall c R,‖fibreRealVector (H z)-a‖≤M := by
  have hp := plurisubharmonicOn_comp_entire_disc isOpen_univ
    (plurisubharmonicOn_realFibreNormSquare a) hH
  have hD : closedBall c R⊆H ⁻¹' (univ:Set (ComplexModel n)) := fun z hz => mem_univ _
  have hb : ∀ z∈sphere c R,((‖fibreRealVector (H z)-a‖^2:ℝ):EReal)≤((M^2:ℝ):EReal) := by
    intro z hz
    apply EReal.coe_le_coe_iff.mpr
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound z hz) 2
  intro z hz
  have hm := hp.le_const_on_closedBall_of_le_on_sphere hR hD hb z hz
  have hm' : ‖fibreRealVector (H z)-a‖^2≤M^2 := EReal.coe_le_coe_iff.mp hm
  nlinarith [norm_nonneg (fibreRealVector (H z)-a)]

end SGPT.PSH.KiselmanNext


/-! Genuine original variable-tube strict-sublevel convexity. Possible poles
are retained; no finite-value or infimum-PSH output is an input. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.KiselmanNext
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

theorem plurisubharmonicOn_comp_entire_product_disc {m n : ℕ}
    {Ω : Set (ComplexModel m × ComplexModel n)} (hΩ : IsOpen Ω)
    {u : ComplexModel m × ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω)
    {F : ℂ → ComplexModel m × ComplexModel n} (hF : Differentiable ℂ F) :
    PlurisubharmonicOn (u ∘ F) (F ⁻¹' Ω) := by
  let e := productCoordinate m n
  have hp := hu.comp_continuousLinearMap
    (e.symm:ComplexModel (m+n) →L[ℂ] (ComplexModel m × ComplexModel n))
  have hOpen : IsOpen (e.symm ⁻¹' Ω) := hΩ.preimage e.symm.continuous
  have hdisc := plurisubharmonicOn_comp_entire_disc hOpen hp (e.differentiable.comp hF)
  convert hdisc using 1
  · funext z
    change u (F z)=u (e.symm (e (F z)))
    rw [e.symm_apply_apply]
  · ext z
    change F z∈Ω ↔ e.symm (e (F z))∈Ω
    rw [e.symm_apply_apply]

theorem real_invariant_slice_lt_of_between
    {v : ℝ → EReal} {I : Set ℝ}
    (hu : PlurisubharmonicOn (fun z : ℂ => v z.re) (Complex.re ⁻¹' I))
    {a b t : ℝ} (habI : Icc a b⊆I) (hat : a≤t) (htb : t≤b) {C : EReal}
    (hCa : v a<C) (hCb : v b<C) : v t<C := by
  rcases eq_or_lt_of_le hat with rfl | hat'
  · exact hCa
  rcases eq_or_lt_of_le htb with rfl | htb'
  · exact hCb
  by_contra hnot
  have hCt : C≤v t := not_lt.mp hnot
  have husc : UpperSemicontinuousOn v (Icc a b) := by
    have hmap : MapsTo (fun s : ℝ => (s:ℂ)) (Icc a b) (Complex.re ⁻¹' I) :=
      fun s hs => by simpa only [mem_preimage,Complex.ofReal_re] using habI hs
    simpa only [Function.comp_def,Complex.ofReal_re] using
      hu.upperSemicontinuousOn.comp Complex.continuous_ofReal.continuousOn hmap
  obtain ⟨x,hx,hmax⟩ := husc.exists_isMaxOn ⟨a,left_mem_Icc.mpr (hat'.trans htb').le⟩ isCompact_Icc
  have htx : v t≤v x := hmax ⟨hat'.le,htb'.le⟩
  have hxtop : v x≠⊤ := by
    have h := (hu (x:ℂ) (by simpa only [mem_preimage,Complex.ofReal_re] using habI hx)).ne_top
    simpa only [Complex.ofReal_re] using h
  have hCx : C≤v x := hCt.trans htx
  have hax : v a<v x := hCa.trans_le hCx
  have hbx : v b<v x := hCb.trans_le hCx
  have hxbot : v x≠⊥ := ne_bot_of_gt hax
  have hxI : x∈Ioo a b := by
    constructor
    · apply lt_of_le_of_ne hx.1
      intro h
      have h' : x=a := h.symm
      rw [h'] at hax
      exact lt_irrefl _ hax
    · apply lt_of_le_of_ne hx.2
      intro h
      rw [h] at hbx
      exact lt_irrefl _ hbx
  have hxeq : v x=(((v x).toReal:ℝ):EReal) := (EReal.coe_toReal hxtop hxbot).symm
  exact hu.comp_re_no_finite_strict_interior_max habI hxI
    (fun y hy => (hmax hy).trans hxeq.le) hxeq (hax.trans_eq hxeq) (hbx.trans_eq hxeq)

theorem tube_mem_iff_of_re_eq {m n : ℕ} {Ω : Set (ComplexModel m × ComplexModel n)}
    (htube : ∀ z,∃ E : Set (Fin n → ℝ),BookDeep2Kiselman.slice Ω z={w | (fun k => (w k).re)∈E})
    (z : ComplexModel m) (w w' : ComplexModel n) (heq : ∀ k,(w k).re=(w' k).re) :
    (z,w)∈Ω ↔ (z,w')∈Ω := by
  obtain ⟨E,hE⟩ := htube z
  change w∈BookDeep2Kiselman.slice Ω z ↔ w'∈BookDeep2Kiselman.slice Ω z
  rw [hE]
  change (fun k => (w k).re)∈E ↔ (fun k => (w' k).re)∈E
  rw [funext heq]

theorem convex_original_real_fibre {m n : ℕ} {Ω : Set (ComplexModel m × ComplexModel n)}
    (htube : ∀ z,∃ E : Set (Fin n → ℝ),Convex ℝ E ∧
      BookDeep2Kiselman.slice Ω z={w | (fun k => (w k).re)∈E}) (z : ComplexModel m) :
    Convex ℝ {t : EuclideanSpace ℝ (Fin n) | (z,realFibreEmbedding t)∈Ω} := by
  obtain ⟨E,hEc,hE⟩ := htube z
  have hm : ∀ t : EuclideanSpace ℝ (Fin n),(z,realFibreEmbedding t)∈Ω ↔ (fun k => t k)∈E := by
    intro t
    change realFibreEmbedding t∈BookDeep2Kiselman.slice Ω z ↔ (fun k => t k)∈E
    rw [hE]
    rfl
  intro a ha b hb α β hα hβ hsum
  apply (hm _).mpr
  have hc := hEc ((hm a).mp ha) ((hm b).mp hb) hα hβ hsum
  exact hc

theorem convex_original_strict_fibre_sublevel {m n : ℕ}
    {Ω : Set (ComplexModel m × ComplexModel n)} (hΩ : IsOpen Ω)
    (htube : ∀ z,∃ E : Set (Fin n → ℝ),Convex ℝ E ∧
      BookDeep2Kiselman.slice Ω z={w | (fun k => (w k).re)∈E})
    {φ : ComplexModel m × ComplexModel n → EReal} (hφ : PlurisubharmonicOn φ Ω)
    (hinv : ∀ z w w',(z,w)∈Ω → (∀ k,(w k).re=(w' k).re) → φ (z,w')=φ (z,w))
    (z : ComplexModel m) (C : EReal) :
    Convex ℝ {t : EuclideanSpace ℝ (Fin n) | (z,realFibreEmbedding t)∈Ω ∧ φ (z,realFibreEmbedding t)<C} := by
  have hE := convex_original_real_fibre htube z
  have hTube : ∀ z,∃ E : Set (Fin n → ℝ),BookDeep2Kiselman.slice Ω z={w | (fun k => (w k).re)∈E} := by
    intro y
    obtain ⟨E,-,hE⟩ := htube y
    exact ⟨E,hE⟩
  intro a ha b hb α β hα hβ hsum
  refine ⟨hE ha.1 hb.1 hα hβ hsum,?_⟩
  let Z : ℂ → ComplexModel m × ComplexModel n := fun τ =>
    (z,realFibreEmbedding a+τ • (realFibreEmbedding b-realFibreEmbedding a))
  have hZ : Differentiable ℂ Z := (differentiable_const (c:=z)).prodMk
    ((differentiable_const (c:=realFibreEmbedding a)).add
      (differentiable_id.smul_const (realFibreEmbedding b-realFibreEmbedding a)))
  let I : Set ℝ := {s | (z,realFibreEmbedding (a+s • (b-a)))∈Ω}
  let v : ℝ → EReal := fun s => φ (z,realFibreEmbedding (a+s • (b-a)))
  have hre : ∀ τ : ℂ,∀ k,((Z τ).2 k).re=
      ((realFibreEmbedding (a+τ.re • (b-a))) k).re := by
    intro τ k
    change (((a k:ℂ)+τ*((b k:ℂ)-(a k:ℂ))).re)=a k+τ.re*(b k-a k)
    simp [Complex.add_re,Complex.mul_re,Complex.sub_re]
  have hdom : Z ⁻¹' Ω=Complex.re ⁻¹' I := by
    ext τ
    exact tube_mem_iff_of_re_eq hTube z _ _ (hre τ)
  have hp := plurisubharmonicOn_comp_entire_product_disc hΩ hφ hZ
  have hpReal : PlurisubharmonicOn (fun τ : ℂ => v τ.re) (Complex.re ⁻¹' I) := by
    rw [← hdom]
    intro τ hτ
    apply (hp τ hτ).congr
    filter_upwards [(hΩ.preimage hZ.continuous).mem_nhds hτ] with σ hσ
    exact (hinv z (Z σ).2 _ hσ (hre σ)).symm
  have hIcc : Icc (0:ℝ) 1⊆I := fun s hs => hE.add_smul_sub_mem ha.1 hb.1 hs
  have h0 : v 0=φ (z,realFibreEmbedding a) := by simp only [v,zero_smul,add_zero]
  have h1 : v 1=φ (z,realFibreEmbedding b) := by
    dsimp only [v]
    rw [one_smul,show a+(b-a)=b by abel]
  have hβ1 : β≤1 := by linarith
  have hlt := real_invariant_slice_lt_of_between hpReal hIcc hβ hβ1
    (by simpa only [h0] using ha.2) (by simpa only [h1] using hb.2)
  have heq : α • a+β • b=a+β • (b-a) := by
    have hαeq : α=1-β := by linarith
    rw [hαeq]
    module
  change φ (z,realFibreEmbedding (α • a+β • b))<C
  rw [heq]
  exact hlt

end SGPT.PSH.KiselmanNext


/-! Original variable convex-tube domain and original possibly polar PSH
function internally produce a whole holomorphic disc graph below each
actual strict continuous boundary majorant of the exact fibre infimum. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.KiselmanNext
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

def tubeInfimum {m n : ℕ} (Ω : Set (ComplexModel m × ComplexModel n))
    (φ : ComplexModel m × ComplexModel n → EReal) (z : ComplexModel m) : EReal :=
  ⨅ w∈BookDeep2Kiselman.slice Ω z,φ (z,w)

theorem continuous_realFibreEmbedding (n : ℕ) : Continuous (@realFibreEmbedding n) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
    (continuous_pi (fun k => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) k)))

theorem exists_original_holomorphic_graph_below_boundary_majorant {m n : ℕ}
    {Ω : Set (ComplexModel m × ComplexModel n)} (hΩ : BookDeep2Kiselman.IsPseudoconvex Ω)
    (htube : ∀ z,∃ E : Set (Fin n → ℝ),Convex ℝ E ∧
      BookDeep2Kiselman.slice Ω z={w | (fun k => (w k).re)∈E})
    {φ : ComplexModel m × ComplexModel n → EReal} (hφ : PlurisubharmonicOn φ Ω)
    (hinv : ∀ z w w',(z,w)∈Ω → (∀ k,(w k).re=(w' k).re) → φ (z,w')=φ (z,w))
    {Z : ℂ → ComplexModel m} (hZ : Differentiable ℂ Z) {c : ℂ} {R : ℝ} (hR : 0<R)
    (hbase : MapsTo Z (closedBall c R) (Prod.fst '' Ω)) {g : ℂ → ℝ} (hg : Continuous g)
    (hlt : ∀ z∈sphere c R,tubeInfimum Ω φ (Z z)<(g z:EReal)) :
    ∃ H : ℂ → ComplexModel n,Differentiable ℂ H ∧
      (∀ z∈closedBall c R,(Z z,H z)∈Ω) ∧ (∀ z∈sphere c R,φ (Z z,H z)<(g z:EReal)) := by
  classical
  let F := EuclideanSpace ℝ (Fin n)
  have hTube : ∀ z,∃ E : Set (Fin n → ℝ),BookDeep2Kiselman.slice Ω z={w | (fun k => (w k).re)∈E} := by
    intro z
    obtain ⟨E,-,hE⟩ := htube z
    exact ⟨E,hE⟩
  have hre : ∀ w : ComplexModel n,∀ k,(w k).re=((realFibreEmbedding (fibreRealVector w)) k).re := by
    intro w k
    rfl
  have hRealMem : ∀ z w,(z,w)∈Ω → (z,realFibreEmbedding (fibreRealVector w))∈Ω :=
    fun z w hw => (tube_mem_iff_of_re_eq hTube z _ _ (hre w)).mp hw
  let f : ℂ × F → ComplexModel m × ComplexModel n := fun p => (Z p.1,realFibreEmbedding p.2)
  have hf : Continuous f := (hZ.continuous.comp continuous_fst).prodMk
    ((continuous_realFibreEmbedding n).comp continuous_snd)
  let V := f ⁻¹' Ω
  let G : Set (ℂ × F) := {p | p∈V ∧ φ (f p)<(g p.1:EReal)}
  have hVo : IsOpen V := hΩ.1.preimage hf
  have hGo : IsOpen G := by
    apply Pending.KiselmanMinimumPrincipleProof.isOpen_setOf_lt_of_upperSemicontinuousAt hVo
      (fun p hp => Pending.KiselmanMinimumPrincipleProof.uscAt_comp
        (hφ (f p) hp).upperSemicontinuousAt hf.continuousAt) (hg.comp continuous_fst)
  have hVne : ∀ z∈closedBall c R,∃ t : F,(z,t)∈V := by
    intro z hz
    obtain ⟨⟨x,w⟩,hw,hx⟩ := hbase hz
    change x=Z z at hx
    subst x
    exact ⟨fibreRealVector w,hRealMem (Z z) w hw⟩
  have hGne : ∀ z∈sphere c R,∃ t : F,(z,t)∈G := by
    intro z hz
    have hp := hlt z hz
    change (⨅ w∈BookDeep2Kiselman.slice Ω (Z z),φ (Z z,w))<(g z:EReal) at hp
    obtain ⟨w,hw⟩ := iInf_lt_iff.mp hp
    obtain ⟨hwΩ,hwφ⟩ := iInf_lt_iff.mp hw
    refine ⟨fibreRealVector w,hRealMem (Z z) w hwΩ,?_⟩
    change φ (Z z,realFibreEmbedding (fibreRealVector w))<(g z:EReal)
    rw [hinv (Z z) w _ hwΩ (hre w)]
    exact hwφ
  have hVc : ∀ z∈closedBall c R,Convex ℝ {t : F | (z,t)∈V} := by
    intro z hz
    exact convex_original_real_fibre htube (Z z)
  have hGc : ∀ z∈sphere c R,Convex ℝ {t : F | (z,t)∈G} := by
    intro z hz
    exact convex_original_strict_fibre_sublevel hΩ.1 htube hφ hinv (Z z) (g z:EReal)
  obtain ⟨w,hwcont,hwV,hwG,ε,hε,hslackV,hslackG⟩ :=
    exists_whole_disc_convex_selector_with_uniform_slack hR hVo hGo (fun p hp => hp.1) hVne hGne hVc hGc
  let T := ↥(Icc (0:ℝ) 1)
  let : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  let t0 : T := ⟨0,by constructor <;> norm_num⟩
  let t1 : T := ⟨1,by constructor <;> norm_num⟩
  let : Nonempty T := ⟨t0⟩
  let radial : T → ℂ → ℂ := fun t z => c+(t.val:ℂ)*(z-c)
  have hrad : Continuous (Function.uncurry radial) := continuous_const.add
    ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_snd.sub continuous_const))
  have hradHol : ∀ t,Differentiable ℂ (radial t) := fun t =>
    (differentiable_const (c:=c)).add
      ((differentiable_id.sub (differentiable_const (c:=c))).const_mul (t.val:ℂ))
  have hradD : ∀ t z,z∈sphere c R → radial t z∈closedBall c R := by
    intro t z hz
    change dist (c+(t.val:ℂ)*(z-c)) c≤R
    rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg t.property.1]
    have hzR : ‖z-c‖=R := by simpa only [dist_eq_norm] using mem_sphere.mp hz
    rw [hzR]
    exact mul_le_of_le_one_left hR.le t.property.2
  have hrad0 : ∀ z,radial t0 z=c := by intro z; simp only [radial,t0,Complex.ofReal_zero,zero_mul,add_zero]
  have hrad1 : ∀ z,radial t1 z=z := by
    intro z
    dsimp only [radial,t1]
    rw [Complex.ofReal_one,one_mul]
    abel
  let B : T × ↥(sphere c R) → F := fun p => w (radial p.1 p.2.val)
  have hB : Continuous B := hwcont.comp_continuous
    (hrad.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    (fun p => hradD p.1 p.2.val p.2.property)
  obtain ⟨H,hHcont,hHhol,hApprox⟩ := exists_continuous_holomorphic_real_vector_boundary_approx
    hR B hB (δ:=ε/2) (div_pos hε (by norm_num))
  let P : T → ℂ → ComplexModel m × ComplexModel n := fun t z => (Z (radial t z),H t z)
  have hP : Continuous (Function.uncurry P) := (hZ.continuous.comp hrad).prodMk hHcont
  have hPhol : ∀ t,Differentiable ℂ (P t) := fun t => (hZ.comp (hradHol t)).prodMk (hHhol t)
  have hBoundary : ∀ t z,z∈sphere c R → P t z∈Ω := by
    intro t z hz
    have hsmall : ‖fibreRealVector (H t z)-w (radial t z)‖<ε :=
      (hApprox t ⟨z,hz⟩).trans (by linarith)
    have hr := hslackV (radial t z) (hradD t z hz) _ hsmall
    exact (tube_mem_iff_of_re_eq hTube (Z (radial t z)) _ _ (hre (H t z))).mpr hr
  have hInitialBound : ∀ z∈sphere c R,‖fibreRealVector (H t0 z)-w c‖≤ε/2 := by
    intro z hz
    have h := (hApprox t0 ⟨z,hz⟩).le
    change ‖fibreRealVector (H t0 z)-w (radial t0 z)‖≤ε/2 at h
    rwa [hrad0] at h
  have hInitialNorm := holomorphic_real_boundary_norm_bound (hHhol t0) (w c) hR
    (div_nonneg hε.le (by norm_num)) hInitialBound
  have hInitial : MapsTo (P t0) (closedBall c R) Ω := by
    intro z hz
    have hsmall : ‖fibreRealVector (H t0 z)-w c‖<ε := (hInitialNorm z hz).trans_lt (by linarith)
    have hr := hslackV c (mem_closedBall_self hR.le) _ hsmall
    have hm := (tube_mem_iff_of_re_eq hTube (Z c) _ _ (hre (H t0 z))).mpr hr
    change (Z (radial t0 z),H t0 z)∈Ω
    rwa [hrad0]
  let e := productCoordinate m n
  let O := e.symm ⁻¹' Ω
  have hO := pseudoconvex_preimage_linearEquiv e.symm hΩ
  let Q : T → ℂ → ComplexModel (m+n) := fun t z => e (P t z)
  have hQ : Continuous (Function.uncurry Q) := e.continuous.comp hP
  have hQhol : ∀ t,Differentiable ℂ (Q t) := fun t => e.differentiable.comp (hPhol t)
  let K := (Function.uncurry Q) '' ((univ:Set T) ×ˢ sphere c R)
  have hK : IsCompact K := (isCompact_univ.prod (isCompact_sphere c R)).image hQ
  have hKO : K⊆O := by
    rintro p ⟨⟨t,z⟩,⟨-,hz⟩,rfl⟩
    change e.symm (e (P t z))∈Ω
    rw [e.symm_apply_apply]
    exact hBoundary t z hz
  have hQ0 : MapsTo (Q t0) (closedBall c R) O := by
    intro z hz
    change e.symm (e (P t0 z))∈Ω
    rw [e.symm_apply_apply]
    exact hInitial hz
  obtain ⟨L,-,hLO,hAll⟩ := holomorphic_disc_continuity_principle hO Q hQ hQhol hR hK hKO
    (fun t z hz => ⟨(t,z),⟨mem_univ t,hz⟩,rfl⟩) t0 hQ0
  refine ⟨H t1,hHhol t1,?_,?_⟩
  · intro z hz
    have h := hLO (hAll t1 z hz)
    change e.symm (e (P t1 z))∈Ω at h
    rw [e.symm_apply_apply] at h
    change (Z (radial t1 z),H t1 z)∈Ω at h
    rwa [hrad1] at h
  · intro z hz
    have hsmall := (hApprox t1 ⟨z,hz⟩).trans (by linarith : ε/2<ε)
    change ‖fibreRealVector (H t1 z)-w (radial t1 z)‖<ε at hsmall
    rw [hrad1] at hsmall
    have hgood := hslackG z hz _ hsmall
    change (Z z,realFibreEmbedding (fibreRealVector (H t1 z)))∈Ω ∧
      φ (Z z,realFibreEmbedding (fibreRealVector (H t1 z)))<(g z:EReal) at hgood
    rw [hinv (Z z) _ _ hgood.1 (fun k => (hre (H t1 z) k).symm)]
    exact hgood.2

end SGPT.PSH.KiselmanNext


/-! Entire exact original convex-tube-slice Kiselman principle, retaining
variable fibres, actual projection, poles, all dimensions and exact infimum. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.KiselmanNext
open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

theorem tubeInfimum_le_of_mem {m n : ℕ} {Ω : Set (ComplexModel m × ComplexModel n)}
    {φ : ComplexModel m × ComplexModel n → EReal} {z : ComplexModel m} {w : ComplexModel n}
    (hw : (z,w)∈Ω) : tubeInfimum Ω φ z≤φ (z,w) :=
  iInf_le_of_le w (iInf_le _ hw)

theorem tubeInfimum_ne_top {m n : ℕ} {Ω : Set (ComplexModel m × ComplexModel n)}
    {φ : ComplexModel m × ComplexModel n → EReal} (hφ : PlurisubharmonicOn φ Ω)
    {z : ComplexModel m} (hz : z∈Prod.fst '' Ω) : tubeInfimum Ω φ z≠⊤ := by
  obtain ⟨⟨x,w⟩,hw,hx⟩ := hz
  change x=z at hx
  subst x
  exact ne_top_of_le_ne_top (hφ (z,w) hw).ne_top (tubeInfimum_le_of_mem hw)

theorem upperSemicontinuousAt_tubeInfimum {m n : ℕ}
    {Ω : Set (ComplexModel m × ComplexModel n)} (hΩ : IsOpen Ω)
    {φ : ComplexModel m × ComplexModel n → EReal} (hφ : PlurisubharmonicOn φ Ω)
    (z : ComplexModel m) : UpperSemicontinuousAt (tubeInfimum Ω φ) z := by
  intro C hC
  change (⨅ w∈BookDeep2Kiselman.slice Ω z,φ (z,w))<C at hC
  obtain ⟨w,hw⟩ := iInf_lt_iff.mp hC
  obtain ⟨hwΩ,hwφ⟩ := iInf_lt_iff.mp hw
  have hu := Pending.KiselmanMinimumPrincipleProof.uscAt_comp (f:=φ)
    (φ:=fun y : ComplexModel m => (y,w)) (x:=z)
    (hφ (z,w) hwΩ).upperSemicontinuousAt
    (continuous_id.prodMk continuous_const).continuousAt
  have hdomain : {y : ComplexModel m | (y,w)∈Ω}∈𝓝 z :=
    (hΩ.preimage (continuous_id.prodMk continuous_const)).mem_nhds hwΩ
  filter_upwards [hdomain,hu C hwφ] with y hyΩ hyφ
  exact (tubeInfimum_le_of_mem hyΩ).trans_lt hyφ

theorem tubeInfimum_le_circleAverage {m n : ℕ}
    {Ω : Set (ComplexModel m × ComplexModel n)} (hΩ : BookDeep2Kiselman.IsPseudoconvex Ω)
    (htube : ∀ z,∃ E : Set (Fin n → ℝ),Convex ℝ E ∧
      BookDeep2Kiselman.slice Ω z={w | (fun k => (w k).re)∈E})
    {φ : ComplexModel m × ComplexModel n → EReal} (hφ : PlurisubharmonicOn φ Ω)
    (hinv : ∀ z w w',(z,w)∈Ω → (∀ k,(w k).re=(w' k).re) → φ (z,w')=φ (z,w))
    {Z : ℂ → ComplexModel m} (hZ : Differentiable ℂ Z) {c : ℂ} {R : ℝ} (hR : 0<R)
    (hbase : MapsTo Z (closedBall c R) (Prod.fst '' Ω)) {g : ℂ → ℝ} (hg : Continuous g)
    (hlt : ∀ z∈sphere c R,tubeInfimum Ω φ (Z z)<(g z:EReal)) :
    tubeInfimum Ω φ (Z c)≤((Real.circleAverage g c R:ℝ):EReal) := by
  obtain ⟨H,hH,hgraph,hboundary⟩ := exists_original_holomorphic_graph_below_boundary_majorant
    hΩ htube hφ hinv hZ hR hbase hg hlt
  let F : ℂ → ComplexModel m × ComplexModel n := fun z => (Z z,H z)
  have hF : Differentiable ℂ F := hZ.prodMk hH
  have hp := plurisubharmonicOn_comp_entire_product_disc hΩ.1 hφ hF
  have hD : closedBall c R⊆F ⁻¹' Ω := hgraph
  have hmean := PlurisubharmonicOn.le_circleAverage_of_continuous_majorant hp hR hD hg
    (fun z hz => (hboundary z hz).le)
    (fun ε hε => exists_global_harmonic_uniformApproxOn_sphere c hR hg.continuousOn hε)
  exact (tubeInfimum_le_of_mem (hgraph c (mem_closedBall_self hR.le))).trans hmean

theorem plurisubharmonicOn_tubeInfimum {m n : ℕ}
    {Ω : Set (ComplexModel m × ComplexModel n)} (hΩ : BookDeep2Kiselman.IsPseudoconvex Ω)
    (htube : ∀ z,∃ E : Set (Fin n → ℝ),Convex ℝ E ∧
      BookDeep2Kiselman.slice Ω z={w | (fun k => (w k).re)∈E})
    {φ : ComplexModel m × ComplexModel n → EReal} (hφ : PlurisubharmonicOn φ Ω)
    (hinv : ∀ z w w',(z,w)∈Ω → (∀ k,(w k).re=(w' k).re) → φ (z,w')=φ (z,w)) :
    PlurisubharmonicOn (tubeInfimum Ω φ) (Prod.fst '' Ω) := by
  let u := tubeInfimum Ω φ
  let U := Prod.fst '' Ω
  have hU : IsOpen U := isOpenMap_fst _ hΩ.1
  have htop : ∀ y∈U,u y≠⊤ := fun y hy => tubeInfimum_ne_top hφ hy
  have husc : UpperSemicontinuousOn u U := fun y hy =>
    (upperSemicontinuousAt_tubeInfimum hΩ.1 hφ y).upperSemicontinuousWithinAt U
  refine DiscPshOn.plurisubharmonicOn ⟨htop,husc,?_⟩ hU
  intro x v r hr hD C hC
  let Z : ℂ → ComplexModel m := fun ζ => x+ζ • v
  have hZ : Differentiable ℂ Z := (differentiable_const (c:=x)).add (differentiable_id.smul_const v)
  have hZcont : Continuous Z := hZ.continuous
  let wfun : ℂ → EReal := fun ζ => u (Z ζ)
  have hdisc : ∀ ζ∈closedBall (0:ℂ) r,Z ζ∈affineClosedDisc x v r := fun ζ hζ => ⟨ζ,hζ,rfl⟩
  have hbase : MapsTo Z (closedBall (0:ℂ) r) U := fun ζ hζ => hD (hdisc ζ hζ)
  let K : Set ℂ := sphere (0:ℂ) r
  have hKne : K.Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hKcl : K⊆closedBall (0:ℂ) r := sphere_subset_closedBall
  have htopK : ∀ ζ∈K,wfun ζ≠⊤ := fun ζ hζ => htop _ (hbase (hKcl hζ))
  have hCK : ∀ ζ∈K,wfun ζ≤(C:EReal) := fun ζ hζ => hC _ (hdisc ζ (hKcl hζ))
  have huscK : UpperSemicontinuousOn wfun K := husc.comp hZcont.continuousOn
    (fun ζ hζ => hbase (hKcl hζ))
  let g : ℕ → ℂ → ℝ := fun k => uscSupConvolution K wfun C k
  have hgcont : ∀ k,Continuous (g k) := fun k => continuous_uscSupConvolution hKne htopK hCK k
  have hcenter : ∀ k,wfun 0≤((Real.circleAverage (g k) 0 r:ℝ):EReal) := by
    intro k
    have hε : ∀ ε : ℝ,0<ε → wfun 0≤((Real.circleAverage (g k) 0 r+ε:ℝ):EReal) := by
      intro ε hε
      have hc := tubeInfimum_le_circleAverage hΩ htube hφ hinv hZ hr hbase (g:=fun ζ => g k ζ+ε)
        ((hgcont k).add continuous_const)
        (fun ζ hζ => (le_coe_uscSupConvolution hKne htopK hCK k hζ).trans_lt
          (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hε)))
      have havg : Real.circleAverage (fun ζ => g k ζ+ε) 0 r=Real.circleAverage (g k) 0 r+ε := by
        rw [Real.circleAverage_fun_add (hgcont k).continuousOn.circleIntegrable'
          (circleIntegrable_const ε 0 r),Real.circleAverage_const]
      rw [havg] at hc
      exact hc
    by_contra hnot
    have hlt : ((Real.circleAverage (g k) 0 r:ℝ):EReal)<wfun 0 := not_le.mp hnot
    obtain ⟨B,hAB,hBw⟩ := EReal.exists_between_coe_real hlt
    have hAB' : Real.circleAverage (g k) 0 r<B := EReal.coe_lt_coe_iff.mp hAB
    have hh := hε (B-Real.circleAverage (g k) 0 r) (by linarith)
    rw [show Real.circleAverage (g k) 0 r+(B-Real.circleAverage (g k) 0 r)=B by ring] at hh
    exact lt_irrefl _ (hh.trans_lt hBw)
  have hsub := circleSubmean_of_continuous_antitone_majorants (w:=wfun) (0:ℂ)
    (R:=r) (C:=C) g hgcont
    (fun k ζ _ => uscSupConvolution_le hKne htopK hCK k ζ)
    (fun ζ a b hab => EReal.coe_le_coe_iff.mpr (uscSupConvolution_antitone hKne htopK hCK _ hab))
    (fun t => iInf_coe_uscSupConvolution hKne huscK htopK hCK
      (by rw [zero_add]; exact circleMap_mem_sphere 0 hr.le t)) hcenter
  have hdef : circleDeficit u x v r C=circleDeficit wfun 0 1 r C := by
    simp only [circleDeficit,wfun,Z,zero_add,smul_eq_mul,mul_one]
  have h0 : wfun 0=u x := by simp only [wfun,Z,zero_smul,add_zero]
  change circleDeficit u x v r C≤ENNReal.ofReal (2*Real.pi)*((C:EReal)-u x).toENNReal
  rw [hdef,← h0]
  exact hsub

theorem tubeInfimum_eq_realInfimum {m n : ℕ} {Ω : Set (ComplexModel m × ComplexModel n)}
    {φ : ComplexModel m × ComplexModel n → EReal}
    (hinv : ∀ z w w',(z,w)∈Ω → (∀ k,(w k).re=(w' k).re) → φ (z,w')=φ (z,w))
    (z : ComplexModel m) {E : Set (Fin n → ℝ)}
    (hE : BookDeep2Kiselman.slice Ω z={w | (fun k => (w k).re)∈E}) :
    tubeInfimum Ω φ z=⨅ t∈E,φ (z,WithLp.toLp 2 (fun k => (t k:ℂ))) := by
  apply le_antisymm
  · apply le_iInf
    intro t
    apply le_iInf
    intro ht
    apply tubeInfimum_le_of_mem
    change WithLp.toLp 2 (fun k => (t k:ℂ))∈BookDeep2Kiselman.slice Ω z
    rw [hE]
    exact ht
  · apply le_iInf
    intro w
    apply le_iInf
    intro hw
    have ht : (fun k => (w k).re)∈E := by
      have h := hw
      rw [hE] at h
      exact h
    have hφeq := hinv z w (WithLp.toLp 2 (fun k => ((w k).re:ℂ))) hw (fun k => rfl)
    exact (iInf_le_of_le (fun k => (w k).re) (iInf_le _ ht)).trans_eq hφeq

theorem kiselmanPrincipleConvexSlices (m n : ℕ) : BookDeep2Kiselman.KiselmanPrincipleConvexSlices m n := by
  intro Ω hConnected hΩ htube φ hφ hinv
  have hp := plurisubharmonicOn_tubeInfimum hΩ htube (hφ.disc.plurisubharmonicOn hΩ.1) hinv
  by_cases hbot : ∀ z∈Prod.fst '' Ω,tubeInfimum Ω φ z=⊥
  · exact Or.inl hbot
  · apply Or.inr
    refine ⟨hp.discPshOn,?_⟩
    push Not at hbot
    exact hbot

end SGPT.PSH.KiselmanNext
