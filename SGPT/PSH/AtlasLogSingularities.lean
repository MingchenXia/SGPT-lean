import SGPT.PSH.AtlasGeometricQOpenRestriction
import SGPT.PSH.AtlasVanishingIdeal

/-! The literal original local logarithmic definition on the original varying
atlas, with its actual intrinsic analytic-singularity consumer. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

open Classical in
/-- Exact original def:pshfunctions:L1393: original QPSH, one original open,
finite DISTINCT original primes, complete SAME restricted divisor coefficients,
actual all-chart holomorphic equations, ENTIRE reduced stalk ideals, and ONE
bounded real remainder on ALL that same open, including original poles. -/
def SourceHasLogSingularitiesAlong (D : AtlasEffectiveGeometricQDivisor A)
    (u : X → EReal) : Prop :=
  A.IsQPSH u ∧ ∀ x : X,∃ U : Opens X,x∈U ∧
    letI := A.openRestriction_paracompactSpace U
    ∃ (r : ℕ) (W : Fin r → AtlasGeometricPrimeCarrier (A.openRestriction U))
      (a : Fin r → ℚ) (p : Fin r → U → ℂ) (R : U → ℝ) (C : ℝ),
      Function.Injective W ∧ (∀ i,0<a i) ∧
      (∀ i,(A.openRestriction U).ChartHolomorphicOn (p i) univ) ∧
      (∀ i y b,(atlasVanishingIdeal (A.openRestriction U) (W i).val).mem y b ↔
        (A.openRestriction U).AtlasIsInSpanAt (· = p i) y b) ∧
      (∀ P : AtlasGeometricPrimeCarrier (A.openRestriction U),
        (D.openRestriction U).coefficient P = ∑ i,if W i=P then a i else 0) ∧
      0≤C ∧ (∀ y,|R y|≤C) ∧
      ∀ y : U,u y=(∑ i,((a i : ℝ) : EReal)*logNormSq (p i y))+(R y : EReal)

omit [T2Space X] [ParacompactSpace X] in
private theorem chartHolomorphicOn_product {ι : Type*} (s : Finset ι)
    (f : ι → X → ℂ) {U : Set X} (hf : ∀ i∈s,A.ChartHolomorphicOn (f i) U) :
    A.ChartHolomorphicOn (fun x => ∏ i∈s,f i x) U := by
  classical
  intro j
  have hprod : ∀ t : Finset ι,
      (∀ i∈t,DifferentiableOn ℂ (f i ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) →
      DifferentiableOn ℂ (fun z => ∏ i∈t,f i ((A.chart j).symm z))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simpa only [Finset.prod_empty] using differentiableOn_const (1 : ℂ)
    | @insert i t hi ih =>
      intro ht
      simp only [Finset.prod_insert hi]
      exact (ht i (Finset.mem_insert_self _ _)).mul
        (ih (fun k hk => ht k (Finset.mem_insert_of_mem hk)))
  exact hprod s (fun i hi => hf i hi j)

omit [T2Space X] [ParacompactSpace X] in
/-- Actual original finite rational logarithms produce a genuine original
connected analytic presentation. Local denominator and product are constructed
internally, including empty prime lists and every original pole. -/
theorem source_finite_logs_intrinsic (U : Opens X) (x : X) (hx : x∈U) {r : ℕ}
    (p : Fin r → U → ℂ)
    (hp : ∀ i,(A.openRestriction U).ChartHolomorphicOn (p i) univ)
    (w : Fin r → ℚ) (hw : ∀ i,0<w i) (u : X → EReal)
    (R : U → ℝ) (C : ℝ) (hC : 0≤C) (hR : ∀ y,|R y|≤C)
    (hu : ∀ y : U,u y=(∑ i,((w i : ℝ) : EReal)*logNormSq (p i y))+(R y : EReal)) :
    A.HasRationalAnalyticPresentationAt u x := by
  classical
  obtain ⟨d,a,hd,_ha,hlog⟩ := exists_finite_rational_logarithmic_product_grouping
    (Finset.univ : Finset (Fin r)) w (fun i _ => hw i)
  let f : Fin r → X → ℂ := fun i => extendOpens U (p i)
  let G : X → ℂ := fun y => ∏ i,f i y^a i
  have hf (i : Fin r) : A.ChartHolomorphicOn (f i) (U : Set X) := by
    have h := (chartHolomorphicOn_openRestriction_iff A U (p i) univ).mp (hp i)
    have himage : (Subtype.val : U → X) '' (univ : Set U)=(U : Set X) := by
      ext y
      simp
    rw [himage] at h
    exact h
  have hG : A.ChartHolomorphicOn G (U : Set X) := by
    apply chartHolomorphicOn_product Finset.univ (fun i y => f i y^a i)
    intro i _ j
    exact (hf i j).pow (a i)
  have hgroup (y : U) :
      (∑ i,((w i : ℝ) : EReal)*logNormSq (p i y)) =
        (((1/(d : ℚ) : ℚ) : ℝ) : EReal)*logNormSq (G y) := by
    simpa [Finset.sum_coe_sort,Finset.prod_coe_sort,G,f] using hlog (fun i => p i y)
  let b : X → ℝ := fun y => if hy : y∈U then R ⟨y,hy⟩ else 0
  have hb (y : X) (hy : y∈U) : b y=R ⟨y,hy⟩ := by
    dsimp only [b]
    rw [dif_pos hy]
  let : LocallyConnectedSpace X := A.locallyConnectedSpace_of_variableAtlas
  obtain ⟨V,⟨hV,hxV,hconn⟩,hVU⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp (U.isOpen.mem_nhds hx)
  refine ⟨1/(d : ℚ),1,(fun _ => G),b,C,V,by positivity,hC,hV,hconn,hxV,
    (fun _ i => (hG i).mono (fun _ hz => ⟨hz.1,hVU hz.2⟩)),?_,?_⟩
  · intro y hy
    rw [hb y (hVU hy)]
    exact hR ⟨y,hVU hy⟩
  · intro y hy
    have hsingle : generatorLog (fun _ : Fin 1 => G) y=logNormSq (G y) := by
      rw [generatorLog_eq_log_sum]
      simp [logNormSq]
    change u y=(((1/(d : ℚ) : ℚ) : ℝ) : EReal)*
      generatorLog (fun _ : Fin 1 => G) y+(b y : EReal)
    rw [hsingle,hb y (hVU hy)]
    exact (hu ⟨y,hVU hy⟩).trans
      (congrArg (fun t => t+(R ⟨y,hVU hy⟩ : EReal)) (hgroup ⟨y,hVU hy⟩))

/-- The LITERAL original varying-atlas logarithmic predicate implies the
existing intrinsic rational analytic type of the SAME original potential.
There is no fixed dimension, compactness, metric or supplied analytic type. -/
theorem SourceHasLogSingularitiesAlong.intrinsic
    {D : AtlasEffectiveGeometricQDivisor A} {u : X → EReal}
    (hu : SourceHasLogSingularitiesAlong D u) : A.HasRationalAnalyticType u := by
  intro x
  obtain ⟨U,hx,r,W,a,p,R,C,_hW,ha,hp,_hideal,_hcoeff,hC,hR,hlog⟩ := hu.2 x
  exact source_finite_logs_intrinsic U x hx p hp a ha u R C hC hR hlog

end SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
