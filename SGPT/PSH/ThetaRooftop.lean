import SGPT.Toric.RelativeThetaCriterion
import SGPT.PSH.SingularityOrder
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Classical ContDiff
variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- A genuine USC finite upper obstacle manufactures every corrected chart
family's actual local uniform upper bound. -/
theorem locallyBounded_corrected_family_of_majorant {I : Type*}
    {v : I → X → EReal} {w : X → EReal}
    (hw : UpperSemicontinuous w) (hwt : ∀ x, w x ≠ ⊤)
    (hle : ∀ j, v j ≤ w) {U : Set X} {g : X → ℝ}
    (hU : IsOpen U) (hg : A.ChartSmoothOn g U) (i : A.Index) :
    SGPT.PSH.LocallyUniformlyBoundedAbove
      (fun j z ↦ A.coordinate (v j) i z + (g ((A.chart i).symm z) : EReal))
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
  intro z hz
  let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U
  let σ := g ∘ (A.chart i).symm
  have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hU
  have hσ : ContinuousAt σ z := ((hg i z hz).contDiffAt (hD.mem_nhds hz)).continuousAt
  have hwc : UpperSemicontinuousAt (fun y ↦ w ((A.chart i).symm y)) z :=
    (hw ((A.chart i).symm z)).comp ((A.chart i).continuousAt_symm hz.1)
  have hs : UpperSemicontinuousAt
      (fun y ↦ w ((A.chart i).symm y) + (σ y : EReal)) z :=
    hwc.add'
      (continuous_coe_real_ereal.continuousAt.comp hσ).upperSemicontinuousAt
      (EReal.continuousAt_add (.inr (EReal.coe_ne_bot (σ z)))
        (.inr (EReal.coe_ne_top (σ z))))
  have ht : w ((A.chart i).symm z) + (σ z : EReal) ≠ ⊤ :=
    EReal.add_ne_top (hwt _) (EReal.coe_ne_top _)
  obtain ⟨C, hC, _⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr ht)
  refine ⟨{y | w ((A.chart i).symm y) + (σ y : EReal) < (C : EReal)},
    mem_nhdsWithin_of_mem_nhds (hs (C : EReal) hC), C, ?_⟩
  intro j y hy
  exact (add_le_add (hle j ((A.chart i).symm y)) le_rfl).trans hy.1.le

/-- Original universal local-potential tests are preserved by a genuinely
upper-regularized nonempty family below an actual finite USC obstacle. -/
theorem isThetaPSH_uscSup_of_majorant {I : Type*} [Nonempty I]
    {θ : AtlasClosedRealOneOneForm A} {v : I → X → EReal} {w : X → EReal}
    (hv : ∀ j, A.IsThetaPSH θ (v j))
    (hw : UpperSemicontinuous w) (hwt : ∀ x, w x ≠ ⊤)
    (hle : ∀ j, v j ≤ w) : A.IsThetaPSH θ (uscSup v) := by
  have hbound : uscSup v ≤ w :=
    uscRegularization_le hw (fun x ↦ iSup_le fun j ↦ hle j x)
  refine ⟨fun x ↦ ne_of_lt ((hbound x).trans_lt (lt_top_iff_ne_top.mpr (hwt x))), ?_⟩
  intro U g hg
  apply (isPSHOn_iff_chart_and_nondegenerate hg.1).mpr
  constructor
  · intro i
    let D := (A.chart i).target ∩ (A.chart i).symm ⁻¹' U
    let σ := g ∘ (A.chart i).symm
    let f := fun j z ↦ A.coordinate (v j) i z + (σ z : EReal)
    have hD : IsOpen D := (A.chart i).isOpen_inter_preimage_symm hg.1
    have hσ : ContDiffOn ℝ ∞ σ D := hg.2.1 i
    have hp : ∀ j, PlurisubharmonicOn (f j) D :=
      fun j ↦ ((hv j).2 U g hg).chartPlurisubharmonic i
    have hb := locallyBounded_corrected_family_of_majorant hw hwt hle hg.1 hg.2.1 i
    have hr := plurisubharmonicOn_uscRegularization_sSup hD
      (Set.range_nonempty f) (by rintro t ⟨j, rfl⟩; exact hp j)
      (locallyUniformlyBoundedAbove_range_iff.mpr hb)
    rw [sSup_range_eq] at hr
    have heq : (fun y ↦ ⨆ j, f j y) =
        (fun y ↦ (⨆ j, A.coordinate (v j) i y) + (σ y : EReal)) := by
      funext y
      exact iSup_add_coe (fun j ↦ A.coordinate (v j) i y) (σ y)
    rw [heq] at hr
    intro z hz
    apply (hr z hz).congr
    filter_upwards [hD.mem_nhds hz] with y hy
    rw [uscRegularization_add_coe_continuousAt_apply _
      (((hσ y hy).contDiffAt (hD.mem_nhds hy)).continuousAt)]
    change uscSup (fun j ↦ A.coordinate (v j) i) y + (σ y : EReal) =
      A.coordinate (uscSup v) i y + (σ y : EReal)
    rw [uscSup_coordinateFamily v i hy.1]
  · intro x hx O hO hxO
    obtain ⟨y, hy, hn⟩ := ((hv (Classical.arbitrary I)).2 U g hg).locallyNondegenerate
      hg.1 x hx O hO hxO
    refine ⟨y, hy, ?_⟩
    intro hb
    change uscSup v y + (g y : EReal) = ⊥ at hb
    apply hn
    have hlow : v (Classical.arbitrary I) y + (g y : EReal) ≤
        uscSup v y + (g y : EReal) :=
      add_le_add ((le_iSup (fun j ↦ v j y) (Classical.arbitrary I)).trans
        (le_uscRegularization (fun z ↦ ⨆ j, v j z) y)) (le_refl (g y : EReal))
    rw [hb] at hlow
    exact le_bot_iff.mp hlow

/-- The literal source raw supremum of ALL genuine theta-PSH common minorants.
The complete lattice itself gives bottom for an empty competitor family. -/
def thetaRooftop (θ : AtlasClosedRealOneOneForm A) (u v : X → EReal) : X → EReal :=
  fun x ↦ ⨆ (f : {f : X → EReal // A.IsThetaPSH θ f ∧ f ≤ u ∧ f ≤ v}), f.1 x

/-- The original source class with the expressly adjoined bottom function. -/
def IsThetaPSHOrBot (θ : AtlasClosedRealOneOneForm A) (u : X → EReal) : Prop :=
  A.IsThetaPSH θ u ∨ u = ⊥

/-- The actual raw rooftop lies below its first obstacle. -/
theorem thetaRooftop_le_left (θ : AtlasClosedRealOneOneForm A) (u v : X → EReal) :
    thetaRooftop θ u v ≤ u :=
  fun x ↦ iSup_le fun f ↦ f.2.2.1 x

/-- The actual raw rooftop lies below its second obstacle. -/
theorem thetaRooftop_le_right (θ : AtlasClosedRealOneOneForm A) (u v : X → EReal) :
    thetaRooftop θ u v ≤ v :=
  fun x ↦ iSup_le fun f ↦ f.2.2.2 x

/-- Every genuine original common minorant is below the actual raw rooftop. -/
theorem le_thetaRooftop {θ : AtlasClosedRealOneOneForm A} {u v f : X → EReal}
    (hf : A.IsThetaPSH θ f) (hfu : f ≤ u) (hfv : f ≤ v) :
    f ≤ thetaRooftop θ u v :=
  fun x ↦ le_iSup (fun t ↦ t.1 x) (⟨f, hf, hfu, hfv⟩ :
    {f : X → EReal // A.IsThetaPSH θ f ∧ f ≤ u ∧ f ≤ v})

/-- Bottom is a genuine branch of the source operation, even on an empty space. -/
theorem thetaRooftop_bot_left (θ : AtlasClosedRealOneOneForm A) (v : X → EReal) :
    thetaRooftop θ ⊥ v = ⊥ :=
  eq_bot_iff.mpr (thetaRooftop_le_left θ ⊥ v)

theorem thetaRooftop_bot_right (θ : AtlasClosedRealOneOneForm A) (u : X → EReal) :
    thetaRooftop θ u ⊥ = ⊥ :=
  eq_bot_iff.mpr (thetaRooftop_le_right θ u ⊥)

/-- The displayed source definition is symmetric before any analytic assumption. -/
theorem thetaRooftop_comm (θ : AtlasClosedRealOneOneForm A) (u v : X → EReal) :
    thetaRooftop θ u v = thetaRooftop θ v u := by
  apply le_antisymm
  · intro x
    exact iSup_le fun f ↦ le_thetaRooftop f.2.1 f.2.2.2 f.2.2.1 x
  · intro x
    exact iSup_le fun f ↦ le_thetaRooftop f.2.1 f.2.2.2 f.2.2.1 x

/-- The actual nonempty original competitor family supplies the PSH rooftop,
without assuming that its raw supremum is USC or is itself a competitor. -/
theorem isThetaPSH_thetaRooftop_of_nonempty
    {θ : AtlasClosedRealOneOneForm A} {u v : X → EReal}
    (hu : A.IsThetaPSH θ u) (hv : A.IsThetaPSH θ v)
    (hn : Nonempty {f : X → EReal // A.IsThetaPSH θ f ∧ f ≤ u ∧ f ≤ v}) :
    A.IsThetaPSH θ (thetaRooftop θ u v) := by
  let := hn
  let F := fun f : {f : X → EReal // A.IsThetaPSH θ f ∧ f ≤ u ∧ f ≤ v} ↦ f.1
  have he : A.IsThetaPSH θ (uscSup F) :=
    isThetaPSH_uscSup_of_majorant (fun f ↦ f.2.1) hu.upperSemicontinuous hu.1
      (fun f ↦ f.2.2.1)
  have heu : uscSup F ≤ u :=
    uscRegularization_le hu.upperSemicontinuous (fun x ↦ iSup_le fun f ↦ f.2.2.1 x)
  have hev : uscSup F ≤ v :=
    uscRegularization_le hv.upperSemicontinuous (fun x ↦ iSup_le fun f ↦ f.2.2.2 x)
  have hraw : thetaRooftop θ u v = uscSup F := by
    apply le_antisymm
    · intro x
      exact le_uscRegularization (fun y ↦ ⨆ f, F f y) x
    · exact le_thetaRooftop he heu hev
  rw [hraw]
  exact he

/-- An actually empty competitor family gives exactly the original bottom. -/
theorem thetaRooftop_eq_bot_of_empty
    {θ : AtlasClosedRealOneOneForm A} {u v : X → EReal}
    (hn : ¬ Nonempty {f : X → EReal // A.IsThetaPSH θ f ∧ f ≤ u ∧ f ≤ v}) :
    thetaRooftop θ u v = ⊥ := by
  have : IsEmpty {f : X → EReal // A.IsThetaPSH θ f ∧ f ≤ u ∧ f ≤ v} :=
    not_nonempty_iff.mp hn
  funext x
  simp [thetaRooftop]

/-- The actual source class with bottom is closed under the literal raw roof. -/
theorem isThetaPSHOrBot_thetaRooftop
    {θ : AtlasClosedRealOneOneForm A} {u v : X → EReal}
    (hu : IsThetaPSHOrBot θ u) (hv : IsThetaPSHOrBot θ v) :
    IsThetaPSHOrBot θ (thetaRooftop θ u v) := by
  rcases hu with hu | rfl
  · rcases hv with hv | rfl
    · by_cases hn : Nonempty {f : X → EReal // A.IsThetaPSH θ f ∧ f ≤ u ∧ f ≤ v}
      · exact Or.inl (isThetaPSH_thetaRooftop_of_nonempty hu hv hn)
      · exact Or.inr (thetaRooftop_eq_bot_of_empty hn)
    · exact Or.inr (thetaRooftop_bot_right θ u)
  · exact Or.inr (thetaRooftop_bot_left θ v)

/-- Defining greatest-minorant property includes the genuinely adjoined bottom. -/
theorem le_thetaRooftop_of_orBot {θ : AtlasClosedRealOneOneForm A} {u v f : X → EReal}
    (hf : IsThetaPSHOrBot θ f) (hfu : f ≤ u) (hfv : f ≤ v) :
    f ≤ thetaRooftop θ u v := by
  rcases hf with hf | rfl
  · exact le_thetaRooftop hf hfu hfv
  · exact bot_le

/-- Genuine class closure and original maximality yield associativity, with
all empty-competitor and bottom-operand cases retained. -/
theorem thetaRooftop_assoc {θ : AtlasClosedRealOneOneForm A} {u v w : X → EReal}
    (hu : IsThetaPSHOrBot θ u) (hv : IsThetaPSHOrBot θ v)
    (hw : IsThetaPSHOrBot θ w) :
    thetaRooftop θ (thetaRooftop θ u v) w =
      thetaRooftop θ u (thetaRooftop θ v w) := by
  have hL := isThetaPSHOrBot_thetaRooftop (isThetaPSHOrBot_thetaRooftop hu hv) hw
  have hR := isThetaPSHOrBot_thetaRooftop hu (isThetaPSHOrBot_thetaRooftop hv hw)
  apply le_antisymm
  · apply le_thetaRooftop_of_orBot hL
    · exact (thetaRooftop_le_left θ (thetaRooftop θ u v) w).trans
        (thetaRooftop_le_left θ u v)
    · apply le_thetaRooftop_of_orBot hL
      · exact (thetaRooftop_le_left θ (thetaRooftop θ u v) w).trans
          (thetaRooftop_le_right θ u v)
      · exact thetaRooftop_le_right θ (thetaRooftop θ u v) w
  · apply le_thetaRooftop_of_orBot hR
    · apply le_thetaRooftop_of_orBot hR
      · exact thetaRooftop_le_left θ u (thetaRooftop θ v w)
      · exact (thetaRooftop_le_right θ u (thetaRooftop θ v w)).trans
          (thetaRooftop_le_left θ v w)
    · exact (thetaRooftop_le_right θ u (thetaRooftop θ v w)).trans
        (thetaRooftop_le_right θ v w)

/-- The actual source operation also fixes every genuine class element. -/
theorem thetaRooftop_self {θ : AtlasClosedRealOneOneForm A} {u : X → EReal}
    (hu : IsThetaPSHOrBot θ u) : thetaRooftop θ u u = u :=
  le_antisymm (thetaRooftop_le_left θ u u) (le_thetaRooftop_of_orBot hu le_rfl le_rfl)

end SGPT.PSH.VariableComplexAtlas
