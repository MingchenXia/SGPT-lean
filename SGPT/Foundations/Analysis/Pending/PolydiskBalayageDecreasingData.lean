import SGPT.Foundations.Analysis.Pending.PolydiskPerronSemiconcave
import SGPT.Foundations.Analysis.Pending.PolydiskPerronDataComparison
import SGPT.Foundations.Analysis.Pending.BedfordTaylorDecreasingLimit

set_option autoImplicit false

/-!
# Balayage on the polydisk for decreasing data

`Pending.PolydiskPerronSemiconcave` solves the homogeneous Monge--Ampère
equation on the unit polydisk for `C²` boundary data: the Perron--Bremermann
envelope of such data carries no Bedford--Taylor mass.  Błocki reaches data that
are merely bounded and upper semicontinuous by regularizing the data downwards,
solving for each smooth member, and passing to the decreasing limit of the
envelopes; the envelope is monotone in its data
(`Pending.BedfordTaylor.IsPerronData.perronEnvelope_mono`), so the envelopes do
decrease.

This module performs that passage.  Its only new input is
`Pending.BedfordTaylor.eq_zero_of_antitone_of_isBTLimit`, the Bedford--Taylor
convergence theorem along a decreasing sequence.

The limit of the envelopes is **constructed**, not assumed: it is the pointwise
infimum, which is plurisubharmonic because a decreasing limit of
plurisubharmonic functions is (`DiscPshOn.plurisubharmonicOn_iInf_of_antitone`),
and locally bounded because a constant below the data on the distinguished
boundary is a competitor for every member.  The only hypothesis on the data
besides `IsPerronData` and `C²` is that they decrease on the distinguished
boundary and stay above one constant there.

**What is not proved here.**  Identifying that infimum with the envelope of the
limiting boundary data — the second half of Błocki's passage — is a statement
about `perronEnvelope`, not about Bedford--Taylor measures; it is
`Pending.PolydiskPerronDecreasingLimit.perronEnvelope_iInf_eq_of_antitone`,
which combines with the theorem below into
`eq_zero_of_isBTLimit_perronEnvelope_of_antitone`.

Source: Z. Błocki, *The complex Monge--Ampère operator in pluripotential
theory*, lecture notes, §2.3 and the proof of Theorem 2.3.1.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- The coercion `ℝ → EReal` turns the infimum of an antitone family bounded
below into the lattice infimum: both are the limit of the same sequence. -/
theorem coe_ciInf_of_antitone {a : ℕ → ℝ} (hanti : Antitone a)
    (hbdd : BddBelow (Set.range a)) :
    ((⨅ i, a i : ℝ) : EReal) = ⨅ i, ((a i : ℝ) : EReal) := by
  have h1 : Tendsto (fun i ↦ a i) atTop (𝓝 (⨅ i, a i)) := tendsto_atTop_ciInf hanti hbdd
  have h2 : Tendsto (fun i ↦ ((a i : ℝ) : EReal)) atTop (𝓝 (((⨅ i, a i : ℝ) : EReal))) :=
    (continuous_coe_real_ereal.tendsto _).comp h1
  have h3 : Tendsto (fun i ↦ ((a i : ℝ) : EReal)) atTop
      (𝓝 (⨅ i, ((a i : ℝ) : EReal))) :=
    tendsto_atTop_iInf fun i j hij ↦ EReal.coe_le_coe_iff.2 (hanti hij)
  exact tendsto_nhds_unique h2 h3

/-- A constant below the boundary data is a competitor for it. -/
theorem isPerronCompetitor_const {v : ComplexModel n → ℝ} {c : ℝ}
    (hc : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ v ζ) :
    IsPerronCompetitor v (fun _ ↦ c) := by
  refine ⟨fun x _ ↦ plurisubharmonicAt_const (c : EReal) (EReal.coe_ne_top c) x,
    fun ζ hζ ε hε ↦ Filter.Eventually.of_forall fun _ ↦ ?_⟩
  have := hc ζ hζ
  linarith

/-! ### The decreasing limit of the envelopes -/

/-- The envelopes of an antitone family of boundary data are antitone. -/
theorem antitone_perronEnvelope
    {v : ℕ → ComplexModel n → ℝ} (hv : ∀ j, IsPerronData (v j))
    (hanti : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, Antitone fun j ↦ v j ζ)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    Antitone fun j ↦ perronEnvelope (v j) z := fun j j' hjj' ↦
  IsPerronData.perronEnvelope_mono (hv j') (hv j) (fun ζ hζ ↦ hanti ζ hζ hjj') hz

/-- A constant below the data on the topological boundary `∂P` lies below the
envelope. -/
theorem le_perronEnvelope_of_forall_le {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) {c : ℝ}
    (hc : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ v ζ)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) : c ≤ perronEnvelope v z :=
  hv.le_perronEnvelope (isPerronCompetitor_const hc) hz

/-- Hence a family of envelopes with a common lower bound for the data is
bounded below at every interior point. -/
theorem bddBelow_range_perronEnvelope
    {v : ℕ → ComplexModel n → ℝ} (hv : ∀ j, IsPerronData (v j)) {c : ℝ}
    (hc : ∀ j, ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ v j ζ)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    BddBelow (Set.range fun j ↦ perronEnvelope (v j) z) :=
  ⟨c, by rintro _ ⟨j, rfl⟩; exact le_perronEnvelope_of_forall_le (hv j) (hc j) hz⟩

/-- **The pointwise infimum of a decreasing family of Perron envelopes is a
locally bounded plurisubharmonic function on the polydisk.**  It is
plurisubharmonic because a decreasing limit of plurisubharmonic functions is,
and locally bounded because the constant `c` lies below every member while the
zeroth member is bounded above. -/
theorem isLocallyBoundedPshOn_iInf_perronEnvelope
    {v : ℕ → ComplexModel n → ℝ} (hv : ∀ j, IsPerronData (v j))
    (hanti : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, Antitone fun j ↦ v j ζ)
    {c : ℝ} (hc : ∀ j, ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ v j ζ) :
    IsLocallyBoundedPshOn (unitPolydiskOpens n)
      (fun z ↦ ⨅ j, perronEnvelope (v j) z) := by
  classical
  have hwpsh : ∀ j, IsLocallyBoundedPshOn (unitPolydiskOpens n) (perronEnvelope (v j)) :=
    fun j ↦ (hv j).isLocallyBoundedPshOn_perronEnvelope
  have hwanti : ∀ z ∈ unitPolydisk n, Antitone fun j ↦ perronEnvelope (v j) z :=
    fun z hz ↦ antitone_perronEnvelope hv hanti hz
  have hcw : ∀ j, ∀ z ∈ unitPolydisk n, c ≤ perronEnvelope (v j) z :=
    fun j z hz ↦ le_perronEnvelope_of_forall_le (hv j) (hc j) hz
  have hbdd : ∀ z ∈ unitPolydisk n,
      BddBelow (Set.range fun j ↦ perronEnvelope (v j) z) := fun z hz ↦
    bddBelow_range_perronEnvelope hv hc hz
  have hupsh : PlurisubharmonicOn (fun z ↦ ((⨅ j, perronEnvelope (v j) z : ℝ) : EReal))
      (unitPolydiskOpens n : Set (ComplexModel n)) := by
    have hdisc : ∀ j, DiscPshOn (fun z ↦ ((perronEnvelope (v j) z : ℝ) : EReal))
        (unitPolydiskOpens n : Set (ComplexModel n)) := fun j ↦ (hwpsh j).1.discPshOn
    have h := DiscPshOn.plurisubharmonicOn_iInf_of_antitone
      (unitPolydiskOpens n).isOpen hdisc
      (fun z hz j j' hjj' ↦ EReal.coe_le_coe_iff.2 (hwanti z hz hjj'))
    intro z hz
    refine (h z hz).congr ?_
    filter_upwards [(unitPolydiskOpens n).isOpen.mem_nhds hz] with y hy
    exact (coe_ciInf_of_antitone (hwanti y hy) (hbdd y hy)).symm
  refine ⟨hupsh, fun z hz ↦ ?_⟩
  obtain ⟨M, hM⟩ := (hv 0).exists_bound
  refine ⟨unitPolydiskOpens n, hz, le_rfl, |c| + M, fun y hy ↦ ?_⟩
  have hle : (⨅ j, perronEnvelope (v j) y) ≤ perronEnvelope (v 0) y :=
    ciInf_le (hbdd y hy) 0
  have hge : c ≤ ⨅ j, perronEnvelope (v j) y := le_ciInf fun j ↦ hcw j y hy
  have hup : perronEnvelope (v 0) y ≤ M :=
    (hv 0).perronEnvelope_le_of_forall_le
      (fun x hx ↦ le_trans (le_abs_self _) (hM x hx)) hy
  have hcabs : -|c| ≤ c := neg_abs_le c
  have hM0 : (0 : ℝ) ≤ |c| := abs_nonneg c
  have hMnn : (0 : ℝ) ≤ M := by
    refine le_trans (abs_nonneg (v 0 0)) (hM 0 ?_)
    intro i
    simp
  rw [abs_le]
  constructor <;> linarith

/-- **Balayage passes to a decreasing sequence of `C²` data.**  If the boundary
data `v j` decrease on the topological boundary `∂P` and stay above one constant
there, then the pointwise infimum of their Perron--Bremermann envelopes solves
the homogeneous Monge--Ampère equation on the polydisk.

The envelopes decrease because the envelope is monotone in its data, each one
has vanishing Bedford--Taylor mass by the `C²` case, and the mass of the limit
is their weak limit. -/
theorem eq_zero_of_isBTLimit_of_antitone_perronEnvelope
    {v : ℕ → ComplexModel n → ℝ} (hv : ∀ j, IsPerronData (v j))
    (hv2 : ∀ j, ContDiff ℝ 2 (v j))
    (hanti : ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, Antitone fun j ↦ v j ζ)
    {c : ℝ} (hc : ∀ j, ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, c ≤ v j ζ)
    {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit (unitPolydiskOpens n)
      (fun _ ↦ fun z ↦ ⨅ j, perronEnvelope (v j) z) μ) :
    μ = 0 := by
  classical
  have hwpsh : ∀ j, IsLocallyBoundedPshOn (unitPolydiskOpens n) (perronEnvelope (v j)) :=
    fun j ↦ (hv j).isLocallyBoundedPshOn_perronEnvelope
  have hwanti : ∀ z ∈ (unitPolydiskOpens n : Set (ComplexModel n)),
      Antitone fun j ↦ perronEnvelope (v j) z :=
    fun z hz ↦ antitone_perronEnvelope hv hanti hz
  have hbdd : ∀ z ∈ unitPolydisk n,
      BddBelow (Set.range fun j ↦ perronEnvelope (v j) z) := fun z hz ↦
    bddBelow_range_perronEnvelope hv hc hz
  -- the infimum is the pointwise limit
  have hlim : ∀ z ∈ unitPolydisk n,
      Tendsto (fun j ↦ perronEnvelope (v j) z) atTop
        (𝓝 (⨅ j, perronEnvelope (v j) z)) := fun z hz ↦
    tendsto_atTop_ciInf (hwanti z hz) (hbdd z hz)
  -- and it is a locally bounded plurisubharmonic function
  have hu : IsLocallyBoundedPshOn (unitPolydiskOpens n)
      (fun z ↦ ⨅ j, perronEnvelope (v j) z) :=
    isLocallyBoundedPshOn_iInf_perronEnvelope hv hanti hc
  -- each member has vanishing mass, hence so does the limit
  choose ν hν using fun j ↦
    exists_isBTLimit_of_isLocallyBoundedPshOn
      (u := fun _ : Fin n ↦ perronEnvelope (v j)) (fun _ ↦ hwpsh j)
  have hνzero : ∀ j, ν j = 0 := fun j ↦
    (hv j).eq_zero_of_isBTLimit_perronEnvelope_of_contDiff (hv2 j) (hν j)
  exact eq_zero_of_antitone_of_isBTLimit hwpsh hu hwanti hlim hν hμ hνzero

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
