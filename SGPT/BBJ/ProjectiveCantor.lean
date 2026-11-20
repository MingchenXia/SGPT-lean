import SGPT.BBJ.FastCantor
import SGPT.Toric.ProjectiveLineNativeManifold
import Mathlib.Topology.Perfect
import Mathlib.Topology.Connected.TotallyDisconnected

/-! The concrete fast Cantor set in the original projective quotient.
This is an existence ingredient for BBJ, not the whole counterexample. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter
open scoped Topology
local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The actual finite projective chart `[z:1]`, using its established quotient homeomorphism. -/
def projectiveCantorCode (b : ℕ → Bool) : P1 :=
  SGPT.Toric.projectiveLineHomeomorph ((cantorCode b : ℂ) : OnePoint ℂ)

/-- The concrete subset of the same original projective line. -/
def projectiveCantorSet : Set P1 := range projectiveCantorCode

lemma continuous_projectiveCantorCode : Continuous projectiveCantorCode := by
  exact SGPT.Toric.projectiveLineHomeomorph.continuous.comp
    (OnePoint.continuous_coe.comp (Complex.continuous_ofReal.comp continuous_cantorCode))

lemma projectiveCantorCode_injective : Function.Injective projectiveCantorCode := by
  intro b d h
  exact cantorCode_injective (Complex.ofReal_injective
    (OnePoint.coe_injective (SGPT.Toric.projectiveLineHomeomorph.injective h)))

lemma isClosedEmbedding_projectiveCantorCode :
    Topology.IsClosedEmbedding projectiveCantorCode :=
  continuous_projectiveCantorCode.isClosedEmbedding projectiveCantorCode_injective

lemma isCompact_projectiveCantorSet : IsCompact projectiveCantorSet :=
  isCompact_range continuous_projectiveCantorCode

lemma isClosed_projectiveCantorSet : IsClosed projectiveCantorSet :=
  isClosedEmbedding_projectiveCantorCode.isClosed_range

lemma projectiveCantorSet_nonempty : projectiveCantorSet.Nonempty :=
  ⟨projectiveCantorCode (fun _ => false), ⟨_, rfl⟩⟩

lemma isTotallyDisconnected_projectiveCantorSet :
    IsTotallyDisconnected projectiveCantorSet :=
  isClosedEmbedding_projectiveCantorCode.isEmbedding.isTotallyDisconnected_range.mpr
    inferInstance

/-- Flipping one bit at a later and later coordinate gives actual distinct points
converging to the original bit sequence. -/
def cantorFlip (b : ℕ → Bool) (n : ℕ) : ℕ → Bool :=
  fun i => if i = n then !(b i) else b i

lemma cantorFlip_ne (b : ℕ → Bool) (n : ℕ) : cantorFlip b n ≠ b := by
  intro h
  have hi := congrFun h n
  cases hb : b n <;> simp [cantorFlip, hb] at hi

lemma tendsto_cantorFlip (b : ℕ → Bool) :
    Tendsto (cantorFlip b) atTop (𝓝 b) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with n hn
  simp [cantorFlip, Nat.ne_of_lt hn]

lemma perfect_projectiveCantorSet : Perfect projectiveCantorSet := by
  refine ⟨isClosed_projectiveCantorSet, preperfect_iff_nhds.mpr ?_⟩
  rintro p ⟨b, rfl⟩ U hU
  have ht := continuous_projectiveCantorCode.continuousAt.tendsto.comp (tendsto_cantorFlip b)
  have hev : ∀ᶠ n in atTop, projectiveCantorCode (cantorFlip b n) ∈ U := ht.eventually hU
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨projectiveCantorCode (cantorFlip b n), ⟨hn, ⟨_, rfl⟩⟩, ?_⟩
  intro h
  exact cantorFlip_ne b n (projectiveCantorCode_injective h)

/-- Explicit nonreal perturbations of a coded real point in the original chart. -/
def projectiveCantorPerturb (b : ℕ → Bool) (n : ℕ) : P1 :=
  SGPT.Toric.projectiveLineHomeomorph
    (((cantorCode b : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) : OnePoint ℂ)

lemma tendsto_projectiveCantorPerturb (b : ℕ → Bool) :
    Tendsto (projectiveCantorPerturb b) atTop (𝓝 (projectiveCantorCode b)) := by
  have hr : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hz : Tendsto (fun n : ℕ => (cantorCode b : ℂ) +
      ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝 (cantorCode b : ℂ)) := by
    simpa using tendsto_const_nhds.add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hr).mul_const Complex.I)
  exact SGPT.Toric.projectiveLineHomeomorph.continuous.continuousAt.tendsto.comp
    (OnePoint.continuous_coe.continuousAt.tendsto.comp hz)

lemma projectiveCantorPerturb_not_mem (b : ℕ → Bool) (n : ℕ) :
    projectiveCantorPerturb b n ∉ projectiveCantorSet := by
  rintro ⟨d, hd⟩
  have hc := OnePoint.coe_injective (SGPT.Toric.projectiveLineHomeomorph.injective hd)
  have hi := congrArg Complex.im hc
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add] at hi
  exact (one_div_ne_zero hn) hi.symm

lemma dense_compl_projectiveCantorSet : Dense projectiveCantorSetᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨b, rfl⟩ := interior_subset hp
  have hU : interior projectiveCantorSet ∈ 𝓝 (projectiveCantorCode b) :=
    isOpen_interior.mem_nhds hp
  have hev : ∀ᶠ n in atTop, projectiveCantorPerturb b n ∈ interior projectiveCantorSet :=
    (tendsto_projectiveCantorPerturb b).eventually hU
  obtain ⟨n, hn⟩ := hev.exists
  exact projectiveCantorPerturb_not_mem b n (interior_subset hn)

end SGPT.BBJ
