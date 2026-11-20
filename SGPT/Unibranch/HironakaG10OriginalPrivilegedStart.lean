import SGPT.Foundations.Analysis.Pending.HironakaG10FlatPrivilegedEuclidean
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace SGPT.Unibranch.HironakaG10OriginalPrivilegedStart
open SGPT.Foundations.Analysis.Pending OkaRelationSheaf HironakaG10FlatPolydiscAlgebra
  HironakaG10FlatResolutionStart HironakaG10FlatPrivilegedNbhd HironakaG10FlatPrivilegedEuclidean
noncomputable section

/-- Choose one genuine holomorphic relation start and privileged polydisc
from the original matrix germ, before every later parameter test. -/
theorem exists_original_privileged_start (n : ℕ) {a b : ℕ}
    (F : Fin a → Fin b → EuclideanSpace ℂ (Fin n) → ℂ)
    (x₀ : EuclideanSpace ℂ (Fin n)) (hF : ∀ i j, HolAt (F i j) x₀) :
    ∃ U K : Set (EuclideanSpace ℂ (Fin n)), ∃ (_hU : IsOpen U),
      ∃ (_hxU : x₀ ∈ U), ∃ (hKU : K ⊆ U), ∃ (hKc : IsCompact K),
      K ∈ closedPolydiscs n ∧ K ∈ 𝓝 x₀ ∧
      ∃ (c : ℕ) (G : Fin b → Fin c → EuclideanSpace ℂ (Fin n) → ℂ)
        (hFU : ∀ i j, DifferentiableOn ℂ (F i j) U)
        (hGU : ∀ j l, DifferentiableOn ℂ (G j l) U),
        (∀ x ∈ U, ∀ i l, ∑ j, F i j x * G j l x = 0) ∧
        let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
        DirectExact (restrictMatrix K hKU G hGU) (restrictMatrix K hKU F hFU) := by
  have hp := privilegedNbhdsProperty_euclidean n Unit (fun _ => a) (fun _ => b)
    (fun _ => F) x₀ (fun _ => hF)
  obtain ⟨U,m,s,d,hres,hU,hx,hfirst,hneigh⟩ := hp
  obtain ⟨K,hK,_,hKU,hKc,hKn,_,hpriv⟩ := hneigh univ univ_mem
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hd0 : d () 0 = F := hfirst ()
  have hFU : ∀ i j, DifferentiableOn ℂ (F i j) U := by
    rw [← hd0]
    exact (hres ()).hol 0
  let G := d () 1
  have hGU : ∀ j l, DifferentiableOn ℂ (G j l) U := (hres ()).hol 1
  have hcomp : ∀ x ∈ U, ∀ i l, ∑ j, F i j x * G j l x = 0 := by
    intro x hx i l
    rw [← hd0]
    exact ((hres ()).exact 0 (hres ()).pos).comp i l x hx
  have hrestrict : restrictMatrix K hKU (d () 0) ((hres ()).hol 0) =
      restrictMatrix K hKU F hFU := by
    funext i j
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    change d () 0 i j z = F i j z
    exact congrFun (congrFun (congrFun hd0 i) j) z
  have hex : DirectExact (restrictMatrix K hKU G hGU) (restrictMatrix K hKU F hFU) := by
    have hex0 := hpriv () 0 (hres ()).pos
    change DirectExact (restrictMatrix K hKU G hGU)
      (restrictMatrix K hKU (d () 0) ((hres ()).hol 0)) at hex0
    rw [hrestrict] at hex0
    exact hex0
  exact ⟨U,K,hU,hx,hKU,hKc,hK,hKn,_,G,hFU,hGU,hcomp,hex⟩
end
end SGPT.Unibranch.HironakaG10OriginalPrivilegedStart
