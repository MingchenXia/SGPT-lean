import SGPT.Hodge.SourceCartierMixedAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft SGPT.Hodge.BDivChain.SourceCartierSequenceDraft

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
local notation "Sys" => ModelSystem.blowup (m+1) X

/-- Genuine all-nef slot additivity, by the accepted ACTUAL decreasing
Cartier sequences and original mixed topology limits. -/
theorem nefIntersectionReal_update_add_pos (ω : KahlerBackground (m+1) X)
    (D : Fin (m+1) → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (j : Fin (m+1)) (U V : WeilFamilyAny Sys) (hU : IsNefAny U) (hV : IsNefAny V) :
    nefIntersectionReal (Function.update D j (U+V))=
      nefIntersectionReal (Function.update D j U)+nefIntersectionReal (Function.update D j V) := by
  classical
  let F : Fin (m+1) ⊕ Bool → WeilFamilyAny Sys := Sum.elim D (fun b => if b then U else V)
  have hF : ∀ i,IsNefAny (F i) := by
    intro i
    cases i with
    | inl i => exact hD i
    | inr b => cases b with | false => exact hV | true => exact hU
  choose A hA ha hc using fun i => exists_decreasing_big_nefCartier_sequence_pos ω (F i) (hF i)
  let B (i : Fin (m+1)) (k : ℕ) := A (Sum.inl i) k
  let P (k : ℕ) := A (Sum.inr true) k
  let Q (k : ℕ) := A (Sum.inr false) k
  have hB i k : IsNefCartierAny (B i k) := (hA (Sum.inl i) k).1
  have hP k : IsNefCartierAny (P k) := (hA (Sum.inr true) k).1
  have hQ k : IsNefCartierAny (Q k) := (hA (Sum.inr false) k).1
  have haB i k l hkl : LEAny (B i l) (B i k) := ha (Sum.inl i) k l hkl
  have haP k l hkl : LEAny (P l) (P k) := ha (Sum.inr true) k l hkl
  have haQ k l hkl : LEAny (Q l) (Q k) := ha (Sum.inr false) k l hkl
  have hcB i : ConvergesAny atTop (B i) (D i) := hc (Sum.inl i)
  have hcP : ConvergesAny atTop P U := hc (Sum.inr true)
  have hcQ : ConvergesAny atTop Q V := hc (Sum.inr false)
  have hlimP := nefIntersectionReal_tendsto_of_antitone ω
    (fun i k => Function.update (fun i => B i k) j (P k) i) (Function.update D j U)
    (fun i k => isNefAny_of_isNefCartierAny (isNefCartierAny_update _ (fun i => hB i k) j _ (hP k) i))
    (fun i k l hkl => leAny_update _ _ (fun i => haB i k l hkl) j _ _ (haP k l hkl) i)
    (convergesAny_update B D hcB j P U hcP)
  have hlimQ := nefIntersectionReal_tendsto_of_antitone ω
    (fun i k => Function.update (fun i => B i k) j (Q k) i) (Function.update D j V)
    (fun i k => isNefAny_of_isNefCartierAny (isNefCartierAny_update _ (fun i => hB i k) j _ (hQ k) i))
    (fun i k l hkl => leAny_update _ _ (fun i => haB i k l hkl) j _ _ (haQ k l hkl) i)
    (convergesAny_update B D hcB j Q V hcQ)
  have hlimSum := nefIntersectionReal_tendsto_of_antitone ω
    (fun i k => Function.update (fun i => B i k) j (P k+Q k) i) (Function.update D j (U+V))
    (fun i k => isNefAny_of_isNefCartierAny (isNefCartierAny_update _ (fun i => hB i k) j _
      (isNefCartierAny_add ω (hP k) (hQ k)) i))
    (fun i k l hkl => leAny_update _ _ (fun i => haB i k l hkl) j _ _
      (leAny_add (haP k l hkl) (haQ k l hkl)) i)
    (convergesAny_update B D hcB j (fun k => P k+Q k) (U+V) (convergesAny_add hcP hcQ))
  have hid k := nefIntersectionReal_update_add_cartier ω (fun i => B i k) (fun i => hB i k)
    j (P k) (Q k) (hP k) (hQ k)
  have hlimSum' : Tendsto (fun k => nefIntersectionReal
      (Function.update (fun i => B i k) j (P k+Q k))) atTop
      (𝓝 (nefIntersectionReal (Function.update D j U)+nefIntersectionReal (Function.update D j V))) := by
    simpa only [hid] using hlimP.add hlimQ
  exact tendsto_nhds_unique hlimSum hlimSum'

/-- Nonnegative real homogeneity, INCLUDING scalar zero on the actual
all-nef extension, with no positive-volume premise on original inputs. -/
theorem nefIntersectionReal_update_smul_pos (ω : KahlerBackground (m+1) X)
    (D : Fin (m+1) → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (j : Fin (m+1)) (U : WeilFamilyAny Sys) (hU : IsNefAny U) (c : ℝ) (hc₀ : 0≤c) :
    nefIntersectionReal (Function.update D j (c • U))=
      c * nefIntersectionReal (Function.update D j U) := by
  classical
  let F : Fin (m+1) ⊕ Unit → WeilFamilyAny Sys := Sum.elim D (fun _ => U)
  have hF : ∀ i,IsNefAny (F i) := by
    intro i
    cases i with | inl i => exact hD i | inr _ => exact hU
  choose A hA ha hc using fun i => exists_decreasing_big_nefCartier_sequence_pos ω (F i) (hF i)
  let B (i : Fin (m+1)) (k : ℕ) := A (Sum.inl i) k
  let P (k : ℕ) := A (Sum.inr ()) k
  have hB i k : IsNefCartierAny (B i k) := (hA (Sum.inl i) k).1
  have hP k : IsNefCartierAny (P k) := (hA (Sum.inr ()) k).1
  have haB i k l hkl : LEAny (B i l) (B i k) := ha (Sum.inl i) k l hkl
  have haP k l hkl : LEAny (P l) (P k) := ha (Sum.inr ()) k l hkl
  have hcB i : ConvergesAny atTop (B i) (D i) := hc (Sum.inl i)
  have hcP : ConvergesAny atTop P U := hc (Sum.inr ())
  have hlimP := nefIntersectionReal_tendsto_of_antitone ω
    (fun i k => Function.update (fun i => B i k) j (P k) i) (Function.update D j U)
    (fun i k => isNefAny_of_isNefCartierAny (isNefCartierAny_update _ (fun i => hB i k) j _ (hP k) i))
    (fun i k l hkl => leAny_update _ _ (fun i => haB i k l hkl) j _ _ (haP k l hkl) i)
    (convergesAny_update B D hcB j P U hcP)
  have hlimScale := nefIntersectionReal_tendsto_of_antitone ω
    (fun i k => Function.update (fun i => B i k) j (c • P k) i) (Function.update D j (c • U))
    (fun i k => isNefAny_of_isNefCartierAny (isNefCartierAny_update _ (fun i => hB i k) j _
      (isNefCartierAny_smul (hP k) hc₀) i))
    (fun i k l hkl => leAny_update _ _ (fun i => haB i k l hkl) j _ _
      (leAny_smul (haP k l hkl) hc₀) i)
    (convergesAny_update B D hcB j (fun k => c • P k) (c • U) (convergesAny_smul hcP c))
  have hid k := nefIntersectionReal_update_smul_cartier ω (fun i => B i k) (fun i => hB i k)
    j (P k) (hP k) c hc₀
  have hlimScale' : Tendsto (fun k => nefIntersectionReal
      (Function.update (fun i => B i k) j (c • P k))) atTop
      (𝓝 (c * nefIntersectionReal (Function.update D j U))) := by
    simpa only [hid] using hlimP.const_mul c
  exact tendsto_nhds_unique hlimScale hlimScale'

theorem nefIntersectionReal_perm_pos (ω : KahlerBackground (m+1) X)
    (D : Fin (m+1) → WeilFamilyAny Sys) (hD : ∀ i,IsNefAny (D i))
    (σ : Equiv.Perm (Fin (m+1))) :
    nefIntersectionReal (fun i => D (σ i))=nefIntersectionReal D := by
  classical
  choose A hA ha hc using fun i => exists_decreasing_big_nefCartier_sequence_pos ω (D i) (hD i)
  have hlim := nefIntersectionReal_tendsto_of_antitone ω A D
    (fun i k => isNefAny_of_isNefCartierAny (hA i k).1) ha hc
  have hlimσ := nefIntersectionReal_tendsto_of_antitone ω (fun i k => A (σ i) k)
    (fun i => D (σ i)) (fun i k => isNefAny_of_isNefCartierAny (hA (σ i) k).1)
    (fun i k l hkl => ha (σ i) k l hkl) (fun i => hc (σ i))
  have hid k := nefIntersectionReal_perm_cartier ω (fun i => A i k) (fun i => (hA i k).1) σ
  have hlimσ' : Tendsto (fun k => nefIntersectionReal (fun i => A (σ i) k)) atTop
      (𝓝 (nefIntersectionReal D)) := by
    simpa only [hid] using hlim
  exact tendsto_nhds_unique hlimσ hlimσ'

end SGPT.Hodge.BDivChain.SourceMixedOrderDraft
