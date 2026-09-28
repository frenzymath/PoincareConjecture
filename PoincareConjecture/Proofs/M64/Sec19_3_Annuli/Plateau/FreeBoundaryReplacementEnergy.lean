import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusReplacement

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 d0 d1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64VariableModulus_boundary_replacement_energy
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) (r : ℝ)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (W : M64ObservedWeakAnnulus (n := n) e d0 d1)
    {K : Set LoopPlane} [DecidablePred (· ∈ K)] (hK : MeasurableSet K) (hKS : K ⊆ S)
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hmap : W.map = K.piecewise f A.map)
    (hcol : ∀ i, (W.column i : LoopPlane → E) =ᵐ[mu] K.piecewise (V i) (A.column i)) :
    W.weightedEnergy Q r = A.weightedEnergy Q r +
      (∫ p in K, (r * Q (f p) (V 0 p) (V 0 p) + r⁻¹ * Q (f p) (V 1 p) (V 1 p)) / 2) -
      ∫ p in K, (r * Q (A.map p) (A.column 0 p) (A.column 0 p) +
        r⁻¹ * Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2 := by
  classical
  let old := fun p => (r * Q (A.map p) (A.column 0 p) (A.column 0 p) +
    r⁻¹ * Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2
  let new := fun p => (r * Q (f p) (V 0 p) (V 0 p) + r⁻¹ * Q (f p) (V 1 p) (V 1 p)) / 2
  have heq : (fun p => (r * Q (W.map p) (W.column 0 p) (W.column 0 p) +
      r⁻¹ * Q (W.map p) (W.column 1 p) (W.column 1 p)) / 2) =ᵐ[mu] K.piecewise new old := by
    filter_upwards [hcol 0, hcol 1] with p h0 h1
    rw [h0, h1, hmap]
    by_cases hp : p ∈ K <;> simp only [piecewise, hp, if_true, if_false, new, old]
  have hi (i : Fin 2) := m64VariableModulus_column_integrable Q hQ hb f hf (V i) (hV i)
  unfold M64ObservedWeakAnnulus.weightedEnergy
  rw [integral_congr_ae heq]
  exact m64Integral_piecewise_of_subset hK hKS
    (((hi 0).const_mul r).add ((hi 1).const_mul r⁻¹) |>.div_const 2)
    (A.weightedEnergy_integrable Q hQ hei hb r)

namespace M64FreeWeakPhaseAnnulus

variable {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

theorem weighted_boundary_local_energy_le
    (R : E →L[ℝ] LoopPlane)
    (A C : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (r : ℝ)
    (hminimum : A.annulus.weightedEnergy B r ≤ C.annulus.weightedEnergy B r)
    {K : Set LoopPlane} [DecidablePred (· ∈ K)] (hK : MeasurableSet K) (hKS : K ⊆ S)
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hmap : C.annulus.map = K.piecewise f A.annulus.map)
    (hcol : ∀ i, (C.annulus.column i : LoopPlane → E) =ᵐ[mu]
      K.piecewise (V i) (A.annulus.column i)) :
    (∫ p in K, (r * B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) +
      r⁻¹ * B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) / 2) ≤
      ∫ p in K, (r * B (f p) (V 0 p) (V 0 p) + r⁻¹ * B (f p) (V 1 p) (V 1 p)) / 2 := by
  have hE := m64VariableModulus_boundary_replacement_energy B hB hei hb r
    A.annulus C.annulus hK hKS f hf V hV hmap hcol
  rw [hE] at hminimum
  exact (add_le_add_iff_left _).mp (le_sub_iff_add_le.mp hminimum)

theorem boundary_local_energy_le
    (R : E →L[ℝ] LoopPlane)
    (A C : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v)
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.annulus.weightedEnergy B r ≤ C.annulus.weightedEnergy B r)
    {K : Set LoopPlane} [DecidablePred (· ∈ K)] (hK : MeasurableSet K) (hKS : K ⊆ S)
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hmap : C.annulus.map = K.piecewise f A.annulus.map)
    (hcol : ∀ i, (C.annulus.column i : LoopPlane → E) =ᵐ[mu]
      K.piecewise (V i) (A.annulus.column i)) :
    (∫ p in K, (B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) +
      B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) / 2) ≤
      (max r r⁻¹) ^ 2 *
        ∫ p in K, (B (f p) (V 0 p) (V 0 p) + B (f p) (V 1 p) (V 1 p)) / 2 := by
  have hlocal := weighted_boundary_local_energy_le R A C B hB hei hb r hminimum
    hK hKS f hf V hV hmap hcol
  have hD : 0 ≤ max r r⁻¹ := hr.le.trans (le_max_left _ _)
  have hold := (m64VariableModulus_integral_comparison
    ((A.annulus.column_energy_integrable B hB hei hb 0).mono_set hKS)
    ((A.annulus.column_energy_integrable B hB hei hb 1).mono_set hKS)
    (Eventually.of_forall fun p => hpos (A.annulus.map p) (A.annulus.column 0 p))
    (Eventually.of_forall fun p => hpos (A.annulus.map p) (A.annulus.column 1 p)) hr).1
  have hnew := (m64VariableModulus_integral_comparison
    (m64VariableModulus_column_integrable B hB hb f hf (V 0) (hV 0))
    (m64VariableModulus_column_integrable B hB hb f hf (V 1) (hV 1))
    (Eventually.of_forall fun p => hpos (f p) (V 0 p))
    (Eventually.of_forall fun p => hpos (f p) (V 1 p)) hr).2
  exact (hold.trans (mul_le_mul_of_nonneg_left hlocal hD)).trans
    ((mul_le_mul_of_nonneg_left hnew hD).trans_eq (by ring))

end M64FreeWeakPhaseAnnulus
end PoincareConjecture
