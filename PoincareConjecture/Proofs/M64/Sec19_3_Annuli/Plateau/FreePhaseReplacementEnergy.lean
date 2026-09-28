import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusReplacement









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S



theorem weighted_local_energy_le_of_replacement
    (A C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hC0 : C.label0 = A.label0) (hC1 : C.label1 = A.label1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ B q v v)
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.annulus.weightedEnergy B r ≤ C.annulus.weightedEnergy B r)
    {K : Set LoopPlane} (hK : MeasurableSet K) (hKS : K ⊆ S)
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hmap : C.annulus.map = K.piecewise f A.annulus.map)
    (hcol : ∀ i, (C.annulus.column i : LoopPlane → E) =ᵐ[mu]
      K.piecewise (V i) (A.annulus.column i)) :
    (∫ p in K, (B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) +
      B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) / 2) ≤
      (max r r⁻¹) ^ 2 *
        ∫ p in K, (B (f p) (V 0 p) (V 0 p) + B (f p) (V 1 p) (V 1 p)) / 2 := by
  let W : M64ObservedWeakAnnulus (n := n) e (c0 ∘ A.label0) (c1 ∘ A.label1) := {
    C.annulus with
    boundary := fun phi hp => by simpa only [hC0, hC1] using C.annulus.boundary phi hp }
  have hE := m64VariableModulus_replacement_energy B hB hei hb r A.annulus W hK hKS
    f hf V hV hmap hcol
  have hlocal : (∫ p in K, (r * B (A.annulus.map p)
        (A.annulus.column 0 p) (A.annulus.column 0 p) +
        r⁻¹ * B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) / 2) ≤
      ∫ p in K, (r * B (f p) (V 0 p) (V 0 p) + r⁻¹ * B (f p) (V 1 p) (V 1 p)) / 2 := by
    change C.annulus.weightedEnergy B r = _ at hE
    linarith
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

end PoincareConjecture.M64FreeWeakPhaseAnnulus
