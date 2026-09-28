import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusEnergy
import Mathlib.Analysis.Calculus.LocalExtr.Basic









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain




theorem hasDerivAt_weightedEnergy
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => A.weightedEnergy B s)
      ((∫ p in S, B (A.map p) (A.column 0 p) (A.column 0 p)) / 2 -
        (∫ p in S, B (A.map p) (A.column 1 p) (A.column 1 p)) / (2 * r ^ 2)) r := by
  let E0 := ∫ p in S, B (A.map p) (A.column 0 p) (A.column 0 p)
  let E1 := ∫ p in S, B (A.map p) (A.column 1 p) (A.column 1 p)
  have hd := (((hasDerivAt_id r).div_const 2).mul_const E0).add
    (((hasDerivAt_inv hr.ne').div_const 2).mul_const E1)
  convert! hd using 1
  · funext s
    exact A.weightedEnergy_eq_column_integrals B hB hei hb s
  · dsimp only [E0, E1]
    ring




theorem weightedEnergy_modulus_balance
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : ∀ s : ℝ, 0 < s → A.weightedEnergy B r ≤ A.weightedEnergy B s) :
    r * (∫ p in S, B (A.map p) (A.column 0 p) (A.column 0 p)) =
      r⁻¹ * (∫ p in S, B (A.map p) (A.column 1 p) (A.column 1 p)) := by
  have hlocal : IsLocalMin (fun s => A.weightedEnergy B s) r := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact hminimum s hs
  have hz := hlocal.hasDerivAt_eq_zero (A.hasDerivAt_weightedEnergy B hB hei hb hr)
  field_simp at hz ⊢
  nlinarith

end PoincareConjecture.M64ObservedWeakAnnulus
