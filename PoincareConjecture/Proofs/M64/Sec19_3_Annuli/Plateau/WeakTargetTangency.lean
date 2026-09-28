import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedTangentProjection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MovingKernelWeakClosure











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "mu" => volume.restrict (interior m64AnnulusDomain)



theorem m64WeakAnnulus_tangent_closed
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) {c0 c1 : ℝ → M}
    (A : ℕ → M64ObservedWeakAnnulus (n := n) e c0 c1)
    (v : LoopPlane → M) (W : Lp E 2 mu) (i : Fin 2)
    (hweak : WeakConverges (fun j => (A j).column i) W)
    (hlim : ∀ᵐ p ∂mu, Tendsto (fun j => (A j).map p) atTop (𝓝 (v p))) :
    ∀ᵐ p ∂mu, W p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (v p)) := by
  obtain ⟨P, K, hP, hK, hb, hfix, hrange⟩ := m64ChartReadable_tangent_projection e he hread
  let R := fun j p => ContinuousLinearMap.id ℝ E - P ((A j).map p)
  let R0 := fun p => ContinuousLinearMap.id ℝ E - P (v p)
  have hR (j : ℕ) : AEStronglyMeasurable (R j) mu :=
    aestronglyMeasurable_const.sub
      (hP.comp_aestronglyMeasurable ((A j).map_aestronglyMeasurable hei))
  have hbound (j : ℕ) : ∀ᵐ p ∂mu, ‖R j p‖ ≤ 1 + K := Eventually.of_forall fun p =>
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (hb _))
  have hRlim : ∀ᵐ p ∂mu, Tendsto (fun j => R j p) atTop (𝓝 (R0 p)) := by
    filter_upwards [hlim] with p hp
    exact tendsto_const_nhds.sub ((hP.tendsto _).comp hp)
  have hzero (j : ℕ) : ∀ᵐ p ∂mu, R j p ((A j).column i p) = 0 := by
    filter_upwards [(A j).tangent i] with p hp
    obtain ⟨w, hw⟩ := hp
    change (A j).column i p - P ((A j).map p) ((A j).column i p) = 0
    have hfixed : P ((A j).map p) ((A j).column i p) = (A j).column i p := by
      rw [← hw]
      exact hfix _ _
    exact sub_eq_zero.mpr hfixed.symm
  have hz := m64MovingKernel_weak_closed R R0 hR (by positivity : 0 ≤ 1 + K)
    hbound hRlim hweak hzero
  filter_upwards [hz] with p hp
  change W p - P (v p) (W p) = 0 at hp
  have heq : P (v p) (W p) = W p := (sub_eq_zero.mp hp).symm
  simpa only [heq] using hrange (v p) (W p)

end PoincareConjecture
