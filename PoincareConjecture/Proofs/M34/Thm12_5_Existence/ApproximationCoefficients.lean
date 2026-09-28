import PoincareConjecture.Proofs.M34.Thm12_5_Existence.CompactApproximation
import PoincareConjecture.Proofs.M34.Standard.ClosedPullbackCoefficients
import PoincareConjecture.Proofs.M34.Mathlib.ParameterSpatialDerivatives
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34



def compactCapSource (g0 : StandardInitialMetric) (k : ℕ) : Set StandardCapSpace :=
  endTruncation g0.cylindrical_end (compactCapHeight k + 1)



theorem compactCapSource_isOpen (g0 : StandardInitialMetric) (k : ℕ) :
    IsOpen (compactCapSource g0 k) :=
  endTruncation_isOpen _ (by linarith [compactCapHeight_gt_one k])



noncomputable def compactCapChart (g0 : StandardInitialMetric) (k : ℕ) :
    StandardCapSpace → CompactCapDouble g0 k :=
  endDoubleParametrization g0.cylindrical_end (compactCapHeight_gt_one k) false



theorem compactCapChart_contMDiffOn (g0 : StandardInitialMetric) (k : ℕ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (compactCapChart g0 k) (compactCapSource g0 k) :=
  endDoubleParametrization_contMDiffOn _ _ _



theorem compactCapChart_mfderiv_isInvertible (g0 : StandardInitialMetric) (k : ℕ)
    {x : StandardCapSpace} (hx : x ∈ compactCapSource g0 k) :
    (mfderiv (𝓡 3) (𝓡 3) (compactCapChart g0 k) x).IsInvertible :=
  endDoubleParametrization_mfderiv_isInvertible _ _ _ hx

namespace CompactCapApproximation

variable {g0 : StandardInitialMetric} (A : CompactCapApproximation g0)



noncomputable def coefficients (k : ℕ) (t : ℝ) (x : StandardCapSpace) :
    StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
  ((A.flow k).metric t).pullbackCoefficients (compactCapChart g0 k) x



theorem contDiffOn_coefficients (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × StandardCapSpace => A.coefficients k p.1 p.2)
      (Icc 0 A.time ×ˢ compactCapSource g0 k) :=
  (A.flow k).smooth.contDiffOn_spacetime_pullbackCoefficients
    (compactCapSource_isOpen g0 k) (compactCapChart_contMDiffOn g0 k)



theorem contDiffOn_spatialJet (k m : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × StandardCapSpace => iteratedFDeriv ℝ m (A.coefficients k p.1) p.2)
      (Icc 0 A.time ×ˢ compactCapSource g0 k) :=
  (A.contDiffOn_coefficients k).iteratedFDeriv_snd_of_isOpen
    (compactCapSource_isOpen g0 k) m



theorem continuousOn_spatialJet_time (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ compactCapSource g0 k) :
    ContinuousOn (fun t => iteratedFDeriv ℝ m (A.coefficients k t) x) (Icc 0 A.time) := by
  have hi : ContDiffOn ℝ ∞ (fun t : ℝ => (t, x)) (Icc 0 A.time) :=
    contDiffOn_id.prodMk contDiffOn_const
  have hmaps : MapsTo (fun t : ℝ => (t, x)) (Icc 0 A.time)
      (Icc 0 A.time ×ˢ compactCapSource g0 k) := fun _ ht => ⟨ht, hx⟩
  exact ((A.contDiffOn_spatialJet k m).comp hi hmaps).continuousOn



theorem differentiableAt_spatialJet_time (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ compactCapSource g0 k) {t : ℝ} (ht : t ∈ Ioo 0 A.time) :
    DifferentiableAt ℝ (fun s => iteratedFDeriv ℝ m (A.coefficients k s) x) t := by
  have hjoint := (A.contDiffOn_spatialJet k m).mono
    (prod_mono Ioo_subset_Icc_self (Subset.refl _))
  exact ((hjoint.contDiffAt
    ((isOpen_Ioo.prod (compactCapSource_isOpen g0 k)).mem_nhds ⟨ht, hx⟩)).comp t
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

set_option backward.isDefEq.respectTransparency false in


theorem coefficients_zero (k : ℕ) {x : StandardCapSpace}
    (hx : x ∈ compactCapSource g0 k) :
    A.coefficients k 0 x = g0.metric.euclideanCoefficients x := by
  unfold coefficients
  rw [A.initial_metric]
  ext u v
  exact (endDoubleParametrization_metric g0.cylindrical_end
    (compactCapHeight_gt_one k) false hx u v).symm



theorem spatialJet_zero (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ compactCapSource g0 k) :
    iteratedFDeriv ℝ m (A.coefficients k 0) x =
      iteratedFDeriv ℝ m g0.metric.euclideanCoefficients x := by
  have heq : A.coefficients k 0 =ᶠ[𝓝 x] g0.metric.euclideanCoefficients := by
    filter_upwards [(compactCapSource_isOpen g0 k).mem_nhds hx] with y hy
    exact A.coefficients_zero k hy
  exact (heq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds

end CompactCapApproximation
end PoincareConjecture.M34
