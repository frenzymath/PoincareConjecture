import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Limits.CompactApproximation
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Coordinates.ClosedPullbackCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.ParameterSpatialDerivatives
import PoincareLib.Geometry.Riemannian.Connection.Euclidean

/-!
# Fixed-coordinate coefficients of the compact cap approximations

All coefficients use the same original cap coordinates. Their spatial
jets are jointly smooth through the initial endpoint and agree there
with the supplied initial metric. This is the fixed-coordinate stage of
Morgan-Tian Theorem 12.5, p. 297; see fixed-chart-endpoint.md.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

/-- The open original-cap source of the k-th fixed parametrization
(Theorem 12.5, p. 297). -/
def compactCapSource (g0 : StandardInitialMetric) (k : ℕ) : Set StandardCapSpace :=
  endTruncation g0.cylindrical_end (compactCapHeight k + 1)

/-- The approximation sources are open in the original cap
(Theorem 12.5, p. 297). -/
theorem compactCapSource_isOpen (g0 : StandardInitialMetric) (k : ℕ) :
    IsOpen (compactCapSource g0 k) :=
  endTruncation_isOpen _ (by linarith [compactCapHeight_gt_one k])

/-- The false-copy map identifies a growing part of the original cap
with each compact double (Theorem 12.5, p. 297). -/
noncomputable def compactCapChart (g0 : StandardInitialMetric) (k : ℕ) :
    StandardCapSpace → CompactCapDouble g0 k :=
  endDoubleParametrization g0.cylindrical_end (compactCapHeight_gt_one k) false

/-- These fixed maps are smooth on their actual open sources
(Theorem 12.5, p. 297). -/
theorem compactCapChart_contMDiffOn (g0 : StandardInitialMetric) (k : ℕ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (compactCapChart g0 k) (compactCapSource g0 k) :=
  endDoubleParametrization_contMDiffOn _ _ _

/-- These coordinate differentials are invertible on their sources
(Theorem 12.5, p. 297). -/
theorem compactCapChart_mfderiv_isInvertible (g0 : StandardInitialMetric) (k : ℕ)
    {x : StandardCapSpace} (hx : x ∈ compactCapSource g0 k) :
    (mfderiv (𝓡 3) (𝓡 3) (compactCapChart g0 k) x).IsInvertible :=
  endDoubleParametrization_mfderiv_isInvertible _ _ _ hx

namespace CompactCapApproximation

variable {g0 : StandardInitialMetric} (A : CompactCapApproximation g0)

/-- The evolving bilinear metric in the fixed original-cap coordinates
(Theorem 12.5, p. 297). -/
noncomputable def coefficients (k : ℕ) (t : ℝ) (x : StandardCapSpace) :
    StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
  ((A.flow k).metric t).pullbackCoefficients (compactCapChart g0 k) x

/-- The pulled-back family is jointly smooth on its closed time slab
(Theorem 12.5, p. 297). -/
theorem contDiffOn_coefficients (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × StandardCapSpace => A.coefficients k p.1 p.2)
      (Icc 0 A.time ×ˢ compactCapSource g0 k) :=
  (A.flow k).smooth.contDiffOn_spacetime_pullbackCoefficients
    (compactCapSource_isOpen g0 k) (compactCapChart_contMDiffOn g0 k)

/-- Every spatial jet is jointly smooth within the same closed time slab
(Theorem 12.5, p. 297). -/
theorem contDiffOn_spatialJet (k m : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × StandardCapSpace => iteratedFDeriv ℝ m (A.coefficients k p.1) p.2)
      (Icc 0 A.time ×ˢ compactCapSource g0 k) :=
  (A.contDiffOn_coefficients k).iteratedFDeriv_snd_of_isOpen
    (compactCapSource_isOpen g0 k) m

/-- Spatial jets are continuous in time through both included endpoints
(Theorem 12.5, p. 297). -/
theorem continuousOn_spatialJet_time (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ compactCapSource g0 k) :
    ContinuousOn (fun t => iteratedFDeriv ℝ m (A.coefficients k t) x) (Icc 0 A.time) := by
  have hi : ContDiffOn ℝ ∞ (fun t : ℝ => (t, x)) (Icc 0 A.time) :=
    contDiffOn_id.prodMk contDiffOn_const
  have hmaps : MapsTo (fun t : ℝ => (t, x)) (Icc 0 A.time)
      (Icc 0 A.time ×ˢ compactCapSource g0 k) := fun _ ht => ⟨ht, hx⟩
  exact ((A.contDiffOn_spatialJet k m).comp hi hmaps).continuousOn

/-- At interior times the spatial jets have ordinary time derivatives
(Theorem 12.5, p. 297). -/
theorem differentiableAt_spatialJet_time (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ compactCapSource g0 k) {t : ℝ} (ht : t ∈ Ioo 0 A.time) :
    DifferentiableAt ℝ (fun s => iteratedFDeriv ℝ m (A.coefficients k s) x) t := by
  have hjoint := (A.contDiffOn_spatialJet k m).mono
    (prod_mono Ioo_subset_Icc_self (Subset.refl _))
  exact ((hjoint.contDiffAt
    ((isOpen_Ioo.prod (compactCapSource_isOpen g0 k)).mem_nhds ⟨ht, hx⟩)).comp t
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The initial coefficients are exactly those of the supplied metric
(Theorem 12.5, p. 297). -/
theorem coefficients_zero (k : ℕ) {x : StandardCapSpace}
    (hx : x ∈ compactCapSource g0 k) :
    A.coefficients k 0 x = g0.metric.euclideanCoefficients x := by
  unfold coefficients
  rw [A.initial_metric]
  ext u v
  exact (endDoubleParametrization_metric g0.cylindrical_end
    (compactCapHeight_gt_one k) false hx u v).symm

/-- All initial spatial jets agree, since the initial coefficients agree
on an open neighborhood (Theorem 12.5, p. 297). -/
theorem spatialJet_zero (k m : ℕ) {x : StandardCapSpace}
    (hx : x ∈ compactCapSource g0 k) :
    iteratedFDeriv ℝ m (A.coefficients k 0) x =
      iteratedFDeriv ℝ m g0.metric.euclideanCoefficients x := by
  have heq : A.coefficients k 0 =ᶠ[𝓝 x] g0.metric.euclideanCoefficients := by
    filter_upwards [(compactCapSource_isOpen g0 k).mem_nhds hx] with y hy
    exact A.coefficients_zero k hy
  exact (heq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds

end CompactCapApproximation
end PoincareMT.M34
