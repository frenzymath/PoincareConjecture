import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Curvature.TerminalCurvatureSectionalScaling
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Metric.LocalPullbackRealization
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareLib.Geometry.Riemannian.Curvature.Euclidean
import PoincareLib.Geometry.Riemannian.Connection.ScalarJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.ScalarLowerBound.CurvatureOperator
import PoincareLib.Geometry.Riemannian.Curvature.IntrinsicCalculus

/-!
# Nonnegative operator from actual two-jets and vanishing sectional error

The fixed limit-orthonormal pair has source Gram determinants tending
to one. Local positive realizations preserve the same coordinate jets
and the actual retained curvature through their metric germs.
Source: terminal-germs-pinched-operator.md, Stage C.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-- Actual scalar two-jets and vanishing source sectional error give
the retained nonnegative operator on a Euclidean metric germ. -/
theorem terminalCurvature_operator_of_euclidean_jets
    {α : Type*} {l : Filter α} [l.NeBot]
    {gseq : α → RiemannianMetric 3 E} {g : RiemannianMetric 3 E}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g) (x : E)
    (hjet : ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin 3,
      Tendsto (fun k => iteratedFDeriv ℝ r (fun y => (gseq k).inner y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) x)))
    (hlower : ∀ eta : ℝ, 0 < eta → ∀ᶠ k in l, ∀ v w : E,
      -eta ≤ (Dseq k).sectionalCurvature x v w) :
    D.NonnegativeCurvatureOperator x := by
  obtain ⟨hzero, hone, htwo⟩ :=
    RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets x
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis hjet
  have hinner (v w : E) : Tendsto (fun k => (gseq k).inner x v w) l
      (𝓝 (g.inner x v w)) := by
    exact (ContinuousLinearMap.apply ℝ ℝ w).continuous.continuousAt.tendsto.comp
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).continuous.continuousAt.tendsto.comp hzero)
  have horth : ∀ v w : E, g.inner x v v = 1 → g.inner x w w = 1 →
      g.inner x v w = 0 → 0 ≤ D.sectionalCurvature x v w := by
    intro v w hv hw hvw
    have hnum := LeviCivitaData.tendsto_curvatureTensor_of_metric_jets
      Dseq D x v w v w hzero hone htwo
    have hgram := ((hinner v v).mul (hinner w w)).sub ((hinner v w).pow 2)
    have hnonzero : g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 ≠ 0 := by
      simp only [hv, hw, hvw]
      norm_num
    have hsectional : Tendsto (fun k => (Dseq k).sectionalCurvature x v w) l
        (𝓝 (D.sectionalCurvature x v w)) := hnum.div hgram hnonzero
    apply le_of_forall_pos_le_add
    intro eta heta
    have hle : -eta ≤ D.sectionalCurvature x v w :=
      ge_of_tendsto hsectional ((hlower eta heta).mono fun k hk => hk v w)
    linarith
  exact D.nonnegativeCurvatureOperator_of_nonnegative_sectional_three
    D.intrinsicCurvatureTensorCalculus x
    (D.curvatureTensor_diagonal_nonneg_of_orthonormal x horth)

/-- Coordinate jets suffice on the original manifold, with all local
metric and connection realizations constructed from the actual germs. -/
theorem terminalCurvature_operator_of_coordinate_jets
    {α : Type*} {l : Filter α} [l.NeBot]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {gseq : α → RiemannianMetric 3 M} {g : RiemannianMetric 3 M}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g) (x : M)
    (hjet : ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin 3,
      Tendsto (fun k => iteratedFDeriv ℝ r
        (fun y => (gseq k).pullbackCoefficients (extChartAt (𝓡 3) x).symm y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
          (extChartAt (𝓡 3) x x)) l
        (𝓝 (iteratedFDeriv ℝ r
          (fun y => g.pullbackCoefficients (extChartAt (𝓡 3) x).symm y
            (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
          (extChartAt (𝓡 3) x x))))
    (hlower : ∀ eta : ℝ, 0 < eta → ∀ᶠ k in l, ∀ (y : M)
      (v w : TangentSpace (𝓡 3) y), -eta ≤ (Dseq k).sectionalCurvature y v w) :
    D.NonnegativeCurvatureOperator x := by
  classical
  let c := extChartAt (𝓡 3) x
  let p := c x
  have hp : p ∈ c.target := mem_extChartAt_target x
  have hc : IsOpen c.target := isOpen_extChartAt_target x
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target :=
    fun y hy => contMDiffWithinAt_extChartAt_symm_target x hy
  have hinj (y : E) (hy : y ∈ c.target) :
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) c.symm y) := by
    have h := isInvertible_mfderivWithin_extChartAt_symm hy
    rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
    exact h.injective
  choose G DG V hVo hpV hVU hcoeff using fun k =>
    (gseq k).exists_local_immersive_pullback_realization c.symm hc hp hf hinj
  obtain ⟨gE, DE, Z, hZo, hpZ, hZU, hE⟩ :=
    g.exists_local_immersive_pullback_realization c.symm hc hp hf hinj
  have hgj (h : RiemannianMetric 3 E) (g' : RiemannianMetric 3 M)
      (heq : h.euclideanCoefficients =ᶠ[𝓝 p] g'.pullbackCoefficients c.symm)
      (r : ℕ) (a b : Fin 3) :
      iteratedFDeriv ℝ r (fun y => h.inner y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p =
        iteratedFDeriv ℝ r (fun y => g'.pullbackCoefficients c.symm y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p := by
    have heq' : (fun y => h.inner y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 p]
        (fun y => g'.pullbackCoefficients c.symm y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) :=
      heq.mono fun y hy => congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ =>
        B (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) hy
    exact (heq'.iteratedFDeriv ℝ r).self_of_nhds
  have hseqgerm (k : α) : (G k).euclideanCoefficients =ᶠ[𝓝 p]
      (gseq k).pullbackCoefficients c.symm :=
    Filter.mem_of_superset ((hVo k).mem_nhds (hpV k)) (hcoeff k)
  have hEgerm : gE.euclideanCoefficients =ᶠ[𝓝 p] g.pullbackCoefficients c.symm :=
    Filter.mem_of_superset (hZo.mem_nhds hpZ) hE
  have hjetE : ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin 3,
      Tendsto (fun k => iteratedFDeriv ℝ r (fun y => (G k).inner y
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => gE.inner y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p)) := by
    intro r hr a b
    simpa only [hgj (G _) _ (hseqgerm _) r a b, hgj gE g hEgerm r a b]
      using hjet r hr a b
  have hlowerE : ∀ eta : ℝ, 0 < eta → ∀ᶠ k in l, ∀ v w : E,
      -eta ≤ (DG k).sectionalCurvature p v w := by
    intro eta heta
    filter_upwards [hlower eta heta] with k hk v w
    rw [M36.sectionalCurvature_eq_of_local_isometry (DG k) (Dseq k)
      (hVo k) (hf.mono (hVU k)) (fun y hy a b =>
        congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B a b) (hcoeff k y hy)) (hpV k) v w]
    exact hk _ _ _
  have hoperator := terminalCurvature_operator_of_euclidean_jets DG DE p hjetE hlowerE
  have htarget := (DE.nonnegativeCurvatureOperator_iff_of_local_isometry D
    (f := c.symm) (U := Z) hZo (hf.mono hZU) (fun y hy a b =>
      congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B a b) (hE y hy)) hpZ).mp hoperator
  have hpx : c.symm p = x := c.left_inv (mem_extChartAt_source x)
  exact hpx ▸ htarget

end PoincareMT.M47
