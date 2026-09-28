import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Spherical.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereCurvature







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture

private theorem gram_ne_zero_of_rescaled {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c) (x : M)
    (u v : TangentSpace (𝓡 n) x)
    (hgram : (rescaledMetric g c hc).inner x u u * (rescaledMetric g c hc).inner x v v -
      ((rescaledMetric g c hc).inner x u v) ^ 2 ≠ 0) :
    g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 := by
  intro h
  apply hgram
  simp only [rescaledMetric_inner]
  calc
    _ = c ^ 2 * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by ring
    _ = 0 := by rw [h, mul_zero]

namespace CompactRoundShrinkingModel

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}


def unitMetric (_C : CompactRoundShrinkingModel G) : RiemannianMetric 3 M :=
  rescaledMetric S.metric (1 / 4) (by norm_num)

theorem unitMetric_sectionalCurvature (C : CompactRoundShrinkingModel G)
    (x : M) (u v : TangentSpace (𝓡 3) x)
    (hgram : C.unitMetric.inner x u u * C.unitMetric.inner x v v -
      (C.unitMetric.inner x u v) ^ 2 ≠ 0) :
    C.unitMetric.leviCivitaData.sectionalCurvature x u v = 1 := by
  let D := rescaledMetric_connection S.metric S.connection (1 / 4) (by norm_num)
  have heq : C.unitMetric.leviCivitaData.sectionalCurvature x u v =
      D.sectionalCurvature x u v := by
    simp only [LeviCivitaData.sectionalCurvature,
      C.unitMetric.leviCivitaData.horizon_curvatureTensor_eq D]
    rfl
  rw [heq, rescaledMetric_sectionalCurvature, C.soliton_sectionalCurvature x u v
    (gram_ne_zero_of_rescaled S.metric (1 / 4) (by norm_num) x u v hgram)]
  norm_num


theorem inner_pullback_eq_round_scale (C : CompactRoundShrinkingModel G)
    (q : UnitSphere 3 → M)
    (hq : ∀ x : UnitSphere 3, ∀ u v : TangentSpace (𝓡 3) x,
      C.unitMetric.inner (q x) (mfderiv (𝓡 3) (𝓡 3) q x u)
        (mfderiv (𝓡 3) (𝓡 3) q x v) = (roundSphereMetric 3).inner x u v)
    (t : ℝ) (ht : t < 0) (x : UnitSphere 3) (u v : TangentSpace (𝓡 3) x) :
    (G.flow.metric t).inner (q x) (mfderiv (𝓡 3) (𝓡 3) q x u)
      (mfderiv (𝓡 3) (𝓡 3) q x v) = (-4 * t) * (roundSphereMetric 3).inner x u v := by
  rw [C.inner_eq_neg_time_mul t ht]
  have h := hq x u v
  change (1 / 4 : ℝ) * S.metric.inner (q x) (mfderiv (𝓡 3) (𝓡 3) q x u)
    (mfderiv (𝓡 3) (𝓡 3) q x v) = (roundSphereMetric 3).inner x u v at h
  rw [← h]
  ring

end CompactRoundShrinkingModel

namespace SphericalShrinkingMetric


def scale (t : ℝ) : ℝ := if t < 0 then -4 * t else 1

theorem scale_pos (t : ℝ) : 0 < scale t := by
  unfold scale
  split_ifs with ht
  · nlinarith
  · norm_num

def metric (t : ℝ) : RiemannianMetric 3 (UnitSphere 3) :=
  rescaledMetric (roundSphereMetric 3) (scale t) (scale_pos t)

def connection (t : ℝ) : LeviCivitaData (metric t) :=
  rescaledMetric_connection (roundSphereMetric 3) (roundSphereMetric 3).leviCivitaData
    (scale t) (scale_pos t)

theorem inner (t : ℝ) (ht : t < 0) (x : UnitSphere 3)
    (u v : TangentSpace (𝓡 3) x) :
    (metric t).inner x u v = (-4 * t) * (roundSphereMetric 3).inner x u v := by
  simp only [metric, rescaledMetric_inner, scale, if_pos ht]

theorem round (t : ℝ) : ConstantPositiveSectionalCurvature (metric t) (connection t) := by
  refine ⟨(scale t)⁻¹, inv_pos.mpr (scale_pos t), fun x u v hu hv huv => ?_⟩
  have hgram : (metric t).inner x u u * (metric t).inner x v v -
      ((metric t).inner x u v) ^ 2 ≠ 0 := by rw [hu, hv, huv]; norm_num
  have hbase := gram_ne_zero_of_rescaled (roundSphereMetric 3) (scale t)
    (scale_pos t) x u v hgram
  rw [connection, rescaledMetric_sectionalCurvature,
    roundSphereMetric_unit_sectionalCurvature x u v hbase, mul_one]

end SphericalShrinkingMetric

end PoincareConjecture
