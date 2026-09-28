import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Product.Certificate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometrySectional

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow.Splitting.RoundCylinderSurface

def scale (t : ℝ) : ℝ := if t < 0 then -2 * t else 1

theorem scale_pos (t : ℝ) : 0 < scale t := by
  unfold scale
  split_ifs with ht
  · linarith
  · norm_num

def sphereMetric (t : ℝ) : RiemannianMetric 2 (UnitSphere 2) :=
  rescaledMetric (roundSphereMetric 2) (scale t) (scale_pos t)

def sphereConnection (t : ℝ) : LeviCivitaData (sphereMetric t) :=
  rescaledMetric_connection (roundSphereMetric 2) (roundSphereMetric 2).leviCivitaData
    (scale t) (scale_pos t)

theorem sphere_round (t : ℝ) :
    ConstantPositiveSectionalCurvature (sphereMetric t) (sphereConnection t) := by
  refine ⟨(scale t)⁻¹, inv_pos.mpr (scale_pos t), fun x u v hu hv huv => ?_⟩
  have hgram : (roundSphereMetric 2).inner x u u * (roundSphereMetric 2).inner x v v -
      ((roundSphereMetric 2).inner x u v) ^ 2 ≠ 0 := by
    intro hzero
    change scale t * (roundSphereMetric 2).inner x u u = 1 at hu
    change scale t * (roundSphereMetric 2).inner x v v = 1 at hv
    change scale t * (roundSphereMetric 2).inner x u v = 0 at huv
    have hh : (scale t * (roundSphereMetric 2).inner x u u) *
        (scale t * (roundSphereMetric 2).inner x v v) -
        (scale t * (roundSphereMetric 2).inner x u v) ^ 2 = 0 := by
      calc
        _ = scale t ^ 2 * ((roundSphereMetric 2).inner x u u *
            (roundSphereMetric 2).inner x v v -
            ((roundSphereMetric 2).inner x u v) ^ 2) := by ring
        _ = 0 := by rw [hzero, mul_zero]
    rw [hu, hv, huv] at hh
    norm_num at hh
  rw [sphereConnection, rescaledMetric_sectionalCurvature,
    roundSphereMetric_unit_sectionalCurvature x u v hgram, mul_one]

variable {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]
  (s : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)

def metric (t : ℝ) : RiemannianMetric 2 N :=
  (sphereMetric t).pullbackOfLocalDiffeomorph s s.isLocalDiffeomorph

def connection (t : ℝ) : LeviCivitaData (metric s t) := (metric s t).leviCivitaData

theorem inner (t : ℝ) (ht : t < 0) (x : N) (u v : TangentSpace (𝓡 2) x) :
    (metric s t).inner x u v = (-2 * t) * inner ℝ
      (mfderiv (𝓡 2) (𝓡 3) (fun y : N => (s y).1) x u)
      (mfderiv (𝓡 2) (𝓡 3) (fun y : N => (s y).1) x v) := by
  change scale t * (roundSphereMetric 2).inner (s x)
    (mfderiv (𝓡 2) (𝓡 2) s x u) (mfderiv (𝓡 2) (𝓡 2) s x v) = _
  rw [scale, if_pos ht, roundSphereMetric_inner]
  have hi : ContMDiff (𝓡 2) (𝓡 3) ∞
      (Subtype.val : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) := contMDiff_coe_sphere
  have hd := mfderiv_comp x
    (hi.mdifferentiable (by simp) (s x))
    (s.contMDiff.mdifferentiable (by simp) x)
  change mfderiv (𝓡 2) (𝓡 3) (fun y : N => (s y).1) x = _ at hd
  rw [hd]
  rfl

theorem round (t : ℝ) : ConstantPositiveSectionalCurvature (metric s t) (connection s t) := by
  obtain ⟨c, hc, hsec⟩ := sphere_round t
  refine ⟨c, hc, fun x u v hu hv huv => ?_⟩
  rw [(connection s t).sectionalCurvature_eq_of_local_isometry (sphereConnection t)
    isOpen_univ s.contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)]
  exact hsec (s x) _ _ hu hv huv

variable {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]

def productData
    (e : P ≃ₘ⟮𝓡 3, (𝓡 2).prod 𝓘(ℝ, ℝ)⟯ (N × ℝ)) :
    SphereLineProductData (P := P) :=
  sphereLineProductDataOfSurface s (metric s) (connection s)
    (fun t _ => round s t) (inner s) e

end PoincareConjecture.RicciFlow.Splitting.RoundCylinderSurface
