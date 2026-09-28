import PoincareConjecture.Proofs.M47.CanonicalNeckSpatialBounds
import PoincareConjecture.Proofs.M47.CanonicalNeckAxialCompression
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistencePullbackSmooth
import PoincareConjecture.Proofs.M34.Mathlib.LinearPrecomposeLocalJets
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates

theorem neck_metric_axial_jet_difference_bound
    {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
    [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {g0 : RiemannianMetric 3 M} (N : EpsilonNeck g0)
    {R : ℝ} (hR : R < N.epsilon⁻¹) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t ∈ Icc a b, ∀ q : UnitTwoSphere,
      ∀ z1 ∈ Icc (-R) R, ∀ z2 ∈ Icc (-R) R, ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
              (chartAt E₂ q) y i l) (0, z1) -
          iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
              (chartAt E₂ q) y i l) (0, z2)‖ ≤ B * |z1 - z2| := by
  obtain ⟨B, hB, hbound⟩ := neck_metric_jets_bounded_on_closed_cylinder hab F N hR (m + 1)
  refine ⟨B, hB, ?_⟩
  intro t ht q z1 hz1 z2 hz2 j hj i l
  let f : V → ℝ := fun y =>
    roundCylinderTensorCoefficient (roundCylinderPullback (F.metric t) N.coordinate_map)
      (chartAt E₂ q) y i l
  let K : Set V := ({0} : Set E₂) ×ˢ Icc (-R) R
  have hconvex : Convex ℝ K := (convex_singleton (0 : E₂)).prod (convex_Icc _ _)
  have hsmooth (x : V) (hx : x ∈ K) : ContDiffAt ℝ ∞ f x := by
    have haxis : x.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨(neg_lt_neg hR).trans_le hx.2.1, hx.2.2.trans_lt hR⟩
    apply (capPersistence_roundCylinderTensorSmoothOn_pullback
      (F.metric t) N.coordinate_map_smooth q i l).contDiffAt
    apply ((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds
    exact ⟨by rw [roundCylinder_sphereChart_target]; trivial, haxis⟩
  have hdiff (x : V) (hx : x ∈ K) : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
    ((hsmooth x hx).of_le (show ((j + 1 : ℕ) : ℕ∞ω) ≤ ∞ from
      by exact_mod_cast le_top)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_self j)
  have hderiv (x : V) (hx : x ∈ K) : ‖fderiv ℝ (iteratedFDeriv ℝ j f) x‖ ≤ B := by
    rcases x with ⟨v, z⟩
    have hv : v = 0 := hx.1
    subst v
    rw [norm_fderiv_iteratedFDeriv]
    exact hbound t ht q z hx.2 (j + 1) (by omega) i l
  have h := hconvex.norm_image_sub_le_of_norm_fderiv_le hdiff hderiv
    (show (0, z2) ∈ K from ⟨rfl, hz2⟩) (show (0, z1) ∈ K from ⟨rfl, hz1⟩)
  simpa [Prod.norm_def, Real.norm_eq_abs] using h

theorem norm_neckAxialLinearMap_le_one {lambda : ℝ} (hlambda : lambda ∈ Icc 0 1) :
    ‖neckAxialLinearMap lambda‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have haxis : |lambda * x.2| ≤ |x.2| := by
    rw [abs_mul, abs_of_nonneg hlambda.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hlambda.2 (abs_nonneg x.2)
  calc
    _ = max ‖x.1‖ |lambda * x.2| := by simp [neckAxialLinearMap, Prod.norm_def, Real.norm_eq_abs]
    _ ≤ max ‖x.1‖ |x.2| := max_le_max le_rfl haxis
    _ = 1 * ‖x‖ := by simp [Prod.norm_def, Real.norm_eq_abs]

theorem norm_iteratedFDeriv_neck_axial_difference_le
    (lambda c : ℝ) (f : V → ℝ) (x : V) (j : ℕ)
    (hc : ContDiffAt ℝ ∞ f (neckAxialCoordinate lambda c x))
    (h0 : ContDiffAt ℝ ∞ f (neckAxialCoordinate lambda 0 x)) :
    ‖iteratedFDeriv ℝ j (fun y => f (neckAxialCoordinate lambda c y) -
        f (neckAxialCoordinate lambda 0 y)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (neckAxialCoordinate lambda c x) -
        iteratedFDeriv ℝ j f (neckAxialCoordinate lambda 0 x)‖ *
          ‖neckAxialLinearMap lambda‖ ^ j := by
  let L := neckAxialLinearMap lambda
  let H : V → ℝ := fun y => f (y + (0, c)) - f y
  have hplus : L x + (0, c) = neckAxialCoordinate lambda c x := by
    ext <;> simp [L, neckAxialLinearMap, neckAxialCoordinate]
  have hzero : L x = neckAxialCoordinate lambda 0 x := by
    ext <;> simp [L, neckAxialLinearMap, neckAxialCoordinate]
  have hc' : ContDiffAt ℝ ∞ f (L x + (0, c)) := by rw [hplus]; exact hc
  have h0' : ContDiffAt ℝ ∞ f (L x) := by rw [hzero]; exact h0
  have hshift : ContDiffAt ℝ ∞ (fun y : V => f (y + (0, c))) (L x) :=
    hc'.comp (L x) (contDiffAt_id.add contDiffAt_const)
  have hjet : iteratedFDeriv ℝ j H (L x) =
      iteratedFDeriv ℝ j f (neckAxialCoordinate lambda c x) -
        iteratedFDeriv ℝ j f (neckAxialCoordinate lambda 0 x) := by
    change iteratedFDeriv ℝ j ((fun y : V => f (y + (0, c))) - f) (L x) = _
    rw [iteratedFDeriv_sub_apply (hshift.of_le (by exact_mod_cast le_top))
      (h0'.of_le (by exact_mod_cast le_top)), iteratedFDeriv_comp_add_right, hplus, hzero]
  have heq : (fun y => f (neckAxialCoordinate lambda c y) -
      f (neckAxialCoordinate lambda 0 y)) = H ∘ L := by
    funext y
    simp [H, L, neckAxialLinearMap, neckAxialCoordinate]
  rw [heq]
  have h := L.norm_iteratedFDeriv_comp_right_of_contDiffAt
    ((hshift.sub h0').of_le (by exact_mod_cast le_top) : ContDiffAt ℝ (j : ℕ∞ω) H (L x))
  change ‖iteratedFDeriv ℝ j (H ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j H (L x)‖ * ‖L‖ ^ j at h
  rw [hjet] at h
  exact h

end PoincareConjecture.Proofs.M47
