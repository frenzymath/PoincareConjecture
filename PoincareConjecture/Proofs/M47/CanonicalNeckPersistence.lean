import PoincareConjecture.Proofs.M47.CanonicalNeckNormalization
import PoincareConjecture.Statements.Ch04.CurvatureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem exists_neck_of_normalized_comparison
    {g h : RiemannianMetric 3 M} (N : EpsilonNeck g) (D : LeviCivitaData h)
    (hR : 0 < D.scalarCurvature N.center)
    (hclose : RoundCylinderClose N.epsilon 0 (fun z v w =>
      D.scalarCurvature N.center * roundCylinderPullback h N.coordinate_map z v w)) :
    ∃ N' : EpsilonNeck h, N'.epsilon = N.epsilon ∧ N'.center = N.center ∧
      N'.carrier = N.carrier ∧ N'.coordinate_map = N.coordinate_map ∧
      N'.coordinate_inverse = N.coordinate_inverse ∧ N'.central_sphere = N.central_sphere ∧
      N'.connection = D ∧ HEq N'.coordinate N.coordinate := by
  have hscale : (D.scalarCurvature N.center ^ (-1 / 2 : ℝ))⁻¹ ^ 2 =
      D.scalarCurvature N.center := by
    rw [inv_pow, ← Real.rpow_mul_natCast hR.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  let N' : EpsilonNeck h := {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scale := D.scalarCurvature N.center ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hR _
    center := N.center
    connection := D
    scalar_center_pos := hR
    scale_eq_scalar := rfl
    carrier := N.carrier
    carrier_open := N.carrier_open
    coordinate := N.coordinate
    coordinate_map := N.coordinate_map
    coordinate_map_eq := N.coordinate_map_eq
    coordinate_map_smooth := N.coordinate_map_smooth
    coordinate_inverse := N.coordinate_inverse
    coordinate_inverse_mem := N.coordinate_inverse_mem
    coordinate_inverse_left := N.coordinate_inverse_left
    coordinate_inverse_right := N.coordinate_inverse_right
    coordinate_inverse_smooth := N.coordinate_inverse_smooth
    central_sphere := N.central_sphere
    central_sphere_eq := N.central_sphere_eq
    center_on_central_sphere := N.center_on_central_sphere
    central_sphere_subset := N.central_sphere_subset
    metric_comparison := ⟨by simpa only [hscale] using hclose⟩ }
  exact ⟨N', rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩

theorem continuous_scalar_at_fixed_point
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow 3 M J) (x : M) :
    Continuous (fun s : J => (F.connection s.val).scalarCurvature x) := by
  have hmap : Continuous (fun s : J => (s.val, x)) :=
    continuous_subtype_val.prodMk continuous_const
  have hscalar : ContinuousOn
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (J ×ˢ univ) :=
    (hC.scalar_regular 3 M J F).continuousOn
  have h := hscalar.comp_continuous hmap (fun s => ⟨s.property, mem_univ x⟩)
  exact h

theorem eventually_same_epsilon_neck [T3Space M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b)) (t : Icc a b)
    (N : EpsilonNeck (F.metric t.val)) (hconnection : N.connection = F.connection t.val)
    {K : Set M} (hK : IsCompact K) (hNK : N.carrier ⊆ K) :
    ∀ᶠ s : Icc a b in 𝓝 t, ∃ N' : EpsilonNeck (F.metric s.val),
      N'.epsilon = N.epsilon ∧ N'.center = N.center ∧ N'.carrier = N.carrier ∧
      N'.coordinate_map = N.coordinate_map ∧ N'.coordinate_inverse = N.coordinate_inverse ∧
      N'.central_sphere = N.central_sphere ∧ N'.connection = F.connection s.val ∧
      HEq N'.coordinate N.coordinate := by
  let lambda : Icc a b → ℝ := fun s => (F.connection s.val).scalarCurvature N.center
  have hlambda : Continuous lambda := continuous_scalar_at_fixed_point hC F N.center
  have hpositive : 0 < lambda t := by
    change 0 < (F.connection t.val).scalarCurvature N.center
    rw [← hconnection]
    exact N.scalar_center_pos
  have hvalue : lambda t = N.scale⁻¹ ^ 2 := by
    change (F.connection t.val).scalarCurvature N.center = N.scale⁻¹ ^ 2
    rw [← hconnection, N.scale_eq_scalar, inv_pow,
      ← Real.rpow_mul_natCast N.scalar_center_pos.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  filter_upwards [hlambda.continuousAt.eventually (Ioi_mem_nhds hpositive),
    eventually_normalized_neck_comparison hab F t N hK hNK lambda
      hlambda.continuousAt hvalue] with s hs hclose
  exact exists_neck_of_normalized_comparison N (F.connection s.val) hs hclose

end PoincareConjecture.Proofs.M47
