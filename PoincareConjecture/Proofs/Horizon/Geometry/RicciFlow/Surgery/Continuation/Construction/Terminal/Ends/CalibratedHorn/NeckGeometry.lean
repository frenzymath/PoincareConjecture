import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.CapConfinement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Curvature
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.InteriorThickness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter








noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}



theorem slice_through_center_subset_of_epsilon_le
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200)
    (hP : P.epsilon ≤ 1 / 200) (hcenter : P.center ∈ N.carrier)
    (q : UnitTwoSphere) :
    N.coordinate_map (q, (N.coordinate_inverse P.center).2) ∈ P.carrier := by
  let z := N.coordinate_inverse P.center
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem P.center hcenter).2
  have hcoord : N.coordinate_map (z.1, z.2) = P.center := by
    rw [Prod.eta, N.coordinate_map_coordinate_inverse hcenter]
  have hscalar : |N.scale ^ 2 * N.connection.scalarCurvature P.center - 1| < 1 / 2 :=
    N.abs_scaled_scalar_sub_one_lt_half_on_carrier N.connection hN hcenter
  have hnormal := P.scale_sq_mul_scalar_center_of_connection N.connection
  have hscale : N.scale ≤ 2 * P.scale := by
    have hu := mul_le_mul_of_nonneg_left (abs_lt.mp hscalar).2.le (sq_nonneg P.scale)
    have hid : P.scale ^ 2 * (N.scale ^ 2 * N.connection.scalarCurvature P.center - 1) =
        N.scale ^ 2 - P.scale ^ 2 := by
      calc
        _ = N.scale ^ 2 * (P.scale ^ 2 * N.connection.scalarCurvature P.center) -
            P.scale ^ 2 := by ring
        _ = _ := by rw [hnormal, mul_one]
    rw [hid] at hu
    nlinarith [N.scale_pos, P.scale_pos]
  have hsqrt : Real.sqrt (1 + N.epsilon) * Real.sqrt 2 ≤ 2 := by
    have hsq : (Real.sqrt (1 + N.epsilon) * Real.sqrt 2) ^ 2 =
        (1 + N.epsilon) * 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos]),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [N.epsilon_lt_half]
  have hdiam : g.edist P.center (N.coordinate_map (q, z.2)) ≤
      ENNReal.ofReal ((4 * Real.pi) * P.scale) := by
    have hh := N.edist_coordinate_map_slice_le z.1 q hz
    rw [hcoord] at hh
    apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi ≤
          (2 * Real.pi) * N.scale := by
        nlinarith [mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt N.scale_pos.le) Real.pi_pos.le]
      _ ≤ (4 * Real.pi) * P.scale := by
        nlinarith [mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 2 * Real.pi)]
  by_contra hout
  have hpaxis := (P.mem_central_sphere_iff P.center).mp P.center_on_central_sphere
  have hpinner : P.center ∈ P.region (-P.epsilon⁻¹ / 2) (P.epsilon⁻¹ / 2) := by
    refine ⟨hpaxis.1, ?_, ?_⟩ <;> rw [hpaxis.2]
    · simpa only [neg_div] using neg_neg_of_pos (half_pos (inv_pos.mpr P.epsilon_pos))
    · exact half_pos (inv_pos.mpr P.epsilon_pos)
  have hlower := P.quarter_width_le_edist_of_mem_middle_half hpinner hout
  have hscaleP := P.scale_pos
  have hreal : P.scale * P.epsilon⁻¹ / 4 ≤ (4 * Real.pi) * P.scale :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hlower.trans hdiam)
  have hinv : (200 : ℝ) ≤ P.epsilon⁻¹ := by
    have hi := one_div_le_one_div_of_le P.epsilon_pos hP
    norm_num at hi
    simpa only [one_div] using hi
  have hlarge := mul_le_mul_of_nonneg_left hinv P.scale_pos.le
  have hpi := mul_lt_mul_of_pos_right Real.pi_lt_four P.scale_pos
  nlinarith [P.scale_pos]

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}



theorem exists_neck_confinement_of_epsilon_le (e : TerminalEnd K)
    (hepsilon : epsilon ≤ 1 / 200)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D))
    (k : ℕ) (L : Set (E.extended.slice T).carrier) (hL : IsCompact L) :
    ∃ n : ℕ, k ≤ n ∧ ∀ m : ℕ, n ≤ m → ∀ x ∈ e.tail m,
      ∀ N : TerminalStrongNeck E epsilon, N.center = x.val →
        N.carrier ⊆ Subtype.val '' e.tail k ∧ Disjoint N.carrier L := by
  let D := E.extended.connection T
  let J := L ∪ Subtype.val '' (e.exhaustion k : Set K.component)
  have hJ : IsCompact J :=
    hL.union ((e.exhaustion.isCompact k).image continuous_subtype_val)
  obtain ⟨B, hB⟩ := hJ.bddAbove_image D.continuous_scalarCurvature.continuousOn
  obtain ⟨n, hn⟩ := e.exists_tail_scalar_gt hlower hproper (2 * max B 0)
  refine ⟨max k n, le_max_left _ _, fun m hnm x hx N hcenter => ?_⟩
  have hhigh : 2 * max B 0 < D.scalarCurvature x :=
    hn m ((le_max_right _ _).trans hnm) x hx
  have havoid : Disjoint N.carrier J := by
    rw [Set.disjoint_left]
    intro y hyN hyJ
    have hcompare := (N.scalar_strictly_within_factor_two_on_carrier hepsilon hyN).1
    rw [hcenter] at hcompare
    have hupper := (hB ⟨y, hyJ, rfl⟩).trans (le_max_left B 0)
    change D.scalarCurvature x / 2 < D.scalarCurvature y at hcompare
    linarith
  refine ⟨?_, havoid.mono_right subset_union_left⟩
  apply e.subset_tail_image_of_isPreconnected k N.isPreconnected_carrier
    (havoid.mono_right subset_union_right) (e.nested ((le_max_left _ _).trans hnm) hx)
  rw [← hcenter]
  exact N.central_sphere_subset N.center_on_central_sphere

end PoincareConjecture.TerminalEnd
