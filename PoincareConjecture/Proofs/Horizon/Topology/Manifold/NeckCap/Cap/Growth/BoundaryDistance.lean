import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceLower
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

theorem boundary_edist_lower_of_not_mem_carrier {x y : M}
    (hx : x ∈ C.boundary_sphere) (hy : y ∉ C.carrier) :
    ENNReal.ofReal ((0.9 : ℝ) * C.boundary_neck.scale * C.epsilon⁻¹) ≤
      g.edist x y := by
  let N := C.boundary_neck
  have hε : N.epsilon ≤ 1 / 200 :=
    C.boundary_neck_epsilon.trans_le C.epsilon_le_threshold
  have hinv : 200 ≤ N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    linarith
  have hroot : (0.99 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  have hnum : (2 * Real.pi) * N.scale +
      (0.9 : ℝ) * N.scale * N.epsilon⁻¹ ≤
      N.scale * Real.sqrt (1 - N.epsilon) * N.epsilon⁻¹ := by
    have hbase : 2 * Real.pi + (0.9 : ℝ) * N.epsilon⁻¹ ≤
        (0.99 : ℝ) * N.epsilon⁻¹ := by nlinarith [Real.pi_le_four]
    have hmul := mul_le_mul_of_nonneg_left hbase N.scale_pos.le
    have hrootmul := mul_le_mul_of_nonneg_left hroot
      (mul_nonneg N.scale_pos.le (inv_pos.mpr N.epsilon_pos).le)
    nlinarith
  have hlow := N.edist_center_lower_of_not_mem_carrier
    (fun hn => hy (C.boundary_neck_subset hn))
  have hdiam := N.edist_central_sphere_le_two_pi_mul_scale N.center_on_central_sphere
    (C.boundary_eq_neck_sphere ▸ hx)
  have hscale := N.scale_pos
  have hepsilon := N.epsilon_pos
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top
    (a := ENNReal.ofReal ((2 * Real.pi) * N.scale))
  rw [← C.boundary_neck_epsilon]
  calc
    _ = ENNReal.ofReal ((2 * Real.pi) * N.scale +
        (0.9 : ℝ) * N.scale * N.epsilon⁻¹) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * N.epsilon⁻¹) :=
      ENNReal.ofReal_le_ofReal hnum
    _ ≤ g.edist N.center y := hlow
    _ ≤ g.edist N.center x + g.edist x y := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal ((2 * Real.pi) * N.scale) + g.edist x y :=
      add_le_add hdiam le_rfl

theorem uniform_boundary_edist_lower (D : LeviCivitaData g) {B : ℝ}
    (hB : C.cap_constant ≤ B) {p x y : M} (hp : p ∈ C.carrier)
    (hx : x ∈ C.boundary_sphere) (hy : y ∉ C.carrier) :
    ENNReal.ofReal ((0.9 : ℝ) * (B * D.scalarCurvature p) ^ (-1 / 2 : ℝ) *
      C.epsilon⁻¹) ≤ g.edist x y := by
  apply (ENNReal.ofReal_le_ofReal ?_).trans
    (C.boundary_edist_lower_of_not_mem_carrier hx hy)
  have hscale := (C.uniform_bounds_at_point D hB hp).2.2
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscale.le (by norm_num))
    (inv_pos.mpr C.epsilon_pos).le

theorem closed_core_edist_lower_of_not_mem_carrier {x y : M}
    (hx : x ∈ C.closed_core) (hy : y ∉ C.carrier) :
    ENNReal.ofReal ((0.9 : ℝ) * C.boundary_neck.scale * C.epsilon⁻¹) ≤
      g.edist x y := by
  rw [C.closed_core_eq_core_union_boundary] at hx
  rcases hx with hx | hx
  · let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    by_contra h
    have hshort : Manifold.riemannianEDist (𝓡 3) x y <
        ENNReal.ofReal ((0.9 : ℝ) * C.boundary_neck.scale * C.epsilon⁻¹) :=
      lt_of_not_ge h
    obtain ⟨γ, h0, h1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt hshort
    have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image γ hγ.continuousOn
    obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := C.boundary_inter_nonempty_of_crossing hconn
      ⟨x, ⟨0, by simp, h0⟩, hx⟩
      ⟨y, ⟨1, by simp, h1⟩, fun hc => hy (C.closed_core_subset_carrier hc)⟩
    have hright : ENNReal.ofReal ((0.9 : ℝ) * C.boundary_neck.scale * C.epsilon⁻¹) ≤
        Manifold.pathELength (𝓡 3) γ t 1 :=
      (C.boundary_edist_lower_of_not_mem_carrier hz hy).trans
        (Manifold.riemannianEDist_le_pathELength
          (hγ.mono (Icc_subset_Icc_left ht.1)) rfl h1 ht.2)
    exact (not_lt_of_ge (hright.trans (Manifold.pathELength_mono ht.1 le_rfl))) hlength
  · exact C.boundary_edist_lower_of_not_mem_carrier hx hy

theorem complement_distance_gain_of_carrier_subset_core (A : CapCertificate g)
    (hAC : A.carrier ⊆ C.core) {p : M} (hp : p ∈ A.carrier) :
    (⨅ z ∈ A.carrierᶜ, g.edist p z) +
        ENNReal.ofReal ((0.9 : ℝ) * C.boundary_neck.scale * C.epsilon⁻¹) ≤
      ⨅ y ∈ C.carrierᶜ, g.edist p y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine le_iInf fun y => le_iInf fun hy => ?_
  by_contra h
  have hshort : Manifold.riemannianEDist (𝓡 3) p y <
      (⨅ z ∈ A.carrierᶜ, g.edist p z) +
        ENNReal.ofReal ((0.9 : ℝ) * C.boundary_neck.scale * C.epsilon⁻¹) := lt_of_not_ge h
  obtain ⟨γ, h0, h1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt hshort
  have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image γ hγ.continuousOn
  obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := C.boundary_inter_nonempty_of_crossing hconn
    ⟨p, ⟨0, by simp, h0⟩, hAC hp⟩
    ⟨y, ⟨1, by simp, h1⟩, fun hc => hy (C.closed_core_subset_carrier hc)⟩
  have hout : γ t ∈ A.carrierᶜ :=
    fun hzA => Set.disjoint_left.mp C.disjoint_core_boundary (hAC hzA) hz
  have hleft : (⨅ z ∈ A.carrierᶜ, g.edist p z) ≤
      Manifold.pathELength (𝓡 3) γ 0 t := by
    exact (iInf_le_of_le (γ t) (iInf_le _ hout)).trans
      (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc_right ht.2)) h0 rfl ht.1)
  have hright : ENNReal.ofReal ((0.9 : ℝ) * C.boundary_neck.scale * C.epsilon⁻¹) ≤
      Manifold.pathELength (𝓡 3) γ t 1 :=
    (C.boundary_edist_lower_of_not_mem_carrier hz hy).trans
      (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc_left ht.1)) rfl h1 ht.2)
  exact (not_lt_of_ge ((add_le_add hleft hright).trans_eq
    (Manifold.pathELength_add ht.1 ht.2))) hlength

end PoincareConjecture.CapCertificate
