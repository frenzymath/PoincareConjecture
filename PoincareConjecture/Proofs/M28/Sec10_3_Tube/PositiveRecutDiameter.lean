import PoincareConjecture.Proofs.M28.Sec10_3_Tube.PositiveComponentDistance
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckRegionConnector
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import Mathlib.Topology.Connected.Clopen











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.M28

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}





theorem exists_intrinsicDiameter_bound_of_neck_recut (N : EpsilonNeck g)
    {P : Set M} (hPo : IsOpen P) (hPS : P ⊆ N.central_sphereᶜ)
    (hPcl : closure P = P ∪ N.central_sphere)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (V : TopologicalSpace.Opens M) (hV : (V : Set M) = P ∪ N.region a b)
    (base : M) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ x ∈ (V : Set M), g.edist base x ≤ ENNReal.ofReal D) :
    ∃ B : ℝ, 0 < B ∧ intrinsicDiameter g (V : Set M) ≤ ENNReal.ofReal B := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let h := intrinsicOpenMetric g V
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : V → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hPV : P ⊆ (V : Set M) := by rw [hV]; exact subset_union_left
  have hRV : N.region a b ⊆ (V : Set M) := by rw [hV]; exact subset_union_right
  have hSV : N.central_sphere ⊆ (V : Set M) :=
    (N.central_sphere_subset_region ha hb).trans hRV
  let z : V := ⟨N.center, hSV N.center_on_central_sphere⟩
  have hcomponent : ∀ q ∈ P, connectedComponentIn N.central_sphereᶜ q ⊆ P := by
    intro q hq
    apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hPo
      ⟨q, mem_connectedComponentIn (hPS hq), hq⟩
    rintro x ⟨hxcl, hxcomp⟩
    rcases hPcl ▸ hxcl with hxP | hxS
    · exact hxP
    · exact False.elim (connectedComponentIn_subset _ q hxcomp hxS)
  let Dpositive := (4 * standardSpherePathCeiling) * N.scale + (2 * D + 1)
  let Dcollar := (2 * N.epsilon⁻¹ + 4 * standardSpherePathCeiling) * N.scale
  let R := Dpositive + Dcollar
  have hSpherePos : 0 < standardSpherePathCeiling := standardSpherePathCeiling_pos
  have hscale : 0 < N.scale := N.scale_pos
  have heps : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hDpositive : 0 < Dpositive := by dsimp [Dpositive]; positivity
  have hDcollar : 0 < Dcollar := by dsimp [Dcollar]; positivity
  have hR : 0 < R := add_pos hDpositive hDcollar
  have hcenterBound : g.edist N.center base ≤ ENNReal.ofReal D := by
    rw [show g.edist N.center base = g.edist base N.center from
      Manifold.riemannianEDist_comm]
    exact hbound N.center z.property
  have hradial (q : V) : h.edist z q ≤ ENNReal.ofReal R := by
    have hq : (q : M) ∈ P ∪ N.region a b := by
      rw [← hV]
      exact q.property
    rcases hq with hqP | hqRegion
    · have hambient : g.edist N.center (q : M) < ENNReal.ofReal (2 * D + 1) := by
        apply (Manifold.riemannianEDist_triangle.trans
          (add_le_add hcenterBound (hbound q q.property))).trans_lt
        rw [← ENNReal.ofReal_add hD.le hD.le]
        apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        linarith
      have hh := intrinsicEDist_to_positive_component_le N V hSV hPV hcomponent hqP
        (by positivity : 0 < 2 * D + 1) hambient
      rw [← intrinsicOpenMetric_edist g V z q] at hh
      exact hh.trans (ENNReal.ofReal_le_ofReal
        (le_add_of_nonneg_right hDcollar.le))
    · obtain ⟨gamma, h0, h1, hgamma, hregion, hlength⟩ :=
        exists_neck_region_center_connector N ha hb hqRegion
      have hh := intrinsicEDist_le_pathELength g zero_le_one hgamma
        (fun t ht => hRV (hregion ht))
      rw [h0, h1, ← intrinsicOpenMetric_edist g V q z] at hh
      have hcomm : h.edist z q = h.edist q z := Manifold.riemannianEDist_comm
      rw [hcomm]
      exact (hh.trans hlength.le).trans (ENNReal.ofReal_le_ofReal
        (le_add_of_nonneg_left hDpositive.le))
  refine ⟨2 * R, by positivity, ?_⟩
  unfold intrinsicDiameter
  apply sSup_le
  rintro _ ⟨⟨x, y⟩, rfl⟩
  change intrinsicEDist g (V : Set M) x y ≤ ENNReal.ofReal (2 * R)
  rw [← intrinsicOpenMetric_edist g V x y]
  have hleft : h.edist x z ≤ ENNReal.ofReal R := by
    rw [show h.edist x z = h.edist z x from Manifold.riemannianEDist_comm]
    exact hradial x
  calc
    h.edist x y ≤ h.edist x z + h.edist z y := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal R + ENNReal.ofReal R := add_le_add hleft (hradial y)
    _ = ENNReal.ofReal (2 * R) := by
      rw [← ENNReal.ofReal_add hR.le hR.le]
      congr 1
      ring

end PoincareConjecture.M28
