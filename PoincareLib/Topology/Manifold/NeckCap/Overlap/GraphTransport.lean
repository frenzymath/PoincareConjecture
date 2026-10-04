import PoincareLib.Topology.Manifold.NeckCap.Overlap.Geometry
import PoincareLib.Topology.Manifold.NeckCap.Separation
import PoincareLib.Topology.Maps.Homeomorph.Vertical

/-!
# Ambient transport to a height graph in a neck

The vertical tent deformation in neck coordinates extends by the identity
to an ambient homeomorphism. Its support is a compact inner collar, and it
preserves each ambient connected component. No general isotopy extension
theorem is needed.

Reference: Morgan--Tian, Proposition A.11(4), pp. 503-504; Lemma A.20, p. 508.
-/

noncomputable section

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

/-- The image of a closed symmetric inner collar. -/
def closedCollar (r : ℝ) : Set M :=
  N.coordinate_map '' (univ ×ˢ Icc (-r) r)

theorem closedCollar_subset_carrier {r : ℝ} (hr : r < N.epsilon⁻¹) :
    N.closedCollar r ⊆ N.carrier := by
  rintro x ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
  exact N.coordinate_map_mem ⟨mem_univ _, by constructor <;> linarith [ht.1, ht.2]⟩

theorem isCompact_closedCollar {r : ℝ} (hr : r < N.epsilon⁻¹) :
    IsCompact (N.closedCollar r) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply N.coordinate_map_smooth.continuousOn.mono
  intro z hz
  exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩

private def graphCarrierHomeomorph {r : ℝ} (hr : 0 < r) (hrN : r < N.epsilon⁻¹)
    (h : UnitTwoSphere → ℝ) (hh : Continuous h) (hbound : ∀ q, |h q| < r) :
    N.carrier ≃ₜ N.carrier :=
  N.coordinatePartialHomeomorph.toHomeomorphSourceTarget.symm.trans
    ((Homeomorph.Vertical.graphHomeomorphOn hr hrN.le h hh hbound).trans
      N.coordinatePartialHomeomorph.toHomeomorphSourceTarget)

private theorem graphCarrierHomeomorph_apply {r : ℝ} (hr : 0 < r)
    (hrN : r < N.epsilon⁻¹) (h : UnitTwoSphere → ℝ) (hh : Continuous h)
    (hbound : ∀ q, |h q| < r) (x : N.carrier) :
    (N.graphCarrierHomeomorph hr hrN h hh hbound x : M) =
      N.coordinate_map (Homeomorph.Vertical.graphMap r h (N.coordinate_inverse x)) := rfl

private theorem graphCarrierHomeomorph_fixed {r : ℝ} (hr : 0 < r)
    (hrN : r < N.epsilon⁻¹) (h : UnitTwoSphere → ℝ) (hh : Continuous h)
    (hbound : ∀ q, |h q| < r) (x : N.carrier) (hx : (x : M) ∉ N.closedCollar r) :
    N.graphCarrierHomeomorph hr hrN h hh hbound x = x := by
  apply Subtype.ext
  rw [N.graphCarrierHomeomorph_apply]
  have ht : r ≤ |(N.coordinate_inverse x).2| := by
    by_contra ht
    have ht' := abs_lt.mp (lt_of_not_ge ht)
    exact hx ⟨N.coordinate_inverse x, ⟨mem_univ _, ht'.1.le, ht'.2.le⟩,
      N.coordinate_map_coordinate_inverse x.property⟩
  rw [Homeomorph.Vertical.graphMap_eq_self ht]
  exact N.coordinate_map_coordinate_inverse x.property

variable [T2Space M]

/-- An ambient homeomorphism taking the central sphere to the graph of `h`.
It is the identity outside the specified compact inner collar. -/
def graphTransport {r : ℝ} (hr : 0 < r) (hrN : r < N.epsilon⁻¹)
    (h : UnitTwoSphere → ℝ) (hh : Continuous h) (hbound : ∀ q, |h q| < r) : M ≃ₜ M :=
  (N.graphCarrierHomeomorph hr hrN h hh hbound).extendOfIsCompact N.carrier_open
    (N.isCompact_closedCollar hrN) (N.closedCollar_subset_carrier hrN)
    (N.graphCarrierHomeomorph_fixed hr hrN h hh hbound)

theorem graphTransport_fixed {r : ℝ} (hr : 0 < r) (hrN : r < N.epsilon⁻¹)
    (h : UnitTwoSphere → ℝ) (hh : Continuous h) (hbound : ∀ q, |h q| < r)
    {x : M} (hx : x ∉ N.closedCollar r) : N.graphTransport hr hrN h hh hbound x = x :=
  Homeomorph.extendOfIsCompact_apply_of_notMem _ _ _ _ _ hx

theorem graphTransport_apply {r : ℝ} (hr : 0 < r) (hrN : r < N.epsilon⁻¹)
    (h : UnitTwoSphere → ℝ) (hh : Continuous h) (hbound : ∀ q, |h q| < r)
    {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain) :
    N.graphTransport hr hrN h hh hbound (N.coordinate_map z) =
      N.coordinate_map (Homeomorph.Vertical.graphMap r h z) := by
  have heq := Homeomorph.extendOfIsCompact_apply
    (N.graphCarrierHomeomorph hr hrN h hh hbound) N.carrier_open
    (N.isCompact_closedCollar hrN) (N.closedCollar_subset_carrier hrN)
    (N.graphCarrierHomeomorph_fixed hr hrN h hh hbound)
    (⟨N.coordinate_map z, N.coordinate_map_mem hz⟩ : N.carrier)
  change N.graphTransport hr hrN h hh hbound (N.coordinate_map z) = _ at heq
  rw [N.graphCarrierHomeomorph_apply, N.coordinate_inverse_coordinate_map hz] at heq
  exact heq

theorem graphTransport_image_central_sphere {r : ℝ} (hr : 0 < r)
    (hrN : r < N.epsilon⁻¹) (h : UnitTwoSphere → ℝ) (hh : Continuous h)
    (hbound : ∀ q, |h q| < r) :
    N.graphTransport hr hrN h hh hbound '' N.central_sphere =
      range (fun q => N.coordinate_map (q, h q)) := by
  have hz (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ N.cylinderDomain :=
    ⟨mem_univ _, by constructor <;> linarith [inv_pos.mpr N.epsilon_pos]⟩
  rw [← N.centralSphere_range, ← range_comp]
  congr 1
  funext q
  rw [Function.comp_apply, N.graphTransport_apply hr hrN h hh hbound (hz q)]
  simp [Homeomorph.Vertical.graphMap, Homeomorph.Vertical.move_zero hr]

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem graphTransport_image_connectedComponent {r : ℝ} (hr : 0 < r)
    (hrN : r < N.epsilon⁻¹) (h : UnitTwoSphere → ℝ) (hh : Continuous h)
    (hbound : ∀ q, |h q| < r) (x : M) :
    N.graphTransport hr hrN h hh hbound '' connectedComponent x = connectedComponent x := by
  apply Homeomorph.image_connectedComponent_eq_of_eqOn_compl
    (U := N.carrier) _ N.isConnected_carrier.isPreconnected
  intro y hy
  exact N.graphTransport_fixed hr hrN h hh hbound
    (fun hmem => hy (N.closedCollar_subset_carrier hrN hmem))

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] [T3Space M] in
/-- A continuous graph strictly inside a neck fits in a compact inner collar. -/
theorem exists_graph_collar (h : UnitTwoSphere → ℝ) (hh : Continuous h)
    (hdom : ∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ r : ℝ, 0 < r ∧ r < N.epsilon⁻¹ ∧ ∀ q, |h q| < r := by
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (univ : Set UnitTwoSphere).Nonempty) hh.abs.continuousOn
  have hqN : |h q| < N.epsilon⁻¹ := abs_lt.mpr (hdom q)
  refine ⟨(|h q| + N.epsilon⁻¹) / 2, ?_, ?_, ?_⟩
  · linarith [abs_nonneg (h q), inv_pos.mpr N.epsilon_pos]
  · linarith
  · intro p
    have hp : |h p| ≤ |h q| := hq (mem_univ p)
    linarith

/-- If the second central sphere is a continuous height graph in the first
neck, their exact component-relative separation labels agree. -/
theorem isSeparating_iff_of_central_sphere_graph (N' : EpsilonNeck g)
    (h : UnitTwoSphere → ℝ) (hh : Continuous h)
    (hdom : ∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hsphere : N'.central_sphere = range (fun q => N.coordinate_map (q, h q))) :
    N.IsSeparating ↔ N'.IsSeparating := by
  obtain ⟨r, hr, hrN, hbound⟩ := N.exists_graph_collar h hh hdom
  apply N.isSeparating_iff_of_homeomorph N' (N.graphTransport hr hrN h hh hbound)
  · rw [N.graphTransport_image_connectedComponent]
    have hcenter : N'.center ∈ N.carrier := by
      have hc := N'.center_on_central_sphere
      rw [hsphere] at hc
      obtain ⟨q, hq⟩ := hc
      rw [← hq]
      exact N.coordinate_map_mem ⟨mem_univ _, hdom q⟩
    exact connectedComponent_eq (N.carrier_subset_connectedComponent hcenter)
  · exact (N.graphTransport_image_central_sphere hr hrN h hh hbound).trans hsphere.symm

/-- When the chosen inner collar lies in the overlap, the graph deformation
constructs the full supported transport used by the local agreement consumer. -/
def supportedHomeomorphOfGraph (N' : EpsilonNeck g) {r : ℝ} (hr : 0 < r)
    (hrN : r < N.epsilon⁻¹) (h : UnitTwoSphere → ℝ) (hh : Continuous h)
    (hbound : ∀ q, |h q| < r)
    (hsphere : N'.central_sphere = range (fun q => N.coordinate_map (q, h q)))
    (hcollar : N.closedCollar r ⊆ N'.carrier) : SupportedHomeomorph N N' where
  graphical_sphere := {
    map := fun q => N'.coordinate_map (q, 0)
    smooth := N'.centralSphere_contMDiff
    embedding := N'.centralSphere_isSmoothEmbedding
    image := N'.central_sphere
    range_eq_image := N'.centralSphere_range
    image_subset_first := by
      rw [hsphere]
      rintro x ⟨q, rfl⟩
      exact N.coordinate_map_mem ⟨mem_univ _,
        (abs_lt.mp ((hbound q).trans hrN))⟩
    image_subset_second := N'.central_sphere_subset }
  homeomorph := N.graphTransport hr hrN h hh hbound
  support := N.closedCollar r
  support_compact := N.isCompact_closedCollar hrN
  support_subset_overlap := subset_inter (N.closedCollar_subset_carrier hrN) hcollar
  fixed_outside_support := fun _ hx => N.graphTransport_fixed hr hrN h hh hbound hx
  component_image := by
    rw [N.graphTransport_image_connectedComponent]
    apply connectedComponent_eq
    apply N.carrier_subset_connectedComponent
    have hc := N'.center_on_central_sphere
    rw [hsphere] at hc
    obtain ⟨q, hq⟩ := hc
    rw [← hq]
    exact N.coordinate_map_mem ⟨mem_univ _, abs_lt.mp ((hbound q).trans hrN)⟩
  sphere_image := (N.graphTransport_image_central_sphere hr hrN h hh hbound).trans hsphere.symm

end PoincareMT.EpsilonNeck
