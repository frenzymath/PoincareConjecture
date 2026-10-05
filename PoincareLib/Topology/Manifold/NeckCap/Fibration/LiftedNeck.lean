import PoincareLib.Topology.Manifold.NeckCap.Fibration.Covering
import PoincareLib.Topology.Homotopy.Sphere.SphereConnectivity
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ambient
import PoincareLib.Topology.Manifold.NeckCap.Separation
import PoincareLib.Topology.Manifold.NeckCap.Cover

/-!
# Neck charts in covering spaces

Every supplied neck lifts through a covering map at any point above its carrier.
The lift is an open embedded collar. In a simply connected covering space its
central sphere separates, and in any connected covering its nontrivial deck
translates are disjoint.

Reference: Morgan--Tian, corrected Lemma A.20, p. 508.
-/

set_option autoImplicit false

open Function Set Topology
open scoped Manifold ContDiff

namespace PoincareMT

/-- The topological domain of a positive-parameter neck is simply connected. -/
theorem simplyConnectedSpace_neckDomain {ε : ℝ} (hε : 0 < ε) :
    SimplyConnectedSpace (NeckDomain ε) := by
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  let : ContractibleSpace (Ioo (-ε⁻¹) ε⁻¹) :=
    (convex_Ioo (-ε⁻¹) ε⁻¹).contractibleSpace
      ⟨0, neg_lt_zero.mpr (inv_pos.mpr hε), inv_pos.mpr hε⟩
  exact ((ContinuousMap.HomotopyEquiv.refl UnitTwoSphere).prodCongr
    (ContractibleSpace.hequiv (Ioo (-ε⁻¹) ε⁻¹) Unit).some |>.trans
      (Homeomorph.prodUnique UnitTwoSphere Unit).toHomotopyEquiv).simplyConnectedSpace

namespace EpsilonNeck

variable {M E : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace E] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

/-- A lifted point in a neck determines an open embedded lift of its entire
coordinate domain. -/
theorem exists_lifted_coordinate {p : E → M} (hp : IsCoveringMap p)
    (e : E) (he : p e ∈ N.carrier) :
    ∃ F : C(NeckDomain N.epsilon, E),
      F (N.coordinate.symm ⟨p e, he⟩) = e ∧
      p ∘ F = (fun z => (N.coordinate z : M)) ∧ IsOpenEmbedding F := by
  let : SimplyConnectedSpace (NeckDomain N.epsilon) :=
    simplyConnectedSpace_neckDomain N.epsilon_pos
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  let : LocallyPathConnectedSpace (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    isOpen_Ioo.locallyPathConnectedSpace
  apply Poincare.Topology.exists_openEmbedding_lift hp
    (N.carrier_open.isOpenEmbedding_subtypeVal.comp N.coordinate.isOpenEmbedding)
    (N.coordinate.symm ⟨p e, he⟩) e
  exact congr_arg Subtype.val (N.coordinate.apply_symm_apply ⟨p e, he⟩).symm

/-- Every nontrivial covering transformation moves a lifted neck off itself. -/
theorem disjoint_lifted_coordinate_translate [PreconnectedSpace E]
    {p : E → M} (hp : IsCoveringMap p) {F : NeckDomain N.epsilon → E}
    (hF : p ∘ F = (fun z => (N.coordinate z : M)))
    (d : E ≃ₜ E) (hd : p ∘ d = p) (hne : d ≠ Homeomorph.refl E) :
    Disjoint (range F) (d '' range F) :=
  Poincare.Topology.disjoint_covering_translate hp
    (Subtype.val_injective.comp N.coordinate.injective) hF d hd hne

omit [TopologicalSpace E] in
/-- A lifted neck is a sheet on which the covering projection is injective. -/
theorem injOn_projection_lifted_coordinate {p : E → M}
    {F : NeckDomain N.epsilon → E}
    (hF : p ∘ F = (fun z => (N.coordinate z : M))) : InjOn p (range F) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  apply congr_arg F
  apply N.coordinate.injective
  apply Subtype.ext
  simpa only [← congr_fun hF x, ← congr_fun hF y, comp_apply] using hxy

omit [TopologicalSpace E] in
/-- The whole lifted neck projects onto the original neck carrier. -/
theorem image_lifted_coordinate {p : E → M} {F : NeckDomain N.epsilon → E}
    (hF : p ∘ F = (fun z => (N.coordinate z : M))) : p '' range F = N.carrier := by
  rw [← range_comp, hF]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact (N.coordinate z).property
  · intro hx
    exact ⟨N.coordinate.symm ⟨x, hx⟩,
      congr_arg Subtype.val (N.coordinate.apply_symm_apply ⟨x, hx⟩)⟩

omit [TopologicalSpace E] in
/-- The lifted central slice projects onto the supplied central sphere. -/
theorem image_lifted_central_sphere {p : E → M} {F : NeckDomain N.epsilon → E}
    (hF : p ∘ F = (fun z => (N.coordinate z : M))) :
    p '' range (fun y : UnitTwoSphere =>
      F (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
        inv_pos.mpr N.epsilon_pos⟩)) = N.central_sphere := by
  rw [← range_comp]
  convert N.coordinate_central_range using 1
  congr 1
  funext y
  exact congr_fun hF _

/-- In a simply connected covering space, the lifted central sphere has two
connected open complementary regions. -/
theorem lifted_coordinate_complementary_regions [T2Space E] [SimplyConnectedSpace E]
    [LocallyPathConnectedSpace E] (F : NeckDomain N.epsilon → E)
    (hF : IsOpenEmbedding F) :
    let S := range (fun y : UnitTwoSphere =>
      F (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
        inv_pos.mpr N.epsilon_pos⟩))
    ∃ A B : Set E,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = Sᶜ ∧ frontier A = S ∧ frontier B = S ∧
      F '' {z | (z.2 : ℝ) < 0} ⊆ A ∧ F '' {z | 0 < (z.2 : ℝ)} ⊆ B := by
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  simpa only [Topology.IsEmbedding.toHomeomorph_apply_coe] using
    Poincare.Topology.exists_collar_complementary_regions
      (inv_pos.mpr N.epsilon_pos) hF.isOpen_range hF.isEmbedding.toHomeomorph

omit [TopologicalSpace E] in
/-- A nonseparating neck cannot lie in a simply connected ambient manifold. -/
theorem not_simplyConnectedSpace_of_isNonseparating [T2Space M]
    (hN : N.IsNonseparating) : ¬ SimplyConnectedSpace M := by
  intro hsc
  let : SimplyConnectedSpace M := hsc
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  obtain ⟨A, B, hA, hB, hAc, hBc, hdis, hcover, _⟩ :=
    N.lifted_coordinate_complementary_regions
      (fun z => (N.coordinate z : M))
      (N.carrier_open.isOpenEmbedding_subtypeVal.comp N.coordinate.isOpenEmbedding)
  rw [N.coordinate_central_range] at hcover
  have hconn : IsConnected (A ∪ B) := by
    rw [hcover]
    simpa only [IsNonseparating, PreconnectedSpace.connectedComponent_eq_univ,
      ← compl_eq_univ_sdiff] using hN
  rcases hconn.isPreconnected.subset_or_subset hA hB hdis Subset.rfl with h | h
  · obtain ⟨x, hx⟩ := hBc.nonempty
    exact Set.disjoint_left.mp hdis (h (Or.inr hx)) hx
  · obtain ⟨x, hx⟩ := hAc.nonempty
    exact Set.disjoint_left.mp hdis hx (h (Or.inl hx))

end EpsilonNeck

namespace NeckOnlyCover

variable {M E : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace E] {g : RiemannianMetric 3 M}

omit [TopologicalSpace E] in
/-- A nonempty cover by nonseparating necks rules out a simply connected base. -/
theorem not_simplyConnectedSpace [T2Space M] (H : NeckOnlyCover g)
    (hns : ∀ N ∈ H.necks, N.IsNonseparating) : ¬ SimplyConnectedSpace M := by
  obtain ⟨x, hx⟩ := H.connected_X.nonempty
  obtain ⟨N, hN, _⟩ := H.pointwise_center_cover x hx
  exact N.not_simplyConnectedSpace_of_isNonseparating (hns N hN)

/-- A whole cover by supplied neck centers lifts to a whole cover by open neck
charts centered above those same supplied centers. -/
theorem exists_lifted_centered_coordinate (H : NeckOnlyCover g) (hwhole : H.X = univ)
    {p : E → M} (hp : IsCoveringMap p) (e : E) :
    ∃ N ∈ H.necks, N.center = p e ∧
      ∃ F : C(NeckDomain N.epsilon, E),
        p ∘ F = (fun z => (N.coordinate z : M)) ∧ IsOpenEmbedding F ∧
        ∃ y : UnitTwoSphere,
          F (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
            inv_pos.mpr N.epsilon_pos⟩) = e := by
  obtain ⟨N, hN, hcenter⟩ := H.pointwise_center_cover (p e) (hwhole.symm ▸ mem_univ _)
  have he : p e ∈ N.carrier := hcenter ▸ N.central_sphere_subset N.center_on_central_sphere
  obtain ⟨F, hFe, hF, hopen⟩ := N.exists_lifted_coordinate hp e he
  refine ⟨N, hN, hcenter, F, hF, hopen, ?_⟩
  have hc : p e ∈ N.central_sphere := hcenter ▸ N.center_on_central_sphere
  rw [← N.coordinate_central_range] at hc
  obtain ⟨y, hy⟩ := hc
  refine ⟨y, ?_⟩
  have hy' : N.coordinate
      (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩) =
        ⟨p e, he⟩ := Subtype.ext hy
  have hz := congr_arg N.coordinate.symm hy'
  rw [N.coordinate.symm_apply_apply] at hz
  rwa [hz]

end NeckOnlyCover
end PoincareMT
