import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SeparatingNeckComponents
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderComponentSide











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] {g : RiemannianMetric 3 M}





theorem exists_neck_component_inside_of_compl_preconnected
    (N : EpsilonNeck g) (hsep : N.IsSeparating) {X : Set M}
    (hNX : N.carrier ⊆ X) (hX : IsPreconnected Xᶜ) :
    ∃ P : Set M, IsOpen P ∧ IsConnected P ∧ P ⊆ X \ N.central_sphere ∧
      frontier P = N.central_sphere ∧ closure P = P ∪ N.central_sphere ∧
      (∀ x ∈ P, connectedComponentIn N.central_sphereᶜ x = P) ∧
      (N.belowGraph_m28 (fun _ => 0) ⊆ P ∨ N.aboveGraph_m28 (fun _ => 0) ⊆ P) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hzero : ∀ q : UnitTwoSphere, (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    fun _ => ⟨neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  obtain ⟨a, ha⟩ := (N.isConnected_belowGraph_m28 _ continuous_const hzero).nonempty
  obtain ⟨b, hb⟩ := (N.isConnected_aboveGraph_m28 _ continuous_const hzero).nonempty
  obtain ⟨ho0, ho1, hc0, hc1, hd, hu, hf0, hf1, hcl0, hcl1, hbelow, habove⟩ :=
    N.complement_components_of_isSeparating hsep ha hb
  have hsub : Xᶜ ⊆ connectedComponentIn N.central_sphereᶜ a ∪
      connectedComponentIn N.central_sphereᶜ b := by
    rw [hu]
    intro x hx hS
    exact hx (hNX (N.central_sphere_subset hS))
  rcases hX.subset_or_subset ho0 ho1 hd hsub with hside | hside
  · refine ⟨connectedComponentIn N.central_sphereᶜ b, ho1, hc1, ?_, hf1, hcl1,
      fun _ hx => (connectedComponentIn_eq hx).symm, Or.inr habove⟩
    intro x hx
    refine ⟨?_, connectedComponentIn_subset _ _ hx⟩
    by_contra hnot
    exact Set.disjoint_left.mp hd (hside hnot) hx
  · refine ⟨connectedComponentIn N.central_sphereᶜ a, ho0, hc0, ?_, hf0, hcl0,
      fun _ hx => (connectedComponentIn_eq hx).symm, Or.inl hbelow⟩
    intro x hx
    refine ⟨?_, connectedComponentIn_subset _ _ hx⟩
    by_contra hnot
    exact Set.disjoint_left.mp hd hx (hside hnot)





theorem exists_positive_ambient_cylinder_half
    (N : EpsilonNeck g) (hsep : N.IsSeparating) {X : Set M}
    (hNX : N.carrier ⊆ X) (hX : IsPreconnected Xᶜ)
    (U : TopologicalSpace.Opens M) (T : OpenCylinderModel (U : Set M))
    (hXU : X ⊆ U) (hisotopy : SmoothSphereIsotopicIn (U : Set M)
      N.central_sphere T.middleSphere) :
    ∃ (P : Set M) (phi : U ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)),
      IsOpen P ∧ IsConnected P ∧ P ⊆ X \ N.central_sphere ∧
      frontier P = N.central_sphere ∧ closure P = P ∪ N.central_sphere ∧
      (∀ x ∈ P, connectedComponentIn N.central_sphereᶜ x = P) ∧
      (N.belowGraph_m28 (fun _ => 0) ⊆ P ∨ N.aboveGraph_m28 (fun _ => 0) ⊆ P) ∧
      (∀ x : U, cylinderSignedHeight phi x = 0 ↔ x.val ∈ N.central_sphere) ∧
      ((∀ x : U, cylinderSignedHeight phi x < 0 ↔ x.val ∈ P) ∨
        (∀ x : U, 0 < cylinderSignedHeight phi x ↔ x.val ∈ P)) := by
  obtain ⟨P, hPo, hPc, hPX, hPf, hPcl, hcomponent, hcollar⟩ :=
    exists_neck_component_inside_of_compl_preconnected N hsep hNX hX
  obtain ⟨phi, a, b, _ha, _ha', _hb, _hb', hzero, _htail⟩ :=
    T.exists_isotopic_sphere_coordinates hisotopy
  have hzero' (x : U) : cylinderSignedHeight phi x = 0 ↔ x.val ∈ N.central_sphere := by
    rw [cylinderSignedHeight, sub_eq_zero]
    exact hzero x
  have hPU : P ⊆ (U : Set M) \ N.central_sphere :=
    fun _ hx => ⟨hXU (hPX hx).1, (hPX hx).2⟩
  have hcomponentU (x : M) (hx : x ∈ P) :
      connectedComponentIn ((U : Set M) \ N.central_sphere) x = P := by
    apply Subset.antisymm
    · exact (connectedComponentIn_mono x (fun _ hy => hy.2)).trans_eq (hcomponent x hx)
    · exact hPc.isPreconnected.subset_connectedComponentIn hx hPU
  exact ⟨P, phi, hPo, hPc, hPX, hPf, hPcl, hcomponent, hcollar, hzero',
    cylinderSignedHeight_component_half phi hzero' hPc hPU hcomponentU⟩

end PoincareConjecture.M28
