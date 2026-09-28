import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SeparatingLimitCover
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

theorem exists_high_selected_neck_inside_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (K : NeckOnlyCover g) (T : CorrectedA19Conclusion g K),
        K.epsilon ≤ epsilon0 → IsOpen K.X → IsCompact (frontier K.X) →
        (∀ B : ℝ, ∃ x ∈ K.X, B < D.scalarCurvature x) →
        ∀ B : ℝ, ∃ i ∈ T.tube.chain.shape.active,
          B < D.scalarCurvature (T.tube.chain.neck i).center ∧
          (T.tube.chain.neck i).carrier ⊆ K.X ∧ (T.tube.chain.neck i).IsSeparating := by
  obtain ⟨epsilon0, hpos, hsmall, hratio⟩ := tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ instT3 g D K T hepsilon hX hfront hunbounded B
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ instT3)
  obtain ⟨B0, hB0⟩ := hfront.bddAbove_image D.continuous_scalarCurvature.continuousOn
  obtain ⟨x, hx, hRx⟩ := hunbounded (2 * max B (2 * B0))
  have hxT := T.contains_X hx
  rw [T.tube.carrier_eq_chain_union] at hxT
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxT
  let N := T.tube.chain.neck i.val
  have hepsN : N.epsilon ≤ epsilon0 := by
    rw [T.tube.chain.epsilon_eq i.val i.property, T.epsilon_eq]
    exact hepsilon
  have hcenter : N.center ∈ N.carrier := N.central_sphere_subset N.center_on_central_sphere
  have hcompare := hratio M g D N hepsN x hi N.center hcenter
  have hhigh : max B (2 * B0) < D.scalarCurvature N.center := by linarith
  have hdisj : Disjoint N.carrier (frontier K.X) := by
    apply Set.disjoint_left.mpr
    intro y hy hyfront
    have hupper := hB0 (mem_image_of_mem D.scalarCurvature hyfront)
    have hlower := hratio M g D N hepsN N.center hcenter y hy
    have hbound := (le_max_right B (2 * B0)).trans_lt hhigh
    linarith
  have hsubset : N.carrier ⊆ K.X := by
    let : ConnectedSpace N.carrier := Subtype.connectedSpace N.isConnected_carrier
    have hclopen : IsClopen ((Subtype.val : N.carrier → M) ⁻¹' K.X) :=
      isClopen_preimage_val hX hdisj.symm
    have hfull := hclopen.eq_univ
      ⟨⟨N.center, hcenter⟩, T.selected_centers_mem i.val i.property⟩
    intro y hy
    have hh : (⟨y, hy⟩ : N.carrier) ∈ (univ : Set N.carrier) := mem_univ _
    rw [← hfull] at hh
    exact hh
  obtain ⟨N0, hN0, hrev⟩ := T.tube.chain.selected i.val i.property
  have hsep := T.separating_necks N0 (T.source_subset hN0)
  have hsepN : N.IsSeparating := by
    unfold EpsilonNeck.IsSeparating
    rw [hrev.2.2.1, hrev.2.2.2.2.1]
    exact hsep
  exact ⟨i.val, i.property, (le_max_left _ _).trans_lt hhigh, hsubset, hsepN⟩

end PoincareConjecture.M28
