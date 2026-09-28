import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalPartitionSides
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalCompatibleCoordinates
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalSliceIsotopy
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CylinderPasting











set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck




theorem exists_two_neck_cylinder_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A B : EpsilonNeck g),
        A.epsilon ≤ ε₀ → B.epsilon ≤ ε₀ →
        B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier →
        A.carrier ∩ B.carrier ⊆
          A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
            B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2) →
        ∃ (U : Opens M)
          (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace U ∞),
          (U : Set M) = A.carrier ∪ B.carrier ∧
          range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
            range (fun q : UnitTwoSphere => B.coordinate_map (q, -3 * B.epsilon⁻¹ / 4)) := by
  obtain ⟨ε₁, hε₁, hsmall₁, hgraphProducer⟩ := exists_sphereSlice_graph_and_isotopy_m28.{u}
  obtain ⟨ε₂, hε₂, _, hchartProducer⟩ := exists_compatible_neck_cut_charts_m28.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall₁, ?_⟩
  intro M _ _ _ _ _ _ _ g A B hA hB hneg hwithin
  let s := -3 * B.epsilon⁻¹ / 4
  have hBpos : 0 < B.epsilon⁻¹ := inv_pos.mpr B.epsilon_pos
  have hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ := by
    dsimp [s]
    constructor <;> linarith
  have hsq : s < -B.epsilon⁻¹ / 2 := by dsimp [s]; linarith
  have hcontained (q : UnitTwoSphere) : B.coordinate_map (q, s) ∈ A.carrier := by
    apply hneg
    refine ⟨B.coordinate_map_mem ⟨mem_univ _, hs⟩, ?_⟩
    rw [B.coordinate_inverse_coordinate_map ⟨mem_univ _, hs⟩]
    exact ⟨hs.1, hsq⟩
  obtain ⟨f, hf, hdom, hgraph, -⟩ := hgraphProducer A B
    (hA.trans (min_le_left _ _)) (hB.trans (min_le_left _ _)) hs hcontained
  obtain ⟨hside, hpartition, hdisjoint⟩ :=
    A.graph_half_partition_m28 B f hf.continuous hdom hs hsq hgraph hneg hwithin
  obtain ⟨r, DA, T, hr, hDAangle, hDAzero, hDAside, hTside, hagree⟩ := hchartProducer A B
    (hA.trans (min_le_right _ _)) (hB.trans (min_le_right _ _))
    s hs hcontained f hf hdom hgraph.symm hside
  have hDAhalf : (fun p : RoundCylinderSpace => (DA p : M)) '' {p | p.2 ≤ 0} =
      A.carrier \ A.aboveGraph_m28 f := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(DA p).property, ?_⟩
      intro hx
      have hle := (hDAside p).mpr hp
      have hlt := hx.2
      rw [hDAangle p] at hlt
      exact hlt.not_ge hle
    · intro hx
      obtain ⟨p, hp⟩ := DA.surjective ⟨x, hx.1⟩
      have hpx : (DA p : M) = x := congrArg Subtype.val hp
      refine ⟨p, (hDAside p).mp ?_, hpx⟩
      apply le_of_not_gt
      intro hlt
      apply hx.2
      refine ⟨hx.1, ?_⟩
      rw [← hpx, hDAangle p]
      exact hlt
  have hTupper : (fun p : RoundCylinderSpace => (T p : M)) '' {p | 0 < p.2} =
      B.region s B.epsilon⁻¹ := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(T p).property, (hTside p).mpr hp,
        (B.coordinate_inverse_mem (T p) (T p).property).2.2⟩
    · intro hx
      obtain ⟨p, hp⟩ := T.surjective ⟨x, hx.1⟩
      have hpx : (T p : M) = x := congrArg Subtype.val hp
      exact ⟨p, (hTside p).mp (hpx.symm ▸ hx.2.1), hpx⟩
  have hsep (p q : RoundCylinderSpace) (hp : p.2 ≤ 0) (hq : 0 < q.2) :
      (DA p : M) ≠ T q := by
    intro heq
    have hleft : (DA p : M) ∈ A.carrier \ A.aboveGraph_m28 f := by
      rw [← hDAhalf]
      exact ⟨p, hp, rfl⟩
    have hright : (T q : M) ∈ B.region s B.epsilon⁻¹ := by
      rw [← hTupper]
      exact ⟨q, hq, rfl⟩
    exact disjoint_left.mp hdisjoint hleft (heq.symm ▸ hright)
  obtain ⟨U, D, hD, hU⟩ :=
    Poincare.exists_pasted_cylinder A.carrierOpen B.carrierOpen DA T r hr hagree hsep
  refine ⟨U, D, ?_, ?_⟩
  · rw [hDAhalf, hTupper] at hU
    exact hU.trans hpartition.symm
  · have hzero (q : UnitTwoSphere) : (D (q, 0) : M) = A.coordinate_map (q, f q) := by
      calc
        _ = (DA (q, 0) : M) := by simpa using hD (q, 0)
        _ = A.coordinate_map (A.coordinate_inverse (DA (q, 0))) :=
          (A.coordinate_map_coordinate_inverse (DA (q, 0)).property).symm
        _ = _ := by rw [hDAzero q]
    have hrange : range (fun q : UnitTwoSphere => (D (q, 0) : M)) =
        range (fun q : UnitTwoSphere => A.coordinate_map (q, f q)) := by
      congr 1
      funext q
      exact hzero q
    exact hrange.trans hgraph.symm

end PoincareConjecture.EpsilonNeck
