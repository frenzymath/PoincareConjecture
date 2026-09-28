import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Pair
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Cylinder.Diffeomorph

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem SmoothSphereIsotopicIn.mono {U V S₀ S₁ : Set M}
    (h : SmoothSphereIsotopicIn U S₀ S₁) (hUV : U ⊆ V) :
    SmoothSphereIsotopicIn V S₀ S₁ := by
  obtain ⟨H, hH, hembed, hzero, hone⟩ := h
  exact ⟨H, hH, fun t ht => ⟨(hembed t ht).1, ((hembed t ht).2).trans hUV⟩,
    hzero, hone⟩

namespace EpsilonNeck

theorem exists_two_neck_openCylinderModel :
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
        ∃ T : OpenCylinderModel (A.carrier ∪ B.carrier),
          SmoothSphereIsotopicIn (A.carrier ∪ B.carrier) A.central_sphere T.middleSphere ∧
          SmoothSphereIsotopicIn (A.carrier ∪ B.carrier) B.central_sphere T.middleSphere := by
  obtain ⟨ε₁, hε₁, hsmall₁, hpair⟩ := exists_two_neck_cylinder.{u}
  obtain ⟨ε₂, hε₂, _, hgraphProducer⟩ := exists_sphereSlice_graph_and_isotopy.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall₁, ?_⟩
  intro M _ _ _ _ _ _ _ g A B hA hB hneg hwithin
  obtain ⟨U, D, hU, hDzero⟩ := hpair A B
    (hA.trans (min_le_left _ _)) (hB.trans (min_le_left _ _)) hneg hwithin
  obtain ⟨E, hEzero⟩ := A.exists_unit_to_real_cylinder
  let q₀ := (A.coordinate_inverse A.center).1
  let T : OpenCylinderModel (U : Set M) :=
    OpenCylinderModel.ofDiffeomorph U (E.trans D) q₀
  have hmiddle : T.middleSphere =
      range (fun q : UnitTwoSphere => (D (q, 0) : M)) := by
    dsimp only [T]
    rw [OpenCylinderModel.ofDiffeomorph_middleSphere]
    congr 1
    funext q
    change (D (E ⟨(q, 1 / 2), mem_univ _, by norm_num⟩) : M) = _
    rw [hEzero q]
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
  obtain ⟨_, _, _, _, hAisotopy⟩ := hgraphProducer A B
    (hA.trans (min_le_right _ _)) (hB.trans (min_le_right _ _)) hs hcontained
  have hBzero : (0 : ℝ) ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ :=
    ⟨neg_neg_of_pos hBpos, hBpos⟩
  have hBisotopy : SmoothSphereIsotopicIn B.carrier B.central_sphere
      (range (fun q : UnitTwoSphere => B.coordinate_map (q, s))) := by
    simpa only [B.centralSphere_range] using B.coordinate_graphs_isotopic
      (fun _ => 0) (fun _ => s) contMDiff_const contMDiff_const
      (fun _ => hBzero) (fun _ => hs)
  have hAU : A.carrier ⊆ (U : Set M) := by
    intro x hx
    rw [hU]
    exact Or.inl hx
  have hBU : B.carrier ⊆ (U : Set M) := by
    intro x hx
    rw [hU]
    exact Or.inr hx
  have hout : ∃ T : OpenCylinderModel (U : Set M),
      SmoothSphereIsotopicIn (U : Set M) A.central_sphere T.middleSphere ∧
      SmoothSphereIsotopicIn (U : Set M) B.central_sphere T.middleSphere := by
    refine ⟨T, ?_, ?_⟩
    · rw [hmiddle, hDzero]
      exact hAisotopy.mono hAU
    · rw [hmiddle, hDzero]
      exact hBisotopy.mono hBU
  exact hU ▸ hout

end EpsilonNeck

end PoincareConjecture
