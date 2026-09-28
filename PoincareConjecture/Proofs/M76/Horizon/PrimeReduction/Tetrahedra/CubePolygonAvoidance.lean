import PoincareConjecture.Proofs.M76.PrimeReduction.AffineContactFiniteness
import PoincareConjecture.Proofs.M76.Mathlib.AffineSubspaceAvoidance
import PoincareConjecture.Proofs.M76.Mathlib.PolygonAffineImage








set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

theorem exists_cube_frontier_point_avoiding_polygons
    {ι : Type*} [Finite ι] (n : ι → ℕ) (P : ∀ i, Polygon V3 (n i + 3)) :
    ∃ v ∈ frontier (closedBall (0 : V3) 1), v ∉ ⋃ i, (P i).boundary ℝ := by
  classical
  let π : V3 →ₗ[ℝ] P2 := (LinearMap.proj 0).prod (LinearMap.proj 1)
  let J := Σ i, Fin (n i + 3)
  let A : J → AffineSubspace ℝ P2 := fun j =>
    affineSpan ℝ (({π (P j.1 j.2), π (P j.1 (finRotate (n j.1 + 3) j.2))} :
      Finset P2) : Set P2)
  have hA (j : J) : A j ≠ ⊤ := by
    have hdim := finrank_affineSpan_finset_le
      (s := {π (P j.1 j.2), π (P j.1 (finRotate (n j.1 + 3) j.2))})
      (Finset.insert_nonempty _ _) (d := 1) (by
        exact (Finset.card_insert_le _ _).trans (by simp))
    intro heq
    have hdim' : Module.finrank ℝ (A j).direction ≤ 1 := hdim
    rw [heq,AffineSubspace.direction_top,finrank_top] at hdim'
    norm_num [Module.finrank_prod] at hdim'
  obtain ⟨p,hp,hpA⟩ := (AffineSubspace.dense_compl_iUnion A hA).inter_open_nonempty
    (ball (0 : P2) 1) isOpen_ball ⟨0,mem_ball_self zero_lt_one⟩
  have hpn : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  let v : V3 := ![p.1,p.2,1]
  have hvn : ‖v‖ = 1 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      fin_cases i
      · exact (norm_fst_le p).trans hpn.le
      · exact (norm_snd_le p).trans hpn.le
      · norm_num [v]
    · simpa [v] using (norm_le_pi_norm v (2 : Fin 3))
  refine ⟨v,?_,?_⟩
  · rw [frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
    exact mem_sphere_zero_iff_norm.mpr hvn
  · intro hv
    obtain ⟨i,hi⟩ := mem_iUnion.mp hv
    obtain ⟨j,hj⟩ := mem_iUnion.mp hi
    have hπ : π v ∈ affineSegment ℝ (π (P i j))
        (π (P i (finRotate (n i + 3) j))) := by
      exact (affineSegment_image π.toAffineMap _ _).subset (mem_image_of_mem π hj)
    apply hpA
    refine mem_iUnion.mpr ⟨⟨i,j⟩,?_⟩
    have heq : π v = p := by ext <;> simp [π,v]
    rw [←heq]
    simpa only [A,Finset.coe_pair] using affineSegment_subset_affineSpan ℝ _ _ hπ

end PoincareConjecture.M76
