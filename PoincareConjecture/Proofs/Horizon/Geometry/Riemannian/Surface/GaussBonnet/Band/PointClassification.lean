import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.ObliqueFrontier








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)



theorem carrier_point_cases {q : S} (hq : q ∈ B.carrier) :
    q ∈ interior B.carrier ∨
    (∃ t ∈ Icc (0 : ℝ) 1, B.coordinates (collarParameterEquiv.symm (t, 0)) = q) ∨
    (∃ z ∈ Icc (0 : ℝ) (B.height 0), B.coordinates (collarParameterEquiv.symm (0, z)) = q) ∨
    (∃ z ∈ Icc (0 : ℝ) (B.height 1), B.coordinates (collarParameterEquiv.symm (1, z)) = q) ∨
    (∃ t ∈ Ioo (0 : ℝ) 1,
      B.coordinates (collarParameterEquiv.symm (t, B.height t)) = q) := by
  rw [B.carrier_eq_image, B.band_eq_subgraph] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  let t := (collarParameterEquiv x).1
  let z := (collarParameterEquiv x).2
  change t ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ z ∧ z ≤ B.height t at hx
  have hxcoord : collarParameterEquiv.symm (t, z) = x := by
    exact collarParameterEquiv.symm_apply_apply x
  by_cases hz : z = 0
  · exact Or.inr (Or.inl ⟨t, hx.1, by simpa only [← hz] using congrArg B.coordinates hxcoord⟩)
  by_cases ht0 : t = 0
  · refine Or.inr (Or.inr (Or.inl ⟨z, ?_, ?_⟩))
    · exact ⟨hx.2.1, ht0 ▸ hx.2.2⟩
    · simpa only [← ht0] using congrArg B.coordinates hxcoord
  by_cases ht1 : t = 1
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨z, ?_, ?_⟩)))
    · exact ⟨hx.2.1, ht1 ▸ hx.2.2⟩
    · simpa only [← ht1] using congrArg B.coordinates hxcoord
  have ht : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx.1.1 (Ne.symm ht0), lt_of_le_of_ne hx.1.2 ht1⟩
  by_cases htop : z = B.height t
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨t, ht, by simpa only [← htop] using congrArg B.coordinates hxcoord⟩)))
  exact Or.inl (B.openBand_image_subset_interior
    ⟨x, ⟨ht, lt_of_le_of_ne hx.2.1 (Ne.symm hz), lt_of_le_of_ne hx.2.2 htop⟩, rfl⟩)



theorem interior_parameter_cell_cases {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∃ j : Fin B.interface.count, t ∈ Ioo (B.cut j.castSucc) (B.cut j.succ)) ∨
    (∃ i j : Fin B.interface.count, i.succ = j.castSucc ∧ t = B.cut i.succ) := by
  have hc : t ∈ ⋃ j : Fin B.interface.count, Icc (B.cut j.castSucc) (B.cut j.succ) := by
    rw [B.cut_interval_cover]
    exact ⟨ht.1.le, ht.2.le⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hc
  by_cases hl : t = B.cut j.castSucc
  · have hjpos : 0 < j.val := by
      by_contra h
      have he : j.castSucc = 0 := Fin.ext (by change j.val = 0; omega)
      rw [hl, he, B.cut_first] at ht
      exact (lt_irrefl _ ht.1)
    let i : Fin B.interface.count := ⟨j.val - 1, by omega⟩
    have hij : i.succ = j.castSucc := Fin.ext (by dsimp [i]; omega)
    exact Or.inr ⟨i, j, hij, hij ▸ hl⟩
  by_cases hr : t = B.cut j.succ
  · have hjlt : j.val + 1 < B.interface.count := by
      by_contra h
      have he : j.succ = Fin.last B.interface.count :=
        Fin.ext (by change j.val + 1 = B.interface.count; omega)
      rw [hr, he, B.cut_last] at ht
      exact (lt_irrefl _ ht.2)
    let k : Fin B.interface.count := ⟨j.val + 1, hjlt⟩
    exact Or.inr ⟨j, k, Fin.ext rfl, hr⟩
  exact Or.inl ⟨j, lt_of_le_of_ne hj.1 (Ne.symm hl), lt_of_le_of_ne hj.2 hr⟩

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
