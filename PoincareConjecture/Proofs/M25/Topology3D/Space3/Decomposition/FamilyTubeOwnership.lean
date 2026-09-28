import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem exists_family_tube_owner
    (n : ℕ) (psi : Fin n → UnitTwoSphere × ℝ → E3)
    (hembed : ∀ i : Fin n, IsCollarEmbedding (psi i))
    (hdisjoint : Pairwise (fun i j : Fin n =>
      Disjoint (range (fun q : UnitTwoSphere => psi i (q, 0)))
        (range (fun q : UnitTwoSphere => psi j (q, 0)))))
    (t d : ℝ) (hd : 0 < d)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hwhole : ∀ x ∈ closedBall (0 : E2) 1,
      ∀ z ∈ Ioo (t - d) (t + d),
        T (x, z) ∈ (⋃ i : Fin n, range (fun q : UnitTwoSphere => psi i (q, 0))) ↔
          x ∈ sphere (0 : E2) 1) :
    ∃ j : Fin n,
      (∀ x ∈ sphere (0 : E2) 1, ∀ z ∈ Ioo (t - d) (t + d),
        T (x, z) ∈ range (fun q : UnitTwoSphere => psi j (q, 0))) ∧
      (∀ k : Fin n,
        (∀ x ∈ sphere (0 : E2) 1, ∀ z ∈ Ioo (t - d) (t + d),
          T (x, z) ∈ range (fun q : UnitTwoSphere => psi k (q, 0))) → k = j) ∧
      (∀ x ∈ closedBall (0 : E2) 1, ∀ z ∈ Ioo (t - d) (t + d),
        T (x, z) ∈ range (fun q : UnitTwoSphere => psi j (q, 0)) ↔
          x ∈ sphere (0 : E2) 1) ∧
      (∀ k : Fin n, k ≠ j →
        Disjoint (range (fun q : UnitTwoSphere => psi k (q, 0)))
          (T '' (closedBall (0 : E2) 1 ×ˢ Ioo (t - d) (t + d)))) := by
  classical
  let S : Fin n → Set E3 := fun i => range (fun q : UnitTwoSphere => psi i (q, 0))
  let A : Set E3 := T '' (sphere (0 : E2) 1 ×ˢ Ioo (t - d) (t + d))
  have hcompact (i : Fin n) : IsCompact (S i) :=
    isCompact_range (collar_central_contMDiff (psi i) (hembed i)).continuous
  have hdim : 1 < Module.rank ℝ E2 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
  have hcircle : IsConnected (sphere (0 : E2) 1) :=
    isConnected_sphere hdim 0 zero_le_one
  have hA : IsPreconnected A :=
    (hcircle.isPreconnected.prod isPreconnected_Ioo).image T
      (T.continuousOn.mono (fun _ hp =>
        hsource ⟨sphere_subset_closedBall hp.1, mem_univ _⟩))
  obtain ⟨x0, hx0⟩ := hcircle.nonempty
  have ht : t ∈ Ioo (t - d) (t + d) := ⟨by linarith only [hd], by linarith only [hd]⟩
  have hyA : T (x0, t) ∈ A := ⟨(x0, t), ⟨hx0, ht⟩, rfl⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp
    ((hwhole x0 (sphere_subset_closedBall hx0) t ht).mpr hx0)
  let V : Set E3 := ⋃ k : {k : Fin n // k ≠ j}, S k.1
  have hV : IsCompact V := isCompact_iUnion (fun k => hcompact k.1)
  have hdis : Disjoint (S j) V := by
    apply Set.disjoint_left.mpr
    intro y hyj hyv
    obtain ⟨k, hk⟩ := mem_iUnion.mp hyv
    exact Set.disjoint_left.mp (hdisjoint k.2) hk hyj
  have hcover : A ⊆ S j ∪ V := by
    rintro y ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp
      ((hwhole x (sphere_subset_closedBall hx) z hz).mpr hx)
    by_cases hkj : k = j
    · exact Or.inl (hkj ▸ hk)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hkj⟩, hk⟩)
  have howner : A ⊆ S j := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hA (S j) V
        (hcompact j).isClosed hV.isClosed hcover
        (by rw [hdis.inter_eq, inter_empty]) with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.mp hdis hj (h hyA))
  have hboundary : ∀ x ∈ sphere (0 : E2) 1, ∀ z ∈ Ioo (t - d) (t + d),
      T (x, z) ∈ S j := by
    intro x hx z hz
    exact howner ⟨(x, z), ⟨hx, hz⟩, rfl⟩
  refine ⟨j, hboundary, ?_, ?_, ?_⟩
  · intro k hk
    by_contra hkj
    exact Set.disjoint_left.mp (hdisjoint hkj) (hk x0 hx0 t ht) hj
  · intro x hx z hz
    exact ⟨fun hy => (hwhole x hx z hz).mp (mem_iUnion.mpr ⟨j, hy⟩),
      fun hcircle => hboundary x hcircle z hz⟩
  · intro k hkj
    apply Set.disjoint_left.mpr
    rintro y hy ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    have hcircle := (hwhole x hx z hz).mp (mem_iUnion.mpr ⟨k, hy⟩)
    exact Set.disjoint_left.mp (hdisjoint hkj) hy (hboundary x hcircle z hz)

end PoincareConjecture.M25.Topology3D
