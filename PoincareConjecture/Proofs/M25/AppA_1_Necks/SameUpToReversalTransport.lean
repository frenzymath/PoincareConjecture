import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem EpsilonNeck.exists_signed_retained_interval_of_sameUpToReversal
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
    (N P : EpsilonNeck g) (hNP : N.SameUpToReversal P)
    (a b : ℝ) (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    ∃ (sigma a' b' : ℝ),
      ((sigma = 1 ∧ a' = a ∧ b' = b) ∨
        (sigma = -1 ∧ a' = -b ∧ b' = -a)) ∧
      P.epsilon = N.epsilon ∧ P.scale = N.scale ∧
      P.center = N.center ∧ P.carrier = N.carrier ∧
      P.central_sphere = N.central_sphere ∧
      -P.epsilon⁻¹ < a' ∧ b' < P.epsilon⁻¹ ∧
      (a ≤ b ↔ a' ≤ b') ∧
      (∀ x ∈ N.carrier,
        P.coordinate_inverse x =
          ((N.coordinate_inverse x).1, sigma * (N.coordinate_inverse x).2)) ∧
      N.coordinate_map '' (Set.univ ×ˢ Set.Icc a b) =
        P.coordinate_map '' (Set.univ ×ˢ Set.Icc a' b') ∧
      (∀ x ∈ N.carrier,
        (N.coordinate_inverse x).2 ∈ Set.Icc a b ↔
          (P.coordinate_inverse x).2 ∈ Set.Icc a' b') := by
  obtain ⟨he, hs, hc, hU, hS, sigma, hsign, hmap⟩ := hNP
  have hinverse (x : M) (hx : x ∈ N.carrier) :
      P.coordinate_inverse x =
        ((N.coordinate_inverse x).1, sigma * (N.coordinate_inverse x).2) := by
    have hn := (N.coordinate_inverse_mem x hx).2
    have hp : sigma * (N.coordinate_inverse x).2 ∈
        Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ := by
      rw [← he]
      rcases hsign with h | h
      · simpa only [h, one_mul] using hn
      · simp only [h, neg_one_mul, mem_Ioo]
        constructor <;> linarith [hn.1, hn.2]
    have hm := hmap (N.coordinate_inverse x) hn
    rw [N.coordinate_map_inverse hx] at hm
    calc
      P.coordinate_inverse x = P.coordinate_inverse
          (P.coordinate_map ((N.coordinate_inverse x).1,
            sigma * (N.coordinate_inverse x).2)) := congrArg P.coordinate_inverse hm
      _ = _ := P.coordinate_inverse_map _ hp
  have image_eq (a' b' : ℝ) (ha' : -P.epsilon⁻¹ < a')
      (hb' : b' < P.epsilon⁻¹)
      (hmem : ∀ x ∈ N.carrier,
        (N.coordinate_inverse x).2 ∈ Icc a b ↔
          (P.coordinate_inverse x).2 ∈ Icc a' b') :
      N.coordinate_map '' (univ ×ˢ Icc a b) =
        P.coordinate_map '' (univ ×ˢ Icc a' b') := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      have hzN : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
        ⟨ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
      have hxN := N.coordinate_map_mem ⟨hz.1, hzN⟩
      have hxP : N.coordinate_map z ∈ P.carrier := hU ▸ hxN
      refine ⟨P.coordinate_inverse (N.coordinate_map z), ⟨mem_univ _, ?_⟩,
        P.coordinate_map_inverse hxP⟩
      apply (hmem _ hxN).mp
      simpa only [N.coordinate_inverse_map z hzN] using hz.2
    · rintro x ⟨z, hz, rfl⟩
      have hzP : z.2 ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ :=
        ⟨ha'.trans_le hz.2.1, hz.2.2.trans_lt hb'⟩
      have hxP := P.coordinate_map_mem ⟨hz.1, hzP⟩
      have hxN : P.coordinate_map z ∈ N.carrier := hU.symm ▸ hxP
      refine ⟨N.coordinate_inverse (P.coordinate_map z), ⟨mem_univ _, ?_⟩,
        N.coordinate_map_inverse hxN⟩
      apply (hmem _ hxN).mpr
      simpa only [P.coordinate_inverse_map z hzP] using hz.2
  rcases hsign with rfl | rfl
  · have ha' : -P.epsilon⁻¹ < a := by rw [← he]; exact ha
    have hb' : b < P.epsilon⁻¹ := by rw [← he]; exact hb
    have hmem (x : M) (hx : x ∈ N.carrier) :
        (N.coordinate_inverse x).2 ∈ Icc a b ↔
          (P.coordinate_inverse x).2 ∈ Icc a b := by
      rw [hinverse x hx]
      simp only [one_mul]
    exact ⟨1, a, b, Or.inl ⟨rfl, rfl, rfl⟩,
      he.symm, hs.symm, hc.symm, hU.symm, hS.symm,
      ha', hb', Iff.rfl, hinverse, image_eq a b ha' hb' hmem, hmem⟩
  · have ha' : -P.epsilon⁻¹ < -b := by rw [← he]; linarith
    have hb' : -a < P.epsilon⁻¹ := by rw [← he]; linarith
    have horder : a ≤ b ↔ -b ≤ -a := by constructor <;> intro h <;> linarith
    have hmem (x : M) (hx : x ∈ N.carrier) :
        (N.coordinate_inverse x).2 ∈ Icc a b ↔
          (P.coordinate_inverse x).2 ∈ Icc (-b) (-a) := by
      rw [hinverse x hx]
      simp only [neg_one_mul, mem_Icc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    exact ⟨-1, -b, -a, Or.inr ⟨rfl, rfl, rfl⟩,
      he.symm, hs.symm, hc.symm, hU.symm, hS.symm,
      ha', hb', horder, hinverse, image_eq (-b) (-a) ha' hb' hmem, hmem⟩

end PoincareConjecture
