import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexFamily









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : SimplicialComplex ℝ E}
  [Fintype K.faces] [Fintype L.faces] {T : BoundaryTriangleFibers K L}
  {P : BoundaryEdgeFamily T}

local notation "I" => Icc (0 : ℝ) 1



theorem BoundaryVertexFamily.agrees (F : BoundaryVertexFamily P)
    (p q : L.vertices) (x : E × ℝ)
    (hx : x ∈ (L.barycentricDualBlock {(p : E)}).space ×ˢ I)
    (hy : x ∈ (L.barycentricDualBlock {(q : E)}).space ×ˢ I) :
    (F.chart p ⟨x, hx⟩ : E) = F.chart q ⟨x, hy⟩ := by
  classical
  by_cases hpq : p = q
  · subst q
    rfl
  have hpq' : (p : E) ≠ (q : E) := fun h => hpq (Subtype.ext h)
  let s : Finset E := {(p : E), (q : E)}
  have hmeet : (L.barycentricDualBlock {(p : E)}).space ∩
      (L.barycentricDualBlock {(q : E)}).space = (L.barycentricDualBlock s).space := by
    rw [L.barycentricDualBlock_space_inter]
    simp only [Finset.singleton_union, s]
  have hxS : x.1 ∈ (L.barycentricDualBlock s).space := hmeet.subset ⟨hx.1, hy.1⟩
  have hs : s ∈ L.faces := by
    by_contra hn
    rw [L.barycentricDualBlock_space_eq_empty_of_not_face
      ⟨p, Finset.mem_insert_self _ _⟩ hn] at hxS
    exact hxS
  have hc : s.card = 2 := by simp only [s, Finset.card_pair hpq']
  have hps : (p : E) ∈ s := Finset.mem_insert_self _ _
  have hqs : (q : E) ∈ s := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact (F.keep_edge p s hs hc hps x ⟨hxS, hx.2⟩).trans
    (F.keep_edge q s hs hc hqs x ⟨hxS, hx.2⟩).symm




theorem BoundaryVertexFamily.overlap_iff (F : BoundaryVertexFamily P)
    (hfull : ∀ u ∈ K.faces, (∀ p ∈ u, p ∈ L.vertices) → u ∈ L.faces)
    (p q : L.vertices)
    (x : ((L.barycentricDualBlock {(p : E)}).space ×ˢ I : Set (E × ℝ))) :
    (x : E × ℝ) ∈ (L.barycentricDualBlock {(q : E)}).space ×ˢ I ↔
      (F.chart p x : E) ∈ (K.barycentricDualBlock {(q : E)}).space := by
  classical
  by_cases hpq : p = q
  · subst q
    exact iff_of_true x.property (F.chart p x).property
  have hpq' : (p : E) ≠ (q : E) := fun h => hpq (Subtype.ext h)
  let s : Finset E := {(p : E), (q : E)}
  have hc : s.card = 2 := by simp only [s, Finset.card_pair hpq']
  have hps : (p : E) ∈ s := Finset.mem_insert_self _ _
  have hqs : (q : E) ∈ s := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmeet : (K.barycentricDualBlock {(p : E)}).space ∩
      (K.barycentricDualBlock {(q : E)}).space = (K.barycentricDualBlock s).space := by
    rw [K.barycentricDualBlock_space_inter]
    simp only [Finset.singleton_union, s]
  constructor
  · intro hxq
    rw [F.agrees p q x x.property hxq]
    exact (F.chart q ⟨x, hxq⟩).property
  · intro hyq
    have hyS : (F.chart p x : E) ∈ (K.barycentricDualBlock s).space :=
      hmeet.subset ⟨(F.chart p x).property, hyq⟩
    have hsK : s ∈ K.faces := by
      by_contra hn
      rw [K.barycentricDualBlock_space_eq_empty_of_not_face ⟨p, hps⟩ hn] at hyS
      exact hyS
    have hsL : s ∈ L.faces := hfull s hsK (by
      intro r hr
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact p.property
      · exact q.property)
    obtain ⟨y, hy, hyeq⟩ := (P.image_eq s hsL hc).symm.subset hyS
    have hyp : y.1 ∈ (L.barycentricDualBlock {(p : E)}).space :=
      space_subset_of_le (L.barycentricDualBlock_antitone
        (Finset.singleton_subset_iff.mpr hps)) hy.1
    have he : F.chart p ⟨y, ⟨hyp, hy.2⟩⟩ = F.chart p x :=
      Subtype.ext ((F.keep_edge p s hsL hc hps y hy).trans hyeq)
    have hyx : y = (x : E × ℝ) := congrArg Subtype.val ((F.chart p).injective he)
    exact hyx ▸ ⟨space_subset_of_le (L.barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr hqs)) hy.1, hy.2⟩

end Geometry.SimplicialComplex
