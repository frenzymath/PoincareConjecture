import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Gluing.CornerCollar
import PoincareConjecture.Proofs.M76.Wall.PLDomainSideCollars










set_option autoImplicit false
open Set Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)




theorem exists_phase_union_local_collars
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N O A B : Set X}
    (he : PLDomain e N) (hO : IsClosed O) (hA : IsClosed A) (hB : IsClosed B)
    (hfront : frontier N = O ∪ (A ∪ B)) (hdis : Disjoint A B)
    (hcorner : ∀ P ∈ ({A, B} : Set (Set X)), ∀ x ∈ P ∩ O,
      ∃ (G : OpenPartialHomeomorph X V3) (psi lambda : V3 →ᴬ[ℝ] ℝ) (w v : V3),
        psi.contLinear w = 1 ∧ psi.contLinear v = 0 ∧ lambda.contLinear v = 1 ∧
        x ∈ G.source ∧
        (∀ y ∈ G.source, y ∈ N ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ P ↔ psi (G y) = 0 ∧ lambda (G y) ≤ 0)) :
    ∃ hSN : A ∪ B ⊆ N,
      ∀ x : ↥(A ∪ B),
        ∃ c : OpenPartialHomeomorph (↥(A ∪ B) × Ico (0 : ℝ) 1) N,
          collarBase x ∈ c.source ∧
            ∀ y, collarBase y ∈ c.source → c (collarBase y) = Set.inclusion hSN y := by
  have hSF : A ∪ B ⊆ frontier N := by
    intro x hx
    rw [hfront]
    exact Or.inr hx
  have hSN : A ∪ B ⊆ N := hSF.trans he.closed.frontier_subset
  refine ⟨hSN, ?_⟩
  have hrim (P Q : Set X) (hPQ : P ∪ Q = A ∪ B) (hQ : IsClosed Q)
      (hPd : Disjoint P Q) (hP : P ∈ ({A, B} : Set (Set X)))
      (x : ↥(A ∪ B)) (hxP : (x : X) ∈ P) (hxO : (x : X) ∈ O) :
      ∃ c : OpenPartialHomeomorph (↥(A ∪ B) × Ico (0 : ℝ) 1) N,
        collarBase x ∈ c.source ∧
          ∀ y, collarBase y ∈ c.source → c (collarBase y) = Set.inclusion hSN y := by
    obtain ⟨G, psi, lambda, w, v, hpw, hpv, hlv, hxG, hN, hPface⟩ :=
      hcorner P hP x ⟨hxP, hxO⟩
    let G' := G.restr Qᶜ
    have hsource : G'.source = G.source ∩ Qᶜ := G.restr_source' Qᶜ hQ.isOpen_compl
    have hxG' : (x : X) ∈ G'.source := by
      rw [hsource]
      exact ⟨hxG, fun hxQ => Set.disjoint_left.mp hPd hxP hxQ⟩
    apply exists_local_collar_of_marked_face_chart hSN G' psi lambda w v hpw hpv hlv
      (fun y hy => hN y ((hsource ▸ hy).1)) _ x hxG'
    intro y hy
    have hy' := hsource ▸ hy
    change y ∈ A ∪ B ↔ psi (G y) = 0 ∧ lambda (G y) ≤ 0
    rw [← hPQ, mem_union, hPface y hy'.1]
    exact or_iff_left hy'.2
  intro x
  by_cases hxO : (x : X) ∈ O
  · rcases x.property with hxA | hxB
    · exact hrim A B rfl hB hdis (by simp) x hxA hxO
    · exact hrim B A (union_comm B A) hA hdis.symm (by simp) x hxB hxO
  · obtain ⟨ell, v, G, hv, hxG, _, _, hhalf⟩ := he.halfspace x (hSF x.property)
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro h
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [h] at hval
      norm_num at hval
    obtain ⟨T, hT⟩ := ell.exists_halfspace_product_homeomorph
      (F := Fin 2 → ℝ) v hv (by simp)
    let G' := (G.restr Oᶜ).transHomeomorph T
    have hsource : G'.source = G.source ∩ Oᶜ := G.restr_source' Oᶜ hO.isOpen_compl
    have hxG' : (x : X) ∈ G'.source := by
      rw [hsource]
      exact ⟨hxG, hxO⟩
    apply exists_positive_halfspace_local_collar G' hSN _ _ x hxG'
    · intro y hy
      have hy' := hsource ▸ hy
      change y ∈ A ∪ B ↔ (T (G y)).2 = 0
      rw [hT]
      have hpair := ((G.isImage_frontier_of_affine_nonneg ell hell hhalf).apply_mem_iff
        hy'.1).symm
      rw [hfront] at hpair
      exact (or_iff_right hy'.2).symm.trans hpair
    · intro y hy
      change y ∈ N ↔ 0 ≤ (T (G y)).2
      rw [hT]
      exact hhalf y ((hsource ▸ hy).1)

end PoincareConjecture.M76.HamiltonIntervalTorus
