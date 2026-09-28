import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.SeparatedSubcomplex








set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_contact_subcomplex_of_open_agreement
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {S N T V : Set X} (hS : IsClosed S) (hN : IsClosed N) (hT : IsClosed T)
    (Q : OpenPartialHomeomorph X V3) (hTQ : T ⊆ Q.source)
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGs : G.space = Q '' (S ∩ T))
    (hV : IsOpen V) (hNV : N ∩ T ⊆ V)
    (hagree : ∀ x ∈ V, x ∈ N ↔ x ∈ S) :
    ∃ (H : SimplicialComplex ℝ V3) (hHG : H ≤ G), H.faces.Finite ∧
      H.space = Q '' (N ∩ T) ∧
      ∀ v : H.vertices,
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
          (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨v.val,hHG v.property⟩).ncard := by
  classical
  have hsub : N ∩ T ⊆ S ∩ T := fun x hx => ⟨(hagree x (hNV hx)).mp hx.1,hx.2⟩
  have hrest : IsClosed ((S ∩ T) \ N) := by
    have heq : (S ∩ T) \ N = (S ∩ T) \ V := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1,fun hv => hx.2 ((hagree x hv).mpr hx.1.1)⟩
      · intro hx
        exact ⟨hx.1,fun hn => hx.2 (hNV ⟨hn,hx.1.2⟩)⟩
    rw [heq]
    exact (hS.inter hT).sdiff hV
  have hGT : G.space ⊆ Q.target := by
    rw [hGs]
    rintro _ ⟨x,hx,rfl⟩
    exact Q.map_source (hTQ hx.2)
  have hphys : Q.symm '' G.space = S ∩ T := by
    rw [hGs]
    exact Q.symm_image_image_of_subset_source (inter_subset_right.trans hTQ)
  have hcover : Q.symm '' G.space ⊆ N ∪ ((S ∩ T) \ N) := by
    rw [hphys]
    intro x hx
    by_cases hn : x ∈ N
    · exact Or.inl hn
    · exact Or.inr ⟨hx,hn⟩
  obtain ⟨H,hHG,hH,hHs,_,hdegree⟩ := G.exists_subcomplex_of_closed_image_partition
    hG Q.symm (Q.symm.continuousOn.mono hGT) hN hrest
      (disjoint_left.mpr (fun _ hn hx => hx.2 hn)) hcover
  refine ⟨H,hHG,hH,?_,hdegree⟩
  rw [hHs,hGs]
  ext z
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hn⟩
    have hn' : x ∈ N := by simpa only [mem_preimage,Q.left_inv (hTQ hx.2)] using hn
    exact ⟨x,⟨hn',hx.2⟩,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hsub hx,rfl⟩,by
      simpa only [mem_preimage,Q.left_inv (hTQ hx.2)] using hx.1⟩

end PoincareConjecture.M76
