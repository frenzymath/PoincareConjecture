import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreFamilyCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem sphere_frontier_family_decrease
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (j : κ)
    (Q : OpenPartialHomeomorph X V3) {F : Set X} (hF : IsClosed F)
    (hFQ : F ⊆ Q.source)
    (hpres : HasDisjointPolygonPresentation (Q '' ((⋃ i, S i) ∩ F)))
    {n : ℕ} (L : Polygon V3 (n + 3))
    (hi : Function.Injective L) (he : L.HasSimplicialEdges)
    (hLS : L.boundary ℝ ⊆ Q '' (S j ∩ F))
    (hrem : IsCompact ((Q '' ((⋃ i, S i) ∩ F)) \ L.boundary ℝ))
    (N : Bool → Set X) (sN : ∀ b, ChartwisePLSphere e (N b))
    (hNd : Disjoint (N true) (N false))
    (hNS : ∀ b i, i ≠ j → Disjoint (N b) (S i))
    (hdelete : (N true ∪ N false) ∩ F = (S j ∩ F) \ Q.symm '' L.boundary ℝ) :
    ∀ b, let S' := Function.update S j (N b)
      HasDisjointPolygonPresentation (Q '' ((⋃ i, S' i) ∩ F)) ∧
      Nat.card (ConnectedComponents ↥(Q '' ((⋃ i, S' i) ∩ F))) <
        Nat.card (ConnectedComponents ↥(Q '' ((⋃ i, S i) ∩ F))) ∧
      (⋃ i, S' i) ∩ F ⊆ (⋃ i, S i) ∩ F := by
  let contact (T : Set X) := Q '' (T ∩ F)
  have hclosed {T : Set X} (sT : ChartwisePLSphere e T) : IsClosed (contact T) :=
    ((sT.isCompact.inter_right hF).image_of_continuousOn
      (Q.continuousOn.mono (inter_subset_right.trans hFQ))).isClosed
  have hmem {T : Set X} {x : V3} (hx : x ∈ contact T) : Q.symm x ∈ T ∩ F := by
    obtain ⟨y,hy,rfl⟩ := hx
    rwa [Q.left_inv (hFQ hy.2)]
  have hsep {T U : Set X} (hTU : Disjoint T U) : Disjoint (contact T) (contact U) :=
    disjoint_left.mpr (fun _ hx hy => disjoint_left.mp hTU (hmem hx).1 (hmem hy).1)
  have hwhole : contact (⋃ i, S i) = ⋃ i, contact (S i) := by
    simp only [contact,iUnion_inter,image_iUnion]
  have hLQ : L.boundary ℝ ⊆ Q.target := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hLS hx
    exact Q.map_source (hFQ hy.2)
  have hdel : contact (N true) ∪ contact (N false) = contact (S j) \ L.boundary ℝ := by
    ext x
    constructor
    · intro hx
      have hxF : Q.symm x ∈ F := by
        rcases hx with hx | hx
        · exact (hmem hx).2
        · exact (hmem hx).2
      have hxN : Q.symm x ∈ N true ∪ N false := by
        rcases hx with hx | hx
        · exact Or.inl (hmem hx).1
        · exact Or.inr (hmem hx).1
      have hh := hdelete.subset ⟨hxN,hxF⟩
      have hxQ : x ∈ Q.target := by
        rcases hx with hx | hx <;> obtain ⟨y,hy,rfl⟩ := hx <;>
          exact Q.map_source (hFQ hy.2)
      exact ⟨⟨Q.symm x,hh.1,Q.right_inv hxQ⟩,
        fun hxL => hh.2 (mem_image_of_mem Q.symm hxL)⟩
    · rintro ⟨hx,hxL⟩
      have hxF := hmem hx
      have hxnot : Q.symm x ∉ Q.symm '' L.boundary ℝ := by
        rintro ⟨z,hz,hzx⟩
        have hxQ : x ∈ Q.target := by
          obtain ⟨y,hy,rfl⟩ := hx
          exact Q.map_source (hFQ hy.2)
        exact hxL ((Q.symm.injOn (hLQ hz) hxQ hzx) ▸ hz)
      have hh := hdelete.symm.subset ⟨hxF,hxnot⟩
      obtain ⟨y,hy,hyx⟩ := hx
      rcases hh.1 with hn | hn
      · exact Or.inl ⟨y,⟨by simpa only [←hyx,Q.left_inv (hFQ hy.2)] using hn,hy.2⟩,hyx⟩
      · exact Or.inr ⟨y,⟨by simpa only [←hyx,Q.left_inv (hFQ hy.2)] using hn,hy.2⟩,hyx⟩
  have hrem' : IsCompact ((⋃ i, contact (S i)) \ L.boundary ℝ) := hwhole ▸ hrem
  have hcounts := cocore_family_count_after_circle_exchange (fun i => contact (S i))
    (fun i => hclosed (sS i)) (fun i k hik => hsep (hdis hik)) j (hwhole ▸ hpres)
    L hi he hLS hrem' (fun b => contact (N b)) (fun b => hclosed (sN b))
    (hsep hNd) (fun b i hij => hsep (hNS b i hij)) hdel
  intro b
  have hupdate : contact (⋃ i, Function.update S j (N b) i) =
      ⋃ i, Function.update (fun i => contact (S i)) j (contact (N b)) i := by
    simp only [contact,iUnion_inter,image_iUnion]
    congr 1
    funext i
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hij]
  refine ⟨?_,?_,?_⟩
  · change HasDisjointPolygonPresentation (contact (⋃ i, Function.update S j (N b) i))
    rw [hupdate]
    exact (hcounts b).1
  · change Nat.card (ConnectedComponents ↥(contact (⋃ i, Function.update S j (N b) i))) <
      Nat.card (ConnectedComponents ↥(contact (⋃ i, S i)))
    rw [hupdate,hwhole]
    exact (hcounts b).2
  · rintro x ⟨hx,hxF⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    refine ⟨?_,hxF⟩
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self] at hi
      apply mem_iUnion_of_mem j
      apply (hdelete.subset ⟨?_,hxF⟩).1.1
      cases b
      · exact Or.inr hi
      · exact Or.inl hi
    · exact mem_iUnion_of_mem i (by simpa only [Function.update_of_ne hij] using hi)

end PoincareConjecture.M76
