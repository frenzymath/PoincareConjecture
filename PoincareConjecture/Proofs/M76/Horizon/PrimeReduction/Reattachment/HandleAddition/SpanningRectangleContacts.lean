import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningBandContactGraph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)

private theorem band_vertical_interval_ball (a : ℝ) {b d : ℝ} (hbd : b < d) :
    IsFinitePLBallPair ℝ ({a} ×ˢ Icc b d : Set P2) {(a,b),(a,d)} := by
  let f : ℝ →ᴬ[ℝ] P2 :=
    (ContinuousAffineMap.const ℝ ℝ a).prod (ContinuousAffineMap.id ℝ ℝ)
  have h := (isFinitePLBallPair_Icc hbd).affine_image f (by
    intro x _ y _ he
    exact congrArg Prod.snd he)
  have hi : f '' Icc b d = ({a} ×ˢ Icc b d : Set P2) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨rfl,hy⟩
    · rintro ⟨hx,hy⟩
      exact ⟨x.2,hy,Prod.ext hx.symm rfl⟩
  rw [hi,image_pair] at h
  exact h

private theorem band_horizontal_interval_ball (b : ℝ) {a c : ℝ} (hac : a < c) :
    IsFinitePLBallPair ℝ (Icc a c ×ˢ {b} : Set P2) {(a,b),(c,b)} := by
  let f : ℝ →ᴬ[ℝ] P2 :=
    (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ b)
  have h := (isFinitePLBallPair_Icc hac).affine_image f (by
    intro x _ y _ he
    exact congrArg Prod.fst he)
  have hi : f '' Icc a c = (Icc a c ×ˢ {b} : Set P2) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy,rfl⟩
    · rintro ⟨hx,hy⟩
      exact ⟨x.1,hx,Prod.ext rfl hy.symm⟩
  rw [hi,image_pair] at h
  exact h

theorem exists_spanning_rectangle_contact_graph
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] [Finite I]
    (n : I → ℕ) (P : ∀ k,Polygon E (n k+3))
    (hP : ∀ k,Function.Injective (P k) ∧ (P k).HasSimplicialEdges)
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))
    (i j : I) (hij : i ≠ j) (r : P2 → E)
    (hr : FinitePiecewiseAffineOn r (Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1))
    (hri : InjOn r (Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1))
    (htrace : (r '' (Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)) ∩ (⋃ k,(P k).boundary ℝ) =
      r '' (({0,1}:Set ℝ) ×ˢ Icc (-1:ℝ) 1))
    (hleft : r '' (({0}:Set ℝ) ×ˢ Icc (-1:ℝ) 1) ⊆ (P i).boundary ℝ)
    (hright : r '' (({1}:Set ℝ) ×ˢ Icc (-1:ℝ) 1) ⊆ (P j).boundary ℝ) :
    let U := r '' (({0}:Set ℝ) ×ˢ Icc (-1:ℝ) 1)
    let V := r '' (({1}:Set ℝ) ×ˢ Icc (-1:ℝ) 1)
    let W := r '' (Icc (0:ℝ) 1 ×ˢ ({1}:Set ℝ))
    let Z := r '' (Icc (0:ℝ) 1 ×ˢ ({-1}:Set ℝ))
    ∃ G : SimplicialComplex ℝ E,G.faces.Finite ∧
      G.space = ((⋃ k,(P k).boundary ℝ) \
        ((U \ {r (0,-1),r (0,1)}) ∪ (V \ {r (1,1),r (1,-1)}))) ∪ (W ∪ Z) ∧
      HasDisjointPolygonPresentation G.space ∧
      (∀ s ∈ G.faces,s.card ≤ 2) ∧
      (∀ x : G.vertices,(G.vertexAbstractComplex.edgeGraph.neighborSet x).ncard = 2) ∧
      Nat.card (ConnectedComponents G.space) + 1 =
        Nat.card (ConnectedComponents ↥(⋃ k,(P k).boundary ℝ)) := by
  classical
  let B : Set P2 := Icc (0:ℝ) 1 ×ˢ Icc (-1:ℝ) 1
  let e0 : Set P2 := {0} ×ˢ Icc (-1:ℝ) 1
  let e1 : Set P2 := {1} ×ˢ Icc (-1:ℝ) 1
  let e2 : Set P2 := Icc (0:ℝ) 1 ×ˢ {1}
  let e3 : Set P2 := Icc (0:ℝ) 1 ×ˢ {-1}
  have he0 : e0 ⊆ B := by rintro x ⟨hx,hy⟩; exact ⟨by simp_all,hy⟩
  have he1 : e1 ⊆ B := by rintro x ⟨hx,hy⟩; exact ⟨by simp_all,hy⟩
  have he2 : e2 ⊆ B := by rintro x ⟨hx,hy⟩; exact ⟨hx,by simp_all⟩
  have he3 : e3 ⊆ B := by rintro x ⟨hx,hy⟩; exact ⟨hx,by simp_all⟩
  let v0 : Fin 4 → P2 := ![(0,-1),(0,1),(1,1),(1,-1)]
  let v : Fin 4 → E := r ∘ v0
  have hvB (k : Fin 4) : v0 k ∈ B := by fin_cases k <;> norm_num [v0,B]
  have hv0 : Function.Injective v0 := by
    intro a b h
    fin_cases a <;> fin_cases b <;> first | rfl | norm_num [v0] at h
  have hvi : Function.Injective v := fun a b h => hv0 (hri (hvB a) (hvB b) h)
  have hU : IsFinitePLBallPair ℝ (r '' e0) {v 0,v 1} := by
    simpa [v,v0,e0,image_pair] using (band_vertical_interval_ball 0 (by norm_num : (-1:ℝ)<1)).image_of_subset hr he0 hri
  have hV : IsFinitePLBallPair ℝ (r '' e1) {v 2,v 3} := by
    simpa [v,v0,e1,image_pair,pair_comm] using (band_vertical_interval_ball 1 (by norm_num : (-1:ℝ)<1)).image_of_subset hr he1 hri
  have hW : IsFinitePLBallPair ℝ (r '' e2) {v 1,v 2} := by
    simpa [v,v0,e2,image_pair] using (band_horizontal_interval_ball 1 (by norm_num : (0:ℝ)<1)).image_of_subset hr he2 hri
  have hZ : IsFinitePLBallPair ℝ (r '' e3) {v 3,v 0} := by
    simpa [v,v0,e3,image_pair,pair_comm] using (band_horizontal_interval_ball (-1) (by norm_num : (0:ℝ)<1)).image_of_subset hr he3 hri
  have hendsB : ({0,1} ×ˢ Icc (-1:ℝ) 1 : Set P2) ⊆ B := by
    rintro x ⟨hx,hy⟩
    rcases hx with hx | hx <;> exact ⟨by simp_all [B],hy⟩
  have hWO : (r '' e2) ∩ (⋃ k,(P k).boundary ℝ) = {v 1,v 2} := by
    apply Subset.antisymm
    · rintro x ⟨⟨y,hy,rfl⟩,hx⟩
      obtain ⟨z,hz,hzy⟩ := htrace.subset ⟨⟨y,he2 hy,rfl⟩,hx⟩
      have heq := hri (hendsB hz) (he2 hy) hzy
      subst z
      rcases hz.1 with h | h
      · exact Or.inl (congrArg r (Prod.ext h hy.2))
      · exact Or.inr (congrArg r (Prod.ext h hy.2))
    · rintro x (rfl | rfl)
      · exact ⟨hW.1 (Or.inl rfl),mem_iUnion_of_mem i (hleft (hU.1 (Or.inr rfl)))⟩
      · exact ⟨hW.1 (Or.inr rfl),mem_iUnion_of_mem j (hright (hV.1 (Or.inl rfl)))⟩
  have hZO : (r '' e3) ∩ (⋃ k,(P k).boundary ℝ) = {v 3,v 0} := by
    apply Subset.antisymm
    · rintro x ⟨⟨y,hy,rfl⟩,hx⟩
      obtain ⟨z,hz,hzy⟩ := htrace.subset ⟨⟨y,he3 hy,rfl⟩,hx⟩
      have heq := hri (hendsB hz) (he3 hy) hzy
      subst z
      rcases hz.1 with h | h
      · exact Or.inr (congrArg r (Prod.ext h hy.2))
      · exact Or.inl (congrArg r (Prod.ext h hy.2))
    · rintro x (rfl | rfl)
      · exact ⟨hZ.1 (Or.inl rfl),mem_iUnion_of_mem j (hright (hV.1 (Or.inr rfl)))⟩
      · exact ⟨hZ.1 (Or.inr rfl),mem_iUnion_of_mem i (hleft (hU.1 (Or.inl rfl)))⟩
  have hWZ : Disjoint (r '' e2) (r '' e3) := by
    apply disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ ⟨z,hz,hzy⟩
    have heq := hri (he3 hz) (he2 hy) hzy
    have hh := congrArg Prod.snd heq
    simp only [e2,e3,mem_prod,mem_singleton_iff] at hy hz
    linarith [hy.2,hz.2]
  exact exists_spanning_band_contact_graph n P hP hdis i j hij v hvi
    (r '' e0) (r '' e1) (r '' e2) (r '' e3) hU hV hW hZ hleft hright hWO hZO hWZ

end PoincareConjecture.M76
