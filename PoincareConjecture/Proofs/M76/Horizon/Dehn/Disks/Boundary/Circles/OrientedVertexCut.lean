import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.LocalCofaceLabels
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.VertexCofaceTransport

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex AbstractSimplicialComplex

namespace PoincareConjecture.M76.Dehn

private theorem align_coface_pairs {T : Type*}
    (label : Bool → T → ZMod 2) (t u : Bool → Bool → T)
    (ht : ∀ j b, label j (t j b) = if b then 1 else 0)
    (hu : ∀ j b, u j b = t j false ∨ u j b = t j true)
    (hun : ∀ j, u j false ≠ u j true)
    (htransport : ∀ b, label false (u false b) = label true (u true b)) :
    ∃ flip : Bool, ∀ j b, u j (Bool.xor flip b) = t j b := by
  have hbits : Function.Injective (fun b : Bool => (if b then 1 else 0 : ZMod 2)) := by
    intro b c h
    cases b <;> cases c <;> simp_all
  have hunique (j b c : Bool) (h : label j (t j b) = label j (t j c)) : b = c := by
    apply hbits
    simpa only [ht] using h
  have hother (b : Bool) (h : u false false = t false b) : u false true = t false (!b) := by
    rcases hu false true with h0 | h1 <;> cases b
    · exact False.elim (hun false (h.trans h0.symm))
    · exact h0
    · exact h1
    · exact False.elim (hun false (h.trans h1.symm))
  have htrue (i b : Bool) (h : u false i = t false b) : u true i = t true b := by
    have he : label true (u true i) = label true (t true b) := by
      rw [← htransport, h, ht, ht]
    rcases hu true i with h0 | h1
    · rw [h0] at he
      exact (hunique true false b he) ▸ h0
    · rw [h1] at he
      exact (hunique true true b he) ▸ h1
  rcases hu false false with h0 | h1
  · refine ⟨false, ?_⟩
    have h1 := hother false h0
    intro j b
    cases j <;> cases b
    · exact h0
    · exact h1
    · exact htrue false false h0
    · exact htrue true true h1
  · refine ⟨true, ?_⟩
    have h0 := hother true h1
    intro j b
    cases j <;> cases b
    · exact h0
    · exact h1
    · exact htrue true false h0
    · exact htrue false true h1




theorem exists_oriented_boundary_vertex_cut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (A L : SimplicialComplex ℝ E) [Fintype A.faces] [Fintype L.faces]
    (hLA : L ≤ A)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hfull : ∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ 2)
    (number : E → ℕ) (sign : Finset E → ZMod 2) (hnumber : InjOn number A.vertices)
    (hcancel : ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (v : E) (p : Bool → E) (hvp : ∀ j, v ≠ p j) (hpne : p false ≠ p true)
    (hedge : ∀ j, ({v, p j} : Finset E) ∈ L.faces)
    (hlink : IsConnected (A.link v).space)
    (hexhaust : ∀ s ∈ L.faces, v ∈ s → s.card = 2 →
      s = {v, p false} ∨ s = {v, p true})
    (t : Bool → Bool → Finset E)
    (_ht : ∀ j b, t j b ∈ A.faces ∧ (t j b).card = 3 ∧ ({v, p j} : Finset E) ⊆ t j b)
    (htex : ∀ j u, u ∈ A.faces → u.card = 3 → ({v, p j} : Finset E) ⊆ u →
      u = t j false ∨ u = t j true)
    (htsign : ∀ j b, sign (t j b) + orderedCofaceParity number (t j b)
      (if j then v else p false) (if j then p true else v) = if b then 1 else 0) :
    let V := (A.barycentricDualBlock {v}).space
    let W := (A.barycentricSubdivision.link v).space
    let Z := V ∩ L.space
    let c := fun j => ({v, p j} : Finset E).centroid ℝ id
    c false ≠ c true ∧ IsFinitePLBallPair ℝ Z {c false, c true} ∧
      ∃ (U F : Bool → Set E),
        (∀ b, IsFinitePLBallPair ℝ (U b) {c false, c true}) ∧
        (∀ b, IsFinitePLBallPair (ℝ × ℝ) (F b) (Z ∪ U b)) ∧
        (∀ b, Z ∩ U b = {c false, c true}) ∧
        U false ∪ U true = W ∧ U false ∩ U true = {c false, c true} ∧
        F false ∪ F true = V ∧ F false ∩ F true = Z ∧
        ∀ j b, segment ℝ (c j) ((t j b).centroid ℝ id) ⊆ U b := by
  classical
  let s := fun j => ({v, p j} : Finset E)
  have hv : v ∈ L.vertices := L.face_subset_vertices (hedge false) (Finset.mem_insert_self _ _)
  have hsc (j : Bool) : (s j).card = 2 := Finset.card_pair (hvp j)
  have hvs (j : Bool) : v ∈ s j := Finset.mem_insert_self _ _
  have hsne : s false ≠ s true := by
    intro he
    have hp : p false ∈ s true := he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases Finset.mem_insert.mp hp with h | h
    · exact hvp false h.symm
    · exact hpne (Finset.mem_singleton.mp h)
  obtain ⟨hc, _, hZ, hZW, _, U₀, U₁, F₀, F₁, hU₀, hU₁, hUU, hUI,
    hF₀, hF₁, hFU, hFI, _, _⟩ := exists_boundary_circle_vertex_cut
      A L hLA hpure hcofaces hLcard hv hlink s hedge hsc hvs hsne hexhaust
  let U : Bool → Set E := fun b => if b then U₁ else U₀
  let F : Bool → Set E := fun b => if b then F₁ else F₀
  let Z := (A.barycentricDualBlock {v}).space ∩ L.space
  let c := fun j => (s j).centroid ℝ id
  have hU (b : Bool) : IsFinitePLBallPair ℝ (U b) {c false, c true} := by
    cases b
    · exact hU₀
    · exact hU₁
  have hF (b : Bool) : IsFinitePLBallPair (ℝ × ℝ) (F b) (Z ∪ U b) := by
    cases b
    · simpa only [F, U, Bool.false_eq_true, ↓reduceIte, union_comm] using hF₀
    · exact hF₁
  have hZU (b : Bool) : Z ∩ U b = {c false, c true} := by
    have hUW : U b ⊆ (A.barycentricSubdivision.link v).space := by
      rw [← hUU]
      cases b
      · exact subset_union_left
      · exact subset_union_right
    exact Subset.antisymm (fun _ hx => hZW.subset ⟨hx.1, hUW hx.2⟩)
      (fun _ hx => ⟨hZ.1 hx, (hU b).1 hx⟩)
  have hbound (u : Finset E) (hu : u ∈ A.faces) : u.card ≤ 3 := by
    obtain ⟨w, _, hwc, huw⟩ := hpure u hu
    exact (Finset.card_le_card huw).trans_eq hwc
  obtain ⟨u, hu, hun, huex, _, _, huU, _, _⟩ :=
    exists_boundary_joint_coface_arc_labels A L hLA hbound hcofaces hfull hLcard
      s hedge hsc hvs hsne U hU hUU hUI
  have htransport := vertex_rim_arc_coface_sign_eq A number sign hnumber hcancel
    v p hvp hpne (fun j => hLA (hedge j)) U
    (fun b => (hU b).isCompact.isClosed) (fun b => (hU b).isConnected.isPreconnected)
    hUU hUI (fun j b => (hU b).1 (by cases j; exact Or.inl rfl; exact Or.inr rfl))
    u huex (fun j b => huU j b (right_mem_segment ℝ _ _))
  let label : Bool → Finset E → ZMod 2 := fun j r => sign r + orderedCofaceParity number r
    (if j then v else p false) (if j then p true else v)
  obtain ⟨flip, halign⟩ := align_coface_pairs label t u htsign
    (fun j b => htex j _ (hu j b).1 (hu j b).2.1 (hu j b).2.2) hun
    (show ∀ b, label false (u false b) = label true (u true b) from htransport)
  refine ⟨hc, hZ, (fun b => U (Bool.xor flip b)), (fun b => F (Bool.xor flip b)),
    (fun b => hU _), (fun b => hF _), (fun b => hZU _), ?_, ?_, ?_, ?_, ?_⟩
  · cases flip
    · exact hUU
    · simpa [U, union_comm] using hUU
  · cases flip
    · exact hUI
    · simpa [U, s, inter_comm] using hUI
  · cases flip
    · exact hFU
    · simpa [F, union_comm] using hFU
  · cases flip
    · exact hFI
    · simpa [F, inter_comm] using hFI
  · intro j b
    rw [← halign j b]
    exact huU j _

end PoincareConjecture.M76.Dehn
