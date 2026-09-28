import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.LocalJointMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedRadiusPrismMaps

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)



theorem exists_boundary_vertex_strip_from_halves
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V Z : Set E) (F U : Bool → Set E) (D : Bool → Bool → Set E)
    (m : Bool → E) (c : Bool → Bool → E)
    (hF : ∀ b, IsFinitePLBallPair P2 (F b) (Z ∪ U b))
    (hZ : IsFinitePLBallPair ℝ Z {m false, m true})
    (hU : ∀ b, IsFinitePLBallPair ℝ (U b) {m false, m true})
    (hZU : ∀ b, Z ∩ U b = {m false, m true})
    (hD : ∀ j b, IsFinitePLBallPair ℝ (D j b) {m j, c j b})
    (hDU : ∀ j b, D j b ⊆ U b)
    (hm : m false ≠ m true) (hmc : ∀ j b, m j ≠ c j b)
    (hDis : ∀ b, Disjoint (D false b) (D true b))
    (hFU : F false ∪ F true = V) (hFI : F false ∩ F true = Z)
    (z : Icc (0 : ℝ) 1 ≃ₜ Z) (hz : z.IsFinitePL)
    (hz0 : (z ⟨0, le_rfl, zero_le_one⟩ : E) = m false)
    (hz1 : (z ⟨1, zero_le_one, le_rfl⟩ : E) = m true)
    (r : ∀ j b, signedTubeRadius 0 b ≃ₜ D j b)
    (hr : ∀ j b, (r j b).IsFinitePL)
    (hrm : ∀ j b, (r j b ⟨(0, 0), left_mem_segment ℝ _ _⟩ : E) = m j)
    (hrc : ∀ j b, (r j b ⟨signedTubeCorner 0 b, right_mem_segment ℝ _ _⟩ : E) = c j b) :
    ∃ G : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) ≃ₜ V, G.IsFinitePL ∧
      (∀ t : Icc (0 : ℝ) 1,
        (G ⟨((0, 0), t), Or.inl (left_mem_segment ℝ _ _), t.property⟩ : E) = z t) ∧
      (∀ j b (x : signedTubeRadius 0 b),
        (G ⟨(x, if j then 1 else 0),
          by cases b; exact Or.inl x.property; exact Or.inr x.property,
          by cases j <;> simp⟩ : E) = r j b x) ∧
      (∀ x : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1),
        (G x : E) ∈ Z ↔ x.val.1 = (0, 0)) ∧
      ∀ b (x : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1)),
        (G x : E) ∈ F b ↔ x.val.1 ∈ signedTubeRadius 0 b := by
  classical
  have hex (b : Bool) := exists_signed_radius_prism_map 0 b 0 1 zero_lt_one
    (fun j => D j b) m (fun j => c j b) (hF b) hZ (hU b) (hZU b)
    (fun j => hD j b) (fun j => hDU j b) hm (fun j => hmc j b) (hDis b)
    z hz hz0 hz1 (fun j => r j b) (fun j => hr j b) (fun j => hrm j b) (fun j => hrc j b)
  choose H hH hHz hHe hHA hHO hHD using hex
  let P : Bool → Set (P2 × ℝ) := fun b => signedTubeRadius 0 b ×ˢ Icc (0 : ℝ) 1
  have hSrcInter : P false ∩ P true = signedTubePrismAxis 0 1 := by
    rw [show P false ∩ P true =
      (signedTubeRadius 0 false ∩ signedTubeRadius 0 true) ×ˢ Icc (0 : ℝ) 1 by
        ext x; simp only [P, mem_inter_iff, mem_prod]; tauto]
    exact congrArg (fun s : Set P2 => s ×ˢ Icc (0 : ℝ) 1) (signedTube_radius_inter 0 false)
  have hoverlap (x : P false) : (x : P2 × ℝ) ∈ P true ↔ (H false x : E) ∈ F true := by
    have hx : (x : P2 × ℝ) ∈ P true ↔ (x : P2 × ℝ) ∈ signedTubePrismAxis 0 1 := by
      rw [← hSrcInter]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (H false x : E) ∈ F true ↔ (H false x : E) ∈ Z := by
      rw [← hFI]
      simp only [mem_inter_iff, (H false x).property, true_and]
    rw [hx, hy]
    exact hHA false x
  have hagree (x : P2 × ℝ) (hx : x ∈ P false) (hy : x ∈ P true) :
      (H false ⟨x, hx⟩ : E) = H true ⟨x, hy⟩ := by
    have hzero : x.1 = (0, 0) := (hSrcInter.subset ⟨hx, hy⟩).1
    rcases x with ⟨x, t⟩
    change x = (0, 0) at hzero
    subst x
    exact (hHz false ⟨_, hx.2⟩).trans (hHz true ⟨_, hy.2⟩).symm
  have hSU : P false ∪ P true = signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1 := by
    ext x
    simp only [P, signedTubeSheet, mem_union, mem_prod]
    tauto
  obtain ⟨G₀, hG₀, hGf, hGt⟩ := Homeomorph.exists_union_finitePL (H false) (H true)
    (hH false) (hH true) hoverlap hagree
  let G : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) ≃ₜ V :=
    (Homeomorph.setCongr hSU.symm).trans (G₀.trans (Homeomorph.setCongr hFU))
  have hG : G.IsFinitePL := hG₀.setCongr hSU hFU
  have hkeep (b : Bool) (x : P b) :
      (G ⟨x, by
        exact ⟨by cases b; exact Or.inl x.property.1; exact Or.inr x.property.1,
          x.property.2⟩⟩ : E) = H b x := by
    cases b
    · exact hGf x
    · exact hGt x
  have hGaxis (t : Icc (0 : ℝ) 1) :
      (G ⟨((0, 0), t), Or.inl (left_mem_segment ℝ _ _), t.property⟩ : E) = z t :=
    (hkeep false ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩).trans (hHz false t)
  refine ⟨G, hG, hGaxis, ?_, ?_, ?_⟩
  · intro j b x
    exact (hkeep b ⟨(x, if j then 1 else 0), x.property, by cases j <;> simp⟩).trans
      (hHe b j x)
  · intro x
    rcases x.property.1 with hx | hx
    · rw [hkeep false ⟨x, hx, x.property.2⟩, ← hHA]
      exact and_iff_left x.property.2
    · rw [hkeep true ⟨x, hx, x.property.2⟩, ← hHA]
      exact and_iff_left x.property.2
  · intro b x
    have hs (y : P2 × ℝ) (hy : y ∈ P b) : y ∈ signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1 := by
      exact ⟨by cases b; exact Or.inl hy.1; exact Or.inr hy.1, hy.2⟩
    have ht (y : E) (hy : y ∈ F b) : y ∈ V := by
      rw [← hFU]
      cases b
      · exact Or.inl hy
      · exact Or.inr hy
    have h := G.mem_subset_iff_of_extension (H b) hs ht (fun y => Subtype.ext (hkeep b y)) x
    exact h.symm.trans (and_iff_left x.property.2)

end PoincareConjecture.M76.Dehn
