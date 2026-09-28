import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PhysicalSelectedHoleDiskPortSum








set_option autoImplicit false
open Set Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

theorem exists_physical_punctured_sphere_disk_port_gluing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {κ : Bool → Type*} [∀ b, Finite (κ b)]
    (R : Bool → Set E) (a r : ∀ b, κ b → Set V4)
    (ha : ∀ b j, IsFinitePLBallPair V3 (a b j) (r b j))
    (haS : ∀ b j, a b j ⊆ sphere)
    (hopen : ∀ b j, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a b j \ r b j)))
    (hdis : ∀ b, Pairwise fun j k => Disjoint (a b j) (a b k)) (i : ∀ b, κ b)
    (C : ∀ b, R b ≃ₜ (sphere \ ⋃ j, a b j \ r b j : Set V4))
    (hC : ∀ b, (C b).IsFinitePL)
    {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hcontact : R false ∩ R true = d)
    (hport : ∀ b (x : R b), (x : E) ∈ d → (C b x : V4) ∈ r b (i b))
    (hout : ∀ b, ∃ x : R b, (C b x : V4) ∈ r b (i b) ∧ (x : E) ∉ d) :
    let s : Bool → Set E := fun b => (Subtype.val : R b → E) ''
      ((fun x : R b => (C b x : V4)) ⁻¹' r b (i b))
    let outer := (s false \ (d \ q)) ∪ (s true \ (d \ q))
    let J := (b : Bool) × {j : κ b // j ≠ i b}
    let m : J → Set E := fun j => (Subtype.val : R j.1 → E) ''
      ((fun x : R j.1 => (C j.1 x : V4)) ⁻¹' r j.1 j.2)
    ∃ A t : Option J → Set V4,
      (∀ j, IsFinitePLBallPair V3 (A j) (t j) ∧ A j ⊆ sphere ∧
        IsOpen ((Subtype.val : sphere → V4) ⁻¹' (A j \ t j))) ∧
      Pairwise (fun j k => Disjoint (A j) (A k)) ∧
      ∃ H : (R false ∪ R true : Set E) ≃ₜ (sphere \ ⋃ j, A j \ t j : Set V4),
        H.IsFinitePL ∧
        (∀ x : (R false ∪ R true : Set E), (x : E) ∈ outer ↔ (H x : V4) ∈ t none) ∧
        ∀ j (x : (R false ∪ R true : Set E)), (x : E) ∈ m j ↔ (H x : V4) ∈ t (some j) := by
  dsimp only
  let J := (b : Bool) × {j : κ b // j ≠ i b}
  obtain ⟨c,t,hct,hcin,hcout,hcdis,L,F,hL,hLs,hF,hmark,_,houter,_⟩ :=
    exists_physical_selected_hole_disk_port_sum R a r ha haS hopen hdis i C hC
      hd hcontact hport hout
  let A : Option J → Set V4 := Option.elim' upper c
  let T : Option J → Set V4 := Option.elim' seam t
  have hA (j : Option J) : IsFinitePLBallPair V3 (A j) (T j) ∧ A j ⊆ sphere ∧
      IsOpen ((Subtype.val : sphere → V4) ⁻¹' (A j \ T j)) := by
    cases j with
    | none =>
      refine ⟨upper_ball,inter_subset_left,?_⟩
      have heq : (Subtype.val : sphere → V4) ⁻¹' (upper \ seam) =
          ((Subtype.val : sphere → V4) ⁻¹' lower)ᶜ := by
        ext x
        have hx := lower_union_upper.symm.subset x.property
        have hs := Set.ext_iff.mp lower_inter_upper (x : V4)
        simp only [mem_union] at hx
        simp only [mem_inter_iff] at hs
        simp only [mem_preimage,mem_sdiff,mem_compl_iff]
        tauto
      change IsOpen ((Subtype.val : sphere → V4) ⁻¹' (upper \ seam))
      rw [heq]
      exact (lower_ball.isCompact.isClosed.preimage continuous_subtype_val).isOpen_compl
    | some j =>
      refine ⟨hct j,(hcin j).trans (sdiff_subset.trans inter_subset_left),?_⟩
      have h := upper_ball.isOpen_double_ball_hole lower_ball
        (by rw [inter_comm,lower_inter_upper]) (hct j) (hcin j)
      exact h.preimage (Homeomorph.setCongr
        ((union_comm upper lower).trans lower_union_upper).symm).continuous
  have hdisA : Pairwise fun j k => Disjoint (A j) (A k) := by
    intro j k hjk
    cases j with
    | none =>
      cases k with
      | none => exact False.elim (hjk rfl)
      | some k => exact hcout k
    | some j =>
      cases k with
      | none => exact (hcout j).symm
      | some k => exact hcdis (fun h => hjk (congrArg some h))
  have heq : (upper \ seam) ∪ ⋃ j, c j \ t j = ⋃ j, A j \ T j := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨none,hx⟩
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨some j,hj⟩
    · intro hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      cases j with
      | none => exact Or.inl hj
      | some j => exact Or.inr (mem_iUnion.mpr ⟨j,hj⟩)
  let H := F.trans (Homeomorph.setCongr (congrArg (fun Z => sphere \ Z) heq))
  exact ⟨A,T,hA,hdisA,H,hF.setCongr rfl (congrArg (fun Z => sphere \ Z) heq),houter,hmark⟩

end Set
