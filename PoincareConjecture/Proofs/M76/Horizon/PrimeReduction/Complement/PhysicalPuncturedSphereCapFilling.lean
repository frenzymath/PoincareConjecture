import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ChosenHolePuncturedBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing

set_option autoImplicit false

open Set Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

theorem exists_physical_punctured_sphere_cap_filling
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (R : Set E) (a r : ι → Set V4)
    (ha : ∀ j, IsFinitePLBallPair V3 (a j) (r j))
    (haS : ∀ j, a j ⊆ sphere)
    (hopen : ∀ j, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a j \ r j)))
    (hdis : Pairwise fun j k => Disjoint (a j) (a k)) (i : ι)
    (C : R ≃ₜ (sphere \ ⋃ j, a j \ r j : Set V4)) (hC : C.IsFinitePL)
    (q : ι → Set E) (hqR : ∀ j, q j ⊆ R)
    (hmark : ∀ j (x : R), (x : E) ∈ q j ↔ (C x : V4) ∈ r j)
    (D : {j : ι // j ≠ i} → Set E)
    (hD : ∀ j, IsFinitePLBallPair V3 (D j) (q j))
    (hcontact : ∀ j, D j ∩ R = q j)
    (hDdis : Pairwise fun j k => Disjoint (D j) (D k)) :
    ∃ H : (R ∪ ⋃ j, D j : Set E) ≃ₜ (sphere \ (a i \ r i) : Set V4),
      H.IsFinitePL ∧
      (∀ x : R, (H ⟨x, Or.inl x.property⟩ : V4) = C x) ∧
      (∀ x : (R ∪ ⋃ j, D j : Set E), (x : E) ∈ q i ↔ (H x : V4) ∈ r i) ∧
      IsFinitePLBallPair V3 (R ∪ ⋃ j, D j) (q i) := by
  classical
  let J := {j : ι // j ≠ i}
  let P : Set V4 := sphere \ ⋃ j, a j \ r j
  have hchosen := selected_hole_punctured_ball a r ha haS hopen hdis i
  have hrP (j : ι) : r j ⊆ P := hchosen.2.2.2 j
  have haP (j : ι) : a j ∩ P = r j := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxr
      exact hx.2.2 (mem_iUnion.mpr ⟨j, hx.1, hxr⟩)
    · exact fun x hx => ⟨(ha j).1 hx, hrP j hx⟩
  have hext (j : J) : ∃ e : D j ≃ₜ a j, e.IsFinitePL ∧
      (∀ x : q j, (e ⟨x, (hD j).1 x.property⟩ : V4) =
        C ⟨x, hqR j x.property⟩) ∧
      ∀ x : D j, (x : E) ∈ q j ↔ (e x : V4) ∈ r j := by
    have hcopy := hD j
    have hCcopy := hC
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKD, _⟩, _⟩, _⟩ := hcopy
    obtain ⟨_, ⟨L, hL, hLR, _⟩, _⟩ := hCcopy
    obtain ⟨T, hT, hTq⟩ := K.exists_finite_triangulation_inter L hK hL
    rw [hKD, hLR, hcontact j] at hTq
    let b := C.restrictSubsets (hqR j) (hrP j) (hmark j)
    have hb : b.IsFinitePL := hC.restrictSubsets (hqR j) (hrP j) (hmark j) T hT hTq
    obtain ⟨e, he, hkeep, hmem⟩ := (hD j).exists_extension (ha j) b hb
    exact ⟨e, he, fun x => congrArg Subtype.val (hkeep x), hmem⟩
  choose e he hekeep hemem using hext
  let S : Option J → Set E := fun j => j.elim R D
  let T : Option J → Set V4 := fun j => j.elim P (fun j => a j)
  let f : ∀ j, S j ≃ₜ T j := fun j => match j with
    | none => C
    | some j => e j
  have hf (j : Option J) : (f j).IsFinitePL := by
    cases j with
    | none => exact hC
    | some j => exact he j
  have hbase (j : J) (x : R) : (x : E) ∈ D j ↔ (C x : V4) ∈ a j := by
    have hleft : (x : E) ∈ D j ↔ (x : E) ∈ q j := by
      rw [← hcontact j]
      simp only [mem_inter_iff, x.property, and_true]
    have hright : (C x : V4) ∈ a j ↔ (C x : V4) ∈ r j := by
      exact ⟨fun hx => (haP j).subset ⟨hx, (C x).property⟩, fun hx => (ha j).1 hx⟩
    exact hleft.trans ((hmark j x).trans hright.symm)
  have hcap (j : J) (x : D j) : (x : E) ∈ R ↔ (e j x : V4) ∈ P := by
    have hleft : (x : E) ∈ R ↔ (x : E) ∈ q j := by
      rw [← hcontact j]
      simp only [mem_inter_iff, x.property, true_and]
    have hright : (e j x : V4) ∈ P ↔ (e j x : V4) ∈ r j := by
      rw [← haP j]
      simp only [mem_inter_iff, (e j x).property, true_and]
    exact hleft.trans ((hemem j x).trans hright.symm)
  have hoverlap (j k : Option J) (x : S j) :
      (x : E) ∈ S k ↔ (f j x : V4) ∈ T k := by
    cases j with
    | none =>
      cases k with
      | none => exact iff_of_true x.property (C x).property
      | some k => exact hbase k x
    | some j =>
      cases k with
      | none => exact hcap j x
      | some k =>
        by_cases hjk : j = k
        · subst k
          exact iff_of_true x.property (e j x).property
        · exact iff_of_false
            (fun hx => disjoint_left.mp (hDdis hjk) x.property hx)
            (fun hx => disjoint_left.mp (hdis (Subtype.val_injective.ne hjk))
              (e j x).property hx)
  have hagree (j k : Option J) (x : E) (hj : x ∈ S j) (hk : x ∈ S k) :
      (f j ⟨x, hj⟩ : V4) = f k ⟨x, hk⟩ := by
    cases j with
    | none =>
      cases k with
      | none => rfl
      | some k => exact (hekeep k ⟨x, (hcontact k).subset ⟨hk, hj⟩⟩).symm
    | some j =>
      cases k with
      | none => exact hekeep j ⟨x, (hcontact j).subset ⟨hj, hk⟩⟩
      | some k =>
        by_cases hjk : j = k
        · subst k; rfl
        · exact (disjoint_left.mp (hDdis hjk) hj hk).elim
  obtain ⟨U, hU, hUkeep⟩ := Homeomorph.exists_iUnion_finitePL S T f hf hoverlap hagree
  have hS : (⋃ j, S j) = R ∪ ⋃ j, D j := by
    ext x
    simp [S, Option.exists, J]
  have hT : (⋃ j, T j) = sphere \ (a i \ r i) := by
    have hTU : (⋃ j, T j) = P ∪ ⋃ j : J, a j := by
      ext x
      simp [T, Option.exists]
    rw [hTU]
    apply Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · exact ⟨hx.1, fun hi => hx.2 (mem_iUnion.mpr ⟨i, hi⟩)⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        exact (hchosen.2.1 j hj).1
    · intro x hx
      by_cases hp : x ∈ P
      · exact Or.inl hp
      · have hh : x ∈ ⋃ j, a j \ r j := by
          by_contra hn
          exact hp ⟨hx.1, hn⟩
        obtain ⟨j, hj⟩ := mem_iUnion.mp hh
        have hji : j ≠ i := by rintro rfl; exact hx.2 hj
        exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj.1⟩)
  let H := (Homeomorph.setCongr hS.symm).trans (U.trans (Homeomorph.setCongr hT))
  have hH : H.IsFinitePL := hU.setCongr hS hT
  have hkeep (x : R) : (H ⟨x, Or.inl x.property⟩ : V4) = C x := hUkeep none x
  have hqi : q i ⊆ R ∪ ⋃ j, D j := (hqR i).trans subset_union_left
  have hri : r i ⊆ sphere \ (a i \ r i) := hchosen.1.1
  let b := C.restrictSubsets (hqR i) (hrP i) (hmark i)
  have hboundary (x : (R ∪ ⋃ j, D j : Set E)) :
      (x : E) ∈ q i ↔ (H x : V4) ∈ r i :=
    H.mem_subset_iff_of_extension b hqi hri (fun y => Subtype.ext (hkeep ⟨y, hqR i y.property⟩)) x
  exact ⟨H, hH, hkeep, hboundary, hchosen.1.of_homeomorph hqi H hH hboundary⟩

theorem exists_physical_punctured_sphere_all_cap_filling
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (R : Set E) (a r : ι → Set V4)
    (ha : ∀ j, IsFinitePLBallPair V3 (a j) (r j))
    (haS : ∀ j, a j ⊆ sphere)
    (hopen : ∀ j, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a j \ r j)))
    (hdis : Pairwise fun j k => Disjoint (a j) (a k))
    (C : R ≃ₜ (sphere \ ⋃ j, a j \ r j : Set V4)) (hC : C.IsFinitePL)
    (q : ι → Set E) (hqR : ∀ j, q j ⊆ R)
    (hmark : ∀ j (x : R), (x : E) ∈ q j ↔ (C x : V4) ∈ r j)
    (D : ι → Set E) (hD : ∀ j, IsFinitePLBallPair V3 (D j) (q j))
    (hcontact : ∀ j, D j ∩ R = q j)
    (hDdis : Pairwise fun j k => Disjoint (D j) (D k)) :
    ∃ H : (R ∪ ⋃ j, D j : Set E) ≃ₜ sphere, H.IsFinitePL ∧
      (∀ x : R, (H ⟨x, Or.inl x.property⟩ : V4) = C x) ∧
      ∀ j (x : (R ∪ ⋃ j, D j : Set E)),
        (x : E) ∈ q j ↔ (H x : V4) ∈ r j := by
  classical
  have hex : ∃ H : (R ∪ ⋃ j, D j : Set E) ≃ₜ sphere, H.IsFinitePL ∧
      ∀ x : R, (H ⟨x, Or.inl x.property⟩ : V4) = C x := by
    cases isEmpty_or_nonempty ι with
    | inl hι =>
      have hsource : R = R ∪ ⋃ j, D j := by simp
      have htarget : (sphere \ ⋃ j, a j \ r j : Set V4) = sphere := by simp
      exact ⟨(Homeomorph.setCongr hsource.symm).trans
        (C.trans (Homeomorph.setCongr htarget)), hC.setCongr hsource htarget, fun _ => rfl⟩
    | inr hι =>
      let i : ι := Classical.choice hι
      let J := {j : ι // j ≠ i}
      let U : Set E := R ∪ ⋃ j : J, D j
      let B : Set V4 := sphere \ (a i \ r i)
      obtain ⟨H, hH, hkeep, hboundary, _⟩ := exists_physical_punctured_sphere_cap_filling
        R a r ha haS hopen hdis i C hC q hqR hmark (fun j : J => D j)
        (fun j => hD j) (fun j => hcontact j)
        (fun j k hjk => hDdis (Subtype.val_injective.ne hjk))
      have hDU : D i ∩ U = q i := by
        apply Subset.antisymm
        · intro x hx
          rcases hx.2 with hxR | hxD
          · exact (hcontact i).subset ⟨hx.1, hxR⟩
          · obtain ⟨j, hj⟩ := mem_iUnion.mp hxD
            exact (disjoint_left.mp (hDdis j.property) hj hx.1).elim
        · exact fun x hx => ⟨(hD i).1 hx, Or.inl (hqR i hx)⟩
      have haB : a i ∩ B = r i := by
        apply Subset.antisymm
        · intro x hx
          by_contra hxr
          exact hx.2.2 ⟨hx.1, hxr⟩
        · exact fun x hx => ⟨(ha i).1 hx, haS i ((ha i).1 hx), fun hh => hh.2 hx⟩
      obtain ⟨G, hG, hGkeep, _, _⟩ := (hD i).exists_union_homeomorph_of_boundary_piece
        (ha i) hDU haB H hH hboundary
      have hsource : D i ∪ U = R ∪ ⋃ j, D j := by
        apply Subset.antisymm
        · intro x hx
          rcases hx with hx | hxR | hxD
          · exact Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
          · exact Or.inl hxR
          · obtain ⟨j, hj⟩ := mem_iUnion.mp hxD
            exact Or.inr (mem_iUnion.mpr ⟨j, hj⟩)
        · intro x hx
          rcases hx with hxR | hxD
          · exact Or.inr (Or.inl hxR)
          · obtain ⟨j, hj⟩ := mem_iUnion.mp hxD
            by_cases hji : j = i
            · exact Or.inl (hji ▸ hj)
            · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩))
      have htarget : a i ∪ B = sphere := by
        apply Subset.antisymm
        · exact union_subset (haS i) sdiff_subset
        · intro x hx
          by_cases hxa : x ∈ a i
          · exact Or.inl hxa
          · exact Or.inr ⟨hx, fun hh => hxa hh.1⟩
      let F := (Homeomorph.setCongr hsource.symm).trans
        (G.trans (Homeomorph.setCongr htarget))
      refine ⟨F, hG.setCongr hsource htarget, ?_⟩
      intro x
      exact (congrArg (fun y : (a i ∪ B : Set V4) => (y : V4))
        (hGkeep ⟨x, Or.inl x.property⟩)).trans (hkeep x)
  obtain ⟨H, hH, hkeep⟩ := hex
  refine ⟨H, hH, hkeep, ?_⟩
  intro j
  have hrP : r j ⊆ sphere \ ⋃ k, a k \ r k := by
    intro x hx
    refine ⟨haS j ((ha j).1 hx), ?_⟩
    intro hh
    obtain ⟨k, hk, hkr⟩ := mem_iUnion.mp hh
    by_cases hjk : j = k
    · exact hkr (hjk ▸ hx)
    · exact disjoint_left.mp (hdis hjk) ((ha j).1 hx) hk
  let b := C.restrictSubsets (hqR j) hrP (hmark j)
  exact H.mem_subset_iff_of_extension b ((hqR j).trans subset_union_left)
    ((ha j).1.trans (haS j))
    (fun x => Subtype.ext (hkeep ⟨x, hqR j x.property⟩))

end Set
