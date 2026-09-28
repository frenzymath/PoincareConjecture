import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.ClippedSphereDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskEdgeCofaces
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeFaceCarrierBounds

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.clipped_face_card_le_three
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (sS : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J P : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target)
    (hPs : P.space = Q '' (S ∩ Q.source) ∩ J.space)
    {t : Finset V3} (ht : t ∈ P.faces) : t.card ≤ 3 := by
  obtain ⟨L, hL, hLs, hbound, _⟩ := sS.exists_finite_chart_carrier Q hQ J hJ hJQ
  exact P.face_card_le_of_hull_subset_finite_carrier L hL ht
    ((P.convexHull_subset_space ht).trans (hPs.trans hLs.symm).subset) hbound

theorem ChartwisePLSphere.ncard_clipped_edge_triangle_cofaces
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (sS : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J P : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hP : P.faces.Finite)
    (hPs : P.space = Q '' (S ∩ Q.source) ∩ J.space)
    {a : Finset V3} (ha : a ∈ P.faces) (ha2 : a.card = 2)
    {w : V3} (hwa : w ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
    (hwJ : w ∈ interior J.space) :
    {t : Finset V3 | t ∈ P.faces ∧ t.card = 3 ∧ a ⊆ t}.ncard = 2 := by
  have hwP := P.convexHull_subset_space ha (intrinsicInterior_subset hwa)
  obtain ⟨d, q, hd, hdP, hwd, hopen⟩ :=
    sS.exists_clipped_disk_neighborhood Q hQ J P hJ hJQ hP hPs hwP hwJ
  exact P.ncard_triangle_cofaces_eq_two_of_local_disk hP
    (fun t ht => sS.clipped_face_card_le_three Q hQ J P hJ hJQ hPs ht)
    ha ha2 hwa hd hdP hwd hopen

theorem ChartwisePLSphere.exists_clipped_edge_two_triangle_germ
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (sS : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J P : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hP : P.faces.Finite)
    (hPs : P.space = Q '' (S ∩ Q.source) ∩ J.space)
    {a : Finset V3} (ha : a ∈ P.faces) (ha2 : a.card = 2)
    {w : V3} (hwa : w ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set V3)))
    (hwJ : w ∈ interior J.space) :
    ∃ (t u : Finset V3) (U : Set V3),
      t ∈ P.faces ∧ u ∈ P.faces ∧ t.card = 3 ∧ u.card = 3 ∧
      a ⊆ t ∧ a ⊆ u ∧ t ≠ u ∧
      (∀ b ∈ P.faces, a ⊆ b → b ⊆ t ∨ b ⊆ u) ∧
      IsOpen U ∧ w ∈ U ∧ U ⊆ interior J.space ∧
      ∀ x ∈ U, Q.symm x ∈ S ↔
        x ∈ convexHull ℝ (t : Set V3) ∪ convexHull ℝ (u : Set V3) := by
  obtain ⟨t, u, htu, hset⟩ := ncard_eq_two.mp
    (sS.ncard_clipped_edge_triangle_cofaces Q hQ J P hJ hJQ hP hPs ha ha2 hwa hwJ)
  have ht : t ∈ P.faces ∧ t.card = 3 ∧ a ⊆ t := by
    change t ∈ {b | b ∈ P.faces ∧ b.card = 3 ∧ a ⊆ b}
    rw [hset]
    exact Or.inl rfl
  have hu : u ∈ P.faces ∧ u.card = 3 ∧ a ⊆ u := by
    change u ∈ {b | b ∈ P.faces ∧ b.card = 3 ∧ a ⊆ b}
    rw [hset]
    exact Or.inr rfl
  have hexhaust (b : Finset V3) (hb : b ∈ P.faces) (hab : a ⊆ b) : b ⊆ t ∨ b ⊆ u := by
    have hlow := Finset.card_le_card hab
    have hupp := sS.clipped_face_card_le_three Q hQ J P hJ hJQ hPs hb
    by_cases hb2 : b.card = 2
    · have he : a = b := Finset.eq_of_subset_of_card_le hab (by omega)
      exact Or.inl (he ▸ ht.2.2)
    · have hmem : b ∈ {b | b ∈ P.faces ∧ b.card = 3 ∧ a ⊆ b} := ⟨hb, by omega, hab⟩
      rw [hset] at hmem
      exact hmem.elim (fun h => Or.inl (h ▸ Finset.Subset.rfl))
        (fun h => Or.inr (h ▸ Finset.Subset.rfl))
  obtain ⟨V, hV, hwV, hlocal⟩ :=
    P.exists_open_two_coface_carrier_germ hP ha ht.1 hu.1 hexhaust hwa
  refine ⟨t, u, V ∩ interior J.space, ht.1, hu.1, ht.2.1, hu.2.1,
    ht.2.2, hu.2.2, htu, hexhaust, hV.inter isOpen_interior, ⟨hwV, hwJ⟩,
    inter_subset_right, ?_⟩
  intro x hx
  rw [← hlocal x hx.1, hPs]
  have hxJ := interior_subset hx.2
  constructor
  · intro hxS
    exact ⟨⟨Q.symm x, ⟨hxS, Q.map_target (hJQ hxJ)⟩, Q.right_inv (hJQ hxJ)⟩, hxJ⟩
  · rintro ⟨⟨y, ⟨hyS, hyQ⟩, rfl⟩, _⟩
    simpa only [Q.left_inv hyQ] using hyS

end PoincareConjecture.M76
