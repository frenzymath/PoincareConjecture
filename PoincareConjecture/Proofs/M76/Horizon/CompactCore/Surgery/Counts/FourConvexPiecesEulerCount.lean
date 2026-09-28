import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SquareAnnulusEulerCount








set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex



theorem surfaceEulerCount_eq_zero_of_four_convex_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (C : Fin 4 → SimplicialComplex ℝ E) (hC : ∀ i, (C i).faces.Finite)
    (hcover : K.space = ⋃ i, (C i).space)
    (hconvex : ∀ i, Convex ℝ (C i).space) (hne : ∀ i, (C i).space.Nonempty)
    (P : Fin 4 → AffineSubspace ℝ E) (hCP : ∀ i, (C i).space ⊆ P i)
    (hdim : ∀ i, Module.finrank ℝ (P i).direction ≤ 2)
    (hadj : ((C 0).space ∩ (C 1).space).Nonempty ∧
      ((C 2).space ∩ (C 3).space).Nonempty ∧
      ((C 0).space ∩ (C 3).space).Nonempty ∧
      ((C 1).space ∩ (C 2).space).Nonempty)
    (hdisj : Disjoint (C 0).space (C 2).space ∧
      Disjoint (C 1).space (C 3).space) :
    K.surfaceEulerCount = 0 := by
  classical
  have hCK (i : Fin 4) : (C i).space ⊆ K.space := by
    rw [hcover]
    exact subset_iUnion (fun i => (C i).space) i
  have hface (J : SimplicialComplex ℝ E) (hJ : J.space ⊆ K.space) :
      ∀ s ∈ J.faces, s.card ≤ 3 := by
    intro s hs
    apply J.face_card_le_of_finite_affine_cover (Finset.univ.image P) (d := 2) ?_ ?_ hs
    · intro A hA
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
      exact hdim i
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.subset (hJ hx))
      exact ⟨P i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hCP i hi⟩
  obtain ⟨R, L, hR, hRK, hL⟩ :=
    K.exists_subdivision_with_finite_polyhedra hK C hC hCK
  have hLs (i : Fin 4) : (L i).space = (C i).space := (hL i).2
  have hLf (i : Fin 4) : (L i).faces.Finite := hR.subset (hL i).1
  have hcommon {A B : SimplicialComplex ℝ E}
      (hA : A ≤ R) (hB : B ≤ R) {s t : Finset E}
      (hs : s ∈ A.faces) (ht : t ∈ B.faces) :
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) :=
    R.inter_subset_convexHull (hA hs) (hB ht)
  let U₀₁ := (L 0).unionOfCompatible (L 1) (fun _ hs _ ht =>
    hcommon (hL 0).1 (hL 1).1 hs ht)
  let U₂₃ := (L 2).unionOfCompatible (L 3) (fun _ hs _ ht =>
    hcommon (hL 2).1 (hL 3).1 hs ht)
  let W := (L 0 ⊓ L 3).unionOfCompatible (L 1 ⊓ L 2) (fun _ hs _ ht =>
    hcommon (le_trans inf_le_left (hL 0).1)
      (le_trans inf_le_left (hL 1).1) hs ht)
  have hU₀₁ : U₀₁.faces = (L 0).faces ∪ (L 1).faces := rfl
  have hU₂₃ : U₂₃.faces = (L 2).faces ∪ (L 3).faces := rfl
  have hW : W.faces = (L 0 ⊓ L 3).faces ∪ (L 1 ⊓ L 2).faces := rfl
  have hRcover : R.space = ⋃ i ∈ (Finset.univ : Finset (Fin 4)), (L i).space := by
    simp only [hLs, Finset.mem_univ, iUnion_true]
    exact hRK.space_eq.trans hcover
  have hfaces : R.faces = U₀₁.faces ∪ U₂₃.faces := by
    rw [R.faces_eq_biUnion_of_subcomplex_cover L (fun i => (hL i).1) _ hRcover,
      hU₀₁, hU₂₃]
    ext s
    simp [Fin.exists_fin_succ, or_assoc]
  have hcount (i : Fin 4) : (L i).surfaceEulerCount = 1 :=
    (L i).surfaceEulerCount_eq_one_of_convex_low_dimension (hLf i)
      (hLs i ▸ hconvex i) (hLs i ▸ hne i) (P i) (hLs i ▸ hCP i) (hdim i)
  have hinter (i j : Fin 4) (hn : ((C i).space ∩ (C j).space).Nonempty) :
      (L i ⊓ L j).surfaceEulerCount = 1 := by
    have hs : (L i ⊓ L j).space = (C i).space ∩ (C j).space := by
      rw [space_inf_eq_inter_of_le R (L i) (L j) (hL i).1 (hL j).1, hLs, hLs]
    apply (L i ⊓ L j).surfaceEulerCount_eq_one_of_convex_low_dimension
      ((hLf i).subset inf_le_left) (hs ▸ (hconvex i).inter (hconvex j))
      (hs ▸ hn) (P i) ?_ (hdim i)
    rw [hs]
    exact inter_subset_left.trans (hCP i)
  have hempty (i j : Fin 4) (hd : Disjoint (C i).space (C j).space) :
      (L i ⊓ L j).faces = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨x, hx⟩ := (L i ⊓ L j).nonempty_of_mem_faces hs
    have hi := (L i).convexHull_subset_space hs.1 (subset_convexHull ℝ _ hx)
    have hj := (L j).convexHull_subset_space hs.2 (subset_convexHull ℝ _ hx)
    exact disjoint_left.mp hd ((hLs i).subset hi) ((hLs j).subset hj)
  have h₀₂ := hempty 0 2 hdisj.1
  have h₁₃ := hempty 1 3 hdisj.2
  have hWempty : ((L 0 ⊓ L 3) ⊓ (L 1 ⊓ L 2)).faces = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hs₀₂ : s ∈ (L 0 ⊓ L 2).faces := ⟨hs.1.1, hs.2.2⟩
    rw [h₀₂] at hs₀₂
    exact hs₀₂
  have hRcount : R.surfaceEulerCount = 0 :=
    surfaceEulerCount_four_strip_cover_eq_zero R (L 0) (L 1) (L 2) (L 3)
      U₀₁ U₂₃ W (hLf 0) (hLf 1) (hLf 2) (hLf 3) hU₀₁ hU₂₃ hfaces hW
      (hcount 0) (hcount 1) (hcount 2) (hcount 3)
      (hinter 0 1 hadj.1) (hinter 2 3 hadj.2.1)
      (hinter 0 3 hadj.2.2.1) (hinter 1 2 hadj.2.2.2) h₀₂ h₁₃ hWempty
  exact (K.surfaceEulerCount_eq_of_space_eq R hK hR (hface K subset_rfl)
    (hface R hRK.space_eq.subset) hRK.space_eq.symm).trans hRcount

end Geometry.SimplicialComplex
