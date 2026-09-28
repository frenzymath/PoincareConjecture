import PoincareConjecture.Proofs.M76.Triangulation.HamiltonFiniteComposition
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonSimplexOrder
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonSimplexCarrier
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonSimplexAtlasStep

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

theorem exists_finite_atlas_supported_straightening
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (c : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (hcompat : ∀ i j, (c i).symm.trans (c j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (hcover : ∀ x : X, ∃ i, x ∈ (c i).source)
    (d : OpenPartialHomeomorph X (Fin 3 → ℝ)) (hd : d.source = univ)
    (hhandle : ∀ J : Finset (Fin 3), HasHamiltonChartHandleStraightening (Fin 3 → ℝ) J)
    {Q : Set X} (hQ : IsCompact Q) :
    ∃ (F : X ≃ₜ X) (U S : Set X),
      IsOpen U ∧ IsCompact S ∧ EqOn F id Sᶜ ∧ Q ⊆ U ∧
      ∀ i, LocallyPiecewiseAffineOn ((d ∘ F) ∘ (c i).symm)
        ((c i).target ∩ (c i).symm ⁻¹' U) := by
  classical
  obtain ⟨t, C, K, G, _, hQC, _, hK, hcharts⟩ :=
    OpenPartialHomeomorph.exists_compact_old_chart_simplex_presentation
      c hcompat hcover hQ isOpen_univ (subset_univ Q)
  obtain ⟨n, f, _, hfaces, _, hspace, hprefix⟩ := K.exists_hamilton_face_order hK
  let B : ℕ → Set (t → ℝ × (Fin 3 → ℝ)) := fun k =>
    ⋃ j : Fin n, ⋃ (_ : j.val < k), convexHull ℝ (f j : Set (t → ℝ × (Fin 3 → ℝ)))
  let P : ℕ → Set X := fun k => hamiltonModelCarrier G (B k)
  have hface (i : Fin n) : f i ∈ K.faces := hfaces ▸ mem_range_self i
  have hBK (k : ℕ) : B k ⊆ K.space := by
    intro x hx
    obtain ⟨j, _, hxj⟩ := mem_iUnion₂.mp hx
    exact K.convexHull_subset_space (hface j) hxj
  have hBP (i : Fin n) : B i.val =
      ⋃ j ∈ Iio i, convexHull ℝ (f j : Set (t → ℝ × (Fin 3 → ℝ))) := by
    ext x
    simp only [B, mem_iUnion, mem_Iio, Fin.lt_def]
  have hBn : B n = K.space := by
    rw [← hspace]
    ext x
    simp only [B, mem_iUnion]
    exact ⟨fun ⟨j, _, hx⟩ => ⟨j, hx⟩, fun ⟨j, hx⟩ => ⟨j, j.isLt, hx⟩⟩
  have hP0 : P 0 = ∅ := by simp [P, B, hamiltonModelCarrier]
  have hPnext (k : ℕ) (hk : k < n) :
      P (k + 1) = P k ∪ hamiltonModelCarrier G
        (convexHull ℝ (f ⟨k, hk⟩ : Set (t → ℝ × (Fin 3 → ℝ)))) := by
    have hnext : B (k + 1) = B k ∪
        convexHull ℝ (f ⟨k, hk⟩ : Set (t → ℝ × (Fin 3 → ℝ))) := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        by_cases hjk : j.val < k
        · exact Or.inl (mem_iUnion₂.mpr ⟨j, hjk, hxj⟩)
        · have hj' : j.val < k + 1 := hj
          have hval : j.val = k :=
            Nat.le_antisymm (Nat.le_of_lt_succ hj') (Nat.le_of_not_gt hjk)
          have heq : j = ⟨k, hk⟩ := Fin.ext hval
          exact Or.inr (heq ▸ hxj)
      · rintro (hx | hx)
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
          exact mem_iUnion₂.mpr ⟨j, Nat.lt_succ_of_lt hj, hxj⟩
        · exact mem_iUnion₂.mpr ⟨⟨k, hk⟩, Nat.lt_succ_self k, hx⟩
    simp only [P, hamiltonModelCarrier, hnext, preimage_union, image_union]
  have hQlast : Q ⊆ P n := by
    intro x hx
    let y : C := ⟨x, interior_subset (hQC hx)⟩
    refine ⟨G.symm y, ?_, ?_⟩
    · change (G.symm y : t → ℝ × (Fin 3 → ℝ)) ∈ B n
      rw [hBn]
      exact (G.symm y).property
    · change (G (G.symm y) : X) = x
      rw [G.apply_symm_apply]
  obtain ⟨F, U, S, hU, hS, _, hF, hPU, hPL⟩ :=
    exists_finite_supported_atlas_composition c d hd P hP0 n univ (by
      intro k hk d' hd' U hU hPU hUpl
      let j : Fin n := ⟨k, hk⟩
      obtain ⟨i, a, hformula, hinj, _⟩ := hcharts (f j) (hface j)
      obtain ⟨hs, hindep, htarget, hcarrier, hfrontier, hinterior⟩ :=
        hamilton_face_coordinates K G (hface j) (c i) a hformula hinj
      have hPk : IsCompact (P k) := by
        apply isCompact_hamiltonModelCarrier G _ (hBK k)
        rw [show k = j.val from rfl, hBP]
        exact (hprefix j).1
      have hfront : (c i).symm '' intrinsicFrontier ℝ
          (convexHull ℝ ((f j).image a : Set (Fin 3 → ℝ))) ⊆ U := by
        rw [← hfrontier]
        apply (hamiltonModelCarrier_mono G ?_).trans hPU
        rw [show k = j.val from rfl, hBP]
        exact (hprefix j).2.1
      have hdis : Disjoint ((c i).symm '' intrinsicInterior ℝ
          (convexHull ℝ ((f j).image a : Set (Fin 3 → ℝ)))) (P k) := by
        rw [← hinterior]
        apply (disjoint_hamiltonModelCarrier G ?_).symm
        rw [show k = j.val from rfl, hBP]
        exact (hprefix j).2.2
      obtain ⟨F, V, S, hV, hS, hSW, _, hF, hPV, hPL⟩ :=
        exists_simplex_atlas_handle_step c hcompat hcover d' hhandle i
          ((f j).image a) hs hindep htarget hU isOpen_univ hPk.isClosed hPU
          (by rw [hd', inter_self]; exact subset_univ _) hfront hdis hUpl
      refine ⟨F, V, S, hV, hS, hSW, hF, ?_, hPL⟩
      rw [hPnext k hk, hcarrier]
      exact hPV)
  exact ⟨F, U, S, hU, hS, hF, hQlast.trans hPU, hPL⟩

end PoincareConjecture.M76
