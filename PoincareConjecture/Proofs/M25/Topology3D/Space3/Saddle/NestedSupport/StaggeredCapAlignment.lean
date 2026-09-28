import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFullCapAlignment
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRegionUniqueness
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_saddle_nested_three_cap_alignment
    (P : SurgeryCapProfile) (u : UnitTwoSphere)
    (U V : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3)
    (hU : ∀ k, ContDiffOn ℝ ∞ (U k) (U k).source)
    (hUi : ∀ k, ContDiffOn ℝ ∞ (U k).symm (U k).target)
    (hV : ∀ k, ContDiffOn ℝ ∞ (V k) (V k).source)
    (hVi : ∀ k, ContDiffOn ℝ ∞ (V k).symm (V k).target)
    (hUs : ∀ k, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (U k).source)
    (hVs : ∀ k, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (V k).source)
    (hUh : ∀ k x, x ∈ (U k).source → ⟪(u : E3), U k x⟫_ℝ = x.2)
    (hVh : ∀ k x, x ∈ (V k).source → ⟪(u : E3), V k x⟫_ℝ = x.2)
    (S : Set E3) (t z v b : ℝ) (hb : 0 < b) (htz : 4 * b < z - t) (hzv : z < v)
    (hlower : ∀ s ∈ Icc (t - 4 * b) (z + 4 * b),
      S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = s} =
        V 0 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∪
          V 1 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∧
      V 0 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆
        V 1 '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∧
      U 0 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆
        U 1 '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ)))
    (hupper : ∀ s ∈ Icc (v - 4 * b) (v + 4 * b),
      V 2 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
        S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = s})
    (hcircles : ∀ (k : Fin 3), ∀ s ∈ (![Icc (z - 4 * b) (z + 4 * b),
        Icc (t - 4 * b) (t + 4 * b), Icc (v - 4 * b) (v + 4 * b)] : Fin 3 → Set ℝ) k,
      U k '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
        V k '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ))) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let cut : Fin 3 → ℝ := ![z, t, v]
    let sign : Fin 3 → ℝ := ![1, 1, -1]
    let M : Set E3 := (S ∩ {y | z ≤ H y ∧ H y ≤ v}) ∪
      V 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z)
    ∃ eta bound : ℝ, 0 < eta ∧ eta < b ∧ 1 ≤ bound ∧ P.heightBound ≤ bound ∧
      ∀ lambda : Fin 3 → ℝ, (∀ k, 0 < lambda k) → (∀ k, lambda k * bound < eta) →
        let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
        let CU : Fin 3 → Set E3 := fun k =>
          P.capMap (U k) (cut k) (sign k) 0 (lambda k) '' Qminus
        let CV : Fin 3 → Set E3 := fun k =>
          P.capMap (V k) (cut k) (sign k) 0 (lambda k) '' Qminus
        ∃ (F : D3) (K : Set E3),
          F '' (M ∪ ⋃ k : Fin 3, CU k) = M ∪ ⋃ k : Fin 3, CV k ∧
          F.symm '' (M ∪ ⋃ k : Fin 3, CV k) = M ∪ ⋃ k : Fin 3, CU k ∧
          (∀ y ∈ M, F y = y ∧ F.symm y = y) ∧
          IsCompact K ∧
          tsupport (fun y => F y - y) ⊆ K ∧
          tsupport (fun y => F.symm y - y) ⊆ K := by
  have hCore
      (P : SurgeryCapProfile) (u : UnitTwoSphere)
      (U V : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3)
      (hU : ∀ i, ContDiffOn ℝ ∞ (U i) (U i).source)
      (hUi : ∀ i, ContDiffOn ℝ ∞ (U i).symm (U i).target)
      (hV : ∀ i, ContDiffOn ℝ ∞ (V i) (V i).source)
      (hVi : ∀ i, ContDiffOn ℝ ∞ (V i).symm (V i).target)
      (hUs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (U i).source)
      (hVs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (V i).source)
      (hUh : ∀ i x, x ∈ (U i).source → ⟪(u : E3), U i x⟫_ℝ = x.2)
      (hVh : ∀ i x, x ∈ (V i).source → ⟪(u : E3), V i x⟫_ℝ = x.2)
      (S : Set E3) (t z c v epsilon : ℝ)
      (hepsilon : 0 < epsilon)
      (htz : t + 64 * epsilon < z)
      (hzc : z + 64 * epsilon < c)
      (hcv : c + 64 * epsilon < v)
      (hBoundary : ∀ (i : Fin 3) (w : ℝ),
        w ∈ Icc (((![z, t, v] : Fin 3 → ℝ) i) - 8 * epsilon)
          (((![z, t, v] : Fin 3 → ℝ) i) + 8 * epsilon) →
        U i '' (sphere (0 : E2) 1 ×ˢ ({w} : Set ℝ)) =
          V i '' (sphere (0 : E2) 1 ×ˢ ({w} : Set ℝ)))
      (hLower : ∀ w ∈ Icc (t - 8 * epsilon) (z + 8 * epsilon),
        S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = w} =
          (V 0 '' (sphere (0 : E2) 1 ×ˢ ({w} : Set ℝ))) ∪
            (V 1 '' (sphere (0 : E2) 1 ×ˢ ({w} : Set ℝ))))
      (hUpper : ∀ w ∈ Icc (v - 8 * epsilon) (v + 8 * epsilon),
        S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ = w} =
          V 2 '' (sphere (0 : E2) 1 ×ˢ ({w} : Set ℝ)))
      (hInner : Disjoint
        ((U 0 '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon))) ∪
          (V 0 '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon))))
        (V 1 '' (sphere (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon)))) :
      let cut : Fin 3 → ℝ := ![z, t, v]
      let sign : Fin 3 → ℝ := ![1, 1, -1]
      let M : Set E3 :=
        (S ∩ {y : E3 | ⟪(u : E3), y⟫_ℝ ∈ Icc z v}) ∪
          (V 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z))
      let O : Fin 3 → Set E3 :=
        ![{y : E3 | |⟪(u : E3), y⟫_ℝ - z| < 8 * epsilon} ∩
            (V 1 '' (sphere (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon)))ᶜ,
          {y : E3 | |⟪(u : E3), y⟫_ℝ - t| < 8 * epsilon},
          {y : E3 | |⟪(u : E3), y⟫_ℝ - v| < 8 * epsilon}]
      ∃ bound : ℝ, 1 ≤ bound ∧ P.heightBound ≤ bound ∧
        ∀ lambda : Fin 3 → ℝ, (∀ i, 0 < lambda i) →
          (∀ i, lambda i * bound < epsilon) →
          let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
          let CU : Fin 3 → Set E3 := fun i =>
            P.capMap (U i) (cut i) (sign i) 0 (lambda i) '' Qminus
          let CV : Fin 3 → Set E3 := fun i =>
            P.capMap (V i) (cut i) (sign i) 0 (lambda i) '' Qminus
          ∃ (F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (K : Set E3),
            (∀ i, F '' CU i = CV i ∧ F.symm '' CV i = CU i) ∧
            F '' (M ∪ ⋃ i : Fin 3, CU i) = (M ∪ ⋃ i : Fin 3, CV i) ∧
            F.symm '' (M ∪ ⋃ i : Fin 3, CV i) = (M ∪ ⋃ i : Fin 3, CU i) ∧
            (∀ y ∈ M, F y = y ∧ F.symm y = y) ∧
            IsCompact K ∧ K ⊆ (⋃ i : Fin 3, O i) ∧
            tsupport (fun y => F y - y) ⊆ K ∧
            tsupport (fun y => F.symm y - y) ⊆ K ∧
            (∀ y, y ∉ K → F y = y ∧ F.symm y = y) := by
    classical
    dsimp only
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let cut : Fin 3 → ℝ := ![z, t, v]
    let sign : Fin 3 → ℝ := ![1, 1, -1]
    let M : Set E3 := (S ∩ {y | H y ∈ Icc z v}) ∪
      (V 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z))
    let Couter := V 1 '' (sphere (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon))
    let W : Fin 3 → Set E3 := fun i => {y | |H y - cut i| < 8 * epsilon}
    let O : Fin 3 → Set E3 := ![W 0 ∩ Couterᶜ, W 1, W 2]
    have hCouter : IsCompact Couter :=
      ((isCompact_sphere (0 : E2) 1).prod isCompact_Icc).image_of_continuousOn
        ((hV 1).continuousOn.mono (fun _ hp =>
          hVs 1 ⟨sphere_subset_closedBall hp.1, mem_univ _⟩))
    have hW (i : Fin 3) : IsOpen (W i) :=
      isOpen_lt ((H.continuous.sub continuous_const).abs) continuous_const
    have hO (i : Fin 3) : IsOpen (O i) := by
      fin_cases i
      · exact (hW 0).inter hCouter.isClosed.isOpen_compl
      · exact hW 1
      · exact hW 2
    have hOW (i : Fin 3) : O i ⊆ W i := by
      fin_cases i
      · exact inter_subset_left
      · exact subset_rfl
      · exact subset_rfl
    have hInnerU : Disjoint
        (U 0 '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon)))
        Couter := hInner.mono subset_union_left subset_rfl
    have hInnerV : Disjoint
        (V 0 '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon)))
        Couter := hInner.mono subset_union_right subset_rfl
    have hstack (A : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3)
        (hAs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (A i).source)
        (hAh : ∀ i x, x ∈ (A i).source → H (A i x) = x.2)
        (hAi : Disjoint
          (A 0 '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon)))
          Couter)
        (r : ℝ) (hr : r < 8 * epsilon) (i : Fin 3) :
        A i '' (closedBall (0 : E2) 1 ×ˢ Icc (cut i - r) (cut i + r)) ⊆ O i := by
      rintro _ ⟨x, hx, rfl⟩
      have hh : H (A i x) = x.2 := hAh i x (hAs i ⟨hx.1, mem_univ _⟩)
      have hw : A i x ∈ W i := by
        change |H (A i x) - cut i| < 8 * epsilon
        rw [hh]
        exact abs_lt.mpr ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
      fin_cases i
      · refine ⟨hw, ?_⟩
        intro hc
        apply Set.disjoint_left.mp hAi ?_ hc
        refine ⟨x, ⟨hx.1, ?_⟩, rfl⟩
        have hlo : z - r ≤ x.2 := hx.2.1
        have hhi : x.2 ≤ z + r := hx.2.2
        exact ⟨by linarith, by linarith⟩
      · exact hw
      · exact hw
    have hslice (T : OpenPartialHomeomorph (E2 × ℝ) E3) (A : Set E2) (w : ℝ) :
        T '' (A ×ˢ ({w} : Set ℝ)) = (fun x : E2 => T (x, w)) '' A := by
      ext y
      constructor
      · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
        have hsw : s = w := mem_singleton_iff.mp hs
        subst s
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(x, w), ⟨hx, rfl⟩, rfl⟩
    have hboundary (i : Fin 3) (w : ℝ)
        (hw : w ∈ Icc (cut i - 8 * epsilon) (cut i + 8 * epsilon)) :
        (fun x : E2 => U i (x, w)) '' sphere (0 : E2) 1 =
          (fun x : E2 => V i (x, w)) '' sphere (0 : E2) 1 := by
      simpa only [hslice] using hBoundary i w hw
    have hcircleO (i : Fin 3) :
        V i '' (sphere (0 : E2) 1 ×ˢ Icc (cut i - 6 * epsilon) (cut i + 6 * epsilon)) ⊆
          O i :=
      (image_mono (prod_mono sphere_subset_closedBall subset_rfl)).trans
        (hstack V hVs hVh hInnerV (6 * epsilon) (by linarith) i)
    choose k hk hkrange hkfix using fun i : Fin 3 =>
      exists_saddle_end_height_clamp (cut i - 6 * epsilon) (cut i + 6 * epsilon)
        epsilon (by linarith) hepsilon
    have hkI (i : Fin 3) (w : ℝ) :
        k i w ∈ Icc (cut i - 8 * epsilon) (cut i + 8 * epsilon) := by
      have hh := hkrange i w
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    choose B hB hPB later using fun i : Fin 3 =>
      exists_stackOriginalCapAlignment_in_height_band P (U i) (V i)
        (hU i) (hUi i) (hV i) (hVi i) u (hUh i) (hVh i) (hUs i) (hVs i)
        (Icc (cut i - 8 * epsilon) (cut i + 8 * epsilon)) isCompact_Icc
        (hboundary i) (k i) (hk i) (hkI i)
        (cut i - 8 * epsilon) (cut i - 6 * epsilon) (cut i - 4 * epsilon)
        (cut i + 4 * epsilon) (cut i + 6 * epsilon) (cut i + 8 * epsilon)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (hkfix i) (O i) (hO i) (hcircleO i)
    let bound := max (B 0) (max (B 1) (B 2))
    have hBbound (i : Fin 3) : B i ≤ bound := by
      fin_cases i
      · exact le_max_left _ _
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    have hPbound : P.heightBound ≤ bound := (hPB 0).trans (hBbound 0)
    refine ⟨bound, (hB 0).trans (hBbound 0), hPbound, ?_⟩
    intro lambda hlambda hsmall
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let CU : Fin 3 → Set E3 := fun i =>
      P.capMap (U i) (cut i) (sign i) 0 (lambda i) '' Qminus
    let CV : Fin 3 → Set E3 := fun i =>
      P.capMap (V i) (cut i) (sign i) 0 (lambda i) '' Qminus
    have hsign (i : Fin 3) : |sign i| = 1 := by fin_cases i <;> norm_num [sign]
    have hsmallB (i : Fin 3) : lambda i * B i < epsilon :=
      (mul_le_mul_of_nonneg_left (hBbound i) (hlambda i).le).trans_lt (hsmall i)
    have hsmallP (i : Fin 3) : lambda i * P.heightBound < epsilon :=
      (mul_le_mul_of_nonneg_left hPbound (hlambda i).le).trans_lt (hsmall i)
    choose Fi Ki hcap _hcapInv hKi hKO _hSupport _hSupportInv hfix hprotected using
      fun i : Fin 3 => later i (cut i) (sign i) (lambda i) epsilon (hsign i)
        (hlambda i) (hsmallB i) (by linarith) (by linarith)
        (O i) (O i) (hO i) (hO i)
        (hstack U hUs hUh hInnerU epsilon (by linarith) i)
        (hstack V hVs hVh hInnerV epsilon (by linarith) i)
    have hKiO (i : Fin 3) : Ki i ⊆ O i := by
      intro y hy
      rcases hKO i hy with (hh | hh) | hh
      · exact hh
      · exact hh.1
      · exact hh
    have hLheight (y : E3)
        (hy : y ∈ V 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z)) : H y ∈ Icc t z := by
      obtain ⟨x, hx, rfl⟩ := hy
      have hh : H (V 1 x) = x.2 :=
        hVh 1 x (hVs 1 ⟨sphere_subset_closedBall hx.1, mem_univ _⟩)
      simpa only [hh] using hx.2
    have hMheight (y : E3) (hy : y ∈ M) : t ≤ H y ∧ H y ≤ v := by
      rcases hy with hy | hy
      · exact ⟨by linarith [hy.2.1], hy.2.2⟩
      · have hh := hLheight y hy
        exact ⟨hh.1, by linarith [hh.2]⟩
    have hLnotO (y : E3)
        (hy : y ∈ V 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z)) : y ∉ O 0 := by
      obtain ⟨x, hx, rfl⟩ := hy
      intro hmem
      change V 1 x ∈ W 0 ∩ Couterᶜ at hmem
      have hw : |H (V 1 x) - z| < 8 * epsilon := hmem.1
      have hh : H (V 1 x) = x.2 :=
        hVh 1 x (hVs 1 ⟨sphere_subset_closedBall hx.1, mem_univ _⟩)
      rw [hh] at hw
      apply hmem.2
      exact ⟨x, ⟨hx.1, by
        exact ⟨by linarith [(abs_lt.mp hw).1], by linarith [(abs_lt.mp hw).2]⟩⟩, rfl⟩
    have hsliceBand (T : OpenPartialHomeomorph (E2 × ℝ) E3) (y : E3)
        (a b : ℝ) (hy : y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({H y} : Set ℝ)))
        (hh : H y ∈ Icc a b) : y ∈ T '' (sphere (0 : E2) 1 ×ˢ Icc a b) := by
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨x, ⟨hx.1, ?_⟩, hxy⟩
      rw [mem_singleton_iff.mp hx.2]
      exact hh
    have hLslice (y : E3)
        (hy : y ∈ V 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z)) :
        y ∈ V 1 '' (sphere (0 : E2) 1 ×ˢ ({H y} : Set ℝ)) := by
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨x, ⟨hx.1, ?_⟩, rfl⟩
      exact (hVh 1 x (hVs 1 ⟨sphere_subset_closedBall hx.1, mem_univ _⟩)).symm
    have hFiM (i : Fin 3) (y : E3) (hy : y ∈ M) : Fi i y = y ∧ (Fi i).symm y = y := by
      fin_cases i
      · rcases hy with hR | hL
        · apply hprotected 0 y ?_ (Or.inl ?_)
          · by_cases hout : y ∈ O 0
            · by_cases hband : H y ∈ Ioo (z - 6 * epsilon) (z + 6 * epsilon)
              · have hw : H y ∈ Icc (t - 8 * epsilon) (z + 8 * epsilon) :=
                  ⟨by linarith [hband.1], by linarith [hband.2]⟩
                have hc : y ∈ (V 0 '' (sphere (0 : E2) 1 ×ˢ ({H y} : Set ℝ))) ∪
                    (V 1 '' (sphere (0 : E2) 1 ×ˢ ({H y} : Set ℝ))) := by
                  rw [← hLower (H y) hw]
                  exact ⟨hR.1, rfl⟩
                rcases hc with hc | hc
                · exact Or.inr (Or.inr (hsliceBand (V 0) y _ _ hc
                    ⟨hband.1.le, hband.2.le⟩))
                · exact (hout.2 (hsliceBand (V 1) y _ _ hc
                    ⟨by linarith [hband.1], by linarith [hband.2]⟩)).elim
              · exact Or.inr (Or.inl hband)
            · exact Or.inl hout
          · change 0 ≤ 1 * (H y - z)
            linarith [hR.2.1]
        · have hout := hLnotO y hL
          exact hprotected 0 y (Or.inl hout) (Or.inr ⟨hout, hout⟩)
      · apply hprotected 1 y ?_ (Or.inl ?_)
        · by_cases hband : H y ∈ Ioo (t - 6 * epsilon) (t + 6 * epsilon)
          · rcases hy with hR | hL
            · exfalso
              linarith [hR.2.1, hband.2]
            · exact Or.inr (Or.inr (hsliceBand (V 1) y _ _ (hLslice y hL)
                ⟨hband.1.le, hband.2.le⟩))
          · exact Or.inr (Or.inl hband)
        · change 0 ≤ 1 * (H y - t)
          linarith [(hMheight y hy).1]
      · apply hprotected 2 y ?_ (Or.inl ?_)
        · by_cases hband : H y ∈ Ioo (v - 6 * epsilon) (v + 6 * epsilon)
          · rcases hy with hR | hL
            · have hw : H y ∈ Icc (v - 8 * epsilon) (v + 8 * epsilon) :=
                ⟨by linarith [hband.1], by linarith [hband.2]⟩
              have hc : y ∈ V 2 '' (sphere (0 : E2) 1 ×ˢ ({H y} : Set ℝ)) := by
                rw [← hUpper (H y) hw]
                exact ⟨hR.1, rfl⟩
              exact Or.inr (Or.inr (hsliceBand (V 2) y _ _ hc
                ⟨hband.1.le, hband.2.le⟩))
            · exfalso
              linarith [(hLheight y hL).2, hband.1]
          · exact Or.inr (Or.inl hband)
        · change 0 ≤ -1 * (H y - v)
          linarith [(hMheight y hy).2]
    have hcapHeight (T : OpenPartialHomeomorph (E2 × ℝ) E3)
        (hTs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
        (hTh : ∀ x ∈ T.source, H (T x) = x.2)
        (i : Fin 3) (y : E3)
        (hy : y ∈ P.capMap T (cut i) (sign i) 0 (lambda i) '' Qminus) :
        |H y - cut i| < epsilon := by
      obtain ⟨q, _hq, rfl⟩ := hy
      have hmodel : (P.model q).1 ∈ closedBall (0 : E2) 1 :=
        mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q)
      rw [SurgeryCapProfile.capMap_apply,
        hTh ((P.model q).1, cut i + sign i * (0 + lambda i * (P.model q).2))
          (hTs ⟨hmodel, mem_univ _⟩)]
      simp only [zero_add, add_sub_cancel_left, abs_mul, hsign i, one_mul,
        abs_of_pos (hlambda i)]
      exact (mul_le_mul_of_nonneg_left (P.height_bound q) (hlambda i).le).trans_lt (hsmallP i)
    have hseparated (i j : Fin 3) (hij : i ≠ j) (w : ℝ)
        (hi : |w - cut i| < epsilon) (hj : |w - cut j| < 8 * epsilon) : False := by
      have hi0 := (abs_lt.mp hi).1
      have hi1 := (abs_lt.mp hi).2
      have hj0 := (abs_lt.mp hj).1
      have hj1 := (abs_lt.mp hj).2
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      all_goals norm_num [cut] at hi0 hi1 hj0 hj1
      all_goals linarith only [hepsilon, htz, hzc, hcv, hi0, hi1, hj0, hj1]
    have hcross (i j : Fin 3) (hij : i ≠ j) (y : E3) (hy : y ∈ CU j ∪ CV j) :
        Fi i y = y ∧ (Fi i).symm y = y := by
      apply hfix i y
      intro hyK
      have hh : |H y - cut j| < epsilon := by
        rcases hy with hy | hy
        · exact hcapHeight (U j) (hUs j) (hUh j) j y hy
        · exact hcapHeight (V j) (hVs j) (hVh j) j y hy
      exact hseparated j i hij.symm (H y) hh (hOW i (hKiO i hyK))
    have hotherU (i j : Fin 3) (hij : i ≠ j) : Fi i '' CU j = CU j :=
      EqOn.image_eq_self (fun y hy => (hcross i j hij y (Or.inl hy)).1)
    have hotherV (i j : Fin 3) (hij : i ≠ j) : Fi i '' CV j = CV j :=
      EqOn.image_eq_self (fun y hy => (hcross i j hij y (Or.inr hy)).1)
    have hcap' (i : Fin 3) : Fi i '' CU i = CV i := hcap i
    let F := ((Fi 0).trans (Fi 1)).trans (Fi 2)
    have hFcap (i : Fin 3) : F '' CU i = CV i := by
      fin_cases i
      · change F '' CU 0 = CV 0
        simp only [F, Diffeomorph.coe_trans, image_comp]
        rw [hcap' 0, hotherV 1 0 (by decide), hotherV 2 0 (by decide)]
      · change F '' CU 1 = CV 1
        simp only [F, Diffeomorph.coe_trans, image_comp]
        rw [hotherU 0 1 (by decide), hcap' 1, hotherV 2 1 (by decide)]
      · change F '' CU 2 = CV 2
        simp only [F, Diffeomorph.coe_trans, image_comp]
        rw [hotherU 0 2 (by decide), hotherU 1 2 (by decide), hcap' 2]
    have hFM (y : E3) (hy : y ∈ M) : F y = y ∧ F.symm y = y := by
      have h0 := hFiM 0 y hy
      have h1 := hFiM 1 y hy
      have h2 := hFiM 2 y hy
      change Fi 2 (Fi 1 (Fi 0 y)) = y ∧ (Fi 0).symm ((Fi 1).symm ((Fi 2).symm y)) = y
      rw [h0.1, h1.1, h2.1, h2.2, h1.2, h0.2]
      exact ⟨rfl, rfl⟩
    have hFimage : F '' (M ∪ ⋃ i : Fin 3, CU i) = M ∪ ⋃ i : Fin 3, CV i := by
      rw [image_union, EqOn.image_eq_self (fun y hy => (hFM y hy).1), image_iUnion]
      simp only [hFcap]
    let K := Ki 0 ∪ Ki 1 ∪ Ki 2
    have hK : IsCompact K := ((hKi 0).union (hKi 1)).union (hKi 2)
    have hKsub : K ⊆ ⋃ i : Fin 3, O i := by
      intro y hy
      rcases hy with (hy | hy) | hy
      · exact mem_iUnion.mpr ⟨0, hKiO 0 hy⟩
      · exact mem_iUnion.mpr ⟨1, hKiO 1 hy⟩
      · exact mem_iUnion.mpr ⟨2, hKiO 2 hy⟩
    have hFfix (y : E3) (hy : y ∉ K) : F y = y ∧ F.symm y = y := by
      have h0 := hfix 0 y (fun hh => hy (Or.inl (Or.inl hh)))
      have h1 := hfix 1 y (fun hh => hy (Or.inl (Or.inr hh)))
      have h2 := hfix 2 y (fun hh => hy (Or.inr hh))
      change Fi 2 (Fi 1 (Fi 0 y)) = y ∧ (Fi 0).symm ((Fi 1).symm ((Fi 2).symm y)) = y
      rw [h0.1, h1.1, h2.1, h2.2, h1.2, h0.2]
      exact ⟨rfl, rfl⟩
    refine ⟨F, K, ?_, hFimage, ?_, hFM, hK, hKsub, ?_, ?_, hFfix⟩
    · intro i
      refine ⟨hFcap i, ?_⟩
      change F.symm '' CV i = CU i
      rw [← hFcap i]
      exact F.symm_image_image (CU i)
    · change F.symm '' (M ∪ ⋃ i : Fin 3, CV i) = M ∪ ⋃ i : Fin 3, CU i
      rw [← hFimage]
      exact F.symm_image_image (M ∪ ⋃ i : Fin 3, CU i)
    · apply closure_minimal ?_ hK.isClosed
      intro y hy
      by_contra hyK
      exact hy (sub_eq_zero.mpr (hFfix y hyK).1)
    · apply closure_minimal ?_ hK.isClosed
      intro y hy
      by_contra hyK
      exact hy (sub_eq_zero.mpr (hFfix y hyK).2)
  classical
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let L := heightPlaneCoordinates u
  let d := min b (min (z - t) (v - z))
  let epsilon := d / 512
  let c := (z + v) / 2
  have hd : 0 < d := lt_min hb (lt_min (by linarith) (sub_pos.mpr hzv))
  have hdb : d ≤ b := min_le_left _ _
  have hdt : d ≤ z - t := (min_le_right _ _).trans (min_le_left _ _)
  have hdv : d ≤ v - z := (min_le_right _ _).trans (min_le_right _ _)
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have heb : epsilon < b := by dsimp [epsilon]; linarith
  have h8 : 8 * epsilon < 4 * b := by dsimp [epsilon]; linarith
  have htz' : t + 64 * epsilon < z := by dsimp [epsilon]; linarith
  have hzc : z + 64 * epsilon < c := by dsimp [epsilon, c]; linarith
  have hcv : c + 64 * epsilon < v := by dsimp [epsilon, c]; linarith
  have hslice (T : OpenPartialHomeomorph (E2 × ℝ) E3) (A : Set E2) (w : ℝ) :
      T '' (A ×ˢ ({w} : Set ℝ)) = (fun x : E2 => T (x, w)) '' A := by
    ext y
    constructor
    · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
      have hsw : s = w := mem_singleton_iff.mp hs
      subst s
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x, w), ⟨hx, rfl⟩, rfl⟩
  have hchart (T : OpenPartialHomeomorph (E2 × ℝ) E3)
      (hT : ContDiffOn ℝ ∞ T T.source) (hTi : ContDiffOn ℝ ∞ T.symm T.target)
      (hTh : ∀ x ∈ T.source, H (T x) = x.2)
      (hTs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source) (w : ℝ) :
      ∃ B : BallNeighborhoodChart E2 E2, ∀ x : E2,
        B.chart x = (L (T (x, w))).1 := by
    let A := T.trans L.toHomeomorph.toOpenPartialHomeomorph
    have hA : ContDiffOn ℝ ∞ A A.source :=
      L.contDiff.comp_contDiffOn (hT.mono (fun _ hx => hx.1))
    have hAi : ContDiffOn ℝ ∞ A.symm A.target :=
      hTi.comp L.symm.contDiff.contDiffOn (fun _ hx => hx.2)
    have hAh (x : E2 × ℝ) (hx : x ∈ A.source) : (A x).2 = x.2 :=
      (heightPlaneCoordinates_snd u (T x)).trans (hTh x hx.1)
    obtain ⟨B, hB, _, _, _⟩ := exists_saddle_end_fiber_chart A hA hAi hAh w
      (fun x hx => ⟨hTs ⟨hx, mem_univ _⟩, mem_univ _⟩)
    exact ⟨B, hB⟩
  have hdim : 1 < Module.rank ℝ E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E2]
  have hlift (A B : OpenPartialHomeomorph (E2 × ℝ) E3)
      (hAs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ A.source)
      (hBs : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ B.source)
      (hAh : ∀ x ∈ A.source, H (A x) = x.2)
      (hBh : ∀ x ∈ B.source, H (B x) = x.2) (w : ℝ)
      (hh : (fun x : E2 => (L (A (x, w))).1) '' closedBall 0 1 =
        (fun x : E2 => (L (B (x, w))).1) '' closedBall 0 1) :
      A '' (closedBall (0 : E2) 1 ×ˢ ({w} : Set ℝ)) ⊆
        B '' (closedBall (0 : E2) 1 ×ˢ ({w} : Set ℝ)) := by
    rw [hslice, hslice]
    rintro _ ⟨x, hx, rfl⟩
    have hximage : (L (A (x, w))).1 ∈
        (fun y : E2 => (L (B (y, w))).1) '' closedBall 0 1 := by
      rw [← hh]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hximage
    refine ⟨y, hy, L.injective (Prod.ext hxy ?_)⟩
    simp only [L, heightPlaneCoordinates_snd]
    exact (hBh (y, w) (hBs ⟨hy, mem_univ _⟩)).trans
      (hAh (x, w) (hAs ⟨hx, mem_univ _⟩)).symm
  have hsame (w : ℝ) (hw : w ∈ Icc (z - 8 * epsilon) (z + 8 * epsilon)) :
      U 0 '' (closedBall (0 : E2) 1 ×ˢ ({w} : Set ℝ)) =
        V 0 '' (closedBall (0 : E2) 1 ×ˢ ({w} : Set ℝ)) := by
    obtain ⟨BU, hBU⟩ := hchart (U 0) (hU 0) (hUi 0) (hUh 0) (hUs 0) w
    obtain ⟨BV, hBV⟩ := hchart (V 0) (hV 0) (hVi 0) (hVh 0) (hVs 0) w
    have hBUs (A : Set E2) : BU.chart '' A =
        (fun x : E2 => (L (U 0 (x, w))).1) '' A := image_congr (fun x _ => hBU x)
    have hBVs (A : Set E2) : BV.chart '' A =
        (fun x : E2 => (L (V 0 (x, w))).1) '' A := image_congr (fun x _ => hBV x)
    have hc : U 0 '' (sphere (0 : E2) 1 ×ˢ ({w} : Set ℝ)) =
        V 0 '' (sphere (0 : E2) 1 ×ˢ ({w} : Set ℝ)) :=
      hcircles 0 w ⟨by linarith [hw.1], by linarith [hw.2]⟩
    have hbound : BU.boundary = BV.boundary := by
      change BU.chart '' sphere 0 1 = BV.chart '' sphere 0 1
      rw [hBUs, hBVs]
      have hh := congrArg (fun A : Set E3 => (fun y => (L y).1) '' A) hc
      simpa only [hslice, image_image] using hh
    have hclosed := BU.closedRegion_eq_of_boundary_eq BV hdim hbound
    change BU.chart '' closedBall 0 1 = BV.chart '' closedBall 0 1 at hclosed
    rw [hBUs, hBVs] at hclosed
    exact Subset.antisymm
      (hlift (U 0) (V 0) (hUs 0) (hVs 0) (hUh 0) (hVh 0) w hclosed)
      (hlift (V 0) (U 0) (hVs 0) (hUs 0) (hVh 0) (hUh 0) w hclosed.symm)
  have hsmallWindow (w : ℝ)
      (hw : w ∈ Icc (z - 8 * epsilon) (z + 8 * epsilon)) :
      w ∈ Icc (t - 4 * b) (z + 4 * b) :=
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hclosedStack :
      U 0 '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon)) ⊆
        V 0 '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon)) := by
    rintro _ ⟨p, hp, rfl⟩
    have hm : U 0 p ∈ V 0 '' (closedBall (0 : E2) 1 ×ˢ ({p.2} : Set ℝ)) := by
      rw [← hsame p.2 hp.2]
      exact ⟨p, ⟨hp.1, rfl⟩, rfl⟩
    obtain ⟨q, hq, hqp⟩ := hm
    refine ⟨q, ⟨hq.1, ?_⟩, hqp⟩
    rw [mem_singleton_iff.mp hq.2]
    exact hp.2
  have hdis : Disjoint
      (V 0 '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon)))
      (V 1 '' (sphere (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon))) := by
    apply disjoint_left.mpr
    rintro y ⟨p, hp, hpy⟩ ⟨q, hq, hqy⟩
    have hi : V 0 p ∈ V 1 '' (ball (0 : E2) 1 ×ˢ ({p.2} : Set ℝ)) :=
      (hlower p.2 (hsmallWindow p.2 hp.2)).2.1 ⟨p, ⟨hp.1, rfl⟩, rfl⟩
    obtain ⟨r, hr, hrp⟩ := hi
    have hrq : r = q := (V 1).injOn
      (hVs 1 ⟨ball_subset_closedBall hr.1, mem_univ _⟩)
      (hVs 1 ⟨sphere_subset_closedBall hq.1, mem_univ _⟩)
      (hrp.trans (hpy.trans hqy.symm))
    have hn := mem_ball_zero_iff.mp hr.1
    rw [hrq] at hn
    have he := mem_sphere_zero_iff_norm.mp hq.1
    linarith
  have hInner : Disjoint
      ((U 0 '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon))) ∪
        (V 0 '' (closedBall (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon))))
      (V 1 '' (sphere (0 : E2) 1 ×ˢ Icc (z - 8 * epsilon) (z + 8 * epsilon))) :=
    hdis.mono (union_subset hclosedStack subset_rfl) subset_rfl
  have hBoundary (i : Fin 3) (w : ℝ)
      (hw : w ∈ Icc (((![z, t, v] : Fin 3 → ℝ) i) - 8 * epsilon)
        (((![z, t, v] : Fin 3 → ℝ) i) + 8 * epsilon)) :
      U i '' (sphere (0 : E2) 1 ×ˢ ({w} : Set ℝ)) =
        V i '' (sphere (0 : E2) 1 ×ˢ ({w} : Set ℝ)) := by
    apply hcircles i w
    fin_cases i <;> norm_num at hw ⊢ <;> constructor <;> linarith [hw.1, hw.2]
  obtain ⟨bound, hbound, hPbound, later⟩ := hCore P u U V hU hUi hV hVi hUs hVs hUh hVh
    S t z c v epsilon hepsilon htz' hzc hcv hBoundary
    (fun w hw => (hlower w ⟨by linarith [hw.1], by linarith [hw.2]⟩).1)
    (fun w hw => (hupper w ⟨by linarith [hw.1], by linarith [hw.2]⟩).symm) hInner
  refine ⟨epsilon, bound, hepsilon, heb, hbound, hPbound, ?_⟩
  intro lambda hlambda hsmall
  obtain ⟨F, K, _hcap, hforward, hinverse, hfix, hK, _hKO, hs, hsi, _hout⟩ :=
    later lambda hlambda hsmall
  exact ⟨F, K, hforward, hinverse, hfix, hK, hs, hsi⟩

end PoincareConjecture.M25.Topology3D
