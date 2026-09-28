import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Nested.RibbonGerms

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)

private theorem region_dichotomy {X : Type*} [TopologicalSpace X] {G C : Set X}
    (hG : IsPreconnected G) (hC : IsClosed C) (havoid : Disjoint G (frontier C)) :
    G ⊆ interior C ∨ G ⊆ Cᶜ := by
  apply hG.subset_or_subset isOpen_interior hC.isOpen_compl
    (disjoint_left.mpr fun _ hx hy => hy (interior_subset hx))
  intro x hx
  by_cases hin : x ∈ interior C
  · exact Or.inl hin
  · right
    intro hxC
    exact disjoint_left.mp havoid hx (by rw [hC.frontier_eq]; exact ⟨hxC, hin⟩)

theorem connector_image_subset_annulus_of_nested_closed
    {X : Type*} [TopologicalSpace X] {C₀ C₁ : Set X}
    (hC₀ : IsClosed C₀) (hC₁ : IsClosed C₁) (hnest : C₁ ⊆ interior C₀)
    {β : Real → X} (hβ : ContinuousOn β (Icc 0 1))
    (hβ₀ : β 0 ∈ frontier C₀) (hβ₁ : β 1 ∈ C₁)
    (havoid : Disjoint (β '' Ioo 0 1) (frontier C₀ ∪ frontier C₁)) :
    β '' Ioo 0 1 ⊆ interior C₀ \ C₁ := by
  let G := β '' Ioo 0 1
  have hG : IsPreconnected G := isPreconnected_Ioo.image β (hβ.mono Ioo_subset_Icc_self)
  have hend {t : Real} (ht : t ∈ Icc 0 1) : β t ∈ closure G := by
    have hc : closure (Ioo (0 : Real) 1) = Icc 0 1 := closure_Ioo zero_ne_one
    exact (hc.symm ▸ hβ).image_closure (mem_image_of_mem β (hc.symm ▸ ht))
  have hin : G ⊆ interior C₀ := by
    rcases region_dichotomy hG hC₀ (havoid.mono_right subset_union_left) with h | h
    · exact h
    · have hh := closure_mono h (hend (show (1 : Real) ∈ Icc 0 1 by simp))
      rw [closure_compl] at hh
      exact (hh (hnest hβ₁)).elim
  have hout : G ⊆ C₁ᶜ := by
    rcases region_dichotomy hG hC₁ (havoid.mono_right subset_union_right) with h | h
    · have hh := closure_minimal (h.trans interior_subset) hC₁
        (hend (show (0 : Real) ∈ Icc 0 1 by simp))
      exact (hβ₀.2 (hnest hh)).elim
    · exact h
  exact fun x hx => ⟨hin hx, hout hx⟩

theorem connector_image_subset_annulus_of_nested_disks
    (A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hnest : B '' closedBall 0 1 ⊆ A '' ball 0 1)
    {β : Real → E2} (hβ : ContinuousOn β (Icc 0 1))
    (hβ₀ : β 0 ∈ A '' sphere (0 : E2) 1)
    (hβ₁ : β 1 ∈ B '' closedBall (0 : E2) 1)
    (havoid : Disjoint (β '' Ioo 0 1)
      ((A '' sphere (0 : E2) 1) ∪ (B '' sphere (0 : E2) 1))) :
    β '' Ioo 0 1 ⊆ (A '' ball (0 : E2) 1) \ (B '' closedBall (0 : E2) 1) := by
  have hi : interior (A '' closedBall (0 : E2) 1) = A '' ball (0 : E2) 1 := by
    have h := A.toHomeomorph.image_interior (closedBall (0 : E2) 1)
    rw [interior_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at h
    exact h.symm
  have hf (D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
      frontier (D '' closedBall (0 : E2) 1) = D '' sphere (0 : E2) 1 := by
    have h := D.toHomeomorph.image_frontier (closedBall (0 : E2) 1)
    rw [frontier_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at h
    exact h.symm
  rw [← hi]
  exact connector_image_subset_annulus_of_nested_closed
    ((isCompact_closedBall _ _).image A.continuous).isClosed
    ((isCompact_closedBall _ _).image B.continuous).isClosed
    (hi.symm ▸ hnest) hβ ((hf A).symm ▸ hβ₀) hβ₁
    (by simpa only [hf A, hf B] using havoid)

theorem compact_ribbon_inter_inner_disk
    (A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hnest : B '' closedBall 0 1 ⊆ A '' ball 0 1)
    (R : E2 → E2) (hR : Continuous R) (a : Real)
    (hstart : ∀ s ∈ Icc (-a) a,
      R (WithLp.toLp 2 ![s, 0]) ∈ A '' sphere (0 : E2) 1)
    (hfinish : ∀ s ∈ Icc (-a) a,
      R (WithLp.toLp 2 ![s, 1]) ∈ B '' closedBall (0 : E2) 1)
    (havoid : ∀ s ∈ Icc (-a) a,
      Disjoint ((fun t : Real => R (WithLp.toLp 2 ![s, t])) '' Ioo 0 1)
        ((A '' sphere (0 : E2) 1) ∪ (B '' sphere (0 : E2) 1))) :
    let P := (fun z : Real × Real => R (WithLp.toLp 2 ![z.1, z.2])) ''
      (Icc (-a) a ×ˢ Icc 0 1)
    IsCompact P ∧ P ⊆ A '' closedBall (0 : E2) 1 ∧
      (B '' closedBall (0 : E2) 1) ∩ P =
        (fun s : Real => R (WithLp.toLp 2 ![s, 1])) '' Icc (-a) a := by
  have hregion (s : Real) (hs : s ∈ Icc (-a) a) :=
    connector_image_subset_annulus_of_nested_disks A B hnest
      (hR.comp (by fun_prop : Continuous (fun t : Real =>
        (WithLp.toLp 2 ![s, t] : E2)))).continuousOn
      (hstart s hs) (hfinish s hs) (havoid s hs)
  refine ⟨(isCompact_Icc.prod isCompact_Icc).image (hR.comp (by fun_prop)), ?_, ?_⟩
  · rintro _ ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
    by_cases ht0 : t = 0
    · subst t
      exact image_mono sphere_subset_closedBall (hstart s hs)
    · by_cases ht1 : t = 1
      · subst t
        exact image_mono ball_subset_closedBall (hnest (hfinish s hs))
      · exact image_mono ball_subset_closedBall
          (hregion s hs (mem_image_of_mem _
            ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩)).1
  · apply Subset.antisymm
    · rintro x ⟨hxB, ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩⟩
      by_cases ht1 : t = 1
      · subst t
        exact ⟨s, hs, rfl⟩
      · by_cases ht0 : t = 0
        · subst t
          obtain ⟨x, hx, hxe⟩ := hstart s hs
          obtain ⟨y, hy, hye⟩ := hnest hxB
          have hxy : x = y := A.injective (hxe.trans hye.symm)
          have hbad : (1 : Real) < 1 := by
            calc
              1 = ‖x‖ := (mem_sphere_zero_iff_norm.mp hx).symm
              _ = ‖y‖ := congrArg norm hxy
              _ < 1 := mem_ball_zero_iff.mp hy
          exact (lt_irrefl _ hbad).elim
        · exact ((hregion s hs (mem_image_of_mem _
            ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩)).2 hxB).elim
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨hfinish s hs, ⟨(s, 1), ⟨hs, by simp⟩, rfl⟩⟩

private def ribbonEdgeCoordinates (s : Real) (i : Fin 2) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := WithLp.toLp 2 ![s + x 0, if i = 0 then x 1 else 1 - x 1]
  invFun x := WithLp.toLp 2 ![x 0 - s, if i = 0 then x 1 else 1 - x 1]
  left_inv x := by ext j; fin_cases j <;> split_ifs <;> simp
  right_inv x := by ext j; fin_cases j <;> split_ifs <;> simp
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro j
    fin_cases j
    · exact contDiff_const.add (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · split_ifs
      · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
      · exact contDiff_const.sub (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro j
    fin_cases j
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.sub contDiff_const
    · split_ifs
      · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
      · exact contDiff_const.sub (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff

theorem exists_filled_coincidence_of_shared_nested_ribbon
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : A 1 '' closedBall 0 1 ⊆ A 0 '' ball 0 1)
    (hB : B 1 '' closedBall 0 1 ⊆ B 0 '' ball 0 1)
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real}
    (hedge : ∀ i : Fin 2, ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, (i : Real)]) ∈
        (A i '' sphere (0 : E2) 1) ∩ (B i '' sphere (0 : E2) 1))
    (havoid : ∀ s ∈ Ioo (-w) w,
      Disjoint ((fun t : Real => R (WithLp.toLp 2 ![s, t])) '' Ioo 0 1)
        (((A 0 '' sphere (0 : E2) 1) ∪ (A 1 '' sphere (0 : E2) 1)) ∪
          ((B 0 '' sphere (0 : E2) 1) ∪ (B 1 '' sphere (0 : E2) 1)))) :
    ∀ i : Fin 2, ∃ V : Set E2, IsOpen V ∧
      (fun s : Real => R (WithLp.toLp 2 ![s, (i : Real)])) '' Ioo (-w) w ⊆ V ∧
      V ∩ (A i '' closedBall 0 1) = V ∩ (B i '' closedBall 0 1) ∧
      V ∩ (A i '' ball 0 1) = V ∩ (B i '' ball 0 1) := by
  classical
  have hlocal (s : Ioo (-w) w) (i : Fin 2) : ∃ V : Set E2, IsOpen V ∧
      R (WithLp.toLp 2 ![(s : Real), (i : Real)]) ∈ V ∧
      V ∩ (A i '' closedBall 0 1) = V ∩ (B i '' closedBall 0 1) ∧
      V ∩ (A i '' ball 0 1) = V ∩ (B i '' ball 0 1) := by
    let β : Real → E2 := fun t => R (WithLp.toLp 2 ![(s : Real), t])
    have hβ : Continuous β := R.continuous.comp (by fun_prop)
    have hAin := connector_image_subset_annulus_of_nested_disks (A 0) (A 1) hA
      hβ.continuousOn (by simpa [β] using (hedge 0 s s.property).1)
      (by simpa [β] using image_mono sphere_subset_closedBall (hedge 1 s s.property).1)
      ((havoid s s.property).mono_right subset_union_left)
    have hBin := connector_image_subset_annulus_of_nested_disks (B 0) (B 1) hB
      hβ.continuousOn (by simpa [β] using (hedge 0 s s.property).2)
      (by simpa [β] using image_mono sphere_subset_closedBall (hedge 1 s s.property).2)
      ((havoid s s.property).mono_right subset_union_right)
    let ε := min ((s : Real) + w) (w - s)
    have hε : 0 < ε := lt_min (by linarith [s.property.1]) (by linarith [s.property.2])
    have hshift {u : Real} (hu : u ∈ Ioo (-ε) ε) :
        (s : Real) + u ∈ Ioo (-w) w := by
      have hl := min_le_left ((s : Real) + w) (w - s)
      have hr := min_le_right ((s : Real) + w) (w - s)
      change -ε < u ∧ u < ε at hu
      constructor <;> dsimp [ε] at hu <;> linarith
    let T (j : Fin 2) := (ribbonEdgeCoordinates s j).trans R
    have hTedge (j : Fin 2) (u : Real) (hu : u ∈ Ioo (-ε) ε) :
        T j (WithLp.toLp 2 ![u, 0]) ∈
          (A j '' sphere (0 : E2) 1) ∩ (B j '' sphere (0 : E2) 1) := by
      fin_cases j
      · change R (WithLp.toLp 2 ![(s : Real) + u, 0]) ∈ _
        simpa using hedge 0 _ (hshift hu)
      · change R (WithLp.toLp 2 ![(s : Real) + u, 1 - 0]) ∈ _
        simpa using hedge 1 _ (hshift hu)
    have hTann (j : Fin 2) : ∀ᶠ t in 𝓝[>] (0 : Real),
        T j (WithLp.toLp 2 ![0, t]) ∈
          ((A 0 '' ball (0 : E2) 1) \ (A 1 '' closedBall (0 : E2) 1)) ∩
          ((B 0 '' ball (0 : E2) 1) \ (B 1 '' closedBall (0 : E2) 1)) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : Real) < 1 by norm_num)] with t ht
      fin_cases j
      · change R (WithLp.toLp 2 ![(s : Real) + 0, t]) ∈ _
        simpa only [add_zero, β, mem_inter_iff] using
          And.intro (hAin (mem_image_of_mem β ht)) (hBin (mem_image_of_mem β ht))
      · have ht' : 1 - t ∈ Ioo (0 : Real) 1 := by constructor <;> linarith [ht.1, ht.2]
        change R (WithLp.toLp 2 ![(s : Real) + 0, 1 - t]) ∈ _
        simpa only [add_zero, β, mem_inter_iff] using
          And.intro (hAin (mem_image_of_mem β ht')) (hBin (mem_image_of_mem β ht'))
    obtain ⟨V, hV, hpV, hc, ho⟩ := exists_common_filled_sides_of_annular_ribbon A B T hε
      (fun j u hu => (hTedge j u hu).1) (fun j u hu => (hTedge j u hu).2) hTann i
    have hTzero : T i 0 = R (WithLp.toLp 2 ![(s : Real), (i : Real)]) := by
      fin_cases i <;> change R (WithLp.toLp 2 ![(s : Real) + (0 : E2) 0, _]) = _
      all_goals congr 1; ext j; fin_cases j <;> simp
    exact ⟨V, hV, hTzero ▸ hpV, hc, ho⟩
  intro i
  choose V hV hpV hc ho using fun s => hlocal s i
  refine ⟨⋃ s, V s, isOpen_iUnion hV, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, hpV ⟨s, hs⟩⟩
  · ext x
    simp only [iUnion_inter]
    simp only [hc]
  · ext x
    simp only [iUnion_inter]
    simp only [ho]

end Poincare.Manifold.Schoenflies.PlaneArcs.Nested
