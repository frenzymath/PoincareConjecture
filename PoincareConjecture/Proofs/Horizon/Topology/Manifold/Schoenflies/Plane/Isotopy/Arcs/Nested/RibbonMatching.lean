import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Nested.RibbonRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Nested.RibbonEdgeIsotopy
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Nested.RibbonInterior

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)

private theorem image_eq_of_fixed_complement
    (F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (S : Set E2)
    (hfix : ∀ x ∉ S, F x = x) : F '' S = S := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    by_contra hn
    have he : x = F x := F.injective (hfix (F x) hn).symm
    exact hn (he ▸ hx)
  · intro x hx
    refine ⟨F.symm x, ?_, F.apply_symm_apply x⟩
    by_contra hn
    have he : F.symm x = x := (hfix (F.symm x) hn).symm.trans (F.apply_symm_apply x)
    exact hn (he.symm ▸ hx)

theorem exists_supported_nested_disk_pair_isotopy_of_shared_ribbon
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : A 1 '' closedBall 0 1 ⊆ A 0 '' ball 0 1)
    (hB : B 1 '' closedBall 0 1 ⊆ B 0 '' ball 0 1)
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {w : Real} (hw : 1 < w)
    (hedge : ∀ i : Fin 2, ∀ s ∈ Ioo (-w) w,
      R (WithLp.toLp 2 ![s, (i : Real)]) ∈
        (A i '' sphere (0 : E2) 1) ∩ (B i '' sphere (0 : E2) 1))
    (havoid : ∀ s ∈ Ioo (-w) w,
      Disjoint ((fun t : Real => R (WithLp.toLp 2 ![s, t])) '' Ioo 0 1)
        (((A 0 '' sphere (0 : E2) 1) ∪ (A 1 '' sphere (0 : E2) 1)) ∪
          ((B 0 '' sphere (0 : E2) 1) ∪ (B 1 '' sphere (0 : E2) 1)))) :
    let P := (fun z : Real × Real => R (WithLp.toLp 2 ![z.1, z.2])) ''
      (Icc (-1) 1 ×ˢ Icc 0 1)
    ∃ K : Set E2, IsCompact K ∧ Disjoint K P ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Φ t x = x) ∧
        (∀ i, Φ 1 '' (A i '' closedBall 0 1) = B i '' closedBall 0 1) ∧
        ∃ U : Set E2, IsOpen U ∧ P ⊆ U ∧ ∀ t, EqOn (Φ t) id U := by
  classical
  let b := (1 + w) / 2
  have hb : 1 < b := by dsimp [b]; linarith
  have hbw : b < w := by dsimp [b]; linarith
  have hsub : Icc (-b) b ⊆ Ioo (-w) w :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let P (a : Real) : Set E2 :=
    (fun z : Real × Real => R (WithLp.toLp 2 ![z.1, z.2])) ''
      (Icc (-a) a ×ˢ Icc 0 1)
  have hPP : P 1 ⊆ P b := image_mono
    (Set.prod_mono (Icc_subset_Icc (by linarith) hb.le) Subset.rfl)
  have hregionA (s : Real) (hs : s ∈ Ioo (-w) w) :=
    connector_image_subset_annulus_of_nested_disks (A 0) (A 1) hA
      (R.continuous.comp (by fun_prop : Continuous (fun t : Real =>
        (WithLp.toLp 2 ![s, t] : E2)))).continuousOn
      (by simpa using (hedge 0 s hs).1)
      (by simpa using image_mono sphere_subset_closedBall (hedge 1 s hs).1)
      ((havoid s hs).mono_right subset_union_left)
  have hregionB (s : Real) (hs : s ∈ Ioo (-w) w) :=
    connector_image_subset_annulus_of_nested_disks (B 0) (B 1) hB
      (R.continuous.comp (by fun_prop : Continuous (fun t : Real =>
        (WithLp.toLp 2 ![s, t] : E2)))).continuousOn
      (by simpa using (hedge 0 s hs).2)
      (by simpa using image_mono sphere_subset_closedBall (hedge 1 s hs).2)
      ((havoid s hs).mono_right subset_union_right)
  obtain ⟨V₀, hV₀, hedgeV₀, hside₀, _⟩ :=
    exists_filled_coincidence_of_shared_nested_ribbon A B hA hB R hedge havoid 0
  obtain ⟨V₁, hV₁, hedgeV₁, hside₁, _⟩ :=
    exists_filled_coincidence_of_shared_nested_ribbon A B hA hB R hedge havoid 1
  obtain ⟨L₀, hL₀, _, hL₀edge, E, hE0, hEs, hEi, hEfix, hEmatch⟩ :=
    exists_supported_disk_isotopy_of_shared_ribbon_edge (A 0) (B 0) R 0
      (zero_lt_one.trans hb) hbw (by simpa using hedge 0)
      V₀ hV₀ (by simpa using hedgeV₀) hside₀ univ isOpen_univ
      (subset_univ _) (subset_univ _)
  let O := (A 0 '' ball (0 : E2) 1) ∩ (B 0 '' ball (0 : E2) 1)
  have hO : IsOpen O := ((A 0).toHomeomorph.isOpenMap _ isOpen_ball).inter
    ((B 0).toHomeomorph.isOpenMap _ isOpen_ball)
  have htrace : ∀ s ∈ Ioo (-w) w, ∀ t ∈ Ioc (0 : Real) 1,
      R (WithLp.toLp 2 ![s, t]) ∈ O := by
    intro s hs t ht
    by_cases ht1 : t = 1
    · subst t
      exact ⟨hA (by simpa using image_mono sphere_subset_closedBall (hedge 1 s hs).1),
        hB (by simpa using image_mono sphere_subset_closedBall (hedge 1 s hs).2)⟩
    · exact ⟨(hregionA s hs (mem_image_of_mem _ ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩)).1,
        (hregionB s hs (mem_image_of_mem _ ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩)).1⟩
  obtain ⟨K₀, hK₀, hK₀P, Φ₀, hΦ₀zero, hΦ₀s, hΦ₀i, hΦ₀fix, hΦ₀match⟩ :=
    exists_supported_isotopy_fixing_ribbon R (zero_lt_one.trans hb) hbw
      hO
      (fun x hx => image_mono ball_subset_closedBall hx.1)
      (fun x hx => image_mono ball_subset_closedBall hx.2)
      htrace hL₀ hL₀edge E hE0 hEs hEi hEfix hEmatch
  let Q := Φ₀ 1
  let A' := (A 1).trans Q
  have hQfix (x : E2) (hx : x ∉ K₀) : Q x = x := hΦ₀fix 1 x hx
  have hQP (x : E2) (hx : x ∈ P b) : Q x = x :=
    hQfix x (fun hk => disjoint_left.mp hK₀P hk hx)
  have hedgeP (s : Real) (hs : s ∈ Icc (-b) b) :
      R (WithLp.toLp 2 ![s, 1]) ∈ P b :=
    ⟨(s, 1), ⟨hs, by simp⟩, rfl⟩
  have hnewedge (s : Real) (hs : s ∈ Ioo (-b) b) :
      R (WithLp.toLp 2 ![s, 1]) ∈
        (A' '' sphere (0 : E2) 1) ∩ (B 1 '' sphere (0 : E2) 1) := by
    have h := hedge 1 s (hsub (Ioo_subset_Icc_self hs))
    refine ⟨?_, by simpa using h.2⟩
    obtain ⟨x, hx, he⟩ := h.1
    refine ⟨x, hx, ?_⟩
    change Q (A 1 x) = _
    simpa [he] using hQP _ (hedgeP s (Ioo_subset_Icc_self hs))
  have hnewV : (fun s : Real => R (WithLp.toLp 2 ![s, 1])) '' Ioo (-b) b ⊆
      V₁ ∩ K₀ᶜ := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨by simpa using hedgeV₁ (mem_image_of_mem _ (hsub (Ioo_subset_Icc_self hs))),
      fun hk => disjoint_left.mp hK₀P hk (hedgeP s (Ioo_subset_Icc_self hs))⟩
  have hnewside : (V₁ ∩ K₀ᶜ) ∩ (A' '' closedBall 0 1) =
      (V₁ ∩ K₀ᶜ) ∩ (B 1 '' closedBall 0 1) := by
    ext x
    constructor
    · rintro ⟨hx, y, hy, he⟩
      have hey : A 1 y = x := Q.injective (he.trans (hQfix x hx.2).symm)
      exact ⟨hx, (show x ∈ V₁ ∩ (B 1 '' closedBall 0 1) from
        hside₁ ▸ ⟨hx.1, y, hy, hey⟩).2⟩
    · rintro ⟨hx, hxb⟩
      obtain ⟨y, hy, he⟩ := (show x ∈ V₁ ∩ (A 1 '' closedBall 0 1) from
        hside₁.symm ▸ ⟨hx.1, hxb⟩).2
      refine ⟨hx, y, hy, ?_⟩
      change Q (A 1 y) = x
      rw [he, hQfix x hx.2]
  have hQopen : Q '' (A 0 '' ball 0 1) = B 0 '' ball 0 1 := by
    have hi (D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
        interior (D '' closedBall 0 1) = D '' ball 0 1 := by
      have h := D.toHomeomorph.image_interior (closedBall (0 : E2) 1)
      rw [interior_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at h
      exact h.symm
    rw [← hi, ← hi, ← hΦ₀match]
    exact Q.toHomeomorph.image_interior _
  have hnewnest : A' '' closedBall 0 1 ⊆ B 0 '' ball 0 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hQopen ▸ mem_image_of_mem Q (hA (mem_image_of_mem _ hx))
  have hcompactP : IsCompact (P 1) :=
    (isCompact_Icc.prod isCompact_Icc).image (R.continuous.comp (by fun_prop))
  have hAinter := (compact_ribbon_inter_inner_disk (A 0) (A 1) hA R R.continuous 1
    (fun s hs => by simpa using (hedge 0 s (hsub (Icc_subset_Icc (by linarith) hb.le hs))).1)
    (fun s hs => by
      simpa using image_mono sphere_subset_closedBall
        (hedge 1 s (hsub (Icc_subset_Icc (by linarith) hb.le hs))).1)
    (fun s hs => (havoid s (hsub (Icc_subset_Icc (by linarith) hb.le hs))).mono_right
      subset_union_left)).2.2
  have hBinter := (compact_ribbon_inter_inner_disk (B 0) (B 1) hB R R.continuous 1
    (fun s hs => by simpa using (hedge 0 s (hsub (Icc_subset_Icc (by linarith) hb.le hs))).2)
    (fun s hs => by
      simpa using image_mono sphere_subset_closedBall
        (hedge 1 s (hsub (Icc_subset_Icc (by linarith) hb.le hs))).2)
    (fun s hs => (havoid s (hsub (Icc_subset_Icc (by linarith) hb.le hs))).mono_right
      subset_union_right)).2.2
  let O₁ := (B 0 '' ball (0 : E2) 1) ∩ (P 1)ᶜ
  have hO₁ : IsOpen O₁ := ((B 0).toHomeomorph.isOpenMap _ isOpen_ball).inter
    hcompactP.isClosed.isOpen_compl
  obtain ⟨K₁, hK₁, hK₁O, _, Φ₁, hΦ₁zero, hΦ₁s, hΦ₁i, hΦ₁fix, hΦ₁match⟩ :=
    exists_supported_disk_isotopy_of_shared_ribbon_edge A' (B 1) R 1
      zero_lt_one hb hnewedge (V₁ ∩ K₀ᶜ) (hV₁.inter hK₀.isClosed.isOpen_compl)
      hnewV hnewside O₁ hO₁
      (by
        intro x hx
        refine ⟨hnewnest hx.1, ?_⟩
        intro hxP
        obtain ⟨y, hy, he⟩ := hx.1
        have he' : A 1 y = x := Q.injective (he.trans (hQP x (hPP hxP)).symm)
        exact hx.2 (hAinter ▸ (show x ∈ (A 1 '' closedBall 0 1) ∩ P 1 from
          ⟨⟨y, hy, he'⟩, hxP⟩)))
      (by
        intro x hx
        exact ⟨hB hx.1, fun hxP => hx.2 (hBinter ▸ ⟨hx.1, hxP⟩)⟩)
  let Φ (t : Real) := (Φ₀ t).trans (Φ₁ t)
  have hKP : Disjoint (K₀ ∪ K₁) (P 1) := disjoint_union_left.mpr
    ⟨hK₀P.mono_right hPP, disjoint_left.mpr (fun _ hk hp => (hK₁O hk).2 hp)⟩
  have hfix (t : Real) (x : E2) (hx : x ∉ K₀ ∪ K₁) : Φ t x = x := by
    change Φ₁ t (Φ₀ t x) = x
    rw [hΦ₀fix t x (fun h => hx (Or.inl h)), hΦ₁fix t x (fun h => hx (Or.inr h))]
  refine ⟨K₀ ∪ K₁, hK₀.union hK₁, hKP, Φ, ?_, ?_, ?_, hfix, ?_,
    (K₀ ∪ K₁)ᶜ, (hK₀.union hK₁).isClosed.isOpen_compl,
    (fun _ hp hk => disjoint_left.mp hKP hk hp), fun t x hx => hfix t x hx⟩
  · intro x
    change Φ₁ 0 (Φ₀ 0 x) = x
    rw [hΦ₀zero, hΦ₁zero]
  · exact hΦ₁s.comp (contDiff_fst.prodMk hΦ₀s)
  · exact hΦ₀i.comp (contDiff_fst.prodMk hΦ₁i)
  · intro i
    change (Φ₁ 1 ∘ Φ₀ 1) '' (A i '' closedBall 0 1) = _
    rw [image_comp]
    fin_cases i
    · change Φ₁ 1 '' (Φ₀ 1 '' (A 0 '' closedBall 0 1)) = B 0 '' closedBall 0 1
      rw [hΦ₀match]
      apply image_eq_of_fixed_complement
      intro x hx
      exact hΦ₁fix 1 x (fun hk => hx (image_mono ball_subset_closedBall (hK₁O hk).1))
    · change Φ₁ 1 '' (Φ₀ 1 '' (A 1 '' closedBall 0 1)) = B 1 '' closedBall 0 1
      simpa only [A', Q, Diffeomorph.coe_trans, image_comp] using hΦ₁match

end Poincare.Manifold.Schoenflies.PlaneArcs.Nested
