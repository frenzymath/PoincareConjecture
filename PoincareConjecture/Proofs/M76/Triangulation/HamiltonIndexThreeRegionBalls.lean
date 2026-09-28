import PoincareConjecture.Proofs.M76.Triangulation.HamiltonHandleThree
import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegionCertificates
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex












set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in





theorem hasAlexanderRegionBalls_identifies_open_region {S C V : Set E}
    (hregions : HasAlexanderRegionBalls S C)
    (hV : IsOpen V) (hVc : IsConnected V) (hVf : frontier V = S)
    (hVC : V ⊆ interior C) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closure V) S := by
  obtain ⟨U, hU, hUc, hUf, hUC, hUB, hUE⟩ := hregions
  have hmeet : (U ∩ V).Nonempty := by
    by_contra hmeet
    let Z := frontier (C ×ˢ Icc (-1 : ℝ) 1)
    let Q : Set Z := (Subtype.val : Z → E × ℝ) ⁻¹'
      ((Z \ U ×ˢ {1}) \ S ×ˢ {1})
    let W : Set Z := (Subtype.val : Z → E × ℝ) ⁻¹' (V ×ˢ {1})
    have hQ : IsPreconnected Q := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      have hsubset : ((Z \ U ×ˢ {(1 : ℝ)}) \ S ×ˢ {1}) ⊆ Z :=
        sdiff_subset.trans sdiff_subset
      rw [image_preimage_eq_of_subset (by simpa using hsubset)]
      exact hUE.isConnected_sdiff.isPreconnected
    have hW : IsOpen W := isOpen_preimage_top_face hV hVC
    have hWf : frontier W =
        (Subtype.val : Z → E × ℝ) ⁻¹' (S ×ˢ {1}) := by
      rw [frontier_preimage_top_face hV hVC, hVf]
    have hdis : Disjoint (frontier W) Q := by
      rw [hWf]
      exact Set.disjoint_left.mpr fun _ hx hy => hy.2 hx
    obtain ⟨x, hx⟩ := hVc.nonempty
    have hxC : x ∈ C := interior_subset (hVC hx)
    have hxtop : (x, (1 : ℝ)) ∈ Z :=
      prod_singleton_one_subset_frontier_cylinder (Subset.rfl : C ⊆ C) ⟨hxC, rfl⟩
    have hxnotU : x ∉ U := fun hxU => hmeet ⟨x, hxU, hx⟩
    have hxnotS : x ∉ S := by
      rw [← hVf, frontier, hV.interior_eq]
      exact fun h => h.2 hx
    have hQW : (Q ∩ W).Nonempty := by
      refine ⟨⟨(x, 1), hxtop⟩, ⟨⟨hxtop, ?_⟩, ?_⟩, hx, rfl⟩
      · exact fun h => hxnotU h.1
      · exact fun h => hxnotS h.1
    have hQsub : Q ⊆ W := hQ.m76_subset_of_disjoint_frontier hW hdis hQW
    have hxbottom : (x, (-1 : ℝ)) ∈ Z := by
      dsimp [Z]
      rw [frontier_prod_eq, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
      exact Or.inl ⟨subset_closure hxC, by simp⟩
    have hbottomQ : (⟨(x, -1), hxbottom⟩ : Z) ∈ Q := by
      refine ⟨⟨hxbottom, ?_⟩, ?_⟩ <;> intro h <;> norm_num at h
    have hbad := (hQsub hbottomQ).2
    norm_num at hbad
  have hUV : U ⊆ V := by
    apply hUc.isPreconnected.m76_subset_of_disjoint_frontier hV
    · rw [hVf, ← hUf, frontier, hU.interior_eq]
      exact Set.disjoint_left.mpr fun _ hx hy => hx.2 hy
    · exact hmeet
  have hVU : V ⊆ U := by
    apply hVc.isPreconnected.m76_subset_of_disjoint_frontier hU
    · rw [hUf, ← hVf, frontier, hV.interior_eq]
      exact Set.disjoint_left.mpr fun _ hx hy => hx.2 hy
    · obtain ⟨x, hxU, hxV⟩ := hmeet
      exact ⟨x, hxV, hxU⟩
  rwa [Subset.antisymm hUV hVU] at hUB

omit [FiniteDimensional ℝ E] in




theorem indexThree_chart_boundary_isFinitePL
    (e : OpenPartialHomeomorph (Fin 3 → ℝ) E)
    (hsource : closedBall (0 : Fin 3 → ℝ) 1 ⊆ e.source)
    {N : Set (Fin 3 → ℝ)} (hPL : LocallyPiecewiseAffineOn e N)
    (hN : sphere (0 : Fin 3 → ℝ) 1 ⊆ N) :
    (e.homeomorphOfImageSubsetSource
      (sphere_subset_closedBall.trans hsource) rfl).IsFinitePL := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKB, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair (Fin 3 → ℝ)
      (closedBall (0 : Fin 3 → ℝ) 1) (sphere (0 : Fin 3 → ℝ) 1))
  let L := K.frontierSubcomplex (closedBall (0 : Fin 3 → ℝ) 1)
  have hL : L.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hLs : L.space = sphere (0 : Fin 3 → ℝ) 1 := by
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKB,
      frontier_closedBall _ one_ne_zero]
  refine ⟨e, ?_, fun _ => rfl⟩
  rw [← hLs]
  exact hPL.finitePiecewiseAffineOn L hL (hLs.subset.trans hN)

omit [FiniteDimensional ℝ E] in




theorem indexThree_chart_image_isFinitePLBallPair
    (e : OpenPartialHomeomorph (Fin 3 → ℝ) E)
    (hsource : closedBall (0 : Fin 3 → ℝ) 1 ⊆ e.source)
    {C : Set E} (hC : e '' closedBall (0 : Fin 3 → ℝ) 1 ⊆ interior C)
    (hregions : HasAlexanderRegionBalls (e '' sphere (0 : Fin 3 → ℝ) 1) C) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (e '' closedBall (0 : Fin 3 → ℝ) 1)
      (e '' sphere (0 : Fin 3 → ℝ) 1) := by
  let V := e '' ball (0 : Fin 3 → ℝ) 1
  have hballsource : ball (0 : Fin 3 → ℝ) 1 ⊆ e.source :=
    ball_subset_closedBall.trans hsource
  have hV : IsOpen V := e.isOpen_image_of_subset_source isOpen_ball hballsource
  have hVc : IsConnected V :=
    (isConnected_ball (x := (0 : Fin 3 → ℝ)) zero_lt_one).image e
      (e.continuousOn.mono hballsource)
  have hclosure : closure V = e '' closedBall (0 : Fin 3 → ℝ) 1 := by
    have hc : closure (ball (0 : Fin 3 → ℝ) 1) = closedBall 0 1 :=
      closure_ball _ one_ne_zero
    have hcompact : IsCompact (closure (ball (0 : Fin 3 → ℝ) 1)) := by
      rw [hc]
      exact isCompact_closedBall _ _
    have hcont : ContinuousOn e (closure (ball (0 : Fin 3 → ℝ) 1)) := by
      rw [hc]
      exact e.continuousOn.mono hsource
    simpa only [hc] using (image_closure_of_isCompact hcompact hcont).symm
  have hfront : frontier V = e '' sphere (0 : Fin 3 → ℝ) 1 := by
    rw [frontier, hV.interior_eq, hclosure]
    rw [← (e.injOn.mono hsource).image_sdiff_subset ball_subset_closedBall]
    congr 1
    ext x
    simp only [mem_sdiff, mem_closedBall, mem_ball, mem_sphere,
      not_lt, le_antisymm_iff]
  have hresult := hasAlexanderRegionBalls_identifies_open_region hregions hV hVc hfront
    ((image_mono ball_subset_closedBall).trans hC)
  rwa [hclosure] at hresult








theorem exists_indexThree_chart_handleStraightening_of_region_balls
    (e : OpenPartialHomeomorph (Fin 3 → ℝ) E)
    (hsource : closedBall (0 : Fin 3 → ℝ) 1 ⊆ e.source)
    {N : Set (Fin 3 → ℝ)} (hPL : LocallyPiecewiseAffineOn e N)
    (hN : sphere (0 : Fin 3 → ℝ) 1 ⊆ N)
    {C : Set E} (hC : e '' closedBall (0 : Fin 3 → ℝ) 1 ⊆ interior C)
    (hregions : HasAlexanderRegionBalls (e '' sphere (0 : Fin 3 → ℝ) 1) C) :
    ∃ g : closedBall (0 : Fin 3 → ℝ) 1 ≃ₜ
        e '' closedBall (0 : Fin 3 → ℝ) 1,
      g.IsFinitePL ∧
      (∀ x : sphere (0 : Fin 3 → ℝ) 1,
        (g ⟨x, sphere_subset_closedBall x.property⟩ : E) = e x) ∧
      ∃ A : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
        (∀ x : closedBall (0 : Fin 3 → ℝ) 1, A x = e.symm (g x)) ∧
        (∀ x, 1 ≤ ‖x‖ → A x = x) ∧
        Nonempty (ContinuousMap.HomotopyWith
          (ContinuousMap.id (Fin 3 → ℝ)) ⟨A, A.continuous⟩
          (fun f => IsHomeomorph f ∧ ∀ x, 1 ≤ ‖x‖ → f x = x)) := by
  let h := e.homeomorphOfImageSubsetSource hsource rfl
  let eb := e.homeomorphOfImageSubsetSource
    (sphere_subset_closedBall.trans hsource) rfl
  have ht := indexThree_chart_image_isFinitePLBallPair e hsource hC hregions
  have heb : eb.IsFinitePL := indexThree_chart_boundary_isFinitePL e hsource hPL hN
  have hboundary (x : sphere (0 : Fin 3 → ℝ) 1) :
      h ⟨x, sphere_subset_closedBall x.property⟩ =
        ⟨eb x, ht.1 (eb x).property⟩ := Subtype.ext rfl
  obtain ⟨g, hg, hgb, A, hA, hfix, hHt⟩ :=
    Homeomorph.exists_finitePL_cube_straightening h ht eb heb hboundary
  refine ⟨g, hg, ?_, A, ?_, hfix, hHt⟩
  · intro x
    exact congrArg Subtype.val (hgb x)
  · intro x
    exact hA x

end PoincareConjecture.M76
