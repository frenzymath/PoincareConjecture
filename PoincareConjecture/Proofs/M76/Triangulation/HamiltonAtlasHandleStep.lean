import PoincareConjecture.Proofs.M76.Triangulation.HamiltonSupportedHandle










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76




theorem locallyPiecewiseAffineOn_incoming_handle_chart
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (c : ι → OpenPartialHomeomorph X E)
    (hcover : ∀ x : X, ∃ i, x ∈ (c i).source)
    (p : OpenPartialHomeomorph (Fin 3 → ℝ) X) (d : OpenPartialHomeomorph X E)
    (hcharts : ∀ i, LocallyPiecewiseAffineOn (p.trans (c i)) (p.trans (c i)).source)
    {U : Set X} (hU : IsOpen U)
    (hUpl : ∀ i, LocallyPiecewiseAffineOn (d ∘ (c i).symm)
      ((c i).target ∩ (c i).symm ⁻¹' U)) :
    LocallyPiecewiseAffineOn (p.trans d) (p.source ∩ p ⁻¹' U) := by
  have hN : IsOpen (p.source ∩ p ⁻¹' U) := p.isOpen_inter_preimage hU
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  obtain ⟨i, hi⟩ := hcover (p x)
  let T := p.trans (c i)
  have hsub : (p.source ∩ p ⁻¹' U) ∩ T.source ⊆
      T.source ∩ T ⁻¹' ((c i).target ∩ (c i).symm ⁻¹' U) := by
    intro y hy
    refine ⟨hy.2, (c i).mapsTo hy.2.2, ?_⟩
    change (c i).symm ((c i) (p y)) ∈ U
    have hcy : p y ∈ (c i).source := hy.2.2
    rw [(c i).left_inv hcy]
    exact hy.1.2
  refine ⟨T.source, ⟨hx.1, hi⟩, ?_⟩
  apply (((hUpl i).comp (hcharts i)).mono (hN.inter T.open_source) hsub).congr
  intro y hy
  change d ((c i).symm ((c i) (p y))) = d (p y)
  have hcy : p y ∈ (c i).source := hy.2.2
  rw [(c i).left_inv hcy]






theorem exists_atlas_supported_handle_step
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (c : ι → OpenPartialHomeomorph X E)
    (J : Finset (Fin 3)) (hhandle : HasHamiltonChartHandleStraightening E J)
    (p : OpenPartialHomeomorph (Fin 3 → ℝ) X) (d : OpenPartialHomeomorph X E)
    (hp : coordinateCylinder J ⊆ p.source) (hpd : p.target ⊆ d.source)
    (hcharts : ∀ i, LocallyPiecewiseAffineOn ((c i).symm.trans p.symm)
      ((c i).symm.trans p.symm).source)
    {U : Set X} (hU : IsOpen U)
    (hUpl : ∀ i, LocallyPiecewiseAffineOn (d ∘ (c i).symm)
      ((c i).target ∩ (c i).symm ⁻¹' U))
    {N : Set (Fin 3 → ℝ)} (hN : IsOpen N)
    (hfront : frontier (coordinateCylinder J) ⊆ N)
    (hNpl : LocallyPiecewiseAffineOn (p.trans d) ((p.trans d).source ∩ N)) :
    ∃ (F : X ≃ₜ X) (V S : Set X),
      IsOpen V ∧ IsCompact S ∧ S ⊆ p.target ∧ EqOn F id Sᶜ ∧
      S = p '' (coordinateCylinder J ∩ closedBall (0 : Fin 3 → ℝ) 2) ∧
      V = (U \ S) ∪ p '' (ball (0 : Fin 3 → ℝ) 1 ∪
        (((p.trans d).source ∩ N) ∩ handleTransverseStrip J)) ∧
      ∀ i, LocallyPiecewiseAffineOn ((d ∘ F) ∘ (c i).symm)
        ((c i).target ∩ (c i).symm ⁻¹' V) := by
  obtain ⟨F, hS, hSp, hFout, hcore, hcollar⟩ :=
    exists_supported_chart_handle_step J hhandle p d hp hpd hN hfront hNpl
  let S := p '' (coordinateCylinder J ∩ closedBall (0 : Fin 3 → ℝ) 2)
  let W := ball (0 : Fin 3 → ℝ) 1 ∪
    (((p.trans d).source ∩ N) ∩ handleTransverseStrip J)
  have hW : IsOpen W := isOpen_ball.union
    (((p.trans d).open_source.inter hN).inter (isOpen_handleTransverseStrip J))
  have hWp : W ⊆ p.source := by
    rintro x (hx | hx)
    · apply hp
      intro i _
      have hnorm : ‖x‖ ≤ 1 := (mem_ball_zero_iff.mp hx).le
      have hi := (pi_norm_le_iff_of_nonneg zero_le_one).mp hnorm i
      simpa only [Real.norm_eq_abs] using hi
    · exact hx.1.1.1
  have hcoreLocal : LocallyPiecewiseAffineOn (d ∘ F ∘ p) (ball (0 : Fin 3 → ℝ) 1) := by
    apply hcore.locallyPiecewiseAffineOn_of_subset_interior isOpen_ball
    rw [interior_closedBall _ one_ne_zero]
  have hWpl : LocallyPiecewiseAffineOn (d ∘ F ∘ p) W := by
    apply LocallyPiecewiseAffineOn.locality
    rintro x (hx | hx)
    · exact ⟨ball 0 1, hx, hcoreLocal.mono (hW.inter isOpen_ball) inter_subset_right⟩
    · exact ⟨_, hx, hcollar.mono (hW.inter hcollar.isOpen) inter_subset_right⟩
  have hOld : IsOpen (U \ S) := hU.inter hS.isClosed.isOpen_compl
  have hNew : IsOpen (p '' W) := p.isOpen_image_of_subset_source hW hWp
  let V := (U \ S) ∪ p '' W
  have hV : IsOpen V := hOld.union hNew
  refine ⟨F, V, S, hV, hS, hSp, hFout, rfl, rfl, ?_⟩
  intro i
  let T := (c i).symm.trans p.symm
  let Yold := (c i).target ∩ (c i).symm ⁻¹' (U \ S)
  let Ynew := (c i).target ∩ (c i).symm ⁻¹' (p '' W)
  let Y := (c i).target ∩ (c i).symm ⁻¹' V
  have hYold : IsOpen Yold := (c i).isOpen_inter_preimage_symm hOld
  have hYnew : IsOpen Ynew := (c i).isOpen_inter_preimage_symm hNew
  have hY : IsOpen Y := (c i).isOpen_inter_preimage_symm hV
  have holdPL : LocallyPiecewiseAffineOn ((d ∘ F) ∘ (c i).symm) Yold := by
    apply ((hUpl i).mono hYold (fun _ hx => ⟨hx.1, hx.2.1⟩)).congr
    intro x hx
    change d ((c i).symm x) = d (F ((c i).symm x))
    exact congrArg d (hFout hx.2.2).symm
  have hnewSub : Ynew ⊆ T.source ∩ T ⁻¹' W := by
    rintro x ⟨hx, y, hy, heq⟩
    have hxy : (c i).symm x ∈ p.target := heq ▸ p.mapsTo (hWp hy)
    refine ⟨⟨hx, hxy⟩, ?_⟩
    change p.symm ((c i).symm x) ∈ W
    rw [← heq, p.left_inv (hWp hy)]
    exact hy
  have hnewPL : LocallyPiecewiseAffineOn ((d ∘ F) ∘ (c i).symm) Ynew := by
    apply ((hWpl.comp (hcharts i)).mono hYnew hnewSub).congr
    intro x hx
    change d (F (p (p.symm ((c i).symm x)))) = d (F ((c i).symm x))
    have hpTarget : (c i).symm x ∈ p.target := (hnewSub hx).1.2
    rw [p.right_inv hpTarget]
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  rcases hx.2 with hxold | hxnew
  · exact ⟨Yold, ⟨hx.1, hxold⟩, holdPL.mono (hY.inter hYold) inter_subset_right⟩
  · exact ⟨Ynew, ⟨hx.1, hxnew⟩, hnewPL.mono (hY.inter hYnew) inter_subset_right⟩

end PoincareConjecture.M76
