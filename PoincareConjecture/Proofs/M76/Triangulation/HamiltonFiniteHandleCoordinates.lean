import PoincareConjecture.Proofs.M76.Triangulation.HamiltonHandleCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonTheoremOne
import Mathlib.Data.Fintype.EquivFin











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

private theorem exists_finite_handle_coordinates {k : ℕ}
    (J : Finset (Fin 3)) (hJ : J.card = k) :
    ∃ a : ((Fin k ⊕ Fin (3 - k)) → ℝ) ≃ᴬ[ℝ] (Fin 3 → ℝ),
      (∀ x, ‖a x‖ = ‖x‖) ∧
        ∀ x, x ∈ coordinateCylinder (Finset.univ.map
          (Function.Embedding.inl : Fin k ↪ Fin k ⊕ Fin (3 - k))) ↔
          a x ∈ coordinateCylinder J := by
  classical
  let e : Fin k ≃ J := (Finset.equivFinOfCardEq hJ).symm
  have hfree : Fintype.card {i : Fin 3 // i ∉ J} = 3 - k := by
    change Fintype.card ↥((J : Set (Fin 3))ᶜ) = 3 - k
    rw [Fintype.card_compl_set, Fintype.card_fin]
    change 3 - Fintype.card J = 3 - k
    rw [Fintype.card_coe, hJ]
  let f : Fin (3 - k) ≃ {i : Fin 3 // i ∉ J} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hfree])
  let sigma := (Equiv.sumCongr e f).trans (Equiv.sumCompl (fun i : Fin 3 => i ∈ J))
  let a : ((Fin k ⊕ Fin (3 - k)) → ℝ) ≃ᴬ[ℝ] (Fin 3 → ℝ) :=
    (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin k ⊕ Fin (3 - k) => ℝ)
      sigma).toAffineEquiv.toContinuousAffineEquiv
  have hnorm (x : (Fin k ⊕ Fin (3 - k)) → ℝ) : ‖a x‖ = ‖x‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
      intro i
      exact norm_le_pi_norm x (sigma.symm i)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (a x))).mpr
      intro i
      have hi := norm_le_pi_norm (a x) (sigma i)
      change ‖x (sigma.symm (sigma i))‖ ≤ ‖a x‖ at hi
      simpa only [sigma.symm_apply_apply] using hi
  refine ⟨a, hnorm, ?_⟩
  intro x
  constructor
  · intro hx i hi
    let j := e.symm ⟨i, hi⟩
    have hsigma : sigma (Sum.inl j) = i := by
      change (e (e.symm ⟨i, hi⟩) : Fin 3) = i
      exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)
    change |x (sigma.symm i)| ≤ 1
    rw [← hsigma, sigma.symm_apply_apply]
    exact hx _ (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · intro hx i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    have hj : sigma (Sum.inl j) ∈ J := (e j).property
    have hh := hx _ hj
    change |x (sigma.symm (sigma (Sum.inl j)))| ≤ 1 at hh
    change |x (Sum.inl j)| ≤ 1
    simpa only [sigma.symm_apply_apply] using hh






theorem hasHamiltonChartHandleStraightening_of_product_case
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    {k : ℕ} (hk : 0 < k) (J : Finset (Fin 3)) (hJ : J.card = k)
    (hcase : ∀ h : OpenPartialHomeomorph
        ((Fin k → ℝ) × (Fin (3 - k) → ℝ)) (Fin 3 → ℝ),
      closedBall (0 : Fin k → ℝ) 1 ×ˢ (univ : Set (Fin (3 - k) → ℝ)) ⊆ h.source →
      ∀ N : Set ((Fin k → ℝ) × (Fin (3 - k) → ℝ)), IsOpen N →
        sphere (0 : Fin k → ℝ) 1 ×ˢ (univ : Set (Fin (3 - k) → ℝ)) ⊆ N →
        LocallyPiecewiseAffineOn h (h.source ∩ N) →
        ∃ B : ((Fin k ⊕ Fin (3 - k)) → ℝ) ≃ₜ ((Fin k ⊕ Fin (3 - k)) → ℝ),
          FinitePiecewiseAffineOn
            ((h ∘ (fun y => (fun i => y (Sum.inl i), fun j => y (Sum.inr j)))) ∘ B)
            (closedBall (0 : (Fin k ⊕ Fin (3 - k)) → ℝ) 1) ∧
          Nonempty (ContinuousMap.HomotopyWith
            (ContinuousMap.id ((Fin k ⊕ Fin (3 - k)) → ℝ)) ⟨B, B.continuous⟩
            (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
              ∀ x ∈ (coordinateCylinder (Finset.univ.map
                (Function.Embedding.inl : Fin k ↪ Fin k ⊕ Fin (3 - k))))ᶜ ∪
                frontier (coordinateCylinder (Finset.univ.map
                  (Function.Embedding.inl : Fin k ↪ Fin k ⊕ Fin (3 - k)))), f x = x))) :
    HasHamiltonChartHandleStraightening E J := by
  classical
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  intro e hsource N hN hfront hPL
  obtain ⟨a, hnorm, hcyl⟩ := exists_finite_handle_coordinates J hJ
  let c := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin k) (Fin (3 - k))
    (fun _ => ℝ)).toContinuousAffineEquiv
  let b := c.symm.trans a
  let t : E ≃ᴬ[ℝ] (Fin 3 → ℝ) :=
    (ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)).toContinuousAffineEquiv
  let h := (b.toHomeomorph.transOpenPartialHomeomorph e).transHomeomorph t.toHomeomorph
  let U := b ⁻¹' N
  have hbC : b ⁻¹' coordinateCylinder J =
      closedBall (0 : Fin k → ℝ) 1 ×ˢ (univ : Set (Fin (3 - k) → ℝ)) := by
    ext y
    change a (c.symm y) ∈ coordinateCylinder J ↔ _
    rw [← hcyl (c.symm y)]
    constructor
    · intro hy
      refine ⟨mem_closedBall_zero_iff.mpr ?_, mem_univ _⟩
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      exact hy _ (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · intro hy i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact (norm_le_pi_norm y.1 j).trans (mem_closedBall_zero_iff.mp hy.1)
  have hhsource : closedBall (0 : Fin k → ℝ) 1 ×ˢ
      (univ : Set (Fin (3 - k) → ℝ)) ⊆ h.source := by
    intro y hy
    have hy' : y ∈ b ⁻¹' coordinateCylinder J := hbC.symm ▸ hy
    exact hsource hy'
  have hU : IsOpen U := hN.preimage b.continuous
  have hUfront : sphere (0 : Fin k → ℝ) 1 ×ˢ
      (univ : Set (Fin (3 - k) → ℝ)) ⊆ U := by
    have heq : b.toHomeomorph ⁻¹' frontier (coordinateCylinder J) =
        sphere (0 : Fin k → ℝ) 1 ×ˢ (univ : Set (Fin (3 - k) → ℝ)) := by
      rw [b.toHomeomorph.preimage_frontier]
      change frontier (b ⁻¹' coordinateCylinder J) = _
      rw [hbC, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
    intro y hy
    have hy' : y ∈ b.toHomeomorph ⁻¹' frontier (coordinateCylinder J) := heq.symm ▸ hy
    exact hfront hy'
  have hpre : LocallyPiecewiseAffineOn (e ∘ b) (h.source ∩ U) :=
    (hPL.comp (locallyPiecewiseAffineOn_affine b.toContinuousAffineMap isOpen_univ)).mono
      (h.open_source.inter hU) (fun y hy => ⟨mem_univ _, hy.1, hy.2⟩)
  have hhPL : LocallyPiecewiseAffineOn h (h.source ∩ U) :=
    ((locallyPiecewiseAffineOn_affine t.toContinuousAffineMap isOpen_univ).comp hpre).mono
      (h.open_source.inter hU) (fun y hy => ⟨hy, mem_univ _⟩)
  obtain ⟨B, hBPL, ⟨HB⟩⟩ := hcase h hhsource U hU hUfront hhPL
  have hactual (x : (Fin k ⊕ Fin (3 - k)) → ℝ) : h (c x) = t (e (a x)) := by
    change t (e (a (c.symm (c x)))) = _
    rw [c.symm_apply_apply]
  have htarget : FinitePiecewiseAffineOn (fun x => e (a (B x)))
      (closedBall (0 : (Fin k ⊕ Fin (3 - k)) → ℝ) 1) := by
    apply (hBPL.postcomp t.symm.toContinuousAffineMap).congr
    intro x _
    change t.symm (h (c (B x))) = e (a (B x))
    rw [hactual, t.symm_apply_apply]
  let C := a.symm.toHomeomorph.trans (B.trans a.toHomeomorph)
  have hnorminv (x : Fin 3 → ℝ) : ‖a.symm x‖ = ‖x‖ := by
    have hh := hnorm (a.symm x)
    rw [a.apply_symm_apply] at hh
    exact hh.symm
  have hball : a '' closedBall (0 : (Fin k ⊕ Fin (3 - k)) → ℝ) 1 =
      closedBall (0 : Fin 3 → ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_closedBall_zero_iff.mpr ((hnorm y).symm ▸ mem_closedBall_zero_iff.mp hy)
    · intro hx
      exact ⟨a.symm x, by simpa only [mem_closedBall_zero_iff, hnorminv] using hx,
        a.apply_symm_apply x⟩
  have hCPL : FinitePiecewiseAffineOn (e ∘ C) (closedBall (0 : Fin 3 → ℝ) 1) := by
    have hh := htarget.precomp_affineEquiv a.symm
    change FinitePiecewiseAffineOn (e ∘ C)
      (a '' closedBall (0 : (Fin k ⊕ Fin (3 - k)) → ℝ) 1) at hh
    rwa [hball] at hh
  have hCout (x : Fin 3 → ℝ) (hx : 2 ≤ ‖x‖) : C x = x := by
    have hfix := (HB.prop 1).2.1 (a.symm x) (by rwa [hnorminv])
    change HB (1, a.symm x) = a.symm x at hfix
    rw [HB.apply_one] at hfix
    change B (a.symm x) = a.symm x at hfix
    change a (B (a.symm x)) = x
    rw [hfix, a.apply_symm_apply]
  have hCrel (x : Fin 3 → ℝ) (hx : x ∉ coordinateCylinder J) : C x = x := by
    have hnot : a.symm x ∉ coordinateCylinder (Finset.univ.map
        (Function.Embedding.inl : Fin k ↪ Fin k ⊕ Fin (3 - k))) := by
      intro hy
      have hh := (hcyl (a.symm x)).mp hy
      rw [a.apply_symm_apply] at hh
      exact hx hh
    have hfix := (HB.prop 1).2.2 (a.symm x) (Or.inl hnot)
    change HB (1, a.symm x) = a.symm x at hfix
    rw [HB.apply_one] at hfix
    change B (a.symm x) = a.symm x at hfix
    change a (B (a.symm x)) = x
    rw [hfix, a.apply_symm_apply]
  have hstar : StarConvex ℝ (0 : Fin 3 → ℝ) (coordinateCylinder J) :=
    (convex_coordinateCylinder J).starConvex (by intro i _; simp)
  exact ⟨C, hCPL,
    ⟨C.relativeSupportedAlexanderHomotopy (by norm_num) hCout hstar hCrel⟩⟩

end PoincareConjecture.M76
