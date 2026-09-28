import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedCoreStretch
import PoincareConjecture.Proofs.M76.Triangulation.PLHandleCompactification









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76





theorem exists_plHandleCompactification_with_protected_core
    (ι : Type*) [Fintype ι] (J : Finset ι) {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ p : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ),
      p.source = univ ∧ p.target = ball 0 2 ∧
      (∀ x, ‖x‖ ≤ 1 → p x = x) ∧
      (∀ x ∈ coordinateCylinder J, ‖x‖ ≤ r → p x = x) ∧
      LocallyPiecewiseAffineOn p p.source ∧
      LocallyPiecewiseAffineOn p.symm p.target ∧
      ∀ (G : coordinateCylinder J ≃ₜ coordinateCylinder J) (C : ℝ),
        0 ≤ C → (∀ x : coordinateCylinder J, ‖(G x : ι → ℝ) - x‖ ≤ C) →
        (∀ x : coordinateCylinder J,
          (x : ι → ℝ) ∈ frontier (coordinateCylinder J) → G x = x) →
        ∃ A : (ι → ℝ) ≃ₜ (ι → ℝ),
          (∀ x : coordinateCylinder J, A (p x) = p (G x)) ∧
          Nonempty (ContinuousMap.HomotopyWith (ContinuousMap.id (ι → ℝ))
            ⟨A, A.continuous⟩
            (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
              ∀ x ∈ (coordinateCylinder J)ᶜ ∪ frontier (coordinateCylinder J),
                f x = x)) := by
  obtain ⟨F, hFPL, hFJ, hFball, hFbound, hFcore⟩ :=
    exists_protected_core_stretch ι J hr hr2
  obtain ⟨p0, hp0s, hp0t, hp0core, hp0PL, hp0iPL, hcompact⟩ :=
    exists_plHandleCompactification ι J
  have hFmem (x : ι → ℝ) : x ∈ coordinateCylinder J ↔ F x ∈ coordinateCylinder J := by
    constructor
    · intro hx i hi
      rw [hFJ x i hi]
      exact hx i hi
    · intro hx i hi
      rw [← hFJ x i hi]
      exact hx i hi
  have hFpre : F ⁻¹' coordinateCylinder J = coordinateCylinder J :=
    Set.ext (fun x => (hFmem x).symm)
  have hFfront : F ⁻¹' frontier (coordinateCylinder J) =
      frontier (coordinateCylinder J) := by
    rw [F.preimage_frontier, hFpre]
  have hFibound (x : ι → ℝ) : ‖F.symm x - x‖ ≤ 4 := by
    have h := hFbound (F.symm x)
    rw [F.apply_symm_apply] at h
    exact (norm_sub_rev _ _).trans_le h
  let FD : coordinateCylinder J ≃ₜ coordinateCylinder J := F.subtype hFmem
  let p := F.symm.toOpenPartialHomeomorph.trans (p0.trans F.toOpenPartialHomeomorph)
  have hps : p.source = univ := by
    change univ ∩ F.symm ⁻¹' (p0.source ∩ p0 ⁻¹' univ) = univ
    rw [hp0s, preimage_univ, inter_self, preimage_univ, inter_self]
  have hpt : p.target = ball 0 2 := by
    change (univ ∩ F.symm ⁻¹' p0.target) ∩ _ ⁻¹' univ = ball 0 2
    rw [preimage_univ, inter_univ, univ_inter, hp0t]
    ext x
    simp only [mem_preimage, mem_ball_zero_iff]
    simpa only [F.apply_symm_apply] using (hFball (F.symm x)).symm
  have hpPL : p ∈ piecewiseAffineGroupoid (ι → ℝ) :=
    (piecewiseAffineGroupoid (ι → ℝ)).trans
      ((piecewiseAffineGroupoid (ι → ℝ)).symm hFPL)
      ((piecewiseAffineGroupoid (ι → ℝ)).trans ⟨hp0PL, hp0iPL⟩ hFPL)
  have hpcore (x : ι → ℝ) (hx : x ∈ coordinateCylinder J) (hxr : ‖x‖ ≤ r) : p x = x := by
    change F (p0 (F.symm x)) = x
    rw [hp0core _ (hFcore x hx hxr), F.apply_symm_apply]
  refine ⟨p, hps, hpt, ?_, hpcore, hpPL.1, hpPL.2, ?_⟩
  · intro x hx
    apply hpcore x _ (hx.trans hr.le)
    intro i _
    have hxi := (pi_norm_le_iff_of_nonneg zero_le_one).mp hx i
    simpa only [Real.norm_eq_abs] using hxi
  · intro G C hC hGbound hGfront
    let G0 := FD.trans (G.trans FD.symm)
    have hG0bound (x : coordinateCylinder J) : ‖(G0 x : ι → ℝ) - x‖ ≤ C + 8 := by
      change ‖F.symm (G (FD x)) - (x : ι → ℝ)‖ ≤ C + 8
      calc
        _ ≤ ‖F.symm (G (FD x)) - (G (FD x) : ι → ℝ)‖ +
            ‖(G (FD x) : ι → ℝ) - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 4 + (‖(G (FD x) : ι → ℝ) - F x‖ + ‖F x - (x : ι → ℝ)‖) :=
          add_le_add (hFibound _) (norm_sub_le_norm_sub_add_norm_sub _ _ _)
        _ ≤ 4 + (C + 4) := add_le_add le_rfl (add_le_add (hGbound (FD x)) (hFbound x))
        _ = C + 8 := by ring
    have hG0front (x : coordinateCylinder J)
        (hx : (x : ι → ℝ) ∈ frontier (coordinateCylinder J)) : G0 x = x := by
      have hFx : (FD x : ι → ℝ) ∈ frontier (coordinateCylinder J) := by
        change (x : ι → ℝ) ∈ F ⁻¹' frontier (coordinateCylinder J)
        rwa [hFfront]
      change FD.symm (G (FD x)) = x
      rw [hGfront (FD x) hFx, FD.symm_apply_apply]
    obtain ⟨A0, hA0, ⟨H0⟩⟩ :=
      hcompact G0 (C + 8) (by linarith) hG0bound hG0front
    have hA0out (x : ι → ℝ) (hx : 2 ≤ ‖x‖) : A0 x = x := by
      simpa using (H0.prop 1).2.1 x hx
    have hA0rel (x : ι → ℝ)
        (hx : x ∈ (coordinateCylinder J)ᶜ ∪ frontier (coordinateCylinder J)) : A0 x = x := by
      simpa using (H0.prop 1).2.2 x hx
    let A := F.symm.trans (A0.trans F)
    have hA (x : coordinateCylinder J) : A (p x) = p (G x) := by
      change F (A0 (F.symm (F (p0 (F.symm x))))) = F (p0 (F.symm (G x)))
      rw [F.symm_apply_apply]
      apply congrArg F
      have h := hA0 (FD.symm x)
      change A0 (p0 (F.symm x)) = p0 (F.symm (G (FD (FD.symm x)))) at h
      simpa only [FD.apply_symm_apply] using h
    have hAout (x : ι → ℝ) (hx : 2 ≤ ‖x‖) : A x = x := by
      have hnorm : 2 ≤ ‖F.symm x‖ := by
        apply le_of_not_gt
        intro h
        have hxlt := (hFball (F.symm x)).mpr h
        rw [F.apply_symm_apply] at hxlt
        exact (not_lt_of_ge hx) hxlt
      change F (A0 (F.symm x)) = x
      rw [hA0out _ hnorm, F.apply_symm_apply]
    have hAext (x : ι → ℝ) (hx : x ∉ coordinateCylinder J) : A x = x := by
      have hFx : F.symm x ∉ coordinateCylinder J := by
        intro h
        apply hx
        simpa only [F.apply_symm_apply] using (hFmem (F.symm x)).mp h
      change F (A0 (F.symm x)) = x
      rw [hA0rel _ (Or.inl hFx), F.apply_symm_apply]
    have hstar : StarConvex ℝ (0 : ι → ℝ) (coordinateCylinder J) :=
      (convex_coordinateCylinder J).starConvex (by intro i _; simp)
    exact ⟨A, hA, ⟨A.relativeSupportedAlexanderHomotopy (by norm_num) hAout hstar hAext⟩⟩

end PoincareConjecture.M76
