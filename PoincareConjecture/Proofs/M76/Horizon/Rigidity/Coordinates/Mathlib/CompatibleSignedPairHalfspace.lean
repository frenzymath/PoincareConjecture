import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.SignedCoordinateCorner









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_compatible_halfspace_of_signed_pair
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) {C : Set X} {p : X}
    (H : OpenPartialHomeomorph X C3) (hp : p ∈ H.source) (hzero : H p = 0)
    (hcompat : ∀ i,
      LocallyPiecewiseAffineOn ((e i).symm.trans H) ((e i).symm.trans H).source)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hpair : (∀ x ∈ H.source, x ∈ C ↔ 0 ≤ ε * (H x).2) ∨
      (∀ x ∈ H.source, x ∈ C ↔ 0 ≤ (H x).1.1 ∧ 0 ≤ ε * (H x).2)) :
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ p ∈ B.source ∧ ell (B p) = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ x ∈ B.source, x ∈ C ↔ 0 ≤ ell (B x) := by
  let c : V3 ≃L[ℝ] C3 := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hlinear : LocallyPiecewiseAffineOn c.symm.toHomeomorph.toOpenPartialHomeomorph
      c.symm.toHomeomorph.toOpenPartialHomeomorph.source :=
    locallyPiecewiseAffineOn_affine c.symm.toContinuousAffineEquiv.toContinuousAffineMap
      isOpen_univ
  have hcompose (J : OpenPartialHomeomorph C3 V3)
      (hJ : LocallyPiecewiseAffineOn J J.source) (i : ι) :
      (e i).symm.trans (H.trans J) ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have h : LocallyPiecewiseAffineOn (((e i).symm.trans H).trans J)
        (((e i).symm.trans H).trans J).source := hJ.comp (hcompat i)
    simpa only [OpenPartialHomeomorph.trans_assoc] using h
  rcases hpair with hhalf | hquad
  · let J := c.symm.toHomeomorph.toOpenPartialHomeomorph
    let B := H.trans J
    let ell : V3 →ᴬ[ℝ] ℝ :=
      (ε • (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap).comp
        c.toContinuousAffineEquiv.toContinuousAffineMap
    have hBs : B.source = H.source := by
      change H.source ∩ H ⁻¹' (univ : Set C3) = H.source
      rw [preimage_univ, inter_univ]
    have hell (x : X) : ell (B x) = ε * (H x).2 := by
      change ε * (c (c.symm (H x))).2 = ε * (H x).2
      rw [c.apply_symm_apply]
    refine ⟨ell, c.symm ((0 : ℝ × ℝ), ε), B, ?_, hBs.symm.subset hp, ?_,
      hcompose J hlinear, ?_⟩
    · change ε * (c (c.symm ((0 : ℝ × ℝ), ε))).2 = 1
      rw [c.apply_symm_apply]
      rcases hε with rfl | rfl <;> norm_num
    · rw [hell, hzero]
      exact mul_zero ε
    · intro x hx
      rw [hell]
      exact hhalf x (hBs.subset hx)
  · obtain ⟨F, hF, hF0, hFquad, _, _⟩ := exists_signed_coordinate_corner ε hε
    let J := F.toOpenPartialHomeomorph.trans c.symm.toHomeomorph.toOpenPartialHomeomorph
    let B := H.trans J
    let ell : V3 →ᴬ[ℝ] ℝ :=
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).toContinuousAffineMap).comp
          c.toContinuousAffineEquiv.toContinuousAffineMap
    have hJs : J.source = univ := by
      simp only [J, OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    have hBs : B.source = H.source := by
      change (H.trans J).source = H.source
      rw [OpenPartialHomeomorph.trans_source, hJs, preimage_univ, inter_univ]
    have hell (x : X) : ell (B x) = (F (H x)).1.1 := by
      change (c (c.symm (F (H x)))).1.1 = (F (H x)).1.1
      rw [c.apply_symm_apply]
    refine ⟨ell, c.symm ((1, 0), 0), B, ?_, hBs.symm.subset hp, ?_,
      hcompose J (hlinear.comp hF.1), ?_⟩
    · change (c (c.symm ((1, 0), 0))).1.1 = 1
      rw [c.apply_symm_apply]
    · rw [hell, hzero, hF0]
      rfl
    · intro x hx
      rw [hell]
      exact (hquad x (hBs.subset hx)).trans (hFquad (H x))

end PoincareConjecture.M76
