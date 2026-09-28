import PoincareConjecture.Proofs.M76.Rigidity.OriginalCutSideCharts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.SignedCoordinateCorner
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.exists_cap_halfspace_chart
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    {t : ℝ} (ht : t ∈ ({-(1 / 2 : ℝ), 1 / 2} : Set ℝ)) (z : D) :
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ P.slice t z ∈ B.source ∧ ell (B (P.slice t z)) = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ B.source, x ∈ P.cutCarrier ↔ 0 ≤ ell (B x)) ∧
      ((B.source ⊆ interior R ∧
        ∀ x ∈ B.source, x ∈ P.slice t '' D ↔ ell (B x) = 0) ∨
       ∃ eta : V3 →ᴬ[ℝ] ℝ,
        (∀ x ∈ B.source, (x ∈ frontier R ∧ x ∈ P.cutCarrier) ↔
          ell (B x) = 0 ∧ 0 ≤ eta (B x)) ∧
        ∀ x ∈ B.source, x ∈ P.slice t '' D ↔ ell (B x) = 0 ∧ eta (B x) ≤ 0) := by
  obtain ⟨H, ε, hε, hzH, hHz, hcompat, hpair⟩ :=
    P.exists_cut_side_chart hR he hopen ht z
  let c : V3 ≃L[ℝ] C3 := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hεsq : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεne : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hlinear : LocallyPiecewiseAffineOn c.symm.toHomeomorph.toOpenPartialHomeomorph
      c.symm.toHomeomorph.toOpenPartialHomeomorph.source :=
    locallyPiecewiseAffineOn_affine c.symm.toContinuousAffineEquiv.toContinuousAffineMap
      isOpen_univ
  have hcompose (J : OpenPartialHomeomorph C3 V3)
      (hJ : LocallyPiecewiseAffineOn J J.source) (i : ι) :
      (e i).symm.trans (H.trans J) ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have h : LocallyPiecewiseAffineOn (((e i).symm.trans H).trans J)
        (((e i).symm.trans H).trans J).source := hJ.comp (hcompat i).1
    simpa only [OpenPartialHomeomorph.trans_assoc] using h
  rcases hpair with ⟨hinside, hside, hcap⟩ | ⟨hregion, hside, hcap⟩
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
    have hv : ell.contLinear (c.symm ((0 : ℝ × ℝ), ε)) = 1 := by
      change ε * (c (c.symm ((0 : ℝ × ℝ), ε))).2 = 1
      rw [c.apply_symm_apply]
      exact hεsq
    refine ⟨ell, c.symm ((0 : ℝ × ℝ), ε), B, hv, hBs.symm.subset hzH, ?_,
      hcompose J hlinear, ?_, Or.inl ⟨hBs.subset.trans hinside, ?_⟩⟩
    · rw [hell, hHz]
      exact mul_zero ε
    · intro x hx
      rw [hell]
      exact hside x (hBs.subset hx)
    · intro x hx
      rw [hell]
      have hmul : ε * (H x).2 = 0 ↔ (H x).2 = 0 := by
        simp only [mul_eq_zero, hεne, false_or]
      exact (hcap x (hBs.subset hx)).trans hmul.symm
  · obtain ⟨F, hF, hF0, hquad, hold, hnew⟩ := exists_signed_coordinate_corner ε hε
    let J := F.toOpenPartialHomeomorph.trans c.symm.toHomeomorph.toOpenPartialHomeomorph
    let B := H.trans J
    let a : C3 →ᴬ[ℝ] ℝ := ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)).toContinuousAffineMap
    let ell : V3 →ᴬ[ℝ] ℝ := a.comp c.toContinuousAffineEquiv.toContinuousAffineMap
    let eta : V3 →ᴬ[ℝ] ℝ :=
      (ε • (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap).comp
        c.toContinuousAffineEquiv.toContinuousAffineMap
    have hJs : J.source = univ := by
      simp only [J, OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    have hBs : B.source = H.source := by
      change (H.trans J).source = H.source
      rw [OpenPartialHomeomorph.trans_source, hJs, preimage_univ, inter_univ]
    have hJ : LocallyPiecewiseAffineOn J J.source := hlinear.comp hF.1
    have hell (x : X) : ell (B x) = (F (H x)).1.1 := by
      change (c (c.symm (F (H x)))).1.1 = (F (H x)).1.1
      rw [c.apply_symm_apply]
    have heta (x : X) : eta (B x) = ε * (F (H x)).2 := by
      change ε * (c (c.symm (F (H x)))).2 = ε * (F (H x)).2
      rw [c.apply_symm_apply]
    have hv : ell.contLinear (c.symm ((1, 0), (0 : ℝ))) = 1 := by
      change (c (c.symm ((1, 0), (0 : ℝ)))).1.1 = 1
      rw [c.apply_symm_apply]
    have ha : a.toAffineMap.linear ≠ 0 := by
      intro h
      have hval : a.toAffineMap.linear ((1, 0), (0 : ℝ)) = 1 := rfl
      rw [h] at hval
      norm_num at hval
    have hfront := H.isImage_frontier_of_affine_nonneg a ha hregion
    have hfrontR (x : X) (hx : x ∈ H.source) :
        x ∈ frontier R ↔ (H x).1.1 = 0 := (hfront.apply_mem_iff hx).symm
    refine ⟨ell, c.symm ((1, 0), (0 : ℝ)), B, hv, hBs.symm.subset hzH, ?_,
      hcompose J hJ, ?_, Or.inr ⟨eta, ?_, ?_⟩⟩
    · rw [hell, hHz, hF0]
      rfl
    · intro x hx
      rw [hell]
      exact (hside x (hBs.subset hx)).trans (hquad (H x))
    · intro x hx
      have hxH := hBs.subset hx
      rw [hell, heta]
      constructor
      · intro h
        exact (hold (H x)).mp ⟨(hfrontR x hxH).mp h.1, ((hside x hxH).mp h.2).2⟩
      · intro h
        obtain ⟨ha0, hb0⟩ := (hold (H x)).mpr h
        exact ⟨(hfrontR x hxH).mpr ha0,
          (hside x hxH).mpr ⟨ha0.symm.le, hb0⟩⟩
    · intro x hx
      rw [hell, heta]
      exact (hcap x (hBs.subset hx)).trans (and_comm.trans (hnew (H x)))

end PoincareConjecture.M76
