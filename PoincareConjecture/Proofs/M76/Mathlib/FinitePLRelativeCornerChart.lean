import PoincareConjecture.Proofs.M76.Mathlib.AffineCornerStraightening
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNonvertexHeightChart

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

theorem exists_nonvertex_relative_corner_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → ℝ} (hf : K.AffineOnFaces f) {x : E}
    (hx : x ∈ interior K.space) (hreg : ∀ v ∈ K.vertices, f v ≠ f x)
    (B : SimplicialComplex ℝ E) (hBK : B ≤ K) (hxB : x ∈ B.space)
    (psi : E →ᴬ[ℝ] ℝ) (hzero : ∀ y ∈ B.space, psi y = 0)
    (u : E) (hu : psi.contLinear u = 1) :
    ∃ (b : E →ᴬ[ℝ] ℝ) (w : E) (T : OpenPartialHomeomorph E E),
      b.contLinear w = 1 ∧ psi.contLinear w = 0 ∧ b x = 0 ∧
      x ∈ T.source ∧ T x = x ∧ T.source ⊆ interior K.space ∧
      T ∈ piecewiseAffineGroupoid E ∧
      (∀ y ∈ T.source, (0 ≤ psi y ∧ f x ≤ f y) ↔ 0 ≤ psi (T y)) ∧
      (∀ y ∈ T.source,
        (psi y = 0 ∧ f x ≤ f y) ↔ (psi (T y) = 0 ∧ 0 ≤ b (T y))) ∧
      ∀ y ∈ T.source,
        (f y = f x ∧ 0 ≤ psi y) ↔ (psi (T y) = 0 ∧ b (T y) ≤ 0) := by
  have hpsix : psi x = 0 := hzero x hxB
  obtain ⟨ell, w, H, hellw, hpsiw, hxH, hHx, hHs, _, hHPL, hheight, hHpsi, _⟩ :=
    K.exists_nonvertex_height_chart_preserving_affine hK hf hx hreg B hBK hxB
      psi (fun y hy => (hzero y hy).trans hpsix.symm)
  let b := ell - ContinuousAffineMap.const ℝ E (f x)
  have hbw : b.contLinear w = 1 := by
    simpa only [b, ContinuousAffineMap.sub_contLinear,
      ContinuousAffineMap.const_contLinear, sub_zero] using hellw
  have hbx : b x = 0 := by
    have hellx : ell x = f x := by simpa only [hHx] using hheight x hxH
    change ell x - f x = 0
    rw [hellx, sub_self]
  let v : E := u - b.contLinear u • w
  have hpsiv : psi.contLinear v = 1 := by
    dsimp only [v]
    rw [map_sub, map_smul, hu, hpsiw, smul_zero, sub_zero]
  have hbv : b.contLinear v = 0 := by
    dsimp only [v]
    rw [map_sub, map_smul, hbw]
    change b.contLinear u - b.contLinear u * 1 = 0
    ring
  obtain ⟨C, hCPL, _, _, hCfix, hCquad, hCold, hCnew⟩ :=
    psi.exists_corner_straightening b v w hpsiv hbv hpsiw hbw
  let T := H.trans C.toOpenPartialHomeomorph
  have hbH (y : E) (hy : y ∈ H.source) : b (H y) = f y - f x := by
    change ell (H y) - f x = f y - f x
    rw [hheight y hy]
  refine ⟨b, w, T, hbw, hpsiw, hbx, ⟨hxH, mem_univ _⟩, ?_,
    (fun y hy => hHs hy.1), (piecewiseAffineGroupoid E).trans hHPL hCPL, ?_, ?_, ?_⟩
  · change C (H x) = x
    rw [hHx]
    exact hCfix x hpsix hbx
  · intro y hy
    change (0 ≤ psi y ∧ f x ≤ f y) ↔ 0 ≤ psi (C (H y))
    simpa only [hHpsi y, hbH y hy.1, sub_nonneg] using hCquad (H y)
  · intro y hy
    change (psi y = 0 ∧ f x ≤ f y) ↔ (psi (C (H y)) = 0 ∧ 0 ≤ b (C (H y)))
    simpa only [hHpsi y, hbH y hy.1, sub_nonneg] using hCold (H y)
  · intro y hy
    change (f y = f x ∧ 0 ≤ psi y) ↔ (psi (C (H y)) = 0 ∧ b (C (H y)) ≤ 0)
    simpa only [hHpsi y, hbH y hy.1, sub_eq_zero] using hCnew (H y)

end Geometry.SimplicialComplex
