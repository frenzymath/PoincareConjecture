import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.Graft

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

open Split

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1

def verticalCapLift (H : Real ≃ₘ[Real] Real) : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun p := vector (p 0) (p 1) (H (p 2))
  invFun p := vector (p 0) (p 1) (H.symm (p 2))
  left_inv p := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact H.symm_apply_apply _
  right_inv p := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact H.apply_symm_apply _
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
    · exact H.contDiff.comp (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
    · exact H.symm.contDiff.comp (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff

@[simp] theorem verticalCapLift_height (H : Real ≃ₘ[Real] Real) (p : E3) :
    verticalCapLift H p 2 = H (p 2) := rfl

theorem verticalCapLift_slice (H : Real ≃ₘ[Real] Real) (t : Real) (q : E2) :
    verticalCapLift H (sliceAtHeight t q) = sliceAtHeight (H t) q := rfl

theorem horizontalScaleLift_upper_slice
    (r : Real → Real) (hr : ContDiff Real ∞ r) (hpos : ∀ t, 0 < r t)
    {t : Real} (ht0 : 0 ≤ t) (ht : t ∈ Ioo (-1 : Real) 1)
    (hrt : r t = (Real.sqrt (1 - t ^ 2))⁻¹) :
    (horizontalScaleLift r hr hpos '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2})) ∩
        {p | p 2 = t} = sliceAtHeight t '' sphere (0 : E2) 1 := by
  let B := horizontalScaleLift r hr hpos
  have hrad : Real.sqrt (1 - t ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (sphereLatitude_radicand_pos ht)).ne'
  have hB (q : E2) : B (tangentPlanarLatitude t q) = sliceAtHeight t q := by
    ext i
    fin_cases i
    · change r t * (Real.sqrt (1 - t ^ 2) * q 0) = q 0
      rw [hrt, ← mul_assoc, inv_mul_cancel₀ hrad, one_mul]
    · change r t * (Real.sqrt (1 - t ^ 2) * q 1) = q 1
      rw [hrt, ← mul_assoc, inv_mul_cancel₀ hrad, one_mul]
    · rfl
  ext p
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hxt⟩
    have hx2 : x 2 = t := hxt
    obtain ⟨q, hq⟩ := (range_sphereLatitude ht).symm ▸
      (show x ∈ sphere (0 : E3) 1 ∩ {p | p 2 = t} from ⟨hx.1, hx2⟩)
    refine ⟨q, q.property, ?_⟩
    change sliceAtHeight t q = B x
    rw [← hq]
    exact (hB q).symm
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨tangentPlanarLatitude t q, ⟨sphereLatitude_mem_sphere ht ⟨q, hq⟩, ht0⟩,
      hB q⟩, rfl⟩

theorem verticalCapLift_preserves_upper_scale_cap
    (r : Real → Real) (hr : ContDiff Real ∞ r) (hpos : ∀ t, 0 < r t)
    {σ : Real} (hσ : 0 < σ) (hσ1 : σ < 1)
    (hrlocal : ∀ t ∈ Icc (0 : Real) σ, r t = (Real.sqrt (1 - t ^ 2))⁻¹)
    (L : Real ≃ₘ[Real] Real) (hLmono : StrictMono L) (hL0 : L 0 = 0)
    (hLfix : ∀ t, σ ≤ t → L t = t) :
    verticalCapLift L '' (horizontalScaleLift r hr hpos ''
      (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2})) =
        horizontalScaleLift r hr hpos '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2}) := by
  let S := horizontalScaleLift r hr hpos '' (sphere (0 : E3) 1 ∩ {p | 0 ≤ p 2})
  have hSpos (p : E3) (hp : p ∈ S) : 0 ≤ p 2 := by
    obtain ⟨q, hq, rfl⟩ := hp
    exact hq.2
  have hLnonneg (t : Real) : 0 ≤ L t ↔ 0 ≤ t := by
    conv_lhs => rw [← hL0]
    exact hLmono.le_iff_le
  have hSlice (p : E3) (hp : p 2 ∈ Icc (0 : Real) σ) :
      p ∈ S ↔ horizontal p ∈ sphere (0 : E2) 1 := by
    have he := horizontalScaleLift_upper_slice r hr hpos hp.1
      ⟨by linarith [hp.1], hp.2.trans_lt hσ1⟩ (hrlocal _ hp)
    constructor
    · intro hs
      obtain ⟨q, hq, hqp⟩ := (Set.ext_iff.mp he p).mp ⟨hs, rfl⟩
      have heq : q = horizontal p := by
        rw [← hqp]
        ext i
        fin_cases i <;> rfl
      exact heq ▸ hq
    · intro hs
      apply ((Set.ext_iff.mp he p).mpr ?_).1
      refine ⟨horizontal p, hs, ?_⟩
      ext i
      fin_cases i <;> rfl
  have hmem (p : E3) : verticalCapLift L p ∈ S ↔ p ∈ S := by
    by_cases hp0 : 0 ≤ p 2
    · by_cases hpσ : p 2 ≤ σ
      · have hLt : L (p 2) ∈ Icc (0 : Real) σ :=
          ⟨(hLnonneg _).mpr hp0, by rw [← hLfix σ le_rfl]; exact hLmono.monotone hpσ⟩
        rw [hSlice (verticalCapLift L p) hLt, hSlice p ⟨hp0, hpσ⟩]
        have hh : horizontal (verticalCapLift L p) = horizontal p := by
          ext i
          fin_cases i <;> rfl
        rw [hh]
      · have he : verticalCapLift L p = p := by
          ext i
          fin_cases i
          · rfl
          · rfl
          · exact hLfix _ (le_of_not_ge hpσ)
        rw [he]
    · constructor
      · intro hp
        exact (hp0 ((hLnonneg _).mp (hSpos _ hp))).elim
      · intro hp
        exact (hp0 (hSpos _ hp)).elim
  apply Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    exact (hmem q).mpr hq
  · intro p hp
    exact ⟨(verticalCapLift L).symm p,
      (hmem _).mp (by rw [Diffeomorph.apply_symm_apply]; exact hp),
        (verticalCapLift L).apply_symm_apply p⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps
