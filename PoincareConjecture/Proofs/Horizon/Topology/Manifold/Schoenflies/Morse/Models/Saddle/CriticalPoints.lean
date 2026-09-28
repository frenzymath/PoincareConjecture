import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LowerCaps



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2+1) := ⟨by simp⟩


def height (p : S2) : Real := shear p 2

theorem height_apply (p : S2) : height p = (p : E3) 2 - ((p : E3) 0)^2 := shear_two p

private def heightDifferential (p : E3) : E3 →L[Real] Real :=
  EuclideanSpace.proj (𝕜 := Real) 2 - (2*p 0) • EuclideanSpace.proj (𝕜 := Real) 0

private theorem hasFDerivAt_height (p : E3) :
    HasFDerivAt (fun p : E3 => p 2 - (p 0)^2) (heightDifferential p) p := by
  convert! (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).hasFDerivAt.sub
    ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).hasFDerivAt.pow 2) using 1
  simp [heightDifferential]

theorem height_contMDiff : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ height := by
  have hs : ContDiff Real ∞ (fun p : E3 => p 2 - (p 0)^2) := by fun_prop
  rw [show height = (fun p : E3 => p 2 - (p 0)^2) ∘ (Subtype.val : S2 → E3) from
    funext height_apply]
  exact hs.contMDiff.comp (contMDiff_coe_sphere (n := 2))

private theorem critical_iff_tangent (p : S2) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 ↔
      ∀ w : E3, inner Real (p : E3) w = 0 → w 2 - 2*(p : E3) 0*w 0 = 0 := by
  let D := mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3) p
  have hrange : D.range = (Real ∙ (p : E3))ᗮ := by
    convert! range_mvfderiv_subtypeVal p
  have hcomp : mfderiv (𝓡 2) 𝓘(Real, Real) height p =
      (heightDifferential p).comp D := by
    have heq : height = (fun p : E3 => p 2 - (p 0)^2) ∘ Subtype.val := funext height_apply
    rw [heq, mfderiv_comp p (hasFDerivAt_height p).differentiableAt.mdifferentiableAt
      ((contMDiff_coe_sphere (n := 2) (m := ∞) p).mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv, (hasFDerivAt_height p).fderiv]
  rw [hcomp]
  constructor
  · intro hz w hw
    have hw' : w ∈ D.range := hrange ▸
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hw)
    obtain ⟨u, rfl⟩ := hw'
    exact congrArg (fun L : TangentSpace (𝓡 2) p →L[Real] Real => L u) hz
  · intro hw
    ext u
    have hmem : D u ∈ (Real ∙ (p : E3))ᗮ := hrange ▸ (show D u ∈ D.range from ⟨u, rfl⟩)
    exact hw (D u) (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem)

private theorem inner_three (p w : E3) :
    inner Real p w = p 0*w 0 + p 1*w 1 + p 2*w 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]


theorem height_critical_iff (p : S2) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 ↔
      (p : E3) 1 = 0 ∧ ((p : E3) 0 = 0 ∨ (p : E3) 2 = -1/2) := by
  rw [critical_iff_tangent]
  constructor
  · intro hp
    have hy := hp (vector 0 ((p : E3) 2) (-(p : E3) 1))
      (by rw [inner_three]; simp; ring)
    have hx := hp (vector ((p : E3) 2) 0 (-(p : E3) 0))
      (by rw [inner_three]; simp; ring)
    have hy0 : (p : E3) 1 = 0 := by simpa using hy
    refine ⟨hy0, ?_⟩
    by_cases hx0 : (p : E3) 0 = 0
    · exact Or.inl hx0
    · right
      have hmul : (p : E3) 0 * (2*(p : E3) 2 + 1) = 0 := by
        simp only [vector_zero, vector_two] at hx
        nlinarith
      have := (mul_eq_zero.mp hmul).resolve_left hx0
      linarith
  · rintro ⟨hy, hx | hz⟩ w hw
    · have hn : ((p : E3) 2)^2 = 1 := by
        have hn := EuclideanSpace.norm_sq_eq (p : E3)
        simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hx, hy] at hn
        exact hn.symm
      have hz : (p : E3) 2 ≠ 0 := by nlinarith
      rw [inner_three, hx, hy] at hw
      have hw2 : w 2 = 0 := (mul_eq_zero.mp (by simpa using hw)).resolve_left hz
      simp [hx, hw2]
    · rw [inner_three, hy, hz] at hw
      nlinarith



theorem critical_height_values {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0) :
    height p = -5/4 ∨ height p = -1 ∨ height p = 1 := by
  obtain ⟨hy, hx | hz⟩ := (height_critical_iff p).mp hp
  · have hn : ((p : E3) 2)^2 = 1 := by
      have hn := EuclideanSpace.norm_sq_eq (p : E3)
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hx, hy] at hn
      exact hn.symm
    rcases sq_eq_one_iff.mp hn with h | h
    · exact Or.inr (Or.inr (by rw [height_apply, hx, h]; norm_num))
    · exact Or.inr (Or.inl (by rw [height_apply, hx, h]; norm_num))
  · left
    have hn := EuclideanSpace.norm_sq_eq (p : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hy, hz] at hn
    rw [height_apply, hz]
    nlinarith


theorem cutting_heights_regular (p : S2)
    (hp : height p = -9/8 ∨ height p = 1/2) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height p ≠ 0 := by
  intro hc
  rcases critical_height_values hc with h | h | h <;>
    rcases hp with hp | hp <;> linarith


def saddlePoint : S2 := ⟨-EuclideanSpace.single 2 1, by simp⟩

theorem height_saddlePoint : height saddlePoint = -1 := by
  rw [height_apply]
  simp [saddlePoint]

theorem saddlePoint_critical :
    mfderiv (𝓡 2) 𝓘(Real, Real) height saddlePoint = 0 := by
  rw [height_critical_iff]
  simp [saddlePoint]


theorem critical_in_band_iff (p : S2) (hp : height p ∈ Icc (-9/8 : Real) (1/2)) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 ↔ p = saddlePoint := by
  constructor
  · intro hc
    obtain ⟨hy, hx | hz⟩ := (height_critical_iff p).mp hc
    · have hn : ((p : E3) 2)^2 = 1 := by
        have hn := EuclideanSpace.norm_sq_eq (p : E3)
        simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hx, hy] at hn
        exact hn.symm
      have hheight : height p = (p : E3) 2 := by rw [height_apply, hx]; ring
      have hz : (p : E3) 2 = -1 := by rw [hheight] at hp; nlinarith [hp.2]
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [saddlePoint, hx, hy, hz]
    · have hheight : height p = -5/4 := by
        have hn := EuclideanSpace.norm_sq_eq (p : E3)
        simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hy, hz] at hn
        rw [height_apply, hz]
        nlinarith
      rw [hheight] at hp
      norm_num at hp
  · rintro rfl
    exact saddlePoint_critical

end Poincare.Manifold.Schoenflies.Saddle
