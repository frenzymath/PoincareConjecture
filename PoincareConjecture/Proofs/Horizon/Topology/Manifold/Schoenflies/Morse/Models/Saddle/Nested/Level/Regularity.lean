import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Equation



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

def height (p : S2) : Real := shear (3 / 10) p 2

theorem height_apply (p : S2) : height p =
    (p : E3) 2 + ((p : E3) 0)^2 + ((p : E3) 1)^2 + (3 / 10) * (p : E3) 0 :=
  shear_two _ _

private def heightDifferential (p : E3) : E3 →L[Real] Real :=
  EuclideanSpace.proj (𝕜 := Real) 2 + (2 * p 0) • EuclideanSpace.proj (𝕜 := Real) 0 +
    (2 * p 1) • EuclideanSpace.proj (𝕜 := Real) 1 +
    (3 / 10 : Real) • EuclideanSpace.proj (𝕜 := Real) 0

private theorem hasFDerivAt_height (p : E3) :
    HasFDerivAt (fun p : E3 => p 2 + (p 0)^2 + (p 1)^2 + (3 / 10) * p 0)
      (heightDifferential p) p := by
  convert! (((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).hasFDerivAt.add
    ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).hasFDerivAt.pow 2)).add
    ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).hasFDerivAt.pow 2)).add
    ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).hasFDerivAt.const_mul (3 / 10 : Real)) using 1
  simp [heightDifferential]

theorem height_contMDiff : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ height := by
  have hs : ContDiff Real ∞
      (fun p : E3 => p 2 + (p 0)^2 + (p 1)^2 + (3 / 10) * p 0) := by fun_prop
  rw [show height =
    (fun p : E3 => p 2 + (p 0)^2 + (p 1)^2 + (3 / 10) * p 0) ∘
      (Subtype.val : S2 → E3) from funext height_apply]
  exact hs.contMDiff.comp (contMDiff_coe_sphere (n := 2))

theorem critical_iff_tangent (p : S2) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 ↔
      ∀ w : E3, inner Real (p : E3) w = 0 →
        w 2 + 2 * (p : E3) 0 * w 0 + 2 * (p : E3) 1 * w 1 + (3 / 10) * w 0 = 0 := by
  let D := mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 → E3) p
  have hrange : D.range = (Real ∙ (p : E3))ᗮ := by
    convert! range_mvfderiv_subtypeVal p
  have hcomp : mfderiv (𝓡 2) 𝓘(Real, Real) height p =
      (heightDifferential p).comp D := by
    have heq : height =
        (fun p : E3 => p 2 + (p 0)^2 + (p 1)^2 + (3 / 10) * p 0) ∘ Subtype.val :=
      funext height_apply
    rw [heq, mfderiv_comp p (hasFDerivAt_height p).differentiableAt.mdifferentiableAt
      ((contMDiff_coe_sphere (n := 2) (m := ∞) p).mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv, (hasFDerivAt_height p).fderiv]
  rw [hcomp]
  constructor
  · intro hp w hw
    have hw' : w ∈ D.range := hrange ▸
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hw)
    obtain ⟨u, rfl⟩ := hw'
    exact congrArg (fun L : TangentSpace (𝓡 2) p →L[Real] Real => L u) hp
  · intro hw
    ext u
    have hmem : D u ∈ (Real ∙ (p : E3))ᗮ := hrange ▸ (show D u ∈ D.range from ⟨u, rfl⟩)
    exact hw (D u) (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem)

private theorem inner_three (p w : E3) :
    inner Real p w = p 0 * w 0 + p 1 * w 1 + p 2 * w 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem critical_point_coordinates {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0) :
    (p : E3) 1 = 0 ∧
      (p : E3) 0 * (2 * (p : E3) 2 - 1) + (3 / 10) * (p : E3) 2 = 0 := by
  have hy := (critical_iff_tangent p).mp hp (vector (-(p : E3) 1) ((p : E3) 0) 0)
    (by rw [inner_three]; simp; ring)
  have hx := (critical_iff_tangent p).mp hp (vector ((p : E3) 2) 0 (-(p : E3) 0))
    (by rw [inner_three]; simp; ring)
  simp only [vector_zero, vector_one, vector_two] at hy hx
  constructor <;> nlinarith


theorem height_one_regular (p : S2) (hp : height p = 1) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height p ≠ 0 := by
  intro hc
  obtain ⟨hy, hxcrit⟩ := critical_point_coordinates hc
  have hn : ((p : E3) 0)^2 + ((p : E3) 1)^2 + ((p : E3) 2)^2 = 1 := by
    have hn := EuclideanSpace.norm_sq_eq (p : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
    exact hn.symm
  rw [height_apply] at hp
  have hx : (p : E3) 0 = levelAbscissa ((p : E3) 2) := by
    dsimp [levelAbscissa]
    nlinarith
  have hrad : levelRadicand ((p : E3) 2) = 0 := by
    dsimp [levelRadicand]
    rw [← hx]
    rw [hy] at hn
    nlinarith
  have hzc : (p : E3) 2 * (200 * ((p : E3) 2)^2 - 300 * (p : E3) 2 + 109) = 0 := by
    rw [hx] at hxcrit
    dsimp [levelAbscissa] at hxcrit
    nlinarith
  have hz0 : (p : E3) 2 ≠ 0 := by
    intro hz
    simp [hz, levelRadicand, levelAbscissa] at hrad
  have hquad := (mul_eq_zero.mp hzc).resolve_left hz0
  rcases (levelRadicand_eq_zero_iff _).mp hrad with hz | hz | hz | hz
  · have hzneg : (p : E3) 2 < 0 := hz ▸ lowerRoot_bounds.2
    nlinarith [sq_nonneg ((p : E3) 2)]
  · rw [hz] at hquad
    norm_num at hquad
  · have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 19)
    rw [hz] at hquad
    dsimp [upperRoot] at hquad
    nlinarith
  · rw [hz] at hquad
    norm_num at hquad

end Poincare.Manifold.Schoenflies.Saddle.Nested
