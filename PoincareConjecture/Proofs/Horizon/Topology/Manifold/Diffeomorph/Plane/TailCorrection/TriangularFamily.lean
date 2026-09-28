import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Euclidean.Triangular
import Mathlib.Geometry.Manifold.Instances.Real

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Manifold

namespace Poincare.Manifold.PlaneDiffeomorph

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

private theorem contDiff_pair
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => (!₂[f x, g x] : E₂)) := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact hf
  · exact hg

theorem exists_vertical_triangular_family
    (f : (ℝ × ℝ) × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hpos : ∀ q t, 0 < deriv (fun s => f (q, s)) t)
    (hbound : ∀ q, ∃ M : ℝ, ∀ t, |f (q, t) - t| ≤ M) :
    ∃ U : ℝ → Diffeomorph (𝓡 2) (𝓡 2) E₂ E₂ ∞,
      ContDiff ℝ ∞ (fun z : ℝ × E₂ => U z.1 z.2) ∧
      ∀ p z, U p z = !₂[z 0, f ((p, z 0), z 1)] := by
  have hbij (q : ℝ × ℝ) : Function.Bijective (fun t => f (q, t)) :=
    bijective_of_deriv_pos_of_bounded_displacement
      (hf.comp (contDiff_const.prodMk contDiff_id)).continuous (hpos q) (hbound q)
  obtain ⟨g, hg, hfg, hgf⟩ := exists_smooth_scalar_inverse hf hbij
    (fun q t => (hpos q t).ne')
  let A : ℝ × E₂ → E₂ := fun z => !₂[z.2 0, f ((z.1, z.2 0), z.2 1)]
  let B : ℝ × E₂ → E₂ := fun z => !₂[z.2 0, g ((z.1, z.2 0), z.2 1)]
  have hcoords : ContDiff ℝ ∞
      (fun z : ℝ × E₂ => ((z.1, z.2 0), z.2 1)) :=
    (contDiff_fst.prodMk
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_snd)).prodMk
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_snd)
  have hA : ContDiff ℝ ∞ A := contDiff_pair
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_snd) (hf.comp hcoords)
  have hB : ContDiff ℝ ∞ B := contDiff_pair
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_snd) (hg.comp hcoords)
  let U (p : ℝ) : Diffeomorph (𝓡 2) (𝓡 2) E₂ E₂ ∞ := {
    toEquiv := {
      toFun := fun z => A (p, z)
      invFun := fun z => B (p, z)
      left_inv := by
        intro z
        ext i
        fin_cases i <;> simp [A, B, hgf]
      right_inv := by
        intro z
        ext i
        fin_cases i <;> simp [A, B, hfg] }
    contMDiff_toFun := (hA.comp (contDiff_const.prodMk contDiff_id)).contMDiff
    contMDiff_invFun := (hB.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  exact ⟨U, hA, fun _ _ => rfl⟩

theorem exists_horizontal_triangular_family
    (f : (ℝ × ℝ) × ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hpos : ∀ q t, 0 < deriv (fun s => f (q, s)) t)
    (hbound : ∀ q, ∃ M : ℝ, ∀ t, |f (q, t) - t| ≤ M) :
    ∃ U : ℝ → Diffeomorph (𝓡 2) (𝓡 2) E₂ E₂ ∞,
      ContDiff ℝ ∞ (fun z : ℝ × E₂ => U z.1 z.2) ∧
      ∀ p z, U p z = !₂[f ((p, z 1), z 0), z 1] := by
  have hbij (q : ℝ × ℝ) : Function.Bijective (fun t => f (q, t)) :=
    bijective_of_deriv_pos_of_bounded_displacement
      (hf.comp (contDiff_const.prodMk contDiff_id)).continuous (hpos q) (hbound q)
  obtain ⟨g, hg, hfg, hgf⟩ := exists_smooth_scalar_inverse hf hbij
    (fun q t => (hpos q t).ne')
  let A : ℝ × E₂ → E₂ := fun z => !₂[f ((z.1, z.2 1), z.2 0), z.2 1]
  let B : ℝ × E₂ → E₂ := fun z => !₂[g ((z.1, z.2 1), z.2 0), z.2 1]
  have hcoords : ContDiff ℝ ∞
      (fun z : ℝ × E₂ => ((z.1, z.2 1), z.2 0)) :=
    (contDiff_fst.prodMk
      ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_snd)).prodMk
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_snd)
  have hA : ContDiff ℝ ∞ A := contDiff_pair (hf.comp hcoords)
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_snd)
  have hB : ContDiff ℝ ∞ B := contDiff_pair (hg.comp hcoords)
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_snd)
  let U (p : ℝ) : Diffeomorph (𝓡 2) (𝓡 2) E₂ E₂ ∞ := {
    toEquiv := {
      toFun := fun z => A (p, z)
      invFun := fun z => B (p, z)
      left_inv := by
        intro z
        ext i
        fin_cases i <;> simp [A, B, hgf]
      right_inv := by
        intro z
        ext i
        fin_cases i <;> simp [A, B, hfg] }
    contMDiff_toFun := (hA.comp (contDiff_const.prodMk contDiff_id)).contMDiff
    contMDiff_invFun := (hB.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  exact ⟨U, hA, fun _ _ => rfl⟩

end Poincare.Manifold.PlaneDiffeomorph
