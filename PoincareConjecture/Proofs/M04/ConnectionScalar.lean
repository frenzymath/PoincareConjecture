import PoincareConjecture.Proofs.M04.KoszulPairing
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Function Topology

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem contMDiffAt_directional_derivative {f : M → ℝ}
    {X : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ mvfderiv (𝓡 n) f y (X y)) x := by
  have hϕ := hf.mfderiv_const (m := ∞) (by simp)
  have happ := ContMDiffAt.clm_apply_of_inCoordinates
    (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := ℝ)
    (B₁ := M) (B₂ := ℝ) (E₁ := fun y : M ↦ TangentSpace (𝓡 n) y)
    (E₂ := fun y : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) y)
    (b₁ := id) (b₂ := f) (m₀ := x)
    (ϕ := fun y ↦ mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f y)
    (v := X) hϕ hX hf
  have hsnd := contMDiff_snd_tangentBundle_modelSpace (n := ∞) ℝ 𝓘(ℝ, ℝ)
  exact (hsnd _).comp x happ

theorem contMDiffOn_directional_derivative {U : Set M} (hU : IsOpen U)
    {f : M → ℝ} {X : (x : M) → TangentSpace (𝓡 n) x}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ mvfderiv (𝓡 n) f y (X y)) U := by
  intro x hx
  exact (contMDiffAt_directional_derivative
    ((hf x hx).contMDiffAt (hU.mem_nhds hx))
    ((hX x hx).contMDiffAt (hU.mem_nhds hx))).contMDiffWithinAt

private theorem contMDiffOn_bracket {U : Set M} (hU : IsOpen U)
    {X Y : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (VectorField.mlieBracket (𝓡 n) X Y)) U := by
  intro x hx
  have hX' := (hX x hx).contMDiffAt (hU.mem_nhds hx)
  have hY' := (hY x hx).contMDiffAt (hU.mem_nhds hx)
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    apply IsManifold.of_le (n := (↑(⊤ : ℕ∞) : ℕ∞ω))
    simpa [minSmoothness_eq_infty] using
      (minSmoothness_monotone (𝕜 := ℝ)
        (by
          exact WithTop.coe_le_coe.mpr
            (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
  letI : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  exact (hX'.mlieBracket_vectorField (m := ⊤) (n := ⊤) hY' (by simp)).contMDiffWithinAt

theorem contMDiffOn_connection_pairing (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Z) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y ↦ g.inner y (D.connection Y y (X y)) (Z y)) U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h1 := contMDiffOn_directional_derivative hU (hY.inner_bundle hZ) hX
  have h2 := contMDiffOn_directional_derivative hU (hZ.inner_bundle hX) hY
  have h3 := contMDiffOn_directional_derivative hU (hX.inner_bundle hY) hZ
  have hb1 := (contMDiffOn_bracket hU hX hY).inner_bundle hZ
  have hb2 := (contMDiffOn_bracket hU hY hZ).inner_bundle hX
  have hb3 := (contMDiffOn_bracket hU hZ hX).inner_bundle hY
  have hs := (((((h1.add h2).sub h3).add hb1).sub hb2).add hb3).div_const (2 : ℝ)
  apply hs.congr
  intro y hy
  have hk := koszul_pairing D
    (((hX y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
    (((hY y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
    (((hZ y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
  have hinner : ∀ (q : M) (u v : TangentSpace (𝓡 n) q),
      g.inner q u v = inner ℝ u v := by
    intro q u v
    rfl
  rw [hinner]
  rw [hinner] at hk
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  simpa [mul_comm, hinner] using hk

end PoincareConjecture.M04
