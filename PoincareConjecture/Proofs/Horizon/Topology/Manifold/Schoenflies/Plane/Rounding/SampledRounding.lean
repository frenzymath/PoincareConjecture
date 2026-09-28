import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.InscribedPolygon
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.RoundedPolygon










set_option autoImplicit false

open Function

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} [NeZero n]



theorem roundedPolygonParameter_inscribed_uniform (ρ : ℝ → ℝ) (γ : ℝ → E)
    (h : ℝ) (hγ : Periodic γ (h * (n : ℝ))) :
    roundedPolygonParameter ρ
      (inscribedPolygon γ (fun i : Fin (n + 1) => h * (i.val : ℝ))) =
        roundedVertexPath ρ (fun j : ℤ => γ (h * (j : ℝ))) := by
  unfold roundedPolygonParameter
  congr 1
  funext j
  change γ (h * ((polygonIntegerIndex n j).val : ℝ)) = γ (h * (j : ℝ))
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hcast : ((polygonIntegerIndex n j).val : ℝ) = ((j % (n : ℤ) : ℤ) : ℝ) := by
    change (((j % (n : ℤ)).toNat : ℕ) : ℝ) = _
    exact_mod_cast Int.toNat_of_nonneg (Int.emod_nonneg j hn)
  rw [hcast]
  have hdecomp : ((j % (n : ℤ) : ℤ) : ℝ) +
      ((j / (n : ℤ) : ℤ) : ℝ) * (n : ℝ) = (j : ℝ) := by
    exact_mod_cast Int.emod_add_ediv_mul j (n : ℤ)
  have heq : h * (j : ℝ) = h * ((j % (n : ℤ) : ℤ) : ℝ) +
      ((j / (n : ℤ) : ℤ) : ℝ) * (h * (n : ℝ)) := by
    rw [← hdecomp]
    ring
  rw [heq]
  exact ((hγ.int_mul (j / (n : ℤ))) _).symm



theorem periodic_rounded_uniform_sampling (ρ : ℝ → ℝ) (γ : ℝ → E)
    {h : ℝ} (hh : h ≠ 0) (hγ : Periodic γ (h * (n : ℝ))) :
    Periodic (fun t => roundedVertexPath ρ (fun j : ℤ => γ (h * (j : ℝ))) (t / h))
      (h * (n : ℝ)) := by
  have hp := periodic_roundedPolygonParameter ρ
    (inscribedPolygon γ (fun i : Fin (n + 1) => h * (i.val : ℝ)))
  rw [roundedPolygonParameter_inscribed_uniform ρ γ h hγ] at hp
  intro t
  change roundedVertexPath ρ (fun j : ℤ => γ (h * (j : ℝ))) ((t + h * (n : ℝ)) / h) = _
  rw [show (t + h * (n : ℝ)) / h = t / h + (n : ℝ) by field_simp]
  exact hp (t / h)

end Poincare.Manifold.Schoenflies.Plane
