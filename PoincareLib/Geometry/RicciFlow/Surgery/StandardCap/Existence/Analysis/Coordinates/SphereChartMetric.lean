import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.StereographicDifferential

/-!
# The induced sphere metric in its literal chosen charts

Mathlib's chosen chart at q is centered stereographic projection from
-q, with its actual selected orthogonal-complement basis. The generic
stereographic calculation gives its precise metric factor. The manifold
chain rule retains both actual derivatives, including that of the chart
inverse. This supplies Proposition 12.7, pp. 298-299; see
canonical-cylinder-model.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- The inverse of the literal chosen sphere chart is globally smooth,
since its stereographic target is the whole model space
(Proposition 12.7, pp. 298-299). -/
theorem contMDiff_sphere_chart_symm {m : ℕ∞ω} (q : sphere (0 : E) 1) :
    ContMDiff (𝓡 n) (𝓡 n) m (chartAt (EuclideanSpace ℝ (Fin n)) q).symm := by
  have ht : (chartAt (EuclideanSpace ℝ (Fin n)) q).target = univ :=
    stereographic'_target (-q)
  rw [← contMDiffOn_univ, ← ht]
  exact contMDiffOn_chart_symm

/-- The ordinary derivative of the included inverse sphere chart scales
inner products by its exact conformal coefficient
(Proposition 12.7, pp. 298-299). -/
theorem inner_fderiv_sphere_chart_symm (q : sphere (0 : E) 1)
    (x a b : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (fderiv ℝ (fun y => ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y : E)) x a)
      (fderiv ℝ (fun y => ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y : E)) x b) =
        16 / (‖x‖ ^ 2 + 4) ^ 2 * inner ℝ a b := by
  let v : sphere (0 : E) 1 := -q
  let U : (ℝ ∙ (v : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
  let L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] E :=
    (ℝ ∙ (v : E))ᗮ.subtypeₗᵢ.comp U.symm.toLinearIsometry
  have heq : (fun y => ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y : E)) =
      (fun y => stereoInvFunAux (v : E) (L y)) := by
    funext y
    change ((stereographic' n v).symm y : E) = stereoInvFunAux (v : E) (L y)
    simpa [stereoInvFunAux, smul_add, L, U] using stereographic'_symm_apply v y
  rw [heq]
  apply inner_fderiv_stereoInvFunAux_comp_linearIsometry L (v : E)
    (norm_eq_of_mem_sphere v)
  intro a
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (U.symm a).property

/-- The frozen induced sphere metric uses the actual inclusion and
inverse-chart manifold derivatives, with the same exact conformal factor
(Proposition 12.7, pp. 298-299). -/
theorem inner_mfderiv_sphere_chart_symm (q : sphere (0 : E) 1)
    (x a b : EuclideanSpace ℝ (Fin n)) :
    @inner ℝ E _
      (mfderiv (𝓡 n) 𝓘(ℝ, E) (fun z : sphere (0 : E) 1 => (z : E))
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x a))
      (mfderiv (𝓡 n) 𝓘(ℝ, E) (fun z : sphere (0 : E) 1 => (z : E))
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x b)) =
      16 / (‖x‖ ^ 2 + 4) ^ 2 * inner ℝ a b := by
  have he (a : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) 𝓘(ℝ, E) (fun z : sphere (0 : E) 1 => (z : E))
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x a) =
      fderiv ℝ (fun y => ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y : E)) x a := by
    have hc := mfderiv_comp x
      ((contMDiff_coe_sphere (n := n) (m := ∞)
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x)).mdifferentiableAt (by simp))
      ((contMDiff_sphere_chart_symm (m := ∞) q x).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hc
    exact (congrArg (fun A => A a) hc).symm
  rw [he, he]
  exact inner_fderiv_sphere_chart_symm q x a b
