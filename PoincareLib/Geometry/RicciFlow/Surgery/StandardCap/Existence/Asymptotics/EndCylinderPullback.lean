import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Asymptotics.EndCylinderMetric

/-!
# The auxiliary metric is the literal cylinder on the original end

Differentiating the actual height identity above height two identifies
the height covector on the genuine end-coordinate differential. The
frozen initial pullback then gives the exact time-dependent cylinder.
This is Proposition 12.7, pp. 298-299 and canonical-cylinder-model.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

/-- The actual height differential reads the axial component through the
actual supplied cylinder-coordinate derivative
(Proposition 12.7, pp. 298-299). -/
theorem endExhaustion_fderiv_coordinate (e : StandardCylindricalEnd g)
    {z : StandardCylinderSpace} (hz : 2 < z.2)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    fderiv ℝ (endExhaustion e) (e.coordinate z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate z v) = v.2 := by
  have heq : endExhaustion e ∘ e.coordinate =ᶠ[𝓝 z]
      (fun w : StandardCylinderSpace => w.2 + 1) := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioi).mem_nhds
      (show z ∈ univ ×ˢ Ioi (2 : ℝ) from ⟨mem_univ _, hz⟩)] with w hw
    dsimp only [Function.comp_apply]
    rw [endExhaustion_coordinate_of_two_le e hw.2.le, add_comm]
  have hc := (end_coordinate_contMDiffAt e (by linarith : 0 < z.2)).mdifferentiableAt
    (by simp)
  have hr := (endExhaustion_contMDiff e (e.coordinate z)).mdifferentiableAt (by simp)
  have hd := heq.mfderiv_eq (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
  rw [mfderiv_comp _ hr hc, mfderiv_eq_fderiv] at hd
  have hs : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun w : StandardCylinderSpace => w.2 + 1) z =
        ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ := by
    change mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun w : StandardCylinderSpace => w.2 + 1) z = _
    rw [mvfderiv_fun_add mdifferentiableAt_snd mdifferentiableAt_const,
      mvfderiv_const, add_zero]
    exact mfderiv_snd
  rw [hs] at hd
  exact congrArg (fun L => L v) hd

/-- The ambient coefficients pull back to the exact frozen cylinder
formula at every real parameter, on heights strictly above two
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderCoefficients_coordinate (e : StandardCylindricalEnd g) (s : ℝ)
    {z : StandardCylinderSpace} (hz : 2 < z.2)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    endCylinderCoefficients e s (e.coordinate z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate z w) =
        standardCylinderInner s z v w := by
  rw [endCylinderCoefficients_apply, e.metric_pullback z (by linarith),
    endExhaustion_fderiv_coordinate e hz, endExhaustion_fderiv_coordinate e hz]
  simp only [standardCylinderInner]
  ring

/-- Each genuine auxiliary metric is exactly the cylinder at its total
positive parameter when pulled back by the supplied end coordinates
(Proposition 12.7, pp. 298-299). -/
theorem endCylinderAuxMetric_coordinate (e : StandardCylindricalEnd g) (t : ℝ)
    {z : StandardCylinderSpace} (hz : 2 < z.2)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    (endCylinderAuxMetric e t).inner (e.coordinate z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate z w) =
        standardCylinderInner (endCylinderParameter t) z v w :=
  endCylinderCoefficients_coordinate e (endCylinderParameter t) hz v w

end PoincareMT.M34
