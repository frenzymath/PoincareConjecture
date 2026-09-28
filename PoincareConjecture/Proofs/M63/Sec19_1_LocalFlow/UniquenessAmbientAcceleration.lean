import PoincareConjecture.Proofs.M63.Mathlib.C2SecondDerivComposition
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CoordinateGaugeEquation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddingHessianVector
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2GaugeWitnesses











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "W" => EuclideanSpace ℝ ι





theorem secondDeriv_embedding_eq_hessian_add_acceleration
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma) (x : ℝ) :
    deriv (deriv (fun y => e (gamma y))) x =
      HAdd.hAdd (α := W) (β := W) (γ := W)
        (coordinateHessian D e (gamma x) (curveVelocity gamma x) (curveVelocity gamma x))
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma x)
          (rampHorizontalCovariantDerivative D gamma (fun y => curveVelocity gamma y) x)) := by
  let p := gamma x
  let c := chartAt E p
  let U := gamma ⁻¹' c.source
  let z : ℝ → E := fun y => c (gamma y)
  let f : E → W := e ∘ c.symm
  have hU : IsOpen U := c.open_source.preimage hgamma.continuous
  have hx : x ∈ U := mem_chart_source E p
  have hmap : MapsTo gamma U c.source := fun _ hy => hy
  have hz : ContDiffOn ℝ 2 z U :=
    (contMDiffOn_chart.comp hgamma.contMDiffOn hmap).contDiffOn
  have hf : ContDiffOn ℝ ∞ f c.target :=
    (he.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 n) (x := p))).contDiffOn
  have htarget : z x ∈ c.target := c.map_source hx
  have hbase : c.symm (z x) = gamma x := c.left_inv hx
  have hvel : chartVectorField p (deriv z x) (gamma x) = curveVelocity gamma x :=
    chartVectorField_coordinate_velocity p gamma x (deriv z x) hx
      ((hgamma x).mdifferentiableAt (by norm_num))
      (((hz.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt)
  have hacc := pullback_velocity_eq_chart_acceleration D p hU hgamma.contMDiffOn hmap hx
  have hhess := coordinateHessian_eq_chart D he p (gamma x) hx (deriv z x) (deriv z x)
  dsimp only at hacc hhess
  rw [hvel] at hhess
  have hpush (v : E) :
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma x) (chartVectorField p v (gamma x)) =
        fderiv ℝ f (z x) v := by
    have hchain := mfderiv_comp (z x) (he.mdifferentiable (by simp)).mdifferentiableAt
      ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt_symm htarget)
    rw [mfderiv_eq_fderiv] at hchain
    have hv := congrArg (fun L : E →L[ℝ] W => L v) hchain
    change fderiv ℝ f (z x) v =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c.symm (z x))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (z x) v) at hv
    rw [← chartVectorField_at_inverse p v (z x) htarget, hbase] at hv
    exact hv.symm
  have hlocal : (fun y => e (gamma y)) =ᶠ[𝓝 x] (fun y => f (z y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    dsimp only [f, z, Function.comp_def]
    rw [c.left_inv hy]
  have hsecond := secondDeriv_comp_of_contDiffAt_two f z x
    ((hf.contDiffAt (c.open_target.mem_nhds htarget)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hz.contDiffAt (hU.mem_nhds hx))
  rw [hlocal.deriv.deriv_eq, hsecond, hhess, hacc, hpush, map_add]
  abel

variable {a b : ℝ}





theorem embedded_curvature_eq_acceleration_sub_tangent
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) (q : ℝ → ℝ → M) {t : ℝ}
    (hspace : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => q y t))
    (himm : ∀ y, curveVelocity (n := n) (fun z => q z t) y ≠ 0) (x : ℝ) :
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t) (m62CurvatureVector F q t x) =
      (curveSpeed F q t x ^ 2)⁻¹ •
          (deriv (deriv (fun y => e (q y t))) x -
            coordinateHessian (F.connection t) e (q x t)
              (curveVelocity (fun y => q y t) x) (curveVelocity (fun y => q y t) x)) -
        (deriv (curveSpeed F q t) x / curveSpeed F q t x ^ 3) •
          deriv (fun y => e (q y t)) x := by
  have hX := ((spatial_velocity_contMDiff_of_c2 hspace) x).mdifferentiableAt (by simp)
  have hv := ((speed_contDiff_of_c2 F q hspace himm).differentiable (by simp) x).hasDerivAt
  have hne : curveSpeed F q t x ≠ 0 :=
    (Real.sqrt_pos.mpr ((F.metric t).pos _ _ (himm x))).ne'
  have hacc := secondDeriv_embedding_eq_hessian_add_acceleration (F.connection t) he hspace x
  have hpushacc :
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t)
          (rampHorizontalCovariantDerivative (F.connection t) (fun y => q y t)
            (fun y => curveVelocity (fun z => q z t) y) x) =
        deriv (deriv (fun y => e (q y t))) x -
          coordinateHessian (F.connection t) e (q x t)
            (curveVelocity (fun y => q y t) x) (curveVelocity (fun y => q y t) x) := by
    rw [hacc]
    abel
  have hpushvel : mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t)
      (curveVelocity (fun y => q y t) x) = deriv (fun y => e (q y t)) x := by
    have hchain : fderiv ℝ (fun y => e (q y t)) x =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => q y t) x) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp x (he.mdifferentiable (by simp)).mdifferentiableAt
        ((hspace x).mdifferentiableAt (by norm_num))
    exact (congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain).symm
  rw [curvatureVector_eq_acceleration_sub_tangent F q hX hv hne,
    map_sub, map_smul, map_smul, hpushacc, hpushvel]

end PoincareConjecture.M63
