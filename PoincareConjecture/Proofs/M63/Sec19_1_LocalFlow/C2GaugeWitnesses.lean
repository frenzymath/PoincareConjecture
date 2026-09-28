import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ParabolicGaugeGeometry
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem spatial_velocity_contMDiff_of_c2 {gamma : ℝ → M}
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma) :
    ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun x => (⟨gamma x, curveVelocity (n := n) gamma x⟩ :
        TangentBundle (𝓡 n) M)) := by
  have hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent 1
      (fun x : ℝ => (⟨x, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    exact contDiff_const
  exact (hgamma.contMDiff_tangentMap (m := 1) (by norm_num)).comp hone



theorem speed_contDiff_of_c2 (F : RicciFlow n M (Set.Icc a b))
    (q : ℝ → ℝ → M) {t : ℝ}
    (hspace : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun x => q x t))
    (himm : ∀ x, curveVelocity (n := n) (fun y => q y t) x ≠ 0) :
    ContDiff ℝ 1 (curveSpeed F q t) := by
  have hX := spatial_velocity_contMDiff_of_c2 hspace
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => q x t) :=
    hspace.of_le (by norm_num)
  have hpair : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod 𝓘(ℝ, ℝ)) 1
      (fun x => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (q x t)
        ((F.metric t).inner (q x t) (curveVelocity (fun y => q y t) x)
          (curveVelocity (fun y => q y t) x))) :=
    (((F.metric t).contMDiff.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).comp
      hgamma).clm_bundle_apply₂ hX hX
  have hsq : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1
      (fun x => (F.metric t).inner (q x t) (curveVelocity (fun y => q y t) x)
        (curveVelocity (fun y => q y t) x)) := by
    intro x
    exact (Bundle.contMDiffAt_totalSpace.mp (hpair x)).2
  exact hsq.contDiff.sqrt fun x => ((F.metric t).pos _ _ (himm x)).ne'




theorem unitTangent_contMDiff_of_c2 (F : RicciFlow n M (Set.Icc a b))
    (q : ℝ → ℝ → M) {t : ℝ}
    (hspace : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun x => q x t))
    (himm : ∀ x, curveVelocity (n := n) (fun y => q y t) x ≠ 0) :
    ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun x => (⟨q x t, spatialUnitTangent F q t x⟩ : TangentBundle (𝓡 n) M)) := by
  have hX := spatial_velocity_contMDiff_of_c2 hspace
  have hvpos (x : ℝ) : 0 < curveSpeed F q t x :=
    Real.sqrt_pos.mpr ((F.metric t).pos _ _ (himm x))
  have hv : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun x => (curveSpeed F q t x)⁻¹) :=
    ((speed_contDiff_of_c2 F q hspace himm).inv (fun x => (hvpos x).ne')).contMDiff
  intro x
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨(hspace.of_le (by norm_num) x), ?_⟩
  have hcoord := (hv x).smul (Bundle.contMDiffAt_totalSpace.mp (hX x)).2
  apply hcoord.congr_of_eventuallyEq
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (q x t)
  have hnear : ∀ᶠ y in 𝓝 x, q y t ∈ e.baseSet :=
    hspace.continuous.continuousAt
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (q x t)))
  filter_upwards [hnear] with y hy
  change (e ⟨q y t, (curveSpeed F q t y)⁻¹ • curveVelocity (fun z => q z t) y⟩).2 =
    (curveSpeed F q t y)⁻¹ • (e ⟨q y t, curveVelocity (fun z => q z t) y⟩).2
  simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hy] using
    (e.continuousLinearMapAt ℝ (q y t)).map_smul
      (curveSpeed F q t y)⁻¹ (curveVelocity (fun z => q z t) y)




theorem normal_equation_of_c2_parabolic_gauge
    (F : RicciFlow n M (Set.Icc a b)) (q : ℝ → ℝ → M) (psi : ℝ → ℝ → ℝ)
    {t x : ℝ}
    (hq : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) (𝓡 n)
      (fun z : ℝ × ℝ => q z.1 z.2) (psi x t, t))
    (hspace : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => q y t))
    (himm : ∀ y, curveVelocity (n := n) (fun z => q z t) y ≠ 0)
    (hlabels : Differentiable ℝ (fun y => psi y t))
    (hpos : ∀ y, 0 < deriv (fun z => psi z t) y)
    (hgauge : curveVelocity (n := n) (fun r => q (psi x t) r) t =
      (curveSpeed F q t (psi x t) ^ 2)⁻¹ •
        rampHorizontalCovariantDerivative (F.connection t) (fun y => q y t)
          (fun y => curveVelocity (n := n) (fun z => q z t) y) (psi x t))
    (hode : HasDerivAt (psi x)
      (-(deriv (curveSpeed F q t) (psi x t) / curveSpeed F q t (psi x t) ^ 3)) t) :
    curveVelocity (n := n) (fun r => q (psi x r) r) t =
      m62CurvatureVector F (fun y r => q (psi y r) r) t x := by
  exact normal_equation_of_parabolic_gauge F q psi hq
    (hspace.mdifferentiable (by norm_num))
    ((unitTangent_contMDiff_of_c2 F q hspace himm _).mdifferentiableAt (by simp))
    hlabels hpos ((spatial_velocity_contMDiff_of_c2 hspace _).mdifferentiableAt (by simp))
    ((speed_contDiff_of_c2 F q hspace himm).differentiable (by simp) _).hasDerivAt
    (Real.sqrt_pos.mpr ((F.metric t).pos _ _ (himm (psi x t)))).ne' hgauge hode

end PoincareConjecture.M63
