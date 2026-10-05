import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.Coordinates.HessianTensorial
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.Coordinates.PreferredMetric

/-!
Adapted from Mapher `PoincareMT/Proofs/M10/FixedChartHessian.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# The actual Hessian in one fixed chart

Morgan-Tian Lemma 7.15 through Claim 7.18, pp. 157-160. The field
extension remains based at the same chart center while the evaluation
point varies. Tensoriality identifies the resulting expression with the
frozen pointwise Hessian.
-/

set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.SurgeryVolume.Measure

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The fixed coordinate extension is smooth at every point of that chart's source. -/
theorem preferredField_contMDiffAt_of_mem (q₀ : M) (v : TangentSpace (𝓡 n) q₀)
    {q : M} (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source) :
    ContMDiffAt (𝓡 n) (𝓡 n).tangent ∞
      (fun x ↦ (⟨x, FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x⟩ :
        TangentBundle (𝓡 n) M)) q := by
  let tr := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) q₀
  let v' : EuclideanSpace ℝ (Fin n) := v
  rw [tr.contMDiffAt_section_iff hq]
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (fun _ : M ↦ v') q := contMDiffAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [tr.open_baseSet.mem_nhds hq] with x hx
  rw [← tr.continuousLinearMapAt_apply_of_mem ℝ hx]
  exact preferredField_coordinates q₀ v hx

set_option backward.isDefEq.respectTransparency false in
/-- Differentiating twice on a fixed coordinate field gives the actual coordinate Hessian. -/
theorem fixedChart_second_scalar_derivative {f : M → ℝ} (q₀ : M) {q : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f q) (v : TangentSpace (𝓡 n) q₀) :
    mvfderiv (𝓡 n) (fun x ↦ mvfderiv (𝓡 n) f x
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) q
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v q) =
        fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 n) q₀).symm))
          (extChartAt (𝓡 n) q₀ q) v v := by
  let e := extChartAt (𝓡 n) q₀
  let l := f ∘ e.symm
  let v' : EuclideanSpace ℝ (Fin n) := v
  have hqe : q ∈ e.source := by simpa only [e, extChartAt_source] using hq
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) 2 e.symm (e q) :=
    (contMDiffOn_extChartAt_symm q₀).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds (e.map_source hqe))
  have hfl : ContDiffAt ℝ 2 l (e q) := by
    have hf' : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f (e.symm (e q)) := by
      simpa only [e.left_inv hqe] using hf
    exact (hf'.comp (e q) hi).contDiffAt
  have hDl := (hfl.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  let K := fun y ↦ fderiv ℝ l y v'
  have hK : DifferentiableAt ℝ K (e q) := hDl.clm_apply (differentiableAt_const v')
  have heq : (fun x ↦ mvfderiv (𝓡 n) f x
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x)) =ᶠ[𝓝 q] K ∘ e := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf,
      (chartAt (EuclideanSpace ℝ (Fin n)) q₀).open_source.mem_nhds hq] with x hx hchart
    exact (preferredField_scalar_derivative q₀ v hchart (hx.mdifferentiableAt two_ne_zero)).symm
  rw [mvfderiv_eq_of_eventuallyEq heq]
  have hchain := mfderiv_comp_apply q hK.mdifferentiableAt
    (mdifferentiableAt_extChartAt (I := 𝓡 n) hq)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v q)
  have hcoords : mfderiv (𝓡 n) (𝓡 n) e q
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v q) =
        (v : EuclideanSpace ℝ (Fin n)) := by
    change (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q₀) q)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v q) = _
    simpa only [TangentBundle.continuousLinearMapAt_trivializationAt hq] using!
      preferredField_coordinates q₀ v hq
  rw [hcoords, mfderiv_eq_fderiv] at hchain
  change mvfderiv (𝓡 n) (K ∘ e) q
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v q) = fderiv ℝ K (e q) v at hchain
  rw [hchain]
  have hEval := hDl.hasFDerivAt.clm_apply (hasFDerivAt_const v' (e q))
  have hEq := congrArg (fun D : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ D v')
    hEval.fderiv
  simpa only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply,
    K, l] using hEq

/-- The connection term relates the frozen Hessian to the fixed-chart second derivative. -/
theorem fixedChart_hessian_formula (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {f : M → ℝ} (q₀ : M) {q : M}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f q) (v : TangentSpace (𝓡 n) q₀) :
    let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
    fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 n) q₀).symm))
      (extChartAt (𝓡 n) q₀ q) v v =
        D.hessian f q (X q) (X q) + mvfderiv (𝓡 n) f q (D.connection X q (X q)) := by
  dsimp only
  rw [hessian_eq_of_extension g D hf _
    ((preferredField_contMDiffAt_of_mem q₀ v hq).mdifferentiableAt (by simp)),
    fixedChart_second_scalar_derivative q₀ hq hf v]
  ring

end PoincareMT.SurgeryVolume.Measure
