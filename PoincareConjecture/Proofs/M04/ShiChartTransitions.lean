import PoincareConjecture.Proofs.M04.ShiCoordinateConnection

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem shiChartTransition_smooth
    {cold cnew : OpenPartialHomeomorph M E}
    (hoi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cold.symm cold.target)
    (hn : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cnew cnew.source) :
    ContDiffOn ℝ ∞ (cnew ∘ cold.symm)
      (cold.target ∩ cold.symm ⁻¹' cnew.source) := by
  exact (hn.comp (hoi.mono inter_subset_left) (fun _ h => h.2)).contDiffOn

set_option backward.isDefEq.respectTransparency false in
theorem shiChartTransition_fderiv
    {cold cnew : OpenPartialHomeomorph M E}
    (hoi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cold.symm cold.target)
    (hn : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cnew cnew.source)
    {z : E} (hz : z ∈ cold.target) (hy : cold.symm z ∈ cnew.source) :
    fderiv ℝ (cnew ∘ cold.symm) z =
      (mvfderiv (𝓡 n) cnew (cold.symm z)).comp
        (mfderiv 𝓘(ℝ, E) (𝓡 n) cold.symm z) := by
  have h := mfderiv_comp z
    ((hn.contMDiffAt (cnew.open_source.mem_nhds hy)).mdifferentiableAt (by simp))
    ((hoi.contMDiffAt (cold.open_target.mem_nhds hz)).mdifferentiableAt (by simp))
  simpa only [mfderiv_eq_fderiv] using! h

set_option backward.isDefEq.respectTransparency false in
theorem shiChartTransition_field
    {cold cnew : OpenPartialHomeomorph M E}
    (ho : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cold cold.source)
    (hoi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cold.symm cold.target)
    (hn : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cnew cnew.source)
    (hni : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cnew.symm cnew.target)
    {z : E} (hz : z ∈ cold.target) (hy : cold.symm z ∈ cnew.source) (v : E) :
    shiChartField cnew (fderiv ℝ (cnew ∘ cold.symm) z v) (cold.symm z) =
      shiChartField cold v (cold.symm z) := by
  apply (shiChart_mfderiv_isInvertible hn hni hy).injective
  change mvfderiv (𝓡 n) cnew (cold.symm z)
      (shiChartField cnew (fderiv ℝ (cnew ∘ cold.symm) z v) (cold.symm z)) =
    mvfderiv (𝓡 n) cnew (cold.symm z) (shiChartField cold v (cold.symm z))
  rw [shiChartField_duality hn hni hy, shiChartField_at_inverse ho hoi hz,
    shiChartTransition_fderiv hoi hn hz hy, ContinuousLinearMap.comp_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem shiChartTransition_vector
    {cold cnew : OpenPartialHomeomorph M E}
    (ho : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cold cold.source)
    (hoi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cold.symm cold.target)
    (hn : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cnew cnew.source)
    {z : E} (hz : z ∈ cold.target) (hy : cold.symm z ∈ cnew.source) (v : E) :
    shiChartVector cnew (shiChartField cold v) ((cnew ∘ cold.symm) z) =
      fderiv ℝ (cnew ∘ cold.symm) z v := by
  dsimp only [shiChartVector, Function.comp_apply]
  erw [cnew.left_inv hy, shiChartField_at_inverse ho hoi hz,
    shiChartTransition_fderiv hoi hn hz hy, ContinuousLinearMap.comp_apply]

set_option backward.isDefEq.respectTransparency false in
theorem shiChartTransition_secondJet [T2Space M] (D : LeviCivitaData g)
    {cold cnew : OpenPartialHomeomorph M E}
    (ho : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cold cold.source)
    (hoi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cold.symm cold.target)
    (hn : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cnew cnew.source)
    (hni : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cnew.symm cnew.target)
    {z : E} (hz : z ∈ cold.target) (hy : cold.symm z ∈ cnew.source) (u v : E) :
    fderiv ℝ (fderiv ℝ (cnew ∘ cold.symm)) z u v +
        shiChartChristoffel D cnew ((cnew ∘ cold.symm) z)
          (fderiv ℝ (cnew ∘ cold.symm) z u)
          (fderiv ℝ (cnew ∘ cold.symm) z v) =
      fderiv ℝ (cnew ∘ cold.symm) z (shiChartChristoffel D cold z u v) := by
  let tau : E → E := cnew ∘ cold.symm
  let U : Set M := cold.source ∩ cnew.source
  let W : Set E := cold.target ∩ cold.symm ⁻¹' cnew.source
  let Y := shiChartField cold v
  let V := shiChartVector cnew Y
  have hU : IsOpen U := cold.open_source.inter cnew.open_source
  have hW : IsOpen W := cold.isOpen_inter_preimage_symm cnew.open_source
  have hzW : z ∈ W := ⟨hz, hy⟩
  have hyU : cold.symm z ∈ U := ⟨cold.map_target hz, hy⟩
  have hw : tau z ∈ cnew.target := cnew.map_source hy
  have hback : cnew.symm (tau z) = cold.symm z := cnew.left_inv hy
  have hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% Y) U :=
    (shiChartField_smooth ho hoi v).mono inter_subset_left
  have hYw : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% Y) (cnew.symm (tau z)) := by
    rw [hback]
    exact hY.contMDiffAt (hU.mem_nhds hyU)
  have hV : ContDiffAt ℝ ∞ V (tau z) := shiChartVector_smoothAt hn hni hw hYw
  have hTau : ContDiffAt ℝ ∞ tau z :=
    (shiChartTransition_smooth hoi hn).contDiffAt (hW.mem_nhds hzW)
  have hGerm : (V ∘ tau) =ᶠ[𝓝 z] (fun d => fderiv ℝ tau d v) := by
    filter_upwards [hW.mem_nhds hzW] with d hd
    exact shiChartTransition_vector ho hoi hn hd.1 hd.2 v
  have hD := (hTau.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hEval := (hD.hasFDerivAt.clm_apply (hasFDerivAt_const v z)).fderiv
  have hComp := ((hV.differentiableAt (by simp)).hasFDerivAt.comp z
    (hTau.differentiableAt (by simp)).hasFDerivAt).fderiv
  have hDerivative :
      fderiv ℝ V (tau z) (fderiv ℝ tau z u) =
        fderiv ℝ (fderiv ℝ tau) z u v := by
    calc
      _ = fderiv ℝ (V ∘ tau) z u :=
        (congrArg (fun A : E →L[ℝ] E => A u) hComp).symm
      _ = fderiv ℝ (fun d => fderiv ℝ tau d v) z u :=
        congrArg (fun A : E →L[ℝ] E => A u) (hGerm.fderiv_eq (𝕜 := ℝ))
      _ = _ := by
        simpa only [map_zero, add_zero, ContinuousLinearMap.zero_apply,
          ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] using!
          congrArg (fun A : E →L[ℝ] E => A u) hEval
  have hValue : V (tau z) = fderiv ℝ tau z v := hGerm.eq_of_nhds
  have hconn :
      mvfderiv (𝓡 n) cnew (cold.symm z)
        (D.connection Y (cold.symm z) (shiChartField cold u (cold.symm z))) =
      fderiv ℝ V (tau z) (fderiv ℝ tau z u) +
        shiChartChristoffel D cnew (tau z) (fderiv ℝ tau z u) (V (tau z)) := by
    have h := shiChart_connection_formula D hn hni hU inter_subset_right hY hw
      (by simpa only [hback] using hyU) (fderiv ℝ tau z u)
    rw [← shiChartField_at_inverse hn hni hw] at h
    erw [hback, shiChartTransition_field ho hoi hn hni hz hy] at h
    exact h
  have hRight :
      fderiv ℝ tau z (shiChartChristoffel D cold z u v) =
      mvfderiv (𝓡 n) cnew (cold.symm z)
        (D.connection Y (cold.symm z) (shiChartField cold u (cold.symm z))) := by
    rw [shiChartChristoffel_connection D ho hoi hz,
      shiChartTransition_fderiv hoi hn hz hy, ContinuousLinearMap.comp_apply]
    have hInv := shiChart_inverse_derivative_apply ho hoi hz
      (D.connection (shiChartField cold v) (cold.symm z)
        (mfderiv 𝓘(ℝ, E) (𝓡 n) cold.symm z u))
    simpa only [Y, shiChartField_at_inverse ho hoi hz] using!
      congrArg (fun a : TangentSpace (𝓡 n) (cold.symm z) =>
        mvfderiv (𝓡 n) cnew (cold.symm z) a) hInv
  rw [hDerivative, hValue] at hconn
  exact hconn.symm.trans hRight.symm

end PoincareConjecture.M04
