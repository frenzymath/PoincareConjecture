import PoincareConjecture.Proofs.M04.ShiCoordinateConnection
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul









set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem shi_density_comp_fderiv {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {H : E → Y} {F : E → E} {z : E}
    (hH : DifferentiableAt ℝ H (F z)) (hF : DifferentiableAt ℝ F z) :
    HasFDerivAt (fun a => H (F a))
      ((fderiv ℝ H (F z)).comp (fderiv ℝ F z)) z := by
  exact HasFDerivAt.comp (𝕜 := ℝ) (F := E) (G := Y)
    (f := F) (g := H) z hH.hasFDerivAt hF.hasFDerivAt

set_option backward.isDefEq.respectTransparency false in
private theorem shi_density_fderiv_eval {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {B : E → E →L[ℝ] Y} {z : E} (hB : DifferentiableAt ℝ B z)
    (u v : E) :
    fderiv ℝ (fun a => B a v) z u = (fderiv ℝ B z u) v := by
  have h := hB.hasFDerivAt.clm_apply (hasFDerivAt_const v z)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    add_apply, zero_apply, map_zero, zero_add] using!
    congrArg (fun L : E →L[ℝ] Y => L u) h.fderiv

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem shi_density_pairing_fderiv [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {F U V : E → E} {z : E} (hz : F z ∈ c.target)
    (hF : DifferentiableAt ℝ F z) (hU : DifferentiableAt ℝ U z)
    (hV : DifferentiableAt ℝ V z) (v : E) :
    fderiv ℝ (fun a => shiChartMetric g c (F a) (U a) (V a)) z v =
      shiChartMetric g c (F z)
        (fderiv ℝ U z v + shiChartChristoffel D c (F z) (fderiv ℝ F z v) (U z))
        (V z) +
      shiChartMetric g c (F z) (U z)
        (fderiv ℝ V z v + shiChartChristoffel D c (F z) (fderiv ℝ F z v) (V z)) := by
  have hG : DifferentiableAt ℝ (shiChartMetric g c) (F z) :=
    ((shiChartMetric_smooth g hc hi).contDiffAt
      (c.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hGF : HasFDerivAt (fun a => shiChartMetric g c (F a))
      ((fderiv ℝ (shiChartMetric g c) (F z)).comp (fderiv ℝ F z)) z := by
    exact shi_density_comp_fderiv (Y := E →L[ℝ] E →L[ℝ] ℝ)
      (H := shiChartMetric g c) (F := F) hG hF
  have h := (hGF.clm_apply hU.hasFDerivAt).clm_apply hV.hasFDerivAt
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) h.fderiv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    add_apply] at hv
  rw [hv, shiChartMetric_derivative D hc hi hz]
  simp only [map_add, add_apply]
  ring

private theorem shi_density_fderiv [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {F W : E → E} {z : E} (hz : F z ∈ c.target)
    (hF : DifferentiableAt ℝ F z) (hW : DifferentiableAt ℝ W z) (v : E) :
    fderiv ℝ (fun a => shiChartMetric g c (F a) (W a) (W a)) z v =
      2 * shiChartMetric g c (F z)
        (fderiv ℝ W z v + shiChartChristoffel D c (F z) (W z) (fderiv ℝ F z v))
        (W z) := by
  rw [shi_density_pairing_fderiv D hc hi hz hF hW hW v,
    shiChartChristoffel_symm D hc hi hz (fderiv ℝ F z v) (W z),
    shiChartMetric_symm g c (F z) (W z)]
  ring

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem shiChart_density_second_jet [T2Space M] (D : LeviCivitaData g)
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {x : E} (hx : x ∈ c.target)
    {F W : E → E} (hF : ContDiffAt ℝ 2 F 0)
    (hW : ContDiffAt ℝ 2 W 0)
    {A P : E →L[ℝ] E} {T : E}
    (hF0 : F 0 = x) (hW0 : W 0 = T)
    (hF1 : fderiv ℝ F 0 = A)
    (hW1 : fderiv ℝ W 0 = P - (shiChartChristoffel D c x T).comp A)
    (hF2 : ∀ v, (fderiv ℝ (fderiv ℝ F) 0 v) v =
      -shiChartChristoffel D c x (A v) (A v))
    (hW2 : ∀ v, (fderiv ℝ (fderiv ℝ W) 0 v) v =
      -(fderiv ℝ (shiChartChristoffel D c) x T) (A v) (A v) -
        (2 : ℝ) • shiChartChristoffel D c x (fderiv ℝ W 0 v) (A v)) :
    let e : E → ℝ := fun z => shiChartMetric g c (F z) (W z) (W z)
    let S := mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm x
    ContDiffAt ℝ 2 e 0 ∧
      (∀ v, fderiv ℝ e 0 v = 2 * shiChartMetric g c x (P v) T) ∧
      ∀ v, (fderiv ℝ (fderiv ℝ e) 0 v) v =
        2 * (shiChartMetric g c x (P v) (P v) -
          D.curvatureTensor (c.symm x) (S T) (S (A v)) (S T) (S (A v))) := by
  let G := shiChartMetric g c
  let Γ := shiChartChristoffel D c
  let e : E → ℝ := fun z => G (F z) (W z) (W z)
  have hx0 : F 0 ∈ c.target := hF0 ▸ hx
  have hG : ContDiffAt ℝ 2 G (F 0) :=
    ((shiChartMetric_smooth g hc hi).contDiffAt
      (c.open_target.mem_nhds hx0)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he : ContDiffAt ℝ 2 e 0 :=
    ((hG.comp 0 hF).clm_apply hW).clm_apply hW
  have hFd : DifferentiableAt ℝ F 0 := hF.differentiableAt (by norm_num)
  have hWd : DifferentiableAt ℝ W 0 := hW.differentiableAt (by norm_num)
  have hFF : DifferentiableAt ℝ (fderiv ℝ F) 0 :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hWW : DifferentiableAt ℝ (fderiv ℝ W) 0 :=
    (hW.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hΓ : DifferentiableAt ℝ Γ (F 0) :=
    ((shiChartChristoffel_smooth D hc hi).contDiffAt
      (c.open_target.mem_nhds hx0)).differentiableAt (by simp)
  refine ⟨he, ?_, ?_⟩
  · intro v
    rw [shi_density_fderiv D hc hi hx0 hFd hWd v, hF0, hW0, hF1, hW1]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      sub_add_cancel]
  · intro v
    let K : E → E := fun z =>
      fderiv ℝ W z v + Γ (F z) (W z) (fderiv ℝ F z v)
    have hK0 : K 0 = P v := by
      dsimp only [K, Γ]
      rw [hF0, hW0, hF1, hW1]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        sub_add_cancel]
    have hFe := hFF.hasFDerivAt.clm_apply (hasFDerivAt_const v 0)
    have hWe := hWW.hasFDerivAt.clm_apply (hasFDerivAt_const v 0)
    have hΓF : HasFDerivAt (fun z => Γ (F z))
        ((fderiv ℝ Γ (F 0)).comp (fderiv ℝ F 0)) 0 := by
      exact shi_density_comp_fderiv (Y := E →L[ℝ] E →L[ℝ] E)
        (H := Γ) (F := F) hΓ hFd
    have hKd := hWe.add ((hΓF.clm_apply hWd.hasFDerivAt).clm_apply hFe)
    have hK : DifferentiableAt ℝ K 0 := hKd.differentiableAt
    have hDK : fderiv ℝ K 0 v =
        (fderiv ℝ (fderiv ℝ W) 0 v) v +
          (fderiv ℝ Γ (F 0) (fderiv ℝ F 0 v)) (W 0) (fderiv ℝ F 0 v) +
          Γ (F 0) (fderiv ℝ W 0 v) (fderiv ℝ F 0 v) +
          Γ (F 0) (W 0) ((fderiv ℝ (fderiv ℝ F) 0 v) v) := by
      have hv := congrArg (fun L : E →L[ℝ] E => L v) hKd.fderiv
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
        add_apply, zero_apply, map_zero, zero_add] at hv
      simpa only [K, Pi.add_apply, add_assoc, add_left_comm, add_comm] using! hv
    have hcov : fderiv ℝ K 0 v + Γ x (A v) (P v) =
        (fderiv ℝ Γ x (A v)) T (A v) - (fderiv ℝ Γ x T) (A v) (A v) +
          Γ x (A v) (Γ x T (A v)) - Γ x T (Γ x (A v) (A v)) := by
      have hP : fderiv ℝ W 0 v + Γ x T (A v) = P v := by
        rw [hW1]
        simp only [Γ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
          sub_add_cancel]
      rw [hDK, hF0, hW0, hF1, hF2 v, hW2 v, ← hP]
      simp only [map_add, map_neg, two_smul]
      rw [shiChartChristoffel_symm D hc hi hx (A v) (fderiv ℝ W 0 v)]
      abel

    have hfirst : (fun z => fderiv ℝ e z v) =ᶠ[𝓝 (0 : E)]
        (fun z => 2 * G (F z) (K z) (W z)) := by
      have htarget := hF.continuousAt.eventually_mem (c.open_target.mem_nhds hx0)
      filter_upwards [hF.eventually (by norm_num), hW.eventually (by norm_num),
        htarget] with z hFz hWz hz
      exact shi_density_fderiv D hc hi hz (hFz.differentiableAt (by norm_num))
        (hWz.differentiableAt (by norm_num)) v
    have hpair : DifferentiableAt ℝ (fun z => G (F z) (K z) (W z)) 0 :=
      (((hG.differentiableAt (by norm_num)).comp 0 hFd).clm_apply hK).clm_apply hWd
    have hEE : DifferentiableAt ℝ (fderiv ℝ e) 0 :=
      (he.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hsecond : (fderiv ℝ (fderiv ℝ e) 0 v) v =
        2 * (G x (P v) (P v) +
          G x (fderiv ℝ K 0 v + Γ x (A v) (P v)) T) := by
      calc
        _ = fderiv ℝ (fun z => fderiv ℝ e z v) 0 v :=
          (shi_density_fderiv_eval hEE v v).symm
        _ = fderiv ℝ (fun z => 2 * G (F z) (K z) (W z)) 0 v :=
          congrArg (fun L : E →L[ℝ] ℝ => L v) (hfirst.fderiv_eq (𝕜 := ℝ))
        _ = 2 * fderiv ℝ (fun z => G (F z) (K z) (W z)) 0 v := by
          rw [fderiv_const_mul hpair]
          rfl
        _ = _ := by
          rw [shi_density_pairing_fderiv D hc hi hx0 hFd hK hWd v,
            hF0, hW0, hF1, hK0,
            shiChartChristoffel_symm D hc hi hx (A v) T]
          have hP : fderiv ℝ W 0 v + Γ x T (A v) = P v := by
            rw [hW1]
            simp only [Γ, ContinuousLinearMap.sub_apply,
              ContinuousLinearMap.comp_apply, sub_add_cancel]
          rw [hP]
          ring
    let Q := (fderiv ℝ Γ x (A v)) T (A v) -
      (fderiv ℝ Γ x T) (A v) (A v) +
      Γ x (A v) (Γ x T (A v)) - Γ x T (Γ x (A v) (A v))
    let S : E →L[ℝ] TangentSpace (𝓡 n) (c.symm x) :=
      mfderiv 𝓘(ℝ, E) (𝓡 n) c.symm x
    have hcurv : G x Q T =
        -D.curvatureTensor (c.symm x) (S T) (S (A v)) (S T) (S (A v)) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      have hcoord : mvfderiv (𝓡 n) c (c.symm x)
          (D.curvature (c.symm x) (S (A v)) (S T) (S (A v))) = Q := by
        exact shiChart_curvature_formula D hc hi hx (A v) T (A v)
      have hSQ : S Q = D.curvature (c.symm x) (S (A v)) (S T) (S (A v)) := by
        calc
          S Q = S (mvfderiv (𝓡 n) c (c.symm x)
              (D.curvature (c.symm x) (S (A v)) (S T) (S (A v)))) :=
            congrArg S hcoord.symm
          _ = _ := shiChart_inverse_derivative_apply hc hi hx _
      change g.inner (c.symm x) (S Q) (S T) = _
      rw [hSQ]
      change D.curvatureTensor (c.symm x) (S (A v)) (S T) (S T) (S (A v)) = _
      exact curvatureTensor_swap_first D (c.symm x) (S T) (S (A v)) (S T) (S (A v))
    change (fderiv ℝ (fderiv ℝ e) 0 v) v = _
    rw [hsecond, hcov]
    change 2 * (G x (P v) (P v) + G x Q T) = _
    rw [hcurv]
    rfl


end PoincareConjecture.M04
