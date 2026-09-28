import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.CurrentMollification
import PoincareConjecture.Proofs.M60.Mathlib.UniformizationPrimitives









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology Manifold ContDiff Convolution

namespace PoincareConjecture.M64

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "b" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)



def coordinateCurrentForm (J : Fin 2 → Plane → ℝ) (p : Plane) : Plane →L[ℝ] ℝ :=
  J 0 p • EuclideanSpace.proj 0 + J 1 p • EuclideanSpace.proj 1



theorem coordinateCurrentForm_apply (J : Fin 2 → Plane → ℝ) (p v : Plane) :
    coordinateCurrentForm J p v = J 0 p * v 0 + J 1 p * v 1 := rfl



theorem coordinateCurrentForm_contDiff (J : Fin 2 → Plane → ℝ)
    (hJ : ∀ i, ContDiff ℝ ∞ (J i)) : ContDiff ℝ ∞ (coordinateCurrentForm J) :=
  ((hJ 0).smul contDiff_const).add ((hJ 1).smul contDiff_const)



theorem coordinateCurrentForm_closed (J : Fin 2 → Plane → ℝ)
    (hJ : ∀ i, ContDiff ℝ ∞ (J i)) {p : Plane}
    (hcurl : fderiv ℝ (J 0) p (b 1) = fderiv ℝ (J 1) p (b 0)) (v w : Plane) :
    fderiv ℝ (coordinateCurrentForm J) p v w =
      fderiv ℝ (coordinateCurrentForm J) p w v := by
  have hD := (((hJ 0).differentiable (by simp) p).hasFDerivAt.smul_const
    (show Plane →L[ℝ] ℝ from EuclideanSpace.proj (0 : Fin 2))).add
      (((hJ 1).differentiable (by simp) p).hasFDerivAt.smul_const
        (show Plane →L[ℝ] ℝ from EuclideanSpace.proj (1 : Fin 2)))
  change HasFDerivAt (coordinateCurrentForm J) _ p at hD
  have hd (u z : Plane) : fderiv ℝ (coordinateCurrentForm J) p u z =
      fderiv ℝ (J 0) p u * z 0 + fderiv ℝ (J 1) p u * z 1 := by
    rw [hD.fderiv]
    rfl
  have hexp (u : Plane) : u = u 0 • b 0 + u 1 • b 1 := by
    ext i
    fin_cases i <;> simp
  have hlin (i : Fin 2) (u : Plane) : fderiv ℝ (J i) p u =
      u 0 * fderiv ℝ (J i) p (b 0) + u 1 * fderiv ℝ (J i) p (b 1) := by
    conv_lhs => rw [hexp u]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hd, hd, hlin 0 v, hlin 1 v, hlin 0 w, hlin 1 w, hcurl]
  ring




theorem smooth_closed_current_exists_local_potential
    (J : Fin 2 → Plane → ℝ) (hJ : ∀ i, ContDiff ℝ ∞ (J i))
    (center : Plane) {radius : ℝ} (hr : 0 < radius)
    (hcurl : ∀ p ∈ Metric.ball center radius,
      fderiv ℝ (J 0) p (b 1) = fderiv ℝ (J 1) p (b 0)) :
    ∃ F : Plane → ℝ, ContDiff ℝ ∞ F ∧ ∀ p ∈ Metric.ball center radius,
      HasFDerivAt F (coordinateCurrentForm J p) p := by
  let T := fun (i : Fin 2) (p : Plane) => J i (center + p)
  have hT (i : Fin 2) : ContDiff ℝ ∞ (T i) :=
    (hJ i).comp (contDiff_const.add contDiff_id)
  let omega := coordinateCurrentForm T
  have homega : ContDiff ℝ ∞ omega := coordinateCurrentForm_contDiff T hT
  have hclosed (p : Plane) (hp : p ∈ Metric.ball (0 : Plane) radius) (v w : Plane) :
      fderiv ℝ omega p v w = fderiv ℝ omega p w v := by
    apply coordinateCurrentForm_closed T hT
    have hm : center + p ∈ Metric.ball center radius := by
      simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hp
    simpa only [T, fderiv_comp_add_left] using hcurl (center + p) hm
  let F := fun p => M60.radialPrimitive omega (p - center)
  refine ⟨F, (M60.radialPrimitive_contDiff homega).comp
    (contDiff_id.sub contDiff_const), ?_⟩
  intro p hp
  have hm : p - center ∈ Metric.ball (0 : Plane) radius := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hp
  have h := (M60.hasFDerivAt_radialPrimitive homega
    ((convex_ball (0 : Plane) radius).starConvex (Metric.mem_ball_self hr))
      hclosed hm).comp p ((hasFDerivAt_id p).sub_const center)
  simpa only [F, Function.comp_def, ContinuousLinearMap.comp_id, omega, T,
    coordinateCurrentForm, id_eq, show center + (p - center) = p by abel] using h

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain




theorem observedWeakAnnulus_smoothed_circle_current_potential
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (R : E →L[ℝ] Plane) (hnorm : ∀ q, ‖R (e q)‖ = 1)
    {c0 c1 : ℝ → M} (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (center : Plane) {radius : ℝ} (hr : 0 < radius)
    (hball : Metric.closedBall center radius ⊆ S) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (eps : ℝ) (heps : 0 < eps), eps ≤ delta →
      ∃ F : Plane → ℝ, ContDiff ℝ ∞ F ∧ ∀ p ∈ Metric.ball center radius, ∀ i : Fin 2,
        fderiv ℝ F p (b i) =
          (Poincare.Analysis.Sobolev.mollifierEps heps ⋆[lsmul ℝ ℝ, volume]
            (S).indicator (fun q => planarCircleCurrent (R (e (A.map q)))
              (R (A.column i q)))) p := by
  classical
  have hcompact := isCompact_closedBall center radius
  obtain ⟨delta, hdelta, hbuffer⟩ :=
    hcompact.exists_cthickening_subset_open isOpen_interior hball
  refine ⟨delta, hdelta, ?_⟩
  intro eps heps hepsd
  let phi : Plane → ℝ := Poincare.Analysis.Sobolev.mollifierEps heps
  have hphi : ContDiff ℝ ∞ phi := Poincare.Analysis.Sobolev.mollifierEps_smooth heps
  have hc : HasCompactSupport phi := Poincare.Analysis.Sobolev.mollifierEps_compactSupport heps
  let J := fun (i : Fin 2) (p : Plane) => planarCircleCurrent (R (e (A.map p)))
    (R (A.column i p))
  have hJ (i : Fin 2) : LocallyIntegrable ((S).indicator (J i)) volume :=
    ((memLp_indicator_iff_restrict isOpen_interior.measurableSet).mpr
      (observedWeakAnnulus_circle_current_memLp e R hnorm A i)).locallyIntegrable (by norm_num)
  let T := fun i => phi ⋆[lsmul ℝ ℝ, volume] (S).indicator (J i)
  have hT (i : Fin 2) : ContDiff ℝ ∞ (T i) :=
    hc.contDiff_convolution_left (lsmul ℝ ℝ) hphi (hJ i)
  have hs (p : Plane) (hp : p ∈ Metric.ball center radius) :
      tsupport (fun q => phi (p - q)) ⊆ S := by
    rw [M60.suMollifier_translated_tsupport]
    intro q hq
    exact hbuffer (Metric.mem_cthickening_of_dist_le q p delta
      (Metric.closedBall center radius) (Metric.ball_subset_closedBall hp)
      ((Metric.mem_closedBall.mp hq).trans hepsd))
  obtain ⟨F, hF, hDF⟩ := smooth_closed_current_exists_local_potential T hT center hr
    (fun p hp => observedWeakAnnulus_smoothed_circle_current_closed e he R hnorm A
      hphi hc p (hs p hp))
  refine ⟨F, hF, ?_⟩
  intro p hp i
  rw [(hDF p hp).fderiv, coordinateCurrentForm_apply]
  fin_cases i <;> simp [T, J, phi]

end PoincareConjecture.M64
