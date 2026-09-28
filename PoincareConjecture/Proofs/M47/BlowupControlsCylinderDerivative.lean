import PoincareConjecture.Proofs.M47.BlowupControlsDerivatives










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {G : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}



noncomputable def normalizedCylinderScalar
    (e : GeneralizedFlowCylinder G C origin scale I U) (x : C.carrier) (s : ℝ) : ℝ := by
  classical
  exact if hs : s ∈ I then G.scalar (e.pointMap s hs x) / scale else 0



theorem normalizedCylinderScalar_hasDerivWithinAt
    (h04 : RicciFlowCurvatureTheory.{u})
    (e : GeneralizedFlowCylinder G C origin scale I U) {x : C.carrier} (hx : x ∈ U)
    (s : ℝ) (hs : s ∈ I) :
    let p := e.pointMap s hs x
    HasDerivWithinAt (normalizedCylinderScalar e x)
      (((G.connection p.1).laplacian (G.connection p.1).scalarCurvature p.2 +
        2 * (G.connection p.1).ricciNormSq p.2) / scale ^ 2) I s := by
  classical
  obtain ⟨b, y, delta, hdelta, hvertical⟩ := e.vertical_compatibility s hs x hx
  obtain ⟨hb, himage⟩ := hvertical s hs (by simpa using hdelta)
  let J := I ∩ Metric.ball s delta
  let clock := fun u : ℝ => origin + u / scale
  have hsJ : s ∈ J := ⟨hs, Metric.mem_ball_self hdelta⟩
  have htime : MapsTo clock J (G.box b).interval := by
    intro u hu
    obtain ⟨hbu, _⟩ := hvertical u hu.1 (by
      simpa only [Metric.mem_ball, Real.dist_eq] using hu.2)
    exact hbu
  have hclock : HasDerivWithinAt clock (1 / scale) J s :=
    (((hasDerivAt_id s).div_const scale).const_add origin).hasDerivWithinAt
  have hderiv := ((h04.scalar_evolution 3 (G.box b).carrier.carrier (G.box b).interval
    (G.box b).flow (origin + s / scale) hb y).comp s hclock htime).div_const scale
  have heq : ∀ u ∈ J, normalizedCylinderScalar e x u =
      ((G.box b).flow.connection (clock u)).scalarCurvature y / scale := by
    intro u hu
    obtain ⟨hbu, himage⟩ := hvertical u hu.1 (by
      simpa only [Metric.mem_ball, Real.dist_eq] using hu.2)
    rw [normalizedCylinderScalar, dif_pos hu.1]
    change G.scalar ⟨origin + u / scale, e.forward u hu.1 x⟩ / scale = _
    rw [himage, ← generalized_box_scalar_eq G b (origin + u / scale) hbu y]
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ((G.box b).forward (clock s) hb) := by
    intro z
    exact (generalized_box_slice_chart G b (clock s) hb).isLocalDiffeomorphAt
      (𝓡 3) (𝓡 3) ∞ (mem_univ z)
  have hevolution := M47Positive.scalarEvolution_eq_of_metric_pullback
    ((G.box b).flow.connection (clock s)) (G.connection (clock s))
    (h04.tensor_calculus 3 (G.slice (clock s)).carrier
      (G.metric (clock s)) (G.connection (clock s))) hf
    (fun z v w => ((G.box b).metric_pullback (clock s) hb z v w).symm) y
  have hresult := hderiv.congr_of_mem heq hsJ
  have hrate :
      ((((G.box b).flow.connection (clock s)).laplacian
          ((G.box b).flow.connection (clock s)).scalarCurvature y +
        2 * ((G.box b).flow.connection (clock s)).ricciNormSq y) * (1 / scale)) / scale =
      ((G.connection (clock s)).laplacian (G.connection (clock s)).scalarCurvature
          (e.forward s hs x) +
        2 * (G.connection (clock s)).ricciNormSq (e.forward s hs x)) / scale ^ 2 := by
    rw [hevolution, himage]
    simp only [div_eq_mul_inv]
    ring
  rw [hrate] at hresult
  apply hresult.mono_of_mem_nhdsWithin
  exact inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds s hdelta))

end PoincareConjecture.M47
