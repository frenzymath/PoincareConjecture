import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Geometry.AxialTransversality
import PoincareLib.Topology.Manifold.NeckCap.Geometry.AnalyticTools.Real.RealPartialDerivative
import PoincareLib.Topology.Manifold.NeckCap.Geometry.AnalyticTools.Connected.ConnectedSign

/-!
# Coherent axial orientation on connected overlap regions

The scaled cross-axis derivative is a real partial derivative of the
actual coordinate transition. It is continuous on the retained overlap,
so pointwise near-unit control has one sign on any preconnected subregion.
This is the coherent-orientation step for MT A.11(3), p. 503, used in
A.12-A.16; see the reviewed coherent-axial-orientation derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- The actual scaled cross-axis derivative is the real partial height
derivative with the exact scale ratio. This is the differential identity
for the orientation in MT A.11(3), p. 503. -/
theorem scaled_cross_axis_eq_real_deriv (N N' : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain)
    (hx' : N.coordinate_map z ∈ N'.carrier) :
    N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2)
      (N.coordinate_map z) (N.normalizedAxialVector (N.coordinate_map z)) =
      (N'.scale / N.scale) *
        deriv (fun r => (N'.coordinate_inverse (N.coordinate_map (z.1, r))).2) z.2 := by
  let D : RoundCylinderSpace → (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
    fun w => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map w
  let L := mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) (N.coordinate_map z)
  have hm := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds hz)).mdifferentiableAt (by simp)
  have hi := (N'.coordinate_inverse_smooth.contMDiffAt
    (N'.carrier_open.mem_nhds hx')).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ)
      (fun y => (N'.coordinate_inverse y).2) (N.coordinate_map z) :=
    mdifferentiableAt_snd.comp (N.coordinate_map z) hi
  have hp : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun r : ℝ => (z.1, r)) z.2 := mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hd : deriv (fun r => (N'.coordinate_inverse (N.coordinate_map (z.1, r))).2) z.2 =
      L (D z (0, 1)) := by
    have hc := mfderiv_comp_apply z.2 hl (hm.comp z.2 hp) (1 : ℝ)
    rw [mfderiv_eq_fderiv] at hc
    change deriv (fun r => (N'.coordinate_inverse (N.coordinate_map (z.1, r))).2) z.2 =
      L (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (N.coordinate_map ∘ (fun r : ℝ => (z.1, r))) z.2 1) at hc
    rw [mfderiv_comp_apply z.2 hm hp, mfderiv_prod_right] at hc
    exact hc
  have ha : (N.normalizedAxialVector (N.coordinate_map z) : EuclideanSpace ℝ (Fin 3)) =
      N.scale⁻¹ • D z (0, 1) := by
    change N.scale⁻¹ • D (N.coordinate_inverse (N.coordinate_map z)) (0, 1) = _
    rw [N.coordinate_inverse_coordinate_map hz]
  change N'.scale * L (N.normalizedAxialVector (N.coordinate_map z)) = _
  rw [ha, map_smul, smul_eq_mul, hd, div_eq_mul_inv, mul_assoc]

/-- The scaled cross-axis scalar is continuous on the actual open
coordinate overlap. No regularity of totalized charts outside their
retained domains is used in this input to MT A.11(3), p. 503. -/
theorem continuousOn_scaled_cross_axis (N N' : EpsilonNeck g) :
    ContinuousOn (fun z : RoundCylinderSpace =>
      N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2)
        (N.coordinate_map z) (N.normalizedAxialVector (N.coordinate_map z)))
      (N.cylinderDomain ∩ N.coordinate_map ⁻¹' N'.carrier) := by
  let U := N.cylinderDomain ∩ N.coordinate_map ⁻¹' N'.carrier
  let H : RoundCylinderSpace → ℝ :=
    fun z => (N'.coordinate_inverse (N.coordinate_map z)).2
  have hU : IsOpen U := N.coordinate_map_smooth.continuousOn.isOpen_inter_preimage
    N.cylinderDomain_open N'.carrier_open
  have hH : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H U :=
    contMDiff_snd.comp_contMDiffOn (N'.coordinate_inverse_smooth.comp
      (N.coordinate_map_smooth.mono inter_subset_left) (fun _ hz => hz.2))
  have hD : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : RoundCylinderSpace => deriv (fun r => H (z.1, r)) z.2) U := by
    intro z hz
    exact ((hH.contMDiffAt (hU.mem_nhds hz)).real_partial_deriv_snd).contMDiffWithinAt
  have hscaled := hD.continuousOn.const_mul (N'.scale / N.scale)
  exact hscaled.congr (fun z hz => N.scaled_cross_axis_eq_real_deriv N' hz.1 hz.2)

/-- One axial orientation works on every preconnected retained overlap
region at a universal threshold. This is the coherent sign form of
MT A.11(3), p. 503, used by the oriented chains in A.12-A.16. -/
theorem exists_intersecting_coherent_orientation {η : ℝ} (hη : η ∈ Ioc 0 (1 / 2)) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ S : Set RoundCylinderSpace, IsPreconnected S →
      S ⊆ N.cylinderDomain ∩ N.coordinate_map ⁻¹' N'.carrier →
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z ∈ S,
        |1 - σ * N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2)
          (N.coordinate_map z) (N.normalizedAxialVector (N.coordinate_map z))| < η := by
  obtain ⟨ε, hpos, hcap, hcontrol⟩ := exists_intersecting_axial_derivative_control.{u} hη.1
  refine ⟨ε, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' S hS hsub
  have hpoint (z : RoundCylinderSpace) (hz : z ∈ S) :
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        |1 - σ * (N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2)
          (N.coordinate_map z) (N.normalizedAxialVector (N.coordinate_map z)))| < η := by
    obtain ⟨σ, hσ, hc⟩ := hcontrol N N' hN hN' (N.coordinate_map z)
      (N.coordinate_map_mem (hsub hz).1) (hsub hz).2
    exact ⟨σ, hσ, by simpa only [mul_assoc] using hc⟩
  obtain ⟨σ, hσ, hc⟩ := hS.exists_sign_mul_close
    ((N.continuousOn_scaled_cross_axis N').mono hsub) (by linarith [hη.2]) hpoint
  exact ⟨σ, hσ, fun z hz => by simpa only [mul_assoc] using hc z hz⟩

end PoincareMT.EpsilonNeck
