import PoincareConjecture.Proofs.M35.Thm12_28.CylinderMetricComparison










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.StandardCylinderPatch

variable {length : ℝ} {center : StandardCapSpace}

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem axial_contMDiffAt (N : StandardCylinderPatch length center)
    {y : StandardCapSpace} (hy : y ∈ N.carrier) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun z => (N.inverse z).2) y :=
  contMDiffAt_snd.comp y
    ((N.inverse_smooth y hy).contMDiffAt (N.carrier_open.mem_nhds hy))



theorem axial_mfderiv_chart (N : StandardCylinderPatch length center)
    (q : UnitTwoSphere) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-length) length)
    (v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun y => (N.inverse y).2)
      (N.coordinate (M35.cylinderChart q p))
      (mfderiv (𝓡 3) (𝓡 3) (N.coordinate ∘ M35.cylinderChart q) p v) =
      (M35.cylinderCoordinateEquiv v).2 := by
  let f := N.coordinate ∘ M35.cylinderChart q
  let L := (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
    M35.cylinderCoordinateEquiv.toContinuousLinearMap
  have hU := (isOpen_Ioo.preimage
    (continuous_snd.comp M35.cylinderCoordinateEquiv.continuous)).mem_nhds hp
  have heq : ((fun y => (N.inverse y).2) ∘ f) =ᶠ[𝓝 p] L := by
    filter_upwards [hU] with y hy
    have hcoord : N.inverse (N.coordinate (M35.cylinderChart q y)) = M35.cylinderChart q y :=
      N.coordinate_left_inverse ⟨mem_univ _, hy⟩
    exact congrArg Prod.snd hcoord
  have hmem : f p ∈ N.carrier :=
    N.coordinate_image ▸ mem_image_of_mem N.coordinate ⟨mem_univ _, hp⟩
  have hderiv : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) ((fun y => (N.inverse y).2) ∘ f) p =
      mfderiv (𝓡 3) 𝓘(ℝ, ℝ) L p := heq.mfderiv_eq
  have hL : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) L p = L := by
    rw [mfderiv_eq_fderiv, L.hasFDerivAt.fderiv]
  rw [mfderiv_comp p ((N.axial_contMDiffAt hmem).mdifferentiableAt (by simp))
    ((N.euclideanChart_contMDiffAt q hp).mdifferentiableAt (by simp)),
    hL] at hderiv
  exact congrArg (fun A => A v) hderiv



theorem axial_derivative_bound {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hesmall : epsilon ≤ 1 / 24) (hu : u ∈ Icc (-1) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    {y : StandardCapSpace} (hy : y ∈ N.carrier) (w : TangentSpace (𝓡 3) y) :
    |mvfderiv (𝓡 3) (fun z => (N.inverse z).2) y w| ≤
      2 * g.tangentNorm y w := by
  obtain ⟨⟨q, s⟩, hs, rfl⟩ := N.coordinate_image.symm ▸ hy
  let p := M35.cylinderCoordinateEquiv.symm (0, s)
  have hp : M35.cylinderCoordinateEquiv p = (0, s) :=
    M35.cylinderCoordinateEquiv.apply_symm_apply (0, s)
  have hdom : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    simpa only [hp] using hs.2
  have hchart : M35.cylinderChart q p = (q, s) := by
    change ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
      (M35.cylinderCoordinateEquiv p).1, (M35.cylinderCoordinateEquiv p).2) = _
    rw [hp]
    apply Prod.ext
    · have h := (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv
        (mem_chart_source (EuclideanSpace ℝ (Fin 2)) q)
      simpa only [M35.sphere_chart_center] using h
    · rfl
  let f := N.coordinate ∘ M35.cylinderChart q
  let A := mfderiv (𝓡 3) (𝓡 3) f p
  obtain ⟨e, heA⟩ := N.euclideanChart_mfderiv_invertible q hdom
  let v : EuclideanSpace ℝ (Fin 3) := e.symm w
  have hv : A v = w := by
    change mfderiv (𝓡 3) (𝓡 3) f p (e.symm w) = w
    rw [← heA]
    exact e.apply_symm_apply w
  have hmetric := N.euclidean_pullback_lower g he hesmall hu hclose q s hs.2 v
  change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ g.inner (f p) (A v) (A v) at hmetric
  have hroot : (g.tangentNorm (f p) (A v)) ^ 2 = g.inner (f p) (A v) (A v) :=
    Real.sq_sqrt ((by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2).trans hmetric)
  have hnorm : ‖v‖ ≤ 2 * g.tangentNorm (f p) (A v) := by
    have hnonneg : 0 ≤ g.tangentNorm (f p) (A v) := Real.sqrt_nonneg _
    nlinarith [norm_nonneg v]
  have haxis : |(M35.cylinderCoordinateEquiv v).2| ≤ ‖v‖ :=
    PiLp.norm_apply_le v (2 : Fin 3)
  have hdiff : mvfderiv (𝓡 3) (fun z => (N.inverse z).2) (f p) (A v) =
      (M35.cylinderCoordinateEquiv v).2 := N.axial_mfderiv_chart q hdom v
  have hbound := (congrArg abs hdiff).trans_le (haxis.trans hnorm)
  rw [hv] at hbound
  change |mvfderiv (𝓡 3) (fun z => (N.inverse z).2)
    (N.coordinate (M35.cylinderChart q p)) w| ≤
      2 * g.tangentNorm (N.coordinate (M35.cylinderChart q p)) w at hbound
  rw [hchart] at hbound
  exact hbound

end PoincareConjecture.StandardCylinderPatch
