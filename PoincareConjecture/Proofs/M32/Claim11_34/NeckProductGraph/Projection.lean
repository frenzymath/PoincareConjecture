import PoincareConjecture.Proofs.M32.Claim11_34.NeckProductGraph.Axial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ProjectionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v w

namespace PoincareConjecture.M32

private theorem neck_graph_inverse_mfderiv
    {M : Type u} {L : Type v} [TopologicalSpace M] [TopologicalSpace L]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) L]
    (E : OpenPartialHomeomorph L M)
    (hE : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E E.source)
    (hEi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target)
    {y : M} (hy : y ∈ E.target) (v : TangentSpace (𝓡 3) y) :
    mfderiv (𝓡 3) (𝓡 3) E (E.symm y)
      (mfderiv (𝓡 3) (𝓡 3) E.symm y v) = v := by
  have hh := mfderiv_comp y
    ((hE.contMDiffAt (E.open_source.mem_nhds (E.map_target hy))).mdifferentiableAt
      (by simp))
    ((hEi.contMDiffAt (E.open_target.mem_nhds hy)).mdifferentiableAt (by simp))
  have heq : E ∘ E.symm =ᶠ[𝓝 y] id := by
    filter_upwards [E.open_target.mem_nhds hy] with z hz
    exact E.right_inv hz
  rw [heq.mfderiv_eq, mfderiv_id] at hh
  exact (congrArg (fun A => A v) hh).symm

variable {M : Type u} {L : Type v} {C : Type w}
  [TopologicalSpace M] [TopologicalSpace L] [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) L] [IsManifold (𝓡 3) ∞ L]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
  {gM : RiemannianMetric 3 M}

omit [IsManifold (𝓡 3) ∞ L] [IsManifold (𝓡 2) ∞ C] in
private theorem neck_graph_projection_mfderiv
    (N : EpsilonNeck gM) (E : OpenPartialHomeomorph L M)
    (hEi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target)
    (Phi : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L)
    {a : ℝ} (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (q : UnitTwoSphere) (hy : N.coordinate_map (q, a) ∈ E.target)
    (v : TangentSpace (𝓡 2) q) :
    mfderiv (𝓡 2) (𝓡 2)
      (fun p : UnitTwoSphere => (Phi.symm (E.symm (N.coordinate_map (p, a)))).1) q v =
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) Phi.symm
        (E.symm (N.coordinate_map (q, a)))
        (mfderiv (𝓡 3) (𝓡 3) E.symm (N.coordinate_map (q, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, a) (v, 0)))).1 := by
  have hi := (hEi.contMDiffAt (E.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  have hs := (N.sphereSlice_contMDiff ha).mdifferentiableAt (by simp) (x := q)
  have hp := Phi.symm.contMDiff.mdifferentiable (by simp)
    (E.symm (N.coordinate_map (q, a)))
  change mfderiv (𝓡 2) (𝓡 2)
    (Prod.fst ∘ (Phi.symm ∘ (E.symm ∘ (fun p : UnitTwoSphere =>
      N.coordinate_map (p, a))))) q v = _
  erw [mfderiv_comp q mdifferentiableAt_fst (hp.comp q (hi.comp q hs)),
    mfderiv_comp q hp (hi.comp q hs), mfderiv_comp q hi hs, mfderiv_fst]
  change (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) Phi.symm _
    (mfderiv (𝓡 3) (𝓡 3) E.symm _
      (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => N.coordinate_map (p, a)) q v))).1 = _
  rw [N.sphereSlice_mfderiv ha]

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

theorem neckSlice_product_projection_mfderiv_bijective
    (gC : RiemannianMetric 2 C) (gL : RiemannianMetric 3 L)
    (DL : LeviCivitaData gL) (DM : LeviCivitaData gM)
    (Phi : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L)
    (hproduct : ∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      gL.inner (Phi z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi z w) =
        gC.inner z.1 v.1 w.1 + v.2 * w.2)
    (E : OpenPartialHomeomorph L M)
    (hE : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E E.source)
    (hEi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target)
    (N : EpsilonNeck gM) {a : ℝ} (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (q : UnitTwoSphere) (hy : N.coordinate_map (q, a) ∈ E.target)
    {Q Lambda delta : ℝ} (hQ : 0 < Q) (_hLambda : 0 < Lambda) (hdelta : 0 ≤ delta)
    (hscale : Q * N.scale ^ 2 ≤ Lambda) (hsmall : delta * Lambda ≤ 1 / 100)
    (hmetric : ∀ v : TangentSpace (𝓡 3) (E.symm (N.coordinate_map (q, a))),
      gL.inner (E.symm (N.coordinate_map (q, a))) v v ≤
        2 * Q * gM.inner (E (E.symm (N.coordinate_map (q, a))))
          (mfderiv (𝓡 3) (𝓡 3) E (E.symm (N.coordinate_map (q, a))) v)
          (mfderiv (𝓡 3) (𝓡 3) E (E.symm (N.coordinate_map (q, a))) v))
    (hricci : ∀ v : TangentSpace (𝓡 3) (E.symm (N.coordinate_map (q, a))),
      |DM.ricci (E (E.symm (N.coordinate_map (q, a))))
          (mfderiv (𝓡 3) (𝓡 3) E (E.symm (N.coordinate_map (q, a))) v)
          (mfderiv (𝓡 3) (𝓡 3) E (E.symm (N.coordinate_map (q, a))) v) -
        DL.ricci (E.symm (N.coordinate_map (q, a))) v v| ≤
          delta * gL.inner (E.symm (N.coordinate_map (q, a))) v v)
    (hneck : ∀ z ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent z,
      |DM.ricci (N.coordinate_map z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) -
        (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 z v v - v.2 ^ 2)| ≤
          (1 / 100 : ℝ) * EvolvingRoundCylinderMetric 0 z v v) :
    Function.Bijective (mfderiv (𝓡 2) (𝓡 2)
      (fun p : UnitTwoSphere => (Phi.symm (E.symm (N.coordinate_map (p, a)))).1) q) := by
  let A := mfderiv (𝓡 2) (𝓡 2)
    (fun p : UnitTwoSphere => (Phi.symm (E.symm (N.coordinate_map (p, a)))).1) q
  have hinj : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    let y := N.coordinate_map (q, a)
    let x := E.symm y
    let w : TangentSpace (𝓡 3) y :=
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, a) (v, 0)
    let u : TangentSpace (𝓡 3) x := mfderiv (𝓡 3) (𝓡 3) E.symm y w
    let Y := EvolvingRoundCylinderMetric 0 (q, a) (v, 0) (v, 0)
    have haxial : (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) Phi.symm x u).1 = 0 := by
      have hp := neck_graph_projection_mfderiv N E hEi Phi ha q hy v
      change A v = (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) Phi.symm x u).1 at hp
      exact hp.symm.trans hv
    have hRzero : DL.ricci x u u = 0 :=
      ricci_eq_zero_of_product_projection_mfderiv_eq_zero gC gL DL Phi hproduct x u haxial
    have hmap : mfderiv (𝓡 3) (𝓡 3) E x u = w :=
      neck_graph_inverse_mfderiv E hE hEi hy w
    have hxy : E x = y := E.right_inv hy
    have hY : 0 ≤ Y := by
      change 0 ≤ EvolvingRoundCylinderMetric 0 (q, a) (v, 0) (v, 0)
      rw [← roundCylinderProductMetric_inner (q, a) (v, 0) (v, 0)]
      by_cases hz : (v, (0 : ℝ)) = (0 : RoundCylinderTangent (q, a))
      · simp [hz]
      · exact (roundCylinderProductMetric.pos (q, a) (v, 0) hz).le
    have hNmetric := (N.pullback_metric_bounds (z := (q, a)) ha (v, 0)).2
    change gM.inner y w w ≤ (1 + N.epsilon) * N.scale ^ 2 * Y at hNmetric
    have hhi : gM.inner y w w ≤ (3 / 2 : ℝ) * N.scale ^ 2 * Y := by
      nlinarith [mul_nonneg (sub_nonneg.mpr N.epsilon_lt_half.le)
        (mul_nonneg (sq_nonneg N.scale) hY)]
    have hRneck := hneck (q, a) ⟨mem_univ _, ha⟩ (v, 0)
    change |DM.ricci y w w - (1 / 2 : ℝ) * (Y - (0 : ℝ) ^ 2)| ≤
      (1 / 100 : ℝ) * Y at hRneck
    have hRlo : (49 / 100 : ℝ) * Y ≤ DM.ricci y w w := by
      have hh := (abs_le.mp hRneck).1
      norm_num at hh
      linarith
    have hmetricu := hmetric u
    change gL.inner x u u ≤ 2 * Q * gM.inner (E x)
      (mfderiv (𝓡 3) (𝓡 3) E x u) (mfderiv (𝓡 3) (𝓡 3) E x u) at hmetricu
    rw [hmap, hxy] at hmetricu
    have hcomp : gL.inner x u u ≤ 3 * Q * N.scale ^ 2 * Y := by
      calc
        _ ≤ 2 * Q * gM.inner y w w := hmetricu
        _ ≤ 2 * Q * ((3 / 2 : ℝ) * N.scale ^ 2 * Y) :=
          mul_le_mul_of_nonneg_left hhi (by positivity)
        _ = _ := by ring
    have hRicciu := hricci u
    change |DM.ricci (E x) (mfderiv (𝓡 3) (𝓡 3) E x u)
      (mfderiv (𝓡 3) (𝓡 3) E x u) - DL.ricci x u u| ≤
      delta * gL.inner x u u at hRicciu
    rw [hmap, hxy, hRzero, sub_zero] at hRicciu
    have hRhi : DM.ricci y w w ≤ (3 / 100 : ℝ) * Y := by
      calc
        _ ≤ delta * gL.inner x u u := (le_abs_self _).trans hRicciu
        _ ≤ delta * (3 * Q * N.scale ^ 2 * Y) :=
          mul_le_mul_of_nonneg_left hcomp hdelta
        _ = (3 * delta * Y) * (Q * N.scale ^ 2) := by ring
        _ ≤ (3 * delta * Y) * Lambda :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = (3 * (delta * Lambda)) * Y := by ring
        _ ≤ (3 * (1 / 100 : ℝ)) * Y := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 3)) hY
        _ = _ := by ring
    have hYzero : Y = 0 := by linarith
    by_contra hvne
    have hvne' : (v, (0 : ℝ)) ≠ (0 : RoundCylinderTangent (q, a)) := by
      intro hh
      exact hvne (congrArg Prod.fst hh)
    have hp := roundCylinderProductMetric.pos (q, a) (v, 0) hvne'
    exact hp.ne' ((roundCylinderProductMetric_inner (q, a) (v, 0) (v, 0)).trans hYzero)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 2) q) := by
    unfold TangentSpace
    infer_instance
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hinj⟩

end PoincareConjecture.M32
