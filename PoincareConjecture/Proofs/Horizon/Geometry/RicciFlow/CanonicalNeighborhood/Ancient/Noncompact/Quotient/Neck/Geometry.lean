import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.StrongNeck

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  (C : M27TwistedSphereLineFlowCertificate K)
  {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hhalf : epsilon < 1 / 2)
  (p : UnitTwoSphere × ℝ)
  (hR : 0 < (K.flow.connection t).scalarCurvature (C.cover p))
  (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
  (ha : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
    (K.flow.connection t).scalarCurvature (C.cover p) *
      (C.sphere.metric t).inner (a x)
        (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
          2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w)
  (hp : epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover p)) ≤ p.2)

local notation "N" => (C.strongNeck ht hε hhalf p hR a ha hp).terminal_neck

@[simp] theorem strongNeck_center :
    (C.strongNeck ht hε hhalf p hR a ha hp).center = C.cover p := rfl

@[simp] theorem strongNeck_terminal_center : (N).center = C.cover p := rfl

@[simp] theorem strongNeck_scale :
    (N).scale = (K.flow.connection t).scalarCurvature (C.cover p) ^ (-1 / 2 : ℝ) := rfl

@[simp] theorem strongNeck_coordinate_map :
    (N).coordinate_map = C.normalizedCover a
      ((K.flow.connection t).scalarCurvature (C.cover p)) p.2 hR := rfl

theorem strongNeck_carrier :
    (N).carrier = C.cover '' (univ ×ˢ Ioo
      (p.2 - epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover p)))
      (p.2 + epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover p)))) := by
  change (C.normalizedSlab a (s := p.2) (epsilon := epsilon) hR hp).target = _
  exact C.normalizedSlab_target (s := p.2) (epsilon := epsilon) a hR hp

theorem strongNeck_central_sphere :
    (N).central_sphere = C.cover '' (univ ×ˢ ({p.2} : Set ℝ)) := by
  rw [EpsilonNeck.central_sphere_eq, strongNeck_coordinate_map]
  exact C.normalizedCover_image_sphere a hR p.2

theorem strongNeck_region {l u : ℝ} (hl : -epsilon⁻¹ ≤ l) (hu : u ≤ epsilon⁻¹) :
    (N).region l u = C.cover '' (univ ×ˢ Ioo
      (p.2 + l / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover p)))
      (p.2 + u / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover p)))) := by
  rw [← C.normalizedCover_image_interval a hR p.2 l u]
  let e := C.normalizedSlab a (s := p.2) (epsilon := epsilon) hR hp
  ext x
  change (x ∈ e.target ∧ l < (e.symm x).2 ∧ (e.symm x).2 < u) ↔
    x ∈ C.normalizedCover a ((K.flow.connection t).scalarCurvature (C.cover p)) p.2 hR ''
      (univ ×ˢ Ioo l u)
  constructor
  · intro hx
    exact ⟨e.symm x, ⟨mem_univ _, hx.2⟩, e.right_inv hx.1⟩
  · rintro ⟨z, hz, rfl⟩
    have hzs : z ∈ e.source := ⟨mem_univ _, hl.trans_lt hz.2.1, hz.2.2.trans_le hu⟩
    have hi : e.symm (C.normalizedCover a
      ((K.flow.connection t).scalarCurvature (C.cover p)) p.2 hR z) = z := e.left_inv hzs
    exact ⟨e.map_source hzs, by simpa only [hi, mem_Ioo] using hz.2⟩

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
