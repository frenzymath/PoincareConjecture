import PoincareConjecture.Definitions.M26CanonicalNeighborhoods

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure M27RoundSphereFamily where
  metric : ℝ → RiemannianMetric 2 UnitTwoSphere
  connection : ∀ t, LeviCivitaData (metric t)
  round : ∀ t, t ≤ 0 → ConstantPositiveSectionalCurvature (metric t) (connection t)
  antipodal_isometry : ∀ t, t ≤ 0 → ∀ x : UnitTwoSphere,
    ∀ v w : TangentSpace (𝓡 2) x,
      (metric t).inner (-x)
        (mfderiv (𝓡 2) (𝓡 2) (fun y : UnitTwoSphere => -y) x v)
        (mfderiv (𝓡 2) (𝓡 2) (fun y : UnitTwoSphere => -y) x w) =
        (metric t).inner x v w

noncomputable def M27RoundSphereFamily.productInner (F : M27RoundSphereFamily)
    (t : ℝ) (p : UnitTwoSphere × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) : ℝ :=
  (F.metric t).inner p.1 v.1 w.1 + v.2 * w.2

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

structure M27SphereLineFlowCertificate (K : AncientKappaSolution 3 M) where
  sphere : M27RoundSphereFamily
  identification : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    (UnitTwoSphere × ℝ) M ∞
  metric_transport : ∀ t, t ≤ 0 → ∀ p : UnitTwoSphere × ℝ,
    ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p,
      (K.flow.metric t).inner (identification p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) identification p v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) identification p w) =
        sphere.productInner t p v w

structure M27ProjectivePlaneLineFlowCertificate (K : AncientKappaSolution 3 M) where
  sphere : M27RoundSphereFamily
  cover : UnitTwoSphere × ℝ → M
  cover_surjective : Function.Surjective cover
  cover_local_diffeomorph : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ cover
  cover_fibers : ∀ p q, cover p = cover q ↔ q = p ∨ q = (-p.1, p.2)
  product_homeomorph : M ≃ₜ (RealProjectiveTwo × ℝ)
  product_coordinates : ∀ p, product_homeomorph (cover p) = (Quotient.mk' p.1, p.2)
  metric_transport : ∀ t, t ≤ 0 → ∀ p : UnitTwoSphere × ℝ,
    ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p,
      (K.flow.metric t).inner (cover p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) cover p v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) cover p w) =
        sphere.productInner t p v w

noncomputable def m27TwistedProductInvolution (p : UnitTwoSphere × ℝ) : UnitTwoSphere × ℝ :=
  (-p.1, -p.2)

structure M27TwistedSphereLineFlowCertificate (K : AncientKappaSolution 3 M) where
  sphere : M27RoundSphereFamily
  involution_smooth : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
    ∞ m27TwistedProductInvolution
  involution_free : ∀ p, m27TwistedProductInvolution p ≠ p
  involution_isometry : ∀ t, t ≤ 0 → ∀ p : UnitTwoSphere × ℝ,
    ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p,
      sphere.productInner t (m27TwistedProductInvolution p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
          m27TwistedProductInvolution p v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
          m27TwistedProductInvolution p w) = sphere.productInner t p v w
  cover : UnitTwoSphere × ℝ → M
  cover_surjective : Function.Surjective cover
  cover_local_diffeomorph : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ cover
  cover_fibers : ∀ p q,
    cover p = cover q ↔ q = p ∨ q = m27TwistedProductInvolution p
  metric_transport : ∀ t, t ≤ 0 → ∀ p : UnitTwoSphere × ℝ,
    ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p,
      (K.flow.metric t).inner (cover p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) cover p v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) cover p w) =
        sphere.productInner t p v w
  puncture : RealProjectiveThree
  projective_topology : M ≃ₜ PuncturedRealProjectiveThree puncture
  projective_smooth_cover : StandardPuncturedProjectiveCover M puncture Set.univ

structure M27SphericalSpaceFormFlowCertificate (K : AncientKappaSolution 3 M) where
  group : Type u
  group_finite : Fintype group
  group_structure : Group group
  representation : group → Matrix (Fin 4) (Fin 4) ℝ
  representation_one : representation 1 = 1
  representation_mul : ∀ a b, representation (a * b) = representation a * representation b
  representation_orthogonal : ∀ a,
    (representation a).transpose * representation a = 1
  representation_orientation : ∀ a, (representation a).det = 1
  action : group → UnitThreeSphere → UnitThreeSphere
  action_representation : ∀ a x, (action a x).1 = Matrix.mulVec (representation a) x.1
  action_one : ∀ x, action 1 x = x
  action_mul : ∀ a b x, action (a * b) x = action a (action b x)
  action_free : ∀ a x, action a x = x → a = 1
  action_smooth : ∀ a, ContMDiff (𝓡 3) (𝓡 3) ∞ (action a)
  cover : UnitThreeSphere → M
  cover_surjective : Function.Surjective cover
  cover_local_diffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ cover
  cover_fibers : ∀ x y, cover x = cover y ↔ ∃ a, action a x = y
  metric : ℝ → RiemannianMetric 3 UnitThreeSphere
  connection : ∀ t, LeviCivitaData (metric t)
  round : ∀ t, t ≤ 0 → ConstantPositiveSectionalCurvature (metric t) (connection t)
  action_isometry : ∀ t, t ≤ 0 → ∀ a, ∀ x : UnitThreeSphere,
    ∀ v w : TangentSpace (𝓡 3) x,
      (metric t).inner (action a x)
        (mfderiv (𝓡 3) (𝓡 3) (action a) x v)
        (mfderiv (𝓡 3) (𝓡 3) (action a) x w) = (metric t).inner x v w
  metric_transport : ∀ t, t ≤ 0 → ∀ x : UnitThreeSphere,
    ∀ v w : TangentSpace (𝓡 3) x,
      (K.flow.metric t).inner (cover x)
        (mfderiv (𝓡 3) (𝓡 3) cover x v)
        (mfderiv (𝓡 3) (𝓡 3) cover x w) = (metric t).inner x v w

end PoincareConjecture
