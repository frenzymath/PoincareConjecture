import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Escaping.Splitting
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Topology.ProjectiveProduct
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.StrongNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Collar
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph.Product

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

variable {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
  [T2Space C] [T3Space C] [ConnectedSpace C] [SecondCountableTopology C]
  [MeasurableSpace C] [BorelSpace C]
  {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

theorem exists_scalarNormalized_sphere_of_round_factor
    (K : AncientKappaSolution 3 M) (A : AncientKappaSolution 2 C)
    (H : TwoDimensionalAncientRoundCertificate A)
    (hplane : NoEmbeddedTrivialNormalProjectivePlane K)
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (hmetric : ∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (K.flow.metric 0).inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          (A.flow.metric 0).inner z.1 v.1 w.1 + v.2 * w.2)
    (p : M) :
    0 < (K.flow.connection 0).scalarCurvature p ∧
      ∃ a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ C,
        ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
          (K.flow.connection 0).scalarCurvature p * (A.flow.metric 0).inner (a x)
            (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
              2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w := by
  let : CompactSpace C := H.compact
  have heq : (K.flow.connection 0).scalarCurvature p =
      (A.flow.connection 0).scalarCurvature (e.symm p).1 := by
    simpa only [e.apply_symm_apply] using
      (A.flow.metric 0).scalarCurvature_eq_of_line_product (K.flow.metric 0)
        (A.flow.connection 0) (K.flow.connection 0) e hmetric (e.symm p)
  obtain ⟨hpos, q, _, hsurj, hlocal, hnorm, hinj | hfiber⟩ :=
    exists_scalarNormalized_roundSurface_cover (A.flow.metric 0)
      (A.flow.connection 0) (H.round_at_all_times 0 le_rfl) (e.symm p).1
  · refine ⟨heq.symm ▸ hpos, hlocal.diffeomorphOfBijective ⟨hinj, hsurj⟩, ?_⟩
    intro x v w
    rw [heq]
    exact hnorm x v w
  · exfalso
    let b : RoundCylinderSpace → C × ℝ := Prod.map q id
    let f : RoundCylinderSpace → M := e ∘ b
    have hb : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ b :=
      hlocal.prodMap (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph
    have hf : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f :=
      fun z => (hb z).comp (𝓡 3) M (e.isLocalDiffeomorph (b z))
    have hfib (z w : RoundCylinderSpace) : f z = f w ↔ w = z ∨ w = (-z.1, z.2) := by
      change e (q z.1, z.2) = e (q w.1, w.2) ↔ _
      rw [show e (q z.1, z.2) = e (q w.1, w.2) ↔
        (q z.1, z.2) = (q w.1, w.2) from ⟨fun h => e.injective h, fun h => congrArg e h⟩,
        Prod.mk.injEq, hfiber]
      constructor
      · rintro ⟨h | h, hl⟩
        · exact Or.inl (Prod.ext h hl.symm)
        · exact Or.inr (Prod.ext h hl.symm)
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, rfl⟩
        · exact ⟨Or.inr rfl, rfl⟩
    obtain ⟨hopen, d, _⟩ := exists_projectiveCylinderSlab_homeomorph f
      (s := 1) hf.isLocalHomeomorph.isLocalHomeomorphOn
      (fun z _ w _ => hfib z w)
    exact hplane ⟨fun z => (d z).val,
      hopen.isOpenEmbedding_subtypeVal.comp d.isOpenEmbedding⟩

theorem exists_strongEvolvingNeck_of_round_factor
    (K : AncientKappaSolution 3 M) (A : AncientKappaSolution 2 C)
    (H : TwoDimensionalAncientRoundCertificate A)
    (hplane : NoEmbeddedTrivialNormalProjectivePlane K)
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (hmetric : ∀ t ≤ 0, ∀ (z : C × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (K.flow.metric t).inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2)
    {epsilon : ℝ} (hε : 0 < epsilon) (hεhalf : epsilon < 1 / 2) (x : M) :
    ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  obtain ⟨hR, a, ha⟩ := exists_scalarNormalized_sphere_of_round_factor
    K A H hplane e (hmetric 0 le_rfl) x
  let R := (K.flow.connection 0).scalarCurvature x
  let ℓ := scalarNormalizedCylinderLine R (e.symm x).2 hR
  let b := a.prodCongr ℓ
  let Φ := centeredScalarNormalizedCylinderDiffeomorph a e R hR x
  have hcenter : Φ (a.symm (e.symm x).1, 0) = x := by
    change e (a (a.symm (e.symm x).1), (e.symm x).2 + 0 / Real.sqrt R) = x
    rw [a.apply_symm_apply, zero_div, add_zero, Prod.mk.eta, e.apply_symm_apply]
  have hscalar : R = (A.flow.connection 0).scalarCurvature (e.symm x).1 := by
    simpa only [e.apply_symm_apply] using
      (A.flow.metric 0).scalarCurvature_eq_of_line_product (K.flow.metric 0)
        (A.flow.connection 0) (K.flow.connection 0) e (hmetric 0 le_rfl) (e.symm x)
  have hmodel : ∀ u ∈ Ioc (-1 : ℝ) 0,
      (fun z v w => R * roundCylinderPullback (K.flow.metric (0 + u / R)) Φ z v w) =
        EvolvingRoundCylinderMetric u := by
    intro u hu
    funext z v w
    have hdb (v : RoundCylinderTangent z) :
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) b z v =
          (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1, v.2 / Real.sqrt R) := by
      change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (Prod.map a ℓ) z v = _
      rw [mfderiv_prodMap (a.mdifferentiable (by simp) _)
        (ℓ.mdifferentiable (by simp) _)]
      change (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1,
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℓ z.2 v.2) = _
      rw [mfderiv_scalarNormalizedCylinderLine]
    have hdΦ (v : RoundCylinderTangent z) :
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v =
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (b z)
            (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1, v.2 / Real.sqrt R) := by
      change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (e ∘ b) z v = _
      rw [mfderiv_comp z (e.mdifferentiable (by simp) _)
        (b.mdifferentiable (by simp) _)]
      exact congrArg (fun q => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (b z) q) (hdb v)
    change R * (K.flow.metric (0 + u / R)).inner (Φ z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z w) = _
    rw [hdΦ, hdΦ]
    change R * (K.flow.metric (0 + u / R)).inner (e (b z)) _ _ = _
    rw [hmetric _ (by simpa using div_nonpos_of_nonpos_of_nonneg hu.2 hR.le)]
    change R * ((A.flow.metric (0 + u / R)).inner (a z.1)
      (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1) (mfderiv (𝓡 2) (𝓡 2) a z.1 w.1) +
        (v.2 / Real.sqrt R) * (w.2 / Real.sqrt R)) = _
    have he := RicciFlow.Splitting.round_surface_inner_backward A.flow
      H.round_at_all_times le_rfl (e.symm x).1 hu.2 (a z.1)
      (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1) (mfderiv (𝓡 2) (𝓡 2) a z.1 w.1)
    rw [← hscalar] at he
    rw [he, mul_add]
    have hline : R * ((v.2 / Real.sqrt R) * (w.2 / Real.sqrt R)) = v.2 * w.2 := by
      rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hR.le]
      exact mul_div_cancel₀ _ hR.ne'
    rw [hline, ← mul_assoc, mul_comm R (1 - u), mul_assoc, ha]
    change (1 - u) * (2 * _) + v.2 * w.2 = 2 * (1 - u) * _ + v.2 * w.2
    rw [← mul_assoc, mul_comm (1 - u) 2]
    rfl
  obtain ⟨N, hN, _⟩ := exists_strongEvolvingNeck_of_exactCylinder K le_rfl hε hεhalf
    x hR Φ (a.symm (e.symm x).1) hcenter hmodel
  exact ⟨N, hN⟩

end PoincareConjecture
