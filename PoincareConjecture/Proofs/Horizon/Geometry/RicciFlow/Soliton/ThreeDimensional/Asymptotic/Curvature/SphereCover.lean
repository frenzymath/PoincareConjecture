import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.DeckAction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Homothety
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Model.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Curvature








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

variable {C : Type*} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
  [T2Space C] [T3Space C] [ConnectedSpace C] [CompactSpace C]



theorem exists_scalarNormalized_roundSurface_cover
    (g : RiemannianMetric 2 C) (D : LeviCivitaData g)
    (hround : ConstantPositiveSectionalCurvature g D) (p : C) :
    0 < D.scalarCurvature p ∧
      ∃ q : UnitTwoSphere → C,
        ContMDiff (𝓡 2) (𝓡 2) ∞ q ∧ Function.Surjective q ∧
        IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q ∧
        (∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
          D.scalarCurvature p * g.inner (q x)
            (mfderiv (𝓡 2) (𝓡 2) q x v) (mfderiv (𝓡 2) (𝓡 2) q x w) =
              2 * (roundSphereMetric 2).inner x v w) ∧
        (Function.Injective q ∨ ∀ x y, q x = q y ↔ y = x ∨ y = -x) := by
  obtain ⟨R, hR, hscalar⟩ :=
    (constantPositiveSectionalCurvature_iff_scalarCurvature D).mp hround
  have hc : 0 < R / 2 := by positivity
  let h := rescaledMetric g (R / 2) hc
  let Dh := rescaledMetric_connection g D (R / 2) hc
  have hsec (x : C) (v w : TangentSpace (𝓡 2) x)
      (hgram : h.inner x v v * h.inner x w w - (h.inner x v w) ^ 2 ≠ 0) :
      h.leviCivitaData.sectionalCurvature x v w = 1 := by
    have hg : g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 ≠ 0 := by
      intro hz
      apply hgram
      change (R / 2 * g.inner x v v) * (R / 2 * g.inner x w w) -
        (R / 2 * g.inner x v w) ^ 2 = 0
      calc
        _ = (R / 2) ^ 2 * (g.inner x v v * g.inner x w w -
          (g.inner x v w) ^ 2) := by ring
        _ = 0 := by rw [hz, mul_zero]
    have heq : h.leviCivitaData.sectionalCurvature x v w =
        Dh.sectionalCurvature x v w := by
      simp only [LeviCivitaData.sectionalCurvature,
        h.leviCivitaData.horizon_curvatureTensor_eq Dh]
      rfl
    rw [heq]
    change (rescaledMetric_connection g D (R / 2) hc).sectionalCurvature x v w = _
    rw [rescaledMetric_sectionalCurvature, D.sectionalCurvature_eq_half_scalarCurvature x v w hg,
      hscalar]
    field_simp
  obtain ⟨q, hq, hsurj, hlocal, hmetric⟩ :=
    RicciFlow.Splitting.exists_unitSphere_two_covering h hsec
  refine ⟨by rw [hscalar]; exact hR, q, hq, hsurj, hlocal, ?_,
    RicciFlow.Splitting.orthogonalSurfaceDeckGroup_fiber_dichotomy h q hlocal hmetric⟩
  intro x v w
  have hm := hmetric x v w
  change R / 2 * g.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x v)
    (mfderiv (𝓡 2) (𝓡 2) q x w) = (roundSphereMetric 2).inner x v w at hm
  rw [hscalar]
  linarith

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem roundCylinder_or_antipodal_cover_of_round_surface_product
    (g : RiemannianMetric 2 C) (G : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (DG : LeviCivitaData G)
    (hround : ConstantPositiveSectionalCurvature g D)
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (hmetric : ∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      G.inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          g.inner z.1 v.1 w.1 + v.2 * w.2)
    (p : M) :
    0 < DG.scalarCurvature p ∧
      ((∃ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
          (q : UnitTwoSphere), Φ (q, 0) = p ∧
          (fun z v w => DG.scalarCurvature p * roundCylinderPullback G Φ z v w) =
            EvolvingRoundCylinderMetric 0) ∨
        ∃ q : UnitTwoSphere → C,
          ContMDiff (𝓡 2) (𝓡 2) ∞ q ∧ Function.Surjective q ∧
          IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q ∧
          (∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
            DG.scalarCurvature p * g.inner (q x)
              (mfderiv (𝓡 2) (𝓡 2) q x v) (mfderiv (𝓡 2) (𝓡 2) q x w) =
                2 * (roundSphereMetric 2).inner x v w) ∧
          ∀ x y, q x = q y ↔ y = x ∨ y = -x) := by
  have heq : DG.scalarCurvature p = D.scalarCurvature (e.symm p).1 := by
    simpa only [e.apply_symm_apply] using
      g.scalarCurvature_eq_of_line_product G D DG e hmetric (e.symm p)
  obtain ⟨hpos, q, hq, hsurj, hlocal, hnormalized, hdichotomy⟩ :=
    exists_scalarNormalized_roundSurface_cover g D hround (e.symm p).1
  have hR : 0 < DG.scalarCurvature p := heq.symm ▸ hpos
  have hnorm (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x) :
      DG.scalarCurvature p * g.inner (q x)
        (mfderiv (𝓡 2) (𝓡 2) q x v) (mfderiv (𝓡 2) (𝓡 2) q x w) =
          2 * (roundSphereMetric 2).inner x v w := by
    rw [heq]
    exact hnormalized x v w
  refine ⟨hR, ?_⟩
  rcases hdichotomy with hinj | hantipodal
  · let a := hlocal.diffeomorphOfBijective ⟨hinj, hsurj⟩
    obtain ⟨Φ, x, _, _, hcenter, hpullback⟩ :=
      exists_centered_scalarNormalized_roundCylinder G g e hmetric hR a hnorm p
    exact Or.inl ⟨Φ, x, hcenter, hpullback⟩
  · exact Or.inr ⟨q, hq, hsurj, hlocal, hnorm, hantipodal⟩

end PoincareConjecture
