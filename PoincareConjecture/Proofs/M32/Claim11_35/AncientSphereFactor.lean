import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.SphereCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Topology

noncomputable section
set_option autoImplicit false

open Set Topology Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M32

variable {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
  [T2Space C] [T3Space C] [ConnectedSpace C] [CompactSpace C]
  {M : Type v} [TopologicalSpace M]

theorem roundSurface_exists_sphereDiffeomorph_of_no_projective_product
    (g : RiemannianMetric 2 C) (D : LeviCivitaData g)
    (hround : ConstantPositiveSectionalCurvature g D)
    (p : C) (hscalar : D.scalarCurvature p = 1)
    (e : (C × ℝ) ≃ₜ M)
    (hno : ¬ ∃ f : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → M, IsOpenEmbedding f) :
    ∃ a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ C,
      ∀ (x : UnitTwoSphere) (u v : TangentSpace (𝓡 2) x),
        g.inner (a x) (mfderiv (𝓡 2) (𝓡 2) a x u)
          (mfderiv (𝓡 2) (𝓡 2) a x v) =
            2 * (roundSphereMetric 2).inner x u v := by
  obtain ⟨_, q, hq, hsurj, hlocal, hmetric, hdichotomy⟩ :=
    exists_scalarNormalized_roundSurface_cover g D hround p
  have hnormalized (x : UnitTwoSphere) (u v : TangentSpace (𝓡 2) x) :
      g.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x u)
        (mfderiv (𝓡 2) (𝓡 2) q x v) =
          2 * (roundSphereMetric 2).inner x u v := by
    simpa only [hscalar, one_mul] using hmetric x u v
  rcases hdichotomy with hinj | hanti
  · exact ⟨hlocal.diffeomorphOfBijective ⟨hinj, hsurj⟩, hnormalized⟩
  · exfalso
    obtain ⟨b, _⟩ := exists_projectiveCentralSection_homeomorph q hq.continuous hanti
    let b' : RealProjectiveTwo ≃ₜ C :=
      b.trans ((Homeomorph.setCongr hsurj.range_eq).trans (Homeomorph.Set.univ C))
    let f : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → M :=
      fun z => e (b' z.1, (z.2 : ℝ))
    have hf : IsOpenEmbedding f :=
      e.isOpenEmbedding.comp (b'.isOpenEmbedding.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal)
    exact hno ⟨f, hf⟩

end PoincareConjecture.M32
