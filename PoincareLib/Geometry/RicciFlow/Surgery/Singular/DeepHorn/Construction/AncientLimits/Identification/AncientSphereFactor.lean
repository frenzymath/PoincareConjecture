import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.SphereCover
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Topology

/-!
# Sphere coordinates for the actual compact round factor

The eligible `exists_scalarNormalized_roundSurface_cover` gives the
actual sphere cover and its exact antipodal alternative. The existing
`exists_projectiveCentralSection_homeomorph` turns the latter into a
projective product neighborhood through the retained product map.

Sources: Morgan--Tian Corollary 9.50(3), printed pp. 213-214, and the
final argument after Claim 11.35, p. 291. The source horn exclusion is
Claim 11.34, pp. 288-289. Reviewed derivation:
`claim11_35-normalized-ancient-cylinder.md`, section 3.
-/

noncomputable section
set_option autoImplicit false

open Set Topology Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareMT.M32

variable {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
  [T2Space C] [T3Space C] [ConnectedSpace C] [CompactSpace C]
  {M : Type v} [TopologicalSpace M]

/-- The compact scalar-one round factor has exact sphere coordinates when
its actual ambient product admits no open projective collar. Sources:
Corollary 9.50(3), pp. 213-214, Claim 11.34, pp. 288-289, and p. 291. -/
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

end PoincareMT.M32
