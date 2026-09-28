import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalTrimmedPartitionReflection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointOrbitCharts










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "V3" => (Fin 3 → ℝ)
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 4000000 in
theorem exists_original_partition_endpoint_cover
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hG : ∀ s k, (G s k).IsFinitePL)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (ι κ : K.FaceOfCard 4 → Type*) [∀ t, Finite (ι t)] [∀ t, Finite (κ t)]
    (cut rim : ∀ t, ι t → Set E)
    (hcut : ∀ t i, IsFinitePLBallPair (ℝ × ℝ) (cut t i) (rim t i))
    (hsub : ∀ t i, cut t i ⊆ convexHull ℝ (t.1 : Set E))
    (hrim : ∀ t i, cut t i ∩ intrinsicFrontier ℝ (convexHull ℝ (t.1 : Set E)) = rim t i)
    (hdis : ∀ t, Pairwise fun i j => Disjoint (cut t i) (cut t j))
    (hphysical : ∀ t, g '' (⋃ i, cut t i) = S ∩ (g '' convexHull ℝ (t.1 : Set E)))
    (B R : ∀ t, κ t → Set E)
    (hB : ∀ t k, IsFinitePLBallPair V3 (B t k) (R t k))
    (hR : ∀ t k, R t k = B t k ∩ (intrinsicFrontier ℝ (convexHull ℝ (t.1 : Set E)) ∪ ⋃ i, cut t i))
    (hcover : ∀ t, (⋃ k, B t k) = convexHull ℝ (t.1 : Set E))
    (hinter : ∀ t, Pairwise (fun k l => B t k ∩ B t l ⊆ ⋃ i, cut t i))
    (hwhole : ∀ t k i, (B t k ∩ cut t i).Nonempty → cut t i ⊆ R t k)
    (hcomp : ∀ t k x, x ∈ B t k \ ⋃ i, cut t i →
      connectedComponentIn (convexHull ℝ (t.1 : Set E) \ ⋃ i, cut t i) x = B t k \ ⋃ i, cut t i) :
    let Cell := RegularOriginalCutCell K g S D κ B
    ∃ (i₀ i₁ : ∀ j : Cell, ι j.1.1),
      (∀ j, i₀ j ≠ i₁ j) ∧
      (∀ j, cut j.1.1 (i₀ j) ⊆ R j.1.1 j.1.2 ∧ cut j.1.1 (i₁ j) ⊆ R j.1.1 j.1.2) ∧
    ∃ flip : ∀ j : Cell,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1) (B j.1.1 j.1.2) → Bool,
    ∃ H : ∀ j : Cell, (cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ B j.1.1 j.1.2,
      (∀ j, (H j).IsFinitePL) ∧
      (∀ j x, (H j x : E) ∈ cut j.1.1 (i₀ j) ↔ (x : E × ℝ).2 = 0) ∧
      (∀ j x, (H j x : E) ∈ cut j.1.1 (i₁ j) ↔ (x : E × ℝ).2 = 1) ∧
      (∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
        (B j.1.1 j.1.2)) (u t : I),
        ((H j).symm ⟨G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
          z.2 (G _ _ _).property⟩ : E × ℝ) =
          ((G z.1.1.1 z.1.2
            ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ))) ∧
    ∃ C : ∀ j : Cell, (cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j),
      (∀ j, (C j).IsFinitePL) ∧
      (∀ j x, (C j x : E) = H j (trimProduct (cut j.1.1 (i₀ j)) x)) ∧
      Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S) ∧
    ∃ (J : (⋃ j, prismTrim (H j)) ≃ₜ (⋃ j, prismTrim (H j))),
      J.IsFinitePL ∧ Function.Involutive J ∧
      (∀ j (x : prismTrim (H j)),
        (J ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) = prismFiberReflection (C j) x) ∧
    ∃ (τ : (⋃ j, prismEnds (C j)) ≃ₜ (⋃ j, prismEnds (C j)))
      (hτ : Function.Involutive τ),
      (∀ x, τ x ≠ x) ∧
      (∀ x, (τ x : E) = J ⟨x,by
        obtain ⟨j,hj⟩ := mem_iUnion.mp x.property
        exact mem_iUnion.mpr ⟨j,prismEnds_subset (C j) hj⟩⟩) ∧
      (∀ j (x : cut j.1.1 (i₀ j)) (b : Bool),
        (τ (prismEndpointLift C j x b) : E) = prismEndMap (C j) x (!b)) ∧
      IsCoveringMap (FreeInvolutionQuotient.projection τ hτ) ∧
      (∀ x, FreeInvolutionQuotient.projection τ hτ ⁻¹'
        {FreeInvolutionQuotient.projection τ hτ x} = {x,τ x}) ∧
      let q := FreeInvolutionQuotient.projection τ hτ
      let m := fun j (x : cut j.1.1 (i₀ j)) => q (prismEndpointLift C j x false)
      (∀ j, ∃ Gcap : cut j.1.1 (i₀ j) ≃ₜ range (m j),
        ∀ x, (Gcap x : FreeInvolutionQuotient.Model τ hτ) = m j x) ∧
      (∀ j x, q (prismEndpointLift C j x true) = m j x) ∧
      (⋃ j, range (m j)) = univ := by
  classical
  dsimp only
  obtain ⟨i₀,i₁,hne,hends,flip,H,hH,hH0,hH1,hformula,C,hC,hCv,havoid,J,hJ,hJinv,hvalue,_⟩ :=
    exists_original_trimmed_partition_reflection K hK g hgi D G hG hW hZ hL haffine
      ι κ cut rim hcut hsub hrim hdis hphysical B R hB hR hcover hinter hwhole hcomp
  refine ⟨i₀,i₁,hne,hends,flip,H,hH,hH0,hH1,hformula,C,hC,hCv,havoid,J,hJ,hJinv,hvalue,?_⟩
  obtain ⟨τ,hτ,hfree,hτval,hτends,hcovering,hfiber⟩ :=
    exists_prism_endpoint_orbit_cover (E := E)
      (ι := RegularOriginalCutCell K g S D κ B) (fun j => cut j.1.1 (i₀ j))
      (fun j => prismTrim (H j)) C J hJinv hvalue
  refine ⟨τ,hτ,hfree,hτval,hτends,hcovering,hfiber,?_⟩
  exact exists_prism_endpoint_quotient_cap_charts
    (A := fun j => cut j.1.1 (i₀ j)) (B := fun j => prismTrim (H j)) C
    (fun j => (hcut j.1.1 (i₀ j)).isCompact) τ hτ hτends

end PoincareConjecture.M76.PrismBelt
