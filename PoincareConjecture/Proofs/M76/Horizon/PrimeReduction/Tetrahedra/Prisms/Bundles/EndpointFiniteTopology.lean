import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointOrbitCover
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteCarrierLocalPathConnected



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_finite_prism_end_triangulation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B : Set E} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (hH : H.IsFinitePL)
    (b : Bool) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧
      K.space = range (fun a : A => (prismEndMap H a b : E)) := by
  obtain ⟨f,hf,hval⟩ := hH
  obtain ⟨L,hL,hLs,hLf⟩ := hf
  have hp : FinitePiecewiseAffineOn (Prod.fst : E × ℝ → E) (A ×ˢ I) :=
    ⟨L,hL,hLs,L.affineOnFaces_affine
      (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap⟩
  obtain ⟨N,hN,hNs⟩ := hp.exists_finite_triangulation_image
  have hNA : N.space = A := hNs.trans (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy.1
    · intro hx; exact ⟨(x,0),⟨hx,by norm_num⟩,rfl⟩)
  let a : E →ᴬ[ℝ] (E × ℝ) := (ContinuousAffineMap.id ℝ E).prod
    (ContinuousAffineMap.const ℝ E (if b then (1 : ℝ) else 0))
  have ha : FinitePiecewiseAffineOn a A :=
    ⟨N,hN,hNA,N.affineOnFaces_affine a⟩
  have hamap : MapsTo a A (A ×ˢ I) := by
    intro x hx
    exact ⟨hx,by cases b <;> norm_num [a]⟩
  obtain ⟨K,hK,hKs⟩ := (FinitePiecewiseAffineOn.comp
    ⟨L,hL,hLs,hLf⟩ ha hamap).exists_finite_triangulation_image
  refine ⟨K,hK,hKs.trans ?_⟩
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,hval ⟨a x,hamap hx⟩⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x,x.property,(hval ⟨a x,hamap x.property⟩).symm⟩

theorem exists_finite_prism_endpoint_triangulation
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] {A B : ι → Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i) (hH : ∀ i, (H i).IsFinitePL) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = ⋃ i, prismEnds (H i) := by
  classical
  choose K hK hKs using fun z : ι × Bool =>
    exists_finite_prism_end_triangulation (H z.1) (hH z.1) z.2
  obtain ⟨N,hN,hNs,_⟩ := SimplicialComplex.exists_finite_triangulation_iUnion K hK
  refine ⟨N,hN,hNs.trans ?_⟩
  ext x
  simp only [mem_iUnion,hKs,mem_range,prismEnds]
  constructor
  · rintro ⟨⟨i,b⟩,a,ha⟩
    exact ⟨i,⟨a,b⟩,ha⟩
  · rintro ⟨i,⟨a,b⟩,ha⟩
    exact ⟨⟨i,b⟩,a,ha⟩

theorem locallyPathConnectedSpace_prism_endpoints
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] {A B : ι → Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i) (hH : ∀ i, (H i).IsFinitePL) :
    LocallyPathConnectedSpace (⋃ i, prismEnds (H i) : Set E) := by
  obtain ⟨K,hK,hKs⟩ := exists_finite_prism_endpoint_triangulation H hH
  rw [← hKs]
  exact K.locallyPathConnectedSpace_of_finite hK

end PoincareConjecture.M76.PrismBelt
