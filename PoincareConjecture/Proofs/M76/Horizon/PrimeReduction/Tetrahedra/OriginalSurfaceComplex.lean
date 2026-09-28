import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.exists_original_surface_complex
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space)
    (hgi : InjOn g K.space) (hS : S ⊆ g '' K.space) :
    ∃ M : SimplicialComplex ℝ E, M.faces.Finite ∧
      M.space = K.space ∩ g ⁻¹' S := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (K.isCompact_space_of_finite hK)
  let H := hg.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h => Subtype.ext (hgi x.property y.property h)) |>.isEmbedding.toHomeomorph
  let pr : K.space ≃ₜ (g '' K.space) :=
    H.trans (Homeomorph.setCongr (image_eq_range g K.space).symm)
  have hsS (x : V3) (hx : x ∈ Sphere) : s.map x ∈ S := by
    rw [s.map_eq ⟨x,hx⟩]
    exact (s.parametrization ⟨x,hx⟩).property
  let q : V3 → E := fun x =>
    if hx : x ∈ Sphere then pr.symm ⟨s.map x,hS (hsS x hx)⟩ else 0
  have hqval (x : Sphere) :
      q x = (pr.symm ⟨s.map x,hS (hsS x x.property)⟩ : E) := by
    simp only [q,dif_pos x.property]
  have hqK : MapsTo q Sphere K.space := by
    intro x hx
    rw [hqval ⟨x,hx⟩]
    exact (pr.symm ⟨s.map x,hS (hsS x hx)⟩).property
  have hvalue (x : V3) (hx : x ∈ Sphere) : g (q x) = s.map x := by
    rw [hqval ⟨x,hx⟩]
    exact congrArg Subtype.val (pr.apply_symm_apply ⟨s.map x,hS (hsS x hx)⟩)
  have hqcont : ContinuousOn q Sphere := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (pr.symm.continuous.comp
      (s.piecewiseAffine.continuousOn.domRestrict.subtype_mk
        (fun x => hS (hsS x x.property))))
    convert h using 1
    funext x
    exact hqval x
  obtain ⟨A,hA,hAS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hq : FinitePiecewiseAffineOn q Sphere := by
    rw [←hAS]
    exact hg.finitePiecewiseAffineOn_lift he hgi A hA
      (hqcont.mono hAS.subset) (fun _ hx => hqK (hAS.subset hx))
      ((s.piecewiseAffine.restrict_finite A hA hAS.subset).congr
        (fun x hx => (hvalue x (hAS.subset hx)).symm))
  obtain ⟨M,hM,hMs⟩ := hq.exists_finite_triangulation_image
  refine ⟨M,hM,hMs.trans ?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨hqK hy,by change g (q y) ∈ S; rw [hvalue y hy]; exact hsS y hy⟩
  · rintro ⟨hx,hgx⟩
    let y := s.parametrization.symm ⟨g x,hgx⟩
    have hy : s.map y = g x := by
      rw [s.map_eq y]
      exact congrArg Subtype.val (s.parametrization.apply_symm_apply ⟨g x,hgx⟩)
    exact ⟨y,y.property,hgi (hqK y.property) hx ((hvalue y y.property).trans hy)⟩

theorem exists_original_sphere_family_complex
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space)
    (hgi : InjOn g K.space) {S : κ → Set X}
    (s : ∀ i, ChartwisePLSphere e (S i)) (hS : ∀ i, S i ⊆ g '' K.space) :
    ∃ M : SimplicialComplex ℝ E, M.faces.Finite ∧
      M.space = K.space ∩ g ⁻¹' (⋃ i, S i) := by
  classical
  choose C hC hCs using fun i =>
    (s i).exists_original_surface_complex he K hK hg hgi (hS i)
  obtain ⟨M,hM,hMs,_⟩ := SimplicialComplex.exists_finite_triangulation_iUnion C hC
  refine ⟨M,hM,hMs.trans ?_⟩
  simp only [hCs, preimage_iUnion, inter_iUnion]

theorem exists_original_sphere_family_complex_in_face
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space)
    (hgi : InjOn g K.space) {S : κ → Set X}
    (s : ∀ i, ChartwisePLSphere e (S i)) (hS : ∀ i, S i ⊆ g '' K.space)
    {t : Finset E} (ht : t ∈ K.faces) :
    ∃ M : SimplicialComplex ℝ E, M.faces.Finite ∧
      M.space = convexHull ℝ (t : Set E) ∩ g ⁻¹' (⋃ i, S i) := by
  classical
  obtain ⟨C,hC,hCs⟩ := exists_original_sphere_family_complex he K hK hg hgi s hS
  obtain ⟨T,hT,hTs,_⟩ := SimplicialComplex.exists_finite_triangulation_iUnion_convexHull
    (fun _ : Unit => t) (fun _ => K.indep ht)
  have hTs' : T.space = convexHull ℝ (t : Set E) := by
    rw [hTs]
    ext x
    exact ⟨fun hx => (mem_iUnion.mp hx).choose_spec, fun hx => mem_iUnion.mpr ⟨(),hx⟩⟩
  obtain ⟨M,hM,hMs⟩ := T.exists_finite_triangulation_inter C hT hC
  refine ⟨M,hM,hMs.trans ?_⟩
  rw [hTs',hCs,←inter_assoc,inter_eq_left.mpr (K.convexHull_subset_space ht)]

end PoincareConjecture.M76
