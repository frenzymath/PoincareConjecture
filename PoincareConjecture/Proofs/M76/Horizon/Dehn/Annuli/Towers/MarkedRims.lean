import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.ProtectedTower
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Coordinates.ShellRetraction
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Dehn.OriginalRimFrontier

set_option autoImplicit false
open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

namespace Geometry.OriginalPLTower.Stage

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {M F ι : Type*} [TopologicalSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {e : ι → OpenPartialHomeomorph M F}
  {S : SimplicialComplex ℝ (V1 × V2)} {f : (V1 × V2) → M}
  {r : M → ℝ} {C : Set M} (s : Stage e S f r C)

def annulusRimMap (b : Bool) (u : V2) : s.Carrier := s.sourceMap (ProtectedAnnulus.endpoint b, u)

theorem annulusRim_polyhedral (hS : S.space = ProtectedAnnulus.source) (b : Bool) :
    PolyhedralPLInCharts s.charts (s.annulusRimMap b) Q2 := by
  let K := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hK := squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hKs : K.space = Q2 :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  let g : V2 →ᴬ[ℝ] (V1 × V2) :=
    (ContinuousAffineMap.const ℝ V2 (ProtectedAnnulus.endpoint b)).prod (ContinuousAffineMap.id ℝ V2)
  have hg : FinitePiecewiseAffineOn g K.space :=
    (K.affineOnFaces_affine g).finitePiecewiseAffineOn hK
  have hmap : MapsTo g K.space S.space := by
    intro u hu
    apply hS.symm.subset
    exact ⟨sphere_subset_closedBall (endpoint_mem_sphere b), hKs.subset hu⟩
  have h := s.sourcePL.comp_finitePiecewiseAffineOn K hK hg hmap
  rw [hKs] at h
  exact h

def annulusRim (hS : S.space = ProtectedAnnulus.source) (b : Bool) : C(Q2, s.Carrier) :=
  ⟨fun u ↦ s.annulusRimMap b u, (s.annulusRim_polyhedral hS b).continuousOn.domRestrict⟩

theorem annulusRim_projection (hS : S.space = ProtectedAnnulus.source)
    (b : Bool) (u : Q2) : s.projection (s.annulusRim hS b u) = f (ProtectedAnnulus.endpoint b, u) :=
  s.source_eq _ (hS.symm.subset
    ⟨sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩)

theorem annulusRim_range_subset (hS : S.space = ProtectedAnnulus.source) (b : Bool) :
    range (s.annulusRim hS b) ⊆ s.sourceMap '' S.space := by
  rintro x ⟨u, rfl⟩
  exact ⟨(ProtectedAnnulus.endpoint b, u), hS.symm.subset
    ⟨sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩, rfl⟩

theorem annulusRim_isClosedEmbedding (hS : S.space = ProtectedAnnulus.source)
    (b : Bool) (hinj : Function.Injective (fun u : Q2 ↦ f (ProtectedAnnulus.endpoint b, u))) :
    IsClosedEmbedding (s.annulusRim hS b) := by
  let : CompactSpace Q2 := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V2) 1)
  apply (s.annulusRim hS b).continuous.isClosedEmbedding
  intro u v huv
  apply hinj
  simpa only [s.annulusRim_projection hS] using congrArg s.projection huv

theorem annulusRim_ranges_disjoint (hS : S.space = ProtectedAnnulus.source)
    (hdis : Disjoint (range (fun u : Q2 ↦ f (ProtectedAnnulus.endpoint false, u)))
      (range (fun u : Q2 ↦ f (ProtectedAnnulus.endpoint true, u)))) :
    Disjoint (range (s.annulusRim hS false)) (range (s.annulusRim hS true)) := by
  apply disjoint_left.mpr
  rintro x ⟨u, rfl⟩ ⟨v, hv⟩
  have hp := congrArg s.projection hv
  rw [s.annulusRim_projection hS, s.annulusRim_projection hS] at hp
  exact disjoint_left.mp hdis ⟨u, rfl⟩ ⟨v, hp⟩

noncomputable def annulusRimHomotopy (hS : S.space = ProtectedAnnulus.source) :
    (s.annulusRim hS false).Homotopy (s.annulusRim hS true) where
  toContinuousMap := s.source.comp
    ⟨(Homeomorph.setCongr hS).symm ∘ cylinder,
      (Homeomorph.setCongr hS).symm.continuous.comp cylinder.continuous⟩
  map_zero_left := by
    intro u
    change s.source ((Homeomorph.setCongr hS).symm (cylinder (0, u))) = _
    rw [cylinder_zero]
    rfl
  map_one_left := by
    intro u
    change s.source ((Homeomorph.setCongr hS).symm (cylinder (1, u))) = _
    rw [cylinder_one]
    rfl

theorem annulusRimHomotopy_mem_source_image (hS : S.space = ProtectedAnnulus.source)
    (t : unitInterval) (u : Q2) :
    s.annulusRimHomotopy hS (t, u) ∈ s.sourceMap '' S.space := by
  exact ⟨(cylinder (t, u) : (Fin 1 → ℝ) × (Fin 2 → ℝ)),
    hS.symm.subset (cylinder (t, u)).property, rfl⟩

theorem annulusRim_mem_frontier (hS : S.space = ProtectedAnnulus.source)
    {R : Set M} {N : Set s.Carrier} (hN : IsClosed N)
    (hDN : s.sourceMap '' S.space ⊆ N) (hNR : N ⊆ s.projection ⁻¹' R)
    (b : Bool) (hfront : ∀ u : Q2, f (ProtectedAnnulus.endpoint b, u) ∈ frontier R)
    (u : Q2) : s.annulusRim hS b u ∈ frontier N :=
  s.source_mem_frontier_of_original_rim hN hDN hNR
    (hS.symm.subset ⟨sphere_subset_closedBall (endpoint_mem_sphere b), u.property⟩)
    (hfront u)

end Geometry.OriginalPLTower.Stage

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable (L : Submodule ℤ V2) {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h)

theorem prescribed_rim_injective
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source)
    {f : (V1 × V2) → chartShell L retained}
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x))
    (b : Bool) : Function.Injective (fun u : Q2 ↦ f (endpoint b, u)) := by
  intro u v huv
  apply (rim_isClosedEmbedding h hsource b).injective
  apply Subtype.ext
  have hv := congrArg (Subtype.val : chartShell L retained → V3) huv
  rw [hvalues _ ⟨endpoint_mem_sphere b, u.property⟩,
    hvalues _ ⟨endpoint_mem_sphere b, v.property⟩] at hv
  exact hv

theorem prescribed_rim_ranges_disjoint
    (hsource : closedBall (0 : V1) 1 ×ˢ (univ : Set V2) ⊆ h.source)
    {f : (V1 × V2) → chartShell L retained}
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x)) :
    Disjoint (range (fun u : Q2 ↦ f (endpoint false, u)))
      (range (fun u : Q2 ↦ f (endpoint true, u))) := by
  apply disjoint_left.mpr
  rintro x ⟨u, rfl⟩ ⟨v, hv⟩
  have heq : rim h hsource true v = rim h hsource false u := by
    apply Subtype.ext
    have hh := congrArg (Subtype.val : chartShell L retained → V3) hv
    rw [hvalues _ ⟨endpoint_mem_sphere true, v.property⟩,
      hvalues _ ⟨endpoint_mem_sphere false, u.property⟩] at hh
    exact hh
  exact disjoint_left.mp (disjoint_rim_ranges h hsource)
    ⟨u, rfl⟩ ⟨v, heq⟩

variable {S : SimplicialComplex ℝ (V1 × V2)}
  {f : (V1 × V2) → chartShell L retained}
  {r : chartShell L retained → ℝ} {C : Set (chartShell L retained)}
  (s : Geometry.OriginalPLTower.Stage (fun _ : Unit ↦
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe
      (chartShell L retained) (chartShell_nonempty L retained)) S f r C)

theorem stage_radial_rim (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x))
    (b : Bool) (u : Q2) :
    chartShellRadial L retained (s.projection (s.annulusRim hS b u)) = u := by
  rw [s.annulusRim_projection hS]
  exact chartShellRadial_prescribed L retained b u
    (hvalues _ ⟨endpoint_mem_sphere b, u.property⟩)

theorem stage_rim_class_ne_one (hS : S.space = source)
    (hvalues : ∀ x ∈ sphere (0 : V1) 1 ×ˢ Q2, (f x : V3) = h (coordinates x))
    (b : Bool) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map (s.annulusRim hS b).continuous)) ≠ 1 :=
  squareRimLoop_map_class_ne_one_of_retraction (s.annulusRim hS b)
    ((chartShellRadial L retained).comp s.projection)
    (stage_radial_rim L retained s hS hvalues b)

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
