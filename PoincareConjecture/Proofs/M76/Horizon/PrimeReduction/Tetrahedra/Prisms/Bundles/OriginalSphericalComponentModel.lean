import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereCylinderModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.ExchangedComponentFinitePL
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RelativeComponentBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphericalSubregionModels

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.PrismBelt

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem hasPuncturedSphereModel_of_finitePL_spherical_product
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFg : ∀ x ∈ K.space, F (g x) = x)
    {T N : Set E} (hNK : N ⊆ K.space)
    (Q : sphere (0 : V3) 1 ≃ₜ T) (hQ : Q.IsFinitePL)
    (H : (T ×ˢ I : Set (E × ℝ)) ≃ₜ N) (hH : H.IsFinitePL) :
    HasPuncturedSphereModel e F (g '' N) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hI : (Homeomorph.refl I).IsFinitePL :=
    ⟨id, ⟨J, hJ, hJs, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩,
      fun _ => rfl⟩
  let QI := (Homeomorph.Set.prod (sphere (0 : V3) 1) I).trans
    ((Q.prodCongr (Homeomorph.refl I)).trans (Homeomorph.Set.prod T I).symm)
  have hQI : QI.IsFinitePL := hQ.prod hI
  let P := QI.trans H
  have hP : P.IsFinitePL := hQI.trans hH
  have hPc := hP.symm
  obtain ⟨_, hPc, _⟩ := hPc
  let : CompactSpace N := isCompact_iff_compactSpace.mp hPc.isCompact
  let G0 : N ≃ₜ (g '' N) := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn g N (hgi.mono hNK))
    ((hg.continuousOn.mono hNK).domRestrict.subtype_mk _)
  have hG0 (x : N) : (G0 x : X) = g x := rfl
  let G := G0.symm
  have hG (x : (g '' N : Set X)) : (G x : E) = F x := by
    have hx : g (G x) = (x : X) := congrArg Subtype.val (G0.apply_symm_apply x)
    exact (hFg (G x) (hNK (G x).property)).symm.trans (congrArg F hx)
  obtain ⟨p, ⟨L, hL, hLs, hfaces⟩, hpval⟩ := hP
  have hp : FinitePiecewiseAffineOn p L.space := ⟨L, hL, rfl, hfaces⟩
  have hpK : MapsTo p L.space K.space := by
    intro x hx
    rw [← hpval ⟨x, hLs.subset hx⟩]
    exact hNK (P ⟨x, hLs.subset hx⟩).property
  have hσ : PolyhedralPLInCharts e (g ∘ p) SphereCylinder.carrier :=
    by simpa only [hLs] using hg.comp_finitePiecewiseAffineOn L hL hp hpK
  let C := G.trans P.symm
  apply hasPuncturedSphereModel_of_original_sphere_cylinder F hF G hG C (g ∘ p) hσ
  intro z
  change g (p z) = (G0 (P z) : X)
  rw [hG0, hpval]

theorem not_finitePL_spherical_product_containing_noL3_component
    {X E ι ν : Type*} [TopologicalSpace X] [T2Space X] [Finite ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R Qcut : Set X}
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFg : ∀ x ∈ K.space, F (g x) = x)
    (hQ : IsCompact Qcut) (hPL : PLDomain e Qcut)
    (hno : HasNoPuncturedSphereComponents e F Qcut)
    (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier Qcut = frontier R ∪ ⋃ i, S i)
    {T N : Set E} (hNK : N ⊆ K.space) (hNint : MapsTo g N (interior R))
    (P : sphere (0 : V3) 1 ≃ₜ T) (hP : P.IsFinitePL)
    (H : (T ×ˢ I : Set (E × ℝ)) ≃ₜ N) (hH : H.IsFinitePL)
    {x : X} (hx : x ∈ Qcut)
    (hcontain : connectedComponentIn Qcut x ⊆ g '' N) : False := by
  have hmodel := hasPuncturedSphereModel_of_finitePL_spherical_product
    K g hg hgi F hF hFg hNK P hP H hH
  have haway : Disjoint (connectedComponentIn Qcut x) (frontier R) := by
    rw [disjoint_left]
    intro y hy hf
    obtain ⟨z, hz, rfl⟩ := hcontain hy
    exact hf.2 (hNint hz)
  obtain ⟨hDc, hDPL, hDconn, hDf⟩ :=
    hPL.component_frontier_away_from_old_boundary hQ S sS hfront hx haway
  let J := {i : ν // S i ⊆ connectedComponentIn Qcut x}
  exact hno x hx (hmodel.of_connected_spherical_subregion hDc hDPL hDconn hcontain
    (fun i : J => S i) (fun i => sS i)
    (fun i j hij => hSdis (Subtype.val_injective.ne hij)) hDf)

end PoincareConjecture.M76.PrismBelt
