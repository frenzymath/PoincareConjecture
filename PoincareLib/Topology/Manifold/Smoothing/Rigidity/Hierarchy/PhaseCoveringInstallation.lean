import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.Phase.RecognizedComponentPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.Phase.SquareParametrization
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.Phase.FiberwiseLocalHomeomorph
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Maps.Adjustments.CollarPhaseGroups

/-!
# Installing recognized phase coverings in the original source collar

The original ambient injection supplies every component group injection.
Only the finite torus recognition data remain geometric inputs: covering
maps, their homotopies, and the supported original PL adjustment are all
constructed here, including the complete product formula on a smaller strip.
-/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_recognized_phase_covering
    {E ι κ η : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite η]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : E × ℝ → X0)
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : J.space ×ˢ Icc (-r) r => c z))
    (hopen : ∀ eps : ℝ, 0 < eps → eps ≤ r → IsOpen (c '' (J.space ×ˢ Ioo (-eps) eps)))
    (theta : C0) (sigma : ℝ) (hsigma : sigma ≠ 0)
    (H : J.space ≃ₜ (hamiltonZeroCircleMap phi ⁻¹' {theta} : Set X0))
    (hzero : ∀ x : J.space, c (x, 0) = H x)
    (hinj : ∀ x : hamiltonZeroCircleMap phi ⁻¹' {theta},
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C((hamiltonZeroCircleMap phi ⁻¹' {theta} : Set X0), X0)) x))
    (hproduct : ∀ x : J.space, ∀ t ∈ Icc (-r) r,
      Q0 (hamiltonZeroAmbientMap phi (c (x, t))) =
        ((Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1, theta + ((sigma * t : ℝ) : C0)))
    (K : η → SimplicialComplex ℝ E)
    (hcover : (⋃ i, (K i).space) = J.space) (hK : ∀ i, (K i).faces.Finite)
    (hdisjoint : Pairwise fun i j => Disjoint (K i).space (K j).space)
    (h : ∀ i, (C0 × C0) ≃ₜ (K i).space)
    (hparam : ∀ i, PolyhedralPLInCharts d
      (hamiltonZeroCollarPhaseTarget (K i) ⟨(h i).symm, (h i).symm.continuous⟩ theta)
      (K i).space) :
    ∃ (g : C(J.space, C0 × C0)) (psi : C(H0, H0)) (C : Set X0),
      IsCoveringMap g ∧
      IsCompact C ∧ C ⊆ c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2)) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      Nonempty (phi.HomotopyRel psi (hamiltonZeroAmbientEquiv '' C)ᶜ) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      (∀ x, x ∉ C → hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      (∀ x : J.space, ∀ t ∈ Icc (-(r / 4)) (r / 4),
        Q0 (hamiltonZeroAmbientMap psi (c (x, t))) = (g x, theta + ((sigma * t : ℝ) : C0))) ∧
      IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
        (c '' (J.space ×ˢ Ioo (-(r / 4)) (r / 4))) ∧
      IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
        (hamiltonZeroCircleMap phi ⁻¹' {theta}) := by
  have hf := hamiltonZeroCollarTangentialMap_pi1_injective phi F J hr c hc theta H hzero hinj
  obtain ⟨_, g, _, hg, _, ⟨G⟩, hgPL⟩ :=
    PhaseCovering.exists_PL_coveringMap_of_recognized_components
      J K hcover hK hdisjoint hJ hd theta
      (hamiltonZeroCollarTangentialMap phi J hr c hc) hf h hparam
  obtain ⟨psi, C, hC, hCU, hpsi, Hpsi, Fpsi, Hext, hnormal, hfixed, hfull, hlocal, hbase⟩ :=
    hphi.exists_hamiltonZero_covering_phase_adjustment hd F J hJ hr c hc hi hopen
      theta sigma hsigma hproduct g hg G hgPL
  refine ⟨g, psi, C, hg, hC, hCU, hpsi, Hpsi, Fpsi, Hext, hnormal, hfixed, hfull, hlocal,
    hbase.mono ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := H.surjective ⟨x, hx⟩
  refine ⟨(y, 0), ⟨y.property, rfl⟩, ?_⟩
  exact (hzero y).trans (congrArg Subtype.val hy)

/- The square producer needs only its forward finite PL formulas and exact
periodic fibers. Both the inverse original-atlas certificate and the phase
covering installed in the original collar are constructed here. -/
theorem exists_hamiltonZero_phase_covering_of_square_maps
    {E ι κ η : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite η]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : E × ℝ → X0)
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : J.space ×ˢ Icc (-r) r => c z))
    (hopen : ∀ eps : ℝ, 0 < eps → eps ≤ r → IsOpen (c '' (J.space ×ˢ Ioo (-eps) eps)))
    (theta : C0) (sigma : ℝ) (hsigma : sigma ≠ 0)
    (H : J.space ≃ₜ (hamiltonZeroCircleMap phi ⁻¹' {theta} : Set X0))
    (hzero : ∀ x : J.space, c (x, 0) = H x)
    (hinj : ∀ x : hamiltonZeroCircleMap phi ⁻¹' {theta},
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C((hamiltonZeroCircleMap phi ⁻¹' {theta} : Set X0), X0)) x))
    (hproduct : ∀ x : J.space, ∀ t ∈ Icc (-r) r,
      Q0 (hamiltonZeroAmbientMap phi (c (x, t))) =
        ((Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1, theta + ((sigma * t : ℝ) : C0)))
    (K : η → SimplicialComplex ℝ E)
    (hcover : (⋃ i, (K i).space) = J.space) (hK : ∀ i, (K i).faces.Finite)
    (hdisjoint : Pairwise fun i j => Disjoint (K i).space (K j).space)
    (u : η → ℝ × ℝ → E)
    (hu : ∀ i, FinitePiecewiseAffineOn (u i)
      (Icc 0 (4 * (16 : ℝ)) ×ˢ Icc 0 (4 * (16 : ℝ))))
    (himage : ∀ i, u i '' (Icc 0 (4 * (16 : ℝ)) ×ˢ Icc 0 (4 * (16 : ℝ))) = (K i).space)
    (hfib : ∀ i (z w : PeriodicSquare.Square (4 * (16 : ℝ))),
      u i (z.1, z.2) = u i (w.1, w.2) ↔
        PeriodicSquare.projection (4 * (16 : ℝ)) z =
          PeriodicSquare.projection (4 * (16 : ℝ)) w) :
    ∃ (g : C(J.space, C0 × C0)) (psi : C(H0, H0)) (C : Set X0),
      IsCoveringMap g ∧
      IsCompact C ∧ C ⊆ c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2)) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      Nonempty (phi.HomotopyRel psi (hamiltonZeroAmbientEquiv '' C)ᶜ) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      (∀ x, x ∉ C → hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      (∀ x : J.space, ∀ t ∈ Icc (-(r / 4)) (r / 4),
        Q0 (hamiltonZeroAmbientMap psi (c (x, t))) = (g x, theta + ((sigma * t : ℝ) : C0))) ∧
      IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
        (c '' (J.space ×ˢ Ioo (-(r / 4)) (r / 4))) ∧
      IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
        (hamiltonZeroCircleMap phi ⁻¹' {theta}) := by
  choose h hval hparam using fun i => exists_PL_torus_parametrization_of_square_map
    hd (K i) (hK i) (u i) (hu i) (himage i) (hfib i)
  exact exists_hamiltonZero_recognized_phase_covering hd phi hphi F J hJ hr c hc hi hopen
    theta sigma hsigma H hzero hinj hproduct K hcover hK hdisjoint h
    (fun i => hparam i theta)

/- Direct source-map facade for the same installation: the producer's exact
fibers and finite PL representative are unpacked internally. -/
theorem exists_hamiltonZero_phase_covering_of_source_square_maps
    {E ι κ η : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite η]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : E × ℝ → X0)
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : J.space ×ˢ Icc (-r) r => c z))
    (hopen : ∀ eps : ℝ, 0 < eps → eps ≤ r → IsOpen (c '' (J.space ×ˢ Ioo (-eps) eps)))
    (theta : C0) (sigma : ℝ) (hsigma : sigma ≠ 0)
    (H : J.space ≃ₜ (hamiltonZeroCircleMap phi ⁻¹' {theta} : Set X0))
    (hzero : ∀ x : J.space, c (x, 0) = H x)
    (hinj : ∀ x : hamiltonZeroCircleMap phi ⁻¹' {theta},
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C((hamiltonZeroCircleMap phi ⁻¹' {theta} : Set X0), X0)) x))
    (hproduct : ∀ x : J.space, ∀ t ∈ Icc (-r) r,
      Q0 (hamiltonZeroAmbientMap phi (c (x, t))) =
        ((Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1, theta + ((sigma * t : ℝ) : C0)))
    (K : η → SimplicialComplex ℝ E)
    (hcover : (⋃ i, (K i).space) = J.space) (hK : ∀ i, (K i).faces.Finite)
    (hdisjoint : Pairwise fun i j => Disjoint (K i).space (K j).space)
    (M : ∀ i, PoincareMT.M76.PeriodicSquare.SourceSquareMap (4 * (16 : ℝ)) (K i)) :
    ∃ (g : C(J.space, C0 × C0)) (psi : C(H0, H0)) (C : Set X0),
      IsCoveringMap g ∧ IsCompact C ∧ C ⊆ c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2)) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      Nonempty (phi.HomotopyRel psi (hamiltonZeroAmbientEquiv '' C)ᶜ) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      (∀ x, x ∉ C → hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      (∀ x : J.space, ∀ t ∈ Icc (-(r / 4)) (r / 4),
        Q0 (hamiltonZeroAmbientMap psi (c (x, t))) = (g x, theta + ((sigma * t : ℝ) : C0))) ∧
      IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
        (c '' (J.space ×ˢ Ioo (-(r / 4)) (r / 4))) ∧
      IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
        (hamiltonZeroCircleMap phi ⁻¹' {theta}) := by
  obtain ⟨u, hu, himage, hfib⟩ :=
    PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_family_ambient_data
      (4 * (16 : ℝ)) M
  exact exists_hamiltonZero_phase_covering_of_square_maps hd phi hphi F J hJ hr c hc hi hopen
    theta sigma hsigma H hzero hinj hproduct K hcover hK hdisjoint u hu himage hfib

end PoincareMT.M76
