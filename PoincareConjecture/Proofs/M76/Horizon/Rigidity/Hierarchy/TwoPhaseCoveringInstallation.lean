import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.RecognizedComponentPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.SquareParametrization
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.FiberwiseLocalHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.CollarPhaseGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.TwoPhaseCoverings

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_two_phase_coverings_of_square_maps
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {η : Bool → Type*} [∀ s, Finite (η s)]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (J : Bool → SimplicialComplex ℝ E) (hJ : ∀ s, (J s).faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : Bool → E × ℝ → X0)
    (hc : ∀ s, PolyhedralPLInCharts e (c s) ((J s).space ×ˢ Icc (-r) r))
    (hi : ∀ s, Topology.IsEmbedding (fun z : (J s).space ×ˢ Icc (-r) r => c s z))
    (hopen : ∀ s, ∀ eps : ℝ, 0 < eps → eps ≤ r →
      IsOpen (c s '' ((J s).space ×ˢ Ioo (-eps) eps)))
    (hdis : Disjoint (c false '' ((J false).space ×ˢ Icc (-r) r))
      (c true '' ((J true).space ×ˢ Icc (-r) r)))
    (theta : Bool → C0) (sigma : Bool → ℝ) (hsigma : ∀ s, sigma s ≠ 0)
    (H : ∀ s, (J s).space ≃ₜ (hamiltonZeroCircleMap phi ⁻¹' {theta s} : Set X0))
    (hzero : ∀ s, ∀ x : (J s).space, c s (x, 0) = H s x)
    (hinj : ∀ s, ∀ x : hamiltonZeroCircleMap phi ⁻¹' {theta s},
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C((hamiltonZeroCircleMap phi ⁻¹' {theta s} : Set X0), X0)) x))
    (hproduct : ∀ s, ∀ x : (J s).space, ∀ t ∈ Icc (-r) r,
      Q0 (hamiltonZeroAmbientMap phi (c s (x, t))) =
        ((Q0 (hamiltonZeroAmbientMap phi (c s (x, 0)))).1,
          theta s + ((sigma s * t : ℝ) : C0)))
    (K : ∀ s, η s → SimplicialComplex ℝ E)
    (hcover : ∀ s, (⋃ i, (K s i).space) = (J s).space)
    (hK : ∀ s i, (K s i).faces.Finite)
    (hdisjoint : ∀ s, Pairwise fun i j => Disjoint (K s i).space (K s j).space)
    (u : ∀ s, η s → ℝ × ℝ → E)
    (hu : ∀ s i, FinitePiecewiseAffineOn (u s i) (Icc 0 p ×ˢ Icc 0 p))
    (himage : ∀ s i, u s i '' (Icc 0 p ×ˢ Icc 0 p) = (K s i).space)
    (hfib : ∀ s i (z w : PeriodicSquare.Square p),
      u s i (z.1, z.2) = u s i (w.1, w.2) ↔
        PeriodicSquare.projection p z = PeriodicSquare.projection p w) :
    ∃ (g : ∀ s, C((J s).space, C0 × C0)) (psi : C(H0, H0)) (A : Set X0),
      (∀ s, IsCoveringMap (g s)) ∧ IsCompact A ∧
      A ⊆ (c false '' ((J false).space ×ˢ Ioo (-(r / 2)) (r / 2))) ∪
        (c true '' ((J true).space ×ˢ Ioo (-(r / 2)) (r / 2))) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      (∀ s, ∀ x : (J s).space, ∀ t ∈ Icc (-(r / 4)) (r / 4),
        Q0 (hamiltonZeroAmbientMap psi (c s (x, t))) =
          (g s x, theta s + ((sigma s * t : ℝ) : C0))) ∧
      ∀ s, IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
        (c s '' ((J s).space ×ˢ Ioo (-(r / 4)) (r / 4))) := by
  classical
  choose h hval hparam using fun s i => exists_PL_torus_parametrization_of_square_map
    hd (K s i) (hK s i) (u s i) (hu s i) (himage s i) (hfib s i)
  have hf (s : Bool) := hamiltonZeroCollarTangentialMap_pi1_injective phi F
    (J s) hr (c s) (hc s) (theta s) (H s) (hzero s) (hinj s)
  have hex (s : Bool) := PhaseCovering.exists_PL_coveringMap_of_recognized_components
    (J s) (K s) (hcover s) (hK s) (hdisjoint s) (hJ s) hd (theta s)
    (hamiltonZeroCollarTangentialMap phi (J s) hr (c s) (hc s)) (hf s) (h s)
    (fun i => hparam s i (theta s))
  choose M g hdet hg hformula HG hgPL using hex
  obtain ⟨psi, A, hA, hAsub, hpsi, Hpsi, Fpsi, hnormal, hfixed, hfull, hlocal⟩ :=
    hphi.exists_hamiltonZero_two_covering_phase_adjustments hd F J hJ hr c hc hi hopen hdis
      theta sigma hsigma hproduct g hg (fun s => (HG s).some) hgPL
  exact ⟨g, psi, A, hg, hA, hAsub, hpsi, Hpsi, Fpsi, hnormal, hfixed, hfull, hlocal⟩

theorem exists_hamiltonZero_two_phase_coverings_of_source_square_maps
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {η : Bool → Type*} [∀ s, Finite (η s)]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (J : Bool → SimplicialComplex ℝ E) (hJ : ∀ s, (J s).faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : Bool → E × ℝ → X0)
    (hc : ∀ s, PolyhedralPLInCharts e (c s) ((J s).space ×ˢ Icc (-r) r))
    (hi : ∀ s, Topology.IsEmbedding (fun z : (J s).space ×ˢ Icc (-r) r => c s z))
    (hopen : ∀ s, ∀ eps : ℝ, 0 < eps → eps ≤ r →
      IsOpen (c s '' ((J s).space ×ˢ Ioo (-eps) eps)))
    (hdis : Disjoint (c false '' ((J false).space ×ˢ Icc (-r) r))
      (c true '' ((J true).space ×ˢ Icc (-r) r)))
    (theta : Bool → C0) (sigma : Bool → ℝ) (hsigma : ∀ s, sigma s ≠ 0)
    (H : ∀ s, (J s).space ≃ₜ (hamiltonZeroCircleMap phi ⁻¹' {theta s} : Set X0))
    (hzero : ∀ s, ∀ x : (J s).space, c s (x, 0) = H s x)
    (hinj : ∀ s, ∀ x : hamiltonZeroCircleMap phi ⁻¹' {theta s},
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C((hamiltonZeroCircleMap phi ⁻¹' {theta s} : Set X0), X0)) x))
    (hproduct : ∀ s, ∀ x : (J s).space, ∀ t ∈ Icc (-r) r,
      Q0 (hamiltonZeroAmbientMap phi (c s (x, t))) =
        ((Q0 (hamiltonZeroAmbientMap phi (c s (x, 0)))).1,
          theta s + ((sigma s * t : ℝ) : C0)))
    (K : ∀ s, η s → SimplicialComplex ℝ E)
    (hcover : ∀ s, (⋃ i, (K s i).space) = (J s).space)
    (hK : ∀ s i, (K s i).faces.Finite)
    (hdisjoint : ∀ s, Pairwise fun i j => Disjoint (K s i).space (K s j).space)
    (M : ∀ s i, PoincareConjecture.M76.PeriodicSquare.SourceSquareMap p (K s i)) :
    ∃ (g : ∀ s, C((J s).space, C0 × C0)) (psi : C(H0, H0)) (A : Set X0),
      (∀ s, IsCoveringMap (g s)) ∧ IsCompact A ∧
      A ⊆ (c false '' ((J false).space ×ˢ Ioo (-(r / 2)) (r / 2))) ∪
        (c true '' ((J true).space ×ˢ Ioo (-(r / 2)) (r / 2))) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      (∀ s, ∀ x : (J s).space, ∀ t ∈ Icc (-(r / 4)) (r / 4),
        Q0 (hamiltonZeroAmbientMap psi (c s (x, t))) =
          (g s x, theta s + ((sigma s * t : ℝ) : C0))) ∧
      ∀ s, IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
        (c s '' ((J s).space ×ˢ Ioo (-(r / 4)) (r / 4))) := by
  obtain ⟨u, hu, himage, hfib⟩ :=
    PoincareConjecture.M76.PeriodicSquare.SourceSquareMap.exists_dependent_family_ambient_data p M
  exact exists_hamiltonZero_two_phase_coverings_of_square_maps hd phi hphi F J hJ hr c hc hi
    hopen hdis theta sigma hsigma H hzero hinj hproduct K hcover hK hdisjoint u hu himage hfib

end PoincareConjecture.M76
