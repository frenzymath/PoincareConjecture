import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.OriginalAnnulusCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.Straightening









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem exists_originalPL_annular_straightening
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {B : Set X} (A : Ann ≃ₜ B)
    (j : P2 → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ x : Ann, j x = (A x : X))
    (gamma : C(Q2, B)) (hinj : Function.Injective gamma)
    (g : V2 → X) (hg : PolyhedralPLInCharts e g Q2)
    (hgval : ∀ x : Q2, g x = (gamma x : X))
    (hdepth : ∀ x : Q2, -1 < depth 8 (A.symm (gamma x) : P2) ∧
      depth 8 (A.symm (gamma x) : P2) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ G : Ann ≃ₜ Ann, G.IsFinitePL ∧ G.symm.IsFinitePL ∧
      (∀ x : Ann, depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1 → G x = x) ∧
      G '' range (fun x => A.symm (gamma x)) = range annulusCoreCircle ∧
      ∃ q : Q2 ≃ₜ Circle, ∀ x : Q2,
        G (A.symm (gamma x)) = annulusCoreCircle (q x) := by
  let K := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hK : K.faces.Finite :=
    squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hKs : K.space = Q2 :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  let T : K.space ≃ₜ Q2 := Homeomorph.setCongr hKs
  let gammaK : C(K.space, B) := gamma.comp ⟨T, T.continuous⟩
  obtain ⟨f, hf, hfv⟩ := exists_finitePL_original_carrier_coordinates e hcompat A j hj hjval
    K hK gammaK g (hKs.symm ▸ hg) (fun x => hgval (T x))
  let delta : C(Q2, Ann) :=
    ⟨fun x => A.symm (gamma x), A.symm.continuous.comp gamma.continuous⟩
  have hvalue (x : Q2) : f x = (delta x : P2) := hfv (T.symm x)
  have hdelta : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map delta.continuous)) ≠ 1 := by
    have hi := FundamentalGroup.map_injective_of_leftInverse
      (⟨A.symm, A.symm.continuous⟩ : C(B, Ann)) ⟨A, A.continuous⟩
      A.apply_symm_apply (gamma squareRimBase)
    intro hn
    apply hessential
    apply hi
    rw [map_one]
    exact hn
  obtain ⟨G, hG, hGi, hGrim, hrange, q, hq⟩ :=
    exists_finitePL_annular_straightening delta (A.symm.injective.comp hinj)
      f (hKs ▸ hf) hvalue hdepth hdelta
  refine ⟨G, hG, hGi, ?_, hrange, q, hq⟩
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨z, rfl⟩ := (range_annulusRimPoint false).symm.subset hx
    exact hGrim false z
  · obtain ⟨z, rfl⟩ := (range_annulusRimPoint true).symm.subset hx
    exact hGrim true z

end PoincareConjecture.M76.Dehn
