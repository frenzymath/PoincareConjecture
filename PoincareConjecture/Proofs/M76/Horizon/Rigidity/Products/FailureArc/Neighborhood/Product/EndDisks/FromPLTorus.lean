import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.OrientedComponent
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.TorusGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.GroupRank.FiniteSurface



set_option autoImplicit false
open Set Geometry
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_torus_component_model_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hS : S ⊆ frontier R) (x : S)
    (hcomponent : connectedComponentIn (frontier R) (x : X) = S)
    (O : LocalOrientation X) {p : ℝ} (hp : 0 < p)
    (T : (AddCircle p × AddCircle p) ≃ₜ S) :
    ∃ (s : Finset R) (phi : X → (s → ℝ × V3))
      (J : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X)
      (H : J.space ≃ₜ S),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      J.faces.Finite ∧ IsConnected J.space ∧ J.surfaceEulerCount = 0 ∧
      (∀ t ∈ J.faces, ∃ u ∈ J.faces, u.card = 3 ∧ t ⊆ u) ∧
      (∀ t ∈ J.faces, t.card = 2 →
        {u : Finset (s → ℝ × V3) | u ∈ J.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (∀ p ∈ J.vertices, IsConnected (J.link p).space) ∧
      PolyhedralPLInCharts e g J.space ∧
      (∀ z : J.space, (H z : X) = g z) ∧
      ∀ z ∈ J.space, phi (g z) = z := by
  classical
  obtain ⟨s, phi, J, g, H, number, sign, hphi, hphiPL, hJ, hconn,
    hpure, hcofaces, hlinks, hg, hH, hinverse, hsign⟩ :=
    he.exists_original_oriented_component_model hR hS x hcomponent O
  obtain ⟨hnt, f, hf⟩ := torus_model_fundamentalGroup_properties hp
    (H.trans T.symm) (H.symm x)
  let : Nontrivial (FundamentalGroup J.space (H.symm x)) := hnt
  have hzero := surfaceEulerCount_eq_zero_of_injective_integer_three_and_signs
    J hJ hpure hconn (by intro z hz; convert! hlinks z hz) hcofaces number sign
      (by intro t u htu a hat hau; convert! hsign t u htu a hat hau) (H.symm x) f hf
  refine ⟨s, phi, J, g, H, hphi, hphiPL, hJ, hconn, hzero, ?_, hcofaces, ?_,
    hg, (fun z => (hH z).symm), hinverse⟩
  · intro t ht
    obtain ⟨u, hu, htu, huc⟩ := hpure t ht
    exact ⟨u, hu, huc, htu⟩
  · intro z hz
    simpa only [J.faceLink_singleton_eq_link] using hlinks z hz

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
