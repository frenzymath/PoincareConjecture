import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.GroupRank.FiniteSurface
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.GroupRank.LatticeWinding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Models.OriginalComponentGroups









set_option autoImplicit false
open Set Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

open Classical in
theorem PLDomain.exists_original_component_euler_zero
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {N : Set X0} (he : PLDomain e N) (hN : IsCompact N)
    (x : X0) (hx : x ∈ frontier N)
    (hnt : Nontrivial (FundamentalGroup (connectedComponentIn (frontier N) x)
      ⟨x, mem_connectedComponentIn hx⟩))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(connectedComponentIn (frontier N) x, X0)) ⟨x, mem_connectedComponentIn hx⟩)) :
    ∃ (s : Finset N) (phi : X0 → (s → ℝ × V3))
      (J : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X0)
      (H : J.space ≃ₜ connectedComponentIn (frontier N) x),
      Continuous phi ∧
      (∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target) ∧
      J.faces.Finite ∧ (∀ t ∈ J.faces, t.card ≤ 3) ∧
      PolyhedralPLInCharts e g J.space ∧
      (∀ z : J.space, (H z : X0) = g z) ∧
      (∀ z ∈ J.space, phi (g z) = z) ∧ J.surfaceEulerCount = 0 := by
  obtain ⟨s, phi, J, g, H, hphi, hphiPL, hJ, hconn, hpure, hcofaces, hlinks,
    hgPL, hH, hinverse, number, sign, hcancel⟩ :=
    he.exists_original_oriented_component e hcover hcompat hN x hx
  let b : connectedComponentIn (frontier N) x := ⟨x, mem_connectedComponentIn hx⟩
  obtain ⟨_, _, hnt', hinj'⟩ :=
    originalComponentGroups_at_original_basepoint g H hH b hnt hinj
  let : Nontrivial (FundamentalGroup J.space (H.symm b)) := hnt'
  let f := (hamiltonZeroAmbientIntegerMap
    (originalComponentAmbientMap g H hH (H.symm b))).comp
      (FundamentalGroup.map (originalComponentAmbientMap g H hH) (H.symm b))
  have hf : Function.Injective f :=
    (hamiltonZeroAmbientIntegerMap_injective _).comp hinj'
  have hzero := surfaceEulerCount_eq_zero_of_injective_integer_three_and_signs
    J hJ hpure hconn (by intro v hv; convert! hlinks v hv) hcofaces number sign
      (by intro t u htu a hat hau; convert! hcancel t u htu a hat hau) (H.symm b) f hf
  refine ⟨s, phi, J, g, H, hphi, hphiPL, hJ, ?_, hgPL, hH, hinverse, hzero⟩
  intro t ht
  obtain ⟨u, _, htu, hu⟩ := hpure t ht
  exact (Finset.card_le_card htu).trans_eq hu

end PoincareConjecture.M76
