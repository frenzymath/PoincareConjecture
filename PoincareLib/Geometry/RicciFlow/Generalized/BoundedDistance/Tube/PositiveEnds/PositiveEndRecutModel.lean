import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.PositiveEnds.PositiveEndRecut
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderComponentModel
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckGraphIsotopy
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Local.Geometry.LocalPairIsotopy
import PoincareLib.Topology.Manifold.NeckCap.Isotopy.Composition

/-!
# The smooth model on the literal positive recut

Morgan--Tian Claim 10.8, p. 254; M28 derivation 94. The negative neck
cross-section has its actual graph isotopy in the original tube. Smooth
adaptation and the full component identity therefore give a smooth model
on exactly the constructed recut, with explicit affine inverse height.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {U : TopologicalSpace.Opens M}

/-- The recut is a literal positive tail of an adapted smooth model and
has its own smooth cylinder model with the exact rescaled height. Source:
MT Claim 10.8, p. 254; M28 derivation 94. -/
theorem exists_positive_recut_model
    (N : EpsilonNeck g) (T : OpenCylinderModel (U : Set M))
    (hNU : N.carrier ⊆ U)
    (hisotopy : SmoothSphereIsotopicIn (U : Set M) N.central_sphere T.middleSphere)
    {P : Set M} (hPU : P ⊆ U) (hPo : IsOpen P) (hPc : IsConnected P)
    (hPcl : closure P = P ∪ N.central_sphere)
    (habove : N.aboveGraph_m28 (fun _ => 0) ⊆ P)
    (hbelow : Disjoint (N.belowGraph_m28 (fun _ => 0)) P)
    {a b : ℝ} (ha : -N.epsilon⁻¹ < a) (ha0 : a < 0)
    (hb0 : 0 < b) (hb : b < N.epsilon⁻¹) :
    let W := P ∪ N.region a b
    ∃ A : OpenCylinderModel (U : Set M),
      A.middleSphere = N.coordinate_map '' (univ ×ˢ ({a} : Set ℝ)) ∧
      W = A.tail true (1 / 2) ∧
      ∃ R : OpenCylinderModel W,
        R.coordinate = (fun z => A.coordinate (z.1, 1 / 2 + (1 - 1 / 2) * z.2)) ∧
        R.inverse =
          (fun x => ((A.inverse x).1, ((A.inverse x).2 - 1 / 2) / (1 - 1 / 2))) := by
  let W := P ∪ N.region a b
  let S := N.coordinate_map '' (univ ×ˢ ({a} : Set ℝ))
  obtain ⟨hWo, hWc, _hSW, hfront, _hclosure, hcomponent, _hslab⟩ :=
    N.recut_positive_component hPo hPc hPcl habove hbelow ha ha0 hb0 hb
  have hWU : W ⊆ (U : Set M) := union_subset hPU (fun _ hx => hNU hx.1)
  have hWS : W ⊆ Sᶜ := by
    intro x hx hxS
    have hf : x ∈ frontier W := hfront.symm ▸ hxS
    exact (hWo.frontier_eq ▸ hf).2 hx
  have hSrange : S = range (fun q : UnitTwoSphere => N.coordinate_map (q, a)) := by
    ext x
    constructor
    · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
      have hs' : s = a := hs
      exact ⟨q, by rw [hs']⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q, a), ⟨mem_univ _, rfl⟩, rfl⟩
  have hS : SmoothSphereIsotopicIn (U : Set M) S T.middleSphere := by
    rw [hSrange]
    exact ((neck_graph_isotopic_central N (fun _ => a) contMDiff_const
      (fun _ => ⟨ha, ha0.trans (hb0.trans hb)⟩)).mono_m28 hNU).trans hisotopy
  obtain ⟨A, hAS, hWA⟩ := T.exists_oriented_model_of_component hS hWc
    (fun _ hx => ⟨hWU hx, hWS hx⟩) hcomponent
  refine ⟨A, hAS, hWA, ?_⟩
  have hR := A.exists_positive_tail_model (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  rwa [← hWA] at hR

end PoincareMT.M28
