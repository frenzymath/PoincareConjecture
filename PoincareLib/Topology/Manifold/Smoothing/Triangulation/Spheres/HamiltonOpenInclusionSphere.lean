import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs

/-!
# The original marked PL sphere through an open inclusion

The extended partial charts need cover only the original open set. The
same sphere parametrization and finite source patches give the ambient
sphere certificate used by the cap transitions. See Hamilton 1976,
p.66 and M76 derivation343.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

variable {X : Type*} [TopologicalSpace X] {U : Set X} [Nonempty U]
  {ι : Type*}

local notation "V3" => (Fin 3 → ℝ)

/-- The actual open inclusion transports the whole marked sphere and
its finite coordinate patches to the literal image sphere. No coverage
of the new ambient space by the extended old family is assumed. See
Hamilton p.66 and derivation343. -/
theorem ChartwisePLSphere.exists_open_inclusion
    (hU : IsOpen U) {e : ι → OpenPartialHomeomorph U V3} {S : Set U}
    (s : ChartwisePLSphere e S) :
    let j : OpenPartialHomeomorph U X :=
      hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → X)
    ∃ t : ChartwisePLSphere (fun i => j.symm.trans (e i)) ((Subtype.val : U → X) '' S),
      t.map = (Subtype.val : U → X) ∘ s.map ∧
      ∀ x : sphere (0 : V3) 1,
        (t.parametrization x : X) = ((s.parametrization x : U) : X) := by
  classical
  let j : OpenPartialHomeomorph U X :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → X)
  have hjs : j.source = univ := rfl
  have hj (x : U) : x ∈ j.source := by rw [hjs]; exact mem_univ x
  let jS : S ≃ₜ ((Subtype.val : U → X) '' S) :=
    j.homeomorphOfImageSubsetSource (by rw [hjs]; exact subset_univ _) rfl
  have hpoly : PolyhedralPLInCharts (fun i => j.symm.trans (e i))
      ((Subtype.val : U → X) ∘ s.map) (sphere (0 : V3) 1) := by
    refine ⟨continuous_subtype_val.comp_continuousOn s.piecewiseAffine.continuousOn, ?_⟩
    intro x
    obtain ⟨i, J, V, hJ, hJS, hV, hxV, hVJ, hm, hPL⟩ :=
      s.piecewiseAffine.coordinates x
    refine ⟨i, J, V, hJ, hJS, hV, hxV, hVJ, ?_, ?_⟩
    · intro y hy
      refine ⟨j.map_source (hj (s.map y)), ?_⟩
      change j.symm (j (s.map y)) ∈ (e i).source
      rw [j.left_inv (hj (s.map y))]
      exact hm hy
    · apply hPL.congr
      intro y _
      change e i (s.map y) = e i (j.symm (j (s.map y)))
      rw [j.left_inv (hj (s.map y))]
  let t : ChartwisePLSphere (fun i => j.symm.trans (e i))
      ((Subtype.val : U → X) '' S) :=
    { parametrization := s.parametrization.trans jS
      map := (Subtype.val : U → X) ∘ s.map
      map_eq := by
        intro x
        change (s.map x : X) = ((s.parametrization x : U) : X)
        rw [s.map_eq x]
      piecewiseAffine := hpoly }
  exact ⟨t, rfl, fun _ => rfl⟩

end PoincareMT.M76
