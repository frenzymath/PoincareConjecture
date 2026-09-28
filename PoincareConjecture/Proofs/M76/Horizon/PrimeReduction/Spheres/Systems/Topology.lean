import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.isCompact
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) : IsCompact S := by
  have himage : s.map '' sphere (0 : V3) 1 = S := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [s.map_eq ⟨x, hx⟩]
      exact (s.parametrization ⟨x, hx⟩).property
    · intro x hx
      obtain ⟨z, hz⟩ := s.parametrization.surjective ⟨x, hx⟩
      exact ⟨z, z.property, (s.map_eq z).trans (congrArg Subtype.val hz)⟩
  rw [← himage]
  exact (isCompact_sphere (0 : V3) 1).image_of_continuousOn s.piecewiseAffine.continuousOn

theorem exists_open_sphere_system_isolation
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} (S : κ → Set X)
    (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j))) (i : κ) :
    ∃ O : Set X, IsOpen O ∧ S i ⊆ O ∧
      O ∩ (⋃ j, S j) = S i ∧ ∀ j, j ≠ i → Disjoint O (S j) := by
  let O := (⋃ j : {j : κ // j ≠ i}, S j.val)ᶜ
  have hO : IsOpen O :=
    (isClosed_iUnion_of_finite
      (fun j : {j : κ // j ≠ i} => (sS j.val).isCompact.isClosed)).isOpen_compl
  have hiO : S i ⊆ O := by
    intro x hx hn
    obtain ⟨j, hj⟩ := mem_iUnion.mp hn
    exact disjoint_left.mp (hdis (Ne.symm j.property)) hx hj
  have hother (j : κ) (hji : j ≠ i) : Disjoint O (S j) := by
    apply disjoint_left.mpr
    intro x hx hj
    exact hx (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  refine ⟨O, hO, hiO, ?_, hother⟩
  apply Subset.antisymm
  · rintro x ⟨hxO, hx⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · exact hji ▸ hj
    · exact (disjoint_left.mp (hother j hji) hxO hj).elim
  · exact fun x hx => ⟨hiO hx, mem_iUnion.mpr ⟨i, hx⟩⟩

end PoincareConjecture.M76
