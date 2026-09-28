import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SelectedBoundaryLabels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphericalComponentSubregions

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HasPuncturedSphereModel

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

theorem component_models_of_selected_boundary_replacement
    {X E ι ν : Type*} [TopologicalSpace X] [T2Space X] [Finite ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R Q B T : Set X}
    (hm : HasPuncturedSphereModel e f R) (hR : IsClosed R)
    (hQ : IsCompact Q) (hPL : PLDomain e Q) (hQR : Q ⊆ R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (hB : IsConnected B) (hBc : IsClosed B) (hTc : IsClosed T)
    (hBT : Disjoint B T) (hRf : frontier R = B ∪ T)
    (N : ν → Set X) (sN : ∀ i, ChartwisePLSphere e (N i))
    (hNdis : Pairwise fun i j => Disjoint (N i) (N j))
    (hNT : ∀ i, Disjoint (N i) T) (hQf : frontier Q = T ∪ ⋃ i, N i) :
    ∀ x ∈ Q, HasPuncturedSphereModel e f (connectedComponentIn Q x) := by
  classical
  obtain ⟨hf, n, A, r, M, G, C, hA, hAdis, hG, hC, hmark⟩ := hm
  have hMK : M ⊆ K.space := by
    intro y hy
    let x := G.symm ⟨y, hy⟩
    have hval : f x = y := (hG x).symm.trans (congrArg Subtype.val (G.apply_symm_apply _))
    exact hval ▸ (hreal x x.property).1
  have hginv (x : R) : g (G x) = (x : X) := by
    rw [hG]
    exact (hreal x x.property).2
  obtain ⟨S, sS, _, _, hSdis, hSf, _, _⟩ := exists_original_punctured_model_boundary_spheres
    hR K g hg hgi hMK G hginv A r (fun i => (hA i).1) (fun i => (hA i).2.1)
    hAdis C hC hmark
  obtain ⟨i, _, _, hT⟩ := hB.exists_eq_label_of_closed_partition hBc hTc hBT S
    (fun j => (sS j).isConnected) (fun j => (sS j).isCompact.isClosed) hSdis
    (hRf.symm.trans hSf)
  let F : {j : Fin n // j ≠ i} ⊕ ν → Set X := Sum.elim (fun j => S j) N
  let sF : ∀ j, ChartwisePLSphere e (F j) := fun j => by
    cases j with
    | inl j => exact sS j
    | inr j => exact sN j
  have hST (j : {j : Fin n // j ≠ i}) : S j ⊆ T :=
    (subset_iUnion (fun j : {j : Fin n // j ≠ i} => S j) j).trans hT.symm.subset
  have hFdis : Pairwise fun j k => Disjoint (F j) (F k) := by
    intro j k hjk
    cases j with
    | inl j =>
      cases k with
      | inl k => exact hSdis (fun h => hjk (congrArg Sum.inl (Subtype.ext h)))
      | inr k => exact (hNT k).symm.mono_left (hST j)
    | inr j =>
      cases k with
      | inl k => exact (hNT j).mono_right (hST k)
      | inr k => exact hNdis (fun h => hjk (congrArg Sum.inr h))
  have hFf : frontier Q = ⋃ j, F j := by
    rw [hQf, hT]
    ext x
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · exact ⟨Sum.inl j, hj⟩
      · exact ⟨Sum.inr j, hj⟩
    · rintro ⟨j, hj⟩
      cases j with
      | inl j => exact Or.inl ⟨j, hj⟩
      | inr j => exact Or.inr ⟨j, hj⟩
  intro x hx
  obtain ⟨A', hA', hA'dis, u, H, hH, hu, _, _, hboundary⟩ :=
    hPL.exists_finitePL_punctured_component_model hQ hQR
      A r (fun j => (hA j).1) (fun j => (hA j).2.1) hAdis (fun j => (hA j).2.2)
      f hf G hG C hC hmark F sF hFdis hFf hx
  exact HasPuncturedSphereModel.of_marked_model A' _
    (fun j => (hA' j).1) (fun j => (hA' j).2.1) hA'dis (fun j => (hA' j).2.2)
    hf u hu H hH hboundary

end PoincareConjecture.M76.HasPuncturedSphereModel
