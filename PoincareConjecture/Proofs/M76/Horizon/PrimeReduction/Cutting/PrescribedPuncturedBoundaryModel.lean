import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SelectedBoundaryLabels

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

theorem exists_prescribed_punctured_boundary_label_equiv
    {X E ι κ η : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite κ] [Finite η]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {M : Set E}
    (hR : IsClosed R) (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hMK : M ⊆ K.space) (G : R ≃ₜ M) (hginv : ∀ x : R, g (G x) = (x : X))
    (A r : κ → Set V4) (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ Sphere)
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (C : M ≃ₜ (Sphere \ ⋃ i, A i \ r i : Set V4)) (hC : C.IsFinitePL)
    (hmark : ∀ x : R, (x : X) ∈ frontier R ↔ (C (G x) : V4) ∈ ⋃ i, r i)
    (P : η → Set X) (sP : ∀ j, ChartwisePLSphere e (P j))
    (hPdis : Pairwise fun j k => Disjoint (P j) (P k))
    (hfront : frontier R = ⋃ j, P j) :
    ∃ l : η ≃ κ, (∀ j, P j ⊆ R) ∧
      (∀ j (x : R), (x : X) ∈ P j ↔ (C (G x) : V4) ∈ r (l j)) ∧
      ∀ j, (fun x : R => (C (G x) : V4)) ''
        ((Subtype.val : R → X) ⁻¹' P j) = r (l j) := by
  classical
  obtain ⟨S, sS, _, hSR, hSdis, hSfront, hSmark, hSsurj⟩ :=
    exists_original_punctured_model_boundary_spheres hR K g hg hgi hMK G hginv
      A r hA hAS hAdis C hC hmark
  have hPS : (⋃ j, P j) = ⋃ i, S i := hfront.symm.trans hSfront
  have hto (j : η) : ∃ i, P j ⊆ S i :=
    ((sP j).isConnected.exists_unique_subset_finite_disjoint_closed S
      (fun i => (sS i).isCompact.isClosed) hSdis
      ((subset_iUnion P j).trans hPS.subset)).exists
  have hfrom (i : κ) : ∃ j, S i ⊆ P j :=
    ((sS i).isConnected.exists_unique_subset_finite_disjoint_closed P
      (fun j => (sP j).isCompact.isClosed) hPdis
      ((subset_iUnion S i).trans hPS.symm.subset)).exists
  choose label hto using hto
  choose reverse hfrom using hfrom
  have hleft (j : η) : reverse (label j) = j := by
    by_contra hne
    obtain ⟨x, hx⟩ := (sP j).isConnected.nonempty
    exact disjoint_left.mp (hPdis hne) (hfrom (label j) (hto j hx)) hx
  have hright (i : κ) : label (reverse i) = i := by
    by_contra hne
    obtain ⟨x, hx⟩ := (sS i).isConnected.nonempty
    exact disjoint_left.mp (hSdis hne) (hto (reverse i) (hfrom i hx)) hx
  let l : η ≃ κ := ⟨label, reverse, hleft, hright⟩
  have hlabel (j : η) : S (l j) = P j := by
    apply Subset.antisymm
    · simpa only [l, Equiv.coe_fn_mk, hleft] using hfrom (label j)
    · exact hto j
  refine ⟨l, ?_, ?_, ?_⟩
  · intro j
    rw [← hlabel j]
    exact hSR (l j)
  · intro j x
    rw [← hlabel j]
    exact hSmark (l j) x
  · intro j
    rw [← hlabel j]
    exact hSsurj (l j)

theorem HasPuncturedSphereModel.exists_prescribed_boundary_model
    {X E ι η : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite η]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {f : X → E}
    (hm : HasPuncturedSphereModel e f R) (hR : IsClosed R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (P : η → Set X) (sP : ∀ j, ChartwisePLSphere e (P j))
    (hPdis : Pairwise fun j k => Disjoint (P j) (P k))
    (hfront : frontier R = ⋃ j, P j) :
    ∃ (A r : η → Set V4) (M : Set E) (G : R ≃ₜ M)
      (C : M ≃ₜ (Sphere \ ⋃ j, A j \ r j : Set V4)),
      (∀ j, IsFinitePLBallPair V3 (A j) (r j) ∧ A j ⊆ Sphere ∧
        IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (A j \ r j))) ∧
      Pairwise (fun j k => Disjoint (A j) (A k)) ∧
      (∀ x : R, (G x : E) = f x) ∧ C.IsFinitePL ∧ (∀ j, P j ⊆ R) ∧
      (∀ j (x : R), (x : X) ∈ P j ↔ (C (G x) : V4) ∈ r j) ∧
      ∀ j, (fun x : R => (C (G x) : V4)) ''
        ((Subtype.val : R → X) ⁻¹' P j) = r j := by
  obtain ⟨_, n, A, r, M, G, C, hA, hAdis, hG, hC, hmark⟩ := hm
  have hMK : M ⊆ K.space := by
    intro y hy
    let x := G.symm ⟨y, hy⟩
    have hval : f x = y := (hG x).symm.trans
      (congrArg Subtype.val (G.apply_symm_apply _))
    exact hval ▸ (hreal x x.property).1
  have hginv (x : R) : g (G x) = (x : X) := by
    rw [hG x]
    exact (hreal x x.property).2
  obtain ⟨l, hPR, hPmark, hPsurj⟩ := exists_prescribed_punctured_boundary_label_equiv
    hR K g hg hgi hMK G hginv A r (fun i => (hA i).1) (fun i => (hA i).2.1)
    hAdis C hC hmark P sP hPdis hfront
  have hreindex : (⋃ j, A (l j) \ r (l j)) = ⋃ i, A i \ r i := by
    apply Subset.antisymm
    · exact iUnion_subset fun j => subset_iUnion (fun i => A i \ r i) (l j)
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨l.symm i, by simpa only [l.apply_symm_apply] using hi⟩
  have htarget : (Sphere \ ⋃ i, A i \ r i : Set V4) =
      Sphere \ ⋃ j, A (l j) \ r (l j) := by rw [hreindex]
  let C' := (Homeomorph.setCongr (rfl : M = M)).trans
    (C.trans (Homeomorph.setCongr htarget))
  refine ⟨A ∘ l, r ∘ l, M, G, C', (fun j => hA (l j)),
    (fun j k hjk => hAdis (l.injective.ne hjk)), hG,
    hC.setCongr rfl htarget, hPR, ?_, ?_⟩
  · exact hPmark
  · exact hPsurj

end PoincareConjecture.M76
