import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.FiniteCutPLDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphericalComponentSubregions
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.restore_one_disjoint_collar
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (O : κ → Set X)
    (hR : IsCompact R) (hO : ∀ i, IsOpen (O i))
    (hinside : ∀ i, closure (O i) ⊆ interior R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hPL : PLDomain e (R \ ⋃ i, O i)) (i : κ) :
    PLDomain e (R \ ⋃ j : {j : κ // j ≠ i}, O j.val) := by
  classical
  obtain ⟨hQ,_,hfrontQ,_⟩ := finite_collar_cut_geometry hR hO hinside hdis
  obtain ⟨hA,_,hfrontA,_⟩ := finite_collar_cut_geometry hR
    (fun j : {j : κ // j ≠ i} => hO j.val)
    (fun j : {j : κ // j ≠ i} => hinside j.val)
    (fun j k hjk => hdis (Subtype.val_injective.ne hjk))
  refine ⟨hPL.cover,hPL.compatible,hA.isClosed,?_⟩
  intro x hx
  have hxQ : x ∈ frontier (R \ ⋃ j, O j) := by
    rw [hfrontQ]
    rcases hfrontA.subset hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨j.val,hj⟩)
  have hxoff : x ∉ closure (O i) := by
    intro hxi
    rcases hfrontA.subset hx with hx | hx
    · exact hx.2 (hinside i hxi)
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      exact disjoint_left.mp (hdis j.property) (frontier_subset_closure hj) hxi
  obtain ⟨ell,v,B,hv,hxB,hzero,hcompat,hhalf⟩ := hPL.halfspace x hxQ
  let U := (closure (O i))ᶜ
  have hU : IsOpen U := isClosed_closure.isOpen_compl
  refine ⟨ell,v,B.restrOpen U hU,hv,⟨hxB,hxoff⟩,hzero,?_,?_⟩
  · intro j
    exact (e j).piecewiseAffine_compatible_restrOpen_right B (hcompat j) hU
  · intro y hy
    change y ∈ R \ ⋃ j : {j : κ // j ≠ i}, O j.val ↔ 0 ≤ ell (B y)
    rw [←hhalf y hy.1]
    constructor
    · rintro ⟨hyR,hyO⟩
      refine ⟨hyR,?_⟩
      intro h
      obtain ⟨j,hj⟩ := mem_iUnion.mp h
      by_cases hji : j = i
      · exact hy.2 (subset_closure (hji ▸ hj))
      · exact hyO (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)
    · rintro ⟨hyR,hyO⟩
      exact ⟨hyR,fun h => hyO (by obtain ⟨j,hj⟩ := mem_iUnion.mp h; exact mem_iUnion.mpr ⟨j.val,hj⟩)⟩

theorem selected_cut_component_eq_full_cut_component
    {X κ : Type*} [TopologicalSpace X] {R : Set X} (O : κ → Set X) (i : κ)
    {a x : X}
    (hx : x ∈ connectedComponentIn (R \ ⋃ j : {j : κ // j ≠ i}, O j.val) a \ O i) :
    connectedComponentIn
      (connectedComponentIn (R \ ⋃ j : {j : κ // j ≠ i}, O j.val) a \ O i) x =
      connectedComponentIn (R \ ⋃ j, O j) x := by
  classical
  let A := R \ ⋃ j : {j : κ // j ≠ i}, O j.val
  let Q := R \ ⋃ j, O j
  have hQA : Q ⊆ A := by
    rintro y ⟨hyR,hyO⟩
    exact ⟨hyR,fun h => hyO (by obtain ⟨j,hj⟩ := mem_iUnion.mp h; exact mem_iUnion.mpr ⟨j.val,hj⟩)⟩
  have hsub : connectedComponentIn A a \ O i ⊆ Q := by
    rintro y ⟨hyC,hyOi⟩
    have hyA := connectedComponentIn_subset A a hyC
    refine ⟨hyA.1,?_⟩
    intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    by_cases hji : j = i
    · exact hyOi (hji ▸ hj)
    · exact hyA.2 (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)
  apply Subset.antisymm (connectedComponentIn_mono x hsub)
  have hxQ : x ∈ Q := hsub hx
  apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hxQ)
  intro y hy
  have hyA : y ∈ connectedComponentIn A x := connectedComponentIn_mono x hQA hy
  have hyC : y ∈ connectedComponentIn A a := by
    rwa [←connectedComponentIn_eq hx.1] at hyA
  exact ⟨hyC,fun h => (connectedComponentIn_subset Q x hy).2 (mem_iUnion.mpr ⟨i,h⟩)⟩

theorem HasNoPuncturedSphereComponents.exists_selected_cut_component_domain
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R Z : Set X}
    (O : κ → Set X) (hR : IsCompact R) (hO : ∀ i, IsOpen (O i))
    (hinside : ∀ i, closure (O i) ⊆ interior R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hPL : PLDomain e (R \ ⋃ i, O i))
    (hno : HasNoPuncturedSphereComponents e f (R \ ⋃ i, O i))
    (i : κ) (hZ : IsConnected Z) (hZR : Z ⊆ interior R)
    (hZother : ∀ j, j ≠ i → Disjoint Z (closure (O j))) :
    ∃ a ∈ Z,
      let C := connectedComponentIn (R \ ⋃ j : {j : κ // j ≠ i}, O j.val) a
      IsCompact C ∧ IsConnected C ∧ PLDomain e C ∧ Z ⊆ interior C ∧
      IsCompact (C \ O i) ∧ PLDomain e (C \ O i) ∧
      frontier (C \ O i) = (C \ O i) ∩ frontier (R \ ⋃ j, O j) ∧
      HasNoPuncturedSphereComponents e f (C \ O i) ∧
      ∀ x ∈ C \ O i, connectedComponentIn (C \ O i) x =
        connectedComponentIn (R \ ⋃ j, O j) x := by
  classical
  let A := R \ ⋃ j : {j : κ // j ≠ i}, O j.val
  let Q := R \ ⋃ j, O j
  have hQA : Q ⊆ A := by
    rintro y ⟨hyR,hyO⟩
    exact ⟨hyR,fun h => hyO (by obtain ⟨j,hj⟩ := mem_iUnion.mp h; exact mem_iUnion.mpr ⟨j.val,hj⟩)⟩
  have hAcut : A \ O i = Q := by
    ext y
    constructor
    · rintro ⟨hyA,hyOi⟩
      refine ⟨hyA.1,?_⟩
      intro h
      obtain ⟨j,hj⟩ := mem_iUnion.mp h
      by_cases hji : j = i
      · exact hyOi (hji ▸ hj)
      · exact hyA.2 (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)
    · exact fun hy => ⟨hQA hy,fun h => hy.2 (mem_iUnion.mpr ⟨i,h⟩)⟩
  obtain ⟨hAc,hAint,_⟩ := finite_collar_cut_geometry hR
    (fun j : {j : κ // j ≠ i} => hO j.val)
    (fun j : {j : κ // j ≠ i} => hinside j.val)
    (fun j k hjk => hdis (Subtype.val_injective.ne hjk))
  have hAPL : PLDomain e A := hPL.restore_one_disjoint_collar O hR hO hinside hdis i
  have hZint : Z ⊆ interior A := by
    rw [hAint]
    intro x hx
    refine ⟨hZR hx,?_⟩
    intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    exact disjoint_left.mp (hZother j.val j.property) hx hj
  obtain ⟨a,ha⟩ := hZ.nonempty
  have haA : a ∈ A := interior_subset (hZint ha)
  let C := connectedComponentIn A a
  have hCc : IsCompact C := isCompact_connectedComponentIn_of_mem hAc haA
  have hCPL : PLDomain e C := hAPL.connectedComponentIn hAc haA
  have hCsub : C ⊆ A := connectedComponentIn_subset A a
  have hZC : Z ⊆ C := hZ.isPreconnected.subset_connectedComponentIn ha
    (hZint.trans interior_subset)
  let : LocallyPathConnectedSpace A := hAPL.locallyPathConnectedSpace
  obtain ⟨U,hU,hCU⟩ := exists_open_inter_of_relative_open hCsub
    (isOpen_preimage_connectedComponentIn haA)
  have hCi : interior C = C ∩ interior A := interior_eq_inter_of_eq_inter_open hU hCU
  have hDC : C \ O i = Q ∩ U := by
    rw [hCU,←hAcut]
    ext y
    simp only [mem_diff,mem_inter_iff]
    tauto
  have hDsub : C \ O i ⊆ Q := hDC.subset.trans inter_subset_left
  have hDc : IsCompact (C \ O i) := hCc.diff (hO i)
  have hDopen : IsOpen ((Subtype.val : Q → X) ⁻¹' (C \ O i)) := by
    have heq : (Subtype.val : Q → X) ⁻¹' (C \ O i) =
        (Subtype.val : Q → X) ⁻¹' U := by
      ext x
      simp only [mem_preimage,hDC,mem_inter_iff]
      exact and_iff_right x.property
    rw [heq]
    exact hU.preimage continuous_subtype_val
  refine ⟨a,ha,hCc,isConnected_connectedComponentIn_iff.mpr haA,hCPL,?_,hDc,
    hPL.of_relative_clopen_subset hDsub hDc.isClosed hDopen,
    frontier_eq_inter_of_eq_inter_open hPL.closed hDc.isClosed hU hDC,?_,?_⟩
  · rw [hCi]
    exact fun x hx => ⟨hZC hx,hZint hx⟩
  · intro x hx hm
    exact hno x (hDsub hx) ((selected_cut_component_eq_full_cut_component O i hx) ▸ hm)
  · exact fun x hx => selected_cut_component_eq_full_cut_component O i hx

end PoincareConjecture.M76
