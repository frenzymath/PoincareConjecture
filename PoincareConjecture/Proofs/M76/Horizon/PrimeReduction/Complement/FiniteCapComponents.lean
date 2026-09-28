import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.FinitePLBallAttachment
import Mathlib.Topology.Homeomorph.Lemmas










set_option autoImplicit false

open Set Geometry

namespace Set

local notation "V3" => (Fin 3 → ℝ)

private theorem exists_component_transport
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ∃ H : ConnectedComponents X ≃ₜ ConnectedComponents Y,
      ∀ x, H (ConnectedComponents.mk x) = ConnectedComponents.mk (e x) := by
  have hfiber (y : Y) : IsConnected (e ⁻¹' {y}) := by
    have heq : e ⁻¹' {y} = {e.symm y} := by
      ext x
      change e x = y ↔ x = e.symm y
      constructor
      · intro h
        simpa only [e.symm_apply_apply] using congrArg e.symm h
      · rintro rfl
        exact e.apply_symm_apply y
    rw [heq]
    exact isConnected_singleton
  exact ⟨e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hfiber, fun _ => rfl⟩




theorem exists_components_homeomorph_finite_cap_attachment
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite κ]
    {P : Set E} (D B : κ → Set E)
    (hP : IsClosed P) (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hattach : ∀ i, P ∩ D i = B i) :
    ∃ H : ConnectedComponents P ≃ₜ ConnectedComponents (P ∪ ⋃ i, D i : Set E),
      ∀ x : P, H (ConnectedComponents.mk x) =
        ConnectedComponents.mk (⟨x, Or.inl x.property⟩ : (P ∪ ⋃ i, D i : Set E)) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  have hfinite (s : Finset κ) :
      ∃ H : ConnectedComponents P ≃ₜ ConnectedComponents (P ∪ ⋃ i ∈ s, D i : Set E),
        ∀ x : P, H (ConnectedComponents.mk x) =
          ConnectedComponents.mk (⟨x, Or.inl x.property⟩ : (P ∪ ⋃ i ∈ s, D i : Set E)) := by
    induction s using Finset.induction_on with
    | empty =>
      have hempty : (P ∪ ⋃ i ∈ (∅ : Finset κ), D i) = P := by simp
      obtain ⟨G, hG⟩ := exists_component_transport (Homeomorph.setCongr hempty.symm)
      exact ⟨G, hG⟩
    | @insert i s his ih =>
      obtain ⟨H, hH⟩ := ih
      have hclosed : IsClosed (P ∪ ⋃ j ∈ s, D j) :=
        hP.union (isClosed_biUnion_finset (fun j _ => (hD j).isCompact.isClosed))
      have hinter : (P ∪ ⋃ j ∈ s, D j) ∩ D i = B i := by
        apply Subset.antisymm
        · rintro x ⟨hxP | hxD, hxi⟩
          · exact (hattach i).subset ⟨hxP, hxi⟩
          · obtain ⟨j, hjs, hxj⟩ := mem_iUnion₂.mp hxD
            have hji : j ≠ i := fun h => his (h ▸ hjs)
            exact False.elim (disjoint_left.mp (hdis hji) hxj hxi)
        · intro x hx
          have hp := (hattach i).symm.subset hx
          exact ⟨Or.inl hp.1, hp.2⟩
      obtain ⟨A, hA⟩ := (hD i).exists_components_homeomorph_of_attachment hclosed hinter
      have hunion : (P ∪ ⋃ j ∈ s, D j) ∪ D i = P ∪ ⋃ j ∈ insert i s, D j := by
        rw [Finset.set_biUnion_insert]
        rw [← union_assoc]
        exact union_right_comm _ _ _
      obtain ⟨G, hG⟩ := exists_component_transport (Homeomorph.setCongr hunion)
      refine ⟨(H.trans A).trans G, fun x => ?_⟩
      change G (A (H (ConnectedComponents.mk x))) = _
      rw [hH, hA, hG]
      rfl
  obtain ⟨H, hH⟩ := hfinite Finset.univ
  have huniv : (P ∪ ⋃ i ∈ (Finset.univ : Finset κ), D i) = P ∪ ⋃ i, D i := by simp
  obtain ⟨G, hG⟩ := exists_component_transport (Homeomorph.setCongr huniv)
  refine ⟨H.trans G, fun x => ?_⟩
  change G (H (ConnectedComponents.mk x)) = _
  rw [hH, hG]
  rfl

end Set
