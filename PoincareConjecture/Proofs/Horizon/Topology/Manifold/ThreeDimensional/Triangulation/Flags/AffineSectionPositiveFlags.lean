import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Flags.AffineSectionFlags

set_option autoImplicit false

noncomputable section

open Set
open scoped BigOperators

universe u v

namespace Poincare.Topology

theorem exists_affine_section_flag_of_centers
    {V : Type u} [Fintype V] {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V)
    (c : AffineSectionFace A s → V → Real)
    (hc : ∀ i, c i ∈ affineCoordinateSection A s ∧ finiteCoordinateSupport (c i) = i.val)
    (z : V → Real) (hz : z ∈ affineCoordinateSection A s) :
    ∃ t : Finset (AffineSectionFace A s), t.Nonempty ∧
      (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) ∧
      (∀ i ∈ t, i.val ⊆ finiteCoordinateSupport z) ∧
      z ∈ convexHull Real (c '' (t : Set (AffineSectionFace A s))) := by
  classical
  have H : ∀ q : Finset V, ∀ z : V → Real,
      z ∈ affineCoordinateSection A s → finiteCoordinateSupport z = q →
      ∃ t : Finset (AffineSectionFace A s), t.Nonempty ∧
        (∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) ∧
        (∀ i ∈ t, i.val ⊆ finiteCoordinateSupport z) ∧
        z ∈ convexHull Real (c '' (t : Set (AffineSectionFace A s))) := by
    apply Finset.strongInduction
    intro q ih z hz hq
    let i : AffineSectionFace A s := ⟨q, z, hz, hq⟩
    by_cases hzi : z = c i
    · refine ⟨{i}, Finset.singleton_nonempty i, ?_, ?_, ?_⟩
      · intro j hj k hk
        obtain rfl := Finset.mem_singleton.mp hj
        obtain rfl := Finset.mem_singleton.mp hk
        exact Or.inl le_rfl
      · intro j hj
        obtain rfl := Finset.mem_singleton.mp hj
        change q ⊆ finiteCoordinateSupport z
        exact hq.symm.subset
      · rw [hzi]
        exact subset_convexHull Real _ (Set.mem_image_of_mem _ (Finset.mem_singleton_self i))
    · obtain ⟨a, y, ha, ha1, hy, hsub, hdecomp⟩ :=
        exists_affine_section_face_residual A s z (c i) hz (hc i).1
          (hq.trans (hc i).2.symm) hzi
      have hyq : finiteCoordinateSupport y ⊂ q := by simpa only [hq] using hsub
      obtain ⟨t, ht, hchain, hsmall, hyhull⟩ :=
        ih (finiteCoordinateSupport y) hyq y hy rfl
      refine ⟨insert i t, Finset.insert_nonempty i t, ?_, ?_, ?_⟩
      · intro j hj k hk
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rcases Finset.mem_insert.mp hk with rfl | hk
          · exact Or.inl le_rfl
          · exact Or.inr (show k.val ⊆ q from (hsmall k hk).trans hyq.subset)
        · rcases Finset.mem_insert.mp hk with rfl | hk
          · exact Or.inl (show j.val ⊆ q from (hsmall j hj).trans hyq.subset)
          · exact hchain j hj k hk
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · change q ⊆ finiteCoordinateSupport z
          exact hq.symm.subset
        · exact (hsmall j hj).trans hsub.subset
      · have hc_mem : c i ∈ convexHull Real
            (c '' (↑(insert i t) : Set (AffineSectionFace A s))) :=
          subset_convexHull Real _ (Set.mem_image_of_mem _ (Finset.mem_insert_self i t))
        have hy_mem : y ∈ convexHull Real
            (c '' (↑(insert i t) : Set (AffineSectionFace A s))) := by
          apply convexHull_mono _ hyhull
          exact Set.image_mono (fun j hj => Finset.mem_insert_of_mem hj)
        rw [hdecomp]
        exact (convex_convexHull Real _) hc_mem hy_mem ha (sub_nonneg.mpr ha1.le) (by ring)
  exact H (finiteCoordinateSupport z) z hz rfl

open scoped Classical in
theorem affineSectionFlagMap_range_of_centers
    {V : Type u} [Fintype V] {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V)
    (c : AffineSectionFace A s → V → Real)
    (hc : ∀ i, c i ∈ affineCoordinateSection A s ∧ finiteCoordinateSupport (c i) = i.val) :
    Set.range (finiteOrderComplexMap (AffineSectionFace A s) c) =
      affineCoordinateSection A s := by
  classical
  let I := AffineSectionFace A s
  apply Set.Subset.antisymm
  · rintro z ⟨w, rfl⟩
    have hw := (finiteOrderComplex_space I w.val).mp w.property
    exact (convex_affineCoordinateSection A s).sum_mem
      (fun i _ => hw.1 i) hw.2.1 (fun i _ => (hc i).1)
  · intro z hz
    obtain ⟨t, ht, hchain, _, hzhull⟩ := exists_affine_section_flag_of_centers A s c hc z hz
    let L : (I → Real) →ₗ[Real] (V → Real) := Fintype.linearCombination Real c
    let basisPoint : I → I → Real := fun i => Pi.single i 1
    have himage : L '' convexHull Real (basisPoint '' (t : Set I)) =
        convexHull Real (c '' (t : Set I)) := by
      rw [L.image_convexHull, Set.image_image]
      congr 1
      have heval : (fun i => L (basisPoint i)) = c := by
        funext i
        simp only [L, basisPoint, Fintype.linearCombination_apply_single, one_smul]
      exact congrArg (fun f : I → V → Real => f '' (t : Set I)) heval
    have hzimage : z ∈ L '' convexHull Real (basisPoint '' (t : Set I)) := by
      rw [himage]
      exact hzhull
    obtain ⟨w, hw, hwz⟩ := hzimage
    have hface : t.image basisPoint ∈ (finiteOrderComplex I).faces := by
      apply (finiteOrderComplex_faces I _).mpr
      refine ⟨t, ht, hchain, ?_⟩
      apply Finset.image_congr
      intro i hi
      funext j
      simp only [basisPoint, Pi.single_apply]
      split_ifs <;> rfl
    have hwspace : w ∈ (finiteOrderComplex I).space := by
      apply Geometry.SimplicialComplex.convexHull_subset_space hface
      simpa only [Finset.coe_image] using hw
    exact ⟨⟨w, hwspace⟩, hwz⟩

open scoped Classical in
def affineSectionFlagHomeomorphOfCenters
    {V : Type u} [Fintype V] {F : Type v} [AddCommGroup F] [Module Real F]
    (A : (V → Real) →ᵃ[Real] F) (s : Finset V)
    (c : AffineSectionFace A s → V → Real)
    (hc : ∀ i, c i ∈ affineCoordinateSection A s ∧ finiteCoordinateSupport (c i) = i.val) :
    (finiteOrderComplex (AffineSectionFace A s)).space ≃ₜ affineCoordinateSection A s := by
  let I := AffineSectionFace A s
  have hsupport : ∀ i : I, (i.val).Nonempty := by
    intro i
    rw [← (hc i).2]
    exact finiteCoordinateSupport_nonempty (c i) (hc i).1.1
  have hc_nonneg : ∀ (i : I) v, 0 ≤ c i v := fun i v => (hc i).1.1.1 v
  have hc_pos : ∀ (i : I) v, 0 < c i v ↔ v ∈ i.val := by
    intro i v
    rw [← (hc i).2, mem_finiteCoordinateSupport]
    exact ⟨ne_of_gt, fun h => lt_of_le_of_ne (hc_nonneg i v) (Ne.symm h)⟩
  let h := finiteOrderComplexMap_homeomorph_range_of_supports c Subtype.val
    hsupport (fun i j => Iff.rfl) hc_nonneg hc_pos
  exact h.trans (Homeomorph.setCongr (affineSectionFlagMap_range_of_centers A s c hc))

end Poincare.Topology
