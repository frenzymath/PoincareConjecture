import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.Mathlib.FiniteSigma

set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M76.PhaseCovering

variable {ι F Y : Type*} [Finite ι] [TopologicalSpace F] [CompactSpace F] [T2Space F]
  [TopologicalSpace Y]
  (S : ι → Set F) (hclosed : ∀ i, IsClosed (S i))
  (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
  (hcover : (⋃ i, S i) = univ)

include hclosed hdisjoint hcover

noncomputable def finiteClosedCoverHomeomorph : (Σ i, S i) ≃ₜ F := by
  let : ∀ i, CompactSpace (S i) := fun i => isCompact_iff_compactSpace.mp (hclosed i).isCompact
  let v : (Σ i, S i) → F := fun z => z.2.1
  have hc : Continuous v := continuous_sigma fun _ => continuous_subtype_val
  have hb : Function.Bijective v := by
    constructor
    · rintro ⟨i, x⟩ ⟨j, y⟩ h
      have hij : i = j := by
        by_contra hij
        apply Set.disjoint_left.mp (hdisjoint hij) x.property
        change (x : F) = (y : F) at h
        rw [h]
        exact y.property
      cases hij
      exact congrArg (Sigma.mk i) (Subtype.ext h)
    · intro x
      have hx : x ∈ ⋃ i, S i := by rw [hcover]; exact mem_univ x
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨⟨i, ⟨x, hi⟩⟩, rfl⟩
  exact (Equiv.ofBijective v hb).toHomeomorphOfContinuousClosed hc hc.isClosedMap

@[simp] theorem finiteClosedCoverHomeomorph_apply (i : ι) (x : S i) :
    finiteClosedCoverHomeomorph S hclosed hdisjoint hcover ⟨i, x⟩ = x := rfl

noncomputable def componentMap (g : ∀ i, C(S i, Y)) : C(F, Y) :=
  (ContinuousMap.sigma g).comp
    ⟨(finiteClosedCoverHomeomorph S hclosed hdisjoint hcover).symm,
      (finiteClosedCoverHomeomorph S hclosed hdisjoint hcover).symm.continuous⟩

@[simp] theorem componentMap_apply (g : ∀ i, C(S i, Y)) (i : ι) (x : S i) :
    componentMap S hclosed hdisjoint hcover g x = g i x := by
  change (ContinuousMap.sigma g)
    ((finiteClosedCoverHomeomorph S hclosed hdisjoint hcover).symm
      (finiteClosedCoverHomeomorph S hclosed hdisjoint hcover ⟨i, x⟩)) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem isCoveringMap_componentMap [T2Space Y] (g : ∀ i, C(S i, Y))
    (hg : ∀ i, IsCoveringMap (g i)) :
    IsCoveringMap (componentMap S hclosed hdisjoint hcover g) := by
  let : ∀ i, CompactSpace (S i) := fun i => isCompact_iff_compactSpace.mp (hclosed i).isCompact
  exact (isCoveringMap_finite_sigma g hg).comp_homeomorph
    (finiteClosedCoverHomeomorph S hclosed hdisjoint hcover).symm

noncomputable def componentHomotopy (f : C(F, Y)) (g : ∀ i, C(S i, Y))
    (H : ∀ i, (f.restrict (S i)).Homotopy (g i)) :
    f.Homotopy (componentMap S hclosed hdisjoint hcover g) where
  toFun z := sigmaHomotopy H
    (z.1, (finiteClosedCoverHomeomorph S hclosed hdisjoint hcover).symm z.2)
  continuous_toFun := (sigmaHomotopy H).continuous.comp
    (continuous_fst.prodMk
      ((finiteClosedCoverHomeomorph S hclosed hdisjoint hcover).symm.continuous.comp continuous_snd))
  map_zero_left x := by
    rw [(sigmaHomotopy H).apply_zero]
    change f (finiteClosedCoverHomeomorph S hclosed hdisjoint hcover
      ((finiteClosedCoverHomeomorph S hclosed hdisjoint hcover).symm x)) = f x
    rw [Homeomorph.apply_symm_apply]
  map_one_left x := (sigmaHomotopy H).apply_one _

@[simp] theorem componentHomotopy_apply (f : C(F, Y)) (g : ∀ i, C(S i, Y))
    (H : ∀ i, (f.restrict (S i)).Homotopy (g i))
    (t : unitInterval) (i : ι) (x : S i) :
    componentHomotopy S hclosed hdisjoint hcover f g H (t, x) = H i (t, x) := by
  change sigmaHomotopy H (t, (finiteClosedCoverHomeomorph S hclosed hdisjoint hcover).symm
    (finiteClosedCoverHomeomorph S hclosed hdisjoint hcover ⟨i, x⟩)) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem exists_coveringMap_with_component_formulas [T2Space Y]
    (f : C(F, Y)) (g : ∀ i, C(S i, Y)) (hg : ∀ i, IsCoveringMap (g i))
    (H : ∀ i, (f.restrict (S i)).Homotopy (g i)) :
    ∃ G : C(F, Y), IsCoveringMap G ∧
      (∀ i (x : S i), G x = g i x) ∧
      ∃ K : f.Homotopy G, ∀ t i (x : S i), K (t, x) = H i (t, x) :=
  ⟨componentMap S hclosed hdisjoint hcover g,
    isCoveringMap_componentMap S hclosed hdisjoint hcover g hg,
    componentMap_apply S hclosed hdisjoint hcover g,
    componentHomotopy S hclosed hdisjoint hcover f g H,
    componentHomotopy_apply S hclosed hdisjoint hcover f g H⟩

theorem exists_coveringMap_of_finite_components [T2Space Y]
    (f : C(F, Y))
    (h : ∀ i, ∃ g : C(S i, Y), IsCoveringMap g ∧ Nonempty ((f.restrict (S i)).Homotopy g)) :
    ∃ G : C(F, Y), IsCoveringMap G ∧ Nonempty (f.Homotopy G) := by
  classical
  choose g hg H using h
  exact ⟨componentMap S hclosed hdisjoint hcover g,
    isCoveringMap_componentMap S hclosed hdisjoint hcover g hg,
    ⟨componentHomotopy S hclosed hdisjoint hcover f g (fun i => (H i).some)⟩⟩

end PoincareConjecture.M76.PhaseCovering
