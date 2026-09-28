import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalFamilyPointPosition
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalPLMotionComposition









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem exists_protected_sphere_system_vertex_position
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {Z : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hZ : IsClosed Z) (hSZ : Disjoint (⋃ i, S i) Z) (V : Finset X) :
    ∃ (F : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ Disjoint C Z ∧ EqOn F id Cᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (∀ i, ChartwisePLSphere e (F '' S i)) ∧ Disjoint (F '' (⋃ i, S i)) (V : Set X) := by
  classical
  have hid : ∀ i j, (e i).symm.trans
      ((Homeomorph.refl X).toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3 := by
    intro i j
    change (e i).symm.trans ((OpenPartialHomeomorph.refl X).trans (e j)) ∈ _
    simpa only [OpenPartialHomeomorph.refl_trans] using he i j
  induction V using Finset.induction_on with
  | empty =>
    refine ⟨Homeomorph.refl X, ∅, isCompact_empty, by simp, ?_,
      hid, hid, ?_, ?_⟩
    · intro x _
      rfl
    · exact ⟨fun i => Classical.choice ((sS i).nonempty_image (Homeomorph.refl X) hcover hid)⟩
    · simp
  | @insert p V hpV ih =>
    obtain ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, ⟨sF⟩, hFV⟩ := ih
    by_cases hpS : p ∈ F '' (⋃ i, S i)
    · have hpZ : p ∉ Z := by
        intro hpZ
        obtain ⟨x, hx, hxp⟩ := hpS
        have hpC : p ∉ C := fun h => disjoint_left.mp hCZ h hpZ
        have hFp : F p = p := hFout hpC
        have hxp' : x = p := F.injective (hxp.trans hFp.symm)
        exact disjoint_left.mp hSZ (hxp' ▸ hx) hpZ
      let U : Set X := Zᶜ ∩ (V : Set X)ᶜ
      have hU : IsOpen U := hZ.isOpen_compl.inter V.finite_toSet.isClosed.isOpen_compl
      have hpU : p ∈ U := ⟨hpZ, hpV⟩
      obtain ⟨G, D, hD, hDU, hGout, hGPL, hGinv, hSG, hpG⟩ :=
        exists_sphere_system_point_avoiding_motion (fun i => F '' S i) sF
          (by
            intro i j hij
            apply disjoint_left.mpr
            rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
            exact disjoint_left.mp (hdis hij) ha (F.injective (hbx.trans hax.symm) ▸ hb))
          hcover he hU hpU
      have hDZ : Disjoint D Z := disjoint_left.mpr fun x hx hz => (hDU hx).1 hz
      have hfixed (x : X) (hx : x ∈ (V : Set X)) : G x = x :=
        hGout (fun h => (hDU h).2 hx)
      have hPL := original_PL_motion_trans e hcover F G hFPL hGPL
      have hinv := original_PL_motion_trans e hcover G.symm F.symm hGinv hFinv
      have himage : (F.trans G) '' (⋃ i, S i) = G '' (F '' (⋃ i, S i)) := by
        rw [image_image]
        rfl
      refine ⟨F.trans G, C ∪ D, hC.union hD, disjoint_union_left.mpr ⟨hCZ, hDZ⟩,
        ?_, hPL, hinv, ?_, ?_⟩
      · intro x hx
        change G (F x) = x
        rw [hFout (fun h => hx (Or.inl h))]
        exact hGout (fun h => hx (Or.inr h))
      · exact ⟨fun i => Classical.choice ((sS i).nonempty_image (F.trans G) hcover hPL)⟩
      · apply disjoint_left.mpr
        intro x hx hxV
        rcases Finset.mem_insert.mp hxV with hxp | hxV
        · apply hpG
          rw [← image_iUnion]
          exact hxp ▸ himage.subset hx
        · obtain ⟨y, hy, hxy⟩ := hx
          have hFy : F y = x := G.injective (hxy.trans (hfixed x hxV).symm)
          exact disjoint_left.mp hFV ⟨y, hy, hFy⟩ hxV
    · refine ⟨F, C, hC, hCZ, hFout, hFPL, hFinv, ⟨sF⟩, ?_⟩
      apply disjoint_left.mpr
      intro x hx hxV
      rcases Finset.mem_insert.mp hxV with hxp | hxV
      · exact hpS (hxp ▸ hx)
      · exact disjoint_left.mp hFV hx hxV

end PoincareConjecture.M76

