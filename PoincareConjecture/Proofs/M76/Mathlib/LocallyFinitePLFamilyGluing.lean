import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasNeighborhood
import Mathlib.Data.Set.UnionLift











set_option autoImplicit false

open Set Geometry

namespace Geometry





theorem exists_finitePL_family_extension {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : ι → Set E) (e : ∀ i, S i → F)
    (he : ∀ i, ∃ g : E → F, FinitePiecewiseAffineOn g (S i) ∧
      ∀ x : S i, e i x = g x)
    (hagree : ∀ i j (x : E) (hi : x ∈ S i) (hj : x ∈ S j),
      e i ⟨x, hi⟩ = e j ⟨x, hj⟩) :
    ∃ f : E → F, (∀ i (x : S i), f x = e i x) ∧
      ∀ i, FinitePiecewiseAffineOn f (S i) := by
  classical
  let f : E → F := fun x => if hx : x ∈ ⋃ i, S i then
    Set.iUnionLift S e hagree (⋃ i, S i) Subset.rfl ⟨x, hx⟩ else 0
  have hfval (i : ι) (x : S i) : f x = e i x := by
    dsimp only [f]
    rw [dif_pos (mem_iUnion.mpr ⟨i, x.property⟩)]
    exact Set.iUnionLift_mk x _
  refine ⟨f, hfval, ?_⟩
  intro i
  obtain ⟨g, hg, hgval⟩ := he i
  exact hg.congr fun x hx => (hgval ⟨x, hx⟩).symm.trans (hfval i ⟨x, hx⟩).symm




theorem locallyPiecewiseAffineOn_of_finite_union_neighborhoods {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (S : ι → Set E)
    (hf : ∀ i, FinitePiecewiseAffineOn f (S i))
    (hlocal : ∀ x ∈ U, ∃ J : Finset ι, x ∈ interior (⋃ i ∈ J, S i)) :
    LocallyPiecewiseAffineOn f U := by
  classical
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  obtain ⟨J, hxJ⟩ := hlocal x hx
  have hPL := FinitePiecewiseAffineOn.iUnion (fun i : {i // i ∈ J} => hf i.val)
  have hset : (⋃ i : {i // i ∈ J}, S i.val) = ⋃ i ∈ J, S i := by
    ext y
    simp
  rw [hset] at hPL
  exact ⟨interior (⋃ i ∈ J, S i), hxJ,
    hPL.locallyPiecewiseAffineOn_of_subset_interior (hU.inter isOpen_interior)
      inter_subset_right⟩

end Geometry

namespace Homeomorph



theorem agree_symm_of_overlap {E F ι : Type*}
    [TopologicalSpace E] [TopologicalSpace F]
    (S : ι → Set E) (T : ι → Set F) (e : ∀ i, S i ≃ₜ T i)
    (hoverlap : ∀ i j (x : S i), (x : E) ∈ S j ↔ (e i x : F) ∈ T j)
    (hagree : ∀ i j (x : E) (hi : x ∈ S i) (hj : x ∈ S j),
      (e i ⟨x, hi⟩ : F) = e j ⟨x, hj⟩)
    (i j : ι) (y : F) (hi : y ∈ T i) (hj : y ∈ T j) :
    ((e i).symm ⟨y, hi⟩ : E) = (e j).symm ⟨y, hj⟩ := by
  let x := (e i).symm ⟨y, hi⟩
  have hxy : (e i x : F) = y := congrArg Subtype.val ((e i).apply_symm_apply ⟨y, hi⟩)
  have hxj : (x : E) ∈ S j := (hoverlap i j x).mpr (hxy.symm ▸ hj)
  have hEj : e j ⟨x, hxj⟩ = ⟨y, hj⟩ :=
    Subtype.ext ((hagree i j x x.property hxj).symm.trans hxy)
  have hinv := congrArg (e j).symm hEj
  rw [(e j).symm_apply_apply] at hinv
  exact congrArg Subtype.val hinv






theorem exists_openPartialHomeomorph_of_finitePL_family {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (S : ι → Set E) (T : ι → Set F) (e : ∀ i, S i ≃ₜ T i)
    (he : ∀ i, (e i).IsFinitePL)
    (hoverlap : ∀ i j (x : S i), (x : E) ∈ S j ↔ (e i x : F) ∈ T j)
    (hagree : ∀ i j (x : E) (hi : x ∈ S i) (hj : x ∈ S j),
      (e i ⟨x, hi⟩ : F) = e j ⟨x, hj⟩)
    (U : Set E) (V : Set F) (hU : IsOpen U) (hV : IsOpen V)
    (hUS : U ⊆ ⋃ i, S i) (hVT : V ⊆ ⋃ i, T i)
    (hUV : ∀ i (x : S i), (x : E) ∈ U ↔ (e i x : F) ∈ V)
    (hlocalS : ∀ x ∈ U, ∃ J : Finset ι, x ∈ interior (⋃ i ∈ J, S i))
    (hlocalT : ∀ y ∈ V, ∃ J : Finset ι, y ∈ interior (⋃ i ∈ J, T i)) :
    ∃ H : OpenPartialHomeomorph E F,
      H.source = U ∧ H.target = V ∧
      LocallyPiecewiseAffineOn H U ∧ LocallyPiecewiseAffineOn H.symm V ∧
      (∀ i (x : S i), H x = (e i x : F)) ∧
      (∀ i (y : T i), H.symm y = ((e i).symm y : E)) := by
  obtain ⟨f, hfval, hf⟩ := exists_finitePL_family_extension S
    (fun i x => (e i x : F)) he hagree
  obtain ⟨g, hgval, hg⟩ := exists_finitePL_family_extension T
    (fun i y => ((e i).symm y : E)) (fun i => (he i).symm)
    (agree_symm_of_overlap S T e hoverlap hagree)
  have hfPL := locallyPiecewiseAffineOn_of_finite_union_neighborhoods hU S hf hlocalS
  have hgPL := locallyPiecewiseAffineOn_of_finite_union_neighborhoods hV T hg hlocalT
  have hmap : MapsTo f U V := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hUS hx)
    rw [hfval i ⟨x, hxi⟩]
    exact (hUV i ⟨x, hxi⟩).mp hx
  have hinvmap : MapsTo g V U := by
    intro y hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp (hVT hy)
    rw [hgval i ⟨y, hyi⟩]
    apply (hUV i ((e i).symm ⟨y, hyi⟩)).mpr
    simpa only [(e i).apply_symm_apply] using hy
  have hleft : LeftInvOn g f U := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hUS hx)
    rw [hfval i ⟨x, hxi⟩, hgval, (e i).symm_apply_apply]
  have hright : LeftInvOn f g V := by
    intro y hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp (hVT hy)
    rw [hgval i ⟨y, hyi⟩, hfval, (e i).apply_symm_apply]
  let H : OpenPartialHomeomorph E F :=
    { toFun := f
      invFun := g
      source := U
      target := V
      map_source' := hmap
      map_target' := hinvmap
      left_inv' := hleft
      right_inv' := hright
      continuousOn_toFun := hfPL.continuousOn
      continuousOn_invFun := hgPL.continuousOn
      open_source := hU
      open_target := hV }
  exact ⟨H, rfl, rfl, hfPL, hgPL, hfval, hgval⟩

end Homeomorph
