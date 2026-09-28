import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalSubdiskUniqueness

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

private theorem original_disk_inverse_lift
    {X E T ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {D : Set E} {j : E → X} (hj : PolyhedralPLInCharts e j D) (hji : InjOn j D)
    (k : X → E) (hkc : ContinuousOn k (j '' D))
    (hright : ∀ x ∈ j '' D,j (k x)=x) (hkD : MapsTo k (j '' D) D)
    {W : Set T} {u v : T} {p : T → X}
      (hW : IsFinitePLBallPair ℝ W {u,v}) (hp : PolyhedralPLInCharts e p W)
      (hpi : InjOn p W) (hpD : p '' W ⊆ j '' D) :
      FinitePiecewiseAffineOn (k ∘ p) W ∧ InjOn (k ∘ p) W := by
    have heq (x : T) (hx : x ∈ W) : j (k (p x)) = p x := hright _ (hpD ⟨x,hx,rfl⟩)
    constructor
    · obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKW,_⟩,_⟩,_⟩ := hW
      rw [←hKW]
      apply hj.finitePiecewiseAffineOn_lift he hji K hK
        ((hkc.comp hp.continuousOn (fun x hx => hpD ⟨x,hx,rfl⟩)).mono hKW.subset)
        (fun x hx => hkD (hpD ⟨x,hKW.subset hx,rfl⟩))
      exact (hp.restrict_finite K hK hKW.subset).congr
        (fun x hx => (heq x (hKW.subset hx)).symm)
    · intro x hx y hy hh
      exact hpi hx hy ((heq x hx).symm.trans ((congrArg j hh).trans (heq y hy)))

theorem exists_original_disk_boundary_arc_split
    {X E F G ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {D r : Set E} {U : Set F} {V : Set G} {a b : F} {c d : G}
    {j : E → X} {f : F → X} {g : G → X}
    (hD : IsFinitePLBallPair P2 D r)
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hV : IsFinitePLBallPair ℝ V {c,d})
    (hj : PolyhedralPLInCharts e j D) (hji : InjOn j D)
    (hf : PolyhedralPLInCharts e f U) (hfi : InjOn f U)
    (hg : PolyhedralPLInCharts e g V) (hgi : InjOn g V)
    (hab : a ≠ b) (h0 : f a = g c) (h1 : f b = g d)
    (hrim : j '' r = f '' U ∪ g '' V)
    (hinter : f '' U ∩ g '' V = {f a,f b}) :
    ∃ A B : Set E, ∃ x y : E,
      IsFinitePLBallPair ℝ A {x,y} ∧ IsFinitePLBallPair ℝ B {x,y} ∧
      A ∪ B = r ∧ A ∩ B = {x,y} ∧ x ≠ y ∧
      j '' A = f '' U ∧ j '' B = g '' V ∧ j x = f a ∧ j y = f b := by
  classical
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  have hje := (hj.continuousOn.domRestrict.isClosedEmbedding
    (fun x y hh => Subtype.ext (hji x.property y.property hh))).isEmbedding
  obtain ⟨k,hkc,hleft,hright,hkD⟩ := hje.exists_inverse_on_image
  have hfD : f '' U ⊆ j '' D := fun x hx =>
    image_mono hD.1 (hrim.symm.subset (Or.inl hx))
  have hgD : g '' V ⊆ j '' D := fun x hx =>
    image_mono hD.1 (hrim.symm.subset (Or.inr hx))
  have hfK := original_disk_inverse_lift he hj hji k hkc hright hkD hU hf hfi hfD
  have hgK := original_disk_inverse_lift he hj hji k hkc hright hkD hV hg hgi hgD
  let A := (k ∘ f) '' U
  let B := (k ∘ g) '' V
  have hA := hU.image hfK.1 hfK.2
  have hB := hV.image hgK.1 hgK.2
  simp only [image_insert_eq,image_singleton,Function.comp_apply] at hA hB
  rw [←h0,←h1] at hB
  have hjA : j '' A = f '' U := by
    rw [←image_comp]
    exact image_congr (fun x hx => hright _ (hfD ⟨x,hx,rfl⟩))
  have hjB : j '' B = g '' V := by
    rw [←image_comp]
    exact image_congr (fun x hx => hright _ (hgD ⟨x,hx,rfl⟩))
  have hAD : A ⊆ D := by rintro _ ⟨x,hx,rfl⟩; exact hkD (hfD ⟨x,hx,rfl⟩)
  have hBD : B ⊆ D := by rintro _ ⟨x,hx,rfl⟩; exact hkD (hgD ⟨x,hx,rfl⟩)
  have hFA : j (k (f a)) = f a := hright _ (hfD ⟨a,hU.1 (by simp),rfl⟩)
  have hFB : j (k (f b)) = f b := hright _ (hfD ⟨b,hU.1 (by simp),rfl⟩)
  refine ⟨A,B,k (f a),k (f b),hA,hB,?_,?_,?_,hjA,hjB,hFA,hFB⟩
  · apply Subset.antisymm
    · intro x hx
      have hxD : x ∈ D := hx.elim (fun h => hAD h) (fun h => hBD h)
      have hxj : j x ∈ j '' r := by
        rw [hrim]
        exact hx.elim (fun h => Or.inl (hjA.subset ⟨x,h,rfl⟩))
          (fun h => Or.inr (hjB.subset ⟨x,h,rfl⟩))
      obtain ⟨y,hy,hh⟩ := hxj
      exact hji (hD.1 hy) hxD hh ▸ hy
    · intro x hx
      rcases hrim.subset (mem_image_of_mem j hx) with hxf | hxg
      · obtain ⟨y,hy,hh⟩ := hjA.symm.subset hxf
        exact Or.inl (hji (hAD hy) (hD.1 hx) hh ▸ hy)
      · obtain ⟨y,hy,hh⟩ := hjB.symm.subset hxg
        exact Or.inr (hji (hBD hy) (hD.1 hx) hh ▸ hy)
  · apply Subset.antisymm
    · intro x hx
      have hh := hinter.subset ⟨hjA.subset ⟨x,hx.1,rfl⟩,hjB.subset ⟨x,hx.2,rfl⟩⟩
      simp only [mem_insert_iff,mem_singleton_iff] at hh ⊢
      rcases hh with hh | hh
      · exact Or.inl ((hleft _ (hAD hx.1)).symm.trans (congrArg k hh))
      · exact Or.inr ((hleft _ (hAD hx.1)).symm.trans (congrArg k hh))
    · intro x hx
      exact ⟨hA.1 hx,hB.1 hx⟩
  · intro hh
    exact hab (hfi (hU.1 (by simp)) (hU.1 (by simp))
      (hFA.symm.trans ((congrArg j hh).trans hFB)))

end PoincareConjecture.M76
