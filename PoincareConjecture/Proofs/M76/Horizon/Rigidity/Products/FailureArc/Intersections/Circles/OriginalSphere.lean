import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.DiskRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.ModelSphere



set_option autoImplicit false
open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)

theorem nonempty_original_sphere_of_disk_union
    {X ι E F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d r : Set E} {c q : Set F} {f : E → X} {g : F → X}
    (hd : IsFinitePLBallPair P2 d r) (hc : IsFinitePLBallPair P2 c q)
    (hf : PolyhedralPLInCharts e f d) (hg : PolyhedralPLInCharts e g c)
    (hfi : InjOn f d) (hgi : InjOn g c)
    (hrim : f '' r = g '' q) (hinter : (f '' d) ∩ (g '' c) = f '' r) :
    Nonempty (ChartwisePLSphere e ((f '' d) ∪ (g '' c))) := by
  obtain ⟨H, hH, hHrim⟩ := (isFinitePLBallPair_cap 1).exists_homeomorph hd
  obtain ⟨u, hu, huval⟩ := hH
  have humap : MapsTo u (cap 1) d := by
    intro x hx
    rw [← huval ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hui : InjOn u (cap 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((huval ⟨x, hx⟩).trans (hxy.trans (huval ⟨y, hy⟩).symm))))
  have huimage : u '' cap 1 = d := by
    apply Subset.antisymm
    · exact image_subset_iff.mpr humap
    · intro y hy
      obtain ⟨x, hx⟩ := H.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (huval x).symm.trans (congrArg Subtype.val hx)⟩
  have hurim : u '' rim = r := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hm := (hHrim ⟨x, (isFinitePLBallPair_cap 1).1 hx⟩).mp hx
      rwa [huval] at hm
    · intro y hy
      obtain ⟨x, hx⟩ := H.surjective ⟨y, hd.1 hy⟩
      have hm : (x : P3) ∈ rim := (hHrim x).mpr (by rw [hx]; exact hy)
      exact ⟨x, hm, (huval x).symm.trans (congrArg Subtype.val hx)⟩
  have hfu : PolyhedralPLInCharts e (f ∘ u) (cap 1) := by
    have hucopy := hu
    obtain ⟨K, hK, hKs, _⟩ := hucopy
    rw [← hKs]
    exact hf.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hu)
      (fun _ hx => humap (hKs.subset hx))
  have hfui : InjOn (f ∘ u) (cap 1) := hfi.comp hui humap
  have hfurim : (f ∘ u) '' rim = g '' q := by rw [image_comp, hurim, hrim]
  obtain ⟨er, her, herval⟩ := exists_original_disk_rim_identification he
    (isFinitePLBallPair_cap 1) hc hfu hg hfui hgi hfurim
  obtain ⟨G, hG, hGrim, _⟩ := isFinitePLBallPair_disk.exists_extension hc er her
  obtain ⟨v, hv, hvval⟩ := hG
  have hvmap : MapsTo v disk c := by
    intro x hx
    rw [← hvval ⟨x, hx⟩]
    exact (G ⟨x, hx⟩).property
  have hvi : InjOn v disk := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (G.injective (Subtype.ext
      ((hvval ⟨x, hx⟩).trans (hxy.trans (hvval ⟨y, hy⟩).symm))))
  have hvimage : v '' disk = c := by
    apply Subset.antisymm
    · exact image_subset_iff.mpr hvmap
    · intro y hy
      obtain ⟨x, hx⟩ := G.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (hvval x).symm.trans (congrArg Subtype.val hx)⟩
  have hgv : PolyhedralPLInCharts e (g ∘ v) disk := by
    have hvcopy := hv
    obtain ⟨K, hK, hKs, _⟩ := hvcopy
    rw [← hKs]
    exact hg.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hv)
      (fun _ hx => hvmap (hKs.subset hx))
  have hagree : EqOn (f ∘ u) (g ∘ v) rim := by
    intro x hx
    have hvx : v x = (er ⟨x, hx⟩ : F) :=
      (hvval ⟨x, isFinitePLBallPair_disk.1 hx⟩).symm.trans
        (congrArg Subtype.val (hGrim ⟨x, hx⟩))
    exact (herval ⟨x, hx⟩).trans (congrArg g hvx.symm)
  have hbetween : ((f ∘ u) '' cap 1) ∩ ((g ∘ v) '' disk) = (f ∘ u) '' rim := by
    rw [image_comp, image_comp, image_comp, huimage, hvimage, hurim, hinter]
  have hs := nonempty_original_sphere_of_standard_disk_maps he hfu hgv
    hfui (hgi.comp hvi hvmap) hagree hbetween
  simpa only [image_comp, huimage, hvimage] using hs

end PoincareConjecture.M76.Dehn.Annuli
