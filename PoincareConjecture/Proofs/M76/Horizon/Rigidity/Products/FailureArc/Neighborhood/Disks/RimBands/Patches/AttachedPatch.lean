import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRelativeAttachedDiskExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

theorem exists_attached_patch_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s q d b u : Set E} {a z : E} {g : E → E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hds : d ⊆ s)
    (hu : IsFinitePLBallPair ℝ u {a,z}) (hub : u ⊆ b) (huq : u ⊆ q) (haz : a ≠ z)
    (hcontact : ∀ x ∈ d, x ∈ q ↔ x ∈ u)
    (hg : FinitePiecewiseAffineOn g d) (hgi : InjOn g d) (hgs : MapsTo g d s)
    (hfix : EqOn g id u) (hgcontact : ∀ x ∈ d, g x ∈ q ↔ x ∈ u) :
    ∃ H : s ≃ₜ s, H.IsFinitePL ∧
      (∀ x : d, (H ⟨x,hds x.property⟩ : E) = g x) ∧
      (∀ x : s, (x : E) ∈ q → H x = x) ∧
      (∀ x : s, (x : E) ∈ d ↔ (H x : E) ∈ g '' d) := by
  obtain ⟨w,hw,hboundary,huw⟩ := hd.exists_boundary_arc_complement hu hub haz
  have hud : u ⊆ d := hub.trans hd.1
  have hwd : w ⊆ d := subset_union_right.trans (hboundary.subset.trans hd.1)
  have hproper : w \ {a,z} ⊆ s \ q := by
    intro x hx
    refine ⟨hds (hwd hx.1),?_⟩
    intro hxq
    exact hx.2 (huw.subset ⟨(hcontact x (hwd hx.1)).mp hxq,hx.1⟩)
  have hgu : g '' u = u := by
    rw [image_congr hfix,image_id]
  have hga : g a = a := hfix (hu.1 (by simp))
  have hgz : g z = z := hfix (hu.1 (by simp))
  have hD : IsFinitePLBallPair (ℝ × ℝ) (g '' d) (u ∪ g '' w) := by
    have hh := hd.image hg hgi
    rwa [← hboundary,image_union,hgu] at hh
  have hW : IsFinitePLBallPair ℝ (g '' w) {a,z} := by
    have hh := hw.image_of_subset hg hwd hgi
    rwa [image_pair,hga,hgz] at hh
  have hProper : (g '' w) \ {a,z} ⊆ s \ q := by
    rintro x ⟨⟨y,hy,rfl⟩,hne⟩
    refine ⟨hgs (hwd hy),?_⟩
    intro hxq
    have hyu := (hgcontact y (hwd hy)).mp hxq
    have hyend : y ∈ ({a,z} : Set E) := huw.subset ⟨hyu,hy⟩
    exact hne ((hfix hyu).symm ▸ hyend)
  obtain ⟨G,hG,hGval⟩ := hg.exists_homeomorph_image hgi
  have hmemu (x : d) : (x : E) ∈ u ↔ (G x : E) ∈ u := by
    rw [hGval]
    exact (hgi.mem_image_iff hud x.property).symm.trans (by rw [hgu])
  have hmemw (x : d) : (x : E) ∈ w ↔ (G x : E) ∈ g '' w := by
    rw [hGval]
    exact (hgi.mem_image_iff hwd x.property).symm
  have hid {v r : Set E} (hv : IsFinitePLBallPair ℝ v r) :
      FinitePiecewiseAffineOn (id : E → E) v := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKv,_⟩,_⟩,_⟩ := hv
    exact ⟨K,hK,hKv,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩
  obtain ⟨v,hv,hq,_⟩ := hs.exists_boundary_arc_complement hu huq haz
  have hidq : (Homeomorph.refl q).IsFinitePL := by
    refine ⟨id,?_,fun _ => rfl⟩
    rw [← hq]
    exact finitePiecewiseAffineOn_union (hid hu) (hid hv)
  obtain ⟨H,hH,hHd,hHq,hmem,_⟩ := hs.exists_extension_of_attached_disk_and_boundary hs
    (hboundary.symm ▸ hd) hds hD (image_subset_iff.mpr hgs)
    hu huq hw haz hproper hu huq hW haz hProper G hG hmemu hmemw
    (Homeomorph.refl q) hidq (by
      intro x
      exact (hGval ⟨x,hud x.property⟩).trans (hfix x.property) |>.symm)
  refine ⟨H,hH,?_,?_,hmem⟩
  · intro x
    exact (congrArg Subtype.val (hHd x)).trans (hGval x)
  · intro x hx
    exact hHq ⟨x,hx⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
