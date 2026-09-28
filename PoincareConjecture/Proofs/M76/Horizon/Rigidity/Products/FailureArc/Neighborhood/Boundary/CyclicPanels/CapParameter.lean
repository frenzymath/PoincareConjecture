import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.DiskRim

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.CyclicPanels

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_disk_parameter_of_rim
    {X ι E F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d r : Set E} {c q : Set F} {φ : E → X} {f : F → X}
    (hd : IsFinitePLBallPair P2 d r) (hc : IsFinitePLBallPair P2 c q)
    (hφ : PolyhedralPLInCharts e φ r) (hf : PolyhedralPLInCharts e f c)
    (hφi : InjOn φ r) (hfi : InjOn f c) (hrim : φ '' r = f '' q) :
    ∃ g : E → X, PolyhedralPLInCharts e g d ∧ InjOn g d ∧
      EqOn g φ r ∧ g '' d = f '' c ∧ g '' r = f '' q := by
  classical
  let : CompactSpace c := isCompact_iff_compactSpace.mp hc.isCompact
  let H := hf.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h => Subtype.ext (hfi x.property y.property h)) |>.isEmbedding.toHomeomorph
  let gr : c ≃ₜ (f '' c) := H.trans (Homeomorph.setCongr (image_eq_range f c).symm)
  have hφr : MapsTo φ r (f '' c) := by
    intro x hx
    exact image_mono hc.1 (hrim.subset ⟨x,hx,rfl⟩)
  let k : E → F := fun x => if hx : x ∈ r then gr.symm ⟨φ x,hφr hx⟩ else 0
  have hkval (x : r) : k x = (gr.symm ⟨φ x,hφr x.property⟩ : F) := by
    simp only [k,dif_pos x.property]
  have hkc : MapsTo k r c := by
    intro x hx
    rw [hkval ⟨x,hx⟩]
    exact (gr.symm ⟨φ x,hφr hx⟩).property
  have hvalue (x : E) (hx : x ∈ r) : f (k x) = φ x := by
    rw [hkval ⟨x,hx⟩]
    exact congrArg Subtype.val (gr.apply_symm_apply ⟨φ x,hφr hx⟩)
  have hkcont : ContinuousOn k r := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (gr.symm.continuous.comp
      (hφ.continuousOn.domRestrict.subtype_mk (fun x => hφr x.property)))
    convert h using 1
    funext x
    exact hkval x
  obtain ⟨n,P,_,hP,hPr⟩ := hd.exists_polygon_boundary
  let J := P.simplicialComplex hP
  have hJ := P.finite_simplicialComplex_faces hP
  have hJr : J.space = r := (P.simplicialComplex_space hP).trans hPr
  have hk : FinitePiecewiseAffineOn k r := by
    rw [← hJr]
    exact hf.finitePiecewiseAffineOn_lift he hfi J hJ (hkcont.mono hJr.subset)
      (fun _ hx => hkc (hJr.subset hx))
      ((hJr.symm ▸ hφ).congr (fun x hx => (hvalue x (hJr.subset hx)).symm))
  have hki : InjOn k r := by
    intro x hx y hy hxy
    apply hφi hx hy
    rw [← hvalue x hx,← hvalue y hy,hxy]
  have hkimage : k '' r = q := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hyx⟩ := hrim.subset ⟨x,hx,rfl⟩
      exact hfi (hc.1 hy) (hkc hx) (hyx.trans (hvalue x hx).symm) ▸ hy
    · intro y hy
      obtain ⟨x,hx,hxy⟩ := hrim.symm.subset ⟨y,hy,rfl⟩
      exact ⟨x,hx,hfi (hkc hx) (hc.1 hy) ((hvalue x hx).trans hxy)⟩
  obtain ⟨B,hB,hBval⟩ := hk.exists_homeomorph_image hki
  let b := B.trans (Homeomorph.setCongr hkimage)
  have hb : b.IsFinitePL := hB.setCongr rfl hkimage
  obtain ⟨G,hG,hGr,_⟩ := hd.exists_extension hc b hb
  obtain ⟨v,hv,hvval⟩ := hG
  have hvmap : MapsTo v d c := by
    intro x hx
    rw [← hvval ⟨x,hx⟩]
    exact (G ⟨x,hx⟩).property
  have hvi : InjOn v d := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (G.injective (Subtype.ext
      ((hvval ⟨x,hx⟩).trans (hxy.trans (hvval ⟨y,hy⟩).symm))))
  have hvimage : v '' d = c := by
    apply Subset.antisymm (image_subset_iff.mpr hvmap)
    intro y hy
    obtain ⟨x,hx⟩ := G.surjective ⟨y,hy⟩
    exact ⟨x,x.property,(hvval x).symm.trans (congrArg Subtype.val hx)⟩
  have hkeep : EqOn (f ∘ v) φ r := by
    intro x hx
    have hvr : v x = k x := (hvval ⟨x,hd.1 hx⟩).symm.trans
      ((congrArg Subtype.val (hGr ⟨x,hx⟩)).trans (hBval ⟨x,hx⟩))
    exact (congrArg f hvr).trans (hvalue x hx)
  have hPL : PolyhedralPLInCharts e (f ∘ v) d := by
    obtain ⟨K,hK,hKs,_⟩ := hv
    exact hKs ▸ hf.comp_finitePiecewiseAffineOn K hK
      ⟨K,hK,rfl,by assumption⟩ (fun _ hx => hvmap (hKs ▸ hx))
  refine ⟨f ∘ v,hPL,hfi.comp hvi hvmap,hkeep,?_,?_⟩
  · rw [image_comp,hvimage]
  · rw [hkeep.image_eq,hrim]

end PoincareConjecture.M76.Dehn.Annuli.CyclicPanels
