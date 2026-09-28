import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalRetainedDiskCap



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

theorem exists_original_disk_rim_identification
    {X ι E F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d r : Set E} {c q : Set F} {f : E → X} {g : F → X}
    (hd : IsFinitePLBallPair P2 d r) (hc : IsFinitePLBallPair P2 c q)
    (hf : PolyhedralPLInCharts e f d) (hg : PolyhedralPLInCharts e g c)
    (hfi : InjOn f d) (hgi : InjOn g c) (hrim : f '' r = g '' q) :
    ∃ H : r ≃ₜ q, H.IsFinitePL ∧ ∀ x : r, f x = g (H x) := by
  classical
  let : CompactSpace c := isCompact_iff_compactSpace.mp hc.isCompact
  let G := hg.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h => Subtype.ext (hgi x.property y.property h)) |>.isEmbedding.toHomeomorph
  let gr : c ≃ₜ (g '' c) := G.trans (Homeomorph.setCongr (image_eq_range g c).symm)
  have hfr : MapsTo f r (g '' c) := by
    intro x hx
    exact image_mono hc.1 (hrim.subset ⟨x, hx, rfl⟩)
  let k : E → F := fun x => if hx : x ∈ r then gr.symm ⟨f x, hfr hx⟩ else 0
  have hkval (x : r) : k x = (gr.symm ⟨f x, hfr x.property⟩ : F) := by
    simp only [k, dif_pos x.property]
  have hkc : MapsTo k r c := by
    intro x hx
    rw [hkval ⟨x, hx⟩]
    exact (gr.symm ⟨f x, hfr hx⟩).property
  have hvalue (x : E) (hx : x ∈ r) : g (k x) = f x := by
    rw [hkval ⟨x, hx⟩]
    exact congrArg Subtype.val (gr.apply_symm_apply ⟨f x, hfr hx⟩)
  have hkcont : ContinuousOn k r := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (gr.symm.continuous.comp
      ((hf.continuousOn.mono hd.1).domRestrict.subtype_mk (fun x => hfr x.property)))
    convert h using 1
    funext x
    exact hkval x
  obtain ⟨n, P, _, hP, hPr⟩ := hd.exists_polygon_boundary
  let J := P.simplicialComplex hP
  have hJ := P.finite_simplicialComplex_faces hP
  have hJr : J.space = r := (P.simplicialComplex_space hP).trans hPr
  have hk : FinitePiecewiseAffineOn k r := by
    rw [← hJr]
    exact hg.finitePiecewiseAffineOn_lift he hgi J hJ (hkcont.mono hJr.subset)
      (fun _ hx => hkc (hJr.subset hx))
      ((hf.restrict_finite J hJ (hJr.subset.trans hd.1)).congr
        (fun x hx => (hvalue x (hJr.subset hx)).symm))
  have hki : InjOn k r := by
    intro x hx y hy hxy
    apply hfi (hd.1 hx) (hd.1 hy)
    rw [← hvalue x hx, ← hvalue y hy, hxy]
  have hkimage : k '' r = q := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hrim.subset ⟨x, hx, rfl⟩
      exact hgi (hc.1 hy) (hkc hx) (hyx.trans (hvalue x hx).symm) ▸ hy
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hrim.symm.subset ⟨y, hy, rfl⟩
      exact ⟨x, hx, hgi (hkc hx) (hc.1 hy) ((hvalue x hx).trans hxy)⟩
  obtain ⟨H, hH, hHval⟩ := hk.exists_homeomorph_image hki
  refine ⟨H.trans (Homeomorph.setCongr hkimage), hH.setCongr rfl hkimage, ?_⟩
  intro x
  change f x = g (H x)
  rw [hHval x, hvalue x x.property]

end PoincareConjecture.M76.Dehn.Annuli
