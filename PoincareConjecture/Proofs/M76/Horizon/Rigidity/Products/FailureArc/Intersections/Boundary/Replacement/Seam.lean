import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalRetainedDiskCap



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_interval_identification
    {X ι E F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {W : Set E} {Z : Set F} {a b : E} {c d : F} {f : E → X} {g : F → X}
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hZ : IsFinitePLBallPair ℝ Z {c, d})
    (hf : PolyhedralPLInCharts e f W) (hg : PolyhedralPLInCharts e g Z)
    (hfi : InjOn f W) (hgi : InjOn g Z) (himage : f '' W = g '' Z) :
    ∃ H : W ≃ₜ Z, H.IsFinitePL ∧ ∀ x : W, f x = g (H x) := by
  classical
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  let G := hg.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h ↦ Subtype.ext (hgi x.property y.property h)) |>.isEmbedding.toHomeomorph
  let gr : Z ≃ₜ (g '' Z) := G.trans (Homeomorph.setCongr (image_eq_range g Z).symm)
  have hfr : MapsTo f W (g '' Z) := fun x hx ↦ himage.subset ⟨x, hx, rfl⟩
  let k : E → F := fun x ↦ if hx : x ∈ W then gr.symm ⟨f x, hfr hx⟩ else 0
  have hkval (x : W) : k x = (gr.symm ⟨f x, hfr x.property⟩ : F) := by
    simp only [k, dif_pos x.property]
  have hkc : MapsTo k W Z := by
    intro x hx
    rw [hkval ⟨x, hx⟩]
    exact (gr.symm ⟨f x, hfr hx⟩).property
  have hvalue (x : E) (hx : x ∈ W) : g (k x) = f x := by
    rw [hkval ⟨x, hx⟩]
    exact congrArg Subtype.val (gr.apply_symm_apply ⟨f x, hfr hx⟩)
  have hkcont : ContinuousOn k W := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (gr.symm.continuous.comp
      (hf.continuousOn.domRestrict.subtype_mk (fun x ↦ hfr x.property)))
    convert h using 1
    funext x
    exact hkval x
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJW, _⟩, _⟩, _⟩ := hW
  have hk : FinitePiecewiseAffineOn k W := by
    rw [← hJW]
    exact hg.finitePiecewiseAffineOn_lift he hgi J hJ (hkcont.mono hJW.subset)
      (fun _ hx ↦ hkc (hJW.subset hx))
      ((hf.restrict_finite J hJ hJW.subset).congr
        (fun x hx ↦ (hvalue x (hJW.subset hx)).symm))
  have hki : InjOn k W := by
    intro x hx y hy hxy
    apply hfi hx hy
    rw [← hvalue x hx, ← hvalue y hy, hxy]
  have hkimage : k '' W = Z := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hkc hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := himage.symm.subset ⟨y, hy, rfl⟩
      exact ⟨x, hx, hgi (hkc hx) hy ((hvalue x hx).trans hxy)⟩
  obtain ⟨H, hH, hHval⟩ := hk.exists_homeomorph_image hki
  refine ⟨H.trans (Homeomorph.setCongr hkimage), hH.setCongr rfl hkimage, ?_⟩
  intro x
  change f x = g (H x)
  rw [hHval x, hvalue x x.property]

end PoincareConjecture.M76.Dehn.Annuli
