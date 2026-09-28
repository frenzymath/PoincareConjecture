import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.MarkedBall.Construction
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.MarkedBall

theorem exists_disk_with_prescribed_rim
    {E F X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    {s q : Set E} {c r : Set F}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c r)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKq : K.space = q)
    {f : E → X} {g : F → X}
    (hf : PolyhedralPLInCharts e f q) (hfi : InjOn f q)
    (hg : PolyhedralPLInCharts e g c) (hgi : InjOn g c)
    (himage : f '' q = g '' r) :
    ∃ k : E → X, PolyhedralPLInCharts e k s ∧ InjOn k s ∧
      k '' s = g '' c ∧ EqOn k f q := by
  classical
  let : CompactSpace c := isCompact_iff_compactSpace.mp hc.isCompact
  let : CompactSpace q := isCompact_iff_compactSpace.mp
    (hKq ▸ K.isCompact_space_of_finite hK)
  let gc : c → g '' c := fun z => ⟨g z, mem_image_of_mem g z.property⟩
  have hgc : Function.Bijective gc := by
    constructor
    · intro x y h
      exact Subtype.ext (hgi x.property y.property (congrArg Subtype.val h))
    · rintro ⟨_, z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let G : c ≃ₜ g '' c :=
    (show Continuous (Equiv.ofBijective gc hgc) from
      hg.continuousOn.domRestrict.subtype_mk _).homeoOfEquivCompactToT2
  have hmem (z : E) (hz : z ∈ q) : f z ∈ g '' c :=
    image_mono hc.1 (himage.subset (mem_image_of_mem f hz))
  let u : E → F := fun z => if hz : z ∈ q then G.symm ⟨f z, hmem z hz⟩ else 0
  have huval (z : q) : u z = (G.symm ⟨f z, hmem z z.property⟩ : F) := dif_pos z.property
  have hug (z : E) (hz : z ∈ q) : g (u z) = f z := by
    rw [huval ⟨z, hz⟩]
    exact congrArg Subtype.val (G.apply_symm_apply ⟨f z, hmem z hz⟩)
  have humap : MapsTo u q c := by
    intro z hz
    rw [huval ⟨z, hz⟩]
    exact (G.symm ⟨f z, hmem z hz⟩).property
  have hucont : ContinuousOn u q := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp (G.symm.continuous.comp
      (hf.continuousOn.domRestrict.subtype_mk _))).congr (fun z => (huval z).symm)
  have hurim : MapsTo u q r := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := himage.subset (mem_image_of_mem f hz)
    exact hgi (humap hz) (hc.1 hy) ((hug z hz).trans hyz.symm) ▸ hy
  let ur : q → r := fun z => ⟨u z, hurim z.property⟩
  have hur : Function.Bijective ur := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply hfi x.property y.property
      exact (hug x x.property).symm.trans
        ((congrArg g (congrArg Subtype.val h)).trans (hug y y.property))
    · intro y
      obtain ⟨x, hx, hxy⟩ := himage.symm.subset (mem_image_of_mem g y.property)
      exact ⟨⟨x, hx⟩, Subtype.ext
        (hgi (humap hx) (hc.1 y.property) ((hug x hx).trans hxy))⟩
  let Hrim : q ≃ₜ r :=
    (show Continuous (Equiv.ofBijective ur hur) from
      hucont.domRestrict.subtype_mk _).homeoOfEquivCompactToT2
  have huPL : FinitePiecewiseAffineOn u q := by
    have hgu : PolyhedralPLInCharts e (g ∘ u) q := hf.congr (fun z hz => (hug z hz).symm)
    exact hKq ▸ hg.finitePiecewiseAffineOn_lift hcompat hgi K hK
      (hKq.symm ▸ hucont) (hKq.symm ▸ humap) (hKq.symm ▸ hgu)
  have hHrim : Hrim.IsFinitePL := ⟨u, huPL, fun _ => rfl⟩
  obtain ⟨H, hH, hboundary, _⟩ := hs.exists_extension hc Hrim hHrim
  obtain ⟨v, hv, hvval⟩ := hH
  have hvmap : MapsTo v s c := by
    intro z hz
    rw [← hvval ⟨z, hz⟩]
    exact (H ⟨z, hz⟩).property
  refine ⟨g ∘ v, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL, hLs, hfaces⟩ := hv
    exact hLs ▸ hg.comp_finitePiecewiseAffineOn L hL ⟨L, hL, rfl, hfaces⟩
      (fun z hz => hvmap (hLs.subset hz))
  · intro x hx y hy hxy
    apply congrArg Subtype.val (H.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) _)
    exact Subtype.ext ((hvval ⟨x, hx⟩).trans
      ((hgi (hvmap hx) (hvmap hy) hxy).trans (hvval ⟨y, hy⟩).symm))
  · rw [image_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hvmap hz
    · intro hy
      exact ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property,
        (hvval _).symm.trans (congrArg Subtype.val (H.apply_symm_apply ⟨y, hy⟩))⟩
  · intro z hz
    change g (v z) = f z
    have h := congrArg Subtype.val (hboundary ⟨z, hz⟩)
    have hvu : v z = u z := (hvval ⟨z, hs.1 hz⟩).symm.trans h
    rw [hvu, hug z hz]

end PoincareConjecture.M76.Dehn.Annuli.MarkedBall
