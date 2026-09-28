import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.UnionDisk.Product

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem exists_original_subdisk_coordinates
    {X ι E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d q : Set E} (hd : IsFinitePLBallPair P2 d q)
    {f : E → X} (hf : PolyhedralPLInCharts e f d) (hfi : InjOn f d)
    {j : V2 → X} (hj : PolyhedralPLInCharts e j Disk) (hji : InjOn j Disk)
    (hsubset : f '' d ⊆ j '' Disk) :
    ∃ u : E → V2, FinitePiecewiseAffineOn u d ∧ InjOn u d ∧
      MapsTo u d Disk ∧ ∀ x ∈ d, j (u x) = f x := by
  classical
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let G := hj.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h ↦ Subtype.ext (hji x.property y.property h)) |>.isEmbedding.toHomeomorph
  let gr : Disk ≃ₜ (j '' Disk) := G.trans (Homeomorph.setCongr (image_eq_range j Disk).symm)
  have hfr : MapsTo f d (j '' Disk) := fun x hx ↦ hsubset ⟨x, hx, rfl⟩
  let u : E → V2 := fun x ↦ if hx : x ∈ d then gr.symm ⟨f x, hfr hx⟩ else 0
  have huval (x : d) : u x = (gr.symm ⟨f x, hfr x.property⟩ : V2) := by
    simp only [u, dif_pos x.property]
  have humap : MapsTo u d Disk := by
    intro x hx
    rw [huval ⟨x, hx⟩]
    exact (gr.symm ⟨f x, hfr hx⟩).property
  have hvalue (x : E) (hx : x ∈ d) : j (u x) = f x := by
    rw [huval ⟨x, hx⟩]
    exact congrArg Subtype.val (gr.apply_symm_apply ⟨f x, hfr hx⟩)
  have hucont : ContinuousOn u d := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (gr.symm.continuous.comp
      (hf.continuousOn.domRestrict.subtype_mk (fun x ↦ hfr x.property)))
    convert h using 1
    funext x
    exact huval x
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJd, _⟩, _⟩, _⟩ := hd
  have hu : FinitePiecewiseAffineOn u d := by
    rw [← hJd]
    exact hj.finitePiecewiseAffineOn_lift he hji J hJ (hucont.mono hJd.subset)
      (fun _ hx ↦ humap (hJd.subset hx))
      ((hf.restrict_finite J hJ hJd.subset).congr
        (fun x hx ↦ (hvalue x (hJd.subset hx)).symm))
  refine ⟨u, hu, ?_, humap, hvalue⟩
  intro x hx y hy hxy
  apply hfi hx hy
  rw [← hvalue x hx, ← hvalue y hy, hxy]

end PoincareConjecture.M76.Dehn.Annuli
