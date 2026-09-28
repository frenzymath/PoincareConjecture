import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.DiskRim
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.Disjoint.Source



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

theorem exists_original_interior_disk_replacement
    {X ι E : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hsub : closure P.inside ⊆ interior J.space)
    {f : P2 → X} (hf : PolyhedralPLInCharts e f J.space) (hfi : InjOn f J.space)
    {c q : Set E} {g : E → X}
    (hc : IsFinitePLBallPair P2 c q)
    (hg : PolyhedralPLInCharts e g c) (hgi : InjOn g c)
    (hrim : f '' P.boundary ℝ = g '' q)
    (hcontact : (g '' c) ∩ (f '' (J.space \ P.inside)) = f '' P.boundary ℝ) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k J.space ∧ InjOn k J.space ∧
      EqOn k f (J.space \ P.inside) ∧ EqOn k f (frontier J.space) ∧
      k '' closure P.inside = g '' c ∧
      k '' J.space = (f '' (J.space \ P.inside)) ∪ (g '' c) := by
  classical
  have hd := P.isFinitePLBallPair_closed_inside hP hPi
  have hdJ : closure P.inside ⊆ J.space := hsub.trans interior_subset
  have hdcopy := hd
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨D, hD, hDs, _⟩, _⟩, _⟩ := hdcopy
  obtain ⟨O, hO, hOs, _, _⟩ := _root_.Dehn.exists_finite_interior_carrier_complement
    J D hJ hD (hDs.subset.trans hsub)
  rw [hDs, P.interior_closure_inside hP hPi] at hOs
  have hfD : PolyhedralPLInCharts e f (closure P.inside) :=
    hDs ▸ hf.restrict_finite D hD (hDs.subset.trans hdJ)
  obtain ⟨er, her, herval⟩ := exists_original_disk_rim_identification he hd hc
    hfD hg (hfi.mono hdJ) hgi hrim
  obtain ⟨H, hH, hHrim, _⟩ := hd.exists_extension hc er her
  obtain ⟨v, hv, hvval⟩ := hH
  have hvmap : MapsTo v (closure P.inside) c := by
    intro x hx
    rw [← hvval ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hvi : InjOn v (closure P.inside) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hvval ⟨x, hx⟩).trans (hxy.trans (hvval ⟨y, hy⟩).symm))))
  have hvimage : v '' closure P.inside = c := by
    apply Subset.antisymm (image_subset_iff.mpr hvmap)
    intro y hy
    obtain ⟨x, hx⟩ := H.surjective ⟨y, hy⟩
    exact ⟨x, x.property, (hvval x).symm.trans (congrArg Subtype.val hx)⟩
  have hboundary : EqOn (g ∘ v) f (P.boundary ℝ) := by
    intro x hx
    have hvx : v x = (er ⟨x, hx⟩ : E) :=
      (hvval ⟨x, hd.1 hx⟩).symm.trans (congrArg Subtype.val (hHrim ⟨x, hx⟩))
    exact (congrArg g hvx).trans (herval ⟨x, hx⟩).symm
  have hgv : PolyhedralPLInCharts e (g ∘ v) D.space :=
    hg.comp_finitePiecewiseAffineOn D hD (hDs.symm ▸ hv)
      (fun _ hx => hvmap (hDs.subset hx))
  have hseam : closure P.inside ∩ (J.space \ P.inside) = P.boundary ℝ := by
    rw [← P.frontier_inside hP hPi, frontier, (P.isOpen_inside hP hPi).interior_eq]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hdJ hx.1, hx.2⟩⟩
  obtain ⟨k, hk, hkd, hko⟩ := _root_.Dehn.exists_circle_attachment_map_union he D O hD hO
    hgv (hf.restrict_finite O hO (hOs.subset.trans sdiff_subset))
    (fun _ hx hy => hboundary (hseam.subset ⟨hDs.subset hx, hOs.subset hy⟩))
  have hkd' : EqOn k (g ∘ v) (closure P.inside) := hDs ▸ hkd
  have hko' : EqOn k f (J.space \ P.inside) := hOs ▸ hko
  have hwhole : closure P.inside ∪ (J.space \ P.inside) = J.space := by
    apply Subset.antisymm (union_subset hdJ sdiff_subset)
    intro x hx
    by_cases hi : x ∈ P.inside
    · exact Or.inl (subset_closure hi)
    · exact Or.inr ⟨hx, hi⟩
  have hmix (x y : P2) (hx : x ∈ closure P.inside) (hy : y ∈ J.space \ P.inside)
      (hxy : g (v x) = f y) : x = y := by
    obtain ⟨z, hz, hzy⟩ := hcontact.subset
      ⟨⟨v x, hvmap hx, hxy⟩, ⟨y, hy, rfl⟩⟩
    have hzy' : z = y := hfi (hdJ (hd.1 hz)) hy.1 hzy
    have hybd : y ∈ P.boundary ℝ := hzy' ▸ hz
    exact hvi hx (hd.1 hybd) (hgi (hvmap hx) (hvmap (hd.1 hybd))
      (hxy.trans (hboundary hybd).symm))
  have hki : InjOn k J.space := by
    intro x hx y hy hxy
    rcases hwhole.symm.subset hx with hx | hx <;>
      rcases hwhole.symm.subset hy with hy | hy
    · exact hvi hx hy (hgi (hvmap hx) (hvmap hy)
        ((hkd' hx).symm.trans (hxy.trans (hkd' hy))))
    · exact hmix x y hx hy ((hkd' hx).symm.trans (hxy.trans (hko' hy)))
    · exact (hmix y x hy hx ((hkd' hy).symm.trans (hxy.symm.trans (hko' hx)))).symm
    · exact hfi hx.1 hy.1 ((hko' hx).symm.trans (hxy.trans (hko' hy)))
  have hkimage : k '' closure P.inside = g '' c := by
    rw [image_congr hkd', image_comp, hvimage]
  refine ⟨k, ?_, hki, hko', ?_, hkimage, ?_⟩
  · simpa only [hDs, hOs, hwhole] using hk
  · intro x hx
    exact hko' ⟨(J.isCompact_space_of_finite hJ).isClosed.frontier_subset hx,
      fun hi => hx.2 (hsub (subset_closure hi))⟩
  · conv_lhs => rw [← hwhole, image_union, hkimage, image_congr hko']
    exact union_comm _ _

end PoincareConjecture.M76.Dehn.Annuli
