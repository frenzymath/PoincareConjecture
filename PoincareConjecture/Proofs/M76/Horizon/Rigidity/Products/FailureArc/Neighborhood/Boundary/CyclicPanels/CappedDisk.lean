import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.CapParameter
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Annulus

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CyclicPanels

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_capped_annulus_disk
    {X ι F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    {g : P2 → X} {f : F → X} {c q : Set F}
    (hg : PolyhedralPLInCharts e g (squareAnnulus L d))
    (hgi : InjOn g (squareAnnulus L d))
    (hc : IsFinitePLBallPair P2 c q)
    (hf : PolyhedralPLInCharts e f c) (hfi : InjOn f c)
    (hrim : g '' frontier (_root_.Dehn.annulusSquare L d) = f '' q)
    (hcontact : (g '' squareAnnulus L d) ∩ (f '' c) =
      g '' frontier (_root_.Dehn.annulusSquare L d)) :
    ∃ k : P2 → X,
      PolyhedralPLInCharts e k (_root_.Dehn.annulusSquare L (-d)) ∧
      InjOn k (_root_.Dehn.annulusSquare L (-d)) ∧
      EqOn k g (squareAnnulus L d) ∧
      k '' _root_.Dehn.annulusSquare L (-d) = (f '' c) ∪ (g '' squareAnnulus L d) ∧
      k '' frontier (_root_.Dehn.annulusSquare L (-d)) =
        g '' frontier (_root_.Dehn.annulusSquare L (-d)) := by
  have hinner := _root_.Dehn.isFinitePLBallPair_annulusSquare (show 2 * d < L by linarith)
  obtain ⟨hunion,hinter,houter⟩ := _root_.Dehn.annulusSquare_partition (L := L) hd
  have hrAnn : frontier (_root_.Dehn.annulusSquare L d) ⊆ squareAnnulus L d :=
    fun _ hx => (hinter.symm.subset hx).2
  obtain ⟨n,P,_,hP,hPr⟩ := hinner.exists_polygon_boundary
  let J := P.simplicialComplex hP
  have hJ := P.finite_simplicialComplex_faces hP
  have hJs : J.space = frontier (_root_.Dehn.annulusSquare L d) :=
    (P.simplicialComplex_space hP).trans hPr
  have hgr : PolyhedralPLInCharts e g (frontier (_root_.Dehn.annulusSquare L d)) :=
    hJs ▸ hg.restrict_finite J hJ (hJs.subset.trans hrAnn)
  obtain ⟨a,ha,hai,hag,haimage,_⟩ := exists_original_disk_parameter_of_rim he
    hinner hc hgr hf (hgi.mono hrAnn) hfi hrim
  have hinnercopy := hinner
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hinnercopy
  obtain ⟨A,hA,hAs⟩ := _root_.Dehn.exists_finite_square_annulus_complex hd hwidth
  obtain ⟨k,hk,hka,hkg⟩ := _root_.Dehn.exists_circle_attachment_map_union he K A hK hA
    (hKs.symm ▸ ha) (hAs.symm ▸ hg)
    (fun x hx hy => hag (hinter.subset ⟨hKs.subset hx,hAs.subset hy⟩))
  have hka' : EqOn k a (_root_.Dehn.annulusSquare L d) := fun _ hx => hka (hKs.symm ▸ hx)
  have hkg' : EqOn k g (squareAnnulus L d) := fun _ hx => hkg (hAs.symm ▸ hx)
  have hcross (x y : P2) (hx : x ∈ _root_.Dehn.annulusSquare L d)
      (hy : y ∈ squareAnnulus L d) (hxy : k x = k y) : x = y := by
    have haxy : a x = g y := (hka' hx).symm.trans (hxy.trans (hkg' hy))
    have hboth : g y ∈ (g '' squareAnnulus L d) ∩ (f '' c) :=
      ⟨⟨y,hy,rfl⟩,haimage.subset ⟨x,hx,haxy⟩⟩
    obtain ⟨z,hzr,hzy⟩ := hcontact.subset hboth
    have hzy' : z = y := hgi (hrAnn hzr) hy hzy
    have hxz : x = z := hai hx (hinner.1 hzr)
      (haxy.trans (hzy.symm.trans (hag hzr).symm))
    exact hxz.trans hzy'
  have hki : InjOn k (_root_.Dehn.annulusSquare L (-d)) := by
    intro x hx y hy hxy
    rcases hunion.symm.subset hx with hx | hx <;>
      rcases hunion.symm.subset hy with hy | hy
    · exact hai hx hy ((hka' hx).symm.trans (hxy.trans (hka' hy)))
    · exact hcross x y hx hy hxy
    · exact (hcross y x hy hx hxy.symm).symm
    · exact hgi hx hy ((hkg' hx).symm.trans (hxy.trans (hkg' hy)))
  have hwhole : K.space ∪ A.space = _root_.Dehn.annulusSquare L (-d) := by
    rw [hKs,hAs,hunion]
  refine ⟨k,hwhole ▸ hk,hki,hkg',?_,?_⟩
  · rw [← hunion,image_union,hka'.image_eq,hkg'.image_eq,haimage]
  · exact (hkg'.mono houter).image_eq

end PoincareConjecture.M76.Dehn.Annuli.CyclicPanels
