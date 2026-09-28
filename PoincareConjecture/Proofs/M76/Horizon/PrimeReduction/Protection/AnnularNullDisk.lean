import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AnnularRealization
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AnnularDiskRealization
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AnnularContactAlternatives

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_annular_null_disk_or_nested_contacts
    {E X α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R D S : Set X}
    (F : X → E) (hFi : InjOn F R)
    (K : SimplicialComplex ℝ E) (hKs : K.space = F '' R)
    (H : R ≃ₜ K.space) (hH : ∀ x : R, (H x : E) = F x)
    (g : E → R) (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (hfrontD : frontier D ⊆ D) (hDR : D ⊆ R) (hSR : S ⊆ R)
    {J B : Set E} (hJ : J = F '' (D ∩ frontier R))
    (ann : Ann ≃ₜ (F '' frontier D \ (J \ B) : Set E)) (hann : ann.IsFinitePL)
    (hannboundary : ∀ z : Ann, (ann z : E) ∈ J ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1)
    {C : Set P2} (hC : C ⊆ {z | -1 < depth 8 z ∧ depth 8 z < 1})
    (hCpoly : HasDisjointPolygonPresentation C)
    (hphysical : Subtype.val '' (ann '' (Subtype.val ⁻¹' C : Set Ann)) = F '' S) :
    ∃ (p : P2 → X) (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon P2 (n i + 3)),
      PolyhedralPLInCharts e p Ann ∧ InjOn p Ann ∧ p '' C = S ∧
      (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
      C = ⋃ i, (P i).boundary ℝ ∧
      Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) ∧
      (∀ i x, x ∈ (P i).boundary ℝ → -1 < depth 8 x ∧ depth 8 x < 1) ∧
      p '' Ann ⊆ frontier D ∧
      frontier D ∩ interior R ⊆ p '' Ann ∧
      p '' {z | -1 < depth 8 z ∧ depth 8 z < 1} ⊆ interior R ∧
      (∀ z : Ann, p z ∈ frontier R ↔
        depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) ∧
      (∀ z : Ann, F (p z) = (ann z : E)) ∧
      ((∃ i, IsFinitePLBallPair P2 (closure (P i).inside) ((P i).boundary ℝ) ∧
          PolyhedralPLInCharts e p (closure (P i).inside) ∧
          InjOn p (closure (P i).inside) ∧
          p '' closure (P i).inside ⊆ frontier D ∩ interior R ∧
          p '' closure (P i).inside ∩ S = p '' (P i).boundary ℝ ∧
          IsCompact (S \ p '' (P i).boundary ℝ) ∧
          ∃ pole, pole ∈ frontier D ∩ frontier R ∧ pole ∉ p '' closure (P i).inside) ∨
        ((∀ i, Dehn.annulusSquare (8 : ℝ) 1 ⊆ (P i).inside) ∧
          ∀ i j, i ≠ j → closure (P i).inside ⊆ (P j).inside ∨
            closure (P j).inside ⊆ (P i).inside)) := by
  have hCAnn : C ⊆ Ann := fun z hz => mem_squareAnnulus_iff_depth.mpr
    ⟨(hC hz).1.le,(hC hz).2.le⟩
  obtain ⟨p,hpPL,hpi,hpfront,hpint,hpC,hpF⟩ := exists_original_annulus_realization
    F hFi K hKs H hH g hg hgPL (hfrontD.trans hDR) hfrontD hSR hJ ann hann
      hannboundary hCAnn hphysical
  obtain ⟨m,n,P,hP,hcover,hdis⟩ := hCpoly
  have hPiC (i : Fin m) : (P i).boundary ℝ ⊆ C :=
    (subset_iUnion (fun j => (P j).boundary ℝ) i).trans hcover.symm.subset
  have hdepth (i : Fin m) (x : P2) (hx : x ∈ (P i).boundary ℝ) := hC (hPiC i hx)
  have hpends (z : Ann) : p z ∈ frontier R ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1 := by
    rw [←hannboundary z,←hpF z,hJ]
    have hpD := hfrontD (hpfront (mem_image_of_mem p z.property))
    constructor
    · intro hz
      exact ⟨p z,⟨hpD,hz⟩,rfl⟩
    · rintro ⟨x,hx,hxp⟩
      exact hFi (hDR hx.1) (hDR hpD) hxp ▸ hx.2
  have hpcover : frontier D ∩ interior R ⊆ p '' Ann := by
    intro x hx
    have hxA : F x ∈ F '' frontier D \ (J \ B) := by
      refine ⟨mem_image_of_mem F hx.1,?_⟩
      rintro ⟨hxJ,_⟩
      obtain ⟨y,hy,hyx⟩ := hJ.subset hxJ
      exact hy.2.2 ((hFi (hDR hy.1) (interior_subset hx.2) hyx).symm ▸ hx.2)
    let z : Ann := ann.symm ⟨F x,hxA⟩
    refine ⟨z,z.property,hFi (hDR (hfrontD (hpfront (mem_image_of_mem p z.property))))
      (interior_subset hx.2) ?_⟩
    exact (hpF z).trans (congrArg Subtype.val (ann.apply_symm_apply ⟨F x,hxA⟩))
  refine ⟨p,m,n,P,hpPL,hpi,hpC,hP,hcover,hdis,hdepth,hpfront,hpcover,hpint,hpends,hpF,?_⟩
  rcases annular_polygon_family_disk_or_nested n P (fun i => (hP i).2)
    (fun i => (hP i).1) hdis (by norm_num : 2*(1:ℝ)<8) hdepth with hnull | hess
  · obtain ⟨i,hd,hdinside,hdcontacts,_,_⟩ := hnull
    have hdAnn : closure (P i).inside ⊆ Ann := fun z hz =>
      mem_squareAnnulus_iff_depth.mpr ⟨(hdinside hz).1.le,(hdinside hz).2.le⟩
    have hcontact : p '' closure (P i).inside ∩ S = p '' (P i).boundary ℝ := by
      rw [←hpC,←hpi.image_inter hdAnn hCAnn,←hcover] at *
      exact congrArg (fun U => p '' U) hdcontacts
    have hbody : p '' closure (P i).inside ⊆ frontier D ∩ interior R :=
      subset_inter ((image_mono hdAnn).trans hpfront) ((image_mono hdinside).trans hpint)
    have hPLdisk : PolyhedralPLInCharts e p (closure (P i).inside) := by
      obtain ⟨_,_,_,_,_,_,⟨_,⟨T,hT,hTs,_⟩,_⟩,_⟩ := hd
      rw [←hTs]
      exact hpPL.restrict_finite T hT (hTs.subset.trans hdAnn)
    have hrem : C \ (P i).boundary ℝ = ⋃ j : {j : Fin m // j ≠ i}, (P j).boundary ℝ := by
      ext z
      constructor
      · rintro ⟨hz,hzi⟩
        obtain ⟨j,hzj⟩ := mem_iUnion.mp (hcover.subset hz)
        exact mem_iUnion.mpr ⟨⟨j,fun heq => hzi (heq ▸ hzj)⟩,hzj⟩
      · intro hz
        obtain ⟨j,hzj⟩ := mem_iUnion.mp hz
        exact ⟨hPiC j hzj,fun hzi => disjoint_left.mp (hdis j.property) hzj hzi⟩
    have hcompact : IsCompact (C \ (P i).boundary ℝ) := by
      rw [hrem]
      exact isCompact_iUnion (fun j : {j : Fin m // j ≠ i} => (P j).isCompact_boundary)
    have hremimage : p '' (C \ (P i).boundary ℝ) = S \ p '' (P i).boundary ℝ := by
      rw [(hpi.mono hCAnn).image_sdiff_subset (hPiC i),hpC]
    have hremcompact : IsCompact (S \ p '' (P i).boundary ℝ) := hremimage ▸
      hcompact.image_of_continuousOn (hpPL.continuousOn.mono (sdiff_subset.trans hCAnn))
    obtain ⟨pole,hpole,hpoleout⟩ := exists_original_annular_frontier_pole F hFi
      (hfrontD.trans hDR) hDR (hbody.trans inter_subset_right) hJ ann hannboundary
    exact Or.inl ⟨i,hd,hPLdisk,hpi.mono hdAnn,hbody,hcontact,hremcompact,pole,hpole,hpoleout⟩
  · exact Or.inr hess

end PoincareConjecture.M76
