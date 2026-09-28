import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SurgeryRimNullhomotopy
import PoincareConjecture.Proofs.M76.Mathlib.TwoIntervalCircle
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalPlanarDiskComplement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalSubdiskUniqueness

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "Rim" => sphere (0 : Fin 2 → ℝ) 1
local notation "V3" => (Fin 3 → ℝ)

theorem exists_polygon_of_two_planar_intervals
    {C Z q : Set P2} (hC : IsFinitePLBallPair ℝ C q)
    (hZ : IsFinitePLBallPair ℝ Z q) (hCZ : C ∩ Z = q) :
    ∃ n, ∃ P : Polygon P2 (n+3), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = C ∪ Z := by
  obtain ⟨H,hH⟩ := hC.exists_twoInterval_circle_model hZ hCZ
  obtain ⟨n,P,hPi,hP,hPb⟩ := TriangularRoofModel.isFinitePLBallPair_base.exists_polygon_boundary
  obtain ⟨f,hf,hfv⟩ := hH.symm
  have hfi : InjOn f (frontier TriangularRoofModel.base) := by
    intro x hx y hy hxy
    apply congrArg Subtype.val (H.symm.injective (show H.symm ⟨x,hx⟩ = H.symm ⟨y,hy⟩ from ?_))
    apply Subtype.ext
    simpa only [hfv] using hxy
  have himage : f '' frontier TriangularRoofModel.base = C ∪ Z := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      rw [←hfv ⟨y,hy⟩]
      exact (H.symm ⟨y,hy⟩).property
    · intro hx
      refine ⟨H ⟨x,hx⟩,(H ⟨x,hx⟩).property,?_⟩
      rw [←hfv (H ⟨x,hx⟩),H.symm_apply_apply]
  obtain ⟨m,Q,hQi,hQ,hQb⟩ := P.exists_polygon_finitePL_image hP hPi hf
    hPb.subset (hfi.mono hPb.subset)
  exact ⟨m,Q,hQi,hQ,hQb.trans (by rw [hPb,himage])⟩

theorem exists_returning_planar_disk_of_nullhomotopic_two_arc_loop
    {K B C Z q : Set P2} (hC : IsFinitePLBallPair ℝ C q)
    (hZ : IsFinitePLBallPair ℝ Z q) (hCZ : C ∩ Z = q)
    (hCB : C ∩ B = q) (hZB : Z ⊆ B) (hKB : K ∩ B = frontier K)
    (gamma : C(Rim,K)) (hgamma : Function.Injective gamma)
    (himage : range (fun z => (gamma z : P2)) = C ∪ Z)
    (hnull : gamma.Nullhomotopic) :
    ∃ D : Set P2, IsFinitePLBallPair P2 D (Z ∪ C) ∧ D ⊆ K ∧ D ∩ B = Z := by
  obtain ⟨n,P,hPi,hP,hPb⟩ := exists_polygon_of_two_planar_intervals hC hZ hCZ
  have hDK := polygon_closed_inside_subset_of_nullhomotopic_rim P hP hPi gamma
    hgamma (himage.trans hPb.symm) hnull
  refine ⟨closure P.inside,?_,hDK,?_⟩
  · simpa [hPb,union_comm] using P.isFinitePLBallPair_closed_inside hP hPi
  have hinK : P.inside ⊆ interior K :=
    interior_maximal (subset_closure.trans hDK) (P.isOpen_inside hP hPi)
  rw [closure_eq_self_union_frontier,P.frontier_inside hP hPi,hPb]
  apply Subset.antisymm
  · rintro x ⟨hx | hx,hxB⟩
    · exact (disjoint_interior_frontier.notMem_of_mem_left (hinK hx)
        (hKB.subset ⟨hDK (subset_closure hx),hxB⟩)).elim
    · rcases hx with hxC | hxZ
      · exact hZ.1 (hCB.subset ⟨hxC,hxB⟩)
      · exact hxZ
  · intro x hx
    exact ⟨Or.inr (Or.inr hx),hZB hx⟩

theorem ChartwisePLSphere.exists_original_returning_disk_of_nullhomotopic_loop
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {S E : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e E) (hE : IsClosed E)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    {B C Z q : Set P2}
    (p : P2 → X) (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : p '' K.space = S ∩ E)
    (hproper : ∀ z ∈ K.space,p z ∈ frontier E ↔ z ∈ B)
    (hcross : ∀ x ∈ S ∩ frontier E, ∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0)
    (hC : IsFinitePLBallPair ℝ C (C ∩ B)) (hCK : C ⊆ K.space)
    (g : P2 → X) (hg : PolyhedralPLInCharts e g Z) (hgi : InjOn g Z)
    (hZ : IsFinitePLBallPair ℝ Z q) (hgZ : g '' Z ⊆ S ∩ frontier E)
    (hgq : g '' q = p '' (C ∩ B))
    (hinter : p '' C ∩ g '' Z = p '' (C ∩ B))
    (gamma : C(Rim,↥(S ∩ E))) (hgamma : Function.Injective gamma)
    (himage : range (fun z => (gamma z : X)) = p '' C ∪ g '' Z)
    (hnull : gamma.Nullhomotopic) :
    ∃ D U : Set P2, IsFinitePLBallPair P2 D (U ∪ C) ∧
      IsFinitePLBallPair ℝ U (U ∩ C) ∧ D ⊆ K.space ∧ D ∩ B = U ∧
      p '' U = g '' Z := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  have hpe := (hp.continuousOn.domRestrict.isClosedEmbedding
    (fun x y hh => Subtype.ext (hpi x.property y.property hh))).isEmbedding
  obtain ⟨k,hkc,hleft,hright,hkK⟩ := hpe.exists_inverse_on_image
  have hgK : g '' Z ⊆ p '' K.space := by
    rw [hps]
    exact fun x hx => ⟨(hgZ hx).1,hE.frontier_subset (hgZ hx).2⟩
  have hkg : FinitePiecewiseAffineOn (k ∘ g) Z := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLZ,_⟩,_⟩,_⟩ := hZ
    rw [←hLZ]
    apply hp.finitePiecewiseAffineOn_lift he.compatible hpi L hL
      ((hkc.comp hg.continuousOn (fun x hx => hgK ⟨x,hx,rfl⟩)).mono hLZ.subset)
      (fun x hx => hkK (hgK ⟨x,hLZ.subset hx,rfl⟩))
    exact (hg.restrict_finite L hL hLZ.subset).congr
      (fun x hx => (hright _ (hgK ⟨x,hLZ.subset hx,rfl⟩)).symm)
  have hkgi : InjOn (k ∘ g) Z := by
    intro x hx y hy hh
    exact hgi hx hy ((hright _ (hgK ⟨x,hx,rfl⟩)).symm.trans
      ((congrArg p hh).trans (hright _ (hgK ⟨y,hy,rfl⟩))))
  let U := (k ∘ g) '' Z
  have hUK : U ⊆ K.space := by
    rintro _ ⟨x,hx,rfl⟩
    exact hkK (hgK ⟨x,hx,rfl⟩)
  have hpU : p '' U = g '' Z := by
    rw [←image_comp]
    exact image_congr (fun x hx => hright _ (hgK ⟨x,hx,rfl⟩))
  have hUq : (k ∘ g) '' q = C ∩ B := by
    rw [image_comp,hgq]
    rw [←image_comp]
    simpa only [Function.comp_def,image_id'] using
      image_congr (fun x (hx : x ∈ C ∩ B) => hleft x (hCK hx.1))
  have hU : IsFinitePLBallPair ℝ U (C ∩ B) := by
    simpa only [hUq] using hZ.image hkg hkgi
  have hCU : C ∩ U = C ∩ B := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨y,hy,hyp⟩ := hinter.subset
        ⟨mem_image_of_mem p hx.1,hpU.subset (mem_image_of_mem p hx.2)⟩
      exact hpi (hCK hy.1) (hCK hx.1) hyp ▸ hy
    · intro x hx
      exact ⟨hx.1,hU.1 hx⟩
  have hUB : U ⊆ B := by
    intro x hx
    exact (hproper x (hUK hx)).mp (hgZ (hpU.subset ⟨x,hx,rfl⟩)).2
  have hproper' : ∀ z ∈ K.space,p z ∈ frontier E ↔ z ∈ K.space ∩ B :=
    fun z hz => (hproper z hz).trans ⟨fun h => ⟨hz,h⟩,fun h => h.2⟩
  have hfront := s.planar_exterior_frontier_eq he K hK inter_subset_left
    p hp hpi hps hproper' hcross
  let back : C(↥(S ∩ E),K.space) :=
    ⟨fun x => ⟨k x,hkK (hps.symm.subset x.property)⟩,
      (hkc.comp_continuous continuous_subtype_val
        (fun x => hps.symm.subset x.property)).subtype_mk _⟩
  have hback (x : ↥(S ∩ E)) : p (back x) = (x : X) :=
    hright _ (hps.symm.subset x.property)
  let delta := back.comp gamma
  have hdi : Function.Injective delta := by
    intro x y hh
    apply hgamma
    apply Subtype.ext
    exact (hback (gamma x)).symm.trans
      ((congrArg (fun z : K.space => p z) hh).trans (hback (gamma y)))
  have hds : range (fun z => (delta z : P2)) = C ∪ U := by
    apply Subset.antisymm
    · rintro _ ⟨z,rfl⟩
      have hx := himage.subset (mem_range_self z)
      rw [←hpU,←image_union] at hx
      obtain ⟨x,hx,hxp⟩ := hx
      have hxK := hx.elim (fun h => hCK h) (fun h => hUK h)
      change (delta z : P2) ∈ C ∪ U
      rw [←hpi hxK (delta z).property (hxp.trans (hback (gamma z)).symm)]
      exact hx
    · intro x hx
      have hpx : p x ∈ p '' C ∪ g '' Z := by
        rw [←hpU,←image_union]
        exact mem_image_of_mem p hx
      obtain ⟨z,hz⟩ := himage.symm.subset hpx
      exact ⟨z,hpi (delta z).property (hx.elim (fun h => hCK h) (fun h => hUK h))
        ((hback (gamma z)).trans hz)⟩
  obtain ⟨D,hD,hDK,hDB⟩ := exists_returning_planar_disk_of_nullhomotopic_two_arc_loop
    hC hU hCU rfl hUB hfront.symm delta hdi hds (hnull.comp_right back)
  exact ⟨D,U,hD,by rwa [inter_comm,hCU],hDK,hDB,hpU⟩

end PoincareConjecture.M76
