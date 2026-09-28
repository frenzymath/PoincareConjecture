import PoincareConjecture.Proofs.M76.Rigidity.OriginalDomainBoundaryCollar
import PoincareConjecture.Proofs.M76.Rigidity.InwardCollarLevelSphere
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalBallOuterAttachment
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Mathlib.ClopenSubcomplexHomeomorph
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected
import PoincareConjecture.Proofs.M76.Mathlib.PlanarRegionSideTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.PLDomainInteriorConnected
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Q3" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1

private theorem sphere_collar_level
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (sph : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ S) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (hbase : ∀ x : L.space, c ((x : E), 0) = HB x)
    {t : ℝ} (ht : t ∈ I) :
    Nonempty (ChartwisePLSphere e (c '' (L.space ×ˢ {t}))) := by
  classical
  let q : V3 → E := fun x =>
    if hx : x ∈ Q3 then HB.symm (sph.parametrization ⟨x, hx⟩) else 0
  have hqval (x : Q3) : q x = (HB.symm (sph.parametrization x) : E) := by
    simp only [q, dif_pos x.property]
  have hqcont : ContinuousOn q Q3 := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (HB.symm.continuous.comp sph.parametrization.continuous)
    convert h using 1
    funext x
    exact hqval x
  have hqmap : MapsTo q Q3 L.space := by
    intro x hx
    rw [hqval ⟨x, hx⟩]
    exact (HB.symm (sph.parametrization ⟨x, hx⟩)).property
  have hbasePL := PolyhedralPLInCharts.finite_product_slice L hL hc (by norm_num : (0 : ℝ) ∈ I)
  have hbaseInj : InjOn (fun z => c (z, 0)) L.space := by
    intro x hx y hy hxy
    have hpairs := congrArg Subtype.val (hi.injective
      (a₁ := ⟨(x, 0), ⟨hx, by norm_num⟩⟩)
      (a₂ := ⟨(y, 0), ⟨hy, by norm_num⟩⟩) hxy)
    exact congrArg Prod.fst hpairs
  have hcomposite : PolyhedralPLInCharts e ((fun z => c (z, 0)) ∘ q) Q3 :=
    sph.piecewiseAffine.congr (by
      intro x hx
      change sph.map x = c (q x, 0)
      rw [hqval ⟨x, hx⟩, hbase, HB.apply_symm_apply]
      exact sph.map_eq ⟨x, hx⟩)
  obtain ⟨K, hK, hKQ⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hq := hbasePL.finitePiecewiseAffineOn_lift hcompat hbaseInj K hK
    (hqcont.mono hKQ.subset) (fun _ hx => hqmap (hKQ.subset hx))
    (hKQ.symm ▸ hcomposite)
  obtain ⟨H, hHval⟩ := exists_homeomorph_collar_level L hL c hc hi ht
  have hlevelPL : PolyhedralPLInCharts e ((fun z => c (z, t)) ∘ q) Q3 := by
    have hslice := PolyhedralPLInCharts.finite_product_slice L hL hc ht
    exact hKQ ▸ hslice.comp_finitePiecewiseAffineOn K hK hq
      (fun _ hx => hqmap (hKQ.subset hx))
  refine ⟨{
    parametrization := (sph.parametrization.trans HB.symm).trans H
    map := (fun z => c (z, t)) ∘ q
    map_eq := ?_
    piecewiseAffine := hlevelPL }⟩
  intro x
  change c (q x, t) = (H (HB.symm (sph.parametrization x)) : X)
  rw [hqval x, hHval]

theorem IsPLIrreducible.nonempty_ball_of_spherical_boundary_component
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {P S : Set X}
    (hI : IsPLIrreducible e P) (hP : IsCompact P) (hconn : IsConnected P)
    (hSP : S ⊆ frontier P)
    (hclopen : IsClopen ((Subtype.val : frontier P → X) ⁻¹' S))
    (sph : ChartwisePLSphere e S) :
    frontier P = S ∧ Nonempty (ChartwisePLBall e P S) := by
  classical
  have hIntConn := hI.1.isConnected_interior hconn
  obtain ⟨s, L, HB, c, hL, hc, hi, hinside, hbase, hproper, _⟩ :=
    hI.1.exists_small_boundary_collar_of_interior_nonempty hP hIntConn.nonempty
      isOpen_univ (subset_univ _)
  let E := s → ℝ × V3
  obtain ⟨J, H, hJ, hJL, _, hH, _⟩ :=
    L.exists_clopen_subcomplex_homeomorph hL HB hSP hclopen
      (fun z => c (z, 0)) hbase
  have hsub : J.space ⊆ L.space := SimplicialComplex.space_subset_of_le hJL
  have hprod : J.space ×ˢ I ⊆ L.space ×ˢ I := prod_mono hsub Subset.rfl
  obtain ⟨K, hK, hKs⟩ := J.exists_finite_interval_product hJ (by norm_num : (0 : ℝ) < 1)
  have hcJ : PolyhedralPLInCharts e c (J.space ×ˢ I) :=
    hKs ▸ hc.restrict_finite K hK (hKs.subset.trans hprod)
  have hiJ : Topology.IsEmbedding (fun z : (J.space ×ˢ I : Set (E × ℝ)) => c z) :=
    hi.comp (Topology.IsEmbedding.inclusion hprod)
  have hzero : c '' (J.space ×ˢ {(0 : ℝ)}) = S := by
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      have ht' : t = 0 := ht
      subst t
      rw [← hH ⟨z, hz⟩]
      exact (H ⟨z, hz⟩).property
    · intro hx
      refine ⟨(H.symm ⟨x, hx⟩, 0), ⟨(H.symm ⟨x, hx⟩).property, rfl⟩, ?_⟩
      rw [← hH, H.apply_symm_apply]
  obtain ⟨sphLevel⟩ := sphere_collar_level sph hI.1.compatible J hJ H c hcJ hiJ
    (fun x => (hH x).symm) (by norm_num : (1 / 2 : ℝ) ∈ I)
  have hlevelInt : c '' (J.space ×ˢ {(1 / 2 : ℝ)}) ⊆ interior P := by
    rintro x ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    have ht' : t = 1 / 2 := ht
    subst t
    have hzI : (z, (1 / 2 : ℝ)) ∈ L.space ×ˢ I := ⟨hsub hz, by norm_num⟩
    apply (mem_interior_iff_notMem_frontier (hinside hzI)).mpr
    intro hf
    have := (hproper ⟨(z, 1 / 2), hzI⟩).mp hf
    norm_num at this
  obtain ⟨D, hDP, ⟨ball⟩⟩ := hI.2 _ hlevelInt ⟨sphLevel⟩
  have hDint : D ⊆ interior P := ball.subset_interior hDP hlevelInt
  have hJconn : IsConnected J.space := isConnected_iff_connectedSpace.mpr
    (H.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp sph.isConnected))
  have hstripConn : IsConnected (c '' (J.space ×ˢ Ico (0 : ℝ) (1 / 2))) := by
    apply (hJconn.prod (isConnected_Ico (by norm_num : (0 : ℝ) < 1 / 2))).image c
    apply hcJ.continuousOn.mono
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.le.trans (by norm_num)⟩
  have havoid : Disjoint (c '' (J.space ×ˢ Ico (0 : ℝ) (1 / 2))) (frontier D) := by
    rw [ball.frontier_eq]
    apply disjoint_left.mpr
    rintro x ⟨z, hz, hzx⟩ ⟨w, hw, hwx⟩
    have hzI : z ∈ J.space ×ˢ I := ⟨hz.1, hz.2.1, hz.2.2.le.trans (by norm_num)⟩
    have hwtime : w.2 = 1 / 2 := hw.2
    have hwI : w ∈ J.space ×ˢ I := ⟨hw.1, by rw [hwtime]; norm_num⟩
    have heq := hiJ.injective (a₁ := ⟨z, hzI⟩) (a₂ := ⟨w, hwI⟩) (hzx.trans hwx.symm)
    have ht := congrArg (fun v : (J.space ×ˢ I : Set (E × ℝ)) => v.1.2) heq
    exact (ne_of_lt hz.2.2) (ht.trans hwtime)
  have houtside : Disjoint D (c '' (J.space ×ˢ Ico (0 : ℝ) (1 / 2))) := by
    obtain ⟨x, hx⟩ := sph.isConnected.nonempty
    have hxstrip : x ∈ c '' (J.space ×ˢ Ico (0 : ℝ) (1 / 2)) := by
      apply image_mono (prod_mono Subset.rfl (by norm_num : {(0 : ℝ)} ⊆ Ico 0 (1 / 2)))
      exact hzero.symm.subset hx
    have hxnot : x ∉ D := fun h => (hSP hx).2 (hDint h)
    exact disjoint_left.mpr (fun y hy hystrip => hxnot
      ((hstripConn.isPreconnected.mem_iff_of_disjoint_frontier havoid hxstrip hystrip).mpr hy))
  have hoverlap : D ∩ c '' (J.space ×ˢ Icc (0 : ℝ) (1 / 2)) =
      c '' (J.space ×ˢ {(1 / 2 : ℝ)}) := by
    apply Subset.antisymm
    · rintro x ⟨hxD, z, hz, rfl⟩
      have ht : z.2 = 1 / 2 := by
        by_contra hne
        exact disjoint_left.mp houtside hxD ⟨z, ⟨hz.1, hz.2.1, lt_of_le_of_ne hz.2.2 hne⟩, rfl⟩
      exact ⟨z, ⟨hz.1, ht⟩, rfl⟩
    · intro x hx
      exact ⟨ball.boundary_subset hx,
        image_mono (prod_mono Subset.rfl (by norm_num : {(1 / 2 : ℝ)} ⊆ Icc 0 (1 / 2))) hx⟩
  obtain ⟨⟨newball⟩, _⟩ := ball.attach_outer_strip hI.1.cover hI.1.compatible
    J hJ c hcJ hiJ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hoverlap
  have hBsub : D ∪ c '' (J.space ×ˢ Icc (0 : ℝ) (1 / 2)) ⊆ P := by
    refine union_subset hDP ?_
    rintro x ⟨z, hz, rfl⟩
    exact hinside ⟨hsub hz.1, hz.2.1, hz.2.2.trans (by norm_num)⟩
  have hBfront : frontier (D ∪ c '' (J.space ×ˢ Icc (0 : ℝ) (1 / 2))) = S :=
    newball.frontier_eq.trans hzero
  have hIntAvoid : Disjoint (interior P)
      (frontier (D ∪ c '' (J.space ×ˢ Icc (0 : ℝ) (1 / 2)))) := by
    rw [hBfront]
    exact disjoint_left.mpr (fun _ hx hs => (hSP hs).2 hx)
  obtain ⟨y, hy⟩ := newball.isConnected_interior.nonempty
  have hIntSub : interior P ⊆ D ∪ c '' (J.space ×ˢ Icc (0 : ℝ) (1 / 2)) := by
    intro z hz
    exact (hIntConn.isPreconnected.mem_iff_of_disjoint_frontier hIntAvoid
      hz (interior_mono hBsub hy)).mpr (interior_subset hy)
  have heq : D ∪ c '' (J.space ×ˢ Icc (0 : ℝ) (1 / 2)) = P := by
    apply Subset.antisymm hBsub
    exact hI.1.closure_interior.symm.subset.trans
      (closure_minimal hIntSub newball.isCompact.isClosed)
  exact ⟨heq ▸ hBfront, ⟨heq ▸ hzero ▸ newball⟩⟩

end PoincareConjecture.M76
