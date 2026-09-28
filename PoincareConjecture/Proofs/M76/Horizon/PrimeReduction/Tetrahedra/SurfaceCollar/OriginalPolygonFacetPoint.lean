import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalFacetGerm
import Mathlib.Order.Interval.Set.Infinite









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_original_polygon_facet_interior_point
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X)
    (hgi : InjOn g K.space) {T : Set X}
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      (T ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {n : ℕ} (P : Polygon E (n + 3)) (hPi : Function.Injective P)
    (hPsub : P.boundary ℝ ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))
    (hPT : g '' P.boundary ℝ ⊆ T) :
    ∃ x ∈ P.boundary ℝ, ∃ s : K.FaceOfCard 3,
      s.1 ⊆ t ∧ x ∈ intrinsicInterior ℝ (convexHull ℝ (s.1 : Set E)) := by
  classical
  let := K.finite_faceOfCard hK 2
  have hPK : P.boundary ℝ ⊆ K.space := hPsub.trans
    ((intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed).trans
      (K.convexHull_subset_space ht))
  have hne : P 0 ≠ P (finRotate (n + 3) 0) := by
    apply hPi.ne
    intro h
    have hh := congrArg Fin.val h
    simp [finRotate_apply] at hh
  have hPinf : (P.boundary ℝ).Infinite := by
    have hline := (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num)).image
      (AffineMap.lineMap_injective ℝ hne).injOn
    apply hline.mono
    rintro z ⟨u,hu,huz⟩
    exact mem_iUnion.mpr ⟨0,u,hu,huz⟩
  have hbad : (T ∩ ⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)).Finite := by
    rw [inter_iUnion]
    exact Set.finite_iUnion fun a => hedges a.1 a.2.1 a.2.2
  obtain ⟨y,⟨x,hx,rfl⟩,hynot⟩ :=
    (hPinf.image (hgi.mono hPK)).exists_notMem_finite hbad
  have hxedge (a : K.FaceOfCard 2) : x ∉ convexHull ℝ (a.1 : Set E) := by
    intro h
    exact hynot ⟨hPT ⟨x,hx,rfl⟩,mem_iUnion.mpr ⟨a,x,h,rfl⟩⟩
  obtain ⟨v,hv,hxv⟩ := ((K.indep ht).mem_intrinsicFrontier_convexHull_finset
    (K.nonempty_of_mem_faces ht) x).mp (hPsub hx)
  have hc : (t.erase v).card = 3 := by rw [Finset.card_erase_of_mem hv,ht4]
  have hs := K.down_closed ht (Finset.erase_subset v t)
    (Finset.card_pos.mp (show 0 < (t.erase v).card by omega))
  refine ⟨x,hx,⟨t.erase v,hs,hc⟩,Finset.erase_subset v t,?_⟩
  rw [←intrinsicClosure_sdiff_intrinsicFrontier]
  refine ⟨subset_intrinsicClosure hxv,?_⟩
  intro hxf
  obtain ⟨w,hw,hxw⟩ := ((K.indep hs).mem_intrinsicFrontier_convexHull_finset
    (K.nonempty_of_mem_faces hs) x).mp hxf
  have hwcard : ((t.erase v).erase w).card = 2 := by rw [Finset.card_erase_of_mem hw,hc]
  have hwface := K.down_closed hs (Finset.erase_subset w (t.erase v))
    (Finset.card_pos.mp (show 0 < ((t.erase v).erase w).card by omega))
  exact hxedge ⟨(t.erase v).erase w,hwface,hwcard⟩ hxw

end PoincareConjecture.M76
