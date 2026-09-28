import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalEdgeInwardPush
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalFacetInwardPush
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.CompactInwardMotion










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_boundary_inward_motion
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s j, (e j).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedge : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {r O : Set X} (hr : IsCompact r)
    (hrS : r ⊆ ⋃ i, S i)
    (hrT : r ⊆ g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))
    (hO : IsOpen O) (hrO : r ⊆ O) :
    ∃ H : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id Oᶜ ∧ (∀ j x, H x ∈ S j ↔ x ∈ S j) ∧
      (∀ x ∈ g '' convexHull ℝ (t : Set E),
        H x ∈ interior (g '' convexHull ℝ (t : Set E)) ∨ H x = x) ∧
      H '' r ⊆ interior (g '' convexHull ℝ (t : Set E)) := by
  classical
  apply exists_compact_inward_motion e he hcover hr
    (hrT.trans (image_mono (intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed))) S
  intro y hyr
  obtain ⟨i,hyi⟩ := mem_iUnion.mp (hrS hyr)
  obtain ⟨N,hN,hSN,_,hNS⟩ := exists_open_sphere_system_isolation S sS hdis i
  obtain ⟨x,hx,rfl⟩ := hrT hyr
  obtain ⟨v,hv,hxv⟩ := ((K.indep ht).mem_intrinsicFrontier_convexHull_finset
    (K.nonempty_of_mem_faces ht) x).mp hx
  have hc : (t.erase v).card = 3 := by rw [Finset.card_erase_of_mem hv,ht4]
  have hs := K.down_closed ht (Finset.erase_subset v t)
    (Finset.card_pos.mp (show 0 < (t.erase v).card by omega))
  let s : K.FaceOfCard 3 := ⟨t.erase v,hs,hc⟩
  have hex : ∃ H : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id (O ∩ N)ᶜ ∧ (∀ y, H y ∈ S i ↔ y ∈ S i) ∧
      (∀ y ∈ g '' convexHull ℝ (t : Set E),
        H y ∈ interior (g '' convexHull ℝ (t : Set E)) ∨ H y = y) ∧
      H (g x) ∈ interior (g '' convexHull ℝ (t : Set E)) := by
    by_cases hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s.1 : Set E))
    · exact exists_original_facet_inward_push he K hK g hg hgi Q hQ A hmap hA
        S sS hdis hposition ht ht4 s (Finset.erase_subset v t) hxs i hyi
        (hO.inter hN) ⟨hrO hyr,hSN hyi⟩
    · have hxf : x ∈ intrinsicFrontier ℝ (convexHull ℝ (s.1 : Set E)) := by
        rw [←intrinsicClosure_sdiff_intrinsicInterior]
        exact ⟨subset_intrinsicClosure hxv,hxs⟩
      obtain ⟨w,hw,hxw⟩ := ((K.indep hs).mem_intrinsicFrontier_convexHull_finset
        (K.nonempty_of_mem_faces hs) x).mp hxf
      have hwcard : ((t.erase v).erase w).card = 2 := by rw [Finset.card_erase_of_mem hw,hc]
      have hwface := K.down_closed hs (Finset.erase_subset w (t.erase v))
        (Finset.card_pos.mp (show 0 < ((t.erase v).erase w).card by omega))
      obtain ⟨p,q,hpq,hpqeq⟩ := Finset.card_eq_two.mp hwcard
      have hpqface : ({p,q} : Finset E) ∈ K.faces := hpqeq ▸ hwface
      have hpqt : ({p,q} : Finset E) ⊆ t := by
        rw [←hpqeq]
        exact (Finset.erase_subset w _).trans (Finset.erase_subset v _)
      have hxseg : x ∈ segment ℝ p q := by
        simpa only [hpqeq,Finset.coe_pair,convexHull_pair] using hxw
      exact (hedge i {p,q} hpqface (hpqeq ▸ hwcard)).exists_original_tetrahedron_inward_push
        he hgi (hSV.mono_left (subset_iUnion S i)) hpq ht ht4 hpqt ⟨hyi,x,hxseg,rfl⟩
        (hO.inter hN) ⟨hrO hyr,hSN hyi⟩
  obtain ⟨H,hHPL,_,hHfix,hHi,hHin,hHx⟩ := hex
  refine ⟨H,hHPL,fun y hy => hHfix (fun h => hy h.1),?_,hHin,hHx⟩
  intro j y
  by_cases hji : j = i
  · subst j
    exact hHi y
  · have hfix (z : X) (hz : z ∈ S j) : H z = z := by
      apply hHfix
      intro hzN
      exact disjoint_left.mp (hNS j hji) hzN.2 hz
    constructor
    · intro hy
      have heq : H y = y := H.injective (hfix (H y) hy)
      exact heq ▸ hy
    · intro hy
      exact (hfix y hy).symm ▸ hy

end PoincareConjecture.M76
