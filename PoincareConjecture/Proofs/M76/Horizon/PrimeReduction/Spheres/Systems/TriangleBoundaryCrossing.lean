import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.CoordinateTriangleEndpointCrossing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalTriangleBoundaryDegree
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.FiniteSphereSystemCofaceCharts










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)






theorem exists_original_sphere_system_triangle_boundary_crossing
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hgi : InjOn g K.space) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (J M G : SimplicialComplex ℝ V3)
    (hTJ : convexHull ℝ (A '' (s : Set E)) ⊆ interior J.space)
    (hJQ : J.space ⊆ Q.target)
    (hGs : G.space = M.space ∩ convexHull ℝ (A '' (s : Set E)))
    (Phi : X ≃ₜ X)
    (hPhiS : ∀ x ∈ J.space, Q.symm x ∈ Phi '' (⋃ i, S i) ↔ x ∈ M.space)
    {W : Set X} (hW : IsOpen W)
    (hedgeW : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      g '' convexHull ℝ (a : Set E) ⊆ W)
    (hagree : Phi '' (⋃ i, S i) ∩ W = (⋃ i, S i) ∩ W)
    {w : V3} (hw : w ∈ G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))))
    {O : Set V3} (hO : IsOpen O) (hwO : w ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 V3,
      H ∈ piecewiseAffineGroupoid V3 ∧ w ∈ H.source ∧
      H.source ⊆ O ∩ interior J.space ∧ H w = 0 ∧
      (∀ x ∈ H.source, x ∈ M.space ↔ H x 1 = 0) ∧
      (∀ x ∈ H.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔
        H x 0 = 0 ∧ 0 ≤ H x 2) ∧
      ∀ x ∈ H.source, x ∈ G.space ↔ H x 0 = 0 ∧ H x 1 = 0 ∧ 0 ≤ H x 2 := by
  classical
  have hwM := (hGs.subset hw.1).1
  have hwt := (hGs.subset hw.1).2
  have hwJ : w ∈ interior J.space := hTJ hwt
  obtain ⟨a, ha, has, ha2, _, hwQ, hyedge⟩ :=
    exists_original_subedge_of_mem_triangle_intrinsicFrontier K g hgi hs hs3 Q A hmap hA hw.2
  have hyW : Q.symm w ∈ W := hedgeW a ha has ha2 hyedge
  have hyPhi : Q.symm w ∈ Phi '' (⋃ i, S i) := (hPhiS w (interior_subset hwJ)).mpr hwM
  have hyS : Q.symm w ∈ ⋃ i, S i := (hagree.subset ⟨hyPhi, hyW⟩).1
  have hyvertex : Q.symm w ∉ g '' K.vertices := fun hv => disjoint_left.mp hSV hyS hv
  have hycover : ∃ i, Q.symm w ∈ (e i).source := by
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hyS
    let v := (sS i).parametrization.symm ⟨Q.symm w, hyi⟩
    have hvy : (sS i).map v = Q.symm w := by
      rw [(sS i).map_eq v]
      exact congrArg Subtype.val ((sS i).parametrization.apply_symm_apply ⟨Q.symm w, hyi⟩)
    obtain ⟨i, P, V, _, _, _, hvV, hVP, hPe, _⟩ := (sS i).piecewiseAffine.coordinates v
    exact ⟨i, hvy ▸ hPe (hVP (mem_image_of_mem Subtype.val hvV))⟩
  let U := O ∩ (interior J.space ∩ (Q.target ∩ Q.symm ⁻¹' W))
  have hU : IsOpen U := hO.inter (isOpen_interior.inter (Q.symm.isOpen_inter_preimage hW))
  have hwU : w ∈ U := ⟨hwO, hwJ, hwQ, hyW⟩
  obtain ⟨p, q, hpq, haeq⟩ := Finset.card_eq_two.mp ha2
  have hpqs : ({p, q} : Finset E) ⊆ s := haeq ▸ has
  obtain ⟨r, hr, hseq⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hpqs, by rw [Finset.card_pair hpq, hs3]⟩
  have hrp : r ≠ p := fun he => hr (he.symm ▸ Finset.mem_insert_self _ _)
  have hrq : r ≠ q := fun he => hr (he.symm ▸ Finset.mem_insert_of_mem
    (Finset.mem_singleton_self _))
  have hface : ({r, p, q} : Finset E) ∈ K.faces := hseq ▸ hs
  have hsset : (s : Set E) = {r, p, q} := by
    rw [← hseq, Finset.coe_insert, Finset.coe_pair]
  have hco : HasOriginalEdgeCofaceCharts e (⋃ i, S i) K g {p, q} := by
    have h := hasOriginalEdgeCofaceCharts_finite_sphere_system S sS hdisjoint K g a
      (fun i => hcofaces i a ha has ha2)
    exact haeq ▸ h
  have hycontact : Q.symm w ∈ (⋃ i, S i) ∩ (g '' segment ℝ p q) := by
    refine ⟨hyS, ?_⟩
    simpa only [haeq, Finset.coe_pair, convexHull_pair] using hyedge
  obtain ⟨H, hH, hwH, hHU, hHzero, hHS, hHT, _, _⟩ :=
    hco.exists_triangle_endpoint_crossing_in_chart hgi hyvertex hpq hrp hrq hface
      hycontact hycover Q hQ (Q.map_target hwQ) hU (by rwa [Q.right_inv hwQ])
  have hwithin (x : V3) (hx : x ∈ H.source) : x ∈ U := (hHU hx).1
  have hphysical (x : V3) (hx : x ∈ Q.target) :
      Q.symm x ∈ g '' convexHull ℝ (s : Set E) ↔
        x ∈ convexHull ℝ (A '' (s : Set E)) := by
    have himage : convexHull ℝ (A '' (s : Set E)) =
        (Q ∘ g) '' convexHull ℝ (s : Set E) :=
      (A.toAffineMap.image_convexHull _).symm.trans (image_congr hA).symm
    rw [himage]
    constructor
    · rintro ⟨z, hz, hzx⟩
      exact ⟨z, hz, by change Q (g z) = x; rw [hzx, Q.right_inv hx]⟩
    · rintro ⟨z, hz, hzx⟩
      exact ⟨z, hz, by rw [← hzx]; exact (Q.left_inv (hmap hz)).symm⟩
  have hMsphere (x : V3) (hx : x ∈ H.source) : x ∈ M.space ↔ H x 1 = 0 := by
    have hxU := hwithin x hx
    have hloc : Q.symm x ∈ Phi '' (⋃ i, S i) ↔ Q.symm x ∈ ⋃ i, S i := by
      exact ⟨fun h => (hagree.subset ⟨h, hxU.2.2.2⟩).1,
        fun h => (hagree.symm.subset ⟨h, hxU.2.2.2⟩).1⟩
    exact (hPhiS x (interior_subset hxU.2.1)).symm.trans (hloc.trans (hHS x hx))
  have htriangle (x : V3) (hx : x ∈ H.source) :
      x ∈ convexHull ℝ (A '' (s : Set E)) ↔ H x 0 = 0 ∧ 0 ≤ H x 2 := by
    rw [← hphysical x (hJQ (interior_subset (hwithin x hx).2.1)), hsset]
    exact hHT x hx
  refine ⟨H, hH, by simpa only [Q.right_inv hwQ] using hwH,
    fun x hx => ⟨(hwithin x hx).1, (hwithin x hx).2.1⟩,
    by simpa only [Q.right_inv hwQ] using hHzero, hMsphere, htriangle, ?_⟩
  intro x hx
  rw [hGs, mem_inter_iff, hMsphere x hx, htriangle x hx]
  tauto

end PoincareConjecture.M76

