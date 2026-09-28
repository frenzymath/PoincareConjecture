import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MinimumAmbientOrbit
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NonreturningTriangleGraphPosition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ReturningFaceMove
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MinimumContactMove









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_protected_minimal_sphere_system_face_position
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {K N : SimplicialComplex ℝ E} (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z)
    (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    (hSZ : Disjoint (⋃ i, S i) Z) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (hmin : IsProtectedSkeletonMinimum e S K g Z) :
    ∃ (Phi : X ≃ₜ X) (V : Set X),
      IsOpen V ∧ Z ∪ g '' K.vertices ⊆ V ∧ EqOn Phi id V ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s → g '' convexHull ℝ (a : Set E) ⊆ V) ∧
      (∀ i j, (e i).symm.trans (Phi.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (Phi.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (∀ i, ChartwisePLSphere e (Phi '' S i)) ∧
      (Pairwise fun i j => Disjoint (Phi '' S i) (Phi '' S j)) ∧
      Disjoint (Phi '' (⋃ i, S i)) (Z ∪ g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card ≤ 2 →
        (g '' convexHull ℝ (a : Set E)) ∩ (Phi '' (⋃ i, S i)) =
          (g '' convexHull ℝ (a : Set E)) ∩ (⋃ i, S i)) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((Phi '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (Phi '' S i) K g a) ∧
      IsProtectedSkeletonMinimum e (fun i => Phi '' S i) K g Z ∧
      InNonreturningTriangleGraphPosition Q (Phi '' (⋃ i, S i)) g s A := by
  classical
  obtain ⟨G, Phi, hG, hGT, hGdim, hinterior, hexterior, hfrontFinite,
      hphysical, hPhiPL, hPhiinv, hPhiZ, hPhiV,
      hedgeAgree, ⟨V, hV, hmarksV, hfacesV, hfixV⟩, hcrossings, hreturn⟩ :=
    exists_original_protected_sphere_system_returning_face_move_with_other_faces
      S sS hdis he hK hNK g hgc hgi hZ hmark hSZ hSV hs hs3
      hedges hcofaces Q hQ A hmap hA zero_lt_one
  have hedgeV (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card ≤ 2) :
      g '' convexHull ℝ (a : Set E) ⊆ V :=
    hfacesV a ha (by omega) (by intro h; subst a; omega)
  have hPhiCofaces (i : κ) (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card = 2) :
      HasOriginalEdgeCofaceCharts e (Phi '' S i) K g a := by
    apply (hcofaces i a ha ha2).image_of_disjoint_support Phi hV.isClosed_compl
    · exact disjoint_left.mpr (fun x hx he => hx (hedgeV a ha ha2.le he))
    · simpa only [compl_compl] using hfixV
  have hPhiEdges (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card = 2) :
      ((Phi '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite := by
    rw [inter_comm, hedgeAgree a ha ha2.le, inter_comm]
    exact hedges a ha ha2
  have hcount :
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩ (Phi '' (⋃ i, S i))).ncard =
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩ (⋃ i, S i)).ncard := by
    congr 1
    rw [iUnion_inter, iUnion_inter]
    exact iUnion_congr (fun a => hedgeAgree a.1 a.2.1 a.2.2.le)
  have hminPhi := hmin.image_of_same_count hcover Phi hV hmarksV hfixV hPhiPL hPhiinv hcount
  obtain ⟨hsPhi, hdisPhi, hPhiMarks, _⟩ := protected_sphere_system_ambient_image
    S sS hdis hcover Phi hPhiPL (disjoint_union_right.mpr ⟨hSZ, hSV⟩)
      (hfixV.mono hmarksV)
  refine ⟨Phi, V, hV, hmarksV, hfixV, hfacesV, hPhiPL, hPhiinv,
    ⟨fun i => Classical.choice (hsPhi i)⟩, hdisPhi, ?_, hedgeAgree, hPhiEdges,
    hPhiCofaces, hminPhi, ?_⟩
  · simpa only [← image_iUnion] using hPhiMarks
  · have hTQ : convexHull ℝ (A '' (s : Set E)) ⊆ Q.target := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := (A.toAffineMap.image_convexHull (s : Set E)).symm.subset hy
      change A x ∈ Q.target
      rw [← hA hx]
      exact Q.map_source (hmap hx)
    refine ⟨G, hG, (fun x hx => ⟨hGT hx, hTQ (hGT hx)⟩), hGdim, hphysical,
      (fun v hv => hinterior v v.property hv), hexterior, hfrontFinite, ?_, ?_⟩
    · intro w hw O hO hwO
      obtain ⟨B, hwB, hBO, hBw, hBPL, hBinv, hBS, hBT⟩ := hcrossings w hw O hO hwO
      exact ⟨B, hwB, hBO.trans inter_subset_left, hBw, hBPL, hBinv, hBS, hBT⟩
    · intro a has ha2 hret
      obtain ⟨H, C, U, x, y, hxy, hx, hy, hU, hC, hCU, hUZ, hUV, hUother,
          hHC, hHU, hHPL, hHinv, hselected, hdrop, hHZ, hHV, hother, hothercard,
          hglobal, hnewCofaces⟩ := hreturn a has ha2 hret
      let Theta := Phi.trans H.symm
      have hThetaImage (B : Set X) : Theta '' B = H.symm '' (Phi '' B) := by
        rw [image_image]
        rfl
      obtain ⟨hThetaPL, hThetainv⟩ := original_PL_motion_trans_both e hcover Phi H.symm
        hPhiPL hPhiinv hHinv hHPL
      have hmarksC : Z ∪ g '' K.vertices ⊆ Cᶜ := by
        intro z hz hzC
        rcases hz with hz | hz
        · exact disjoint_left.mp hUZ (hCU hzC) hz
        · exact disjoint_left.mp hUV (hCU hzC) hz
      have hHfix : EqOn H.symm id Cᶜ := by
        intro z hz
        apply H.injective
        change H (H.symm z) = H z
        rw [H.apply_symm_apply, hHC z hz]
      obtain ⟨hVC, hmarksVC, hfixTheta, _⟩ := protected_ambient_trans_neighborhood
        Phi H.symm hV hC.isClosed.isOpen_compl hmarksV hmarksC hfixV hHfix
      have hThetaEdges (b : Finset E) (hb : b ∈ K.faces) (hb2 : b.card = 2) :
          ((Theta '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (b : Set E))).Finite := by
        rw [hThetaImage, inter_comm]
        by_cases hba : b = a
        · subst b
          rw [hselected]
          have hf := hedges a hb hb2
          rw [inter_comm] at hf
          exact hf.sdiff
        · rw [hother b hb hb2.le hba, inter_comm]
          exact hedges b hb hb2
      have hThetaCofaces (i : κ) (b : Finset E) (hb : b ∈ K.faces) (hb2 : b.card = 2) :
          HasOriginalEdgeCofaceCharts e (Theta '' S i) K g b := by
        rw [hThetaImage]
        exact hnewCofaces i b hb hb2
      exact no_two_contact_union_decrease_at_protected_minimum g Z hmin Theta
        (V ∩ Cᶜ) hVC hmarksVC hfixTheta hThetaPL hThetainv hThetaEdges hThetaCofaces
        (by simpa only [hThetaImage] using hglobal)

end PoincareConjecture.M76
