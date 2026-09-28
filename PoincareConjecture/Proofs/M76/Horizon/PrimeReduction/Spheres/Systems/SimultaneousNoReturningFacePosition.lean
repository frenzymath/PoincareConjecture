import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MinimalFacePosition

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_simultaneous_protected_sphere_system_position_without_returns
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z)
    (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    (hSZ : Disjoint (⋃ i, S i) Z) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s i, (e i).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E))) :
    ∃ (F : X ≃ₜ X) (W : Set X),
      IsOpen W ∧ Z ∪ g '' K.vertices ⊆ W ∧
      EqOn F id W ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (∀ i, ChartwisePLSphere e (F '' S i)) ∧
      (Pairwise fun i j => Disjoint (F '' S i) (F '' S j)) ∧
      Disjoint (F '' (⋃ i, S i)) (Z ∪ g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (F '' S i) K g a) ∧
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
        (F '' (⋃ i, S i))).ncard ≤
        ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩ (⋃ i, S i)).ncard ∧
      ∀ s : K.FaceOfCard 3,
        InNonreturningTriangleGraphPosition (Q s) (F '' (⋃ i, S i)) g s.1 (A s) := by
  classical
  obtain ⟨F₀, W₀, ⟨sF₀⟩, hW₀, hmarks₀, hfix₀, hF₀PL, hF₀inv,
      hdis₀, hF₀Z, hF₀V, hedges₀, hcofaces₀, hfinite₀, hmin₀⟩ :=
    exists_protected_sphere_system_skeleton_minimum S sS hdis hcover he K hK g
      hSZ hSV hedges hcofaces
  have hminimum₀ := protected_skeleton_minimum_of_attained_orbit_minimum
    S K g Z hcover F₀ hW₀ hmarks₀ hfix₀ hF₀PL hF₀inv hmin₀
  have hid : ∀ i j, (e i).symm.trans
      ((Homeomorph.refl X).toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3 := by
    intro i j
    change (e i).symm.trans ((OpenPartialHomeomorph.refl X).trans (e j)) ∈ _
    simpa only [OpenPartialHomeomorph.refl_trans] using he i j
  have hbound₀ := hmin₀ (Homeomorph.refl X) univ isOpen_univ (subset_univ _)
    (fun _ _ => rfl) hid hid
    (by simpa only [Homeomorph.refl_apply, id_eq, image_id'] using hedges)
    (by simpa only [Homeomorph.refl_apply, id_eq, image_id'] using hcofaces)
  have hstage : ∀ t : Finset (K.FaceOfCard 3), ∃ (F : X ≃ₜ X) (W : Set X),
      IsOpen W ∧ Z ∪ g '' K.vertices ⊆ W ∧ EqOn F id W ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (∀ i, ChartwisePLSphere e (F '' S i)) ∧
      (Pairwise fun i j => Disjoint (F '' S i) (F '' S j)) ∧
      Disjoint (F '' (⋃ i, S i)) (Z ∪ g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (F '' S i) K g a) ∧
      IsProtectedSkeletonMinimum e (fun i => F '' S i) K g Z ∧
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
        (F '' (⋃ i, S i))).ncard ≤
        ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩ (⋃ i, S i)).ncard ∧
      ∀ s ∈ t, InNonreturningTriangleGraphPosition (Q s) (F '' (⋃ i, S i)) g s.1 (A s) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨F₀, W₀, hW₀, hmarks₀, hfix₀, hF₀PL, hF₀inv, ⟨sF₀⟩,
        hdis₀, disjoint_union_right.mpr ⟨hF₀Z, hF₀V⟩, hedges₀, hcofaces₀,
        hminimum₀, ?_, by simp⟩
      simpa only [Homeomorph.refl_apply, id_eq, image_id'] using hbound₀
    | @insert s t hst ih =>
      obtain ⟨F, W, hW, hmarks, hfix, hFPL, hFinv, ⟨sF⟩, hdisF,
        havoidF, hFedges, hFcofaces, hminimum, hbound, hpositions⟩ := ih
      have hunion : (⋃ i, F '' S i) = F '' (⋃ i, S i) := image_iUnion.symm
      obtain ⟨Phi, V, hV, hmarksV, hfixV, hfacesV, hPhiPL, hPhiinv,
          hsPhi, hdisPhi, havoidPhi, hagree, hPhiEdges, hPhiCofaces,
          hminimumPhi, hposition⟩ :=
        exists_protected_minimal_sphere_system_face_position
          (fun i => F '' S i) sF hdisF hcover he hK hNK g hgc hgi hZ hmark
          (by simpa only [hunion] using havoidF.mono_right subset_union_left)
          (by simpa only [hunion] using havoidF.mono_right subset_union_right)
          s.2.1 s.2.2
          (by simpa only [hunion] using hFedges) hFcofaces
          (Q s) (hQ s) (A s) (hmap s) (hA s) hminimum
      let F' := F.trans Phi
      have himage (B : Set X) : F' '' B = Phi '' (F '' B) := by
        rw [image_image]
        rfl
      obtain ⟨hF'PL, hF'inv⟩ := original_PL_motion_trans_both
        e hcover F Phi hFPL hFinv hPhiPL hPhiinv
      obtain ⟨hWV, hmarksWV, hfixWV, _⟩ := protected_ambient_trans_neighborhood
        F Phi hW hV hmarks hmarksV hfix hfixV
      have hcount :
          ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
            (F' '' (⋃ i, S i))).ncard =
          ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
            (F '' (⋃ i, S i))).ncard := by
        congr 1
        rw [himage, ← hunion, iUnion_inter, iUnion_inter]
        apply iUnion_congr
        intro a
        exact hagree a.1 a.2.1 a.2.2.le
      refine ⟨F', W ∩ V, hWV, hmarksWV, hfixWV, hF'PL, hF'inv,
        ?_, ?_, ?_, ?_, ?_, ?_, hcount.le.trans hbound, ?_⟩
      · obtain ⟨sPhi⟩ := hsPhi
        refine ⟨fun i => ?_⟩
        rw [himage]
        exact sPhi i
      · simpa only [himage] using hdisPhi
      · simpa only [himage, hunion] using havoidPhi
      · simpa only [himage, hunion] using hPhiEdges
      · simpa only [himage] using hPhiCofaces
      · simpa only [himage] using hminimumPhi
      · intro q hq
        rcases Finset.mem_insert.mp hq with hqs | hqt
        · subst q
          simpa only [himage, hunion] using hposition
        · have hqs : q.1 ≠ s.1 := by
            intro heq
            have hqs' : q = s := Subtype.ext heq
            exact hst (hqs' ▸ hqt)
          have hh := (hpositions q hqt).image_of_fixed Phi hV
            (hfacesV q.1 q.2.1 q.2.2.le hqs) hfixV
          simpa only [himage] using hh
  let := K.finite_faceOfCard hK 3
  let := Fintype.ofFinite (K.FaceOfCard 3)
  obtain ⟨F, W, hW, hmarks, hfix, hFPL, hFinv, hsF, hdisF, havoidF,
      hFedges, hFcofaces, _, hbound, hpositions⟩ := hstage Finset.univ
  exact ⟨F, W, hW, hmarks, hfix, hFPL, hFinv, hsF, hdisF, havoidF,
    hFedges, hFcofaces, hbound, fun s => hpositions s (Finset.mem_univ s)⟩

end PoincareConjecture.M76
