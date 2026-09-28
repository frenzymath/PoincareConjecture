import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereSideRegions
import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedGraphImages
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.Rigidity.MarkedMixedChartStars
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.OriginalDiskStarNeighborhood
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Metric Geometry SignType

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_finite_graph_image
    {X G ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (F : X → G)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) :
    ∃ P : SimplicialComplex ℝ G, P.faces.Finite ∧ P.space = F '' S := by
  have hmap : s.map '' sphere (0 : V3) 1 = S := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [s.map_eq ⟨x, hx⟩]
      exact (s.parametrization ⟨x, hx⟩).property
    · intro x hx
      obtain ⟨z, hz⟩ := s.parametrization.surjective ⟨x, hx⟩
      refine ⟨z, z.property, ?_⟩
      rw [s.map_eq z, hz]
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V3
      (closedBall (0 : V3) 1) (sphere (0 : V3) 1))
  let J := K.frontierSubcomplex (closedBall (0 : V3) 1)
  have hJ : J.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hJs : J.space = sphere (0 : V3) 1 := by
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKs,
      frontier_closedBall _ one_ne_zero]
  have hsJ : PolyhedralPLInCharts e s.map J.space := hJs.symm ▸ s.piecewiseAffine
  obtain ⟨P, hP, hPs⟩ :=
    (hsJ.finitePiecewiseAffineOn_comp J hJ hF).exists_finite_triangulation_image
  exact ⟨P, hP, by rw [hPs, hJs, image_comp, hmap]⟩

theorem ChartwisePLSphere.exists_oriented_domain_stars
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) :
    ∃ (t : Finset R) (F : X → (t → ℝ × V3))
      (K L N : SimplicialComplex ℝ (t → ℝ × V3))
      (H : R ≃ₜ K.space) (g : (t → ℝ × V3) → R)
      (W Rpos Rneg : Set X)
      (B : N.vertices → OpenPartialHomeomorph X V3),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧ L ≤ K ∧ N ≤ K ∧
      (∀ a ∈ K.faces, (∀ v ∈ a, v ∈ L.vertices) → a ∈ L.faces) ∧
      (∀ a ∈ K.faces, (∀ v ∈ a, v ∈ N.vertices) → a ∈ N.faces) ∧
      K.space = F '' R ∧ L.space = F '' frontier R ∧ N.space = F '' S ∧
      (∀ x : R, (H x : t → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      IsOpen W ∧ S ⊆ W ∧ Rpos ∪ Rneg = W ∧ Rpos ∩ Rneg = S ∧
      IsClosed ((Subtype.val : W → X) ⁻¹' Rpos) ∧
      IsClosed ((Subtype.val : W → X) ⁻¹' Rneg) ∧
      (∀ p : N.vertices,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
        (B p).source ⊆ W ∧
        (∀ i, (e i).symm.trans (B p) ∈ piecewiseAffineGroupoid V3) ∧
        (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
        InjOn (fun z => B p (g z)) (K.closedStar p).space ∧
        (∃ O : Set X, IsOpen O ∧ (g p : X) ∈ O ∧ O ⊆ (B p).source ∧
          O ⊆ (fun z => (g z : X)) '' (K.closedStar p).space) ∧
        B p (g p) ∈ interior ((fun z => B p (g z)) '' (K.closedStar p).space) ∧
        ∀ z ∈ (K.closedStar p).space,
          (z ∈ N.space ↔ (B p (g z)) 0 = 0) ∧
          ((g z : X) ∈ Rpos ↔ 0 ≤ (B p (g z)) 0) ∧
          ((g z : X) ∈ Rneg ↔ (B p (g z)) 0 ≤ 0)) ∧
      ∀ p q : N.vertices, EqOn
        (fun z => sign ((B p (g z)) 0)) (fun z => sign ((B q (g z)) 0))
        ((K.closedStar p).space ∩ (K.closedStar q).space) := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨t, F, K0, L0, H0, hFc, hF, hK0, hL0K, hL0, hK0s, hL0s,
    hH0, _, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_domain_finite_pair
      e he.compatible he.cover hR he.halfspace
  obtain ⟨N0, hN0, hN0s⟩ := s.exists_finite_graph_image F hF
  have hN0K : N0.space ⊆ K0.space := by
    rw [hN0s, hK0s]
    exact image_mono (hSR.trans interior_subset)
  obtain ⟨x0, hx0⟩ :=
    (show (sphere (0 : V3) 1).Nonempty from NormedSpace.sphere_nonempty.mpr zero_le_one)
  let r0 : R := ⟨s.parametrization ⟨x0, hx0⟩,
    interior_subset (hSR (s.parametrization ⟨x0, hx0⟩).property)⟩
  obtain ⟨g, hgc, hg, hgPL⟩ :=
    exists_polyhedral_PL_model_inverse e K0 hK0 H0 F subset_rfl r0 hH0 hproj
  have hFinj : InjOn F R := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H0.injective (Subtype.ext
      ((hH0 ⟨x, hx⟩).trans (hxy.trans (hH0 ⟨y, hy⟩).symm))))
  have hFg (z : t → ℝ × V3) (hz : z ∈ K0.space) : F (g z) = z := by
    rw [hg ⟨z, hz⟩]
    exact (hH0 (H0.symm ⟨z, hz⟩)).symm.trans
      (congrArg Subtype.val (H0.apply_symm_apply ⟨z, hz⟩))
  have hgS (z : t → ℝ × V3) (hz : z ∈ K0.space) :
      (g z : X) ∈ S ↔ z ∈ N0.space := by
    rw [hN0s]
    constructor
    · intro h
      exact ⟨g z, h, hFg z hz⟩
    · rintro ⟨y, hy, hyz⟩
      have hyR := interior_subset (hSR hy)
      exact hFinj hyR (g z).property (hyz.trans (hFg z hz).symm) ▸ hy
  obtain ⟨W, Rp, Rn, hW, hSW, hu, hi, hpc, hnc, hlocal⟩ :=
    s.exists_side_regions he.compatible (fun x _ => he.cover x)
  choose C hxC hCW hC hside using fun x : S => hlocal x x.property
  let xS : N0.space → S := fun z => ⟨g z, (hgS z (hN0K z.property)).mpr z.property⟩
  let J : Fin 2 → SimplicialComplex ℝ (t → ℝ × V3) := ![L0, N0]
  have hJ : ∀ i, (J i).faces.Finite := by
    intro i
    fin_cases i <;> assumption
  have hJK : ∀ i, (J i).space ⊆ K0.space := by
    intro i
    fin_cases i
    · exact SimplicialComplex.space_subset_of_le hL0K
    · exact hN0K
  obtain ⟨K, A, hK, hKK0, hA, hstars⟩ :=
    hgPL.exists_full_marked_mixed_chart_stars K0 hK0
      (N0.isCompact_space_of_finite hN0) hN0K (fun z => C (xS z))
      (fun z i => (hC (xS z) i).1) (fun z => hxC (xS z))
      (fun _ => univ) (fun _ => isOpen_univ) (fun _ => mem_univ _) J hJ hJK
  let H : R ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  have hg' (z : K.space) : (g z : X) = (H.symm z : X) :=
    hg ⟨z, hKK0.space_eq.subset z.property⟩
  have hNs : (A 1).space = N0.space := (hA 1).2.1
  have hselect (p : (A 1).vertices) : ∃ z : N0.space,
      MapsTo (fun w => (g w : X)) (K.closedStar p).space (C (xS z)).source ∧
      (K.closedStar p).AffineOnFaces (fun w => C (xS z) (g w)) := by
    obtain ⟨z, _, hsource, hface⟩ := hstars p ((hA 1).1 p.property)
      (hNs.subset ((A 1).vertices_subset_space p.property))
    exact ⟨z, hsource, hface⟩
  choose z hsource hface using hselect
  let B (p : (A 1).vertices) := C (xS (z p))
  have hmodel (p : (A 1).vertices) (w : t → ℝ × V3)
      (hw : w ∈ (K.closedStar p).space) :
      (w ∈ (A 1).space ↔ (B p (g w)) 0 = 0) ∧
      ((g w : X) ∈ Rp ↔ 0 ≤ (B p (g w)) 0) ∧
      ((g w : X) ∈ Rn ↔ (B p (g w)) 0 ≤ 0) := by
    have hstarle : K.closedStar (p : t → ℝ × V3) ≤ K := fun _ ht => ht.1
    have hwK : w ∈ K0.space := hKK0.space_eq.subset
      (SimplicialComplex.space_subset_of_le hstarle hw)
    have hm := hside (xS (z p)) (g w) (hsource p hw)
    exact ⟨((Set.ext_iff.mp hNs w).trans (hgS w hwK).symm).trans hm.1, hm.2⟩
  refine ⟨t, F, K, A 0, A 1, H, g, W, Rp, Rn, B, hFc, hF, hK,
    (hA 0).1, (hA 1).1, (hA 0).2.2, (hA 1).2.2,
    hKK0.space_eq.trans hK0s, (hA 0).2.1.trans hL0s, hNs.trans hN0s,
    hH0, hKK0.space_eq.symm ▸ hgc, hg', hKK0.space_eq.symm ▸ hgPL,
    hW, hSW, hu, hi, hpc, hnc, ?_, ?_⟩
  · intro p
    have hpK : (p : t → ℝ × V3) ∈ K.vertices := (hA 1).1 p.property
    have hpS : (g p : X) ∈ S :=
      (hgS p (hKK0.space_eq.subset (K.vertices_subset_space hpK))).mpr
        (hNs.subset ((A 1).vertices_subset_space p.property))
    obtain ⟨hinj, hO, hint⟩ :=
      K.exists_original_open_neighborhood_inside_closedStar hK H g hg'
        hpK (hSR hpS) (B p) (hsource p)
    exact ⟨hsource p, hCW (xS (z p)), hC (xS (z p)), hface p,
      hinj, hO, hint, hmodel p⟩
  · intro p q w hw
    change sign ((B p (g w)) 0) = sign ((B q (g w)) 0)
    have hp := hmodel p w hw.1
    have hq := hmodel q w hw.2
    have hn : (B p (g w)) 0 ≤ 0 ↔ (B q (g w)) 0 ≤ 0 := hp.2.2.symm.trans hq.2.2
    have hz : (B p (g w)) 0 = 0 ↔ (B q (g w)) 0 = 0 := hp.1.symm.trans hq.1
    rcases lt_trichotomy ((B p (g w)) 0) 0 with hlt | heq | hgt
    · rw [sign_eq_neg_one_iff.mpr hlt,
        sign_eq_neg_one_iff.mpr (lt_of_le_of_ne (hn.mp hlt.le)
          (fun h => (ne_of_lt hlt) (hz.mpr h)))]
    · rw [sign_eq_zero_iff.mpr heq, sign_eq_zero_iff.mpr (hz.mp heq)]
    · rw [sign_eq_one_iff.mpr hgt, sign_eq_one_iff.mpr
        (lt_of_not_ge (fun h => (not_le_of_gt hgt) (hn.mpr h))) ]

end PoincareConjecture.M76
