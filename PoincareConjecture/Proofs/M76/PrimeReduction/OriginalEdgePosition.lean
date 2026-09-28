import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartEdgePrism
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalSphereChartCarrier
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartSurfacePosition
import PoincareConjecture.Proofs.M76.PrimeReduction.SphereAmbientTransport
import PoincareConjecture.Proofs.M76.Mathlib.FiniteSegmentCorrespondence

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_whole_edge_position
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S U : Set X}
    (s : ChartwisePLSphere e S)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (hU : IsOpen U) (p q : V3) (hpq : p ≠ q)
    (htarget : ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap p q t ∈ B.target)
    (hpS : B.symm p ∉ S) (hqS : B.symm q ∉ S)
    (haxis : ∀ t ∈ Ioo (0 : ℝ) 1, B.symm (AffineMap.lineMap p q t) ∈ U) :
    ∃ (G : X ≃ₜ X) (C : Set X),
      IsCompact C ∧ C ⊆ U ∧ EqOn G id Cᶜ ∧
      (∀ i j, (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      Nonempty (ChartwisePLSphere e (G '' S)) ∧
      ((G '' S) ∩ (B.symm '' segment ℝ p q)).Finite ∧
      ∀ x ∈ segment ℝ p q, B.symm x ∈ G '' S →
        ∃ (V : Set V3) (F : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ B.target ∧ F 0 = x ∧
          (∀ z, F z ∈ V → (B.symm (F z) ∈ G '' S ↔ z.2 = 0)) ∧
          ∀ z, F z ∈ V → (F z ∈ segment ℝ p q ↔ z.1 = 0) := by
  classical
  let : CompactSpace (sphere (0 : V3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V3) 1)
  let : CompactSpace S := s.parametrization.compactSpace
  have hS : IsClosed S := (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  obtain ⟨_, _, _, _, J, _, _, _, _, _, hJ, _, hcv, hJB, hJU,
      hcontacts, _, _, hfront⟩ :=
    exists_original_chart_edge_prism (by simp) B hS hU p q hpq
      htarget hpS hqS haxis
  obtain ⟨P, hP, hPs, hPc, hlocal⟩ := s.exists_finite_chart_carrier B hB J hJ hJB
  have hPJ : P.space ⊆ J.space := hPs.subset.trans inter_subset_right
  obtain ⟨D, hD, hDs⟩ := J.exists_finite_convex_frontier_triangulation hJ hcv
  obtain ⟨P0, hP0, hP0s⟩ := P.exists_finite_triangulation_inter D hP hD
  have hP0eq : P0.space = P.space ∩ frontier J.space := by rw [hP0s, hDs]
  have hsegmentB : segment ℝ p q ⊆ B.target := by
    rw [segment_eq_image_lineMap]
    rintro _ ⟨t, ht, rfl⟩
    exact htarget t ht
  have hprot : Disjoint P0.space (segment ℝ p q) := by
    apply disjoint_left.mpr
    intro x hx hxe
    obtain ⟨t, ht, rfl⟩ := (segment_eq_image_lineMap ℝ p q).subset hxe
    have hxp := hP0eq.subset hx
    exact hfront t ht hxp.2 ((hlocal _ (hPJ hxp.1)).mpr hxp.1)
  obtain ⟨T, hT, hTf, hTs⟩ :=
    SimplicialComplex.exists_finite_segment_complex (fun _ : Unit => p)
      (fun _ : Unit => q) (fun _ => hpq)
      (by intro i j; simp only [inter_self, convexHull_pair]; exact subset_refl _)
  have hTspace : T.space = segment ℝ p q := by simpa only [iUnion_const] using hTs
  have hpair : ({p, q} : Finset V3) ∈ T.faces :=
    (hTf _).mpr ⟨by simp, (), subset_refl _⟩
  have hpairCard : ({p, q} : Finset V3).card = 2 := by simp [hpq]
  have hpairHull : convexHull ℝ (({p, q} : Finset V3) : Set V3) = segment ℝ p q := by
    simp only [Finset.coe_pair, convexHull_pair]
  have hTv : T.vertices ⊆ segment ℝ p q := T.vertices_subset_space.trans hTspace.subset
  have hvertices : Disjoint P0.space T.vertices := hprot.mono_right hTv
  have hedges (a : Finset V3) (ha : a ∈ T.faces) (_ : a.card = 2) :
      (P0.space ∩ convexHull ℝ (a : Set V3)).Finite := by
    have hdis : Disjoint P0.space (convexHull ℝ (a : Set V3)) :=
      hprot.mono_right ((T.convexHull_subset_space ha).trans hTspace.subset)
    rw [hdis.inter_eq]
    exact finite_empty
  obtain ⟨H, A, G, _, _, _, _, _, hAe, _, hGB, hGout, _, hGPL, hGinv,
      hGA, hcharts⟩ :=
    exists_original_chart_surface_position (by simp) e he B hB J P P0 T
      hJ hP hP0 hT hcv (hP0eq.subset.trans inter_subset_left) hPJ hJB
      (fun _ hx => hP0eq.symm.subset hx) hPc hvertices hedges S hlocal zero_lt_one

  have hnewInterior (x : V3) (hxe : x ∈ segment ℝ p q)
      (hxS : B.symm x ∈ G '' S) : x ∈ interior J.space := by
    by_contra hxJ
    have hfix : G (B.symm x) = B.symm x := by
      rw [hGB x (hsegmentB hxe), H.outside 1 x hxJ]
    obtain ⟨y, hy, hxy⟩ := hxS
    have heq : y = B.symm x := G.injective (hxy.trans hfix.symm)
    have hxold : B.symm x ∈ S := heq ▸ hy
    obtain ⟨t, ht, rfl⟩ := (segment_eq_image_lineMap ℝ p q).subset hxe
    exact hxJ (hcontacts t ht hxold).2
  have hfinite : (A.space ∩ segment ℝ p q).Finite := by
    simpa only [hpairHull] using hAe _ hpair hpairCard.le
  let C := B.symm '' J.space
  have hC : IsCompact C := (J.isCompact_space_of_finite hJ).image_of_continuousOn
    (B.symm.continuousOn.mono hJB)
  refine ⟨G, C, hC, hJU, hGout, hGPL, hGinv, s.nonempty_image G hcover hGPL, ?_, ?_⟩
  · apply (hfinite.image B.symm).subset
    rintro y ⟨hyS, x, hxe, rfl⟩
    exact ⟨x, ⟨(hGA x (interior_subset (hnewInterior x hxe hyS))).mp hyS, hxe⟩, rfl⟩
  · intro x hxe hxS
    have hxJ := hnewInterior x hxe hxS
    have hxA : x ∈ A.space := (hGA x (interior_subset hxJ)).mp hxS
    have hxP0 : x ∉ P0.space := fun hx => disjoint_left.mp hprot hx hxe
    obtain ⟨V, F, hV, hxV, hVB, _, hF, hFs, hFe⟩ :=
      hcharts _ hpair hpairCard x ⟨hxA, hpairHull.symm.subset hxe⟩ hxJ hxP0
    exact ⟨V, F, hV, hxV, hVB, hF, hFs, by simpa only [hpairHull] using hFe⟩

end PoincareConjecture.M76
