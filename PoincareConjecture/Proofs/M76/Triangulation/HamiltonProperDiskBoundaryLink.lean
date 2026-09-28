import PoincareConjecture.Proofs.M76.Mathlib.MarkedRadialFrontierChart
import PoincareConjecture.Proofs.M76.Mathlib.SmallClosedStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.PrescribedSubdivisionVertices
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneStandardBoundaryPair










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

private theorem linear_signs_in_zero_neighborhood {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (h0 : (0 : E) ∈ interior C)
    (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0) :
    (∃ x ∈ interior C, A x < 0) ∧ ∃ x ∈ interior C, 0 < A x := by
  obtain ⟨v, hv⟩ := LinearMap.surjective hA (1 : ℝ)
  let U : Set ℝ := (fun t : ℝ => t • v) ⁻¹' interior C
  have hU : IsOpen U := isOpen_interior.preimage (continuous_id.smul continuous_const)
  have h0U : (0 : ℝ) ∈ U := by
    change (0 : ℝ) • v ∈ interior C
    simpa only [zero_smul] using h0
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 0 h0U
  have hp : ε / 2 ∈ ball (0 : ℝ) ε := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have hn : -(ε / 2) ∈ ball (0 : ℝ) ε := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  refine ⟨⟨-(ε / 2) • v, hεU hn, ?_⟩, ⟨(ε / 2) • v, hεU hp, ?_⟩⟩
  · rw [map_smul, hv, smul_eq_mul, mul_one]
    exact neg_neg_of_pos (half_pos hε)
  · rw [map_smul, hv, smul_eq_mul, mul_one]
    exact half_pos hε

private theorem finite_triangulation_of_linear_unit_halfspaces {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] {C : Set E} (hC : IsCompact C)
    (L : ι → E →ₗ[ℝ] ℝ) (hrep : C = {x | ∀ i, L i x ≤ 1}) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧ J.space = C := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let A : ι → E →ᵃ[ℝ] ℝ := fun i =>
    (L i).toAffineMap - AffineMap.const ℝ E 1
  let H := Finset.univ.image A
  apply hC.exists_finite_triangulation_of_halfspaces H
  rw [hrep]
  ext x
  simp only [H, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, A, AffineMap.coe_sub, Pi.sub_apply,
    LinearMap.coe_toAffineMap, AffineMap.const_apply, sub_nonpos]




theorem isFinitePLBallPair_link_of_halfplane_germ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (hdim : Module.finrank ℝ E = 2)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (h0K : (0 : E) ∈ K.vertices)
    (B : E →ₗ[ℝ] ℝ) (hB : B ≠ 0)
    (hpositive : ∀ x ∈ K.space, 0 ≤ B x)
    {U : Set E} (hU : IsOpen U) (h0U : (0 : E) ∈ U)
    (hlocal : ∀ x ∈ U, x ∈ K.space ↔ 0 ≤ B x) :
    IsFinitePLBallPair ℝ (K.link 0).space
      ((K.link 0).space ∩ {x | B x = 0}) := by
  classical
  let coords : E ≃L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨C, L, _, hC, hcv, h0C, hCU, hdisj, hstar, hL, hrep, _, _⟩ :=
    K.exists_small_closedStar_halfspace_neighborhood hK h0K hU h0U coords
  obtain ⟨J, hJ, hJC⟩ := finite_triangulation_of_linear_unit_halfspaces hC L hrep
  obtain ⟨hnegative, _⟩ := linear_signs_in_zero_neighborhood h0C B hB
  have hcap := J.isFinitePLBallPair_convex_frontier_affine_cap (F := ℝ)
    hJ hC hcv hJC B.toAffineMap hnegative ⟨0, h0C, B.map_zero⟩
      (by simpa using hdim)
  have hsection : (K.closedStar 0).space ∩ frontier C =
      frontier C ∩ {x | 0 ≤ B x} := by
    ext x
    constructor
    · rintro ⟨hx, hxC⟩
      exact ⟨hxC, hpositive x (SimplicialComplex.space_subset_of_le
        (show K.closedStar 0 ≤ K from fun _ hs => hs.1) hx)⟩
    · rintro ⟨hxC, hxB⟩
      have hxC' := hC.isClosed.frontier_subset hxC
      exact ⟨(hstar.subset ⟨(hlocal x (hCU hxC')).mpr hxB, hxC'⟩).1, hxC⟩
  have hrespect : (K.link 0).RespectsAffineHyperplane B.toAffineMap := by
    intro s hs
    exact Or.inr (fun x hx => hpositive x (K.convexHull_subset_space hs.1 hx))
  obtain ⟨e, he, hezero⟩ :=
    K.exists_finitePL_link_convex_frontier_chart_preserving_zero hK B hrespect
      hC hcv h0C hdisj L hL hrep
  let d := e.trans (Homeomorph.setCongr hsection)
  have hd : d.IsFinitePL := he.setCongr rfl hsection
  apply hcap.of_homeomorph inter_subset_left d hd
  intro x
  change ((x : E) ∈ (K.link 0).space ∧ B x = 0) ↔
    ((d x : E) ∈ frontier C ∧ B (d x : E) = 0)
  exact ⟨fun hx => ⟨(d x).property.1, (hezero x).mpr hx.2⟩,
    fun hx => ⟨x.property, (hezero x).mp hx.2⟩⟩





theorem exists_pair_chart_of_finitePL_halfplane_patch {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    {Q : Set (Fin 2 → ℝ)} {S V : Set E}
    {f : (Fin 2 → ℝ) → E} (hf : FinitePiecewiseAffineOn f Q)
    (hinj : InjOn f Q) (hf0 : f 0 = 0) (h0Q : (0 : Fin 2 → ℝ) ∈ Q)
    (B : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (hB : B ≠ 0)
    (hQpositive : ∀ x ∈ Q, 0 ≤ B x)
    {U : Set (Fin 2 → ℝ)} (hU : IsOpen U) (h0U : (0 : Fin 2 → ℝ) ∈ U)
    (hQlocal : ∀ x ∈ U, x ∈ Q ↔ 0 ≤ B x)
    (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0)
    (hfpositive : ∀ x ∈ Q, 0 ≤ A (f x))
    (hfzero : ∀ x ∈ Q, A (f x) = 0 ↔ B x = 0)
    (hV : IsOpen V) (h0V : (0 : E) ∈ V)
    (hfull : S ∩ V = (f '' Q) ∩ V) :
    ∃ H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ),
      (0 : E) ∈ H.source ∧ H.source ⊆ V ∧
      H.target = interior (CoordinateHalfBoxes.box 1) ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧ H 0 = 0 ∧
      (∀ x ∈ H.source, 0 ≤ A x ↔ 0 ≤ (H x).1.1) ∧
      ∀ x ∈ H.source, x ∈ S ↔ 0 ≤ (H x).1.1 ∧ (H x).2 = 0 := by
  classical
  obtain ⟨K, hK, hKQ, hfK⟩ := hf
  obtain ⟨D, hD, hDK, h0D⟩ := K.exists_finite_subdivision_with_vertices hK {0}
    (by simpa only [Finset.coe_singleton, singleton_subset_iff, hKQ] using h0Q)
  have hDs : D.space = Q := hDK.space_eq.trans hKQ
  have hvertex : (0 : Fin 2 → ℝ) ∈ D.vertices := h0D (by simp)
  have hfD : D.AffineOnFaces f := hDK.affineOnFaces hfK
  have hinjD : InjOn f D.space := hinj.mono hDs.subset
  have hsource := isFinitePLBallPair_link_of_halfplane_germ (by simp) D hD
    hvertex B hB (fun x hx => hQpositive x (hDs.subset hx)) hU h0U
      (fun x hx => by rw [hDs]; exact hQlocal x hx)
  let M := hfD.embeddedImage hinjD
  have hM : M.faces.Finite := hfD.embeddedImage_finite hinjD hD
  have hMs : M.space = f '' Q := by rw [hfD.embeddedImage_space, hDs]
  have h0M : (0 : E) ∈ M.vertices := by
    rw [hfD.embeddedImage_vertices]
    exact ⟨0, hvertex, hf0⟩
  have hMpositive (x : E) (hx : x ∈ M.space) : 0 ≤ A x := by
    rw [hMs] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hfpositive y hy
  have hlink : (M.link 0).space = f '' (D.link 0).space := by
    simpa only [hf0] using hfD.embeddedImage_link_space hinjD hvertex
  have hlinksub : (D.link 0).space ⊆ D.space :=
    SimplicialComplex.space_subset_of_le (fun _ hs => hs.1)
  have hfLink : (D.link 0).AffineOnFaces f := fun s hs => hfD s hs.1
  let d := (hfLink.homeomorphImage (SimplicialComplex.finite_link_faces hD 0)
    (hinjD.mono hlinksub)).trans (Homeomorph.setCongr hlink.symm)
  have hd : d.IsFinitePL :=
    ⟨f, ⟨D.link 0, SimplicialComplex.finite_link_faces hD 0, rfl, hfLink⟩,
      fun _ => rfl⟩
  have htarget : IsFinitePLBallPair ℝ (M.link 0).space
      ((M.link 0).space ∩ {x | A x = 0}) := by
    apply hsource.of_homeomorph inter_subset_left d.symm hd.symm
    intro x
    have hfx : f (d.symm x) = (x : E) := congrArg Subtype.val (d.apply_symm_apply x)
    have hz := hfzero (d.symm x) (hDs.subset (hlinksub (d.symm x).property))
    rw [hfx] at hz
    exact ⟨fun hx => ⟨(d.symm x).property, hz.mp hx.2⟩,
      fun hx => ⟨x.property, hz.mpr hx.2⟩⟩
  let coords : E ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨C, L, _, hC, hcv, h0C, hCV, hdisj, hstar, hL, hrep, _, _⟩ :=
    M.exists_small_closedStar_halfspace_neighborhood hM h0M hV h0V coords
  obtain ⟨J, hJ, hJC⟩ := finite_triangulation_of_linear_unit_halfspaces hC L hrep
  have hrespect : (M.link 0).RespectsAffineHyperplane A.toAffineMap := by
    intro s hs
    exact Or.inr (fun x hx => hMpositive x (M.convexHull_subset_space hs.1 hx))
  obtain ⟨e, he, hezero⟩ :=
    M.exists_finitePL_link_convex_frontier_chart_preserving_zero hM A hrespect
      hC hcv h0C hdisj L hL hrep
  let w := (M.closedStar 0).space ∩ frontier C
  have hw : IsFinitePLBallPair ℝ w (w ∩ {x | A x = 0}) := by
    apply htarget.of_homeomorph inter_subset_left e.symm he.symm
    intro x
    have hz := hezero (e.symm x)
    rw [e.apply_symm_apply] at hz
    exact ⟨fun hx => ⟨(e.symm x).property, hz.mp hx.2⟩,
      fun hx => ⟨x.property, hz.mpr hx.2⟩⟩
  obtain ⟨a, b, hab, hboundary⟩ := hw.exists_boundary_eq_pair
  have ha : a ∈ w ∩ {x | A x = 0} := hboundary.symm.subset (Or.inl rfl)
  have hb : b ∈ w ∩ {x | A x = 0} := hboundary.symm.subset (Or.inr rfl)
  have hwab : IsFinitePLBallPair ℝ w {a, b} := hboundary ▸ hw
  have hproper : w \ {a, b} ⊆
      (frontier C ∩ {x | 0 ≤ A x}) \ (frontier C ∩ {x | A x = 0}) := by
    intro x hx
    refine ⟨⟨hx.1.2, hMpositive x (SimplicialComplex.space_subset_of_le
      (show M.closedStar 0 ≤ M from fun _ hs => hs.1) hx.1.1)⟩, ?_⟩
    exact fun hz => hx.2 (hboundary.subset ⟨hx.1, hz.2⟩)
  have hSC : S ∩ C = M.space ∩ C := by
    ext x
    constructor
    · rintro ⟨hx, hxC⟩
      exact ⟨hMs.symm.subset (hfull.subset ⟨hx, hCV hxC⟩).1, hxC⟩
    · rintro ⟨hx, hxC⟩
      exact ⟨(hfull.symm.subset ⟨hMs.subset hx, hCV hxC⟩).1, hxC⟩
  have hcone : S ∩ C = convexJoin ℝ {0} w := by
    rw [hSC, hstar]
    exact (M.convexJoin_closedStar_frontier_eq_inter hC hcv h0C hdisj
      ⟨a, ha.1⟩).symm
  obtain ⟨hnegative, hpositive⟩ := linear_signs_in_zero_neighborhood h0C A hA
  obtain ⟨H, hHs, hHt, hH, hHi, hH0, hHA, hHS⟩ :=
    exists_standard_boundary_pair_chart hdim J hJ hC hcv hJC h0C A
      hnegative hpositive hab ha.1.2 hb.1.2 ha.2 hb.2 hwab hproper hcone
  exact ⟨H, hHs.symm.subset h0C, fun _ hx => hCV (interior_subset (hHs.subset hx)),
    hHt, hH, hHi, hH0, hHA, hHS⟩

end PoincareConjecture.M76.HamiltonIndexOne
