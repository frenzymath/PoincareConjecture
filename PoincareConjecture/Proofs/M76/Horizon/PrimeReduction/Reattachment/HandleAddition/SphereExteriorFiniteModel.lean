import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CompactSphereDiskChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereDomainStars
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartImageIntersection
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLEqualityLoci
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompatibleInverseChart
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes

set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_finite_flat_exterior_model
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R E S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hE : IsCompact E) (heE : PLDomain e E)
    (hne : E.Nonempty) (pole : X) (hpole : pole ∈ S) (hpoleE : pole ∉ E) :
    ∃ (Q : OpenPartialHomeomorph X V3) (K B : SimplicialComplex ℝ V3),
      K.faces.Finite ∧ B ≤ K ∧ B.faces.Finite ∧
      K.space ⊆ Q.target ∩ {z | z 2 = 0} ∧
      S ∩ E ⊆ Q.source ∧ Q.source ⊆ interior R ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ Q.source, x ∈ S ↔ Q x 2 = 0) ∧
      PolyhedralPLInCharts e Q.symm K.space ∧ InjOn Q.symm K.space ∧
      Q.symm '' K.space = S ∩ E ∧ Q.symm '' B.space = S ∩ frontier E ∧
      ∀ z ∈ K.space, Q.symm z ∈ frontier E ↔ z ∈ B.space := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  have hS : IsCompact S := isCompact_iff_compactSpace.mpr s.parametrization.compactSpace
  have hSE : IsCompact (S ∩ E) := hS.inter hE
  obtain ⟨Q, hSEQ, hQR, hQ, hQS, hQt⟩ :=
    s.exists_compact_flattening_chart_with_target hR he hSR hSE inter_subset_left
      pole hpole (fun h => hpoleE h.2)
  have hQE : IsCompact (Q '' (S ∩ E)) :=
    hSE.image_of_continuousOn (Q.continuousOn.mono hSEQ)
  have hQEball : Q '' (S ∩ E) ⊆ ball (0 : V3) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hQt ▸ Q.map_source (hSEQ hx)
  obtain ⟨r, ⟨hr, hr1⟩, hQr⟩ := exists_pos_lt_subset_ball zero_lt_one hQE.isClosed hQEball
  obtain ⟨J, hJ, hJs⟩ := SimplicialComplex.exists_finite_coordinate_closedBall (0 : V3) hr.le
  have hJQ : J.space ⊆ Q.target := by rw [hJs, hQt]; exact closedBall_subset_ball hr1
  have hQJ : Q '' (S ∩ E) ⊆ J.space := hJs.symm ▸ hQr.trans ball_subset_closedBall
  obtain ⟨t, F, C, A, H, hFc, hF, hC, hAC, hA, hCs, hAs, hHF, _, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_domain_finite_pair e heE.compatible heE.cover hE heE.halfspace
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨g, _, hg, hgPL⟩ := exists_polyhedral_PL_model_inverse
    e C hC H F subset_rfl ⟨x0, hx0⟩ hHF hproj
  have hgC : (fun z => (g z : X)) '' C.space = E := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩; exact (g z).property
    · intro hx
      refine ⟨H ⟨x, hx⟩, (H ⟨x, hx⟩).property, ?_⟩
      change (g (H ⟨x, hx⟩) : X) = x
      rw [hg (H ⟨x, hx⟩), H.symm_apply_apply]
  have hgA : (fun z => (g z : X)) '' A.space = frontier E := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hyz⟩ := hAs.subset hz
      have hyE := heE.closed.frontier_subset hy
      have hzH : (⟨z, SimplicialComplex.space_subset_of_le hAC hz⟩ : C.space) = H ⟨y, hyE⟩ :=
        Subtype.ext (hyz.symm.trans (hHF ⟨y, hyE⟩).symm)
      change (g z : X) ∈ frontier E
      rw [hg ⟨z, SimplicialComplex.space_subset_of_le hAC hz⟩, hzH, H.symm_apply_apply]
      exact hy
    · intro hx
      have hxE := heE.closed.frontier_subset hx
      refine ⟨H ⟨x, hxE⟩, ?_, ?_⟩
      · rw [hHF]; exact hAs.symm.subset ⟨x, hx, rfl⟩
      · change (g (H ⟨x, hxE⟩) : X) = x
        rw [hg (H ⟨x, hxE⟩), H.symm_apply_apply]
  obtain ⟨P, hP, hPs⟩ := hgPL.exists_finite_chart_image_intersection C hC Q hQ J hJ hJQ
  obtain ⟨T, hT, hTs⟩ := (hgPL.restrict_finite A hA (SimplicialComplex.space_subset_of_le hAC)).exists_finite_chart_image_intersection
    A hA Q hQ J hJ hJQ
  rw [hgC] at hPs
  rw [hgA] at hTs
  let height : V3 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj (2 : Fin 3)).toContinuousAffineMap
  have hheightP : FinitePiecewiseAffineOn height P.space :=
    ⟨P, hP, rfl, P.affineOnFaces_affine height⟩
  have hheightT : FinitePiecewiseAffineOn height T.space :=
    ⟨T, hT, rfl, T.affineOnFaces_affine height⟩
  obtain ⟨K0, hK0, hK0s⟩ := hheightP.exists_finite_fiber_complex 0
  obtain ⟨B0, hB0, hB0s⟩ := hheightT.exists_finite_fiber_complex 0
  have hKT : K0.space ⊆ Q.target := fun z hz => hJQ ((hPs.subset (hK0s.subset hz).1).2)
  have hBT : B0.space ⊆ Q.target := fun z hz => hJQ ((hTs.subset (hB0s.subset hz).1).2)
  have hKimage : K0.space = Q '' (S ∩ E) := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨x, ⟨hxE, hxQ⟩, rfl⟩, _⟩ := hPs.subset (hK0s.subset hz).1
      exact ⟨x, ⟨(hQS x hxQ).mpr (hK0s.subset hz).2, hxE⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      apply hK0s.symm.subset
      exact ⟨hPs.symm.subset ⟨⟨x, ⟨hx.2, hSEQ hx⟩, rfl⟩, hQJ ⟨x, hx, rfl⟩⟩,
        (hQS x (hSEQ hx)).mp hx.1⟩
  have hBimage : B0.space = Q '' (S ∩ frontier E) := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨x, ⟨hxE, hxQ⟩, rfl⟩, _⟩ := hTs.subset (hB0s.subset hz).1
      exact ⟨x, ⟨(hQS x hxQ).mpr (hB0s.subset hz).2, hxE⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hxE : x ∈ S ∩ E := ⟨hx.1, heE.closed.frontier_subset hx.2⟩
      apply hB0s.symm.subset
      exact ⟨hTs.symm.subset ⟨⟨x, ⟨hx.2, hSEQ hxE⟩, rfl⟩, hQJ ⟨x, hxE, rfl⟩⟩,
        (hQS x (hSEQ hxE)).mp hx.1⟩
  have hBK : B0.space ⊆ K0.space := by
    rw [hBimage, hKimage]
    exact image_mono (inter_subset_inter_right _ heE.closed.frontier_subset)
  obtain ⟨K, B, hK, hKK, hBK', hBs⟩ :=
    K0.exists_subdivision_with_polyhedron_subcomplex B0 hK0 hB0 hBK
  have hKs : K.space = Q '' (S ∩ E) := hKK.space_eq.trans hKimage
  have hBs' : B.space = Q '' (S ∩ frontier E) := hBs.trans hBimage
  have hKQ : K.space ⊆ Q.target := hKK.space_eq ▸ hKT
  have hPL : PolyhedralPLInCharts e Q.symm K.space :=
    polyhedralPLInCharts_of_compatible_chart_inverse e he.cover Q (fun i => by
      simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm (hQ i)) K hK
      ⟨K, hK, rfl, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)⟩ hKQ
  have hback (Z : Set X) (hZ : Z ⊆ S ∩ E) : Q.symm '' (Q '' Z) = Z := by
    rw [image_image]
    exact image_congr (fun x hx => Q.left_inv (hSEQ (hZ hx))) |>.trans (image_id Z)
  refine ⟨Q, K, B, hK, hBK', hK.subset hBK', ?_, hSEQ, hQR, hQ, hQS,
    hPL, Q.symm.injOn.mono hKQ, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨hKQ hz, (hK0s.subset (hKK.space_eq.subset hz)).2⟩
  · rw [hKs]; exact hback _ subset_rfl
  · rw [hBs']; exact hback _ (inter_subset_inter_right _ heE.closed.frontier_subset)
  · intro z hz
    constructor
    · intro hf
      apply hBs'.symm.subset
      have hzS : Q.symm z ∈ S := by
        obtain ⟨x, hx, hxz⟩ := hKs.subset hz
        rw [← hxz, Q.left_inv (hSEQ hx)]
        exact hx.1
      exact ⟨Q.symm z, ⟨hzS, hf⟩, Q.right_inv (hKQ hz)⟩
    · intro hzB
      obtain ⟨x, hx, hxz⟩ := hBs'.subset hzB
      rw [← hxz, Q.left_inv (hSEQ ⟨hx.1, heE.closed.frontier_subset hx.2⟩)]
      exact hx.2

private noncomputable def exteriorPlaneInclusion : (ℝ × ℝ) →ᴬ[ℝ] V3 :=
  (ContinuousLinearMap.pi (fun i : Fin 3 =>
    if i = 0 then ContinuousLinearMap.fst ℝ ℝ ℝ
      else if i = 1 then ContinuousLinearMap.snd ℝ ℝ ℝ else 0)).toContinuousAffineMap

private noncomputable def exteriorPlaneProjection : V3 →ᴬ[ℝ] (ℝ × ℝ) :=
  ((ContinuousLinearMap.proj (0 : Fin 3)).prod
    (ContinuousLinearMap.proj (1 : Fin 3))).toContinuousAffineMap

private theorem exteriorPlaneProjection_inclusion (x : ℝ × ℝ) :
    exteriorPlaneProjection (exteriorPlaneInclusion x) = x := by
  ext <;> simp [exteriorPlaneProjection, exteriorPlaneInclusion]

private theorem exteriorPlaneInclusion_projection {x : V3} (hx : x 2 = 0) :
    exteriorPlaneInclusion (exteriorPlaneProjection x) = x := by
  ext i
  fin_cases i <;> simp [exteriorPlaneProjection, exteriorPlaneInclusion, hx]

theorem ChartwisePLSphere.exists_finite_planar_exterior_model
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R E S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hE : IsCompact E) (heE : PLDomain e E)
    (hne : E.Nonempty) (pole : X) (hpole : pole ∈ S) (hpoleE : pole ∉ E) :
    ∃ (K B : SimplicialComplex ℝ (ℝ × ℝ)) (p : (ℝ × ℝ) → X),
      K.faces.Finite ∧ B ≤ K ∧ B.faces.Finite ∧
      PolyhedralPLInCharts e p K.space ∧ InjOn p K.space ∧
      p '' K.space = S ∩ E ∧ p '' B.space = S ∩ frontier E ∧
      ∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B.space := by
  obtain ⟨Q, C, A, hC, hAC, hA, hCT, hSQ, hQR, hQ, hQS, hQC, hQi,
    hCS, hAS, hproper⟩ := s.exists_finite_flat_exterior_model hR he hSR hE heE hne pole hpole hpoleE
  let pr := exteriorPlaneProjection
  let inc := exteriorPlaneInclusion
  have hi (x : V3) (hx : x ∈ C.space) : inc (pr x) = x :=
    exteriorPlaneInclusion_projection (hCT hx).2
  obtain ⟨K0, hK0, hK0s, _⟩ := (C.affineOnFaces_affine pr).exists_finite_triangulation_image hC
  obtain ⟨B0, hB0, hB0s, _⟩ := (A.affineOnFaces_affine pr).exists_finite_triangulation_image hA
  have hB0K : B0.space ⊆ K0.space := by
    rw [hB0s, hK0s]
    exact image_mono (SimplicialComplex.space_subset_of_le hAC)
  obtain ⟨K, B, hK, hKK, hBK, hBs⟩ :=
    K0.exists_subdivision_with_polyhedron_subcomplex B0 hK0 hB0 hB0K
  have hKs : K.space = pr '' C.space := hKK.space_eq.trans hK0s
  have hBs' : B.space = pr '' A.space := hBs.trans hB0s
  have hinc (x : ℝ × ℝ) (hx : x ∈ K.space) : inc x ∈ C.space := by
    obtain ⟨y, hy, rfl⟩ := hKs.subset hx
    rwa [hi y hy]
  have hincQ : MapsTo inc K.space Q.target := fun x hx => (hCT (hinc x hx)).1
  let p : (ℝ × ℝ) → X := Q.symm ∘ inc
  have hp : PolyhedralPLInCharts e p K.space :=
    polyhedralPLInCharts_of_compatible_chart_inverse e he.cover Q (fun i => by
      simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm (hQ i)) K hK
      ⟨K, hK, rfl, K.affineOnFaces_affine inc⟩ hincQ
  have hpi : InjOn p K.space := by
    intro x hx y hy hxy
    have hh := Q.symm.injOn (hincQ hx) (hincQ hy) hxy
    have hh' := congrArg pr hh
    simpa only [pr, inc, exteriorPlaneProjection_inclusion] using hh'
  have himage (Z : Set V3) (hZ : Z ⊆ C.space) : p '' (pr '' Z) = Q.symm '' Z := by
    rw [image_image]
    exact image_congr (fun x hx => congrArg Q.symm (hi x (hZ hx)))
  refine ⟨K, B, p, hK, hBK, hK.subset hBK, hp, hpi, ?_, ?_, ?_⟩
  · rw [hKs, himage _ subset_rfl, hCS]
  · rw [hBs', himage _ (SimplicialComplex.space_subset_of_le hAC), hAS]
  · intro x hx
    change Q.symm (inc x) ∈ frontier E ↔ x ∈ B.space
    rw [hproper _ (hinc x hx), hBs']
    constructor
    · intro h
      exact ⟨inc x, h, exteriorPlaneProjection_inclusion x⟩
    · rintro ⟨y, hy, hxy⟩
      rw [← hxy, hi y (SimplicialComplex.space_subset_of_le hAC hy)]
      exact hy

theorem ChartwisePLSphere.exists_planar_exterior_model_or_subset
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R E S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hE : IsCompact E) (heE : PLDomain e E)
    (hne : E.Nonempty) :
    S ⊆ E ∨ ∃ (K B : SimplicialComplex ℝ (ℝ × ℝ)) (p : (ℝ × ℝ) → X),
      K.faces.Finite ∧ B ≤ K ∧ B.faces.Finite ∧
      PolyhedralPLInCharts e p K.space ∧ InjOn p K.space ∧
      p '' K.space = S ∩ E ∧ p '' B.space = S ∩ frontier E ∧
      ∀ z ∈ K.space, p z ∈ frontier E ↔ z ∈ B.space := by
  by_cases hSE : S ⊆ E
  · exact Or.inl hSE
  · obtain ⟨pole, hpS, hpE⟩ := Set.not_subset.mp hSE
    exact Or.inr (s.exists_finite_planar_exterior_model hR he hSR hE heE hne pole hpS hpE)

end PoincareConjecture.M76
