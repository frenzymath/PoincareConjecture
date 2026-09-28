import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Data
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Repairs.CoordinateSupport
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMarkedChartMotion

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval PLAnnularStrip
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => depth 8 z = -1 ∨ depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}

set_option maxHeartbeats 800000 in

theorem Step.nonempty_planar_annulus_boundary_motion
    (step : Step s t) {R Fmark : Set M} (he : PoincareConjecture.M76.PLDomain e R)
    (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    (Source : SimplicialComplex ℝ P2) (hSource : Source.faces.Finite)
    (hSourceAnn : Source.space = Ann)
    {j : P2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j Ann)
    (hemb : IsEmbedding (fun z : Ann => j z))
    (hDR : MapsTo j Ann (t.projection ⁻¹' R))
    (hproper : ∀ z : Ann, j z ∈ frontier (t.projection ⁻¹' R) ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1)
    (hmark : MapsTo j Rim (t.projection ⁻¹' Fmark))
    (a b : Ann) (hab : a ≠ b) (haRim : (a : P2) ∈ Rim)
    (hpair : step.projection (step.inclusion (j a)) =
      step.projection (step.inclusion (j b)))
    {W : Set s.Carrier} (hW : IsOpen W)
    (haW : step.projection (step.inclusion (j a)) ∈ W)
    (ε : ℝ) (hε : 0 < ε) :
    Nonempty (PlanarAnnulusBoundaryMotion step j R Fmark a b W ε) := by
  classical
  let p := step.projection ∘ step.inclusion
  obtain ⟨Vmark, hVmark, hFmark⟩ := exists_open_frontier_mark hF hopen
  have haMark : p (j a) ∈ s.projection ⁻¹' Vmark := by
    change s.projection (step.projection (step.inclusion (j a))) ∈ Vmark
    rw [← step.original_eq]
    exact (hFmark.subset (hmark haRim)).2
  obtain ⟨w, c, Q, ha, hb, haQ, hQW, hQzero, hQPL, hbranches, _,
    hregion, hfront, hsheet, hproperLower, hclip⟩ :=
    step.exists_original_annulus_boundary_double_branch_chart he Source hSource hSourceAnn
      hj hemb hDR hproper a b hab ((hproper a).mpr haRim) hpair
      (hW.inter (hVmark.preimage s.projection.continuous)) ⟨haW, haMark⟩
  have hQw : Q.source ⊆ w.target := fun _ hz => (hQW hz).2
  have hzeroQ : (0 : V3) ∈ Q.target := hQzero ▸ Q.map_source haQ
  obtain ⟨r₀, J, hr₀, hJ, hJs, hJQ, _, _⟩ :=
    SimplicialComplex.exists_nested_finite_coordinate_cubes Q.open_target hzeroQ
  have hcv : Convex ℝ J.space := hJs.symm ▸ convex_closedBall (0 : V3) (3 * r₀)
  have hzeroJ : (0 : V3) ∈ interior J.space := by
    rw [hJs]
    apply ball_subset_interior_closedBall
    simpa only [mem_ball, dist_self] using (show 0 < 3 * r₀ by positivity)
  obtain ⟨B, q, hB, hBs, hq, hqi, hqD, hright, hleft, hqint⟩ := hclip J hJ hJQ
  let height : V3 →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap)
  let ell : V3 →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp
    c.toContinuousLinearMap
  obtain ⟨P, hP, hPs⟩ := B.exists_finite_affineLevel_complex hB height.toLinearMap.toAffineMap 0
  have hPB : P.space ⊆ B.space := hPs.subset.trans inter_subset_left
  have hBJ : B.space ⊆ J.space := hBs.subset.trans inter_subset_right
  have hlevel : P.space ⊆ {z | height z = 0} := fun _ hz => (hPs.subset hz).2
  have htransverse : ∃ z : V3, height z = 0 ∧ ell z ≠ 0 := by
    refine ⟨c.symm ((0, 0), 1), ?_, ?_⟩
    · change (c (c.symm ((0, 0), 1))).1.1 = 0
      rw [c.apply_symm_apply]
    · change (c (c.symm ((0, 0), 1))).2 ≠ 0
      rw [c.apply_symm_apply]
      exact one_ne_zero
  let T := w.right.trans Q
  have hTQ : T.target = Q.target := by
    change Q.target ∩ Q.symm ⁻¹' w.right.target = Q.target
    apply inter_eq_left.mpr
    intro z hz
    exact w.right_target.symm.subset (hQw (Q.map_target hz))
  have hJT : J.space ⊆ T.target := hJQ.trans hTQ.symm.subset
  have hTp (x : t.Carrier) : T x = Q (p x) := congrArg Q (congrFun w.right_eq x)
  have hbT : j b ∈ T.source := by
    refine ⟨hb, ?_⟩
    change w.right (j b) ∈ Q.source
    rw [congrFun w.right_eq]
    change step.projection (step.inclusion (j b)) ∈ Q.source
    exact hpair ▸ haQ
  have hzeroB : (0 : V3) ∈ B.space := by
    apply hBs.symm.subset
    refine ⟨⟨j b, ⟨mem_image_of_mem j b.property, hbT⟩, ?_⟩, interior_subset hzeroJ⟩
    rw [hTp]
    exact (congrArg Q hpair).symm.trans hQzero
  have hparamRim (z : V3) (hz : z ∈ B.space) : z ∈ P.space ↔ q z ∈ Rim := by
    have hzT := hright z hz
    have hfront' := hfront (p (j (q z))) (by
      have h := hzT.1.2
      change w.right (j (q z)) ∈ Q.source at h
      rwa [congrFun w.right_eq] at h)
    have hzero : height z = 0 ↔ q z ∈ Rim := by
      change (c z).1.1 = 0 ↔ depth 8 (q z) = -1 ∨ depth 8 (q z) = 1
      have hzcoord : Q (p (j (q z))) = z := (hTp _).symm.trans hzT.2
      simpa only [hzcoord] using hfront'.symm.trans (hproperLower ⟨q z, hqD hz⟩)
    rw [hPs]
    exact (and_iff_right hz).trans hzero
  have hRimAnn : Rim ⊆ Ann := by
    intro z hz
    apply mem_squareAnnulus_iff_depth.mpr
    rcases hz with hz | hz <;> rw [hz] <;> norm_num
  have hPr : P.space = T '' (j '' Rim ∩ T.source) ∩ J.space := by
    apply Subset.antisymm
    · intro z hz
      have hzB := hPB hz
      exact ⟨⟨j (q z),
        ⟨mem_image_of_mem j ((hparamRim z hzB).mp hz), (hright z hzB).1⟩,
        (hright z hzB).2⟩, hBJ hzB⟩
    · rintro z ⟨⟨x, ⟨⟨u, hu, rfl⟩, huT⟩, huz⟩, hzJ⟩
      have huD := hRimAnn hu
      have hzB : z ∈ B.space := hBs.symm.subset
        ⟨⟨j u, ⟨mem_image_of_mem j huD, huT⟩, huz⟩, hzJ⟩
      apply (hparamRim z hzB).mpr
      have hqz : q z = u := by
        rw [← huz]
        exact hleft u huD huT (huz.symm ▸ hzJ)
      exact hqz.symm ▸ hu
  obtain ⟨ρ, C₀, hρ, hclosed, hC₀, hcollar, _⟩ :=
    exists_finite_branch_outer_collar J B hB hzeroJ
  have hCB : C₀.space ⊆ B.space := hcollar.subset.trans sdiff_subset
  obtain ⟨u, ⟨N₀, hN₀, hN₀J, huN₀⟩, huq, _, _⟩ :=
    hq.exists_supported_extension J hJ hBJ isOpen_univ (subset_univ _)
  obtain ⟨N, hN, hNJ, hNN₀⟩ := J.exists_common_finite_subdivision N₀ hJ hN₀ hN₀J.symm
  have huN := hNN₀.affineOnFaces huN₀
  have hNs : N.space = J.space := hNJ.space_eq
  have hrepair := exists_protected_boundary_branch_repair N B P C₀ hN hB hP hC₀
    (hNs.symm ▸ hcv) hPB (hBJ.trans hNs.symm.subset)
    (hCB.trans (hBJ.trans hNs.symm.subset)) height ell hlevel htransverse
  rw [hNs] at hrepair
  obtain ⟨R₀, B₀, K, K₀, L, hR₀, hR₀N, hB₀R, hB₀s, hKB₀, hKs,
    hK₀K, hK₀s, hfull, hL, hLs, _, _, _, hmotions⟩ := hrepair
  have hqB₀ : B₀.AffineOnFaces q :=
    (show B₀.AffineOnFaces u from fun face hface =>
      (hR₀N.affineOnFaces huN) face (hB₀R hface)).congr
        (fun x hx => huq (hB₀s.subset hx))
  obtain ⟨H, hHaff, hheight, hsign, hzero, hfaces, hbranchfaces, _, hposition⟩ := hmotions ε hε
  have hupper : ∀ z ∈ T.target,
      T.symm z ∈ t.projection ⁻¹' R ↔ 0 ≤ height z := by
    intro z hz
    have hzQ := hTQ.subset hz
    have hzright : Q.symm z ∈ w.right.target :=
      w.right_target.symm.subset (hQw (Q.map_target hzQ))
    have hproj : p (T.symm z) = Q.symm z :=
      (congrFun w.right_eq _).symm.trans (w.right.right_inv hzright)
    rw [step.region_preimage R]
    change p (T.symm z) ∈ s.projection ⁻¹' R ↔ 0 ≤ height z
    rw [hproj, hregion _ (Q.map_target hzQ), Q.right_inv hzQ]
    rfl
  have hFup : t.projection ⁻¹' Fmark =
      frontier (t.projection ⁻¹' R) ∩ t.projection ⁻¹' Vmark := by
    rw [hFmark, preimage_inter, t.frontier_region R]
  have hsupport : T.symm '' J.space ⊆ t.projection ⁻¹' Vmark := by
    rintro x ⟨z, hz, rfl⟩
    have hzQ := hJQ hz
    have hzright := w.right_target.symm.subset (hQw (Q.map_target hzQ))
    change t.projection (w.right.symm (Q.symm z)) ∈ Vmark
    rw [step.original_eq]
    have hp : p (w.right.symm (Q.symm z)) = Q.symm z :=
      (congrFun w.right_eq _).symm.trans (w.right.right_inv hzright)
    change s.projection (p (w.right.symm (Q.symm z))) ∈ Vmark
    rw [hp]
    exact (hQW (Q.map_target hzQ)).1.2
  obtain ⟨G, hG, hGinv, hGzero, hGT, hGout, hGprotected, _, _, hGregion, hGPL, hGiPL⟩ :=
    H.exists_marked_chart_motion J hJ T.symm hJT (hCB.trans (hBJ.trans hJT))
      t.charts t.compatible (fun k => (hbranches k).2) hupper
      (fun u z => by change 0 ≤ height (H.map u z) ↔ 0 ≤ height z; rw [hheight])
      hFup hsupport
  have hGleft (u : I) : EqOn (G u) id w.left.source := by
    intro x hx
    apply hGout u
    rintro ⟨z, hz, rfl⟩
    exact Set.disjoint_left.mp w.disjoint hx (T.map_target (hJT hz)).1
  have hmarkLower (y : s.Carrier) (hy : y ∈ Q.source) :
      s.projection y ∈ Fmark ↔ (c (Q y)).1.1 = 0 := by
    rw [hFmark]
    change s.projection y ∈ frontier R ∧ s.projection y ∈ Vmark ↔ _
    have hv : s.projection y ∈ Vmark := (hQW hy).1.2
    rw [and_iff_left hv]
    have hf := hfront y hy
    rwa [s.frontier_region R] at hf
  exact ⟨{
    window := w, coordinates := c, chart := Q
    left_point := ha, right_point := hb, point := haQ, centered := hQzero
    chart_inside := fun _ hz => ⟨(hQW hz).1.1, hQw hz⟩
    lower_PL := hQPL, branches_PL := hbranches
    lower_region := hregion, lower_frontier := hfront, lower_mark := hmarkLower
    left_halfplane := hsheet
    support := J, source := B, boundary := P, fixed := C₀
    ambientComplex := R₀, branchComplex := B₀, rimComplex := K, fixedRim := K₀, line := L
    parameter := q, radius := ρ, radius_pos := hρ
    support_finite := hJ, support_convex := hcv, support_target := hJQ
    center_interior := hzeroJ, closed_clearance := hclosed
    source_finite := hB, source_space := hBs, center_source := hzeroB
    boundary_finite := hP, boundary_level := hPs, boundary_space := hPr
    fixed_finite := hC₀, fixed_space := hcollar
    parameter_PL := hq, parameter_injective := hqi, parameter_range := hqD
    parameter_right := hright, parameter_left := hleft, parameter_rim := hparamRim
    parameter_interior := hqint
    ambient_finite := hR₀, subdivision := hR₀N.trans hNJ
    branch_le := hB₀R, branch_space := hB₀s, parameter_affine := hqB₀
    rim_le := hKB₀, rim_space := hKs, fixed_le := hK₀K, fixed_rim_space := hK₀s
    fixed_full := hfull, line_finite := hL, line_space := hLs
    motion := H, endpoint_affine := hHaff, height := hheight
    signs := fun v hv hn u => (hsign v hv hn u).2
    zero_vertices := hzero, zero_faces := hfaces, branch_zero_faces := hbranchfaces
    position := hposition
    ambient := G, continuous := hG, continuous_inverse := hGinv, zero := hGzero
    formula := hGT, outside := hGout, protected_fixed := hGprotected, left_fixed := hGleft
    region := fun u => (hGregion u).1
    frontier := fun u => (hGregion u).2.1
    mark := fun u => (hGregion u).2.2
    ambient_PL := hGPL, inverse_PL := hGiPL }⟩

end Geometry.OriginalPLTower
