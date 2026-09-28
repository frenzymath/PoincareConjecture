import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryStep
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMarkedChartMotion












set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

set_option maxHeartbeats 800000 in







theorem Step.exists_original_boundary_branch_operation_with_closed_support
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup)
    (a b : D) (hab : a ≠ b) (haRim : (a : V2) ∈ Rim)
    (hpair : step.projection (step.inclusion (old.map a)) =
      step.projection (step.inclusion (old.map b)))
    {U : Set s.Carrier} (hU : IsOpen U)
    (haU : step.projection (step.inclusion (old.map a)) ∈ U) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
      (J B P C₀ R₀ B₀ K K₀ L : SimplicialComplex ℝ V3)
      (q : V3 → V2) (ρ δ : ℝ),
      old.map a ∈ w.left.source ∧ old.map b ∈ w.right.source ∧
      step.projection (step.inclusion (old.map a)) ∈ Q.source ∧
      Q (step.projection (step.inclusion (old.map a))) = 0 ∧
      Q.source ⊆ U ∩ w.target ∧
      (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ Q.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ (c (Q y)).1.1) ∧
      (∀ y ∈ Q.source, y ∈ frontier (s.projection ⁻¹' R) ↔ (c (Q y)).1.1 = 0) ∧
      (∀ y ∈ Q.source,
        y ∈ (step.projection ∘ step.inclusion) '' (old.map '' D ∩ w.left.source) ↔
          0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0) ∧
      J.faces.Finite ∧ Convex ℝ J.space ∧ J.space ⊆ Q.target ∧
      (0 : V3) ∈ interior J.space ∧ 0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
      closedBall (0 : V3) ρ ⊆ interior J.space ∧
      B.faces.Finite ∧ P.faces.Finite ∧ C₀.faces.Finite ∧
      B.space = (w.right.trans Q) '' (old.map '' D ∩ (w.right.trans Q).source) ∩
        J.space ∧ P.space = B.space ∩ {z | (c z).1.1 = 0} ∧
      P.space = (w.right.trans Q) '' (old.map '' Rim ∩ (w.right.trans Q).source) ∩
        J.space ∧ C₀.space = B.space \ ball (0 : V3) ρ ∧
      FinitePiecewiseAffineOn q B.space ∧ InjOn q B.space ∧ MapsTo q B.space D ∧
      (∀ z ∈ B.space, old.map (q z) ∈ (w.right.trans Q).source ∧
        (w.right.trans Q) (old.map (q z)) = z) ∧
      (∀ x ∈ D, old.map x ∈ (w.right.trans Q).source →
        (w.right.trans Q) (old.map x) ∈ J.space → q ((w.right.trans Q) (old.map x)) = x) ∧
      (∀ z ∈ B.space, z ∈ P.space ↔ q z ∈ Rim) ∧
      R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ B₀ ≤ R₀ ∧ B₀.space = B.space ∧
      B₀.AffineOnFaces q ∧ K ≤ B₀ ∧ K.space = P.space ∧ K₀ ≤ K ∧
      K₀.space = P.space ∩ (C₀.space ∪ frontier J.space) ∧
      (∀ face ∈ K.faces, (∀ v ∈ face, v ∈ K₀.vertices) → face ∈ K₀.faces) ∧
      L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).1.1 = 0 ∧ (c z).2 = 0} ∧
      (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
        (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
      0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
      ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space C₀.space ε,
        R₀.AffineOnFaces (H.map 1) ∧
        (∀ u z, (c (H.map u z)).1.1 = (c z).1.1) ∧
        (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → ∀ u,
          (0 < (c (H.map u v)).2 ↔ 0 < (c v).2) ∧
          ((c (H.map u v)).2 < 0 ↔ (c v).2 < 0)) ∧
        (∀ v ∈ K.vertices,
          (c (H.map 1 v)).2 = 0 ↔ v ∈ K₀.vertices ∧ (c v).2 = 0) ∧
        (∀ face ∈ K.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) ↔
          face ∈ K₀.faces ∧ ∀ v ∈ face, (c v).2 = 0) ∧
        (∀ face ∈ B₀.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) →
          ∀ v ∈ face, (c v).2 = 0) ∧
        (∀ face ∈ K.faces, face ∉ K₀.faces → ∀ other ∈ L.faces,
          affineSpan ℝ (H.map 1 '' (face : Set V3) ∪ (other : Set V3)) =
              ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
                ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp
                  c.toContinuousLinearMap)).ker.toAffineSubspace ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (face : Set V3))))
              (convexHull ℝ (other : Set V3))) ∧
        ∃ Bnew Knew : SimplicialComplex ℝ V3,
          Bnew.faces.Finite ∧ Knew.faces.Finite ∧ Knew ≤ Bnew ∧ K₀ ≤ Knew ∧
          Bnew.faces = (fun face => face.image (H.map 1)) '' B₀.faces ∧
          Knew.faces = (fun face => face.image (H.map 1)) '' K.faces ∧
          Knew.vertices = H.map 1 '' K.vertices ∧
          Bnew.space = H.map 1 '' B.space ∧ Knew.space = H.map 1 '' P.space ∧
          Bnew.AffineOnFaces (q ∘ (H.map 1).symm) ∧
          InjOn (q ∘ (H.map 1).symm) Bnew.space ∧
        ∃ (G : I → t.Carrier ≃ₜ t.Carrier) (new : StageMarkedDisk t R Fmark base Jgroup)
          (eta : old.rim.Homotopy new.rim),
          Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
          Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
          (∀ x, G 0 x = x) ∧
          (∀ u, EqOn (G u)
            ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
              (w.right.trans Q).source) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' C₀.space)) ∧
          (∀ u, EqOn (G u) id w.left.source) ∧
          (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
            (G u) ⁻¹' frontier (t.projection ⁻¹' R) = frontier (t.projection ⁻¹' R) ∧
            (G u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
          (∀ u k l, (t.charts k).symm.trans
            ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
          (∀ x, new.map x = G 1 (old.map x)) ∧
          new.basepath = old.basepath.trans (eta.evalAt squareRimBase) ∧
          (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
            H.map 1 '' B.space ∧
          (w.right.trans Q) '' (new.map '' Rim ∩ (w.right.trans Q).source) ∩ J.space =
            H.map 1 '' P.space ∧
          ∃ (Z : SimplicialComplex ℝ (V2 × V2)) (E : SimplicialComplex ℝ V2)
            (first : Z.space ≃ₜ E.space),
            Z.faces.Finite ∧ E.faces.Finite ∧
            Z.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
              step.projection (step.inclusion (new.map z.1)) =
                step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
            E.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
              step.projection (step.inclusion (new.map x)) =
                step.projection (step.inclusion (new.map y))} ∧
            first.IsFinitePL ∧ first.symm.IsFinitePL ∧
            ∀ z : Z.space, (first z : V2) = z.val.1 := by
  classical
  let p := step.projection ∘ step.inclusion
  obtain ⟨Vmark, hVmark, hFmark⟩ := exists_open_frontier_mark hF hopen
  have haF : t.projection (old.map a) ∈ Fmark := by
    rw [old.boundary_values ⟨a, haRim⟩]
    exact (old.rim ⟨a, haRim⟩).property
  have haMark : p (old.map a) ∈ s.projection ⁻¹' Vmark := by
    change s.projection (step.projection (step.inclusion (old.map a))) ∈ Vmark
    rw [← step.original_eq]
    exact (hFmark.subset haF).2
  obtain ⟨w, c, Q, ha, hb, haQ, hQW, hQzero, hQPL, hbranches, _, hmodel,
    hproper, hclip⟩ := step.exists_original_double_branch_chart he old.piecewiseAffine
      old.embedding old.inside old.whole_boundary_iff a b hab hpair
      (hU.inter (hVmark.preimage s.projection.continuous)) ⟨haU, haMark⟩
  have hQw : Q.source ⊆ w.target := fun _ hz => (hQW hz).2
  obtain ⟨hregion, hfront, hsheet⟩ :
      (∀ y ∈ Q.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ (c (Q y)).1.1) ∧
      (∀ y ∈ Q.source, y ∈ frontier (s.projection ⁻¹' R) ↔ (c (Q y)).1.1 = 0) ∧
      (∀ y ∈ Q.source, y ∈ p '' (old.map '' D ∩ w.left.source) ↔
        0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0) := by
    rcases hmodel with ⟨hinterior, _⟩ | hboundary
    · exact ((hproper a).mpr haRim).2 (hinterior haQ) |>.elim
    · exact hboundary
  have hzeroQ : (0 : V3) ∈ Q.target := hQzero ▸ Q.map_source haQ
  have hprism : ∃ J : SimplicialComplex ℝ V3,
      J.faces.Finite ∧ Convex ℝ J.space ∧ J.space ⊆ Q.target ∧
      (0 : V3) ∈ interior J.space := by
    obtain ⟨d, T, hd, _, hTs, hTQ, _, _⟩ :=
      SimplicialComplex.exists_nested_finite_coordinate_cubes Q.open_target hzeroQ
    let u : V3 := fun _ => -d
    let v : V3 := fun _ => d
    have hu : u ∈ closedBall (0 : V3) (3 * d) := by
      simp only [mem_closedBall, dist_zero_right, u, pi_norm_const, Real.norm_eq_abs, abs_neg]
      rw [abs_of_pos hd]
      linarith
    have hv : v ∈ closedBall (0 : V3) (3 * d) := by
      simpa only [u, v, mem_closedBall, dist_zero_right, pi_norm_const,
        Real.norm_eq_abs, abs_neg] using hu
    have hline (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
        AffineMap.lineMap u v z ∈ Q.target := by
      apply hTQ
      rw [hTs]
      exact (convex_closedBall (0 : V3) (3 * d)).segment_subset hu hv
        (lineMap_mem_segment ℝ u v hz)
    have huv : u ≠ v := by
      intro h
      have h' := congrFun h (0 : Fin 3)
      change -d = d at h'
      linarith
    have hu0 : u ≠ 0 := by
      intro h
      have h' := congrFun h (0 : Fin 3)
      change -d = 0 at h'
      linarith
    have hv0 : v ≠ 0 := by
      intro h
      have h' := congrFun h (0 : Fin 3)
      change d = 0 at h'
      exact hd.ne' h'
    have huQ : u ∈ Q.target := by simpa using hline 0 (by simp)
    have hvQ : v ∈ Q.target := by simpa using hline 1 (by simp)
    have hun : Q.symm u ∉ ({Q.symm 0} : Set s.Carrier) :=
      fun h => hu0 (Q.symm.injOn huQ hzeroQ h)
    have hvn : Q.symm v ∉ ({Q.symm 0} : Set s.Carrier) :=
      fun h => hv0 (Q.symm.injOn hvQ hzeroQ h)
    obtain ⟨_, _, _, _, J, _, _, _, _, _, hJ, _, hcv, hJQ, _, hcontact, _, _, _⟩ :=
      PoincareConjecture.M76.exists_original_chart_edge_prism (by simp) Q
        isClosed_singleton Q.open_source u v huv hline hun hvn
        (fun z hz => Q.map_target (hline z ⟨hz.1.le, hz.2.le⟩))
    have hmid : AffineMap.lineMap u v (1 / 2 : ℝ) = 0 := by
      rw [AffineMap.lineMap_apply_module]
      ext i
      change (1 - (1 / 2 : ℝ)) * (-d) + (1 / 2 : ℝ) * d = 0
      ring
    refine ⟨J, hJ, hcv, hJQ, ?_⟩
    have h := (hcontact (1 / 2) (by norm_num) (by rw [hmid]; rfl)).2
    simpa only [hmid] using h
  obtain ⟨J, hJ, hcv, hJQ, hzeroJ⟩ := hprism
  obtain ⟨B, q, hB, hBs, hq, hqi, hqD, hright, hleft, _⟩ := hclip J hJ hJQ
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
  have hparamRim (z : V3) (hz : z ∈ B.space) : z ∈ P.space ↔ q z ∈ Rim := by
    have hzT := hright z hz
    have hfront' := hfront (p (old.map (q z))) (by
      have h := hzT.1.2
      change w.right (old.map (q z)) ∈ Q.source at h
      rwa [congrFun w.right_eq] at h)
    have hzero : height z = 0 ↔ q z ∈ Rim := by
      change (c z).1.1 = 0 ↔ _
      have hzcoord : Q (p (old.map (q z))) = z := (hTp _).symm.trans hzT.2
      simpa only [hzcoord] using hfront'.symm.trans (hproper ⟨q z, hqD hz⟩)
    rw [hPs]
    exact (and_iff_right hz).trans hzero
  have hPr : P.space = T '' (old.map '' Rim ∩ T.source) ∩ J.space := by
    apply Subset.antisymm
    · intro z hz
      have hzB := hPB hz
      exact ⟨⟨old.map (q z),
        ⟨mem_image_of_mem old.map ((hparamRim z hzB).mp hz), (hright z hzB).1⟩,
        (hright z hzB).2⟩, hBJ hzB⟩
    · rintro z ⟨⟨x, ⟨⟨u, hu, rfl⟩, huT⟩, huz⟩, hzJ⟩
      have huD := sphere_subset_closedBall hu
      have hzB : z ∈ B.space := hBs.symm.subset
        ⟨⟨old.map u, ⟨mem_image_of_mem old.map huD, huT⟩, huz⟩, hzJ⟩
      apply (hparamRim z hzB).mpr
      have hqz : q z = u := by
        rw [← huz]
        exact hleft u huD huT (huz.symm ▸ hzJ)
      exact hqz.symm ▸ hu
  obtain ⟨radius, hradius, hradiusJ⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hzeroJ
  let ρ := radius / 2
  have hρ : 0 < ρ := half_pos hradius
  have hclosed : closedBall (0 : V3) ρ ⊆ interior J.space :=
    (closedBall_subset_ball (half_lt_self hradius)).trans hradiusJ
  have hball : ball (0 : V3) ρ ⊆ interior J.space :=
    ball_subset_closedBall.trans hclosed
  let A (i : Fin 3 × Bool) : V3 →ᵃ[ℝ] ℝ :=
    if i.2 then AffineMap.const ℝ V3 ρ - (LinearMap.proj i.1).toAffineMap
    else AffineMap.const ℝ V3 ρ + (LinearMap.proj i.1).toAffineMap
  choose L₀ hL₀ hL₀s using fun i : Fin 3 × Bool =>
    B.exists_finite_triangulation_inter_halfspaces hB {A i}
  obtain ⟨C₀, hC₀, hC₀s, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion L₀ hL₀
  have hcollar : C₀.space = B.space \ ball (0 : V3) ρ := by
    rw [hC₀s]
    ext x
    simp only [mem_iUnion, hL₀s, mem_inter_iff, mem_ofPred_eq,
      Finset.mem_singleton, forall_eq, mem_sdiff, mem_ball, dist_zero_right]
    constructor
    · rintro ⟨⟨i, b⟩, hxB, hxA⟩
      refine ⟨hxB, fun hxnorm => ?_⟩
      have hi := (pi_norm_lt_iff hρ).mp hxnorm i
      rw [Real.norm_eq_abs, abs_lt] at hi
      cases b with
      | false =>
        have hxa : ρ + x i ≤ 0 := by
          simpa only [A, Bool.false_eq_true, if_false, AffineMap.coe_add, Pi.add_apply,
            AffineMap.const_apply, LinearMap.coe_toAffineMap, LinearMap.proj_apply] using hxA
        linarith
      | true =>
        have hxa : ρ - x i ≤ 0 := by
          simpa only [A, if_true, AffineMap.coe_sub, Pi.sub_apply,
            AffineMap.const_apply, LinearMap.coe_toAffineMap, LinearMap.proj_apply] using hxA
        linarith
    · rintro ⟨hxB, hxnorm⟩
      have hn : ¬ ∀ i : Fin 3, ‖x i‖ < ρ :=
        fun h => hxnorm ((pi_norm_lt_iff hρ).mpr h)
      obtain ⟨i, hi⟩ := not_forall.mp hn
      have hi' : ¬ (-ρ < x i ∧ x i < ρ) := by
        simpa only [Real.norm_eq_abs, abs_lt] using hi
      by_cases hn : x i ≤ -ρ
      · refine ⟨(i, false), hxB, ?_⟩
        change ρ + x i ≤ 0
        linarith
      · refine ⟨(i, true), hxB, ?_⟩
        change ρ - x i ≤ 0
        have hp : ρ ≤ x i := le_of_not_gt (fun h => hi' ⟨lt_of_not_ge hn, h⟩)
        linarith
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
    hK₀K, hK₀s, hfull, hL, hLs, δ, hδ, hmargin, hmotions⟩ := hrepair
  have hqB₀ : B₀.AffineOnFaces q :=
    (show B₀.AffineOnFaces u from fun face hface =>
      (hR₀N.affineOnFaces huN) face (hB₀R hface)).congr
        (fun x hx => huq (hB₀s.subset hx))
  have hqB₀i : InjOn q B₀.space := hqi.mono hB₀s.subset
  have hwhole : p ⁻¹' (Q.symm '' J.space) =
      (w.left.trans Q).symm '' J.space ∪ T.symm '' J.space := by
    have hbranch (V : OpenPartialHomeomorph t.Carrier s.Carrier)
        (hV : (V : t.Carrier → s.Carrier) = p) (ht : V.target = w.target)
        {z : V3} (hz : z ∈ J.space) :
        p ((V.trans Q).symm z) = Q.symm z :=
      (congrFun hV _).symm.trans
        (V.right_inv (ht.symm.subset (hQw (Q.map_target (hJQ hz)))))
    ext x
    constructor
    · rintro ⟨z, hz, heq⟩
      have hxw := w.whole_preimage.subset (heq ▸ hQw (Q.map_target (hJQ hz)))
      have hside (V : OpenPartialHomeomorph t.Carrier s.Carrier)
          (hV : (V : t.Carrier → s.Carrier) = p) (hxV : x ∈ V.source) :
          x ∈ (V.trans Q).symm '' J.space := by
        refine ⟨z, hz, ?_⟩
        change V.symm (Q.symm z) = x
        rw [heq, ← congrFun hV x]
        exact V.left_inv hxV
      exact hxw.elim (fun hx => Or.inl (hside w.left w.left_eq hx))
        (fun hx => Or.inr (hside w.right w.right_eq hx))
    · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨z, hz, (hbranch w.left w.left_eq w.left_target hz).symm⟩
      · exact ⟨z, hz, (hbranch w.right w.right_eq w.right_target hz).symm⟩
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
  refine ⟨w, c, Q, J, B, P, C₀, R₀, B₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, fun _ hz => ⟨(hQW hz).1.1, hQw hz⟩,
    hQPL, hbranches, hregion, hfront, hsheet, hJ, hcv, hJQ, hzeroJ,
    hρ, hball, hclosed, hB, hP, hC₀, hBs, hPs, hPr, hcollar, hq, hqi, hqD,
    hright, hleft, hparamRim, hR₀, hR₀N.trans hNJ, hB₀R, hB₀s, hqB₀,
    hKB₀, hKs, hK₀K, hK₀s, hfull, hL, hLs, hwhole, hδ, hmargin, ?_⟩
  intro ε hε
  obtain ⟨H, hHaff, hheight, hsign, hzero, hfaces, hbranchfaces, _, hposition⟩ := hmotions ε hε
  have hHB₀ : B₀.AffineOnFaces (H.map 1) := fun face hface => hHaff face (hB₀R hface)
  have hHK : K.AffineOnFaces (H.map 1) := fun face hface => hHB₀ face (hKB₀ hface)
  have hiB : InjOn (H.map 1) B₀.space := (H.map 1).injective.injOn
  have hiK : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
  let Bnew := hHB₀.embeddedImage hiB
  let Knew := hHK.embeddedImage hiK
  have hBnew : Bnew.faces.Finite := hHB₀.embeddedImage_finite hiB (hR₀.subset hB₀R)
  have hKnew : Knew.faces.Finite :=
    hHK.embeddedImage_finite hiK (hR₀.subset (hKB₀.trans hB₀R))
  have hnewle : Knew ≤ Bnew := by
    intro face hface
    change face ∈ (hHK.embeddedImage hiK).faces at hface
    change face ∈ (hHB₀.embeddedImage hiB).faces
    rw [hHK.embeddedImage_faces hiK] at hface
    rw [hHB₀.embeddedImage_faces hiB]
    obtain ⟨oldface, holdface, rfl⟩ := hface
    exact ⟨oldface, hKB₀ holdface, rfl⟩
  have hfixK₀ (u : I) (z : V3) (hz : z ∈ K₀.space) : H.map u z = z := by
    rcases (hK₀s.subset hz).2 with hzC | hzfront
    · exact H.fixed_protected u z hzC
    · exact H.outside u z hzfront.2
  have hprotected : K₀ ≤ Knew := hHK.protected_le_embeddedImage hiK hK₀K (hfixK₀ 1)
  have hBnews : Bnew.space = H.map 1 '' B.space := by
    rw [hHB₀.embeddedImage_space hiB, hB₀s]
  have hKnews : Knew.space = H.map 1 '' P.space := by
    rw [hHK.embeddedImage_space hiK, hKs]
  have hinverse : LeftInvOn (H.map 1).symm (H.map 1) B₀.space :=
    fun z _ => (H.map 1).symm_apply_apply z
  have hnewparam : Bnew.AffineOnFaces (q ∘ (H.map 1).symm) :=
    hHB₀.comp_inverse_on_embeddedImage hqB₀ hiB hinverse
  have hnewparami : InjOn (q ∘ (H.map 1).symm) Bnew.space :=
    hHB₀.injOn_comp_inverse_on_embeddedImage hiB hqB₀i hinverse
  obtain ⟨G, hG, hGinv, hGzero, hGT, hGout, hGprotected, _, _, hGregion, hGPL, _⟩ :=
    H.exists_marked_chart_motion J hJ T.symm hJT (hCB.trans (hBJ.trans hJT))
      t.charts t.compatible (fun k => (hbranches k).2) hupper
      (fun u z => by change 0 ≤ height (H.map u z) ↔ 0 ≤ height z; rw [hheight])
      hFup hsupport
  have hformula (u : I) : EqOn (G u) (T.symm ∘ H.map u ∘ T) T.source := hGT u
  have hGleft (u : I) : EqOn (G u) id w.left.source := by
    intro x hx
    apply hGout u
    rintro ⟨z, hz, rfl⟩
    exact Set.disjoint_left.mp w.disjoint hx (T.map_target (hJT hz)).1
  obtain ⟨rim', eta, hnewPL, hnewi, hnewR, hnewproper, hrim', hout'⟩ :=
    t.exists_moved_marked_disk G hG hGzero (hGPL 1)
      (fun u => (hGregion u).1) (fun u => (hGregion u).2.2)
      old.piecewiseAffine old.embedding old.inside old.whole_boundary_iff
      old.rim old.boundary_values old.basepath Jgroup old.outside
  let new : StageMarkedDisk t R Fmark base Jgroup := {
    map := G 1 ∘ old.map
    rim := rim'
    piecewiseAffine := hnewPL
    embedding := hnewi
    inside := hnewR
    boundary_values := hrim'
    whole_boundary_iff := hnewproper
    basepath := old.basepath.trans (eta.evalAt squareRimBase)
    outside := hout' }
  have hsource (u : I) (x : t.Carrier) : G u x ∈ T.source ↔ x ∈ T.source := by
    have hout (y : t.Carrier) (hy : y ∉ T.source) : G u y = y := by
      apply hGout u
      rintro ⟨z, hz, rfl⟩
      exact hy (T.map_target (hJT hz))
    constructor
    · intro hx
      by_contra hn
      exact hn (hout x hn ▸ hx)
    · intro hx
      by_contra hn
      have hfix := hout (G u x) hn
      have heq : G u x = x := (G u).injective hfix
      exact hn (heq.symm ▸ hx)
  have hcoord (u : I) (x : t.Carrier) (hx : x ∈ T.source) :
      T (G u x) = H.map u (T x) := by
    rw [hformula u hx]
    change T (T.symm (H.map u (T x))) = H.map u (T x)
    apply T.right_inv
    by_cases hz : T x ∈ J.space
    · exact hJT ((H.carrier u).subset (mem_image_of_mem (H.map u) hz))
    · rw [H.outside u (T x) (fun h => hz (interior_subset h))]
      exact T.map_source hx
  have hJiff (u : I) (z : V3) : H.map u z ∈ J.space ↔ z ∈ J.space := by
    constructor
    · intro hz
      obtain ⟨y, hy, heq⟩ := (H.carrier u).symm.subset hz
      exact (H.map u).injective heq ▸ hy
    · intro hz
      exact (H.carrier u).subset (mem_image_of_mem (H.map u) hz)
  have himage (A : Set V2) :
      T '' (new.map '' A ∩ T.source) ∩ J.space =
        H.map 1 '' (T '' (old.map '' A ∩ T.source) ∩ J.space) := by
    apply Subset.antisymm
    · rintro z ⟨⟨y, ⟨⟨x, hx, hxy⟩, hyT⟩, hyz⟩, hzJ⟩
      have hxy' : G 1 (old.map x) = y := hxy
      have hxT : old.map x ∈ T.source :=
        (hsource 1 _).mp ((congrArg (fun v => v ∈ T.source) hxy').mpr hyT)
      have heq : H.map 1 (T (old.map x)) = z :=
        (hcoord 1 _ hxT).symm.trans ((congrArg T hxy).trans hyz)
      exact ⟨T (old.map x),
        ⟨⟨old.map x, ⟨mem_image_of_mem old.map hx, hxT⟩, rfl⟩,
          (hJiff 1 _).mp (heq.symm ▸ hzJ)⟩, heq⟩
    · rintro z ⟨y, ⟨⟨v, ⟨⟨x, hx, hxv⟩, hvT⟩, hvy⟩, hyJ⟩, rfl⟩
      have hxT : old.map x ∈ T.source := hxv.symm ▸ hvT
      have hxy : T (old.map x) = y := (congrArg T hxv).trans hvy
      refine ⟨⟨G 1 (old.map x), ⟨⟨x, hx, rfl⟩, (hsource 1 _).mpr hxT⟩, ?_⟩,
        (hJiff 1 _).mpr hyJ⟩
      rw [hcoord 1 _ hxT, hxy]
  obtain ⟨_, _, _, _, _, _, hmodelD, _⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨Source, hSource, hSourceD, _⟩, _⟩ := hmodelD
  have hnewSource : PolyhedralPLInCharts t.charts new.map Source.space := by
    rw [hSourceD]
    exact new.piecewiseAffine
  have hnewSourcei : IsEmbedding (fun x : Source.space => new.map x) :=
    new.embedding.comp (Homeomorph.setCongr hSourceD).isEmbedding
  obtain ⟨Z, E, first, hZ, hE, hZs, hEs, hfirst, hfirstinv, hfirstval⟩ :=
    step.exists_finite_double_source_polyhedron Source hSource hnewSource hnewSourcei
  refine ⟨H, hHaff, hheight, fun v hv hn u => (hsign v hv hn u).2,
    hzero, hfaces, hbranchfaces, hposition,
    Bnew, Knew, hBnew, hKnew, hnewle, hprotected,
    hHB₀.embeddedImage_faces hiB, hHK.embeddedImage_faces hiK,
    hHK.embeddedImage_vertices hiK, hBnews, hKnews,
    hnewparam, hnewparami, G, new, eta, hG, hGinv, hGzero, hformula,
    hGout, hGprotected, hGleft, hGregion, hGPL, fun _ => rfl, rfl, ?_, ?_,
    Z, E, first, hZ, hE, ?_, ?_, hfirst, hfirstinv, hfirstval⟩
  · rw [himage D, ← hBs]
  · rw [himage Rim, ← hPr]
  · simpa only [hSourceD] using hZs
  · simpa only [hSourceD] using hEs



theorem Step.exists_original_boundary_branch_operation
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup)
    (a b : D) (hab : a ≠ b) (haRim : (a : V2) ∈ Rim)
    (hpair : step.projection (step.inclusion (old.map a)) =
      step.projection (step.inclusion (old.map b)))
    {U : Set s.Carrier} (hU : IsOpen U)
    (haU : step.projection (step.inclusion (old.map a)) ∈ U) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
      (J B P C₀ R₀ B₀ K K₀ L : SimplicialComplex ℝ V3)
      (q : V3 → V2) (ρ δ : ℝ),
      old.map a ∈ w.left.source ∧ old.map b ∈ w.right.source ∧
      step.projection (step.inclusion (old.map a)) ∈ Q.source ∧
      Q (step.projection (step.inclusion (old.map a))) = 0 ∧
      Q.source ⊆ U ∩ w.target ∧
      (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ Q.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ (c (Q y)).1.1) ∧
      (∀ y ∈ Q.source, y ∈ frontier (s.projection ⁻¹' R) ↔ (c (Q y)).1.1 = 0) ∧
      (∀ y ∈ Q.source,
        y ∈ (step.projection ∘ step.inclusion) '' (old.map '' D ∩ w.left.source) ↔
          0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0) ∧
      J.faces.Finite ∧ Convex ℝ J.space ∧ J.space ⊆ Q.target ∧
      (0 : V3) ∈ interior J.space ∧ 0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
      B.faces.Finite ∧ P.faces.Finite ∧ C₀.faces.Finite ∧
      B.space = (w.right.trans Q) '' (old.map '' D ∩ (w.right.trans Q).source) ∩
        J.space ∧ P.space = B.space ∩ {z | (c z).1.1 = 0} ∧
      P.space = (w.right.trans Q) '' (old.map '' Rim ∩ (w.right.trans Q).source) ∩
        J.space ∧ C₀.space = B.space \ ball (0 : V3) ρ ∧
      FinitePiecewiseAffineOn q B.space ∧ InjOn q B.space ∧ MapsTo q B.space D ∧
      (∀ z ∈ B.space, old.map (q z) ∈ (w.right.trans Q).source ∧
        (w.right.trans Q) (old.map (q z)) = z) ∧
      (∀ x ∈ D, old.map x ∈ (w.right.trans Q).source →
        (w.right.trans Q) (old.map x) ∈ J.space → q ((w.right.trans Q) (old.map x)) = x) ∧
      (∀ z ∈ B.space, z ∈ P.space ↔ q z ∈ Rim) ∧
      R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ B₀ ≤ R₀ ∧ B₀.space = B.space ∧
      B₀.AffineOnFaces q ∧ K ≤ B₀ ∧ K.space = P.space ∧ K₀ ≤ K ∧
      K₀.space = P.space ∩ (C₀.space ∪ frontier J.space) ∧
      (∀ face ∈ K.faces, (∀ v ∈ face, v ∈ K₀.vertices) → face ∈ K₀.faces) ∧
      L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).1.1 = 0 ∧ (c z).2 = 0} ∧
      (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
        (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
      0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
      ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space C₀.space ε,
        R₀.AffineOnFaces (H.map 1) ∧
        (∀ u z, (c (H.map u z)).1.1 = (c z).1.1) ∧
        (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → ∀ u,
          (0 < (c (H.map u v)).2 ↔ 0 < (c v).2) ∧
          ((c (H.map u v)).2 < 0 ↔ (c v).2 < 0)) ∧
        (∀ v ∈ K.vertices,
          (c (H.map 1 v)).2 = 0 ↔ v ∈ K₀.vertices ∧ (c v).2 = 0) ∧
        (∀ face ∈ K.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) ↔
          face ∈ K₀.faces ∧ ∀ v ∈ face, (c v).2 = 0) ∧
        (∀ face ∈ B₀.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) →
          ∀ v ∈ face, (c v).2 = 0) ∧
        (∀ face ∈ K.faces, face ∉ K₀.faces → ∀ other ∈ L.faces,
          affineSpan ℝ (H.map 1 '' (face : Set V3) ∪ (other : Set V3)) =
              ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
                ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp
                  c.toContinuousLinearMap)).ker.toAffineSubspace ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (face : Set V3))))
              (convexHull ℝ (other : Set V3))) ∧
        ∃ Bnew Knew : SimplicialComplex ℝ V3,
          Bnew.faces.Finite ∧ Knew.faces.Finite ∧ Knew ≤ Bnew ∧ K₀ ≤ Knew ∧
          Bnew.faces = (fun face => face.image (H.map 1)) '' B₀.faces ∧
          Knew.faces = (fun face => face.image (H.map 1)) '' K.faces ∧
          Knew.vertices = H.map 1 '' K.vertices ∧
          Bnew.space = H.map 1 '' B.space ∧ Knew.space = H.map 1 '' P.space ∧
          Bnew.AffineOnFaces (q ∘ (H.map 1).symm) ∧
          InjOn (q ∘ (H.map 1).symm) Bnew.space ∧
        ∃ (G : I → t.Carrier ≃ₜ t.Carrier) (new : StageMarkedDisk t R Fmark base Jgroup)
          (eta : old.rim.Homotopy new.rim),
          Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
          Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
          (∀ x, G 0 x = x) ∧
          (∀ u, EqOn (G u)
            ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
              (w.right.trans Q).source) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' C₀.space)) ∧
          (∀ u, EqOn (G u) id w.left.source) ∧
          (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
            (G u) ⁻¹' frontier (t.projection ⁻¹' R) = frontier (t.projection ⁻¹' R) ∧
            (G u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
          (∀ u k l, (t.charts k).symm.trans
            ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
          (∀ x, new.map x = G 1 (old.map x)) ∧
          new.basepath = old.basepath.trans (eta.evalAt squareRimBase) ∧
          (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
            H.map 1 '' B.space ∧
          (w.right.trans Q) '' (new.map '' Rim ∩ (w.right.trans Q).source) ∩ J.space =
            H.map 1 '' P.space ∧
          ∃ (Z : SimplicialComplex ℝ (V2 × V2)) (E : SimplicialComplex ℝ V2)
            (first : Z.space ≃ₜ E.space),
            Z.faces.Finite ∧ E.faces.Finite ∧
            Z.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
              step.projection (step.inclusion (new.map z.1)) =
                step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
            E.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
              step.projection (step.inclusion (new.map x)) =
                step.projection (step.inclusion (new.map y))} ∧
            first.IsFinitePL ∧ first.symm.IsFinitePL ∧
            ∀ z : Z.space, (first z : V2) = z.val.1 := by
  obtain ⟨w, c, Q, J, B, P, C₀, R₀, B₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQU, hQPL, hbranches, hregion, hfront, hsheet,
    hJ, hcv, hJQ, hzeroJ, hρ, hball, _hclosed, rest⟩ :=
    step.exists_original_boundary_branch_operation_with_closed_support
      he hF hopen old a b hab haRim hpair hU haU
  exact ⟨w, c, Q, J, B, P, C₀, R₀, B₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQU, hQPL, hbranches, hregion, hfront, hsheet,
    hJ, hcv, hJQ, hzeroJ, hρ, hball, rest⟩

end Geometry.OriginalPLTower
