import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcBranchChart
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcBranchLinks
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleSourcePolyhedron
import PoincareConjecture.Proofs.M76.Dehn.OriginalStageDiskMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTowerDescent
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierInteriorChartMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalChartEdgePrism

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

private theorem exists_original_centered_prism
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (Q : OpenPartialHomeomorph X V3) (hzero : (0 : V3) ∈ Q.target) :
    ∃ J : SimplicialComplex ℝ V3, J.faces.Finite ∧ Convex ℝ J.space ∧
      J.space ⊆ Q.target ∧ (0 : V3) ∈ interior J.space := by
  obtain ⟨a, T, ha, _, hTs, hTQ, _, _⟩ :=
    SimplicialComplex.exists_nested_finite_coordinate_cubes Q.open_target hzero
  let p : V3 := fun _ => -a
  let q : V3 := fun _ => a
  have hp : p ∈ closedBall (0 : V3) (3 * a) := by
    simp only [mem_closedBall, dist_zero_right, p, pi_norm_const, Real.norm_eq_abs, abs_neg]
    rw [abs_of_pos ha]
    linarith
  have hq : q ∈ closedBall (0 : V3) (3 * a) := by
    simpa only [p, q, mem_closedBall, dist_zero_right, pi_norm_const,
      Real.norm_eq_abs, abs_neg] using hp
  have hline (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap p q v ∈ Q.target := by
    apply hTQ
    rw [hTs]
    exact (convex_closedBall (0 : V3) (3 * a)).segment_subset hp hq
      (lineMap_mem_segment ℝ p q hv)
  have hpq : p ≠ q := by
    intro h
    have he := congrFun h (0 : Fin 3)
    change -a = a at he
    linarith
  have hp0 : p ≠ 0 := by
    intro h
    have he := congrFun h (0 : Fin 3)
    change -a = 0 at he
    linarith
  have hq0 : q ≠ 0 := by
    intro h
    have he := congrFun h (0 : Fin 3)
    change a = 0 at he
    exact ha.ne' he
  have hpQ : p ∈ Q.target := by simpa using hline 0 (by simp)
  have hqQ : q ∈ Q.target := by simpa using hline 1 (by simp)
  have hnotp : Q.symm p ∉ ({Q.symm 0} : Set X) :=
    fun h => hp0 (Q.symm.injOn hpQ hzero h)
  have hnotq : Q.symm q ∉ ({Q.symm 0} : Set X) :=
    fun h => hq0 (Q.symm.injOn hqQ hzero h)
  obtain ⟨_, _, _, _, J, _, _, _, _, _, hJ, _, hcv, hJQ, _, hcontact, _, _, _⟩ :=
    PoincareConjecture.M76.exists_original_chart_edge_prism (by simp) Q
      isClosed_singleton Q.open_source p q hpq hline hnotp hnotq
      (fun v hv => Q.map_target (hline v ⟨hv.1.le, hv.2.le⟩))
  have hmid : AffineMap.lineMap p q (1 / 2 : ℝ) = 0 := by
    rw [AffineMap.lineMap_apply_module]
    ext i
    change (1 - (1 / 2 : ℝ)) * (-a) + (1 / 2 : ℝ) * a = 0
    ring
  refine ⟨J, hJ, hcv, hJQ, ?_⟩
  have h := (hcontact (1 / 2) (by norm_num) (by rw [hmid]; rfl)).2
  simpa only [hmid] using h

private theorem exists_finite_branch_collar
    (J P : SimplicialComplex ℝ V3) (hP : P.faces.Finite)
    (hzero : (0 : V3) ∈ interior J.space) :
    ∃ (ρ : ℝ) (P₀ : SimplicialComplex ℝ V3), 0 < ρ ∧
      ball (0 : V3) ρ ⊆ interior J.space ∧
      closedBall (0 : V3) ρ ⊆ interior J.space ∧ P₀.faces.Finite ∧
      P₀.space = P.space \ ball (0 : V3) ρ ∧
      P.space ∩ frontier J.space ⊆ P₀.space := by
  classical
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hzero
  let ρ := r₀ / 2
  have hρ : 0 < ρ := half_pos hr₀
  have hclosed : closedBall (0 : V3) ρ ⊆ interior J.space :=
    (closedBall_subset_ball (half_lt_self hr₀)).trans hball₀
  have hball : ball (0 : V3) ρ ⊆ interior J.space := ball_subset_closedBall.trans hclosed
  let A (i : Fin 3 × Bool) : V3 →ᵃ[ℝ] ℝ :=
    if i.2 then AffineMap.const ℝ V3 ρ - (LinearMap.proj i.1).toAffineMap
    else AffineMap.const ℝ V3 ρ + (LinearMap.proj i.1).toAffineMap
  choose L hL hLs using fun i : Fin 3 × Bool =>
    P.exists_finite_triangulation_inter_halfspaces hP {A i}
  obtain ⟨P₀, hP₀, hP₀s, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion L hL
  have hspace : P₀.space = P.space \ ball (0 : V3) ρ := by
    rw [hP₀s]
    ext x
    simp only [mem_iUnion, hLs, mem_inter_iff, mem_ofPred_eq,
      Finset.mem_singleton, forall_eq, mem_sdiff, mem_ball, dist_zero_right]
    constructor
    · rintro ⟨⟨i, b⟩, hxP, hxA⟩
      refine ⟨hxP, fun hxnorm => ?_⟩
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
    · rintro ⟨hxP, hxnorm⟩
      have hn : ¬ ∀ i : Fin 3, ‖x i‖ < ρ :=
        fun h => hxnorm ((pi_norm_lt_iff hρ).mpr h)
      obtain ⟨i, hi⟩ := not_forall.mp hn
      have hi' : ¬ (-ρ < x i ∧ x i < ρ) := by
        simpa only [Real.norm_eq_abs, abs_lt] using hi
      by_cases hn : x i ≤ -ρ
      · refine ⟨(i, false), hxP, ?_⟩
        change ρ + x i ≤ 0
        linarith
      · refine ⟨(i, true), hxP, ?_⟩
        change ρ - x i ≤ 0
        have hp : ρ ≤ x i := le_of_not_gt (fun h => hi' ⟨lt_of_not_ge hn, h⟩)
        linarith
  refine ⟨ρ, P₀, hρ, hball, hclosed, hP₀, hspace, ?_⟩
  intro x hx
  rw [hspace]
  exact ⟨hx.1, fun h => hx.2.2 (hball h)⟩

private theorem whole_two_branch_chart_preimage
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} (w : TwoBranchWindow p) (Q : OpenPartialHomeomorph Y V3)
    (hQw : Q.source ⊆ w.target) {A : Set V3} (hA : A ⊆ Q.target) :
    p ⁻¹' (Q.symm '' A) = (w.left.trans Q).symm '' A ∪
      (w.right.trans Q).symm '' A := by
  have hinverse (B : OpenPartialHomeomorph X Y) (hB : (B : X → Y) = p)
      (htarget : B.target = w.target) (z : V3) (hz : z ∈ A) :
      (B.trans Q).symm z ∈ B.source ∧
        p ((B.trans Q).symm z) = Q.symm z := by
    have hzQ := Q.map_target (hA hz)
    have hzB : Q.symm z ∈ B.target := htarget.symm.subset (hQw hzQ)
    refine ⟨B.map_target hzB, ?_⟩
    change p (B.symm (Q.symm z)) = Q.symm z
    exact (congrFun hB _).symm.trans (B.right_inv hzB)
  ext x
  constructor
  · rintro ⟨z, hz, heq⟩
    have hxw : p x ∈ w.target := heq ▸ hQw (Q.map_target (hA hz))
    have hx : x ∈ w.left.source ∪ w.right.source := w.whole_preimage.subset hxw
    have hside (B : OpenPartialHomeomorph X Y) (hB : (B : X → Y) = p)
        (hxB : x ∈ B.source) : x ∈ (B.trans Q).symm '' A := by
      refine ⟨z, hz, ?_⟩
      change B.symm (Q.symm z) = x
      rw [heq, ← congrFun hB x]
      exact B.left_inv hxB
    exact hx.elim (fun h => Or.inl (hside w.left w.left_eq h))
      (fun h => Or.inr (hside w.right w.right_eq h))
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨z, hz, (hinverse w.left w.left_eq w.left_target z hz).2.symm⟩
    · exact ⟨z, hz, (hinverse w.right w.right_eq w.right_target z hz).2.symm⟩

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

open Classical in

theorem Step.exists_original_protected_branch_operation_with_closed_support
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup)
    (a b : D) (hab : a ≠ b) (haint : (a : V2) ∉ Rim)
    (hpair : step.projection (step.inclusion (old.map a)) =
      step.projection (step.inclusion (old.map b)))
    {W : Set s.Carrier} (hW : IsOpen W)
    (haW : step.projection (step.inclusion (old.map a)) ∈ W) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
      (J P P₀ R₀ K K₀ L : SimplicialComplex ℝ V3)
      (q : V3 → ℝ × ℝ) (ρ δ : ℝ),
      old.map a ∈ w.left.source ∧ old.map b ∈ w.right.source ∧
      step.projection (step.inclusion (old.map a)) ∈ Q.source ∧
      Q (step.projection (step.inclusion (old.map a))) = 0 ∧
      Q.source ⊆ W ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
      (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ Q.source,
        y ∈ (step.projection ∘ step.inclusion) '' (old.map '' D ∩ w.left.source) ↔
          (c (Q y)).2 = 0) ∧
      J.faces.Finite ∧ Convex ℝ J.space ∧ J.space ⊆ Q.target ∧
      (0 : V3) ∈ interior J.space ∧ 0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
      closedBall (0 : V3) ρ ⊆ interior J.space ∧
      P.faces.Finite ∧ P₀.faces.Finite ∧
      P.space = (w.right.trans Q) '' (old.map '' D ∩ (w.right.trans Q).source) ∩
        J.space ∧ P₀.space = P.space \ ball (0 : V3) ρ ∧
      old.map b ∈ (w.right.trans Q).source ∧ (0 : V3) ∈ P.space ∧
      FinitePiecewiseAffineOn q P.space ∧ InjOn q P.space ∧
      (∀ z ∈ P.space, z ∈ interior J.space → q z ∈ interior (q '' P.space)) ∧
      R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ K ≤ R₀ ∧ K.space = P.space ∧
      K.AffineOnFaces q ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
      L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).2 = 0} ∧
      (∀ v ∈ K.vertices, v ∈ interior J.space →
        ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
          T.HasSimplicialEdges ∧ T.boundary ℝ = (K.link v).space) ∧
      (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
        (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
      0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
      ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
        R₀.AffineOnFaces (H.map 1) ∧
        (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → ∀ u,
          (0 < (c (H.map u v)).2 ↔ 0 < (c v).2) ∧
          ((c (H.map u v)).2 < 0 ↔ (c v).2 < 0)) ∧
        (∀ v ∈ K.vertices,
          (c (H.map 1 v)).2 = 0 ↔ v ∈ K₀.vertices ∧ (c v).2 = 0) ∧
        (∀ face ∈ K.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) ↔
          face ∈ K₀.faces ∧ ∀ v ∈ face, (c v).2 = 0) ∧
        (∀ face ∈ K.faces, face ∉ K₀.faces → ∀ other ∈ L.faces,
          affineSpan ℝ (H.map 1 '' (face : Set V3) ∪ (other : Set V3)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (face : Set V3))))
              (convexHull ℝ (other : Set V3))) ∧
        ∃ Kamb Knew : SimplicialComplex ℝ V3,
          Kamb.faces.Finite ∧ Kamb.space = J.space ∧ Knew ≤ Kamb ∧
          Knew.space = H.map 1 '' P.space ∧ K₀ ≤ Knew ∧
          Knew.AffineOnFaces (q ∘ (H.map 1).symm) ∧
          InjOn (q ∘ (H.map 1).symm) Knew.space ∧
          (∀ v ∈ K.vertices,
            (Knew.link (H.map 1 v)).space = H.map 1 '' (K.link v).space ∧
            (Knew.closedStar (H.map 1 v)).space = H.map 1 '' (K.closedStar v).space) ∧
          (∀ v ∈ K.vertices, v ∈ interior J.space →
            ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
              T.HasSimplicialEdges ∧ T.boundary ℝ = (Knew.link (H.map 1 v)).space) ∧
        ∃ (G : I → t.Carrier ≃ₜ t.Carrier) (new : StageMarkedDisk t R Fmark base Jgroup),
          Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
          Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
          (∀ x, G 0 x = x) ∧
          (∀ u, EqOn (G u)
            ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
              (w.right.trans Q).source) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' P₀.space)) ∧
          (∀ u, EqOn (G u) id w.left.source) ∧
          (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
          (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
          (∀ u k l, (t.charts k).symm.trans
            ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
          (∀ x, new.map x = G 1 (old.map x)) ∧ new.rim = old.rim ∧
          HEq new.basepath old.basepath ∧
          (∀ x : Rim, new.map x = old.map x) ∧
          (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
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
  have hp : Continuous p := step.projection.continuous.comp step.inclusion.continuous
  have hregions : t.projection ⁻¹' R = p ⁻¹' (s.projection ⁻¹' R) :=
    step.region_preimage R
  have hay : p (old.map a) ∈ interior (s.projection ⁻¹' R) := by
    have haR : p (old.map a) ∈ s.projection ⁻¹' R :=
      hregions.subset (old.inside a.property)
    by_contra hn
    have hf : p (old.map a) ∈ frontier (s.projection ⁻¹' R) := ⟨subset_closure haR, hn⟩
    have hu : old.map a ∈ frontier (t.projection ⁻¹' R) :=
      (step.frontier_preimage R).symm.subset hf
    exact haint ((old.whole_boundary_iff a).mp hu)
  obtain ⟨w, c, Q, ha, hb, haQ, hQW, hQzero, hQPL, hbranches, _, hmodel, _, hclip⟩ :=
    step.exists_original_double_branch_chart he old.piecewiseAffine old.embedding
      old.inside old.whole_boundary_iff a b hab hpair
      (hW.inter isOpen_interior) ⟨haW, hay⟩
  have hQinside : Q.source ⊆ W ∩ interior (s.projection ⁻¹' R) := fun _ hx => (hQW hx).1
  have hQw : Q.source ⊆ w.target := fun _ hx => (hQW hx).2
  have hplane : ∀ y ∈ Q.source,
      y ∈ p '' (old.map '' D ∩ w.left.source) ↔ (c (Q y)).2 = 0 := by
    rcases hmodel with ⟨_, hplane⟩ | ⟨_, hfront, _⟩
    · exact hplane
    · have hf : p (old.map a) ∈ frontier (s.projection ⁻¹' R) :=
        (hfront _ haQ).mpr (by rw [hQzero, map_zero]; rfl)
      exact (hf.2 hay).elim
  have hzeroQ : (0 : V3) ∈ Q.target := hQzero ▸ Q.map_source haQ
  obtain ⟨J, hJ, hcv, hJQ, hzeroJ⟩ := exists_original_centered_prism Q hzeroQ
  obtain ⟨P, q₀, hP, hPs, hq₀, hq₀i, hq₀D, hright, _, hparameter⟩ :=
    hclip J hJ hJQ
  obtain ⟨ρ, P₀, hρ, hball, hclosed, hP₀, hP₀s, hfront⟩ :=
    exists_finite_branch_collar J P hP hzeroJ
  have hP₀P : P₀.space ⊆ P.space := hP₀s.subset.trans sdiff_subset
  have hPJ : P.space ⊆ J.space := hPs.subset.trans inter_subset_right
  let q : V3 → ℝ × ℝ := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) ∘ q₀
  have hq : FinitePiecewiseAffineOn q P.space :=
    (locallyPiecewiseAffineOn_affine
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearMap.toContinuousAffineMap
        isOpen_univ).comp_finitePiecewiseAffineOn hq₀ (mapsTo_univ _ _)
  have hqi : InjOn q P.space := fun x hx y hy h =>
    hq₀i hx hy ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).injective h)
  let B := w.right.trans Q
  have hBQ : B.target = Q.target := by
    apply inter_eq_left.mpr
    intro z hz
    exact w.right_target.symm.subset (hQw (Q.map_target hz))
  have hJB : J.space ⊆ B.target := fun z hz => hBQ.symm.subset (hJQ hz)
  have hBmaps : MapsTo p B.source Q.source := by
    intro x hx
    have heq : w.right x = p x := congrFun w.right_eq x
    exact (congrArg (fun y => y ∈ Q.source) heq).mp hx.2
  have hbB : old.map b ∈ B.source := by
    refine ⟨hb, ?_⟩
    have heq : w.right (old.map b) = p (old.map b) := congrFun w.right_eq (old.map b)
    apply (congrArg (fun y => y ∈ Q.source) heq).mpr
    change step.projection (step.inclusion (old.map b)) ∈ Q.source
    rw [← hpair]
    exact haQ
  have hzeroP : (0 : V3) ∈ P.space := by
    rw [hPs]
    refine ⟨⟨old.map b, ⟨mem_image_of_mem old.map b.property, hbB⟩, ?_⟩,
      interior_subset hzeroJ⟩
    change Q (w.right (old.map b)) = 0
    rw [congrFun w.right_eq (old.map b)]
    change Q (step.projection (step.inclusion (old.map b))) = 0
    rw [← hpair]
    exact hQzero
  have hBinside : B.source ⊆ interior (t.projection ⁻¹' R) := by
    intro x hx
    have h := preimage_interior_subset_interior_preimage hp ((hQinside (hBmaps hx)).2)
    exact interior_mono hregions.symm.subset h
  have hqint (z : V3) (hz : z ∈ P.space) (hzJ : z ∈ interior J.space) :
      q z ∈ interior (q '' P.space) := by
    have hzD := hq₀D hz
    have hn : q₀ z ∉ Rim := fun hr =>
      ((old.whole_boundary_iff ⟨q₀ z, hzD⟩).mpr hr).2 (hBinside (hright z hz).1)
    have hint : q₀ z ∈ interior D := by
      apply ball_subset_interior_closedBall
      apply mem_ball.mpr
      by_contra hlt
      exact hn (mem_sphere.mpr (le_antisymm (mem_closedBall.mp hzD) (le_of_not_gt hlt)))
    let A := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toHomeomorph
    change A (q₀ z) ∈ interior ((A ∘ q₀) '' P.space)
    have himage : A '' (q₀ '' P.space) = (A ∘ q₀) '' P.space := image_image A q₀ P.space
    exact interior_mono himage.subset
      ((A.image_interior _).subset (mem_image_of_mem A (hparameter z hz hzJ hint)))
  let ell : V3 →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  have hell : ell ≠ 0 := by
    intro h
    have hv : ell (c.symm ((0, 0), 1)) = 1 := by
      change (c (c.symm ((0, 0), 1))).2 = 1
      rw [c.apply_symm_apply]
    rw [h, zero_apply] at hv
    exact zero_ne_one hv
  obtain ⟨R₀, K, K₀, L, hR₀, hR₀J, hKR, hKs, hqK, hK₀K, hK₀s, _,
      hL, hLs, hlinks, δ, hδ, hmargin, hmotions⟩ :=
    exists_parameterized_protected_branch_repair J P P₀ hJ hP hP₀ hcv hP₀P hPJ
      hfront q hq hqi ell hell
  have hFup : t.projection ⁻¹' Fmark ⊆ frontier (t.projection ⁻¹' R) := by
    rw [t.frontier_region R]
    exact preimage_mono hF
  refine ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQinside, hQw, hQPL, hbranches, hplane,
    hJ, hcv, hJQ, hzeroJ, hρ, hball, hclosed, hP, hP₀, hPs, hP₀s, hbB, hzeroP, hq, hqi, hqint,
    hR₀, hR₀J, hKR, hKs, hqK, hK₀K, hK₀s, hL, hLs,
    fun v hv hi => hlinks v hv (hqint v (hKs.subset (K.vertices_subset_space hv)) hi),
    whole_two_branch_chart_preimage w Q hQw hJQ, hδ, hmargin, ?_⟩
  intro ε hε
  obtain ⟨H, hHaff, hsign, hzero, hfaces, hposition,
    Kamb, Knew, hKamb, hKambs, hKnew, hKnews, hK₀new,
    hnewparam, hnewparami, hnewstars, hnewlinks⟩ := hmotions ε hε
  obtain ⟨G, hG, hGinv, hGzero, hGB, hGout, hGprotected, _, _, hGfront,
      hGregion, hGPL, _⟩ :=
    H.exists_interior_chart_motion J hJ B.symm hJB (hP₀P.trans (hPJ.trans hJB))
      t.charts t.compatible (fun k => (hbranches k).2) hFup (Or.inl hBinside)
  have hformula (u : I) : EqOn (G u) (B.symm ∘ H.map u ∘ B) B.source := hGB u
  have hGleft (u : I) : EqOn (G u) id w.left.source := by
    intro x hx
    apply hGout u
    rintro ⟨z, hz, rfl⟩
    exact Set.disjoint_left.mp w.disjoint hx (B.map_target (hJB hz)).1
  obtain ⟨_, _, hnewPL, hnewi, hnewR, hnewproper, _, _⟩ :=
    t.exists_moved_marked_disk G hG hGzero (hGPL 1)
      (fun u => (hGregion u).1) (fun u => (hGregion u).2)
      old.piecewiseAffine old.embedding old.inside old.whole_boundary_iff
      old.rim old.boundary_values old.basepath Jgroup old.outside
  have hrimfix (x : Rim) : G 1 (old.map x) = old.map x := by
    apply hGfront 1
    exact (old.whole_boundary_iff ⟨x, sphere_subset_closedBall x.property⟩).mpr x.property
  let new : StageMarkedDisk t R Fmark base Jgroup := {
    map := G 1 ∘ old.map
    rim := old.rim
    piecewiseAffine := hnewPL
    embedding := hnewi
    inside := hnewR
    boundary_values := fun x => by
      change t.projection (G 1 (old.map x)) = (old.rim x : M)
      rw [hrimfix x, old.boundary_values x]
    whole_boundary_iff := hnewproper
    basepath := old.basepath
    outside := old.outside }
  have hsource (u : I) (x : t.Carrier) : G u x ∈ B.source ↔ x ∈ B.source := by
    have hout (y : t.Carrier) (hy : y ∉ B.source) : G u y = y := by
      apply hGout u
      rintro ⟨z, hz, rfl⟩
      exact hy (B.map_target (hJB hz))
    constructor
    · intro hx
      by_contra hn
      exact hn (hout x hn ▸ hx)
    · intro hx
      by_contra hn
      have hfix := hout (G u x) hn
      have heq : G u x = x := (G u).injective hfix
      exact hn (heq.symm ▸ hx)
  have hcoord (u : I) (x : t.Carrier) (hx : x ∈ B.source) :
      B (G u x) = H.map u (B x) := by
    rw [hformula u hx]
    change B (B.symm (H.map u (B x))) = H.map u (B x)
    apply B.right_inv
    by_cases hz : B x ∈ J.space
    · exact hJB ((H.carrier u).subset (mem_image_of_mem (H.map u) hz))
    · rw [H.outside u (B x) (fun h => hz (interior_subset h))]
      exact B.map_source hx
  have hJiff (u : I) (z : V3) : H.map u z ∈ J.space ↔ z ∈ J.space := by
    constructor
    · intro hz
      obtain ⟨y, hy, heq⟩ := (H.carrier u).symm.subset hz
      exact (H.map u).injective heq ▸ hy
    · intro hz
      exact (H.carrier u).subset (mem_image_of_mem (H.map u) hz)
  have himage : B '' (new.map '' D ∩ B.source) ∩ J.space = H.map 1 '' P.space := by
    apply Subset.antisymm
    · rintro z ⟨⟨y, ⟨⟨x, hx, hxy⟩, hyB⟩, hyz⟩, hzJ⟩
      have hxy' : G 1 (old.map x) = y := hxy
      have hxB : old.map x ∈ B.source :=
        (hsource 1 _).mp ((congrArg (fun v => v ∈ B.source) hxy').mpr hyB)
      have heq : H.map 1 (B (old.map x)) = z :=
        (hcoord 1 _ hxB).symm.trans ((congrArg B hxy).trans hyz)
      refine ⟨B (old.map x), ?_, heq⟩
      rw [hPs]
      exact ⟨⟨old.map x, ⟨mem_image_of_mem old.map hx, hxB⟩, rfl⟩,
        (hJiff 1 _).mp (heq.symm ▸ hzJ)⟩
    · rintro z ⟨y, hy, rfl⟩
      obtain ⟨⟨v, ⟨⟨x, hx, hxv⟩, hvB⟩, hvy⟩, hyJ⟩ := hPs.subset hy
      have hxB : old.map x ∈ B.source := hxv.symm ▸ hvB
      have hxy : B (old.map x) = y := (congrArg B hxv).trans hvy
      refine ⟨⟨G 1 (old.map x), ⟨⟨x, hx, rfl⟩, (hsource 1 _).mpr hxB⟩, ?_⟩,
        (hJiff 1 _).mpr hyJ⟩
      rw [hcoord 1 _ hxB, hxy]
  obtain ⟨_, _, _, _, _, _, hmodelD, _⟩ := isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨T, hT, hTD, _⟩, _⟩ := hmodelD
  have hnewT : PolyhedralPLInCharts t.charts new.map T.space := by
    rw [hTD]
    exact new.piecewiseAffine
  have hnewTi : IsEmbedding (fun x : T.space => new.map x) :=
    new.embedding.comp (Homeomorph.setCongr hTD).isEmbedding
  obtain ⟨Z, E, first, hZ, hE, hZs, hEs, hfirst, hfirstinv, hfirstval⟩ :=
    step.exists_finite_double_source_polyhedron T hT hnewT hnewTi
  refine ⟨H, hHaff, fun v hv hn u => (hsign v hv hn u).2,
    hzero, hfaces, hposition, Kamb, Knew, hKamb, hKambs, hKnew, hKnews,
    hK₀new, hnewparam, hnewparami, hnewstars,
    fun v hv hi => hnewlinks v hv (hqint v (hKs.subset (K.vertices_subset_space hv)) hi),
    G, new, hG, hGinv, hGzero, hformula,
    hGout, hGprotected, hGleft, hGfront, fun u => (hGregion u).1,
    hGPL, fun _ => rfl, rfl, HEq.rfl, hrimfix, himage,
    Z, E, first, hZ, hE, ?_, ?_, hfirst, hfirstinv, hfirstval⟩
  · simpa only [hTD] using hZs
  · simpa only [hTD] using hEs

open Classical in

theorem Step.exists_original_protected_branch_operation
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup)
    (a b : D) (hab : a ≠ b) (haint : (a : V2) ∉ Rim)
    (hpair : step.projection (step.inclusion (old.map a)) =
      step.projection (step.inclusion (old.map b)))
    {W : Set s.Carrier} (hW : IsOpen W)
    (haW : step.projection (step.inclusion (old.map a)) ∈ W) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
      (J P P₀ R₀ K K₀ L : SimplicialComplex ℝ V3)
      (q : V3 → ℝ × ℝ) (ρ δ : ℝ),
      old.map a ∈ w.left.source ∧ old.map b ∈ w.right.source ∧
      step.projection (step.inclusion (old.map a)) ∈ Q.source ∧
      Q (step.projection (step.inclusion (old.map a))) = 0 ∧
      Q.source ⊆ W ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
      (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ Q.source,
        y ∈ (step.projection ∘ step.inclusion) '' (old.map '' D ∩ w.left.source) ↔
          (c (Q y)).2 = 0) ∧
      J.faces.Finite ∧ Convex ℝ J.space ∧ J.space ⊆ Q.target ∧
      (0 : V3) ∈ interior J.space ∧ 0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
      P.faces.Finite ∧ P₀.faces.Finite ∧
      P.space = (w.right.trans Q) '' (old.map '' D ∩ (w.right.trans Q).source) ∩
        J.space ∧ P₀.space = P.space \ ball (0 : V3) ρ ∧
      old.map b ∈ (w.right.trans Q).source ∧ (0 : V3) ∈ P.space ∧
      FinitePiecewiseAffineOn q P.space ∧ InjOn q P.space ∧
      (∀ z ∈ P.space, z ∈ interior J.space → q z ∈ interior (q '' P.space)) ∧
      R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ K ≤ R₀ ∧ K.space = P.space ∧
      K.AffineOnFaces q ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
      L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).2 = 0} ∧
      (∀ v ∈ K.vertices, v ∈ interior J.space →
        ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
          T.HasSimplicialEdges ∧ T.boundary ℝ = (K.link v).space) ∧
      (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
        (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
      0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
      ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
        R₀.AffineOnFaces (H.map 1) ∧
        (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → ∀ u,
          (0 < (c (H.map u v)).2 ↔ 0 < (c v).2) ∧
          ((c (H.map u v)).2 < 0 ↔ (c v).2 < 0)) ∧
        (∀ v ∈ K.vertices,
          (c (H.map 1 v)).2 = 0 ↔ v ∈ K₀.vertices ∧ (c v).2 = 0) ∧
        (∀ face ∈ K.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) ↔
          face ∈ K₀.faces ∧ ∀ v ∈ face, (c v).2 = 0) ∧
        (∀ face ∈ K.faces, face ∉ K₀.faces → ∀ other ∈ L.faces,
          affineSpan ℝ (H.map 1 '' (face : Set V3) ∪ (other : Set V3)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (face : Set V3))))
              (convexHull ℝ (other : Set V3))) ∧
        ∃ Kamb Knew : SimplicialComplex ℝ V3,
          Kamb.faces.Finite ∧ Kamb.space = J.space ∧ Knew ≤ Kamb ∧
          Knew.space = H.map 1 '' P.space ∧ K₀ ≤ Knew ∧
          Knew.AffineOnFaces (q ∘ (H.map 1).symm) ∧
          InjOn (q ∘ (H.map 1).symm) Knew.space ∧
          (∀ v ∈ K.vertices,
            (Knew.link (H.map 1 v)).space = H.map 1 '' (K.link v).space ∧
            (Knew.closedStar (H.map 1 v)).space = H.map 1 '' (K.closedStar v).space) ∧
          (∀ v ∈ K.vertices, v ∈ interior J.space →
            ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
              T.HasSimplicialEdges ∧ T.boundary ℝ = (Knew.link (H.map 1 v)).space) ∧
        ∃ (G : I → t.Carrier ≃ₜ t.Carrier) (new : StageMarkedDisk t R Fmark base Jgroup),
          Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
          Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
          (∀ x, G 0 x = x) ∧
          (∀ u, EqOn (G u)
            ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
              (w.right.trans Q).source) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' P₀.space)) ∧
          (∀ u, EqOn (G u) id w.left.source) ∧
          (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
          (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
          (∀ u k l, (t.charts k).symm.trans
            ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
          (∀ x, new.map x = G 1 (old.map x)) ∧ new.rim = old.rim ∧
          HEq new.basepath old.basepath ∧
          (∀ x : Rim, new.map x = old.map x) ∧
          (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
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
  obtain ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ, h⟩ :=
    step.exists_original_protected_branch_operation_with_closed_support
      he hF old a b hab haint hpair hW haW
  refine ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ, ?_⟩
  rcases h with ⟨ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches, hplane,
    hJ, hcv, hJQ, hzeroJ, hρ, hball, _hclosed, hrest⟩
  exact ⟨ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches, hplane,
    hJ, hcv, hJQ, hzeroJ, hρ, hball, hrest⟩

end Geometry.OriginalPLTower
