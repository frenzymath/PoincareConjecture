import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SelectedHoleComplement
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas









set_option autoImplicit false

open Set Metric Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere
local notation "Cube" => closedBall (0 : V3) 1

private theorem finitePL_positive_cube {ρ : ℝ} (hρ : 0 < ρ) :
    IsFinitePLBallPair V3 (closedBall (0 : V3) ρ) (Metric.sphere (0 : V3) ρ) := by
  classical
  let A : Fin 3 ⊕ Fin 3 → V3 →ᵃ[ℝ] ℝ := fun i =>
    (signedCubeCoordinate i).toAffineMap - AffineMap.const ℝ V3 ρ
  let H := Finset.univ.image A
  have hrep : closedBall (0 : V3) ρ = {x | ∀ a ∈ H, a x ≤ 0} := by
    ext x
    constructor
    · intro hx a ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      change signedCubeCoordinate i x - ρ ≤ 0
      exact sub_nonpos.mpr ((signedCubeCoordinate_le_norm i x).trans
        (mem_closedBall_zero_iff.mp hx))
    · intro hx
      apply mem_closedBall_zero_iff.mpr
      apply (pi_norm_le_iff_of_nonneg hρ.le).mpr
      intro i
      rw [Real.norm_eq_abs]
      have hp : x i ≤ ρ := sub_nonpos.mp
        (hx (A (.inl i)) (Finset.mem_image.mpr ⟨.inl i,Finset.mem_univ _,rfl⟩))
      have hn : -x i ≤ ρ := sub_nonpos.mp
        (hx (A (.inr i)) (Finset.mem_image.mpr ⟨.inr i,Finset.mem_univ _,rfl⟩))
      exact abs_le.mpr ⟨by linarith,hp⟩
  have hball := isFinitePLBallPair_of_affine_halfspaces (isCompact_closedBall _ _) H hrep
    ⟨0,ball_subset_interior_closedBall (mem_ball_self hρ)⟩
  simpa only [frontier_closedBall _ hρ.ne'] using hball




theorem IsFinitePLBallPair.exists_sphere_ball_enlargement
    {A r K : Set V4} (hA : IsFinitePLBallPair V3 A r) (hAS : A ⊆ Sphere)
    (hAopen : IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (A \ r)))
    (hK : IsCompact K) (hKS : K ⊆ Sphere) (hAK : Disjoint A K) :
    ∃ B t : Set V4, IsFinitePLBallPair V3 B t ∧ B ⊆ Sphere ∧
      A ⊆ B \ t ∧ Disjoint B K ∧
      IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B \ t)) ∧
      IsFinitePLBallPair V3 (Sphere \ (B \ t)) t := by
  classical
  let C := Sphere \ (A \ r)
  have hC : IsFinitePLBallPair V3 C r := hA.selected_hole_complement hAS hAopen
  have hKC : K ⊆ C \ r := by
    intro x hx
    have hxA : x ∉ A := fun ha => disjoint_left.mp hAK ha hx
    exact ⟨⟨hKS hx,fun h => hxA h.1⟩,fun hr => hxA (hA.1 hr)⟩
  obtain ⟨e,he,heb⟩ := hC.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  have hecopy := he
  obtain ⟨f,hf,hfval⟩ := hecopy
  have hicopy := he.symm
  obtain ⟨g,hg,hgval⟩ := hicopy
  have hgf {x : V4} (hx : x ∈ C) : g (f x) = x := by
    rw [← hfval ⟨x,hx⟩,← hgval,e.symm_apply_apply]
  have hgi : InjOn g Cube := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.symm.injective
      (Subtype.ext ((hgval ⟨x,hx⟩).trans (hxy.trans (hgval ⟨y,hy⟩).symm))))
  have hfKc : IsCompact (f '' K) :=
    hK.image_of_continuousOn (hf.continuousOn.mono (hKC.trans sdiff_subset))
  have hfKball : f '' K ⊆ ball (0 : V3) 1 := by
    rintro _ ⟨x,hx,rfl⟩
    have hxc := (hKC hx).1
    have hfx := hfval ⟨x,hxc⟩
    have hfc : f x ∈ Cube := hfx ▸ (e ⟨x,hxc⟩).property
    rw [← interior_closedBall (0 : V3) one_ne_zero]
    by_contra hn
    exact (hKC hx).2 ((heb ⟨x,hxc⟩).mpr (hfx.symm ▸ And.intro (subset_closure hfc) hn))
  obtain ⟨ρ,hρ,hfKρ⟩ := exists_pos_lt_subset_ball (by norm_num : (0 : ℝ) < 1)
    hfKc.isClosed hfKball
  have hsmall := finitePL_positive_cube hρ.1
  have hsmallsub : closedBall (0 : V3) ρ ⊆ Cube := closedBall_subset_closedBall hρ.2.le
  let D := g '' closedBall (0 : V3) ρ
  let q := g '' Metric.sphere (0 : V3) ρ
  have hD : IsFinitePLBallPair V3 D q := hsmall.image_of_subset hg hsmallsub hgi
  have hDC : D ⊆ C \ r := by
    rintro _ ⟨x,hx,rfl⟩
    have hxc := hsmallsub hx
    have hgx := hgval ⟨x,hxc⟩
    refine ⟨hgx ▸ (e.symm ⟨x,hxc⟩).property,?_⟩
    intro hr
    have hh := (heb (e.symm ⟨x,hxc⟩)).mp (hgx.symm ▸ hr)
    rw [e.apply_symm_apply,frontier_closedBall _ one_ne_zero] at hh
    have hn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hh
    have hxρ : ‖x‖ ≤ ρ := mem_closedBall_zero_iff.mp hx
    linarith [hρ.2]
  have hKD : K ⊆ D \ q := by
    intro x hx
    have hfx := hfKρ (mem_image_of_mem f hx)
    refine ⟨⟨f x,ball_subset_closedBall hfx,hgf (hKC hx).1⟩,?_⟩
    rintro ⟨y,hy,hyx⟩
    have heq : y = f x := hgi (hsmallsub (sphere_subset_closedBall hy))
      (hsmallsub (ball_subset_closedBall hfx)) (hyx.trans (hgf (hKC hx).1).symm)
    exact (mem_ball.mp hfx).ne (heq ▸ mem_sphere.mp hy)
  have hAC : A ∩ C = r := by
    ext x
    have hrr := @hA.1 x
    have hrs := @hAS x
    change (x ∈ A ∧ x ∈ Sphere ∧ ¬ (x ∈ A ∧ x ∉ r)) ↔ x ∈ r
    tauto
  have hwhole : A ∪ C = Sphere := by
    ext x
    have hx := @hAS x
    change (x ∈ A ∨ x ∈ Sphere ∧ ¬ (x ∈ A ∧ x ∉ r)) ↔ x ∈ Sphere
    tauto
  have hDopen : IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (D \ q)) := by
    have hh := hA.isOpen_double_ball_hole hC hAC hD hDC
    rwa [hwhole] at hh
  have hDS : D ⊆ Sphere := hDC.trans (sdiff_subset.trans sdiff_subset)
  let B := Sphere \ (D \ q)
  have hB : IsFinitePLBallPair V3 B q := hD.selected_hole_complement hDS hDopen
  have hAD : Disjoint A D := by
    apply disjoint_left.mpr
    intro x hxA hxD
    exact (hDC hxD).2 (hAC.subset ⟨hxA,(hDC hxD).1⟩)
  have hAB : A ⊆ B \ q := by
    intro x hx
    have hxD : x ∉ D := fun hd => disjoint_left.mp hAD hx hd
    exact ⟨⟨hAS hx,fun h => hxD h.1⟩,fun hq => hxD (hD.1 hq)⟩
  have hBK : Disjoint B K := disjoint_left.mpr fun x hx hk => hx.2 (hKD hk)
  have hBopen : IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B \ q)) := by
    have heq : (Subtype.val : Sphere → V4) ⁻¹' (B \ q) =
        ((Subtype.val : Sphere → V4) ⁻¹' D)ᶜ := by
      ext x
      have hq := @hD.1 (x : V4)
      change ((x : V4) ∈ Sphere ∧ ¬ ((x : V4) ∈ D ∧ (x : V4) ∉ q)) ∧
        (x : V4) ∉ q ↔ (x : V4) ∉ D
      have hx := x.property
      tauto
    rw [heq]
    exact (hD.isCompact.isClosed.preimage continuous_subtype_val).isOpen_compl
  exact ⟨B,q,hB,sdiff_subset,hAB,hBK,hBopen,
    hB.selected_hole_complement sdiff_subset hBopen⟩



theorem IsFinitePLBallPair.exists_sphere_ball_enlargement_subset
    {A r O : Set V4} (hA : IsFinitePLBallPair V3 A r) (hAS : A ⊆ Sphere)
    (hAopen : IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (A \ r)))
    (hO : IsOpen ((Subtype.val : Sphere → V4) ⁻¹' O)) (hAO : A ⊆ O) :
    ∃ B t : Set V4, IsFinitePLBallPair V3 B t ∧ B ⊆ Sphere ∧
      A ⊆ B \ t ∧ B ⊆ O ∧
      IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B \ t)) ∧
      IsFinitePLBallPair V3 (Sphere \ (B \ t)) t := by
  have hSc : IsCompact Sphere := by
    rw [← lower_union_upper]
    exact lower_ball.isCompact.union upper_ball.isCompact
  let : CompactSpace Sphere := isCompact_iff_compactSpace.mp hSc
  have himage : (Subtype.val : Sphere → V4) ''
      (((Subtype.val : Sphere → V4) ⁻¹' O)ᶜ) = Sphere \ O := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · intro hx
      exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  have hK : IsCompact (Sphere \ O) := himage ▸
    hO.isClosed_compl.isCompact.image continuous_subtype_val
  have hdis : Disjoint A (Sphere \ O) :=
    disjoint_left.mpr fun x hx hk => hk.2 (hAO hx)
  obtain ⟨B,t,hB,hBS,hAB,hBK,hBopen,hBc⟩ :=
    hA.exists_sphere_ball_enlargement hAS hAopen hK sdiff_subset hdis
  refine ⟨B,t,hB,hBS,hAB,?_,hBopen,hBc⟩
  intro x hx
  by_contra hn
  exact disjoint_left.mp hBK hx ⟨hBS hx,hn⟩

end Set
