import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Vertices.BaseCharts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ConvexAffineSectionBallPair



set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (T : CoorientedSurfaceStars E)




theorem frontier_vertex_ballPair (p : (T.marked 2).vertices)
    (hpfront : (p : E) ∈ (T.marked 1).space) :
    IsFinitePLBallPair P2 ((T.vertexBlock p).space ∩ (T.marked 1).space)
      (((T.vertexBlock p).space ∩ (T.marked 1).space) ∩
        ((T.vertexBlock p).link p).space) := by
  let N := T.vertexBlock p
  obtain ⟨boundary, C, L, G, hC, hcv, hz, hrep, hG, hbp, hlink, _, _, _, hfront⟩ :=
    T.exists_vertex_base_convex_chart p
  have htrue := hbp.mpr hpfront
  have hboundary (x : N.space) : (x : E) ∈ (T.marked 1).space ↔
      (G x : C3).1.1 = 0 := by
    simpa only [htrue, true_and] using hfront x
  let a : P2 →L[ℝ] C3 :=
    { toFun := fun z => ((0, z.1), z.2)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp
      cont := by fun_prop }
  let r : C3 →L[ℝ] P2 :=
    { toFun := fun z => (z.1.2, z.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  have harange : range a = {x : C3 | x.1.1 = 0} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      rfl
    · intro hx
      exact ⟨(x.1.2, x.2), Prod.ext (Prod.ext hx.symm rfl) rfl⟩
  have hsection := isFinitePLBallPair_convex_affine_section hC hcv hz L hrep
    a.toContinuousAffineMap r.toContinuousAffineMap (fun _ => rfl) rfl
  change IsFinitePLBallPair P2 (C ∩ range a) (frontier C ∩ range a) at hsection
  rw [harange] at hsection
  obtain ⟨g, hg, hgval⟩ := hG.symm
  have hginj : InjOn g C := by
    intro x hx y hy hxy
    have he : G.symm ⟨x, hx⟩ = G.symm ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hgval] using hxy
    exact congrArg Subtype.val (G.symm.injective he)
  have himage (U : Set C3) (S : Set (E))
      (hUC : U ⊆ C) (hSN : S ⊆ N.space)
      (hiff : ∀ x : N.space, (G x : C3) ∈ U ↔ (x : E) ∈ S) :
      g '' U = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h : (G.symm ⟨y, hUC hy⟩ : E) ∈ S := (hiff _).mp (by
        simpa only [G.apply_symm_apply] using hy)
      rwa [hgval] at h
    · intro hx
      refine ⟨G ⟨x, hSN hx⟩, (hiff _).mpr hx, ?_⟩
      rw [← hgval, G.symm_apply_apply]
  have hbody : g '' (C ∩ {x : C3 | x.1.1 = 0}) = N.space ∩ (T.marked 1).space := by
    apply himage _ _ inter_subset_left inter_subset_left
    intro x
    exact ⟨fun hx => ⟨x.property, (hboundary x).mpr hx.2⟩,
      fun hx => ⟨(G x).property, (hboundary x).mp hx.2⟩⟩
  have hrim : g '' (frontier C ∩ {x : C3 | x.1.1 = 0}) =
      (N.space ∩ (T.marked 1).space) ∩ (N.link p).space := by
    apply himage _ _ (fun _ hx => hC.isClosed.frontier_subset hx.1)
      (inter_subset_left.trans inter_subset_left)
    intro x
    exact ⟨fun hx => ⟨⟨x.property, (hboundary x).mpr hx.2⟩, (hlink x).mpr hx.1⟩,
      fun hx => ⟨(hlink x).mp hx.2, (hboundary x).mp hx.1.2⟩⟩
  have hball := hsection.image_of_subset hg inter_subset_left hginj
  simpa only [hbody, hrim] using hball

end Geometry.SimplicialComplex.CoorientedSurfaceStars

