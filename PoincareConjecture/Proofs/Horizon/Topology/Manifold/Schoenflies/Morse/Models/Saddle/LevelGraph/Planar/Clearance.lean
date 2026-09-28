import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates
import Mathlib.Geometry.Manifold.SmoothEmbedding



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1


def planarProjection {v : E3} (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (y : E3) : E2 :=
  J.symm ((Real ∙ v)ᗮ.orthogonalProjectionOnto y)

@[simp] theorem planarProjection_graph {v : E3}
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (x : E2) (t : Real) :
    planarProjection J ((J x : E3) + t • v) = x := by
  simp [planarProjection]

private theorem graph_height {v : E3} (hv : ‖v‖ = 1)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (x : E2) (t : Real) :
    inner Real v ((J x : E3) + t • v) = t := by
  have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J x).property
  simp [inner_add_right, inner_smul_right, h, hv]

private theorem projection_height_decomposition {v : E3} (hv : ‖v‖ = 1)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (y : E3) :
    y = (J (planarProjection J y) : E3) + inner Real v y • v := by
  simpa [planarProjection, add_comm] using
    ((Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply y).symm




theorem exists_planar_clearance
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (e : OpenPartialHomeomorph E2 S2) (hep : e 0 = p)
    {a : Real} (ha : 0 < a) (has : closedBall (0 : E2) a ⊆ e.source)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y)
    (hgraph : ∀ x ∈ closedBall (0 : E2) a,
      D (f (e x)) = (J x : E3) +
        (inner Real v (f p) - x 0 ^ 2 + x 1 ^ 2) • v)
    {ε : Real} (hε : 0 < ε) :
    ∃ r : Real, 0 < r ∧ r < ε ∧ closedSquare r ⊆ ball (0 : E2) a ∧
      (∀ q : S2, inner Real v (f q) = inner Real v (f p) ->
        (planarProjection J (D (f q)) ∈ closedSquare r ↔ q ∈ e '' closedSquare r)) ∧
      (∀ q : S2, inner Real v (f q) = inner Real v (f p) ->
        (planarProjection J (D (f q)) ∈ openSquare r ↔ q ∈ e '' openSquare r)) ∧
      {q : S2 | inner Real v (f q) = inner Real v (f p) ∧
        planarProjection J (D (f q)) ∈ closedSquare r \ openSquare r} =
          range (fun i : Fin 2 × Fin 2 => e (contact r i)) ∧
      Function.Injective (fun i : Fin 2 × Fin 2 => e (contact r i)) := by
  let F : S2 -> E3 := D ∘ f
  let c := inner Real v (f p)
  have hFi : Topology.IsEmbedding F := D.toHomeomorph.isEmbedding.comp hf.isEmbedding
  have hU : IsOpen (e '' ball (0 : E2) a) :=
    e.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans has)
  obtain ⟨V, hV, hFV⟩ := hFi.isInducing.isOpen_iff.mp hU
  have hpV : F p ∈ V := by
    change p ∈ F ⁻¹' V
    rw [hFV]
    exact ⟨0, mem_ball_self ha, hep⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  let r := min ε (min a δ) / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by
    have := min_le_left ε (min a δ)
    dsimp [r]
    linarith
  have hra : 2 * r < a := by
    have := (min_le_right ε (min a δ)).trans (min_le_left a δ)
    dsimp [r]
    linarith
  have hrδ : 2 * r < δ := by
    have := (min_le_right ε (min a δ)).trans (min_le_right a δ)
    dsimp [r]
    linarith
  have hrs : closedSquare r ⊆ ball (0 : E2) a := by
    intro x hx
    exact (closedSquare_subset_closedBall hr.le hx).trans_lt hra
  have hrclosed : closedSquare r ⊆ closedBall (0 : E2) a := hrs.trans ball_subset_closedBall
  have hproj (x : E2) (hx : x ∈ closedBall (0 : E2) a) :
      planarProjection J (F (e x)) = x := by
    change planarProjection J (D (f (e x))) = x
    rw [hgraph x hx, planarProjection_graph]
  have hcenter : F p = c • v := by
    simpa [F, hep, c] using hgraph 0 (mem_closedBall_self ha.le)
  have hlocal (q : S2) (hq : inner Real v (f q) = c)
      (hπ : planarProjection J (F q) ∈ closedSquare r) :
      q ∈ e '' ball (0 : E2) a := by
    have hdec := projection_height_decomposition hv J (F q)
    have hh : inner Real v (F q) = c := (hDheight (f q)).trans hq
    rw [hh] at hdec
    have hdist : dist (F q) (F p) = ‖planarProjection J (F q)‖ := by
      calc
        dist (F q) (F p) = ‖(J (planarProjection J (F q)) : E3)‖ := by
          rw [hcenter]
          nth_rw 1 [hdec]
          rw [dist_eq_norm, add_sub_cancel_right]
        _ = ‖planarProjection J (F q)‖ := J.norm_map _
    have hnorm := mem_closedBall_zero_iff.mp (closedSquare_subset_closedBall hr.le hπ)
    have hqV : F q ∈ V := hδV (by
      rw [mem_ball, hdist]
      exact hnorm.trans_lt hrδ)
    change q ∈ F ⁻¹' V at hqV
    rwa [hFV] at hqV
  have hclosed (q : S2) (hq : inner Real v (f q) = c) :
      planarProjection J (F q) ∈ closedSquare r ↔ q ∈ e '' closedSquare r := by
    constructor
    · intro hπ
      obtain ⟨x, hx, rfl⟩ := hlocal q hq hπ
      exact ⟨x, (hproj x (ball_subset_closedBall hx)) ▸ hπ, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rwa [hproj x (hrclosed hx)]
  have hopen (q : S2) (hq : inner Real v (f q) = c) :
      planarProjection J (F q) ∈ openSquare r ↔ q ∈ e '' openSquare r := by
    constructor
    · intro hπ
      obtain ⟨x, hx, rfl⟩ := hlocal q hq (openSquare_subset_closedSquare r hπ)
      exact ⟨x, (hproj x (ball_subset_closedBall hx)) ▸ hπ, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rwa [hproj x (hrclosed (openSquare_subset_closedSquare r hx))]
  refine ⟨r, hr, hrε, hrs, hclosed, hopen, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨hq, hπ, hπout⟩
      obtain ⟨x, hx, rfl⟩ := (hclosed q hq).mp hπ
      have hxout : x ∉ openSquare r := by
        change planarProjection J (F (e x)) ∉ openSquare r at hπout
        simpa only [hproj x (hrclosed hx)] using hπout
      have hxheight : x 0 ^ 2 = x 1 ^ 2 := by
        have hh := congrArg (inner Real v) (hgraph x (hrclosed hx))
        rw [hDheight, graph_height hv] at hh
        linarith
      have hxcontact : x ∈ range (contact r) :=
        (square_boundary_zeroLevel hr) ▸ (show x ∈
          (closedSquare r \ openSquare r) ∩ {x : E2 | x 0 ^ 2 = x 1 ^ 2} from
          ⟨⟨hx, hxout⟩, hxheight⟩)
      obtain ⟨i, rfl⟩ := hxcontact
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      have hi := contact_mem hr i
      have hh := congrArg (inner Real v) (hgraph (contact r i) (hrclosed hi.1.1))
      rw [hDheight, graph_height hv] at hh
      refine ⟨?_, ?_⟩
      · linarith [hi.2]
      · change planarProjection J (F (e (contact r i))) ∈ _
        rw [hproj _ (hrclosed hi.1.1)]
        exact hi.1
  · intro i j hij
    apply contact_injective hr
    exact e.injOn (has (hrclosed (contact_mem hr i).1.1))
      (has (hrclosed (contact_mem hr j).1.1)) hij

end Poincare.Manifold.Schoenflies.SaddleLevel
