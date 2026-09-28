import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceRegions
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall












set_option autoImplicit false

open Set Metric Geometry

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "R" => sphere (0 : V2) 1

private theorem source_copy_image {A B : Set V2} (H : A ≃ₜ B)
    {j : V2 → V2} (hj : ∀ x : A, (H x : V2) = j x) : j '' A = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hj ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  · intro hy
    refine ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property, ?_⟩
    rw [← hj, H.apply_symm_apply]

private theorem source_copy_embedding {A B : Set V2} (H : A ≃ₜ B)
    {j : V2 → V2} (hj : ∀ x : A, (H x : V2) = j x) :
    Topology.IsEmbedding (fun x : A => j x) := by
  have heq : (fun x : A => j x) = fun x : A => (H x : V2) :=
    funext fun x => (hj x).symm
  rw [heq]
  exact Topology.IsEmbedding.subtypeVal.comp H.isEmbedding





theorem exists_disjoint_circle_source_disk {m n : ℕ}
    (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPsq : P.boundary ℝ ⊆ ball 0 1)
    (hQsq : Q.boundary ℝ ⊆ ball 0 1)
    (hdisj : Disjoint (closure P.inside) (closure Q.inside))
    (eb : P.boundary ℝ ≃ₜ Q.boundary ℝ) (heb : eb.IsFinitePL) :
    ∃ (H : closure P.inside ≃ₜ closure Q.inside) (jP jQ : V2 → V2),
      H.IsFinitePL ∧
      FinitePiecewiseAffineOn jP (closure P.inside) ∧
      FinitePiecewiseAffineOn jQ (closure Q.inside) ∧
      (∀ x : closure P.inside, jP x = (H x : V2)) ∧
      (∀ x : closure Q.inside, jQ x = (H.symm x : V2)) ∧
      Topology.IsEmbedding (fun x : closure P.inside => jP x) ∧
      Topology.IsEmbedding (fun x : closure Q.inside => jQ x) ∧
      jP '' closure P.inside = closure Q.inside ∧
      jQ '' closure Q.inside = closure P.inside ∧
      (∀ x ∈ closure P.inside, jQ (jP x) = x) ∧
      (∀ x ∈ closure Q.inside, jP (jQ x) = x) ∧
      (∀ x : P.boundary ℝ, jP x = (eb x : V2)) ∧
      (∀ x : Q.boundary ℝ, jQ x = (eb.symm x : V2)) ∧
      (∀ x ∈ closure P.inside, ∀ y ∈ D \ (P.inside ∪ Q.inside),
        jP x = y ↔ ∃ hx : x ∈ P.boundary ℝ, (eb ⟨x, hx⟩ : V2) = y) ∧
      (∀ x ∈ closure Q.inside, ∀ y ∈ D \ (P.inside ∪ Q.inside),
        jQ x = y ↔ ∃ hx : x ∈ Q.boundary ℝ, (eb.symm ⟨x, hx⟩ : V2) = y) ∧
      Disjoint (jP '' closure P.inside) (jQ '' closure Q.inside) ∧
      jP '' closure P.inside ∩ (D \ (P.inside ∪ Q.inside)) = Q.boundary ℝ ∧
      jQ '' closure Q.inside ∩ (D \ (P.inside ∪ Q.inside)) = P.boundary ℝ ∧
      ((jP '' closure P.inside) ∪ (jQ '' closure Q.inside)) ∪
        (D \ (P.inside ∪ Q.inside)) = D ∧
      IsFinitePLBallPair V2 (((jP '' closure P.inside) ∪ (jQ '' closure Q.inside)) ∪
        (D \ (P.inside ∪ Q.inside))) R ∧
      R ⊆ D \ (P.inside ∪ Q.inside) ∧
      Disjoint ((jP '' closure P.inside) ∪ (jQ '' closure Q.inside)) R ∧
      (closure P.inside ∩ (D \ (P.inside ∪ Q.inside)) = P.boundary ℝ) ∧
      (closure Q.inside ∩ (D \ (P.inside ∪ Q.inside)) = Q.boundary ℝ) := by
  obtain ⟨hdP, hiP, hfP, hsP⟩ := polygon_source_region P
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hP hinjP (convex_ball _ _) hPsq
  obtain ⟨hdQ, hiQ, hfQ, hsQ⟩ := polygon_source_region Q
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hQ hinjQ (convex_ball _ _) hQsq
  obtain ⟨H, hH, hHb, hHmem⟩ := hdP.exists_extension hdQ eb heb
  obtain ⟨jP, hjP, hHP⟩ := hH
  obtain ⟨jQ, hjQ, hHQ⟩ := (show H.IsFinitePL from ⟨jP, hjP, hHP⟩).symm
  have himP := source_copy_image H hHP
  have himQ := source_copy_image H.symm hHQ
  have hbP (x : P.boundary ℝ) : jP x = (eb x : V2) := by
    have h := congrArg Subtype.val (hHb x)
    rwa [hHP] at h
  have hbQ (x : Q.boundary ℝ) : jQ x = (eb.symm x : V2) := by
    have h := hHb (eb.symm x)
    have h' : H ⟨eb.symm x, hdP.1 (eb.symm x).property⟩ = ⟨x, hdQ.1 x.property⟩ := by
      simpa only [eb.apply_symm_apply] using h
    have h'' := congrArg (fun y => (H.symm y : V2)) h'
    simpa only [H.symm_apply_apply, hHQ] using h''.symm
  have hPD : closure P.inside ⊆ D := hsP.trans ball_subset_closedBall
  have hQD : closure Q.inside ⊆ D := hsQ.trans ball_subset_closedBall
  have hcP : closure P.inside ∩ (D \ (P.inside ∪ Q.inside)) = P.boundary ℝ := by
    rw [← hfP, frontier, isClosed_closure.closure_eq, hiP]
    ext x
    constructor
    · exact fun hx => ⟨hx.1, fun h => hx.2.2 (Or.inl h)⟩
    · rintro ⟨hx, hxi⟩
      refine ⟨hx, hPD hx, ?_⟩
      rintro (h | h)
      · exact hxi h
      · exact Set.disjoint_left.mp hdisj hx (subset_closure h)
  have hcQ : closure Q.inside ∩ (D \ (P.inside ∪ Q.inside)) = Q.boundary ℝ := by
    rw [← hfQ, frontier, isClosed_closure.closure_eq, hiQ]
    ext x
    constructor
    · exact fun hx => ⟨hx.1, fun h => hx.2.2 (Or.inr h)⟩
    · rintro ⟨hx, hxi⟩
      refine ⟨hx, hQD hx, ?_⟩
      rintro (h | h)
      · exact Set.disjoint_left.mp hdisj (subset_closure h) hx
      · exact hxi h
  have hcover : (jP '' closure P.inside ∪ jQ '' closure Q.inside) ∪
      (D \ (P.inside ∪ Q.inside)) = D := by
    rw [himP, himQ]
    apply Subset.antisymm (union_subset (union_subset hQD hPD) sdiff_subset)
    intro x hx
    by_cases hp : x ∈ P.inside
    · exact Or.inl (Or.inr (subset_closure hp))
    by_cases hq : x ∈ Q.inside
    · exact Or.inl (Or.inl (subset_closure hq))
    exact Or.inr ⟨hx, fun h => h.elim hp hq⟩
  refine ⟨H, jP, jQ, ⟨jP, hjP, hHP⟩, hjP, hjQ,
    fun x => (hHP x).symm, fun x => (hHQ x).symm,
    source_copy_embedding H hHP, source_copy_embedding H.symm hHQ,
    himP, himQ, ?_, ?_, hbP, hbQ, ?_, ?_, ?_, ?_, ?_, hcover, ?_, ?_, ?_, hcP, hcQ⟩
  · intro x hx
    rw [← hHP ⟨x, hx⟩, ← hHQ, H.symm_apply_apply]
  · intro x hx
    rw [← hHQ ⟨x, hx⟩, ← hHP, H.apply_symm_apply]
  · intro x hx y hy
    constructor
    · intro heq
      have hxb : x ∈ P.boundary ℝ := (hHmem ⟨x, hx⟩).mpr (by
        rw [hHP, heq]
        exact hcQ ▸ ⟨heq ▸ (himP ▸ mem_image_of_mem jP hx), hy⟩)
      exact ⟨hxb, (hbP ⟨x, hxb⟩).symm.trans heq⟩
    · rintro ⟨hxb, heq⟩
      exact (hbP ⟨x, hxb⟩).trans heq
  · intro x hx y hy
    constructor
    · intro heq
      have hyb : y ∈ P.boundary ℝ :=
        hcP ▸ ⟨heq ▸ (himQ ▸ mem_image_of_mem jQ hx), hy⟩
      have hxb : x ∈ Q.boundary ℝ := by
        have h := (hHmem (H.symm ⟨x, hx⟩)).mp (by rwa [hHQ, heq])
        simpa only [H.apply_symm_apply] using h
      exact ⟨hxb, (hbQ ⟨x, hxb⟩).symm.trans heq⟩
    · rintro ⟨hxb, heq⟩
      exact (hbQ ⟨x, hxb⟩).trans heq
  · rw [himP, himQ]
    exact hdisj.symm
  · rwa [himP]
  · rwa [himQ]
  · rw [hcover]
    exact isFinitePLBallPair_unit_cube
  · intro x hx
    refine ⟨sphere_subset_closedBall hx, ?_⟩
    rintro (hp | hq)
    · exact (ne_of_lt (hsP (subset_closure hp))) hx
    · exact (ne_of_lt (hsQ (subset_closure hq))) hx
  · rw [himP, himQ]
    apply Set.disjoint_left.mpr
    rintro x (hq | hp) hx
    · exact (ne_of_lt (hsQ hq)) hx
    · exact (ne_of_lt (hsP hp)) hx

end Dehn
