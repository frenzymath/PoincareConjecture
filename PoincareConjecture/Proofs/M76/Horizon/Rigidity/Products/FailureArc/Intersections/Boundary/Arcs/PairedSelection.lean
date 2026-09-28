import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Arcs.FamilySelection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Arcs.Models
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.ComponentMatching
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.ComponentComplement

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_paired_returning_cut_disks
    {X : Type*} {H T : Set P2} {f g : P2 → X}
    (hH : IsFinitePLBallPair P2 H (frontier H))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hHT : H ⊆ interior T)
    (C : SurfaceIntersectionComponents (T \ interior H) (T \ interior H) f g
      (frontier H ∪ frontier T))
    (D : SurfaceIntersectionComponents (T \ interior H) (T \ interior H) g f
      (frontier H ∪ frontier T))
    (hrims : ∀ x ∈ T \ interior H, ∀ y ∈ T \ interior H, f x = g y →
      (x ∈ frontier H ∪ frontier T ↔ y ∈ frontier H ∪ frontier T))
    (hprotected : ∀ x ∈ T \ interior H, ∀ y ∈ T \ interior H, f x = g y →
      (x ∈ frontier H ↔ y ∈ frontier H))
    (a : P2) (hfirst : ((T \ interior H) ∩ g ⁻¹' (f '' (T \ interior H))) ∩ frontier H = {a})
    (hboundary : ∀ x : ((T \ interior H) ∩ g ⁻¹' (f '' (T \ interior H)) : Set P2),
      ∃ y : ((T \ interior H) ∩ g ⁻¹' (f '' (T \ interior H)) : Set P2),
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : P2) ∈ frontier H ∪ frontier T)
    (hreturn : ∃ i, Disjoint (C.pieces i) (frontier H)) :
    ∃ i j, ∃ D₀ E₀ U₀ V₀ D₁ E₁ U₁ V₁ : Set P2,
      IsFinitePLBallPair P2 D₀ (U₀ ∪ D.pieces j) ∧
      IsFinitePLBallPair P2 E₀ (D.pieces j ∪ V₀) ∧
      IsFinitePLBallPair ℝ U₀ (U₀ ∩ D.pieces j) ∧
      D₀ ∪ E₀ = T ∧ D₀ ∩ E₀ = D.pieces j ∧
      D₀ ∩ frontier T = U₀ ∧ E₀ ∩ frontier T = V₀ ∧
      Disjoint D₀ H ∧ D₀ ⊆ T \ H ∧
      IsFinitePLBallPair P2 D₁ (U₁ ∪ C.pieces i) ∧
      IsFinitePLBallPair P2 E₁ (C.pieces i ∪ V₁) ∧
      D₁ ∪ E₁ = T ∧ D₁ ∩ E₁ = C.pieces i ∧ D₁ ∩ frontier T = U₁ ∧
      Disjoint D₁ H ∧ D₁ ⊆ T \ H ∧
      IsFinitePLBallPair ℝ (D.pieces j) (D.pieces j ∩ (frontier T ∪ frontier H)) ∧
      f '' D.pieces j = g '' C.pieces i ∧
      (∀ x ∈ D₁, g x ∈ f '' (T \ interior H) → x ∈ C.pieces i) ∧
      IsClosed (((T \ interior H) ∩ f ⁻¹' (g '' (T \ interior H))) \ D.pieces j) := by
  classical
  let := C.components_finite
  have hCsub (i) : C.pieces i ⊆ T \ interior H := fun x hx ↦
    (C.right_space.subset (C.cover.symm.subset (mem_iUnion.mpr ⟨i, hx⟩))).1
  have hDsub (j) : D.pieces j ⊆ T \ interior H := fun x hx ↦
    (D.right_space.subset (D.cover.symm.subset (mem_iUnion.mpr ⟨j, hx⟩))).1
  have hCcover : (⋃ i, C.pieces i) = (T \ interior H) ∩ g ⁻¹' (f '' (T \ interior H)) :=
    C.cover.symm.trans C.right_space
  have hmodels := C.ball_models_of_components_meet_rim hboundary
  obtain ⟨i, D₁, E₁, U₁, V₁, hD₁, hE₁, _, hcover₁, hcommon₁, hDU₁, _, _,
    hD₁H, hD₁T, htotal⟩ := exists_outermost_returning_disk_of_interval_family hH hT hHT
      C.pieces hCsub C.disjoint hmodels a (hCcover ▸ hfirst) hreturn
  obtain ⟨c, hc⟩ := C.exists_component_equiv D
  let j := c.symm i
  have hphysical : f '' D.pieces j = g '' C.pieces i := by
    rw [hc]
    simp only [j, c.apply_symm_apply]
  have hCiD : C.pieces i ⊆ D₁ := subset_union_right.trans hD₁.1
  have hCprotected : Disjoint (C.pieces i) (frontier H) :=
    hD₁H.mono hCiD hH.1
  have hDprotected : Disjoint (D.pieces j) (frontier H) := by
    refine disjoint_left.mpr fun x hx hxH ↦ ?_
    obtain ⟨y, hy, hyx⟩ := hphysical.subset ⟨x, hx, rfl⟩
    exact disjoint_left.mp hCprotected hy
      ((hprotected x (hDsub j hx) y (hCsub i hy) hyx.symm).mp hxH)
  have hDball : IsFinitePLBallPair ℝ (D.pieces j)
      (D.pieces j ∩ (frontier H ∪ frontier T)) := by
    rcases D.models j with hj | ⟨_, _, _, _, _, hnoRim⟩
    · exact hj
    · obtain ⟨u, v, _, huv⟩ := (hmodels i).exists_boundary_eq_pair
      have hu := huv.superset (show u ∈ ({u, v} : Set P2) from Or.inl rfl)
      obtain ⟨x, hx, hxu⟩ := hphysical.superset ⟨u, hu.1, rfl⟩
      exact (disjoint_left.mp hnoRim hx
        ((hrims x (hDsub j hx) u (hCsub i hu.1) hxu).mpr hu.2)).elim
  obtain ⟨u, v, huv, hends⟩ := hDball.exists_boundary_eq_pair
  have hu : u ∈ frontier T := by
    have hh := hends.superset (show u ∈ ({u, v} : Set P2) from Or.inl rfl)
    exact hh.2.resolve_left (fun hq ↦ disjoint_left.mp hDprotected hh.1 hq)
  have hv : v ∈ frontier T := by
    have hh := hends.superset (show v ∈ ({u, v} : Set P2) from Or.inr rfl)
    exact hh.2.resolve_left (fun hq ↦ disjoint_left.mp hDprotected hh.1 hq)
  have hproper : D.pieces j \ {u, v} ⊆ interior T := by
    rw [hT.interior_eq_sdiff_of_finrank_eq rfl]
    exact fun x hx ↦ ⟨(hDsub j hx.1).1,
      fun hq ↦ hx.2 (hends.subset ⟨hx.1, Or.inr hq⟩)⟩
  have hDH : Disjoint (D.pieces j) H := by
    refine disjoint_left.mpr fun x hx hxH ↦ ?_
    exact disjoint_left.mp hDprotected hx ⟨subset_closure hxH, (hDsub j hx).2⟩
  have hW : IsFinitePLBallPair ℝ (D.pieces j) {u, v} := hends ▸ hDball
  obtain ⟨D₀, E₀, U₀, V₀, hU₀, _, _, _, hD₀, hE₀, hcover₀, hcommon₀,
    hDU₀, hEV₀, _, hD₀H, hD₀T, _⟩ :=
    exists_returning_arc_disk hH hT hHT hW huv hu hv hproper hDH
  have hUcontact : U₀ ∩ D.pieces j = {u, v} := by
    apply Subset.antisymm
    · exact fun x hx ↦ hends.subset ⟨hx.2, Or.inr (hDU₀.superset hx.1).2⟩
    · exact fun x hx ↦ ⟨hU₀.1 hx, hW.1 hx⟩
  refine ⟨i, j, D₀, E₀, U₀, V₀, D₁, E₁, U₁, V₁, hD₀, hE₀, hUcontact.symm ▸ hU₀,
    hcover₀, hcommon₀, hDU₀, hEV₀, hD₀H, hD₀T, hD₁, hE₁, hcover₁, hcommon₁,
    hDU₁, hD₁H, hD₁T, ?_, hphysical, ?_, D.isClosed_complement_piece j⟩
  · simpa only [union_comm] using hDball
  · intro x hx hgx
    exact htotal.subset ⟨hx, hCcover.superset ⟨⟨(hD₁T hx).1,
      fun hin ↦ (hD₁T hx).2 (interior_subset hin)⟩, hgx⟩⟩

end PoincareConjecture.M76.Dehn.Annuli
