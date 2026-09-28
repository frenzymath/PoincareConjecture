import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.AnnulusSides










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem mem_closure_surface_interior_of_crossing_frontier
    {X : Type*} [TopologicalSpace X] {S R : Set X} {x : X}
    (B : OpenPartialHomeomorph X C3) (hx : x ∈ B.source) (hBx : B x = 0)
    (hS : ∀ y ∈ B.source, y ∈ S ↔ (B y).2 = 0)
    (hfront : ∀ y ∈ B.source, y ∈ frontier R ↔ (B y).1.1 = 0)
    (hreg : x ∈ closure (interior R)) : x ∈ closure (S ∩ interior R) := by
  apply _root_.mem_closure_iff.mpr
  intro O hO hxO
  have hW : IsOpen (B.target ∩ B.symm ⁻¹' O) := B.symm.isOpen_inter_preimage hO
  have hzero : (0 : C3) ∈ B.target ∩ B.symm ⁻¹' O := by
    refine ⟨hBx ▸ B.map_source hx,?_⟩
    change B.symm 0 ∈ O
    rw [←hBx,B.left_inv hx]
    exact hxO
  obtain ⟨δ,hδ,hδW⟩ := Metric.isOpen_iff.mp hW 0 hzero
  have hδtarget : ball (0 : C3) δ ⊆ B.target := fun z hz => (hδW hz).1
  have hU : IsOpen (B.symm '' ball (0 : C3) δ) :=
    B.symm.isOpen_image_of_subset_source isOpen_ball hδtarget
  have hxU : x ∈ B.symm '' ball (0 : C3) δ :=
    ⟨0,mem_ball_self hδ,by rw [←hBx,B.left_inv hx]⟩
  obtain ⟨y,⟨v,hv,rfl⟩,hyR⟩ := _root_.mem_closure_iff.mp hreg _ hU hxU
  have hvB := hδtarget hv
  have hvfirst : v.1.1 ≠ 0 := by
    intro h
    have hfr := (hfront (B.symm v) (B.map_target hvB)).mpr (by rw [B.right_inv hvB]; exact h)
    exact hfr.2 hyR
  let A : C3 →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.fst ℝ P2 ℝ)
  let Z := ball (0 : C3) δ ∩ {z : C3 | 0 < v.1.1 * A z}
  have hZcv : Convex ℝ Z := (convex_ball _ _).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage (v.1.1 • A.toLinearMap))
  have hvZ : v ∈ Z := ⟨hv,mul_self_pos.mpr hvfirst⟩
  have hZB : Z ⊆ B.target := fun z hz => hδtarget hz.1
  have hZconn : IsPreconnected (B.symm '' Z) :=
    hZcv.isPreconnected.image _ (B.continuousOn_symm.mono hZB)
  have hZfront : Disjoint (B.symm '' Z) (frontier R) := by
    apply disjoint_left.mpr
    rintro z ⟨w,hw,rfl⟩ hwfront
    have h := (hfront _ (B.map_target (hZB hw))).mp hwfront
    rw [B.right_inv (hZB hw)] at h
    have hz := hw.2
    change 0 < v.1.1 * w.1.1 at hz
    rw [h,mul_zero] at hz
    exact lt_irrefl _ hz
  have hZin : B.symm '' Z ⊆ interior R :=
    hZconn.subset_interior_of_avoids_frontier hZfront ⟨B.symm v,⟨v,hvZ,rfl⟩,hyR⟩
  let q : C3 := ((v.1.1,0),0)
  have hqnorm : ‖q‖ = |v.1.1| := by simp [q,Prod.norm_def]
  have hnorm : |v.1.1| ≤ ‖v‖ :=
    (le_max_left |v.1.1| |v.1.2|).trans (le_max_left ‖v.1‖ ‖v.2‖)
  have hqball : q ∈ ball (0 : C3) δ := by
    rw [mem_ball_zero_iff,hqnorm]
    exact hnorm.trans_lt (mem_ball_zero_iff.mp hv)
  have hqZ : q ∈ Z := ⟨hqball,mul_self_pos.mpr hvfirst⟩
  refine ⟨B.symm q,(hδW hqball).2,?_,hZin ⟨q,hqZ,rfl⟩⟩
  exact (hS _ (B.map_target (hδtarget hqball))).mpr (by rw [B.right_inv (hδtarget hqball)])

end PoincareConjecture.M76
