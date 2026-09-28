import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Cofaces
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VerticalTriangleGerm
import PoincareConjecture.Proofs.M76.Mathlib.HeightPlaneAffineCoordinates

set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

set_option maxHeartbeats 800000 in
theorem exists_boundary_carrier_affine_coordinates
    (J B K : SimplicialComplex ℝ V3) (c : V3 ≃L[ℝ] C3)
    (hK : K.faces.Finite) (hKB : K ≤ B)
    (hKcard : ∀ face ∈ K.faces, face.card ≤ 2)
    (hKzero : K.space = B.space ∩ {z | (c z).1.1 = 0})
    (hvertices : ∀ v ∈ K.vertices, (c v).2 ≠ 0)
    (hBpositive : ∀ z ∈ B.space, 0 ≤ (c z).1.1)
    (hcofaces : ∀ edge ∈ K.faces, edge.card = 2 → ∀ z,
      z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)) →
      z ∈ interior J.space →
      ∃ face ∈ B.faces, edge ⊆ face ∧ face.card = 3 ∧
        (∀ other ∈ B.faces, edge ⊆ other → other ⊆ face) ∧
        ∀ O : Set V3, IsOpen O → z ∈ O →
          ∃ V : Set V3, IsOpen V ∧ z ∈ V ∧ V ⊆ O ∩ interior J.space ∧
            ∀ x ∈ V, x ∈ B.space ↔ x ∈ convexHull ℝ (face : Set V3))
    {z : V3} (hzK : z ∈ K.space) (hzJ : z ∈ interior J.space) (hz0 : (c z).2 = 0)
    (O : Set V3) (hO : IsOpen O) (hzO : z ∈ O) :
    ∃ (A : V3 ≃ᴬ[ℝ] C3) (N : Set V3), IsOpen N ∧ z ∈ N ∧
      N ⊆ O ∩ interior J.space ∧ A z = 0 ∧
      (∀ x, (A x).1.2 = (c x).1.1) ∧ (∀ x, (A x).2 = (c x).2) ∧
      ∀ x ∈ N, x ∈ B.space ↔ 0 ≤ (c x).1.1 ∧ (A x).1.1 = 0 := by
  classical
  let height : V3 →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap)
  let ell : V3 →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  have hzh : height z = 0 := (hKzero.subset hzK).2
  have hze : ell z = 0 := hz0
  obtain ⟨edge, hedge, hzeint⟩ := K.exists_face_intrinsicInterior_of_finite hK hzK
  have he2 : edge.card = 2 := by
    have hlo := Finset.card_pos.mpr (K.nonempty_of_mem_faces hedge)
    have hhi := hKcard edge hedge
    by_contra hn
    have hone : edge.card = 1 := by omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
    have hzv : z = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        intrinsicInterior_subset hzeint
    exact hvertices v hedge (hzv ▸ hz0)
  obtain ⟨face, hface, hef, hf3, _hexhaust, hgerm⟩ :=
    hcofaces edge hedge he2 z hzeint hzJ
  obtain ⟨u, v, _huv, heuv, hu, hv⟩ :
      ∃ u v : V3, u ≠ v ∧ edge = {u, v} ∧ ell u < 0 ∧ 0 < ell v := by
    obtain ⟨u, v, huv, heuv⟩ := Finset.card_eq_two.mp he2
    have huK : u ∈ K.vertices := K.face_subset_vertices hedge
      (heuv.symm ▸ Finset.mem_insert_self _ _)
    have hvK : v ∈ K.vertices := K.face_subset_vertices hedge
      (heuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    obtain ⟨wt, hwt, _, hval⟩ :=
      (K.indep hedge).exists_positive_weights_of_mem_intrinsicInterior hzeint
    have hwu := hwt u (heuv.symm ▸ Finset.mem_insert_self _ _)
    have hwv := hwt v (heuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hbalance : wt u * ell u + wt v * ell v = 0 := by
      simpa only [heuv, Finset.sum_pair huv, map_add, map_smul, smul_eq_mul, hze]
        using congrArg ell hval
    rcases lt_or_gt_of_ne (show ell u ≠ 0 from hvertices u huK) with hu | hu
    · have hv : 0 < ell v := by
        by_contra hn
        have h₁ := mul_neg_of_pos_of_neg hwu hu
        have h₂ := mul_nonpos_of_nonneg_of_nonpos hwv.le (not_lt.mp hn)
        linarith
      exact ⟨u, v, huv, heuv, hu, hv⟩
    · have hv : ell v < 0 := by
        by_contra hn
        have h₁ := mul_pos hwu hu
        have h₂ := mul_nonneg hwv.le (not_lt.mp hn)
        linarith
      exact ⟨v, u, huv.symm, heuv.trans (Finset.pair_comm _ _), hv, hu⟩
  have hue : u ∈ edge := heuv.symm ▸ Finset.mem_insert_self _ _
  have hve : v ∈ edge := heuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have huf : u ∈ face := hef hue
  have hvf : v ∈ face := hef hve
  have huh : height u = 0 := (hKzero.subset (K.subset_space hedge hue)).2
  have hvh : height v = 0 := (hKzero.subset (K.subset_space hedge hve)).2
  obtain ⟨w₃, _hw₃e, hw₃face⟩ := Finset.exists_eq_insert_iff.mpr ⟨hef, by omega⟩
  have hw₃f : w₃ ∈ face := hw₃face ▸ Finset.mem_insert_self _ _
  have hw₃h : 0 < height w₃ := by
    have hnonneg := hBpositive w₃ (B.subset_space hface hw₃f)
    apply lt_of_le_of_ne hnonneg
    intro heq
    have hzeroHull : convexHull ℝ (face : Set V3) ⊆ {x | height x = 0} := by
      apply convexHull_min ?_ ((convex_singleton (0 : ℝ)).linear_preimage height.toLinearMap)
      intro x hx
      rw [← hw₃face, heuv] at hx
      change x ∈ (insert w₃ ({u, v} : Finset V3)) at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact heq.symm
      · exact huh
      · exact hvh
    have hne : (convexHull ℝ (face : Set V3)).Nonempty :=
      convexHull_nonempty_iff.mpr (B.nonempty_of_mem_faces hface).to_set
    obtain ⟨x, hx⟩ := hne.intrinsicInterior (convex_convexHull ℝ _)
    have hxK : x ∈ K.space := hKzero.symm.subset
      ⟨B.convexHull_subset_space hface (intrinsicInterior_subset hx),
        hzeroHull (intrinsicInterior_subset hx)⟩
    obtain ⟨other, hother, hxother⟩ := mem_space_iff.mp hxK
    have hsub := B.subset_of_mem_intrinsicInterior_face hface (hKB hother) hx hxother
    have hlo := Finset.card_le_card hsub
    have hhi := hKcard other hother
    omega
  let plane := affineSpan ℝ (face : Set V3)
  have hzplane : z ∈ plane := convexHull_subset_affineSpan (s := (face : Set V3))
    (convexHull_mono hef (intrinsicInterior_subset hzeint))
  have huplane : u ∈ plane := subset_affineSpan ℝ _ huf
  have hvplane : v ∈ plane := subset_affineSpan ℝ _ hvf
  have hwplane : w₃ ∈ plane := subset_affineSpan ℝ _ hw₃f
  have hdim : Module.finrank ℝ plane.direction = 2 :=
    B.finrank_faceDirection_of_card hface hf3
  obtain ⟨F, hFzero, hFell', hFplane⟩ := plane.exists_centered_height_plane_coordinates
    (by simp) hdim ell.toLinearMap.toAffineMap
    ⟨u, huplane, z, hzplane, by change ell u ≠ ell z; rw [hze]; exact hu.ne⟩ hzplane
  have hFell (x : C3) : ell (F x) = x.1.1 := by
    have h := hFell' x
    change ell (F x) = ell z + x.1.1 at h
    simpa only [hze, zero_add] using h
  let ellH : C3 →ₗ[ℝ] ℝ := height.toLinearMap.comp F.toAffineEquiv.linear.toLinearMap
  have hHvalue (x : C3) : ellH x = height (F x) := by
    have hlin := F.toAffineEquiv.toAffineMap.linearMap_vsub x 0
    change F.toAffineEquiv.linear (x - 0) = F x - F 0 at hlin
    rw [sub_zero, hFzero] at hlin
    change height (F.toAffineEquiv.linear x) = height (F x)
    rw [hlin, map_sub, hzh, sub_zero]
  let α := ellH ((1, 0), 0)
  let β := ellH ((0, 1), 0)
  let γ := ellH ((0, 0), 1)
  have hlinear (x : C3) : ellH x = α * x.1.1 + β * x.1.2 + γ * x.2 := by
    have hx : x = x.1.1 • (((1, 0), 0) : C3) +
        x.1.2 • (((0, 1), 0) : C3) + x.2 • (((0, 0), 1) : C3) := by
      ext <;> simp
    conv_lhs => rw [hx]
    rw [map_add, map_add, map_smul, map_smul, map_smul]
    change x.1.1 * α + x.1.2 * β + x.2 * γ = _
    ring
  have hFuplane : (F.symm u).2 = 0 := (hFplane _).mp (by simpa using huplane)
  have hFwplane : (F.symm w₃).2 = 0 := (hFplane _).mp (by simpa using hwplane)
  have hFuell : (F.symm u).1.1 = ell u := by simpa using (hFell (F.symm u)).symm
  have hβ : β ≠ 0 := by
    intro hb₀
    have hu₀ : ellH (F.symm u) = 0 := by rw [hHvalue, F.apply_symm_apply, huh]
    have hαu : α * ell u = 0 := by
      simpa only [hlinear, hb₀, hFuplane, hFuell, zero_mul, mul_zero, add_zero] using hu₀
    have hα : α = 0 := (mul_eq_zero.mp hαu).resolve_right hu.ne
    have hw₀ : height w₃ = 0 := calc
      height w₃ = ellH (F.symm w₃) := by
        rw [hHvalue, F.apply_symm_apply]
      _ = 0 := by rw [hlinear, hα, hb₀, hFwplane]; ring
    exact hw₃h.ne' hw₀
  let X := (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let Z := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  let L := (Z.prod ellH).prod X
  let eL : C3 ≃ₗ[ℝ] C3 :=
    { L with
      invFun := fun x => ((x.2, (x.1.2 - α * x.2 - γ * x.1.1) / β), x.1.1)
      left_inv := by
        intro x
        change ((x.1.1, (ellH x - α * x.1.1 - γ * x.2) / β), x.2) = x
        rw [hlinear]
        ext <;> dsimp
        field_simp [hβ]
        ring
      right_inv := by
        intro x
        change ((x.1.1, ellH ((x.2,
          (x.1.2 - α * x.2 - γ * x.1.1) / β), x.1.1)), x.2) = x
        rw [hlinear]
        ext <;> dsimp
        field_simp [hβ]
        ring }
  let A := F.symm.trans eL.toAffineEquiv.toContinuousAffineEquiv
  have hAzero : A z = 0 := by
    change eL (F.symm z) = 0
    rw [← hFzero, F.symm_apply_apply, map_zero]
  have hAplane (x : V3) : (A x).1.1 = 0 ↔ x ∈ plane := by
    change (F.symm x).2 = 0 ↔ x ∈ plane
    simpa only [F.apply_symm_apply] using (hFplane (F.symm x)).symm
  have hAheight (x : V3) : (A x).1.2 = height x := by
    change ellH (F.symm x) = height x
    rw [hHvalue, F.apply_symm_apply]
  have hAell (x : V3) : (A x).2 = ell x := by
    change (F.symm x).1.1 = ell x
    simpa only [F.apply_symm_apply] using (hFell (F.symm x)).symm
  have hAu : A u = ((0, 0), ell u) :=
    Prod.ext (Prod.ext ((hAplane u).mpr huplane) ((hAheight u).trans huh)) (hAell u)
  have hAv : A v = ((0, 0), ell v) :=
    Prod.ext (Prod.ext ((hAplane v).mpr hvplane) ((hAheight v).trans hvh)) (hAell v)
  have hAw : A w₃ = ((0, height w₃), ell w₃) :=
    Prod.ext (Prod.ext ((hAplane w₃).mpr hwplane) (hAheight w₃)) (hAell w₃)
  have hAhull : A '' convexHull ℝ (face : Set V3) =
      convexHull ℝ ({((0, 0), ell u), ((0, 0), ell v),
        ((0, height w₃), ell w₃)} : Set C3) := by
    change A.toAffineEquiv.toAffineMap '' convexHull ℝ (face : Set V3) = _
    rw [A.toAffineEquiv.toAffineMap.image_convexHull]
    change convexHull ℝ (A '' (face : Set V3)) = _
    rw [← hw₃face, heuv]
    simp only [Finset.coe_insert, Finset.coe_singleton, image_insert_eq,
      image_singleton, hAu, hAv, hAw]
    congr 1
    ext x
    simp [or_comm, or_assoc]
  have hwout : ((0, height w₃) : ℝ × ℝ) ≠ 0 := by
    intro heq
    exact hw₃h.ne' (congrArg Prod.snd heq)
  obtain ⟨N, hN, hzeroN, htriangle⟩ := exists_open_vertical_triangle_germ hwout hu hv (ell w₃)
  obtain ⟨V, hV, hzV, hVO, hBface⟩ := hgerm O hO hzO
  let N₀ := V ∩ A ⁻¹' N
  have hN₀ : IsOpen N₀ := hV.inter (hN.preimage A.continuous)
  have hzN₀ : z ∈ N₀ := ⟨hzV, by change A z ∈ N; rw [hAzero]; exact hzeroN⟩
  have hlocal (x : V3) (hx : x ∈ N₀) :
      x ∈ B.space ↔ 0 ≤ height x ∧ (A x).1.1 = 0 := by
    rw [hBface x hx.1, ← A.injective.mem_set_image, hAhull]
    change A x ∈ convexHull ℝ ({(0, ell u), (0, ell v),
      ((0, height w₃), ell w₃)} : Set C3) ↔ _
    rw [htriangle _ hx.2]
    constructor
    · rintro ⟨u, hu, heq⟩
      have hf := congrArg Prod.fst heq
      have hs := congrArg Prod.snd heq
      refine ⟨?_, ?_⟩
      · rw [← hAheight x, hs]
        exact mul_nonneg hu hw₃h.le
      · simpa using hf
    · rintro ⟨hh, hx0⟩
      refine ⟨height x / height w₃, div_nonneg hh hw₃h.le, ?_⟩
      apply Prod.ext
      · simpa using hx0
      · change (A x).1.2 = height x / height w₃ * height w₃
        rw [hAheight, div_mul_cancel₀ _ hw₃h.ne']
  exact ⟨A, N₀, hN₀, hzN₀, fun _ hx => hVO hx.1, hAzero, hAheight, hAell, hlocal⟩

end Geometry.SimplicialComplex
