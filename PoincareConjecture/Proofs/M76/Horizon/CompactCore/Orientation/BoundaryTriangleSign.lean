import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.ConvexBoundarySign
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem boundary_triangle_det_ne_zero (b : Module.Basis (Fin 3) ℝ E)
    (ell : E →ᴬ[ℝ] ℝ) (n : E) (hn : ell.contLinear n = 1)
    (p : Fin 3 → E) (hp : AffineIndependent ℝ p) (hz : ∀ i, ell (p i) = 0) :
    b.det ![p 1 - p 0, p 2 - p 0, n] ≠ 0 := by
  have hpair : LinearIndependent ℝ ![p 1 - p 0, p 2 - p 0] := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ p 0).mp hp
    have hc := h.comp (fun i : Fin 2 => (⟨i.succ, Fin.succ_ne_zero i⟩ : {j : Fin 3 // j ≠ 0}))
      (by intro i j he; exact Fin.succ_injective _ (congrArg Subtype.val he))
    convert! hc using 1
    funext i
    fin_cases i <;> rfl
  have ht (i : Fin 2) : ell.toAffineMap.linear (![p 1 - p 0, p 2 - p 0] i) = 0 := by
    fin_cases i
    all_goals
      change ell.contLinear (_ -ᵥ p 0) = 0
      rw [ell.contLinear_map_vsub]
      simp [hz]
  have hspan : Submodule.span ℝ (range ![p 1 - p 0, p 2 - p 0]) ≤
      LinearMap.ker ell.toAffineMap.linear := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ht i
  have hnspan : n ∉ Submodule.span ℝ (range ![p 1 - p 0, p 2 - p 0]) := by
    intro he
    have hz' : ell.contLinear n = 0 := hspan he
    rw [hn] at hz'
    norm_num at hz'
  have hfull : LinearIndependent ℝ ![p 1 - p 0, p 2 - p 0, n] := by
    convert! (linearIndependent_finSnoc.mpr ⟨hpair, hnspan⟩) using 1
    funext i
    fin_cases i <;> rfl
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E :=
    (Module.finrank_eq_card_basis b).symm
  exact ((b.is_basis_iff_det).mp ⟨hfull, hfull.span_eq_top_of_card_eq_finrank hcard⟩).ne_zero

theorem affineSpan_triangle_eq_zero_plane
    (hdim : Module.finrank ℝ E = 3) (ell : E →ᴬ[ℝ] ℝ) (n : E)
    (hn : ell.contLinear n = 1) (p : Fin 3 → E) (hp : AffineIndependent ℝ p)
    (hz : ∀ i, ell (p i) = 0) :
    (affineSpan ℝ (convexHull ℝ (range p)) : Set E) = {x | ell x = 0} := by
  let S := AffineSubspace.mk' (p 0) (LinearMap.ker ell.toAffineMap.linear)
  have hS : (S : Set E) = {x | ell x = 0} := by
    ext x
    change ell.toAffineMap.linear (x -ᵥ p 0) = 0 ↔ ell x = 0
    rw [ell.toAffineMap.linearMap_vsub]
    change ell x - ell (p 0) = 0 ↔ ell x = 0
    rw [hz 0, sub_zero]
  have hsurj : Function.Surjective ell.toAffineMap.linear := by
    intro r
    refine ⟨r • n, ?_⟩
    change ell.contLinear (r • n) = r
    simp [hn]
  have hdimker : Module.finrank ℝ (LinearMap.ker ell.toAffineMap.linear) = 2 := by
    have h := ell.toAffineMap.linear.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hdim] at h
    norm_num at h
    omega
  have hle : affineSpan ℝ (range p) ≤ S := by
    apply affineSpan_le.mpr
    rintro x ⟨i, rfl⟩
    change p i ∈ (S : Set E)
    rw [hS]
    exact hz i
  have heq := hp.affineSpan_eq_of_le_of_card_eq_finrank_add_one hle
    (by change 3 = Module.finrank ℝ S.direction + 1
        rw [show S.direction = LinearMap.ker ell.toAffineMap.linear from
          AffineSubspace.direction_mk' (p 0) _, hdimker])
  rw [affineSpan_convexHull, heq, hS]

theorem plLocalSign_mul_triangle_det_sign
    (b : Module.Basis (Fin 3) ℝ E)
    (h : OpenPartialHomeomorph E E) (hh : h ∈ piecewiseAffineGroupoid E)
    (ell m : E →ᴬ[ℝ] ℝ) (n n' : E) (B : E →ᴬ[ℝ] E)
    (hn : ell.contLinear n = 1) (hn' : m.contLinear n' = 1)
    (p : Fin 3 → E) (hp : AffineIndependent ℝ p) (hz : ∀ i, ell (p i) = 0)
    (hsource : convexHull ℝ (range p) ⊆ h.source)
    (hside : ∀ y ∈ h.source, 0 ≤ m (h y) ↔ 0 ≤ ell y)
    (hagree : EqOn h B (convexHull ℝ (range p))) (x : h.source)
    (hx : (x : E) ∈ intrinsicInterior ℝ (convexHull ℝ (range p))) :
    plLocalSign h hh x * SignType.sign (b.det ![p 1 - p 0, p 2 - p 0, n]) =
      SignType.sign (b.det ![B (p 1) - B (p 0), B (p 2) - B (p 0), n']) := by
  have hdim : Module.finrank ℝ E = 3 := by simpa using Module.finrank_eq_card_basis b
  exact plLocalSign_mul_boundary_det_sign b h hh ell m n n' B hn hn'
    (convexHull ℝ (range p)) (convex_convexHull ℝ _)
    (range_nonempty p).convexHull hsource
    (affineSpan_triangle_eq_zero_plane hdim ell n hn p hp hz) hside hagree x hx p
    (fun i => subset_convexHull ℝ _ (mem_range_self i))

end Geometry
