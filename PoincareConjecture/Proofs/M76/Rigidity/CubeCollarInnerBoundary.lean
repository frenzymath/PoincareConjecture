import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnitCubePLCollar
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V3) 1
local notation "Q0" => sphere (0 : V3) (7 / 8)
local notation "J" => Icc (0 : ℝ) (1 / 8)
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7 / 8) 1



theorem exists_finitePL_cube_collar_inner_boundary
    (h : (Q ×ˢ J : Set (V3 × ℝ)) ≃ₜ T) (hh : h.IsFinitePL)
    (hnorm : ∀ z : (Q ×ˢ J : Set (V3 × ℝ)),
      ‖(h z : V3)‖ = 1 - (z : V3 × ℝ).2) :
    ∃ b : Q ≃ₜ Q0, b.IsFinitePL ∧ ∀ z : Q,
      (b z : V3) = (h ⟨((z : V3), 1 / 8), ⟨z.property, by norm_num⟩⟩ : V3) := by
  obtain ⟨f, hf, hfval⟩ := hh
  let A : V3 →ᴬ[ℝ] V3 × ℝ :=
    (ContinuousAffineMap.id ℝ V3).prod (ContinuousAffineMap.const ℝ V3 (1 / 8))
  let q : V3 → V3 := f ∘ A
  obtain ⟨K, hK, hKQ⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hA : FinitePiecewiseAffineOn A K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine A⟩
  have hAmap : MapsTo A K.space (Q ×ˢ J) := by
    intro z hz
    refine ⟨hKQ.subset hz, ?_⟩
    change (1 / 8 : ℝ) ∈ J
    norm_num
  have hq : FinitePiecewiseAffineOn q Q := hKQ ▸ hf.comp hA hAmap
  have hqval (z : Q) : q z =
      (h ⟨((z : V3), 1 / 8), ⟨z.property, by norm_num⟩⟩ : V3) := by
    exact (hfval ⟨((z : V3), 1 / 8), ⟨z.property, by norm_num⟩⟩).symm
  have hqi : InjOn q Q := by
    intro x hx y hy hxy
    rw [hqval ⟨x, hx⟩, hqval ⟨y, hy⟩] at hxy
    have hp := h.injective (Subtype.ext hxy)
    exact congrArg (fun z : (Q ×ˢ J : Set (V3 × ℝ)) => z.1.1) hp
  have hqimage : q '' Q = Q0 := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      apply mem_sphere_zero_iff_norm.mpr
      rw [hqval ⟨z, hz⟩, hnorm]
      norm_num
    · intro hx
      have hxnorm : ‖x‖ = 7 / 8 := mem_sphere_zero_iff_norm.mp hx
      have hxT : x ∈ T := by
        change 7 / 8 ≤ ‖x‖ ∧ ‖x‖ ≤ 1
        rw [hxnorm]
        norm_num
      let w : (Q ×ˢ J : Set (V3 × ℝ)) := h.symm ⟨x, hxT⟩
      have hwtime : (w : V3 × ℝ).2 = 1 / 8 := by
        have hn := hnorm w
        change ‖(h (h.symm ⟨x, hxT⟩) : V3)‖ = 1 - (w : V3 × ℝ).2 at hn
        rw [h.apply_symm_apply, hxnorm] at hn
        linarith
      refine ⟨(w : V3 × ℝ).1, w.property.1, ?_⟩
      rw [hqval ⟨(w : V3 × ℝ).1, w.property.1⟩]
      have hw : (⟨((w : V3 × ℝ).1, 1 / 8),
          ⟨w.property.1, by norm_num⟩⟩ : (Q ×ˢ J : Set (V3 × ℝ))) = w :=
        Subtype.ext (Prod.ext rfl hwtime.symm)
      rw [hw]
      exact congrArg Subtype.val (h.apply_symm_apply ⟨x, hxT⟩)
  obtain ⟨b, _, hbval⟩ := hq.exists_homeomorph_image hqi
  refine ⟨b.trans (Homeomorph.setCongr hqimage), ?_, ?_⟩
  · exact ⟨q, hq, fun z => hbval z⟩
  · intro z
    exact (hbval z).trans (hqval z)

end PoincareConjecture.M76
