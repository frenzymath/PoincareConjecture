import PoincareConjecture.Proofs.M76.Triangulation.ConvexSphereCapDisks










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]





theorem isFinitePLBallPair_convex_frontier_affine_cap (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hspace : K.space = s) (A : E →ᵃ[ℝ] ℝ)
    (hneg : ∃ q ∈ interior s, A q < 0)
    (hplane : ∃ w ∈ interior s, A w = 0)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1) :
    IsFinitePLBallPair F (frontier s ∩ {x | 0 ≤ A x}) (frontier s ∩ {x | A x = 0}) := by
  obtain ⟨q, hq, hAq⟩ := hneg
  obtain ⟨w, hw, hAw⟩ := hplane
  let a : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-q)
  let C := a '' s
  let L : E →ₗ[ℝ] ℝ := (-A q)⁻¹ • A.linear
  have hpos : 0 < -A q := neg_pos.mpr hAq
  have heval (x : E) : L (a x) = (A x - A q) / (-A q) := by
    change (-A q)⁻¹ * A.linear (-q + x) = _
    have hsub : A.linear (x - q) = A x - A q := A.linearMap_vsub x q
    rw [show -q + x = x - q by abel, hsub]
    exact (div_eq_inv_mul _ _).symm
  have hcap (x : E) : 1 ≤ L (a x) ↔ 0 ≤ A x := by
    rw [heval, le_div_iff₀ hpos]
    constructor <;> intro h <;> linarith
  have hrim (x : E) : L (a x) = 1 ↔ A x = 0 := by
    rw [heval, div_eq_iff hpos.ne']
    constructor <;> intro h <;> linarith
  have hLw : L (a w) = 1 := (hrim w).mpr hAw
  have hL : L ≠ 0 := by
    intro he
    simp only [he, LinearMap.zero_apply] at hLw
    exact zero_ne_one hLw
  have hC : IsCompact C := hs.image a.continuous
  have hCcv : Convex ℝ C := hcv.affine_image a.toAffineEquiv.toAffineMap
  have haint (x : E) (hx : x ∈ interior s) : a x ∈ interior C := by
    change a x ∈ interior (a.toHomeomorph '' s)
    rw [← a.toHomeomorph.image_interior]
    exact mem_image_of_mem a hx
  have haq : a q = 0 := by change -q + q = 0; exact neg_add_cancel q
  have hC0 : (0 : E) ∈ interior C := haq ▸ haint q hq
  have hfa : a '' frontier s = frontier C := a.toHomeomorph.image_frontier s
  have hfront (x : E) : a x ∈ frontier C ↔ x ∈ frontier s := by
    rw [← hfa]
    exact a.injective.mem_set_image
  have haff : K.AffineOnFaces a := K.affineOnFaces_affine a.toContinuousAffineMap
  let J := haff.embeddedImage a.injective.injOn
  have hJ : J.faces.Finite := haff.embeddedImage_finite _ hK
  have hJC : J.space = C := by rw [haff.embeddedImage_space, hspace]
  have hp := J.isFinitePLBallPair_convex_frontier_cap hJ hC hCcv hC0 hJC L hL
    ⟨a w, haint w hw, hLw⟩ hdim
  have hbackcap : a.symm '' (frontier C ∩ {x | 1 ≤ L x}) =
      frontier s ∩ {x | 0 ≤ A x} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hfront (a.symm y)).mp (by simpa using hy.1),
        (hcap (a.symm y)).mp (by simpa using hy.2)⟩
    · intro hx
      exact ⟨a x, ⟨(hfront x).mpr hx.1, (hcap x).mpr hx.2⟩, a.symm_apply_apply x⟩
  have hbackrim : a.symm '' (frontier C ∩ {x | L x = 1}) =
      frontier s ∩ {x | A x = 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hfront (a.symm y)).mp (by simpa using hy.1),
        (hrim (a.symm y)).mp (by simpa using hy.2)⟩
    · intro hx
      exact ⟨a x, ⟨(hfront x).mpr hx.1, (hrim x).mpr hx.2⟩, a.symm_apply_apply x⟩
  have hback := hp.affine_image a.symm.toContinuousAffineMap a.symm.injective.injOn
  change IsFinitePLBallPair F (a.symm '' (frontier C ∩ {x | 1 ≤ L x}))
    (a.symm '' (frontier C ∩ {x | L x = 1})) at hback
  rwa [hbackcap, hbackrim] at hback

end Geometry.SimplicialComplex
