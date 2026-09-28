import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicConvexCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLLocalInterior










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

private theorem local_PL_mem_interior_image
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E → F} {U : Set E}
    (hf : LocallyPiecewiseAffineOn f U)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hinj : InjOn f U) {x : E} (hx : x ∈ U) : f x ∈ interior (f '' U) := by
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  exact interior_mono (image_mono hKU)
    ((hfK.finitePiecewiseAffineOn hK).mem_interior_image hdim (hinj.mono hKU) hxK)

private noncomputable def plane_inclusion : P2 →ᴬ[ℝ] V3 :=
  (ContinuousLinearMap.pi (fun i : Fin 3 =>
    if i = 0 then 0 else if i = 1 then ContinuousLinearMap.fst ℝ ℝ ℝ
      else ContinuousLinearMap.snd ℝ ℝ ℝ)).toContinuousAffineMap

private noncomputable def plane_projection : V3 →ᴬ[ℝ] P2 :=
  ((ContinuousLinearMap.proj (1 : Fin 3)).prod
    (ContinuousLinearMap.proj (2 : Fin 3))).toContinuousAffineMap

private theorem plane_projection_inclusion (x : P2) :
    plane_projection (plane_inclusion x) = x := by
  ext <;> simp [plane_projection, plane_inclusion]

private theorem plane_inclusion_projection {x : V3} (hx : x 0 = 0) :
    plane_inclusion (plane_projection x) = x := by
  ext i
  fin_cases i <;> simp [plane_projection, plane_inclusion, hx]




theorem _root_.OpenPartialHomeomorph.intrinsicFrontier_iff_of_planar_halfplane
    (B : OpenPartialHomeomorph V3 V3)
    (hB : B ∈ piecewiseAffineGroupoid V3) {S : Set V3}
    (hS : IsClosed S)
    (hdim : Module.finrank ℝ (affineSpan ℝ S).direction = 2)
    (hhalf : ∀ x ∈ B.source, x ∈ S ↔ B x 0 = 0 ∧ 0 ≤ B x 2)
    {x : V3} (hx : x ∈ B.source) :
    x ∈ intrinsicFrontier ℝ S ↔ B x 0 = 0 ∧ B x 2 = 0 := by
  classical
  by_cases hxS : x ∈ S
  swap
  · have hnot : x ∉ intrinsicFrontier ℝ S := by
      rw [← closure_sdiff_intrinsicInterior, hS.closure_eq]
      exact fun h => hxS h.1
    exact iff_of_false hnot (fun h => hxS ((hhalf x hx).mpr ⟨h.1, h.2.ge⟩))
  let L := affineSpan ℝ S
  let p : L := ⟨x, subset_affineSpan ℝ S hxS⟩
  let : Nonempty L := ⟨p⟩
  let a := L.directionCoordinates p
  let e := AffineIsometryEquiv.vaddConst ℝ p
  have hspan (z : V3) (hz : z ∈ S) : z ∈ range a := by
    rw [AffineSubspace.range_directionCoordinates]
    exact subset_affineSpan ℝ S hz
  have hinter (u : L.direction) :
      a u ∈ intrinsicInterior ℝ S ↔ u ∈ interior (a ⁻¹' S) := by
    rw [mem_intrinsicInterior]
    constructor
    · rintro ⟨v, hv, heq⟩
      have hvu : v = e u := Subtype.ext heq
      rw [hvu] at hv
      change u ∈ interior (e.toHomeomorph ⁻¹' ((Subtype.val : L → V3) ⁻¹' S))
      rw [← e.toHomeomorph.preimage_interior]
      exact hv
    · intro hu
      refine ⟨e u, ?_, rfl⟩
      change u ∈ interior (e.toHomeomorph ⁻¹' ((Subtype.val : L → V3) ⁻¹' S)) at hu
      rwa [← e.toHomeomorph.preimage_interior] at hu
  let i := a.linearIsometry.toLinearMap
  obtain ⟨r₀, hr₀⟩ := i.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr a.linearIsometry.injective)
  let rA : V3 →ᵃ[ℝ] L.direction :=
    r₀.toAffineMap - AffineMap.const ℝ V3 (r₀ (a 0))
  let r : V3 →ᴬ[ℝ] L.direction := ⟨rA, rA.continuous_of_finiteDimensional⟩
  have ha (u : L.direction) : a u = i u + a 0 := by
    simpa only [i, LinearIsometry.coe_toLinearMap, vadd_eq_add, add_zero]
      using a.map_vadd 0 u
  have hra (u : L.direction) : r (a u) = u := by
    change r₀ (a u) - r₀ (a 0) = u
    rw [ha, map_add, add_sub_cancel_right]
    exact LinearMap.congr_fun hr₀ u
  have har (z : V3) (hz : z ∈ S) : a (r z) = z := by
    obtain ⟨u, rfl⟩ := hspan z hz
    rw [hra]
  have hdim' : Module.finrank ℝ L.direction = Module.finrank ℝ P2 := by
    simpa [Module.finrank_prod] using hdim
  have hBPL := (mem_piecewiseAffineGroupoid_iff V3 B).mp hB
  have hforward : x ∈ intrinsicInterior ℝ S → 0 < B x 2 := by
    intro hxi
    let U := a ⁻¹' B.source ∩ interior (a ⁻¹' S)
    have hU : IsOpen U := (B.open_source.preimage a.continuous).inter isOpen_interior
    let f : L.direction → P2 := plane_projection ∘ B ∘ a
    have hf : LocallyPiecewiseAffineOn f U := by
      apply ((locallyPiecewiseAffineOn_affine plane_projection isOpen_univ).comp
        (hBPL.1.comp (locallyPiecewiseAffineOn_affine a.toContinuousAffineMap isOpen_univ))).mono hU
      intro u hu
      exact ⟨⟨mem_univ _, hu.1⟩, mem_univ _⟩
    have hinj : InjOn f U := by
      intro u hu v hv huv
      have huS : a u ∈ S := (interior_subset hu.2 : u ∈ a ⁻¹' S)
      have hvS : a v ∈ S := (interior_subset hv.2 : v ∈ a ⁻¹' S)
      apply a.injective
      apply B.injOn hu.1 hv.1
      have heq := congrArg plane_inclusion huv
      change plane_inclusion (plane_projection (B (a u))) =
        plane_inclusion (plane_projection (B (a v))) at heq
      rwa [plane_inclusion_projection ((hhalf _ hu.1).mp huS).1,
        plane_inclusion_projection ((hhalf _ hv.1).mp hvS).1] at heq
    have hru : r x ∈ U := by
      refine ⟨?_, ?_⟩
      · change a (r x) ∈ B.source
        rwa [har x hxS]
      · exact (hinter _).mp (by rwa [har x hxS])
    have himage : f '' U ⊆ (univ : Set ℝ) ×ˢ Ici (0 : ℝ) := by
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨mem_univ _, ((hhalf _ hu.1).mp
        (interior_subset hu.2 : u ∈ a ⁻¹' S)).2⟩
    have hout := interior_mono himage (local_PL_mem_interior_image hf hdim' hinj hru)
    rw [interior_prod_eq, interior_univ, interior_Ici] at hout
    have hpos : 0 < B (a (r x)) 2 := hout.2
    rwa [har x hxS] at hpos
  have hbackward : 0 < B x 2 → x ∈ intrinsicInterior ℝ S := by
    intro hxpos
    let V := plane_inclusion ⁻¹' B.target ∩ {z : P2 | 0 < z.2}
    have hV : IsOpen V := (B.open_target.preimage plane_inclusion.continuous).inter
      (isOpen_lt continuous_const continuous_snd)
    let g : P2 → L.direction := r ∘ B.symm ∘ plane_inclusion
    have hg : LocallyPiecewiseAffineOn g V := by
      apply ((locallyPiecewiseAffineOn_affine r isOpen_univ).comp
        (hBPL.2.comp (locallyPiecewiseAffineOn_affine plane_inclusion isOpen_univ))).mono hV
      intro u hu
      exact ⟨⟨mem_univ _, hu.1⟩, mem_univ _⟩
    have hmem (z : P2) (hz : z ∈ V) : B.symm (plane_inclusion z) ∈ S := by
      apply (hhalf _ (B.map_target hz.1)).mpr
      rw [B.right_inv hz.1]
      exact ⟨by simp [plane_inclusion], by simpa [plane_inclusion] using hz.2.le⟩
    have hinj : InjOn g V := by
      intro u hu v hv huv
      have heq := congrArg a huv
      change a (r (B.symm (plane_inclusion u))) = a (r (B.symm (plane_inclusion v))) at heq
      rw [har _ (hmem u hu), har _ (hmem v hv)] at heq
      have hh := B.symm.injOn hu.1 hv.1 heq
      have hh' := congrArg plane_projection hh
      simpa only [plane_projection_inclusion] using hh'
    have hy : plane_projection (B x) ∈ V := by
      refine ⟨?_, hxpos⟩
      change plane_inclusion (plane_projection (B x)) ∈ B.target
      rw [plane_inclusion_projection ((hhalf x hx).mp hxS).1]
      exact B.map_source hx
    have hsub : g '' V ⊆ a ⁻¹' S := by
      rintro _ ⟨z, hz, rfl⟩
      change a (r (B.symm (plane_inclusion z))) ∈ S
      rw [har _ (hmem z hz)]
      exact hmem z hz
    have hout := interior_mono hsub (local_PL_mem_interior_image hg hdim'.symm hinj hy)
    have hh := (hinter _).mpr hout
    change a (r (B.symm (plane_inclusion (plane_projection (B x))))) ∈
      intrinsicInterior ℝ S at hh
    rwa [plane_inclusion_projection ((hhalf x hx).mp hxS).1,
      B.left_inv hx, har x hxS] at hh
  rw [← closure_sdiff_intrinsicInterior, hS.closure_eq]
  have hcoord := (hhalf x hx).mp hxS
  constructor
  · intro hf
    exact ⟨hcoord.1, le_antisymm (le_of_not_gt (fun h => hf.2 (hbackward h))) hcoord.2⟩
  · intro hz
    exact ⟨hxS, fun hi => by simpa only [hz.2, lt_self_iff_false] using hforward hi⟩



theorem _root_.OpenPartialHomeomorph.triangle_intrinsicFrontier_iff_of_halfplane
    (B : OpenPartialHomeomorph V3 V3)
    (hB : B ∈ piecewiseAffineGroupoid V3) (t : Finset V3)
    (ht : AffineIndependent ℝ ((↑) : t → V3)) (ht3 : t.card = 3)
    (hhalf : ∀ x ∈ B.source,
      x ∈ convexHull ℝ (t : Set V3) ↔ B x 0 = 0 ∧ 0 ≤ B x 2)
    {x : V3} (hx : x ∈ B.source) :
    x ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set V3)) ↔
      B x 0 = 0 ∧ B x 2 = 0 := by
  apply B.intrinsicFrontier_iff_of_planar_halfplane hB
    (t.finite_toSet.isCompact_convexHull ℝ).isClosed _ hhalf hx
  rw [affineSpan_convexHull, direction_affineSpan]
  have hrange : range ((↑) : t → V3) = (t : Set V3) := by ext y; simp
  have hh := ht.finrank_vectorSpan (n := 2) (by simpa using ht3)
  rwa [hrange] at hh

end PoincareConjecture.M76
