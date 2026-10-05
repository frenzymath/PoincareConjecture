import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.ThickTorusMap

/-!
# The actual bounded thick-torus open embedding

Compose two literal annulus charts with factor permutations
and invertible real scalings. Their exact intermediate
height bounds include the entire radius-32 cylinder in the
source. See Hamilton 1976, p. 66 and M76 derivation 279.
-/

set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace ThickTorus

/-- The first actual factor exchange and transverse scaling.
See the two-annulus construction in M76 derivation 279. -/
noncomputable def firstCoordinates : ((ℝ × Circle) × Circle) ≃ₜ ((Circle × ℝ) × Circle) where
  toFun z := ((z.1.2, z.1.1 / 64), z.2)
  invFun z := ((64 * z.1.2, z.1.1), z.2)
  left_inv z := Prod.ext (Prod.ext (by dsimp; ring) rfl) rfl
  right_inv z := Prod.ext (Prod.ext rfl (by dsimp; ring)) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The next circle pairs with the first annulus height;
its other real coordinate is retained. See derivation 279. -/
noncomputable def secondCoordinates : ((ℝ × ℝ) × Circle) ≃ₜ ((Circle × ℝ) × ℝ) where
  toFun z := ((z.2, z.1.2 / 64), z.1.1)
  invFun z := ((z.2, 64 * z.1.2), z.1.1)
  left_inv z := Prod.ext (Prod.ext rfl (by dsimp; ring)) rfl
  right_inv z := Prod.ext (Prod.ext rfl (by dsimp; ring)) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The final factor order reverses both transverse scales.
See Hamilton p. 66 and M76 derivation 279. -/
noncomputable def finalCoordinates : ((ℝ × ℝ) × ℝ) ≃ₜ CubeShell.Ambient where
  toFun z := ((4096 * z.1.2, z.2), z.1.1)
  invFun z := ((z.2, z.1.1 / 4096), z.1.2)
  left_inv z := Prod.ext (Prod.ext rfl (by dsimp; ring)) rfl
  right_inv z := Prod.ext (Prod.ext (by dsimp; ring) rfl) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The explicit two-annulus map is an actual open embedding
of the full bounded thick torus, with exact source and full
standard quotient-coordinate PL formulas. The entire closed
quarter-radius coordinate cube is fixed literally.
See Hamilton p. 66 and M76 derivation 279. -/
theorem exists_openPartialHomeomorph :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    ∃ H : OpenPartialHomeomorph ((ℝ × Circle) × Circle) CubeShell.Ambient,
      H.source = {z | |z.1.1| < 32} ∧
      (H : ((ℝ × Circle) × Circle) → CubeShell.Ambient) = map ∧
      (∀ r s t : ℝ, |r| ≤ 1 / 4 → |s| ≤ 1 / 4 → |t| ≤ 1 / 4 →
        H ((r, (s : Circle)), (t : Circle)) = ((r, s), t)) ∧
      ∀ a b : ℝ,
        let T := ((OpenPartialHomeomorph.refl ℝ).prod
          (AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) a)).prod
            (AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) b)
        LocallyPiecewiseAffineOn (H ∘ T) (T.source ∩ T ⁻¹' H.source) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨e, heS, heval⟩ := exists_centeredAnnulus_openPartialHomeomorph
    (L := (16 : ℝ)) (d := 1) (by norm_num) (by norm_num) (by norm_num)
  let F := firstCoordinates.toOpenPartialHomeomorph.trans
    ((e.prod (OpenPartialHomeomorph.refl Circle)).trans
      (secondCoordinates.toOpenPartialHomeomorph.trans
        ((e.prod (OpenPartialHomeomorph.refl ℝ)).trans
          finalCoordinates.toOpenPartialHomeomorph)))
  let U : Set ((ℝ × Circle) × Circle) := {z | |z.1.1| < 32}
  have hU : IsOpen U := by apply isOpen_lt <;> fun_prop
  have hUS : U ⊆ F.source := by
    intro z hz
    have hfirst : (z.1.2, z.1.1 / 64) ∈ e.source := by
      rw [heS]
      exact ⟨mem_univ _, first_height_mem_unit hz⟩
    have hsecond : (z.2, (e (z.1.2, z.1.1 / 64)).2 / 64) ∈ e.source := by
      rw [heS, heval]
      exact ⟨mem_univ _, second_height_mem_unit hz z.1.2⟩
    exact ⟨mem_univ _, ⟨hfirst, mem_univ _⟩,
      mem_univ _, ⟨hsecond, mem_univ _⟩, mem_univ _⟩
  have hFval (z : (ℝ × Circle) × Circle) : F z = map z := by
    change ((4096 * (e (z.2, (e (z.1.2, z.1.1 / 64)).2 / 64)).2,
      (e (z.1.2, z.1.1 / 64)).1), (e (z.2, (e (z.1.2, z.1.1 / 64)).2 / 64)).1) = _
    rw [heval]
    rfl
  let H := F.restrOpen U hU
  have hHS : H.source = U := by
    change F.source ∩ U = U
    exact inter_eq_right.mpr hUS
  have hHval : (H : ((ℝ × Circle) × Circle) → CubeShell.Ambient) = map := funext hFval
  refine ⟨H, hHS, hHval, ?_, ?_⟩
  · intro r s t hr hs ht
    rw [hHval]
    exact map_core hr hs ht
  · intro a b
    let T := ((OpenPartialHomeomorph.refl ℝ).prod
      (AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) a)).prod
        (AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) b)
    have hdom : IsOpen (T.source ∩ T ⁻¹' H.source) :=
      T.continuousOn_toFun.isOpen_inter_preimage T.open_source H.open_source
    have hsub : T.source ∩ T ⁻¹' H.source ⊆ {x : CubeShell.Ambient | |x.1.1| < 32} := by
      intro x hx
      have h : T x ∈ U := hHS ▸ hx.2
      exact h
    apply (locallyPiecewiseAffineOn_map_lift.mono hdom hsub).congr
    intro x _
    rw [Function.comp_apply, hHval]
    rfl

end ThickTorus
