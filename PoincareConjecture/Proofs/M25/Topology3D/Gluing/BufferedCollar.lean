import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Geometry.Manifold.LocalDiffeomorph












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D





theorem isCollarEmbedding_of_buffered_chart
    {W : Type u} [TopologicalSpace W] [ChartedSpace E3 W]
    [IsManifold (𝓡 3) ∞ W]
    (Phi0 : Diffeomorph (𝓡 3) (𝓡 3) W E3 ∞)
    (e : OpenPartialHomeomorph (UnitTwoSphere × ℝ) W)
    {a b c h : ℝ}
    (hsource : e.source = univ ×ˢ Ioo a b)
    (he : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target)
    (hh : 0 < h) (ha : a < c - h) (hb : c + h < b) :
    IsCollarEmbedding (fun p => Phi0 (e (p.1, c + h * p.2))) := by
  let height : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ :=
    { toFun := fun t => c + h * t
      invFun := fun s => (s - c) / h
      left_inv := by
        intro t
        field_simp [hh.ne']
        ring
      right_inv := by
        intro s
        field_simp [hh.ne']
        ring
      contMDiff_toFun := (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
      contMDiff_invFun := ((contDiff_id.sub contDiff_const).div_const h).contMDiff }
  let A := (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞).prodCongr height
  let d : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      (UnitTwoSphere × ℝ) W ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := he
      contMDiffOn_invFun := hei }
  let kappa := fun p : UnitTwoSphere × ℝ => Phi0 (e (p.1, c + h * p.2))
  have hmap : MapsTo A (univ ×ˢ Ioo (-1 : ℝ) 1) e.source := by
    intro z hz
    change (z.1, c + h * z.2) ∈ e.source
    rw [hsource]
    have hlo := mul_lt_mul_of_pos_left hz.2.1 hh
    have hhi := mul_lt_mul_of_pos_left hz.2.2 hh
    exact ⟨mem_univ _, by nlinarith, by nlinarith⟩
  have heloc (z : UnitTwoSphere × ℝ) (hz : z ∈ e.source) :
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e z :=
    ⟨d, hz, fun _ _ => rfl⟩
  have hloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      kappa (univ ×ˢ Ioo (-1 : ℝ) 1) := by
    intro z
    exact ((A.isLocalDiffeomorph z.1).comp (𝓡 3) W (heloc (A z.1) (hmap z.2))).comp
      (𝓡 3) E3 (Phi0.isLocalDiffeomorph (e (A z.1)))
  refine ⟨hloc.contMDiffOn, ?_, ?_⟩
  · intro z hz w hw hzw
    exact A.injective (e.injOn (hmap hz) (hmap hw) (Phi0.injective hzw))
  · intro z hz
    exact ((hloc ⟨z, hz⟩).mfderivToContinuousLinearEquiv (by simp)).injective

end PoincareConjecture.M25.Topology3D
