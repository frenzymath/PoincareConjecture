import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalPolygonCut
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)

theorem isConnected_half_open_square_shell {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    IsConnected {x : P2 | ‖x‖ ∈ Ico a 1} := by
  have hprod := (isConnected_sphere (E := P2) (by simp; norm_num) 0 zero_le_one).prod
    (isConnected_Ico ha1)
  have himage : (fun z : P2 × ℝ => z.2 • z.1) ''
      (sphere (0 : P2) 1 ×ˢ Ico a 1) = {x : P2 | ‖x‖ ∈ Ico a 1} := by
    ext x
    constructor
    · rintro ⟨⟨y,t⟩,⟨hy,ht⟩,rfl⟩
      have hy' : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
      change ‖t • y‖ ∈ Ico a 1
      rwa [norm_smul,Real.norm_eq_abs,abs_of_pos (ha.trans_le ht.1),hy',mul_one]
    · intro hx
      have hnorm : 0 < ‖x‖ := ha.trans_le hx.1
      refine ⟨⟨‖x‖⁻¹ • x,‖x‖⟩,⟨?_,hx⟩,?_⟩
      · rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,
          abs_inv,abs_of_pos hnorm,inv_mul_cancel₀ hnorm.ne']
      · simp only [smul_smul,mul_inv_cancel₀ hnorm.ne',one_smul]
  rw [←himage]
  exact hprod.image _ (continuous_snd.smul continuous_fst).continuousOn

theorem isConnected_retained_annulus_without_rim
    {E : Type*} [TopologicalSpace E] {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f : P2 → E} (hf : ContinuousOn f (closedBall (0 : P2) 1))
    (hfi : InjOn f (closedBall (0 : P2) 1)) :
    IsConnected ((f '' {x : P2 | ‖x‖ ∈ Icc a 1}) \ (f '' sphere (0 : P2) 1)) := by
  have heq : ((f '' {x : P2 | ‖x‖ ∈ Icc a 1}) \ (f '' sphere (0 : P2) 1)) =
      f '' {x : P2 | ‖x‖ ∈ Ico a 1} := by
    ext x
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hnot⟩
      refine ⟨y,⟨hy.1,lt_of_le_of_ne hy.2 ?_⟩,rfl⟩
      intro heq
      exact hnot ⟨y,mem_sphere_zero_iff_norm.mpr heq,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      refine ⟨⟨y,⟨hy.1,hy.2.le⟩,rfl⟩,?_⟩
      rintro ⟨z,hz,hzy⟩
      have heq : z = y := hfi (sphere_subset_closedBall hz)
        (mem_closedBall_zero_iff.mpr hy.2.le) hzy
      exact (ne_of_lt hy.2) (heq ▸ mem_sphere_zero_iff_norm.mp hz)
  rw [heq]
  exact (isConnected_half_open_square_shell ha ha1).image _
    (hf.mono (fun x hx => mem_closedBall_zero_iff.mpr hx.2.le))

theorem _root_.IsPreconnected.subset_interior_of_avoids_frontier
    {X : Type*} [TopologicalSpace X] {A R : Set X}
    (hA : IsPreconnected A) (hfront : Disjoint A (frontier R))
    (hmeet : (A ∩ interior R).Nonempty) : A ⊆ interior R := by
  apply hA.subset_of_closure_inter_subset isOpen_interior hmeet
  rintro x ⟨hxcl,hxA⟩
  by_contra hx
  exact disjoint_left.mp hfront hxA
    ⟨closure_mono interior_subset hxcl,hx⟩

end PoincareConjecture.M76
