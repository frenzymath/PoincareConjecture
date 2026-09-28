import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Collars
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapHeight
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.Tube.Reparametrization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

variable {v : E3} {g : S2 → E3} {B : Set Real}

theorem exists_normalized_belt_chart (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {a ε : Real} (hε : 0 < ε) (hεa : ε < a) (hε1 : ε < 1-a) :
    ∃ (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
      (T : OpenPartialHomeomorph (S1 × Real) S2),
      T.source = univ ×ˢ Ioo (-ε) ε ∧
      ContMDiffOn Iprod (𝓡 2) ∞ T T.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ T.symm T.target ∧
      (∀ q t, t ∈ Ioo (-ε) ε →
        g (T (q, t)) = (D.center+D.scale*(a+t)) • v +
          (D.planeMap (J.symm (q : E2)) : E3)) ∧
      (∀ q t, t ∈ Ioo (-ε) ε → T (q, t) ∈ D.chart '' ball (0 : E2) 1) ∧
      range (fun q : S1 => T (q, 0)) =
        (D.chart '' closedBall (0 : E2) 1) ∩
          {p : S2 | (inner Real v (g p)-D.center)/D.scale = a} := by
  obtain ⟨J, F, hFs, hF, hFi, hformula, htarget, hinside⟩ :=
    D.exists_cylindrical_belt_chart_of_width hg (δ := |D.scale|/2) le_rfl
  have hbound : |D.scale * (a - 1/2)| + |D.scale| * ε < |D.scale| / 2 := by
    rw [abs_mul]
    have habs : |a-1/2|+ε < (1/2 : Real) := by
      rcases le_total a (1/2 : Real) with ha | ha
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        linarith
    nlinarith [abs_pos.mpr D.scale_ne_zero]
  obtain ⟨T, hTs, hT, hTi, hTF⟩ := exists_reparametrized_sphere_tube
    F hF hFi hFs (D.scale*(a-1/2)) D.scale D.scale_ne_zero hε hbound
  have htF {t : Real} (ht : t ∈ Ioo (-ε) ε) :
      D.scale*(a-1/2)+D.scale*t ∈ Ioo (-(|D.scale|/2)) (|D.scale|/2) := by
    apply abs_lt.mp
    calc
      |D.scale*(a-1/2)+D.scale*t| ≤ |D.scale*(a-1/2)|+|D.scale*t| := abs_add_le _ _
      _ = |D.scale * (a-1/2)| + |D.scale| * |t| := by rw [abs_mul D.scale t]
      _ ≤ |D.scale * (a-1/2)| + |D.scale| * ε :=
        add_le_add_right (mul_le_mul_of_nonneg_left (abs_lt.mpr ht).le (abs_nonneg _)) _
      _ < |D.scale|/2 := hbound
  have hclock (t : Real) : D.center+D.scale/2+(D.scale*(a-1/2)+D.scale*t) =
      D.center+D.scale*(a+t) := by ring
  have hTformula (q : S1) (t : Real) (ht : t ∈ Ioo (-ε) ε) :
      g (T (q, t)) = (D.center+D.scale*(a+t)) • v +
        (D.planeMap (J.symm (q : E2)) : E3) := by
    rw [hTF, hformula q _ (htF ht), hclock]
  have hTin (q : S1) (t : Real) (ht : t ∈ Ioo (-ε) ε) :
      T (q, t) ∈ D.chart '' ball (0 : E2) 1 := by
    rw [hTF]
    apply hinside
    exact F.map_source (by rw [hFs]; exact ⟨mem_univ _, htF ht⟩)
  have ht0 : (0 : Real) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  refine ⟨J, T, hTs, hT, hTi, hTformula, hTin, ?_⟩
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨image_mono ball_subset_closedBall (hTin q 0 ht0), ?_⟩
    change (inner Real v (g (T (q, 0)))-D.center)/D.scale = a
    rw [hTformula q 0 ht0]
    have hh : inner Real v ((D.center+D.scale*(a+0)) • v +
        (D.planeMap (J.symm (q : E2)) : E3)) = D.center+D.scale*a := by
      simpa only [Poincare.Geometry.Euclidean.heightCoordinates_apply, add_zero] using
        Poincare.Geometry.Euclidean.inner_heightCoordinates
        D.unit_v (D.center+D.scale*(a+0), D.planeMap (J.symm (q : E2)))
    rw [hh, add_sub_cancel_left, mul_div_cancel_left₀ a D.scale_ne_zero]
  · rintro ⟨hpD, hpheight⟩
    have hh : inner Real v (g p) = D.center+D.scale*a := by
      have hz := (div_eq_iff D.scale_ne_zero).mp hpheight
      linarith
    have hpF : p ∈ F.target := by
      rw [htarget]
      refine ⟨hpD, ?_⟩
      change |inner Real v (g p)-(D.center+D.scale/2)| < |D.scale|/2
      rw [hh, show D.center+D.scale*a-(D.center+D.scale/2) = D.scale*(a-1/2) by ring]
      have := htF ht0
      simpa only [mul_zero, add_zero] using abs_lt.mpr this
    let z := F.symm p
    have hzs : z ∈ F.source := F.map_target hpF
    have hztime : z.2 = D.scale*(a-1/2) := by
      have hzheight := congrArg (inner Real v) (hformula z.1 z.2 (hFs ▸ hzs).2)
      have hright : F (z.1,z.2) = p := F.right_inv hpF
      rw [hright] at hzheight
      have hrhs : inner Real v ((D.center+D.scale/2+z.2) • v +
          (D.planeMap (J.symm (z.1 : E2)) : E3)) = D.center+D.scale/2+z.2 := by
        simpa only [Poincare.Geometry.Euclidean.heightCoordinates_apply] using
          Poincare.Geometry.Euclidean.inner_heightCoordinates D.unit_v
            (D.center+D.scale/2+z.2, D.planeMap (J.symm (z.1 : E2)))
      rw [hrhs, hh] at hzheight
      linarith
    refine ⟨z.1, ?_⟩
    change T (z.1, 0) = p
    rw [hTF, mul_zero, add_zero, ← hztime]
    exact F.right_inv hpF

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
