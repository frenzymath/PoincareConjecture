import PoincareConjecture.Proofs.M28.Sec10_3_Tube.ChainEndBarrier
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapBoundaryTransport
import PoincareConjecture.Proofs.M28.Mathlib.FrontierCrossing

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem intrinsic_ball_subset_first_two_necks {X : Set M}
    (T : EpsilonTubeCertificate g X) {i : ℤ} (hi : IsLeast T.chain.shape.active i)
    (Q : EpsilonNeck g) (hε : T.epsilon ≤ 1 / 1000)
    (hQε : Q.epsilon = T.epsilon)
    (hscale : (0.999 : ℝ) * (T.chain.neck i).scale < Q.scale)
    (hclose : Q.center ∈ closure ((T.chain.neck i).region
      ((255 : ℝ) * T.epsilon⁻¹ / 256) T.epsilon⁻¹))
    {x : M}
    (hx : intrinsicEDist g T.carrier (T.chain.neck i).center x <
      ENNReal.ofReal ((7 / 4 : ℝ) * (T.chain.neck i).scale * T.epsilon⁻¹)) :
    x ∈ (T.chain.neck i).carrier ∪ Q.carrier := by
  let N := T.chain.neck i
  let A : ℝ := T.epsilon⁻¹
  let s : ℝ := N.scale
  have hNε : N.epsilon = T.epsilon := T.chain.epsilon_eq i hi.1
  have heps : 0 < T.epsilon := hNε ▸ N.epsilon_pos
  have hApos : 0 < A := inv_pos.mpr heps
  have hs : 0 < s := N.scale_pos
  have hA : (1000 : ℝ) ≤ A := by
    have h := mul_le_mul_of_nonneg_right hε hApos.le
    rw [mul_inv_cancel₀ heps.ne'] at h
    linarith only [h]
  have hroot : (0.999 : ℝ) ≤ Real.sqrt (1 - T.epsilon) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 - T.epsilon by linarith only [hε])
    nlinarith [Real.sqrt_nonneg (1 - T.epsilon)]
  by_contra hout
  have hxN : x ∉ N.carrier := fun h => hout (Or.inl h)
  have hxQ : x ∉ Q.carrier := fun h => hout (Or.inr h)
  obtain ⟨L, hL, hshort⟩ := sInf_lt_iff.mp hx
  obtain ⟨γ, hγ, h0, h1, hγT, rfl⟩ := hL
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcN : N.center ∈ N.carrier := N.central_sphere_subset N.center_on_central_sphere
  have hc0 : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier hcN).mp N.center_on_central_sphere
  have hstart : γ 0 ∈ N.region (-A) ((255 : ℝ) * A / 256) := by
    rw [h0]
    exact ⟨hcN, by rw [hc0]; linarith only [hApos],
      by rw [hc0]; linarith only [hApos]⟩
  have hend : γ 1 ∉ N.region (-A) ((255 : ℝ) * A / 256) := by
    rw [h1]
    exact fun h => hxN h.1
  obtain ⟨y, ⟨t, ht, rfl⟩, hfront⟩ :=
    (isPreconnected_Icc.image γ hγ.continuousOn).exists_mem_frontier_of_mem_of_notMem
      ⟨0, left_mem_Icc.mpr zero_le_one, rfl⟩ hstart
      ⟨1, right_mem_Icc.mpr zero_le_one, rfl⟩ hend
  have hcut := T.frontier_first_region hi
    (s := (255 : ℝ) * A / 256)
    (by dsimp only [A]; linarith only [hApos])
    (by dsimp only [A]; linarith only [hApos])
  have hysphere : γ t ∈ N.coordinate_map '' (univ ×ˢ ({(255 : ℝ) * A / 256} : Set ℝ)) :=
    hcut ▸ And.intro hfront (hγT (mem_image_of_mem γ ht))
  obtain ⟨z, hz, hy⟩ := hysphere
  have hzA : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rw [hNε, hz.2]
    constructor <;> linarith only [hApos]
  have hyN : γ t ∈ N.carrier := hy ▸ N.coordinate_map_mem_of_axial z hzA
  have hyheight : (N.coordinate_inverse (γ t)).2 = (255 : ℝ) * A / 256 := by
    rw [← hy, N.coordinate_inverse_coordinate_map_of_axial z hzA]
    exact hz.2
  have hfirst := N.edist_central_lower_of_not_mem_region
    (r := (255 : ℝ) * A / 256) (by positivity)
    (by rw [hNε]; linarith only [hApos]) N.center_on_central_sphere
    (show γ t ∉ N.region (-((255 : ℝ) * A / 256)) ((255 : ℝ) * A / 256) from
      fun h => (lt_irrefl _) (hyheight ▸ h.2.2))
  have hfirstNum : (0.99 : ℝ) * s * A ≤
      (N.scale * Real.sqrt (1 - N.epsilon)) * ((255 : ℝ) * A / 256) := by
    rw [hNε]
    have h := mul_le_mul_of_nonneg_left hroot hs.le
    have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (255 : ℝ) * A / 256)
    nlinarith only [h', mul_pos hs hApos]
  have hfirstLength : ENNReal.ofReal ((0.99 : ℝ) * s * A) ≤ g.pathELength γ 0 t :=
    (ENNReal.ofReal_le_ofReal hfirstNum).trans
      (hfirst.trans (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc le_rfl ht.2)) h0 rfl ht.1))
  have hnear := edist_le_of_mem_closure_tail N (by rwa [hNε]) hyN
    (A := A) (by rw [hyheight]; linarith only [hApos]) hclose
  have hnearNum : (1.0005 : ℝ) * N.scale *
      (A - (N.coordinate_inverse (γ t)).2 + A / 256 + 7.1) ≤
      (0.015 : ℝ) * s * A := by
    rw [hyheight]
    have h : (1.0005 : ℝ) * (A - 255 * A / 256 + A / 256 + 7.1) ≤
        (0.015 : ℝ) * A := by linarith only [hA]
    have h' := mul_le_mul_of_nonneg_left h hs.le
    nlinarith only [h']
  have hnear' : g.edist Q.center (γ t) ≤ ENNReal.ofReal ((0.015 : ℝ) * s * A) := by
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using
      hnear.trans (ENNReal.ofReal_le_ofReal hnearNum)
  have hlast := Q.edist_central_lower_of_not_mem_region
    (r := (0.999 : ℝ) * A) (by positivity)
    (by rw [hQε]; linarith only [hApos]) Q.center_on_central_sphere
    (show x ∉ Q.region (-((0.999 : ℝ) * A)) ((0.999 : ℝ) * A) from
      fun h => hxQ h.1)
  have hlastNum : (0.99 : ℝ) * s * A ≤
      (Q.scale * Real.sqrt (1 - Q.epsilon)) * ((0.999 : ℝ) * A) := by
    rw [hQε]
    have h := mul_le_mul_of_nonneg_left hroot Q.scale_pos.le
    have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (0.999 : ℝ) * A)
    have h'' := mul_lt_mul_of_pos_right hscale hApos
    nlinarith only [h', h'', mul_pos hs hApos]
  have hlastLength : ENNReal.ofReal ((0.99 : ℝ) * s * A) ≤
      ENNReal.ofReal ((0.015 : ℝ) * s * A) + g.pathELength γ t 1 := by
    apply (ENNReal.ofReal_le_ofReal hlastNum).trans
    apply hlast.trans
    exact (Manifold.riemannianEDist_triangle (I := 𝓡 3)
      (x := Q.center) (y := γ t) (z := x)).trans
      (add_le_add hnear' (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Icc_subset_Icc ht.1 le_rfl)) rfl h1 ht.2))
  have hsum := add_le_add hfirstLength hlastLength
  have hadd : g.pathELength γ 0 t + g.pathELength γ t 1 = g.pathELength γ 0 1 :=
    Manifold.pathELength_add ht.1 ht.2
  have hsum' : ENNReal.ofReal ((1.98 : ℝ) * s * A) ≤
      ENNReal.ofReal ((0.015 : ℝ) * s * A) + g.pathELength γ 0 1 := by
    calc
      ENNReal.ofReal ((1.98 : ℝ) * s * A) =
          ENNReal.ofReal ((0.99 : ℝ) * s * A) +
            ENNReal.ofReal ((0.99 : ℝ) * s * A) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ g.pathELength γ 0 t +
          (ENNReal.ofReal ((0.015 : ℝ) * s * A) + g.pathELength γ t 1) := hsum
      _ = ENNReal.ofReal ((0.015 : ℝ) * s * A) + g.pathELength γ 0 1 := by
        rw [← add_assoc, add_comm (g.pathELength γ 0 t), add_assoc, hadd]
  have hupper : ENNReal.ofReal ((0.015 : ℝ) * s * A) + g.pathELength γ 0 1 <
      ENNReal.ofReal ((1.765 : ℝ) * s * A) := by
    calc
      _ < ENNReal.ofReal ((0.015 : ℝ) * s * A) +
          ENNReal.ofReal ((7 / 4 : ℝ) * s * A) :=
        ENNReal.add_lt_add_left (by simp) hshort
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hreal : (1.765 : ℝ) * s * A ≤ (1.98 : ℝ) * s * A := by
    nlinarith only [mul_pos hs hApos]
  exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal hreal)) (hsum'.trans_lt hupper)

end PoincareConjecture.M28
